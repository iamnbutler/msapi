// msapi on Cloudflare.
//
// The Worker serves the reference web app from static assets and sends API
// paths to one Durable Object, `Api("main")`. That object runs the msapi
// container and keeps its write log: the container's disk is lost whenever it
// stops, so every write batch is sent here (to the `Log` entrypoint, reached as
// http://log.internal from inside the container) before it commits. On boot
// the server rebuilds its database from the latest snapshot and the batches
// after it. See crates/msapi-server/src/durable.rs for the other side.

import { DurableObject, WorkerEntrypoint } from "cloudflare:workers";

interface Env {
  API: DurableObjectNamespace<Api>;
  ASSETS: Fetcher;
  MSAPI_RP_ID: string;
  MSAPI_ORIGIN: string;
  /** Secret for `/__ops/*`. Unset disables those routes. */
  OPS_TOKEN?: string;
}

const LOG_HOST = "log.internal";
const PORT = 8080;
const INACTIVITY_TIMEOUT_MS = 30 * 60 * 1000;
const READY_TIMEOUT_MS = 90 * 1000;
// Durable Object SQLite rows hold at most 2 MB; snapshots are stored in chunks.
const CHUNK = 1024 * 1024;

export default {
  async fetch(request, env): Promise<Response> {
    const url = new URL(request.url);
    if (url.pathname === "/__ops/restart" && request.method === "POST") {
      // Stops the container; the next request boots a fresh one from the log.
      if (!env.OPS_TOKEN || request.headers.get("authorization") !== `Bearer ${env.OPS_TOKEN}`) {
        return new Response("forbidden", { status: 403 });
      }
      await env.API.getByName("main").restart();
      return new Response(null, { status: 204 });
    }
    if (url.pathname === "/health" || url.pathname === "/v1" || url.pathname.startsWith("/v1/")) {
      return env.API.getByName("main").fetch(request);
    }
    return env.ASSETS.fetch(request);
  },
} satisfies ExportedHandler<Env>;

export class Api extends DurableObject<Env> {
  private starting: Promise<void> | undefined;

  constructor(ctx: DurableObjectState, env: Env) {
    super(ctx, env);
    ctx.storage.sql.exec(`
      CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value INTEGER NOT NULL);
      CREATE TABLE IF NOT EXISTS batches (seq INTEGER PRIMARY KEY, body BLOB NOT NULL);
      CREATE TABLE IF NOT EXISTS snapshot (part INTEGER PRIMARY KEY, body BLOB NOT NULL);
    `);
  }

  async fetch(request: Request): Promise<Response> {
    this.starting ??= this.start().finally(() => {
      this.starting = undefined;
    });
    try {
      await this.starting;
    } catch (err) {
      console.error("container did not become ready", err);
      return Response.json({ error: { code: "unavailable", message: "the API is starting; try again" } }, { status: 503, headers: { "retry-after": "5" } });
    }

    const url = new URL(request.url);
    const forwarded = new Request(`http://container${url.pathname}${url.search}`, request);
    forwarded.headers.set("x-forwarded-for", request.headers.get("cf-connecting-ip") ?? "");
    forwarded.headers.delete("host");
    return this.ctx.container!.getTcpPort(PORT).fetch(forwarded);
  }

  private async start(): Promise<void> {
    const container = this.ctx.container!;
    if (!container.running) {
      // Register the log before the container's first DNS lookup of it.
      await container.interceptOutboundHttp(LOG_HOST, this.ctx.exports.Log({ props: {} }));
      container.start({
        image: container.images.base,
        enableInternet: false,
        env: {
          MSAPI_LOG: LOG_HOST,
          MSAPI_RP_ID: this.env.MSAPI_RP_ID,
          MSAPI_ORIGIN: this.env.MSAPI_ORIGIN,
        },
      });
    }
    await container.setInactivityTimeout(INACTIVITY_TIMEOUT_MS);

    const deadline = Date.now() + READY_TIMEOUT_MS;
    for (;;) {
      try {
        const res = await container.getTcpPort(PORT).fetch("http://container/health");
        if (res.ok) return;
      } catch {
        // Not listening yet.
      }
      if (Date.now() > deadline) throw new Error("timed out waiting for /health");
      await scheduler.wait(250);
    }
  }

  /** Destroys the running container, losing its disk. */
  async restart(): Promise<void> {
    const container = this.ctx.container!;
    if (container.running) await container.destroy();
  }

  private meta(key: string): number {
    const row = this.ctx.storage.sql.exec<{ value: number }>("SELECT value FROM meta WHERE key = ?", key).toArray()[0];
    return row?.value ?? 0;
  }

  private setMeta(key: string, value: number): void {
    this.ctx.storage.sql.exec("INSERT OR REPLACE INTO meta (key, value) VALUES (?, ?)", key, value);
  }

  /** The snapshot, then every batch after it, as (seq u64, len u64, bytes) frames. */
  state(): Uint8Array {
    const sql = this.ctx.storage.sql;
    const parts = sql.exec<{ body: ArrayBuffer }>("SELECT body FROM snapshot ORDER BY part").toArray().map((r) => new Uint8Array(r.body));
    const frames: Uint8Array[] = [frame(this.meta("snapshot"), concat(parts))];
    for (const row of sql.exec<{ seq: number; body: ArrayBuffer }>("SELECT seq, body FROM batches ORDER BY seq")) {
      frames.push(frame(row.seq, new Uint8Array(row.body)));
    }
    return concat(frames);
  }

  /** Appends batch `seq`. Refused unless it directly follows the last one. */
  append(seq: number, body: Uint8Array): boolean {
    return this.ctx.storage.transactionSync(() => {
      if (seq !== this.meta("last") + 1) return false;
      this.ctx.storage.sql.exec("INSERT INTO batches (seq, body) VALUES (?, ?)", seq, body);
      this.setMeta("last", seq);
      return true;
    });
  }

  /** Replaces the snapshot with the database after batch `seq`, and drops the batches it covers. */
  snapshot(seq: number, body: Uint8Array): boolean {
    return this.ctx.storage.transactionSync(() => {
      if (seq > this.meta("last") || seq < this.meta("snapshot")) return false;
      const sql = this.ctx.storage.sql;
      sql.exec("DELETE FROM snapshot");
      for (let part = 0; part * CHUNK < body.length; part++) {
        sql.exec("INSERT INTO snapshot (part, body) VALUES (?, ?)", part, body.subarray(part * CHUNK, (part + 1) * CHUNK));
      }
      sql.exec("DELETE FROM batches WHERE seq <= ?", seq);
      this.setMeta("snapshot", seq);
      return true;
    });
  }
}

/** The log as the container sees it: `http://log.internal`. */
export class Log extends WorkerEntrypoint<Env> {
  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    const api = this.env.API.getByName("main");
    const seq = Number(url.searchParams.get("seq"));
    const route = `${request.method} ${url.pathname}`;
    if (route === "GET /state") {
      return new Response(await api.state(), { headers: { "content-type": "application/octet-stream" } });
    }
    if ((route === "POST /changeset" || route === "PUT /snapshot") && Number.isSafeInteger(seq) && seq >= 0) {
      const body = new Uint8Array(await request.arrayBuffer());
      const ok = route === "POST /changeset" ? await api.append(seq, body) : await api.snapshot(seq, body);
      return ok ? new Response(null, { status: 204 }) : new Response(`seq ${seq} is out of order`, { status: 409 });
    }
    return new Response("not found", { status: 404 });
  }
}

function frame(seq: number, body: Uint8Array): Uint8Array {
  const out = new Uint8Array(16 + body.length);
  const view = new DataView(out.buffer);
  view.setBigUint64(0, BigInt(seq));
  view.setBigUint64(8, BigInt(body.length));
  out.set(body, 16);
  return out;
}

function concat(parts: Uint8Array[]): Uint8Array {
  const out = new Uint8Array(parts.reduce((n, p) => n + p.length, 0));
  let at = 0;
  for (const p of parts) {
    out.set(p, at);
    at += p.length;
  }
  return out;
}
