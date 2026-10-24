// Puts item icons into the msapi-assets R2 bucket, keyed by content.
//
//   bun upload-icons.ts icons/*.png > keys.json
//
// Each PNG is stored at item/icon/{sha256}.png, which is what an item's
// `item_icon` holds and what the Worker serves at /assets/{key}. The same
// image always gets the same key, so running this twice is harmless. Prints
// {"file": "key"} as JSON.

import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { basename } from "node:path";

const BUCKET = "msapi-assets";
const MAX_BYTES = 256 * 1024;
const PNG = [0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a];

const files = process.argv.slice(2);
if (!files.length) {
  console.error("usage: bun upload-icons.ts FILE.png...");
  process.exit(2);
}

const keys: Record<string, string> = {};
for (const file of files) {
  const bytes = readFileSync(file);
  if (bytes.length > MAX_BYTES) throw new Error(`${file}: ${bytes.length} bytes; icons are at most ${MAX_BYTES}`);
  if (!PNG.every((b, i) => bytes[i] === b)) throw new Error(`${file}: not a PNG`);
  const key = `item/icon/${createHash("sha256").update(bytes).digest("hex")}.png`;
  const put = Bun.spawnSync(
    ["bunx", "wrangler", "r2", "object", "put", `${BUCKET}/${key}`, "--file", file, "--content-type", "image/png", "--remote"],
    { cwd: import.meta.dir, stdout: "ignore", stderr: "pipe" },
  );
  if (put.exitCode !== 0) throw new Error(`${file}: upload failed\n${put.stderr.toString()}`);
  keys[basename(file)] = key;
  console.error(`${basename(file)} -> ${key}`);
}
console.log(JSON.stringify(keys, null, 2));
