# msapi: guide for agents and tools

msapi records MapleStory accounts, characters and the character screen's stat
window. Nothing here is fetched from Nexon: a person (or an agent acting for
them) enters what the game shows. Your job is usually to read values off a
screenshot or out of a conversation and write them here exactly.

Base URL: wherever this was served from. Every path below starts with `/v1`.

## Authentication

Send `Authorization: Bearer msk_…` on every request except `/health`, `/v1`,
`/v1/docs`, `/v1/ref/*` and `/v1/auth/*`.

People get a root token by signing in with a passkey; the web app at `/` does
this. The four calls, all `POST`, use the browser's WebAuthn JSON forms
(`PublicKeyCredential.parseCreationOptionsFromJSON` and `credential.toJSON()`):

| Path | Body | Returns |
|---|---|---|
| `/v1/auth/passkey/register/start` | `{"display_name": "Nate"}` | `{"publicKey": creation options}` |
| `/v1/auth/passkey/register/finish` | `{"credential": …}` | a session (201) |
| `/v1/auth/passkey/login/start` | `{}` | `{"publicKey": request options}` |
| `/v1/auth/passkey/login/finish` | `{"credential": …}` | a session |

A session is `{"user_id", "display_name", "token", "token_id", "expires_at"}`:
a root token that lasts 30 days. Sign out by revoking it
(`DELETE /v1/tokens/{token_id}`).

`GET /v1/me` tells you whose token you hold, its scopes, the accounts it is
limited to (`account_ids`, `null` meaning all) and when it expires. Call it
first.

Scopes: `accounts:read`, `accounts:write`, `characters:read`,
`characters:write` (also covers the stat window), `delete`, `tokens:read`,
`tokens:write`, `audit:read`.

Every write you make is recorded with your token's label, the request, and the
data before and after. The owner can read it at `GET /v1/audit`. Writes you
were refused (403) are recorded too.

### Minting a token for another agent

`POST /v1/tokens` with

```json
{ "label": "sheet importer", "scopes": ["characters:read"], "account_ids": ["acc_…"], "expires_in_seconds": 3600 }
```

The new token can only have fewer powers than yours: a subset of your scopes,
a subset of your accounts (required if yours is limited), and it cannot outlive
yours. The default lifetime is a day, shortened to your own expiry if that is
sooner; the maximum is thirty days. The secret is in the response once and
never again. `DELETE /v1/tokens/{id}` revokes a token and everything minted
from it; any token may revoke itself.

## Reference data

- `GET /v1/ref/regions`: `gms`, `kms`, `msea`, `tms`, `jms`. Only regions marked `supported` accept accounts (GMS today).
- `GET /v1/ref/worlds`: each world's `key`, `name`, `region`, `data_center` (`na`/`eu`) and `world_type` (`heroic`, formerly Reboot, or `interactive`).
- `GET /v1/ref/classes`: each class's `id`, `name`, `job_type`, primary and secondary stats, weapon constant and mastery.

World and class names are matched loosely: `"Night Walker"`, `"night-walker"`
and `"nightwalker"` are the same class; `"Kronos"` and `"kronos"` the same world.

## Accounts

One account is one region login. A person may have several.

| Method | Path | Body |
|---|---|---|
| GET | `/v1/accounts` | |
| POST | `/v1/accounts` | `{"region": "gms", "label": "main", "notes": null}` |
| GET | `/v1/accounts/{id}` | |
| PATCH | `/v1/accounts/{id}` | JSON Merge Patch of `label`, `notes` (region cannot change) |
| DELETE | `/v1/accounts/{id}` | deletes its characters and their history; needs `delete` |

An account lists `worlds` (with `world_type` and `character_count`) and its
`character_list`.

## Characters

Field names follow the Nexon Open API's `character/basic`.

| Method | Path | |
|---|---|---|
| GET | `/v1/characters?world=kronos` | all reachable characters, optionally one world |
| GET | `/v1/accounts/{id}/characters` | one account's characters |
| POST | `/v1/accounts/{id}/characters` | create |
| GET / PATCH / DELETE | `/v1/characters/{id}` | read, merge-patch, delete |

```json
{
  "character_name": "Lutoren",
  "world_name": "Kronos",
  "character_class": "Ren",
  "character_level": 285,
  "character_class_level": 6,
  "character_exp": 1234567890,
  "character_exp_rate": 42.125,
  "character_gender": "female",
  "character_guild_name": "Example",
  "popularity": 12,
  "liberation": "genesis",
  "character_image": "https://…",
  "notes": null
}
```

Required: `character_name`, `world_name`, `character_class`, `character_level`
(1-300). Everything else is optional; leave out what you do not know rather
than guessing. `character_exp_rate` takes up to three decimals, as the game
shows it. `liberation` is `none`, `genesis` or `destiny`. A name may be used
once per world per user (409 otherwise). Unknown fields are rejected.

## The stat window

| Method | Path | |
|---|---|---|
| GET | `/v1/characters/{id}/stat` | the latest window, or `{"stat": null}` |
| PUT | `/v1/characters/{id}/stat` | record a complete window |
| PATCH | `/v1/characters/{id}/stat` | merge-patch the latest window into a new one |
| GET | `/v1/characters/{id}/stat/history?limit=&before=` | every recorded window, newest first |

Every write appends a snapshot; nothing is overwritten.

**Absent is not zero.** Omit a field (or send `null`) when you did not see it.
Send `0` only when the screen shows 0.

**Exact decimals.** Percentages are numbers with at most two decimals, exactly
as displayed: `162.27`, not `"162.27%"` or `1.6227`. More precision than the
game shows is rejected, because it means the value was computed, not read.
Responses always write every decimal place (`100.00`, `40.50`). Send plain
decimal numbers: exponent forms like `1e2` and extra trailing zeros (`93.140`)
are rejected. Numbers are read and written as exact decimal text, never as
floating point.

```json
{
  "captured_at": "2026-10-23T14:00:00.000Z",
  "combat_power": 123456789,
  "stat_attack_min": 11788806, "stat_attack_max": 14736287,
  "hp": 98765, "mp": 54321,
  "str": 29216, "dex": 3882, "int": 1015, "luk": 1022,
  "damage": 102.00, "boss_damage": 380.00, "normal_damage": 10.00,
  "final_damage": 162.27, "ignore_defense": 95.53, "ignore_elemental_resistance": 10.00,
  "critical_rate": 100.00, "critical_damage": 112.30,
  "abnormal_status_damage": 8.00,
  "attack_power": 1772, "magic_attack": 600,
  "buff_duration": 120.00, "cooldown_reduction_seconds": 5.00, "cooldown_reduction_percent": 6.00,
  "cooldown_skip": 0.00, "summon_duration": 0.00, "attack_speed": 8, "weapon_mastery": 95.00,
  "star_force": 325, "arcane_power": 1320, "sacred_power": 440,
  "item_drop_rate": 60.00, "mesos_obtained": 20.00, "additional_exp": 30.00,
  "status_resistance": 54, "stance": 100.00, "defense": 30000, "speed": 140.00, "jump": 123.00,
  "remain_ap": 0,
  "breakdowns": {
    "str": { "base": 11910, "percent": 129.00, "flat": 1943 }
  }
}
```

`breakdowns` holds what a stat's tooltip shows (base, percent, flat) for
`str`, `dex`, `int`, `luk`, `hp`, `attack_power` and `magic_attack`.

Responses carry `warnings`, for example when a breakdown implies a different
total than the one recorded; that usually means a misread digit, so look again.
Errors (422, listed in `error.details.issues`) are things that cannot be true,
such as ignore defense of 100 or more or a minimum range above the maximum.

`captured_at` is when the screen showed these values; it defaults to now and
may not be more than five minutes in the future.

## Planned

`/v1/characters/{id}/item-equipment`, `symbol-equipment`, `hyper-stat`,
`ability`, `link-skill`, `vmatrix` and `hexamatrix` exist and answer 501 until
they are built. `GET /v1` lists them.

## Audit

`GET /v1/audit?token_id=&include_descendants=true&target_id=&action=&before=&limit=`

A root token sees every event of its user; a delegated token sees its own and
those of tokens minted below it. Each event has `action` (such as
`character.update` or `stat.replace`), `status`, `token_label`, `request_id`,
and `before`/`after` snapshots of the data.

## Errors

```json
{ "error": { "name": "invalid", "message": "unknown GMS world `Reboot`; expected one of …", "details": { } } }
```

| Status | `name` | Meaning |
|---|---|---|
| 400 | `bad_request`, `invalid_body` | malformed request or JSON that does not fit (the message names the field) |
| 401 | `unauthorized` | missing, unknown, expired or revoked token |
| 403 | `forbidden` | the token lacks a scope or cannot reach that account |
| 404 | `not_found` | does not exist, or belongs to someone else |
| 409 | `conflict` | e.g. a character name already used in that world |
| 413 | `payload_too_large` | body over 256 KiB |
| 415 | `unsupported_media_type` | send `Content-Type: application/json` |
| 422 | `invalid` | well-formed but not possible |
| 501 | `not_implemented` | a planned resource |

Every response has an `x-request-id` header; quote it when reporting problems.

## Paging

Lists that page take `limit` (1-200, default 50) and `before` (an ID). Pass a
response's `next_before` as `before` to get the next page; it is `null` on the
last page.
