-- Users, delegated tokens, the audit log, and the first game data:
-- accounts, characters and stat-window snapshots.
--
-- Times are milliseconds since the Unix epoch (UTC). IDs are prefixed,
-- time-sortable strings (see src/ids.rs), so ORDER BY id is creation order.

CREATE TABLE users (
    id           TEXT PRIMARY KEY,
    display_name TEXT NOT NULL,
    created_at   INTEGER NOT NULL
) STRICT;

-- A bearer credential. Root tokens (parent_id NULL) belong to a person;
-- delegated tokens are minted from another token and can never exceed it.
CREATE TABLE tokens (
    id           TEXT PRIMARY KEY,
    user_id      TEXT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    parent_id    TEXT REFERENCES tokens(id) ON DELETE CASCADE,
    label        TEXT NOT NULL,
    scopes       TEXT NOT NULL,          -- space-separated, e.g. "characters:read characters:write"
    account_ids  TEXT,                   -- JSON array; NULL means every account the parent can reach
    secret_hash  BLOB NOT NULL UNIQUE,   -- SHA-256 of the full token string
    created_at   INTEGER NOT NULL,
    expires_at   INTEGER,                -- NULL only for root tokens
    revoked_at   INTEGER,
    last_used_at INTEGER
) STRICT;
CREATE INDEX tokens_user ON tokens(user_id);
CREATE INDEX tokens_parent ON tokens(parent_id);

-- One row per write (and per refused write). Never updated or deleted by the API.
CREATE TABLE audit_events (
    id          TEXT PRIMARY KEY,
    at          INTEGER NOT NULL,
    user_id     TEXT NOT NULL,
    token_id    TEXT NOT NULL,
    token_label TEXT NOT NULL,           -- copied, so renaming or deleting a token keeps history readable
    request_id  TEXT NOT NULL,
    method      TEXT NOT NULL,
    path        TEXT NOT NULL,
    action      TEXT NOT NULL,           -- e.g. "character.create", "stat.replace"
    target_type TEXT,
    target_id   TEXT,
    status      INTEGER NOT NULL,
    client      TEXT,
    user_agent  TEXT,
    before_json TEXT,
    after_json  TEXT
) STRICT;
CREATE INDEX audit_user ON audit_events(user_id, id);
CREATE INDEX audit_token ON audit_events(token_id, id);
CREATE INDEX audit_target ON audit_events(target_id, id);

-- A game account in one region (one Nexon login can hold several worlds).
CREATE TABLE accounts (
    id         TEXT PRIMARY KEY,
    user_id    TEXT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    region     TEXT NOT NULL,
    label      TEXT,
    notes      TEXT,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL
) STRICT;
CREATE INDEX accounts_user ON accounts(user_id);

CREATE TABLE characters (
    id              TEXT PRIMARY KEY,
    user_id         TEXT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    account_id      TEXT NOT NULL REFERENCES accounts(id) ON DELETE CASCADE,
    character_name  TEXT NOT NULL,
    name_key        TEXT NOT NULL,       -- lowercase name, for uniqueness
    world_key       TEXT NOT NULL,
    class_id        TEXT NOT NULL,
    class_level     INTEGER,
    level           INTEGER NOT NULL,
    exp             INTEGER,
    exp_rate        INTEGER,             -- thousandths of a percent
    gender          TEXT,
    guild_name      TEXT,
    popularity      INTEGER,
    liberation      TEXT,
    image_url       TEXT,
    notes           TEXT,
    created_at      INTEGER NOT NULL,
    updated_at      INTEGER NOT NULL,
    UNIQUE (user_id, world_key, name_key)
) STRICT;
CREATE INDEX characters_account ON characters(account_id);

-- Append-only. The latest row per character is its current stat window.
CREATE TABLE stat_snapshots (
    id           TEXT PRIMARY KEY,
    character_id TEXT NOT NULL REFERENCES characters(id) ON DELETE CASCADE,
    captured_at  INTEGER NOT NULL,
    recorded_at  INTEGER NOT NULL,
    event_id     TEXT NOT NULL,
    data         TEXT NOT NULL           -- StatWindow JSON; kept last (large column)
) STRICT;
CREATE INDEX stat_snapshots_character ON stat_snapshots(character_id, id);
