-- Passkeys (WebAuthn credentials). Signing in with one mints a root token that
-- expires, so root tokens may now have an expiry too.
CREATE TABLE passkeys (
    id           TEXT PRIMARY KEY,       -- the credential ID, base64url
    user_id      TEXT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    public_key   BLOB NOT NULL,          -- the COSE key, as the authenticator sent it
    sign_count   INTEGER NOT NULL,
    created_at   INTEGER NOT NULL,
    last_used_at INTEGER
) STRICT;
CREATE INDEX passkeys_user ON passkeys(user_id);
