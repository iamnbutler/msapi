-- Who may read a character: anyone ('public', the default) or only its owner.
ALTER TABLE characters ADD COLUMN visibility TEXT NOT NULL DEFAULT 'public'
    CHECK (visibility IN ('public', 'private'));
