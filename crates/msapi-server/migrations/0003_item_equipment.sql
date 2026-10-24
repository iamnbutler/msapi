-- The equipment window. Like the stat window, every write appends a snapshot.
CREATE TABLE item_equipment_snapshots (
    id           TEXT PRIMARY KEY,
    character_id TEXT NOT NULL REFERENCES characters(id) ON DELETE CASCADE,
    captured_at  INTEGER NOT NULL,
    recorded_at  INTEGER NOT NULL,
    event_id     TEXT NOT NULL,
    data         TEXT NOT NULL           -- ItemEquipment JSON; kept last (large column)
) STRICT;
CREATE INDEX item_equipment_snapshots_character ON item_equipment_snapshots(character_id, id);
