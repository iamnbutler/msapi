---
id: 01M5MN0JMJB7J1J9JQY681RNZ8
anchor: '@file'
created: 2026-10-23T15:10:32Z
norm: '1'
sig: e3b0c44298fc1c14
body_hash: 368d9e1ada59da0b
raw_hash: 51fd442bba36b040
vouched: 2026-10-23T17:45:09Z
lines: 1-468
---

ceremonies are keyed by their challenge in process memory, not the DB: a container restart mid-ceremony just means the user retries; sessions and passkeys are written through Write so they are logged and audited
