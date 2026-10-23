---
id: 01M5MN0JMJB7J1J9JQY681RNZ8
anchor: '@file'
created: 2026-10-23T15:10:32Z
norm: '1'
sig: e3b0c44298fc1c14
body_hash: cd125547750b8803
raw_hash: e8ee762fdaf6c571
vouched: 2026-10-23T15:16:09Z
lines: 1-468
---

ceremonies are keyed by their challenge in process memory, not the DB: a container restart mid-ceremony just means the user retries; sessions and passkeys are written through Write so they are logged and audited
