---
id: 01M5MKQVQYHX2757DT6J9K0TXK
anchor: '@file'
created: 2026-10-23T14:48:17Z
norm: '1'
sig: e3b0c44298fc1c14
body_hash: 69d4bcaf986fce59
raw_hash: 4cbf009925e64eb9
vouched: 2026-10-23T17:45:09Z
lines: 1-445
supersedes: 01M5MKGKC2EYVGT0HT06HYV505
---

a write batch is sent while the position lock is held, so the log's order is the commit order; a commit that fails after logging exits so the restart replays the log. Writes must go through Logged::execute/query_map (never conn().execute) or they are lost on restart; SQL must not call random()/now functions since batches are replayed
