---
id: 01M5MP5R2B2DNZ4QWA3TNEZXY9
anchor: '@file'
created: 2026-10-23T15:30:50Z
norm: '1'
sig: e3b0c44298fc1c14
body_hash: 50fc94950251499b
raw_hash: 867f8d3890111104
vouched: 2026-10-23T16:17:53Z
lines: 1-579
---

validation runs before accumulation so a malformed long string is Invalid, not OutOfRange; the zero-padding loop stops at acc == 0 so "0" at a huge dp does not loop dp times
