---
id: 01M5MP5R2B2DNZ4QWA3TNEZXY9
anchor: '@file'
created: 2026-10-23T15:30:50Z
norm: '1'
sig: e3b0c44298fc1c14
body_hash: 401ee7e6e69a8287
raw_hash: c68c962ed18d1feb
lines: 1-579
---

validation runs before accumulation so a malformed long string is Invalid, not OutOfRange; the zero-padding loop stops at acc == 0 so "0" at a huge dp does not loop dp times
