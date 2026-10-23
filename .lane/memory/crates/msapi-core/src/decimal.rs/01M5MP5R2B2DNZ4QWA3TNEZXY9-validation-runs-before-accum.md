---
id: 01M5MP5R2B2DNZ4QWA3TNEZXY9
anchor: '@file'
created: 2026-10-23T15:30:50Z
norm: '1'
---

validation runs before accumulation so a malformed long string is Invalid, not OutOfRange; the zero-padding loop stops at acc == 0 so "0" at a huge dp does not loop dp times
