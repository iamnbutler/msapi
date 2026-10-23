---
id: 01M5MZGQHFRBE8M3Y0RMNH65CF
anchor: '@file'
created: 2026-10-23T18:14:07Z
norm: '1'
sig: e3b0c44298fc1c14
body_hash: 529f483a04e34c0d
raw_hash: a613c3987d65410f
lines: 1-336
supersedes: 01M5MQQNV8VQE1ZFFC9YX6V1CC
---

JobType, MainStat and Class have hand-written Serialize impls (Verus refuses serde's derive on a checked type); their output must stay byte for byte the derive's, which /v1/ref/classes serves
