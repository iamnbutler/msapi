---
id: 01M5MZGQHFRBE8M3Y0RMNH65CF
anchor: '@file'
created: 2026-10-23T18:14:07Z
norm: '1'
sig: e3b0c44298fc1c14
body_hash: 536bfdcf17e0d916
raw_hash: 3ab10b3a939dd4dc
vouched: 2026-10-23T19:13:39Z
lines: 1-336
supersedes: 01M5MQQNV8VQE1ZFFC9YX6V1CC
---

JobType, MainStat and Class have hand-written Serialize impls (Verus refuses serde's derive on a checked type); their output must stay byte for byte the derive's, which /v1/ref/classes serves
