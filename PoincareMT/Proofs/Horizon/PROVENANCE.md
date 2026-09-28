# Shared Horizon proof library

This directory contains one shared dependency closure used by the completed
M06, M16, M17, M18, M19, M20, and M24 proofs. Existing milestone-local helper
trees remain in place because the repository records their ownership in the
frozen layout catalog; the seven new ports do not duplicate this closure per
milestone.

The directory also contains incremental post-snapshot modules used by M22
(and subsequent milestone ports). M22 adds 102 generated module paths, M23
adds 300, and M33 adds 1,082 from workspace commit
`1e68e1700661486fd1b953051b30a642ad9788b5`, after subtracting the shared
and preceding milestone closures. Their exact path inventories are recorded in
`tools/horizon_milestone_ports.json`; collision decisions remain reproducible
through `tools/horizon_dedup.json`.

The imported source snapshot is Archon Horizon workspace commit
`a1096626d6e26fc0b5c134fe20899e46600575fb`. The published milestone proof
commits represented in that snapshot are:

- M06: `549bd96ad51b49d844bccdbdd6f82a033af154ac`
- M16: `a34865533efbe4854e530d597b074ce3efb1c44e`
- M17: `a1096626d6e26fc0b5c134fe20899e46600575fb`
- M18: `83d3af24a8c9bd08f74e7375fbd2e320521a1892`
- M19: `216f6f4c5059058eef2f6e697331984cadc0d160`
- M20: `d5958a977a8f975082f5436400d9460bac2d69d8`
- M24: `ac78464425d157ccd842bc0ec19fafeb8123c5ec`

`tools/port_horizon_chain.py` computes the recursive import closure, rewrites
its module prefix, and generates compatibility bridges for declarations whose
authority remains Mapher's frozen definition and statement modules. The seven
published theorem names receive a `horizon_` prefix; the numbered proof files
retain Mapher's original theorem names and exact frozen types.

Seven internal Horizon helper names that collide with declarations already
loaded by Mapher's M03/M04 proofs are likewise rewritten consistently with a
`horizon_` prefix. This keeps both implementations available without changing
either proof body or Mapher's established APIs.

The source-only, unused declaration
`RiemannianMetric.exists_radialHomeomorph_of_point_soul` is omitted because it
still contains an admission at the pinned snapshot. None of the seven published
theorems depends on it; the source axiom audit for M20 confirms the complete
classification closure uses only `propext`, `Classical.choice`, and
`Quot.sound`.

## Incremental source authentication

The M22 import was generated from a disk-backed export of the local Horizon
workspace bare repository, not from an unauthenticated loose source tree. A
blob-by-blob comparison against that repository matched all 8,897
`PoincareLib` files at current commit
`1e68e1700661486fd1b953051b30a642ad9788b5` and all 4,614 `PoincareLib` files
at baseline commit `a1096626d6e26fc0b5c134fe20899e46600575fb`.

`SOURCE_COMMIT` in the generator is descriptive metadata rather than a source
authentication mechanism by itself. Reproduction therefore requires either a
Git tree at the recorded object or a separately authenticated export, followed
by the generator's `--check` mode.

A literal scan of the 102 M22-generated files found none of the copyright or
license markers inventoried for the older Horizon closure (`Copyright`,
`All rights reserved`, `Apache-2.0`, `ClassificationOfSurfaces`, or
`DifferentialGeometry`). One of 300 M23-generated files,
`Geometry/Riemannian/Distance/Boundary.lean`, has a PoincareLib contributor
copyright notice; the other 299 and all 1,082 M33-generated files have none of
those literal markers. This bounded result does not change the repository's
project-wide license position or the attribution holds documented in
`references/2026-09-20-horizon-reland-attribution.md`.
