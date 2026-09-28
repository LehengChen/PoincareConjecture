import PoincareMT.Proofs.M05.Analysis.Parabolic.LocalPreservation
import PoincareMT.Proofs.Horizon.Analysis.Parabolic.SupportTransport
import PoincareMT.Proofs.Horizon.Analysis.Parabolic.CompactMaximum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Basic

/-! Deduplicated bridge for the Horizon snapshot module
`Analysis.Parabolic.LocalPreservation`.
Its constants already exist on main in
`PoincareMT.Proofs.M05.Analysis.Parabolic.LocalPreservation`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/
