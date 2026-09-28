import PoincareMT.Proofs.M05.Analysis.Parabolic.CompactMaximum
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-! Deduplicated bridge for the Horizon snapshot module
`Analysis.Parabolic.CompactMaximum`.
Its constants already exist on main in
`PoincareMT.Proofs.M05.Analysis.Parabolic.CompactMaximum`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/
