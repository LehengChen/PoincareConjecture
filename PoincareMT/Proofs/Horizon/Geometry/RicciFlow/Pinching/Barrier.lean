import PoincareMT.Proofs.M05.Geometry.RicciFlow.Pinching.Barrier
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Pinching.Barrier`.
Its constants already exist on main in
`PoincareMT.Proofs.M05.Geometry.RicciFlow.Pinching.Barrier`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/
