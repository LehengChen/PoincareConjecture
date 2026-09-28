import PoincareMT.Proofs.M05.Geometry.RicciFlow.Pinching.ReactionInvariance
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PoincareMT.Proofs.Horizon.Analysis.Calculus.Nonnegative
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Pinching.Barrier
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Pinching.Reaction

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Pinching.ReactionInvariance`.
Its constants already exist on main in
`PoincareMT.Proofs.M05.Geometry.RicciFlow.Pinching.ReactionInvariance`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/
