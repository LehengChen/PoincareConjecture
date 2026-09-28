import PoincareMT.Proofs.M07.Analysis.ODE.CompactTrajectory
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Cauchy
import PoincareMT.Proofs.Horizon.Analysis.ODE.LocalFlow.Smooth

/-! Deduplicated bridge for the Horizon snapshot module
`Analysis.ODE.CompactTrajectory`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Analysis.ODE.CompactTrajectory`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/
