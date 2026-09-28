import PoincareMT.Proofs.M07.Geometry.Riemannian.Distance.GeodesicGrowth
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.Riemannian.Distance.GeodesicGrowth`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Geometry.Riemannian.Distance.GeodesicGrowth`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/
