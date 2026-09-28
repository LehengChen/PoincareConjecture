import PoincareMT.Proofs.M07.Analysis.ODE.ParameterCurveSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecificLimits.Normed

/-! Deduplicated bridge for the Horizon snapshot module
`Analysis.ODE.ParameterCurveSpace`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Analysis.ODE.ParameterCurveSpace`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/
