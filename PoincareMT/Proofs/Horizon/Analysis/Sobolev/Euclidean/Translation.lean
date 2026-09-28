import PoincareMT.Proofs.M07.Analysis.Sobolev.Euclidean.Translation
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Tactic

/-! Deduplicated bridge for the Horizon snapshot module
`Analysis.Sobolev.Euclidean.Translation`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Analysis.Sobolev.Euclidean.Translation`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/
