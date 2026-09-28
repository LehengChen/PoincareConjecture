import PoincareMT.Proofs.M07.Analysis.Matrix.Determinant
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Instances.Matrix

/-! Deduplicated bridge for the Horizon snapshot module
`Analysis.Matrix.Determinant`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Analysis.Matrix.Determinant`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/
