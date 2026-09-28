import PoincareMT.Proofs.M07.Analysis.Calculus.SmoothCompactness
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import PoincareMT.Proofs.Horizon.Topology.Sequences.Diagonal

/-! Deduplicated bridge for the Horizon snapshot module
`Analysis.Calculus.SmoothCompactness`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Analysis.Calculus.SmoothCompactness`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/
