import PoincareMT.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Precompact
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Distance.BallCoverage
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Distance.CompactConfinement
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Measure.HausdorffDensity
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.CenterDensity
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.IntegralRatio
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.ModelIntegral
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.ScalarComparison
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Riccati
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Jacobi.Matrix
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Jacobi.Density
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Jacobi.Root
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Jacobi.CurvatureFrame
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Cutoff
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.OneDimensional
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Transverse.CutoffComparison
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.Assembly

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.Riemannian.Comparison.Volume.Precompact`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Precompact`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/
