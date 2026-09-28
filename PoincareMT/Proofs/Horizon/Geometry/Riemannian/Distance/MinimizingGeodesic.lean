import PoincareMT.Proofs.M07.Geometry.Riemannian.Distance.MinimizingGeodesic
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Distance.MinimizingStep
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Distance.Minimizing.ExponentialChord
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Distance.SegmentSpeed
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Distance.GeodesicGrowth

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.Riemannian.Distance.MinimizingGeodesic`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Geometry.Riemannian.Distance.MinimizingGeodesic`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/
