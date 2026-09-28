import PoincareMT.Proofs.M07.Geometry.Riemannian.Coordinates.Precompact
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Coordinates.Continuation
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Coordinates.Continuation.Geodesic
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Coordinates.Continuation.TerminalChart
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Coordinates.Continuation.ChangeCoordinates
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Coordinates.Continuation.FixedChart
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Coordinates.Continuation.Speed

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.Riemannian.Coordinates.Precompact`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Geometry.Riemannian.Coordinates.Precompact`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/
