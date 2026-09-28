import PoincareMT.Proofs.M07.Geometry.Riemannian.Coordinates.TransitionBounds
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Coordinates.Continuation.ChangeCoordinates
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Coordinates.Transition.JetBounds.Operations
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Coordinates.Transition.Hessian
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.ChristoffelBounds
import PoincareMT.Proofs.Horizon.Analysis.Calculus.SmoothCompactness

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.Riemannian.Coordinates.TransitionBounds`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Geometry.Riemannian.Coordinates.TransitionBounds`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/
