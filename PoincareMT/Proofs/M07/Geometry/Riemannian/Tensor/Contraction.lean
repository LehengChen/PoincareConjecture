import PoincareMT.Proofs.M05.Geometry.Riemannian.Tensor.Contraction
import PoincareMT.Proofs.M07.Geometry.Riemannian.Tensor.RicciDerivative
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Metric contractions of covariant tensors

The contraction calculations use the specified metric and connection. The
pointwise orthonormal basis is never treated as a smooth vector field.
-/

/-! This entry reuses the identical declaration block from the existing local
M05 provider above. Lean rejects duplicate data declarations even when their
types and bodies agree. Original imports and attribution are retained;
the provider retains its existing semantic and provenance review status. -/
