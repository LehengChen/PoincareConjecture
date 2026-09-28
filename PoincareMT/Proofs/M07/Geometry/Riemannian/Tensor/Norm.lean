import PoincareMT.Proofs.M05.Geometry.Riemannian.Tensor.Norm
import PoincareMT.Proofs.M07.Geometry.Riemannian.Tensor.Contraction
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Topology.Instances.Matrix

/-!
# Hilbert-Schmidt norms of covariant tensors

Inverse Gram contractions express the norm in a fixed basis. The expression
agrees with the sum of squares in every orthonormal basis and is continuous
under convergence of the metric and tensor components.

These are auxiliary linear algebra results for Topping, "Remarks on Hamilton's
Compactness Theorem for Ricci flow", Theorem 1.7 and its proof, p. 179.
-/

/-! This entry reuses the identical declaration block from the existing local
M05 provider above. Lean rejects duplicate data declarations even when their
types and bodies agree. Original imports and attribution are retained;
the provider retains its existing semantic and provenance review status. -/
