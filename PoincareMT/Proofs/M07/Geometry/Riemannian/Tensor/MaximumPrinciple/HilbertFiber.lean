import PoincareMT.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.HilbertFiber
import PoincareMT.Proofs.M07.Geometry.Riemannian.Tensor.Norm
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hilbert fibers of covariant tensors

A separate type for covariant tensors carries the Hilbert--Schmidt norm,
whose square is the sum of squared orthonormal-frame components. This keeps
the Hilbert norm distinct from an operator norm. Transport of the tangent
fiber by a linear isometry equivalence induces isometric covariant tensor
transport. The scalar inner product is a finite tensor contraction in any
orthonormal basis.
-/

/-! This entry reuses the identical declaration block from the existing local
M05 provider above. Lean rejects duplicate data declarations even when their
types and bodies agree. Original imports and attribution are retained;
the provider retains its existing semantic and provenance review status. -/
