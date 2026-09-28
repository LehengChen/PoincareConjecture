import PoincareMT.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Local
import PoincareMT.Proofs.M07.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Radial
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Radial transport for locally smooth connection coefficients

A smooth cutoff extends a local coefficient field. On a smaller ball the
resulting radial field obeys the original parallel equation, so its contact
jets use the original connection.
-/

/-! This entry reuses the identical declaration block from the existing local
M05 provider above. Lean rejects duplicate data declarations even when their
types and bodies agree. Original imports and attribution are retained;
the provider retains its existing semantic and provenance review status. -/
