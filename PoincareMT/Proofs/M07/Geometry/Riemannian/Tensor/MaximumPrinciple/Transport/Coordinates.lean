import PoincareMT.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Coordinates

/-!
# Shared connection coefficients in a tangent trivialization

M07 uses the existing local M05 implementation of the connection coefficients,
including the derivative terms of the local frame. The copied declaration block
was identical, but its private coefficient name differed by module path and
made the generated public equation incompatible with a joint import.

The original M05 provenance and pending semantic reviews remain in force.
-/
