import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Proof
import PoincareMT.Statements.M27KappaAlternatives
import PoincareMT.Statements.M27Providers

/-!
# M27 full canonical alternatives

The single admission belongs to this milestone. Future proof helpers belong
in Proofs/M27; earlier milestone files and this contract remain read-only.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-
Given the fourteen primitive predecessor services supplied from M04, M16,
M19, M22, M23, M24, M25 and M26, choose a universal positive epsilon
threshold. For each smaller positive epsilon choose C>0
before the carrier and the three-dimensional ancient kappa-solution K.
Its zero slice is one of: a round finite spherical space form; a compact
positive-curvature S3 or RP3 with uniform diameter, volume and cross-point
sectional bounds at scalar-curvature scale; a positive double-capped strong
tube; a positive capped strong tube on R3; the free orientation-preserving
round S2-times-line quotient on punctured RP3; round S2 times R; or the
exceptional evolving round RP2 times R product. In the tube cases every
point is in a cap core or centers a strong neck. The round and product
witnesses identify the same whole past flow through fixed spatial maps.
All solutions satisfy the
strict uniform gradient/scalar^(3/2) and absolute time-derivative/scalar^2
bounds for t<=0, with an actual within-domain derivative at time zero.

M26's Theorem 9.89 classifies only its zero slice. If the original zero
slice is round but an earlier slice is nonround, apply M16 normalization
and the shifted M26 theorem at that earlier time. Its compact-small branch
gives S3/RP3 topology; its double-cap branch gives the same topology by
the M25 compact-topology argument in steps 7-8 of the complete contract.
The original round quotient then has fundamental group of order one or
two, so its explicit diameter, volume and sectional-curvature constants
put it in compactPositive after one uniform enlargement of C. Conversely,
a round zero-slice space form with different fundamental group has no
nonround earlier slice. In the all-round case put c(t)=R(t)/6. Then
Ric=2*c(t)*g(t), scalar evolution gives c'=4*c^2, and the metric equation
gives g(t)=(1-4*c(0)*t)*g(0) on the fixed carrier. The single quotient map
chosen at time zero therefore identifies the whole past family. This is
the route of Theorem 9.89, pp. 240-241, and Theorem 9.93, p. 242, recorded
in steps 4 and 10 of the complete contract; no backward uniqueness is used.

For every positive epsilon up to a smaller uniform threshold, choose C>0
before K so that every spacetime point has a strong (C,epsilon)-canonical
neighborhood unless K is the genuine evolving RP2-times-line product.
Round neighborhoods allow arbitrary compact curvature-one references;
their full covariant C^[1/epsilon] comparison is Definition 2.16.

Sources: Morgan--Tian Theorem 9.93 and Corollary 9.94, printed pp. 242-243;
Propositions 9.83 and 9.91, pp. 236 and 241-242; Corollary 9.71 and
equations (9.31)-(9.34), pp. 229-230 and 243; Definitions 9.72, 9.75-9.78
and 9.81-9.82, pp. 230-236; Definition 2.16, equation (2.1), p. 30.
Theorem 9.93(2)'s lower diameter uses the corrected R^(-1/2) exponent:
MT-CANONICAL-DIAMETER-SCALING, reviews/errata/2026-09-13-canonical-diameter.md.
MT-NECK-SEPARATION, MT-COMPACTNESS-5.15, MT-TIME-ENDPOINTS and
MT-ANCIENT-LIMIT-BOUNDED-CURVATURE remain binding through the providers.
The source derivation is reviews/contracts/2026-09-15-m27-complete-contract.md.
Remark 9.73's printed cap-radius exponent is corrected to R^(-1/2) by
reviews/errata/2026-09-15-cap-radius-scaling.md; the Lean root equation
already has r^(-2). Appendix A.11-A.25, the M20 quotient correction, M23
terminal jets, M24 model identity and M25/M26 provider corrections remain
binding through the checked services.
-/
theorem m27KappaAlternatives (P : M27KappaAlternativePredecessors.{u}) :
    RepairedKappaAlternativeTheory.{u} :=
  horizon_m27KappaAlternatives P


end PoincareMT
