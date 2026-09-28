import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.M26Proof
import PoincareMT.Statements.M26CanonicalNeighborhoods

/-!
# M26 canonical-neighborhood proof entry

The numbered theorem below owns the single M26 skeleton admission. Earlier
milestone outputs and the M26 definition/statement boundary are read-only
inputs; future proof helpers belong in `Proofs/M26/`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-
M26: Given the fourteen applied M04, M16, M17, M19, M20, M22, M23, M24
and M25 services,
there are separate positive thresholds `epsilon₂` and `epsilon₃`, with
finite positive functions `C₀(epsilon)` and `C₁(epsilon)`. For every
three-dimensional ancient kappa-solution whose zero slice is noncompact and
has no embedded `RP²` with trivial normal bundle, Corollary 9.88 gives a
strong epsilon-tube covering the zero slice or a `C₀`-capped strong
epsilon-tube covering the zero slice. For every compact
three-dimensional ancient kappa-solution, Theorem 9.89 gives constant positive
sectional curvature, the small-diameter `S³`/`RP³` branch, or a double
`C₁`-capped strong epsilon-tube covering the whole slice. In every tube
branch the static tube has exactly the requested epsilon and every point
of its tube factor centers an actual strong evolving neck of this flow.
The compact alternatives are represented by
the M26 repaired three-way interface, whose round branch carries the existing
arbitrary-finite-quotient `RoundAncientQuotientCertificate`.
The all-time pointwise canonical-neighborhood conclusion belongs to M27.

Sources: Morgan--Tian Definitions 9.1, 9.72, 9.77, 9.81 and 9.82, printed
pp. 180--181 and 230--236; Corollary 9.88, printed pp. 239--240; Theorem
9.89 and Claim 9.90, printed pp. 240--241; Propositions 9.58, 9.79, 9.83,
9.85, and Appendix Proposition A.25, printed pp. 220--221, 232--234,
236--239, and 514; and Theorem 9.42/Corollary 9.54, printed pp. 206--208
and 217--218. The corrected A.19/A.20 separating convention is supplied by
M25 and `MT-NECK-SEPARATION`; compactness endpoint restrictions remain in
M23. The old Chapter 16 Proposition 16.5 cap-persistence admission is a
historical record for M44 and is not an M26 premise.
The complete derivation and provider correction are in
reviews/contracts/2026-09-15-m26-complete-contract.md and its independent
round-one record. Internal work includes whole-past splitting, construction
of the actual two-dimensional factors, compact Ricci pinching, same-slice
diameter normalization, the varying-limit minimizing line, buffered strong
coverage and exclusion of the two-cap-only case. M24 is applied to the
actual constructed negative-time model; no forward extension of K is assumed.
M23's same terminal maps and metric jets through zero are required for local
transfer. Coherent small-carrier transports remain internal proof work.
No source orientation restriction or desired tube/limit is an input.
The authors' Section 19.2 correction has no local application.
-/
theorem m26CanonicalNeighborhoods
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    RepairedCanonicalNeighborhoodTheory.{u} :=
  horizon_m26CanonicalNeighborhoods P


/-! Downstream imports use the named theory wrapper without a second
admission. -/
theorem m26CanonicalNeighborhoodTheory
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    RepairedCanonicalNeighborhoodTheory.{u} :=
  m26CanonicalNeighborhoods P

end PoincareMT
