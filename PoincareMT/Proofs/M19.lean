import PoincareMT.Statements.M19TwoDimensionalClassification
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional

/-!
# M19 two-dimensional classification proof assembly

Earlier milestone files and the M19 definition/statement boundary are
read-only inputs.  Future proof work belongs in `Proofs/M19/`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-!
Given the M07 pointed-compactness service and the direct M18
asymptotic-soliton service on actual fixed-carrier rescaling sequences, classify
every two-dimensional ancient `kappa`-solution and every two-dimensional
gradient shrinking soliton.
For each prescribed rescaling sequence, construct a limit of that sequence
and establish the bounded-curvature time-slice estimates and the
self-similar homothety that Remark 9.12 leaves open; then apply the
two-dimensional argument to obtain compactness and positive constant
curvature.  The ancient branch gives a compact round flow at every
nonpositive time, and the static shrinking-soliton branch gives the
compact-round model.  No three-dimensional product, quotient, orientation,
or projective-plane alternative is introduced here.

Sources: Morgan--Tian Proposition 9.39 and Corollary 9.40, pp. 203--205
(the noncompact two-dimensional contradiction); Theorem 9.42, pp. 206--207
(the static shrinking-soliton hypotheses and flow construction);
Corollary 9.49, pp. 213--214 (compactness of the two-dimensional case);
Corollary 9.50(1)--(3), pp. 213--214 (round asymptotic limits and all
two-dimensional kappa-solutions); and Theorem 9.11 with Remark 9.12,
pp. 183--185 (the M18 limit and the explicitly deferred bounded-curvature
and self-similarity claims).  Proposition 9.46 and Claims 9.43 and 9.45,
pp. 209--213, rule out the noncompact and non-strict-curvature alternatives;
Hamilton's Proposition 5.21 (p. 118 of [13]), Theorem 5.64 (p. 149 of [13]),
and Proposition 5.39 (p. 134 of [13]) supply the roundness, forward-extension,
and entropy-rigidity steps cited by Morgan--Tian.  The printed Corollary
9.50(1) reference to Proposition 9.50 is a typographical error; this
formalization follows the preceding Proposition 9.39.  The separating and
noncompactness conventions follow the project source audit; no literal
three-dimensional Corollaries 9.53--9.54 are used.
Applicable project records: `reviews/contracts/M19-repair-contract.md`,
`reviews/contracts/M19-round1.md`, `reviews/declarations/M19-round2.md`, and
`reviews/errata/2026-09-10-analytic-outline-audit.md`.
-/
theorem twoDimensionalAncientAndShrinkingSolitonClassification
    (P : TwoDimensionalClassificationPredecessors (M := M)) :
    TwoDimensionalClassificationTheory (M := M) := by
  exact horizon_twoDimensionalAncientAndShrinkingSolitonClassification P

/-! No-sorry named assembly used by downstream milestone imports. -/
theorem twoDimensionalClassificationTheory
    (P : TwoDimensionalClassificationPredecessors (M := M)) :
    TwoDimensionalClassificationTheory (M := M) :=
  twoDimensionalAncientAndShrinkingSolitonClassification P

end PoincareMT
