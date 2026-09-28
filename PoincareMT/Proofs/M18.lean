import PoincareMT.Statements.M18AsymptoticSoliton
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Limits

/-!
# M18 asymptotic soliton proof assembly

This numbered file exposes the source-specific asymptotic-soliton proof from
the pinned Horizon closure. Earlier definitions and statements are read-only;
future native proof helpers belong in `Proofs/M18/`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-!
Given an actual fixed-carrier ancient kappa-solution `K` and a rescaling
sequence `S` with its reference point, positive divergent scales and
reduced-length minimizing basepoints, suppose the reviewed M06--M10,
M07 compactness, and M16 structural services are supplied. For that exact
sequence, pass to a strictly increasing subsequence and construct a pointed
smooth Ricci-flow limit on `t < 0`, using compact time windows whose union is
the open ancient interval and whose base time is `-1`. The embeddings preserve
spatial worldlines on each compact window. The limit is complete,
has nonnegative curvature, is nonflat at every negative time, is
`K.kappa`-noncollapsed on all scales, and has nonnegative scalar-curvature
time derivative.  Construct a smooth potential satisfying
`Ric + Hess(f) + (1/(2*t)) g = 0` at every negative time.

Sources: Morgan--Tian Definition 3.40, p. 61 (ordinary rescaling);
Theorem 7.10 and Claim 7.11, pp. 154--156 (reduced-length minimisers);
Definition 5.12 and Theorem 5.15, pp. 90--92 (pointed compactness with
time-vector compatibility); Section 9.2.2, p. 187 (spatial embeddings);
Theorem 9.11 and
Remark 9.12, pp. 183--185 (the asymptotic soliton limit and its exclusions);
Corollary 6.74, p. 142 (reduced-length scale invariance); Claims 9.13 and
9.15 and Corollaries 9.14, 9.16--9.17, pp. 185--187 (finite-window estimates,
diagonal extraction, and limit properties); Proposition 9.20, pp. 188--198
(the limit reduced-length equations); and Proposition 9.32 and Lemma 9.33,
pp. 198--202 (the soliton-equation conversion).  The scale, endpoint, and
full-curvature-norm conventions follow
`reviews/contracts/M17-repair-contract.md` and
`reviews/errata/2026-09-13-reduced-length-source.md`; Theorem 7.26 and
Proposition 7.27, pp. 165--167, supply reduced-volume rigidity and the
nonflatness contradiction.  Compactness endpoints and ancient Harnack use
`MT-COMPACTNESS-5.15`, `MT-TIME-ENDPOINTS`, and `MT-HARNACK-ANCIENT`, while
the separation from later bounded-curvature and self-similarity claims follows
`MT-SOLITON-STAGING`.  The compact-time and nonflatness boundary follows the
M18 source review and the compact-window correction in
`reviews/contracts/2026-09-19-m18-m35-boundaries-round1.md`. Bounded-curvature
time-slices and a global one-parameter self-similarity family are deliberately
not conclusions, as required by Remark 9.12. -/
theorem ancientAsymptoticSolitonLimits
    (n : ℕ)
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) :
    AncientAsymptoticSolitonConclusion S := by
  exact horizon_ancientAsymptoticSolitonLimits n M K S P

/-! Apply the core theorem to the exact sequence constructed by M17.
Conversely any primitive sequence S gives the M17 setup `⟨S, rfl, rfl⟩`
at its own reference and scales; their positivity and divergence are fields. -/
theorem ancientAsymptoticSolitonLimits_of_setup
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    {K : AncientKappaSolution n M} {reference : M} {tau : ℕ → ℝ}
    (S : AncientBlowupSetup K reference tau)
    (P : AncientAsymptoticSolitonPredecessors K) :
    AncientAsymptoticSolitonConclusion S.sequence :=
  ancientAsymptoticSolitonLimits n M K S.sequence P

/-! Checked assembly captures the universal predecessor provider once.
The resulting service takes an actual sequence, including any sequence
constructed by M17; its analytic proof is the theorem above. -/
theorem ancientAsymptoticSolitonTheory_from_predecessors (n : ℕ)
    (hP : ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
      [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution n M),
      AncientAsymptoticSolitonPredecessors K) :
    AncientAsymptoticSolitonTheory.{u} n := by
  refine ⟨?_⟩
  intro M _ _ _ _ _ _ _ _ _ K S
  exact ancientAsymptoticSolitonLimits n M K S (hP M K)

end PoincareMT
