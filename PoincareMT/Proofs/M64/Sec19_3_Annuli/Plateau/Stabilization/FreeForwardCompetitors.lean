import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreeBoundaryVariation
import PoincareMT.Proofs.M64.Sec19_3_Annuli.ModulusFreeAnnulusFamily
import PoincareMT.Proofs.M64.Sec19_3_Annuli.ForwardMinimalCompetitor

/-!
# Sharp actual future competitors after auxiliary stabilization

The closed M63 smooth relabeling supplier and the smooth anchor annulus
produce a genuine moving family with literal future boundaries. The sharp
double-product variation therefore gives actual competitors and the guarded
forward inequality with the original base coefficient `2 * n - 1`.
Smoothness on an open neighborhood of the closed annulus remains explicit.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareMT.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

/-- An actual smooth weighted-conformal attained annulus supplies future competitors with
the sharp original-base coefficient and arbitrary positive error. Source: Morgan--Tian Lemma
19.15, printed pp. 447-449, and Lemma 19.31, pp. 464-466;
`proof-work/tasks/M64/derivations/2026-09-26-finite-forward-competitors.md`. -/
theorem auxiliaryCircle_free_modulus_exists_forward
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (hn : 1 ≤ n)
    {c0 c1 : ℝ → ℝ → Q.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn Q.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn Q.flow c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus (Q.flow.metric t)
      ((fun x => c0 x t) ∘ sigma0.map) ((fun x => c1 x t) ∘ sigma1.map))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (Q.flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (Q.flow.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (Q.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (Q.flow.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) ∞ A.map O)
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∃ B : M64Annulus (Q.flow.metric (t + h))
          (fun x => c0 x (t + h)) (fun x => c1 x (t + h)),
        B.area ≤ A.area + h * ((2 * (n : ℝ) - 1) * K * A.area + eta) := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  obtain ⟨delta, hdelta, U, hU, hDU, v, hv, hbase, hperiodic, -, -,
      hvelocity0, hvelocity1, hadmit⟩ :=
    m64FreeAnnulus_exists_c2_moving_family_with_literal_competitors
      Q.flow hc0 hc1 ht sigma0 sigma1 A hO hdom hA
  have hforward := (auxiliaryCircle_free_modulus_sharp_variation P Q hn hc0 hc1 ht
    sigma0 sigma1 A hr hminimum hconformal hO hdom hA hK hcurv
    hdelta hU hDU hv hbase hperiodic hvelocity0 hvelocity1).2
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo (-delta) delta :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, hdelta⟩)
  intro eta heta
  filter_upwards [hforward eta heta, hsmall] with h hh hd
  obtain ⟨B, hB⟩ := hadmit h hd
  exact ⟨B, hB.trans_le hh⟩

/-- The attained free-modulus minimum and actual future competitors give the forward
derivative bound with the original curvature supremum. Source: Morgan--Tian Lemma 19.15,
printed pp. 447-449, and Lemma 19.31, pp. 464-466;
`proof-work/tasks/M64/derivations/2026-09-26-finite-forward-competitors.md`. -/
theorem auxiliaryCircle_annulusFlow_forward_of_free_modulus_minimum
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (hn : 1 ≤ n)
    {c0 c1 : ℝ → ℝ → Q.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn Q.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn Q.flow c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus (Q.flow.metric t)
      ((fun x => c0 x t) ∘ sigma0.map) ((fun x => c1 x t) ∘ sigma1.map))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (Q.flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (Q.flow.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (Q.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (Q.flow.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) ∞ A.map O) :
    AnnulusForwardDerivativeBound (m64FlowAnnulusArea Q c0 c1)
      ((2 * (n : ℝ) - 1) * m64CurvatureSupremum F t * m64FlowAnnulusArea Q c0 c1 t) t := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  have hbounded := m64CurvatureRange_bddAbove_of_compact
    (F := F) isCompact_univ (Ioo_subset_Icc_self ht)
  have hcomp := auxiliaryCircle_free_modulus_exists_forward P Q hn hc0 hc1 ht
    sigma0 sigma1 A hr hminimum hconformal hO hdom hA
    (m64CurvatureSupremum_nonneg hbounded) (m64Curvature_le_supremum hbounded)
  obtain ⟨A0, hA0⟩ := m64C2ShrinkingCurves_freeBoundaryAreaTransport Q.flow hc0 hc1
    (Ioo_subset_Icc_self ht) sigma0 sigma1 A
  apply m64AnnulusForward_of_minimal_competitors A0 (hA0.trans hminimum)
  intro eta heta
  filter_upwards [hcomp eta heta] with h hh
  obtain ⟨B, hB⟩ := hh
  refine ⟨B, ?_⟩
  rw [hminimum] at hB
  rw [hA0, hminimum]
  exact hB

end PoincareMT.M64
