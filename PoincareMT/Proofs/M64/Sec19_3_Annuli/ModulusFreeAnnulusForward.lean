import PoincareMT.Proofs.M64.Sec19_3_Annuli.ModulusFreeProductVariation
import PoincareMT.Proofs.M64.Sec19_3_Annuli.ModulusFreeAnnulusFamily
import PoincareMT.Proofs.M64.Sec19_3_Annuli.ForwardMinimalCompetitor

/-!
# Sharp literal-boundary forward evolution from a free conformal minimum

The actual free-label boundary motions construct their smooth annular
extension. The sharp weighted variation is proved including boundary
branches; zero-area collars restore literal labels after the variation.
The final guarded infimum estimate has the exact public curvature rate.
MT2007 Lemma 19.15, pp. 447-449.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

/-- Actual literal-boundary competitors satisfy the sharp weighted rate from a true free
conformal minimum. The moving family, its original-curve curvature velocity, and collar
admission are constructed, including free lifts with flat intervals. No boundary separation
is required. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449;
project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64FreeCircleProductAnnulus_modulus_exists_forward
    (P : M62.CircleProductData F circumference) (hn : 1 ≤ n) (hcirc : 0 < circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus (P.flow.metric t)
      ((fun x => c0 x t) ∘ sigma0.map) ((fun x => c1 x t) ∘ sigma1.map))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map O)
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∃ B : M64Annulus (P.flow.metric (t + h))
          (fun x => c0 x (t + h)) (fun x => c1 x (t + h)),
        B.area ≤ A.area + h * ((2 * (n : ℝ) - 1) * K * A.area + eta) := by
  let : Fact (0 < circumference) := ⟨hcirc⟩
  obtain ⟨delta, hdelta, U, hU, hDU, v, hv, hbase, hperiodic, _hlo, _hup,
      hvelocity0, hvelocity1, hadmit⟩ :=
    m64FreeAnnulus_exists_c2_moving_family_with_literal_competitors
      P.flow hc0 hc1 ht sigma0 sigma1 A hO hdom hA
  have hforward := (m64FreeCircleProductAnnulus_modulus_sharp_variation
    P hn hcirc hc0 hc1 ht sigma0 sigma1 A hr hminimum hconformal hO hdom hA
    hK hcurv hdelta hU hDU hv hbase hperiodic hvelocity0 hvelocity1).2
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo (-delta) delta :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, hdelta⟩)
  intro eta heta
  filter_upwards [hforward eta heta, hsmall] with h hh hδ
  obtain ⟨B, hB⟩ := hadmit h hδ
  exact ⟨B, hB.trans_le hh⟩

/-- Guarding the full-curvature supremum by compactness gives the exact public numerical
rate for actual literal-boundary competitors. Source: Morgan--Tian (2007), Lemma 19.15 and
Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64FreeCircleProductAnnulus_modulus_exists_forward_with_curvature_supremum
    (P : M62.CircleProductData F circumference) (hn : 1 ≤ n) (hcirc : 0 < circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus (P.flow.metric t)
      ((fun x => c0 x t) ∘ sigma0.map) ((fun x => c1 x t) ∘ sigma1.map))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map O) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∃ B : M64Annulus (P.flow.metric (t + h))
          (fun x => c0 x (t + h)) (fun x => c1 x (t + h)),
        B.area ≤ A.area +
          h * ((2 * (n : ℝ) - 1) * m64CurvatureSupremum F t * A.area + eta) := by
  have hbounded := m64CurvatureRange_bddAbove_of_compact
    (F := F) isCompact_univ (Ioo_subset_Icc_self ht)
  exact m64FreeCircleProductAnnulus_modulus_exists_forward P hn hcirc hc0 hc1 ht
    sigma0 sigma1 A hr hminimum hconformal hO hdom hA
    (m64CurvatureSupremum_nonneg hbounded) (m64Curvature_le_supremum hbounded)

/-- The actual annular infimum has the exact public interior-time upper forward bound
whenever a smooth free conformal minimum is supplied. The original literal C2 boundary class
is restored by proved collars. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16,
pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64AnnulusFlow_forward_of_free_modulus_minimum
    (P : M62.CircleProductData F circumference) (hn : 1 ≤ n) (hcirc : 0 < circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus (P.flow.metric t)
      ((fun x => c0 x t) ∘ sigma0.map) ((fun x => c1 x t) ∘ sigma1.map))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map O) :
    AnnulusForwardDerivativeBound (m64FlowAnnulusArea P c0 c1)
      ((2 * (n : ℝ) - 1) * m64CurvatureSupremum F t * m64FlowAnnulusArea P c0 c1 t) t := by
  let : Fact (0 < circumference) := ⟨hcirc⟩
  obtain ⟨A0, hA0⟩ := m64C2ShrinkingCurves_freeBoundaryAreaTransport P.flow hc0 hc1
    (Ioo_subset_Icc_self ht) sigma0 sigma1 A
  have hcomp := m64FreeCircleProductAnnulus_modulus_exists_forward_with_curvature_supremum
    P hn hcirc hc0 hc1 ht sigma0 sigma1 A hr hminimum hconformal hO hdom hA
  apply m64AnnulusForward_of_minimal_competitors A0 (hA0.trans hminimum)
  intro eta heta
  filter_upwards [hcomp eta heta] with h hh
  obtain ⟨B, hB⟩ := hh
  refine ⟨B, ?_⟩
  rw [hminimum] at hB
  rw [hA0, hminimum]
  exact hB

end PoincareMT
