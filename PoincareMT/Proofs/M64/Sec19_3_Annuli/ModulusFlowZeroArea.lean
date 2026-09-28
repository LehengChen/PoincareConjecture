import PoincareMT.Proofs.M64.Sec19_3_Annuli.ModulusFlowEndpoint
import PoincareMT.Proofs.M64.Sec19_3_Annuli.ModulusZeroAreaForward

/-!
# Actual annular evolution across zero-area times

Swept admissible annuli guard the infimum and give its nonnegativity and
continuity. Positive-cutoff comparison therefore reduces both the sharp
forward estimate and the constant-rate exponential estimate to positive
area at interior times. MT2007 Lemma 19.15 and Corollary 19.16, pp. 447-449.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

/-- Only positive-area interior times need a geometric sharp forward estimate. Proved
continuity and nonnegativity give every remaining time. Source: Morgan--Tian (2007), Lemma
19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64AnnulusFlow_forward_on_Ico_of_positive_on_Ioo
    (hcompact : IsCompact (univ : Set M)) (hcirc : 0 < circumference)
    (P : M62.CircleProductData F circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    (A : M64Annulus (P.flow.metric a) (fun x => c0 x a) (fun x => c1 x a))
    (hforward : ∀ t ∈ Ioo a b, 0 < m64FlowAnnulusArea P c0 c1 t →
      AnnulusForwardDerivativeBound (m64FlowAnnulusArea P c0 c1)
        ((2 * (n : ℝ) - 1) * m64CurvatureSupremum F t *
          m64FlowAnnulusArea P c0 c1 t) t) :
    ∀ t ∈ Ico a b,
      AnnulusForwardDerivativeBound (m64FlowAnnulusArea P c0 c1)
        ((2 * (n : ℝ) - 1) * m64CurvatureSupremum F t *
          m64FlowAnnulusArea P c0 c1 t) t := by
  exact m64AnnulusForwardDerivativeBound.on_Ico_of_positive_on_Ioo
    (m64AnnulusFlow_continuous_of_initial hcompact hcirc P hc0 hc1 A)
    (continuousOn_const.mul (m64CurvatureSupremum_continuous_of_compact hcompact))
    (m64AnnulusFlow_nonnegative_of_initial hcompact hcirc P hc0 hc1 A) hforward

/-- A constant-rate estimate at positive-area interior times gives the actual exponential
comparison between every two included times. Source: Morgan--Tian (2007), Lemma 19.15 and
Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64AnnulusFlow_exponential_of_positive_forward
    (hcompact : IsCompact (univ : Set M)) (hcirc : 0 < circumference)
    (P : M62.CircleProductData F circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    (A : M64Annulus (P.flow.metric a) (fun x => c0 x a) (fun x => c1 x a))
    {K : ℝ} (hK : 0 ≤ K)
    (hforward : ∀ t ∈ Ioo a b, 0 < m64FlowAnnulusArea P c0 c1 t →
      AnnulusForwardDerivativeBound (m64FlowAnnulusArea P c0 c1)
        (K * m64FlowAnnulusArea P c0 c1 t) t) :
    ∀ s t : ℝ, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      m64FlowAnnulusArea P c0 c1 t ≤
        Real.exp (K * (t - s)) * m64FlowAnnulusArea P c0 c1 s := by
  have hf := m64AnnulusFlow_continuous_of_initial hcompact hcirc P hc0 hc1 A
  have hn := m64AnnulusFlow_nonnegative_of_initial hcompact hcirc P hc0 hc1 A
  intro s t hs ht hst
  exact m64AnnulusForwardDerivativeBound.exponential_of_positive_on_Ioo hK
    (hf.mono (Icc_subset_Icc hs.1 ht.2)) (hn s hs)
    (fun x hx => hforward x ⟨hs.1.trans_lt hx.1, hx.2.trans_le ht.2⟩)
    t ⟨hst, le_rfl⟩

end PoincareMT
