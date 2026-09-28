import PoincareMT.Proofs.M64.Sec19_3_Annuli.AnnulusLogBoundaryLimit

/-!
# Removing boundary regularization when the current vanishes at branches

The factored normal derivative is controlled by the actual integrable
current. Its vanishing on the zero-energy set gives the dominated limit
even on boundary intervals of rank zero. MT2007 Lemma 19.15, pp. 447-449;
the regularized M60 curvature argument with a zero-set weight.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareMT

private theorem regularized_ratio_tendsto_of_zero_set
    {X : Type*} [MeasurableSpace X] {mu : Measure X} {f g : X → ℝ}
    (hf : AEMeasurable f mu) (hnonneg : ∀ᵐ x ∂mu, 0 ≤ f x)
    (hg : Integrable g mu) (hzero : ∀ᵐ x ∂mu, f x = 0 → g x = 0) :
    Tendsto (fun m : ℕ => ∫ x, (f x / (f x + 1 / ((m : ℝ) + 1))) * g x ∂mu)
      atTop (𝓝 (∫ x, g x ∂mu)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
  · intro m
    exact ((hf.div (hf.add aemeasurable_const)).aestronglyMeasurable).mul
      hg.aestronglyMeasurable
  · exact hg.norm
  · intro m
    filter_upwards [hnonneg] with x hx
    have he : 0 < 1 / ((m : ℝ) + 1) := by positivity
    have hden : 0 < f x + 1 / ((m : ℝ) + 1) := add_pos_of_nonneg_of_pos hx he
    have hq0 : 0 ≤ f x / (f x + 1 / ((m : ℝ) + 1)) := div_nonneg hx hden.le
    have hq1 : f x / (f x + 1 / ((m : ℝ) + 1)) ≤ 1 :=
      (div_le_one hden).mpr (le_add_of_nonneg_right he.le)
    rw [norm_mul, Real.norm_of_nonneg hq0]
    exact mul_le_of_le_one_left (norm_nonneg _) hq1
  · filter_upwards [hzero] with x hx
    by_cases hfx : f x = 0
    · simp only [hfx, zero_div, zero_mul, hx hfx]
      exact tendsto_const_nhds
    · have hlim := (tendsto_const_nhds (x := f x)).div
        (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat)
        (by simpa using hfx)
      simpa [hfx] using hlim.mul_const (g x)

/-- A genuine factored normal trace has the regularized logarithmic integral limit when its
continuous factor vanishes on the zero-energy set. Boundary positivity is not required.
Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project
derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64Annulus_log_normal_trace_tendsto_of_factored_trace
    {a : LoopPlane → ℝ} {O : Set LoopPlane} (hO : IsOpen O)
    (hdom : m64AnnulusDomain ⊆ O) (ha : ContDiffOn ℝ ∞ a O)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {J : ℝ → ℝ}
    (hJ : ContinuousOn J (Icc (0 : ℝ) curvePeriod))
    (hnonneg : ∀ x ∈ Icc (0 : ℝ) curvePeriod, 0 ≤ a (annulusPoint x s))
    (hfactor : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      fderiv ℝ a (annulusPoint x s) (EuclideanSpace.single (1 : Fin 2) 1) =
        a (annulusPoint x s) * J x)
    (hzero : ∀ x ∈ Icc (0 : ℝ) curvePeriod, a (annulusPoint x s) = 0 → J x = 0) :
    Tendsto (fun m : ℕ => ∫ x in Icc (0 : ℝ) curvePeriod,
      fderiv ℝ (fun q => Real.log (a q + 1 / ((m : ℝ) + 1)))
        (annulusPoint x s) (EuclideanSpace.single (1 : Fin 2) 1)) atTop
      (𝓝 (∫ x in Icc (0 : ℝ) curvePeriod, J x)) := by
  let F := fun x : ℝ => a (annulusPoint x s)
  have hpoint (x : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod) : annulusPoint x s ∈ O :=
    hdom ⟨hx.1, hx.2, hs.1, hs.2⟩
  have hcurve : Continuous (fun x : ℝ => annulusPoint x s) := by
    unfold annulusPoint
    fun_prop
  have hF : ContinuousOn F (Icc (0 : ℝ) curvePeriod) :=
    ha.continuousOn.comp hcurve.continuousOn hpoint
  have hnonnegae : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) curvePeriod), 0 ≤ F x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hnonneg x hx
  have hzeroae : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) curvePeriod), F x = 0 → J x = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hzero x hx
  have hlim := regularized_ratio_tendsto_of_zero_set
    (hF.aemeasurable measurableSet_Icc) hnonnegae
    (hJ.integrableOn_compact isCompact_Icc) hzeroae
  convert hlim using 1
  funext m
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hepsilon : 0 < 1 / ((m : ℝ) + 1) := by positivity
  have hden : 0 < a (annulusPoint x s) + 1 / ((m : ℝ) + 1) :=
    add_pos_of_nonneg_of_pos (hnonneg x hx) hepsilon
  have hd := (((ha.contDiffAt (hO.mem_nhds (hpoint x hx))).differentiableAt
    (by simp)).hasFDerivAt.add_const (1 / ((m : ℝ) + 1))).log hden.ne'
  rw [hd.fderiv]
  simp only [smul_apply, smul_eq_mul]
  rw [hfactor x hx]
  dsimp only [F]
  ring

end PoincareMT
