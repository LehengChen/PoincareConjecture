import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Actual derivative bounds for the two formulas of the gauge forcing

Morgan-Tian pp. 313-320. The canceled smooth tip formula and the
reciprocal-warping exterior formula are bounded on their actual domains.
The following operations retain actual derivatives when multiplying,
subtracting, or adding the displacement variable by a linear projection.
-/

set_option autoImplicit false

open Set
open scoped ContDiff BigOperators

namespace PoincareMT.M35.RadialGauge

variable {A E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Common actual derivative bounds are closed under subtraction on
any part of an open smoothness domain. -/
theorem family_jet_bounds_sub {f g : A → E → ℝ} {U S : Set E}
    (hU : IsOpen U) (hS : S ⊆ U)
    (hf : ∀ a, ContDiffOn ℝ ∞ (f a) U) (hg : ∀ a, ContDiffOn ℝ ∞ (g a) U)
    (hfb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ S →
      ‖iteratedFDeriv ℝ j (f a) x‖ ≤ C)
    (hgb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ S →
      ‖iteratedFDeriv ℝ j (g a) x‖ ≤ C) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ S →
      ‖iteratedFDeriv ℝ j (fun y => f a y - g a y) x‖ ≤ C := by
  intro j
  obtain ⟨C, hC, hCb⟩ := hfb j
  obtain ⟨D, hD, hDb⟩ := hgb j
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  intro a x hx
  have hj : (j : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  rw [fun_iteratedFDeriv_sub_apply
    (((hf a x (hS hx)).contDiffAt (hU.mem_nhds (hS hx))).of_le hj)
    (((hg a x (hS hx)).contDiffAt (hU.mem_nhds (hS hx))).of_le hj)]
  exact (norm_sub_le _ _).trans (add_le_add (hCb a x hx) (hDb a x hx))

/-- A fixed scalar factor preserves the common derivative bounds. -/
theorem family_jet_bounds_const_mul {f : A → E → ℝ} {U S : Set E}
    (hU : IsOpen U) (hS : S ⊆ U) (hf : ∀ a, ContDiffOn ℝ ∞ (f a) U)
    (hfb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ S →
      ‖iteratedFDeriv ℝ j (f a) x‖ ≤ C) (b : ℝ) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ S →
      ‖iteratedFDeriv ℝ j (fun y => b * f a y) x‖ ≤ C := by
  intro j
  obtain ⟨C, hC, hCb⟩ := hfb j
  refine ⟨|b| * C, mul_nonneg (abs_nonneg b) hC, ?_⟩
  intro a x hx
  have hj : (j : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  have hd := iteratedFDeriv_const_smul_apply' (a := b)
    (((hf a x (hS hx)).contDiffAt (hU.mem_nhds (hS hx))).of_le hj)
  simp only [smul_eq_mul] at hd
  rw [hd, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hCb a x hx) (abs_nonneg b)

/-- Products preserve common actual derivative bounds on the same
region, without extending the exterior factors across the tip. -/
theorem family_jet_bounds_mul {f g : A → E → ℝ} {U S : Set E}
    (hU : IsOpen U) (hS : S ⊆ U)
    (hf : ∀ a, ContDiffOn ℝ ∞ (f a) U) (hg : ∀ a, ContDiffOn ℝ ∞ (g a) U)
    (hfb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ S →
      ‖iteratedFDeriv ℝ j (f a) x‖ ≤ C)
    (hgb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ S →
      ‖iteratedFDeriv ℝ j (g a) x‖ ≤ C) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ S →
      ‖iteratedFDeriv ℝ j (fun y => f a y * g a y) x‖ ≤ C := by
  classical
  choose B hB0 hB using hfb
  choose D hD0 hD using hgb
  intro j
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * D (j - i),
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB0 i)) (hD0 (j - i))), ?_⟩
  intro a x hx
  have hbound := norm_iteratedFDerivWithin_mul_le (hf a) (hg a) hU.uniqueDiffOn
    (hS hx) (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
  simp only [iteratedFDerivWithin_of_isOpen _ hU (hS hx)] at hbound
  apply hbound.trans
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (hB i a x hx) (Nat.cast_nonneg (j.choose i)))
    (hD (j - i) a x hx) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg (j.choose i)) (hB0 i))

/-- A norm-at-most-one linear projection does not enlarge an actual
jet. In particular a current-time spatial profile can be regarded as a
joint space-displacement profile with the same bound. -/
theorem norm_jet_comp_linear_le {f : E → ℝ} {U : Set E}
    (L : F →L[ℝ] E) (hL : ‖L‖ ≤ 1) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {x : F} (hx : L x ∈ U) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y => f (L y)) x‖ ≤
      ‖iteratedFDeriv ℝ j f (L x)‖ := by
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have heq := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn
    hpre.uniqueDiffOn hx (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
  rw [iteratedFDerivWithin_of_isOpen _ hpre hx,
    iteratedFDerivWithin_of_isOpen _ hU hx] at heq
  rw [show (fun y => f (L y)) = f ∘ L from rfl, heq]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hp : (∏ _i : Fin j, ‖L‖) ≤ 1 := by
    simpa only [Finset.prod_const_one] using
      Finset.prod_le_prod (fun _ _ => norm_nonneg L) (fun _ _ => hL)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg _)

/-- A fixed pointwise weight is preserved by subtraction of actual
jets; the weight itself is never differentiated. -/
theorem family_weighted_jet_bounds_sub {f g : A → E → ℝ} {U S : Set E} {w : E → ℝ}
    (hU : IsOpen U) (hS : S ⊆ U) (hw : ∀ x ∈ S, 0 ≤ w x)
    (hf : ∀ a, ContDiffOn ℝ ∞ (f a) U) (hg : ∀ a, ContDiffOn ℝ ∞ (g a) U)
    (hfb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ S →
      w x * ‖iteratedFDeriv ℝ j (f a) x‖ ≤ C)
    (hgb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ S →
      w x * ‖iteratedFDeriv ℝ j (g a) x‖ ≤ C) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ S →
      w x * ‖iteratedFDeriv ℝ j (fun y => f a y - g a y) x‖ ≤ C := by
  intro j
  obtain ⟨C, hC, hCb⟩ := hfb j
  obtain ⟨D, hD, hDb⟩ := hgb j
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  intro a x hx
  have hj : (j : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  rw [fun_iteratedFDeriv_sub_apply
    (((hf a x (hS hx)).contDiffAt (hU.mem_nhds (hS hx))).of_le hj)
    (((hg a x (hS hx)).contDiffAt (hU.mem_nhds (hS hx))).of_le hj)]
  have hn := mul_le_mul_of_nonneg_left (norm_sub_le
    (iteratedFDeriv ℝ j (f a) x) (iteratedFDeriv ℝ j (g a) x)) (hw x hx)
  nlinarith only [hn, hCb a x hx, hDb a x hx]

theorem family_weighted_jet_bounds_const_mul {f : A → E → ℝ} {U S : Set E}
    {w : E → ℝ} (hU : IsOpen U) (hS : S ⊆ U)
    (hf : ∀ a, ContDiffOn ℝ ∞ (f a) U)
    (hfb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ S →
      w x * ‖iteratedFDeriv ℝ j (f a) x‖ ≤ C) (b : ℝ) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ S →
      w x * ‖iteratedFDeriv ℝ j (fun y => b * f a y) x‖ ≤ C := by
  intro j
  obtain ⟨C, hC, hCb⟩ := hfb j
  refine ⟨|b| * C, mul_nonneg (abs_nonneg b) hC, ?_⟩
  intro a x hx
  have hj : (j : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  have hd := iteratedFDeriv_const_smul_apply' (a := b)
    (((hf a x (hS hx)).contDiffAt (hU.mem_nhds (hS hx))).of_le hj)
  simp only [smul_eq_mul] at hd
  rw [hd, norm_smul, Real.norm_eq_abs]
  have hm := mul_le_mul_of_nonneg_left (hCb a x hx) (abs_nonneg b)
  convert! hm using 1
  ring

/-- Weighted actual jets of one factor and bounded actual jets of the
other preserve the same weight under the genuine binomial product rule. -/
theorem family_weighted_jet_bounds_mul {f g : A → E → ℝ} {U S : Set E} {w : E → ℝ}
    (hU : IsOpen U) (hS : S ⊆ U) (hw : ∀ x ∈ S, 0 ≤ w x)
    (hf : ∀ a, ContDiffOn ℝ ∞ (f a) U) (hg : ∀ a, ContDiffOn ℝ ∞ (g a) U)
    (hfb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ S →
      w x * ‖iteratedFDeriv ℝ j (f a) x‖ ≤ C)
    (hgb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ S →
      ‖iteratedFDeriv ℝ j (g a) x‖ ≤ C) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ S →
      w x * ‖iteratedFDeriv ℝ j (fun y => f a y * g a y) x‖ ≤ C := by
  classical
  choose B hB0 hB using hfb
  choose D hD0 hD using hgb
  intro j
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * D (j - i),
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB0 i)) (hD0 (j - i))), ?_⟩
  intro a x hx
  have hbound := norm_iteratedFDerivWithin_mul_le (hf a) (hg a) hU.uniqueDiffOn
    (hS hx) (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
  simp only [iteratedFDerivWithin_of_isOpen _ hU (hS hx)] at hbound
  apply (mul_le_mul_of_nonneg_left hbound (hw x hx)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hm := mul_le_mul
    (mul_le_mul_of_nonneg_left (hB i a x hx) (Nat.cast_nonneg (j.choose i)))
    (hD (j - i) a x hx) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg (j.choose i)) (hB0 i))
  convert! hm using 1
  ring

end PoincareMT.M35.RadialGauge
