import PoincareMT.Proofs.M25.Topology3D.Space3.StereographicCap

/-!
# Complementary round stereographic discs

The cap formula is valid for every positive radius, including the large
disc at the opposite pole. Mathlib's scale-two stereographic convention
makes the complementary radius equal to `4 / r`. These exact image and
boundary identities implement the reviewed source-sphere-disc-split
derivation of 2026-09-22, for Hatcher, Notes on Basic 3-Manifold Topology,
Theorem 1.1 and Lemma 1.3, pp. 1-3.
-/

set_option autoImplicit false

open Set Metric
open scoped InnerProductSpace

namespace PoincareMT.M25.Topology3D

/-- Every positive finite stereographic radius has cap height strictly
between the two pole heights. -/
theorem stereographicCapHeight_mem_unit_interval {r : ℝ} (hr : 0 < r) :
    stereographicCapHeight r ∈ Ioo (-1 : ℝ) 1 := by
  have hd : 0 < 4 + r ^ 2 := by positivity
  constructor
  · change -1 < (4 - r ^ 2) / (4 + r ^ 2)
    apply (lt_div_iff₀ hd).mpr
    nlinarith
  · change (4 - r ^ 2) / (4 + r ^ 2) < 1
    apply (div_lt_one hd).mpr
    nlinarith [sq_pos_of_pos hr]

/-- Opposite-pole stereographic discs have reciprocal radii with
factor four in Mathlib's scale-two convention. -/
theorem stereographicCapHeight_complement {r : ℝ} (hr : 0 < r) :
    stereographicCapHeight (4 / r) = -stereographicCapHeight r := by
  have hd : 4 + r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hD : 4 + (4 / r) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold stereographicCapHeight
  field_simp [hr.ne', hd, hD]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The closed-disc cap image holds at every positive radius. In
particular it includes the large disc used at the opposite pole. -/
theorem stereoInvFun_image_closedBall_pos (v : E) (hv : ‖v‖ = 1) {r : ℝ}
    (hr : 0 < r) :
    (fun w => (stereoInvFun hv w : E)) '' closedBall 0 r =
      {y : E | ‖y‖ = 1 ∧ stereographicCapHeight r ≤ ⟪-v, y⟫_ℝ} := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨norm_eq_of_mem_sphere _, (stereoInvFun_cap_iff v hv hr.le w).mpr hw⟩
  · rintro ⟨hynorm, hycap⟩
    have hyv : y ≠ v := by
      intro heq
      rw [heq, inner_neg_left, real_inner_self_eq_norm_sq, hv] at hycap
      have ha := (stereographicCapHeight_mem_unit_interval hr).1
      norm_num at hycap
      linarith
    let q : sphere (0 : E) 1 := ⟨y, mem_sphere_zero_iff_norm.mpr hynorm⟩
    have heq : (stereoInvFun hv (stereoToFun v y) : E) = y :=
      congrArg Subtype.val (stereo_left_inv hv (x := q) hyv)
    refine ⟨stereoToFun v y, ?_, heq⟩
    apply (stereoInvFun_cap_iff v hv hr.le _).mp
    rwa [heq]

/-- A stereographic point has exactly the boundary cap height if and
only if its planar norm is the prescribed nonnegative radius. -/
theorem stereoInvFun_cap_eq_iff (v : E) (hv : ‖v‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (w : (ℝ ∙ v)ᗮ) :
    stereographicCapHeight r = ⟪-v, (stereoInvFun hv w : E)⟫_ℝ ↔ w ∈ sphere 0 r := by
  rw [stereoInvFun_opposite_height, mem_sphere_zero_iff_norm]
  have hd : 4 + r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hw : 4 + ‖w‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold stereographicCapHeight
  rw [div_eq_div_iff hd hw]
  constructor
  · intro h
    nlinarith [norm_nonneg w]
  · intro h
    rw [h]

/-- The boundary circle of every positive stereographic disc is the
entire corresponding latitude, including surjectivity on the latitude. -/
theorem stereoInvFun_image_sphere_pos (v : E) (hv : ‖v‖ = 1) {r : ℝ}
    (hr : 0 < r) :
    (fun w => (stereoInvFun hv w : E)) '' sphere 0 r =
      {y : E | ‖y‖ = 1 ∧ stereographicCapHeight r = ⟪-v, y⟫_ℝ} := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨norm_eq_of_mem_sphere _, (stereoInvFun_cap_eq_iff v hv hr.le w).mpr hw⟩
  · rintro ⟨hynorm, hycap⟩
    have hyclosed : y ∈ (fun w => (stereoInvFun hv w : E)) '' closedBall 0 r := by
      rw [stereoInvFun_image_closedBall_pos v hv hr]
      exact ⟨hynorm, hycap.le⟩
    obtain ⟨w, _, rfl⟩ := hyclosed
    exact ⟨w, (stereoInvFun_cap_eq_iff v hv hr.le w).mp hycap, rfl⟩

end PoincareMT.M25.Topology3D
