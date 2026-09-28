import PoincareMT.Proofs.M25.Topology3D.Space3.BoundaryDiscCoordinates

/-!
# Round stereographic discs are spherical caps

Mathlib's stereographic inverse has denominator `norm(w)^2 + 4`.
The radius-r disc therefore has cap height `(4-r^2)/(4+r^2)` about
the opposite pole. For `0 < r <= 1` this height lies strictly between
one half and one, matching the retained-cap contraction lemmas.
This is the explicit cap convention for Hatcher, Notes on Basic
3-Manifold Topology, Lemma 1.3, p. 3.
-/

set_option autoImplicit false

open Set Metric
open scoped InnerProductSpace

namespace PoincareMT.M25.Topology3D

/-- Height of the spherical cap represented by a round stereographic disc. -/
noncomputable def stereographicCapHeight (r : ℝ) : ℝ := (4 - r ^ 2) / (4 + r ^ 2)

/-- A positive disc of radius at most one gives the small-cap thresholds
used by the relative ball contraction. -/
theorem stereographicCapHeight_mem_Ioo {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    stereographicCapHeight r ∈ Ioo (1 / 2 : ℝ) 1 := by
  have hd : 0 < 4 + r ^ 2 := by positivity
  have hrSq : r ^ 2 ≤ 1 := by simpa only [one_pow] using (sq_le_sq₀ hr.le zero_le_one).mpr hr1
  change 1 / 2 < (4 - r ^ 2) / (4 + r ^ 2) ∧ (4 - r ^ 2) / (4 + r ^ 2) < 1
  constructor
  · apply (lt_div_iff₀ hd).mpr
    nlinarith
  · apply (div_lt_one hd).mpr
    nlinarith [sq_pos_of_pos hr]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact height of a stereographic point above the opposite pole. -/
theorem stereoInvFun_opposite_height (v : E) (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) :
    ⟪-v, (stereoInvFun hv w : E)⟫_ℝ = stereographicCapHeight ‖w‖ := by
  have hw : ⟪v, (w : E)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
  rw [stereoInvFun_apply, inner_neg_left, real_inner_smul_right, inner_add_right,
    real_inner_smul_right, real_inner_smul_right, hw, real_inner_self_eq_norm_sq, hv]
  simp only [mul_zero, one_pow, mul_one, zero_add, stereographicCapHeight]
  ring

/-- A stereographic point lies in the cap exactly when its plane
coordinate lies in the corresponding closed disc. -/
theorem stereoInvFun_cap_iff (v : E) (hv : ‖v‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (w : (ℝ ∙ v)ᗮ) :
    stereographicCapHeight r ≤ ⟪-v, (stereoInvFun hv w : E)⟫_ℝ ↔ w ∈ closedBall 0 r := by
  rw [stereoInvFun_opposite_height v hv w, mem_closedBall_zero_iff]
  have hd : 0 < 4 + r ^ 2 := by positivity
  have hw : 0 < 4 + ‖w‖ ^ 2 := by positivity
  rw [stereographicCapHeight, stereographicCapHeight, div_le_div_iff₀ hd hw]
  constructor
  · intro h
    apply (sq_le_sq₀ (norm_nonneg w) hr).mp
    nlinarith
  · intro h
    have hsq := (sq_le_sq₀ (norm_nonneg w) hr).mpr h
    nlinarith

/-- The entire closed stereographic disc is precisely the indicated
spherical cap, with no missing pole or boundary points. -/
theorem stereoInvFun_image_closedBall (v : E) (hv : ‖v‖ = 1) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
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
      have ha := (stereographicCapHeight_mem_Ioo hr hr1).1
      norm_num at hycap
      linarith
    let q : sphere (0 : E) 1 := ⟨y, mem_sphere_zero_iff_norm.mpr hynorm⟩
    have heq : (stereoInvFun hv (stereoToFun v y) : E) = y :=
      congrArg Subtype.val (stereo_left_inv hv (x := q) hyv)
    refine ⟨stereoToFun v y, ?_, heq⟩
    apply (stereoInvFun_cap_iff v hv hr.le _).mp
    rwa [heq]

end PoincareMT.M25.Topology3D
