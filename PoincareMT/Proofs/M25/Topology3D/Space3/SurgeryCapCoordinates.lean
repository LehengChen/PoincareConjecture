import PoincareMT.Proofs.M25.Topology3D.Space3.CircleRadialChart
import PoincareMT.Proofs.M25.Topology3D.Space3.FlatCapModel
import PoincareMT.Proofs.M25.Topology3D.Space3.NorthSphereCoordinates
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Southern rounded-cap coordinates for regular-disc surgery

The actual flat-cap ambient diffeomorphism restricts to the native unit
sphere. Its horizontal radius stays at most one, its equatorial band is
an exact cylinder, and its southern polar patch is an exact flat disc.
Positive vertical scaling preserves the original height sign; compactness
bounds its absolute height without any monotonicity assumption.

The affine placement retains these coordinates before composition with
the horizontal tube chart. Source: equations (7)-(8) and the preceding
profile bounds in
`proof-work/tasks/M25/schoenflies/derivations/2026-09-22-regular-disc-surgery.md`,
following Hatcher, Notes on Basic 3-Manifold Topology, Theorem 1.1 and
Lemma 1.3, pp. 1-3.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareMT.M25.Topology3D

variable (a : ℝ → ℝ) (b : E2 → ℝ)
variable (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
variable (ha0 : ∀ z, a z ≠ 0) (hb0 : ∀ x, b x ≠ 0)

/-- The rounded-cap model on the actual unit sphere, before affine
placement in the horizontal tube chart. -/
noncomputable def surgeryCapModel (q : UnitTwoSphere) : E2 × ℝ :=
  flatCapDiffeomorph a b ha hb ha0 hb0 (heightCoordinates (q : E3))

/-- The cap model is smooth for the existing sphere smooth structure. -/
theorem surgeryCapModel_contMDiff :
    ContMDiff (𝓡 2) 𝓘(ℝ, E2 × ℝ) ∞ (surgeryCapModel a b ha hb ha0 hb0) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  exact (flatCapDiffeomorph a b ha hb ha0 hb0).contMDiff_toFun.comp
    (heightCoordinates.contDiff.contMDiff.comp contMDiff_coe_sphere)

/-- The horizontal profile upper bound keeps the whole model sphere
inside the closed unit-disc cylinder. -/
theorem surgeryCapModel_fst_norm_le
    (hapos : ∀ z, 0 < a z)
    (habound : ∀ z, |z| < 1 → a z ≤ (Real.sqrt (1 - z ^ 2))⁻¹)
    (q : UnitTwoSphere) :
    ‖(surgeryCapModel a b ha hb ha0 hb0 q).1‖ ≤ 1 :=
  flatCapDiffeomorph_fst_norm_le a b ha hb ha0 hb0 hapos habound
    (heightCoordinates (q : E3)) (sphere_height_coordinates_sq q).le

/-- On the equatorial band the model retains the original height and
has horizontal coordinate equal to the actual circle direction. -/
theorem surgeryCapModel_cylinder
    (hanear : ∀ z, |z| ≤ 1 / 4 → a z = (Real.sqrt (1 - z ^ 2))⁻¹)
    (hbfar : ∀ x, 1 / 2 ≤ ‖x‖ → b x = 1)
    (q : UnitTwoSphere) (hq : |(heightCoordinates (q : E3)).2| ≤ 1 / 4) :
    surgeryCapModel a b ha hb ha0 hb0 q =
      ((circleDirection (heightCoordinates (q : E3)).1 : E2),
        (heightCoordinates (q : E3)).2) := by
  let x := (heightCoordinates (q : E3)).1
  let z := (heightCoordinates (q : E3)).2
  have hunit : ‖x‖ ^ 2 + z ^ 2 = 1 := sphere_height_coordinates_sq q
  have hr : Real.sqrt (1 - z ^ 2) = ‖x‖ := by
    rw [show 1 - z ^ 2 = ‖x‖ ^ 2 by linarith, Real.sqrt_sq (norm_nonneg x)]
  have hx : Real.sqrt (1 - z ^ 2) • (circleDirection x : E2) = x := by
    rw [hr]
    exact circleDirection_norm_smul x
  have h := flatCapDiffeomorph_cylinder a b ha hb ha0 hb0 hanear hbfar
    (circleDirection x : E2) (norm_eq_of_mem_sphere (circleDirection x)) z hq
  rw [hx] at h
  exact h

/-- The southern polar patch becomes a flat cap at height minus one,
with the original horizontal coordinate unchanged. -/
theorem surgeryCapModel_flat_south
    (hafar : ∀ z, 1 / 2 ≤ |z| → a z = 1)
    (hbnear : ∀ x, ‖x‖ ≤ 1 / 4 → b x = (Real.sqrt (1 - ‖x‖ ^ 2))⁻¹)
    (q : UnitTwoSphere) (hx : ‖(heightCoordinates (q : E3)).1‖ ≤ 1 / 4)
    (hz : (heightCoordinates (q : E3)).2 ≤ 0) :
    surgeryCapModel a b ha hb ha0 hb0 q = ((heightCoordinates (q : E3)).1, -1) := by
  let x := (heightCoordinates (q : E3)).1
  let z := (heightCoordinates (q : E3)).2
  have hunit : ‖x‖ ^ 2 + z ^ 2 = 1 := sphere_height_coordinates_sq q
  have hs : -Real.sqrt (1 - ‖x‖ ^ 2) = z := by
    rw [show 1 - ‖x‖ ^ 2 = z ^ 2 by linarith,
      Real.sqrt_sq_eq_abs, abs_of_nonpos hz, neg_neg]
  have h := flatCapDiffeomorph_cap a b ha hb ha0 hb0 hafar hbnear
    x hx (-1) (by norm_num)
  simpa only [neg_one_mul, hs, surgeryCapModel, x, z, Prod.eta] using h

/-- Positive vertical scaling preserves nonpositive sphere height. -/
theorem surgeryCapModel_snd_nonpos_iff
    (hbpos : ∀ x, 0 < b x) (q : UnitTwoSphere) :
    (surgeryCapModel a b ha hb ha0 hb0 q).2 ≤ 0 ↔
      (heightCoordinates (q : E3)).2 ≤ 0 := by
  change b (a (heightCoordinates (q : E3)).2 • (heightCoordinates (q : E3)).1) *
    (heightCoordinates (q : E3)).2 ≤ 0 ↔ (heightCoordinates (q : E3)).2 ≤ 0
  simpa only [mul_zero] using
    (mul_le_mul_iff_right₀
      (hbpos (a (heightCoordinates (q : E3)).2 • (heightCoordinates (q : E3)).1))
      (b := (heightCoordinates (q : E3)).2) (c := 0))

/-- Positive vertical scaling also preserves strict negative height. -/
theorem surgeryCapModel_snd_neg_iff
    (hbpos : ∀ x, 0 < b x) (q : UnitTwoSphere) :
    (surgeryCapModel a b ha hb ha0 hb0 q).2 < 0 ↔
      (heightCoordinates (q : E3)).2 < 0 := by
  change b (a (heightCoordinates (q : E3)).2 • (heightCoordinates (q : E3)).1) *
    (heightCoordinates (q : E3)).2 < 0 ↔ (heightCoordinates (q : E3)).2 < 0
  simpa only [mul_zero] using
    (mul_lt_mul_iff_right₀
      (hbpos (a (heightCoordinates (q : E3)).2 • (heightCoordinates (q : E3)).1))
      (b := (heightCoordinates (q : E3)).2) (c := 0))

/-- Positive vertical scaling preserves positive height as well. -/
theorem surgeryCapModel_snd_pos_iff
    (hbpos : ∀ x, 0 < b x) (q : UnitTwoSphere) :
    0 < (surgeryCapModel a b ha hb ha0 hb0 q).2 ↔
      0 < (heightCoordinates (q : E3)).2 := by
  change 0 < b (a (heightCoordinates (q : E3)).2 • (heightCoordinates (q : E3)).1) *
    (heightCoordinates (q : E3)).2 ↔ 0 < (heightCoordinates (q : E3)).2
  exact mul_pos_iff_of_pos_left (hbpos _)

/-- Compactness of the native sphere gives a uniform absolute height
bound at least one, without any order property of the height profile. -/
theorem surgeryCapModel_exists_height_bound :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ q : UnitTwoSphere, |(surgeryCapModel a b ha hb ha0 hb0 q).2| ≤ M := by
  have hc : Continuous (fun q : UnitTwoSphere =>
      (surgeryCapModel a b ha hb ha0 hb0 q).2) :=
    (surgeryCapModel_contMDiff a b ha hb ha0 hb0).continuous.snd
  obtain ⟨C, hC⟩ :=
    (isCompact_univ : IsCompact (univ : Set UnitTwoSphere)).exists_bound_of_continuousOn
      hc.continuousOn
  refine ⟨max 1 C, le_max_left _ _, fun q => ?_⟩
  have hq : |(surgeryCapModel a b ha hb ha0 hb0 q).2| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC q (mem_univ q)
  exact hq.trans (le_max_right _ _)

/-- Affine placement of the rounded cap at signed distance `c` from
height `m`, with vertical scale `l`, before applying the tube chart. -/
noncomputable def surgeryCapCoordinates (m sigma c l : ℝ) (q : UnitTwoSphere) : E2 × ℝ :=
  let p := surgeryCapModel a b ha hb ha0 hb0 q
  (p.1, m + sigma * (c + l * p.2))

/-- The affine cap placement is smooth on the whole native sphere. -/
theorem surgeryCapCoordinates_contMDiff (m sigma c l : ℝ) :
    ContMDiff (𝓡 2) 𝓘(ℝ, E2 × ℝ) ∞
      (surgeryCapCoordinates a b ha hb ha0 hb0 m sigma c l) := by
  have h : ContDiff ℝ ∞ (fun p : E2 × ℝ => (p.1, m + sigma * (c + l * p.2))) :=
    contDiff_fst.prodMk (contDiff_const.add
      (contDiff_const.mul (contDiff_const.add (contDiff_const.mul contDiff_snd))))
  exact h.contMDiff.comp (surgeryCapModel_contMDiff a b ha hb ha0 hb0)

/-- Affine vertical placement does not change the horizontal radius bound. -/
theorem surgeryCapCoordinates_fst_norm_le
    (hapos : ∀ z, 0 < a z)
    (habound : ∀ z, |z| < 1 → a z ≤ (Real.sqrt (1 - z ^ 2))⁻¹)
    (m sigma c l : ℝ) (q : UnitTwoSphere) :
    ‖(surgeryCapCoordinates a b ha hb ha0 hb0 m sigma c l q).1‖ ≤ 1 :=
  surgeryCapModel_fst_norm_le a b ha hb ha0 hb0 hapos habound q

/-- The placed cap has the literal cylindrical overlap formula used
to match the northern chart on an open equatorial band. -/
theorem surgeryCapCoordinates_cylinder
    (hanear : ∀ z, |z| ≤ 1 / 4 → a z = (Real.sqrt (1 - z ^ 2))⁻¹)
    (hbfar : ∀ x, 1 / 2 ≤ ‖x‖ → b x = 1)
    (m sigma c l : ℝ) (q : UnitTwoSphere)
    (hq : |(heightCoordinates (q : E3)).2| ≤ 1 / 4) :
    surgeryCapCoordinates a b ha hb ha0 hb0 m sigma c l q =
      ((circleDirection (heightCoordinates (q : E3)).1 : E2),
        m + sigma * (c + l * (heightCoordinates (q : E3)).2)) := by
  unfold surgeryCapCoordinates
  rw [surgeryCapModel_cylinder a b ha hb ha0 hb0 hanear hbfar q hq]

/-- The flat southern patch has constant placed height and retains
the original horizontal disc coordinates. -/
theorem surgeryCapCoordinates_flat_south
    (hafar : ∀ z, 1 / 2 ≤ |z| → a z = 1)
    (hbnear : ∀ x, ‖x‖ ≤ 1 / 4 → b x = (Real.sqrt (1 - ‖x‖ ^ 2))⁻¹)
    (m sigma c l : ℝ) (q : UnitTwoSphere)
    (hx : ‖(heightCoordinates (q : E3)).1‖ ≤ 1 / 4)
    (hz : (heightCoordinates (q : E3)).2 ≤ 0) :
    surgeryCapCoordinates a b ha hb ha0 hb0 m sigma c l q =
      ((heightCoordinates (q : E3)).1, m + sigma * (c - l)) := by
  unfold surgeryCapCoordinates
  rw [surgeryCapModel_flat_south a b ha hb ha0 hb0 hafar hbnear q hx hz]
  simp only [mul_neg_one, sub_eq_add_neg]

/-- For either unit sign, signed displacement from the cutting plane
recovers the unreflected scaled model height. -/
theorem surgeryCapCoordinates_signed_height
    (m sigma c l : ℝ) (hsigma : |sigma| = 1) (q : UnitTwoSphere) :
    sigma * ((surgeryCapCoordinates a b ha hb ha0 hb0 m sigma c l q).2 - m) =
      c + l * (surgeryCapModel a b ha hb ha0 hb0 q).2 := by
  have hs : sigma * sigma = 1 := by nlinarith [sq_abs sigma]
  calc
    sigma * ((surgeryCapCoordinates a b ha hb ha0 hb0 m sigma c l q).2 - m) =
        (sigma * sigma) * (c + l * (surgeryCapModel a b ha hb ha0 hb0 q).2) := by
      dsimp only [surgeryCapCoordinates]
      ring
    _ = c + l * (surgeryCapModel a b ha hb ha0 hb0 q).2 := by rw [hs, one_mul]

/-- A positive sufficiently small vertical scale places every southern
cap point at signed height in `(3*c/4,c]`. -/
theorem surgeryCapCoordinates_south_height_bounds
    (hbpos : ∀ x, 0 < b x)
    (m sigma c l M : ℝ) (hsigma : |sigma| = 1) (hl : 0 < l)
    (hlM : l * M < c / 4)
    (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 ≤ 0)
    (hM : |(surgeryCapModel a b ha hb ha0 hb0 q).2| ≤ M) :
    3 * c / 4 <
        sigma * ((surgeryCapCoordinates a b ha hb ha0 hb0 m sigma c l q).2 - m) ∧
      sigma * ((surgeryCapCoordinates a b ha hb ha0 hb0 m sigma c l q).2 - m) ≤ c := by
  rw [surgeryCapCoordinates_signed_height a b ha hb ha0 hb0 m sigma c l hsigma q]
  have hz := (surgeryCapModel_snd_nonpos_iff a b ha hb ha0 hb0 hbpos q).mpr hq
  have hlo := mul_le_mul_of_nonneg_left (abs_le.mp hM).1 hl.le
  have hhi := mul_nonpos_of_nonneg_of_nonpos hl.le hz
  constructor <;> nlinarith

end PoincareMT.M25.Topology3D
