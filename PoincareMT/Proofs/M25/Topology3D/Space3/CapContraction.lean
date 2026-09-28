import PoincareMT.Proofs.M25.Topology3D.Space3.FieldLocalization
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# A contraction field tangent to a spherical cap

The explicit field points inward on the unit sphere, is tangent on a
chosen polar cap, and uniformly attracts the closed ball toward the
cap center. These are the local estimates for Hatcher's relative disc
move, Notes on Basic 3-Manifold Topology, Lemma 1.3, p. 3. Invariance
and transport through shared cap charts are separate steps.
See `derivations/2026-09-21-relative-ball-shrinking.md` in the task records.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace

namespace PoincareMT.M25.Topology3D

/-- A smooth cutoff is zero below half-height and one throughout the
retained cap heights, with values in the unit interval. -/
theorem exists_capContraction_cutoff (a : ℝ) (ha : 1 / 2 < a) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ z, χ z ∈ Icc 0 1) ∧
      (∀ z, z ≤ 1 / 2 → χ z = 0) ∧
      ∀ z ∈ Icc a 1, χ z = 1 := by
  obtain ⟨χ, hχ, _, hs, hnear, hrange⟩ := exists_compact_smooth_cutoff
    (K := Icc a 1) (U := Ioi (1 / 2 : ℝ)) isCompact_Icc isOpen_Ioi
    (fun _ hz => ha.trans_le hz.1)
  refine ⟨χ, hχ, hrange, ?_, ?_⟩
  · intro z hz
    apply image_eq_zero_of_notMem_tsupport
    intro hzs
    have hgt := hs hzs
    exact (not_lt_of_ge hz) hgt
  · intro z hz
    exact (eventually_nhdsSet_iff_forall.mp hnear z hz).self_of_nhds

/-- The interpolation coefficient between central and cap-tangent
contraction, depending only on height. -/
def capContractionCoefficient (χ : ℝ → ℝ) (z : ℝ) : ℝ := 1 - χ z * (1 - z)

/-- On heights at most one, the coefficient is at least one half,
at most one, and no smaller than the height. -/
theorem capContractionCoefficient_bounds (χ : ℝ → ℝ)
    (hχ : ∀ z, χ z ∈ Icc 0 1) (hzero : ∀ z, z ≤ 1 / 2 → χ z = 0)
    (z : ℝ) (hz : z ≤ 1) :
    1 / 2 ≤ capContractionCoefficient χ z ∧
      capContractionCoefficient χ z ≤ 1 ∧ z ≤ capContractionCoefficient χ z := by
  by_cases hhalf : z ≤ 1 / 2
  · simp only [capContractionCoefficient, hzero z hhalf, zero_mul, sub_zero]
    exact ⟨by norm_num, le_rfl, hz⟩
  · have hlow := mul_nonneg (hχ z).1 (sub_nonneg.mpr hz)
    have hupp := mul_le_mul_of_nonneg_right (hχ z).2 (sub_nonneg.mpr hz)
    dsimp [capContractionCoefficient]
    constructor
    · linarith
    · constructor <;> linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unit ball contracts toward u, with its polar cap moving
tangentially when the cutoff is one. -/
noncomputable def capContractionField (χ : ℝ → ℝ) (u x : E) : E :=
  u - capContractionCoefficient χ ⟪u, x⟫_ℝ • x

/-- Smoothness of the scalar cutoff gives a globally smooth model field. -/
theorem capContractionField_contDiff (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (u : E) :
    ContDiff ℝ ∞ (capContractionField χ u) := by
  have hz : ContDiff ℝ ∞ (fun x : E => ⟪u, x⟫_ℝ) := (innerSL ℝ u).contDiff
  exact contDiff_const.sub
    ((contDiff_const.sub ((hχ.comp hz).mul (contDiff_const.sub hz))).smul contDiff_id)

/-- The radial component of the cap contraction is explicit. -/
theorem capContractionField_radial (χ : ℝ → ℝ) (u x : E) :
    ⟪x, capContractionField χ u x⟫_ℝ =
      ⟪u, x⟫_ℝ - capContractionCoefficient χ ⟪u, x⟫_ℝ * ‖x‖ ^ 2 := by
  simp only [capContractionField, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm x u]

/-- The field points inward on the entire unit sphere. -/
theorem capContractionField_inward (χ : ℝ → ℝ)
    (hχ : ∀ z, χ z ∈ Icc 0 1) (hzero : ∀ z, z ≤ 1 / 2 → χ z = 0)
    (u : E) (hu : ‖u‖ = 1) (x : E) (hx : ‖x‖ = 1) :
    ⟪x, capContractionField χ u x⟫_ℝ ≤ 0 := by
  have hz : ⟪u, x⟫_ℝ ≤ 1 := by simpa only [hu, hx, one_mul] using real_inner_le_norm u x
  have hb := (capContractionCoefficient_bounds χ hχ hzero _ hz).2.2
  rw [capContractionField_radial, hx, one_pow, mul_one]
  linarith

/-- On the retained cap the inward radial component vanishes exactly. -/
theorem capContractionField_tangent (χ : ℝ → ℝ) (u x : E)
    (hx : ‖x‖ = 1) (hcap : χ ⟪u, x⟫_ℝ = 1) :
    ⟪x, capContractionField χ u x⟫_ℝ = 0 := by
  rw [capContractionField_radial, capContractionCoefficient, hcap, hx]
  ring

/-- Squared distance to the cap center strictly contracts away from
that center, uniformly throughout the closed unit ball. -/
theorem capContractionField_attraction (χ : ℝ → ℝ)
    (hχ : ∀ z, χ z ∈ Icc 0 1) (hzero : ∀ z, z ≤ 1 / 2 → χ z = 0)
    (u : E) (hu : ‖u‖ = 1) (x : E) (hx : ‖x‖ ≤ 1) :
    ⟪x - u, capContractionField χ u x⟫_ℝ ≤ -(1 / 2) * ‖x - u‖ ^ 2 := by
  have hz : ⟪u, x⟫_ℝ ≤ 1 := by
    have h := real_inner_le_norm u x
    rw [hu, one_mul] at h
    exact h.trans hx
  obtain ⟨hlow, hupp, _⟩ := capContractionCoefficient_bounds χ hχ hzero _ hz
  have heq : ⟪x - u, capContractionField χ u x⟫_ℝ =
      (1 - capContractionCoefficient χ ⟪u, x⟫_ℝ) * (⟪u, x⟫_ℝ - 1) -
        capContractionCoefficient χ ⟪u, x⟫_ℝ * ‖x - u‖ ^ 2 := by
    simp only [capContractionField, inner_sub_left, inner_sub_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq, norm_sub_sq_real,
      hu, real_inner_comm x u]
    ring
  rw [heq]
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hupp) (sub_nonpos.mpr hz)
  have hlowmul := mul_le_mul_of_nonneg_right hlow (sq_nonneg ‖x - u‖)
  linarith

end PoincareMT.M25.Topology3D
