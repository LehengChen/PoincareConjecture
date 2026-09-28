import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Tangent fields with unit height speed

Project a fixed height direction onto a normal's perpendicular plane,
then divide by its squared norm. The field annihilates the defining
function and has unit height derivative wherever the projected vector
is nonzero. This is the field for Hatcher's regular tubes, Notes on
Basic 3-Manifold Topology, Theorem 1.1 and Lemma 1.2, pp. 1-3.
-/

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareMT.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The component of a height vector tangent to a given normal plane;
the normal is not required to have unit length. -/
noncomputable def tangentHeightVector (n u : E) : E :=
  u - (⟪n, u⟫ / ⟪n, n⟫) • n

/-- The projected vector is perpendicular to the nonzero normal. -/
theorem tangentHeightVector_normal (n u : E) (hn : n ≠ 0) :
    ⟪n, tangentHeightVector n u⟫ = 0 := by
  rw [tangentHeightVector, inner_sub_right, inner_smul_right,
    div_mul_cancel₀ _ (inner_self_ne_zero.mpr hn), sub_self]

/-- Height paired with its tangent component is the component's squared
norm; Hatcher's regular-height normalization, Lemma 1.2. -/
theorem tangentHeightVector_height (n u : E) (hn : n ≠ 0) :
    ⟪u, tangentHeightVector n u⟫ =
      ⟪tangentHeightVector n u, tangentHeightVector n u⟫ := by
  conv_rhs => lhs; unfold tangentHeightVector
  rw [inner_sub_left, real_inner_smul_left, tangentHeightVector_normal n u hn,
    mul_zero, sub_zero]

/-- Normalize the tangent height vector to have unit height speed away
from height critical points; Hatcher's no-critical-level construction. -/
noncomputable def tangentHeightField (n u : E) : E :=
  (⟪tangentHeightVector n u, tangentHeightVector n u⟫)⁻¹ • tangentHeightVector n u

/-- The normalized height field is tangent to the normal plane. -/
theorem tangentHeightField_normal (n u : E) (hn : n ≠ 0) :
    ⟪n, tangentHeightField n u⟫ = 0 := by
  rw [tangentHeightField, inner_smul_right, tangentHeightVector_normal n u hn, mul_zero]

/-- The normalized field has height derivative one when both the normal
and its projected height direction are nonzero. -/
theorem tangentHeightField_height (n u : E) (hn : n ≠ 0)
    (hw : tangentHeightVector n u ≠ 0) : ⟪u, tangentHeightField n u⟫ = 1 := by
  rw [tangentHeightField, inner_smul_right, tangentHeightVector_height n u hn,
    inv_mul_cancel₀ (inner_self_ne_zero.mpr hw)]

/-- The projected field varies smoothly with a smooth nonvanishing
normal field. The scalar denominators are explicitly kept nonzero. -/
theorem tangentHeightVector_contDiffOn {U : Set E} (n : E → E)
    (hn : ContDiffOn ℝ ∞ n U) (hn0 : ∀ x ∈ U, n x ≠ 0) (u : E) :
    ContDiffOn ℝ ∞ (fun x => tangentHeightVector (n x) u) U := by
  exact contDiffOn_const.sub (((hn.inner ℝ contDiffOn_const).div (hn.inner ℝ hn)
    (fun x hx => inner_self_ne_zero.mpr (hn0 x hx))).smul hn)

/-- Normalization is smooth on the domain without height critical points. -/
theorem tangentHeightField_contDiffOn {U : Set E} (n : E → E)
    (hn : ContDiffOn ℝ ∞ n U) (hn0 : ∀ x ∈ U, n x ≠ 0) (u : E)
    (hw0 : ∀ x ∈ U, tangentHeightVector (n x) u ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => tangentHeightField (n x) u) U := by
  have hw := tangentHeightVector_contDiffOn n hn hn0 u
  exact ((hw.inner ℝ hw).inv (fun x hx => inner_self_ne_zero.mpr (hw0 x hx))).smul hw

/-- A gradient normal identifies tangency with the vanishing derivative
of the defining function. The identity is used on its smooth domain. -/
theorem tangentHeightField_defining_derivative [CompleteSpace E]
    (ρ : E → ℝ) (x u : E) (hn : gradient ρ x ≠ 0) :
    fderiv ℝ ρ x (tangentHeightField (gradient ρ x) u) = 0 := by
  rw [← inner_gradient_left]
  exact tangentHeightField_normal _ _ hn

/-- The gradient of a smooth defining function is smooth on its open
domain, using the continuous linear Riesz correspondence. -/
theorem contDiffOn_gradient_of_isOpen [CompleteSpace E] {U : Set E}
    (hU : IsOpen U) (ρ : E → ℝ) (hρ : ContDiffOn ℝ ∞ ρ U) :
    ContDiffOn ℝ ∞ (gradient ρ) U := by
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (hρ.fderiv_of_isOpen hU (by simp))

/-- Multiplying the field by a scalar cutoff retains tangency and
changes the height derivative to exactly that cutoff value. -/
theorem tangentHeightField_cutoff (n u : E) (hn : n ≠ 0)
    (hw : tangentHeightVector n u ≠ 0) (a : ℝ) :
    ⟪n, a • tangentHeightField n u⟫ = 0 ∧
      ⟪u, a • tangentHeightField n u⟫ = a := by
  simp only [inner_smul_right, tangentHeightField_normal n u hn,
    tangentHeightField_height n u hn hw, mul_zero, mul_one, and_self]

end PoincareMT.M25.Topology3D
