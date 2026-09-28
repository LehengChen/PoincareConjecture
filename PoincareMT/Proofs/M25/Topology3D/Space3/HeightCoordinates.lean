import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Tactic.FinCases

/-!
# Horizontal and height coordinates in Euclidean three-space

The standard tube and cap models use a horizontal plane times a height.
The continuous linear equivalence below records the Euclidean norm as
a sum of squares, without assigning the product its maximum norm.
These are the coordinates used in Hatcher, Notes on Basic 3-Manifold
Topology, Theorem 1.1 and Lemma 1.2, pp. 1-3.
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold

namespace PoincareMT.M25.Topology3D

/-- The first two coordinates and the final height, using Mathlib's
finite-dimensional product decomposition. -/
noncomputable def heightCoordinates :
    EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) × ℝ :=
  (EuclideanSpace.finAddEquivProd (n := 2) (m := 1)).trans
    ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)))

/-- The horizontal coordinate has the original first two entries. -/
@[simp] theorem heightCoordinates_fst_apply (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 2) :
    (heightCoordinates x).1 i = x i.castSucc := rfl

/-- The height coordinate is the last entry. -/
@[simp] theorem heightCoordinates_snd_apply (x : EuclideanSpace ℝ (Fin 3)) :
    (heightCoordinates x).2 = x 2 := rfl

/-- The inverse stacks the horizontal vector and its height. -/
theorem heightCoordinates_symm_apply (p : EuclideanSpace ℝ (Fin 2) × ℝ) :
    heightCoordinates.symm p = !₂[p.1 0, p.1 1, p.2] := by
  ext i
  fin_cases i <;> rfl

/-- Euclidean norm is the sum of the squared horizontal norm and height. -/
theorem heightCoordinates_norm_sq (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖ ^ 2 = ‖(heightCoordinates x).1‖ ^ 2 + (heightCoordinates x).2 ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_two]
  rfl

/-- The corresponding norm identity for inverse product coordinates. -/
theorem heightCoordinates_symm_norm_sq (p : EuclideanSpace ℝ (Fin 2) × ℝ) :
    ‖heightCoordinates.symm p‖ ^ 2 = ‖p.1‖ ^ 2 + p.2 ^ 2 := by
  simpa only [heightCoordinates.apply_symm_apply] using
    heightCoordinates_norm_sq (heightCoordinates.symm p)

/-- The open Euclidean ball is the strict sum-of-squares region. -/
theorem heightCoordinates_image_ball :
    heightCoordinates '' ball 0 1 =
      {p : EuclideanSpace ℝ (Fin 2) × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 < 1} := by
  ext p
  rw [heightCoordinates.image_eq_preimage_symm, mem_preimage, mem_ball_zero_iff,
    mem_ofPred_eq, ← heightCoordinates_symm_norm_sq]
  constructor <;> intro hp <;> nlinarith [norm_nonneg (heightCoordinates.symm p)]

/-- The closed Euclidean ball is the non-strict sum-of-squares region. -/
theorem heightCoordinates_image_closedBall :
    heightCoordinates '' closedBall 0 1 =
      {p : EuclideanSpace ℝ (Fin 2) × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1} := by
  ext p
  rw [heightCoordinates.image_eq_preimage_symm, mem_preimage, mem_closedBall_zero_iff,
    mem_ofPred_eq, ← heightCoordinates_symm_norm_sq]
  constructor <;> intro hp <;> nlinarith [norm_nonneg (heightCoordinates.symm p)]

/-- The standard sphere is exactly the sum-of-squares level one. -/
theorem heightCoordinates_image_sphere :
    heightCoordinates '' sphere 0 1 =
      {p : EuclideanSpace ℝ (Fin 2) × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 = 1} := by
  ext p
  rw [heightCoordinates.image_eq_preimage_symm, mem_preimage, mem_sphere_zero_iff_norm,
    mem_ofPred_eq, ← heightCoordinates_symm_norm_sq]
  constructor <;> intro hp <;> nlinarith [norm_nonneg (heightCoordinates.symm p)]

end PoincareMT.M25.Topology3D
