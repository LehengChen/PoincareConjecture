import PoincareMT.Proofs.M25.AppA_1_Necks.SphereAxialDerivative
import PoincareMT.Proofs.M25.AppA_1_Necks.SphereSliceControl
import PoincareMT.Proofs.M25.AppA_1_Necks.OverlapSlab
import Mathlib.Analysis.Calculus.MeanValue

/-!
# One orthogonal sphere map on a bounded overlap slab

Slow axial sphere motion compares every retained height with one anchor
slice. The anchor's orthogonal map therefore gives uniform C0 control on
the whole closed slab. This is the sphere component of the bounded-slab
transition in MT A.11(3),(5), pp. 503-504; see the reviewed
slab-sphere-control derivation. Derivative comparison with that map is
not asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.EpsilonNeck

/-- One orthogonal map approximates the sphere component throughout a
whole retained slab, including its closed endpoints and zero width.
The threshold precedes the geometry and anchor height; MT A.11(3),(5),
pp. 503-504. This is a C0 estimate in the Euclidean inclusion norm. -/
theorem exists_contained_slab_orthogonal_control {L ζ : ℝ} (hL : 0 ≤ L) (hζ : 0 < ζ) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 → ∀ s0 : ℝ,
      univ ×ˢ Icc (s0 - L) (s0 + L) ⊆
        N.cylinderDomain ∩ N.coordinate_map ⁻¹' N'.carrier →
      ∃ A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
        ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Icc (s0 - L) (s0 + L) →
          ‖(N'.coordinate_inverse (N.coordinate_map (q, s))).1.1 - A q.1‖ < ζ := by
  let η := ζ / (4 * (L + 1))
  have hη : 0 < η := div_pos hζ (by positivity)
  have hbudget : η * L ≤ ζ / 4 := by
    have h := div_mul_cancel₀ ζ (show 4 * (L + 1) ≠ 0 by positivity)
    change η * (4 * (L + 1)) = ζ at h
    nlinarith
  obtain ⟨εa, hapos, hacap, haxis⟩ :=
    exists_intersecting_transition_sphere_axial_bound.{u} hη
  obtain ⟨εf, hfpos, _, hframe⟩ :=
    exists_contained_slice_orthogonal_control.{u} (half_pos hζ)
  refine ⟨min εa εf, lt_min hapos hfpos, (min_le_left _ _).trans hacap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' s0 hsub
  have hs0 : s0 ∈ Icc (s0 - L) (s0 + L) := ⟨by linarith, by linarith⟩
  have hs0N : s0 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (hsub (show ((N.coordinate_inverse N.center).1, s0) ∈
      univ ×ˢ Icc (s0 - L) (s0 + L) from ⟨mem_univ _, hs0⟩)).1.2
  obtain ⟨A, hA⟩ := hframe N N' (hN.trans (min_le_right _ _))
    (hN'.trans (min_le_right _ _)) s0 hs0N
    (fun q => (hsub (show (q, s0) ∈ univ ×ˢ Icc (s0 - L) (s0 + L)
      from ⟨mem_univ q, hs0⟩)).2)
  refine ⟨A, ?_⟩
  intro q s hs
  let F : ℝ → EuclideanSpace ℝ (Fin 3) :=
    fun t => (N'.coordinate_inverse (N.coordinate_map (q, t))).1.1
  have hdiff (t : ℝ) (ht : t ∈ Icc (s0 - L) (s0 + L)) : DifferentiableAt ℝ F t := by
    have hz := hsub (show (q, t) ∈ univ ×ˢ Icc (s0 - L) (s0 + L)
      from ⟨mem_univ q, ht⟩)
    exact N.differentiableAt_transition_sphere_axial N' hz.1 hz.2
  have hbound (t : ℝ) (ht : t ∈ Icc (s0 - L) (s0 + L)) : ‖deriv F t‖ ≤ η := by
    have hz := hsub (show (q, t) ∈ univ ×ˢ Icc (s0 - L) (s0 + L)
      from ⟨mem_univ q, ht⟩)
    exact (haxis N N' (hN.trans (min_le_left _ _)) (hN'.trans (min_le_left _ _))
      (q, t) hz.1 hz.2).le
  have hlength : ‖s - s0‖ ≤ L := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hdisp : ‖F s - F s0‖ ≤ ζ / 4 :=
    (Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (convex_Icc (s0 - L) (s0 + L)) hs0 hs).trans
      ((mul_le_mul_of_nonneg_left hlength hη.le).trans hbudget)
  calc
    ‖F s - A q.1‖ = ‖(F s - F s0) + (F s0 - A q.1)‖ := by congr 1; abel
    _ ≤ ‖F s - F s0‖ + ‖F s0 - A q.1‖ := norm_add_le _ _
    _ < ζ / 4 + ζ / 2 := add_lt_add_of_le_of_lt hdisp (hA q)
    _ < ζ := by linarith

/-- A fixed-width slab about a middle-region center admits one uniformly
close orthogonal sphere map. The actual slab containment is supplied by
the overlap theorem; MT A.11(3),(5), pp. 503-504. -/
theorem exists_middle_overlap_slab_orthogonal_control {L κ ζ : ℝ}
    (hL : 0 ≤ L) (hκ : κ ∈ Ioc 0 1) (hζ : 0 < ζ) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 → N'.center ∈ N.carrier →
      |(N.coordinate_inverse N'.center).2| ≤ (1 - κ) * N.epsilon⁻¹ →
      ∃ A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
        ∀ (q : UnitTwoSphere) (s : ℝ),
          s ∈ Icc ((N.coordinate_inverse N'.center).2 - L)
            ((N.coordinate_inverse N'.center).2 + L) →
          ‖(N'.coordinate_inverse (N.coordinate_map (q, s))).1.1 - A q.1‖ < ζ := by
  obtain ⟨εb, hbpos, hbcap, hslab⟩ := exists_middle_overlap_slab.{u} hL hκ
  obtain ⟨εf, hfpos, _, hframe⟩ := exists_contained_slab_orthogonal_control.{u} hL hζ
  refine ⟨min εb εf, lt_min hbpos hfpos, (min_le_left _ _).trans hbcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' hcenter hmiddle
  exact hframe N N' (hN.trans (min_le_right _ _)) (hN'.trans (min_le_right _ _)) _
    (hslab N N' (hN.trans (min_le_left _ _)) (hN'.trans (min_le_left _ _)) hcenter hmiddle)

end PoincareMT.EpsilonNeck
