import PoincareMT.Proofs.M25.Topology3D.Space3.HeightPlaneProjection
import PoincareMT.Proofs.M25.Topology3D.Space3.ClockSmoothFlow
import PoincareMT.Proofs.M25.Topology3D.Space3.ClockTracks

/-!
# The horizontal field of a retained ambient band field

Project the actual ambient field after reconstructing a point from its
height and planar coordinates. The reconstruction is a continuous linear
equivalence, so compact ambient support gives compact spacetime support.
This is the horizontal regular-band extension in Hatcher, Notes on Basic
3-Manifold Topology, Theorem 1.1 and Lemma 1.2, printed pp. 1-3; see the
reviewed horizontal-regular-band-extension derivation of 2026-09-22.
-/

set_option autoImplicit false

open Set Function
open scoped ContDiff InnerProductSpace NNReal

namespace PoincareMT.M25.Topology3D

/-- The planar part of the exact height coordinates is continuous linear. -/
noncomputable def horizontalBandProjection (u : UnitTwoSphere) : E3 →L[ℝ] E2 :=
  (ContinuousLinearMap.fst ℝ E2 ℝ).comp (heightPlaneCoordinates u).toContinuousLinearMap

/-- The projection agrees with the first exact height coordinate. -/
@[simp] theorem horizontalBandProjection_apply (u : UnitTwoSphere) (y : E3) :
    horizontalBandProjection u y = (heightPlaneCoordinates u y).1 := rfl

/-- Spacetime coordinates reconstruct the corresponding ambient point. -/
noncomputable def horizontalBandLift (u : UnitTwoSphere) : (ℝ × E2) ≃L[ℝ] E3 :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ E2).trans (heightPlaneCoordinates u).symm

/-- The lift agrees with inverse height coordinates after swapping factors. -/
@[simp] theorem horizontalBandLift_apply (u : UnitTwoSphere) (p : ℝ × E2) :
    horizontalBandLift u p = (heightPlaneCoordinates u).symm (p.2, p.1) := rfl

/-- Lifting preserves the prescribed planar coordinate. -/
@[simp] theorem horizontalBandProjection_lift (u : UnitTwoSphere) (z : ℝ) (p : E2) :
    horizontalBandProjection u (horizontalBandLift u (z, p)) = p := by
  change (heightPlaneCoordinates u ((heightPlaneCoordinates u).symm (p, z))).1 = p
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- Every lifted point has exactly its prescribed height. -/
@[simp] theorem horizontalBandLift_height (u : UnitTwoSphere) (z : ℝ) (p : E2) :
    ⟪(u : E3), horizontalBandLift u (z, p)⟫_ℝ = z := by
  rw [← heightPlaneCoordinates_snd u]
  change (heightPlaneCoordinates u ((heightPlaneCoordinates u).symm (p, z))).2 = z
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- Height and projection reconstruct the actual ambient point. -/
theorem horizontalBandLift_reconstruct (u : UnitTwoSphere) (y : E3) (z : ℝ)
    (hy : ⟪(u : E3), y⟫_ℝ = z) :
    horizontalBandLift u (z, horizontalBandProjection u y) = y :=
  heightPlaneCoordinates_reconstruct u y z hy

/-- The exact planar velocity obtained from the retained ambient field. -/
noncomputable def horizontalBandField (u : UnitTwoSphere) (F : E3 → E3)
    (p : ℝ × E2) : E2 :=
  horizontalBandProjection u (F (horizontalBandLift u p))

/-- Ambient smoothness gives joint smoothness in height and planar position. -/
theorem horizontalBandField_contDiff (u : UnitTwoSphere) (F : E3 → E3)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (horizontalBandField u F) :=
  (horizontalBandProjection u).contDiff.comp (hF.comp (horizontalBandLift u).contDiff)

/-- The horizontal field is supported over the actual ambient support. -/
theorem horizontalBandField_tsupport (u : UnitTwoSphere) (F : E3 → E3) :
    tsupport (horizontalBandField u F) ⊆ (horizontalBandLift u) ⁻¹' tsupport F := by
  apply closure_minimal _ ((isClosed_tsupport F).preimage (horizontalBandLift u).continuous)
  intro p hp
  apply subset_tsupport
  intro hzero
  exact hp (by simp only [horizontalBandField, hzero, map_zero])

/-- The coordinate lift is a homeomorphism, so compact ambient support
gives compact support in the full height-position space. -/
theorem horizontalBandField_hasCompactSupport (u : UnitTwoSphere) (F : E3 → E3)
    (hF : HasCompactSupport F) : HasCompactSupport (horizontalBandField u F) := by
  exact (hF.comp_homeomorph (horizontalBandLift u).toHomeomorph).comp_left
    (horizontalBandProjection u).map_zero

/-- The compact smooth horizontal field supplies global clock-flow bounds. -/
theorem horizontalBandField_clock_bounds (u : UnitTwoSphere) (F : E3 → E3)
    (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F) :
    ∃ K L : ℝ≥0, LipschitzWith K (clockField (horizontalBandField u F)) ∧
      ∀ p, ‖clockField (horizontalBandField u F) p‖ ≤ L :=
  clockField_bounds (horizontalBandField u F) (horizontalBandField_contDiff u F hF)
    (horizontalBandField_hasCompactSupport u F hs)

/-- Every planar evolution displacement has compact spatial support. -/
theorem horizontalBandField_evolution_hasCompactSupport (u : UnitTwoSphere)
    (F : E3 → E3) (hs : HasCompactSupport F) {K L : ℝ≥0}
    (hK : LipschitzWith K (clockField (horizontalBandField u F)))
    (hL : ∀ p, ‖clockField (horizontalBandField u F) p‖ ≤ L) (s t : ℝ) :
    HasCompactSupport (fun p => clockEvolution (horizontalBandField u F) hK hL s t p - p) :=
  clockEvolution_hasCompactSupport (horizontalBandField u F) hK hL
    (horizontalBandField_hasCompactSupport u F hs) s t

end PoincareMT.M25.Topology3D
