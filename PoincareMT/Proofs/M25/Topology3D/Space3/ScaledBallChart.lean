import PoincareMT.Proofs.M25.Topology3D.Space3.BallNeighborhood

/-!
# Round balls as smooth neighborhood charts

Positive scalar multiplication supplies a neighborhood chart for each
round ball and its boundary sphere. This is the round target disc in
Hatcher, Notes on Basic 3-Manifold Topology, Lemma 1.3, p. 3.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Pointwise

namespace PoincareMT.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Scalar coordinates give a smooth neighborhood chart for a round ball. -/
noncomputable def scaledBallNeighborhoodChart (r : ℝ) (hr : 0 < r) :
    BallNeighborhoodChart E E where
  chart := (Homeomorph.smulOfNeZero r hr.ne').toOpenPartialHomeomorph
  closedBall_subset_source := subset_univ _
  smooth := (contDiff_const.smul contDiff_id).contDiffOn
  smooth_symm := (contDiff_const.smul contDiff_id).contDiffOn

/-- The scalar chart has its prescribed multiplication formula. -/
theorem scaledBallNeighborhoodChart_apply (r : ℝ) (hr : 0 < r) (x : E) :
    (scaledBallNeighborhoodChart r hr).chart x = r • x := rfl

/-- Its boundary is the round sphere of the given positive radius. -/
theorem scaledBallNeighborhoodChart_boundary (r : ℝ) (hr : 0 < r) :
    (scaledBallNeighborhoodChart (E := E) r hr).boundary = sphere 0 r := by
  change r • sphere (0 : E) 1 = sphere 0 r
  simpa only [smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one] using
    smul_sphere' hr.ne' (0 : E) 1

/-- Its closed region is the entire round closed ball. -/
theorem scaledBallNeighborhoodChart_closedRegion (r : ℝ) (hr : 0 < r) :
    (scaledBallNeighborhoodChart (E := E) r hr).closedRegion = closedBall 0 r := by
  change r • closedBall (0 : E) 1 = closedBall 0 r
  simpa only [smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one] using
    smul_closedBall' hr.ne' (0 : E) 1

end PoincareMT.M25.Topology3D
