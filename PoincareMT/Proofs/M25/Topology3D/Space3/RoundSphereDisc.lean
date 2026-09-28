import PoincareMT.Proofs.M25.Topology3D.Space3.SourceCircleDisc
import PoincareMT.Proofs.M25.Topology3D.Space3.ScaledBallChart
import PoincareMT.Proofs.M25.Topology3D.Space3.SphereDiscCoordinates

/-!
# Smooth round discs in the source sphere

Positive scaling followed by inverse stereographic projection gives a
smooth chart on the whole plane. Its unit closed-disc and boundary images
retain the exact positive stereographic radius. This implements the
explicit complementary-chart step of the reviewed source-sphere-disc-split
derivation of 2026-09-22, following Hatcher, Notes on Basic 3-Manifold
Topology, Theorem 1.1 and Lemma 1.3, pp. 1-3.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareMT.M25.Topology3D

attribute [local instance] space3_stereographic_dimension

/-- The round disc chart at a chosen pole and positive radius. -/
noncomputable def roundSphereDiscChart (v : UnitTwoSphere) (r : ℝ) (hr : 0 < r) :
    OpenPartialHomeomorph E2 UnitTwoSphere :=
  (scaledBallNeighborhoodChart r hr).chart.trans (stereographic' 2 v).symm

/-- The round source-disc chart is defined on the entire plane. -/
theorem roundSphereDiscChart_source (v : UnitTwoSphere) (r : ℝ) (hr : 0 < r) :
    (roundSphereDiscChart v r hr).source = univ := by
  ext x
  change (x ∈ (univ : Set E2) ∧
    (scaledBallNeighborhoodChart r hr).chart x ∈ (stereographic' 2 v).target) ↔ x ∈ univ
  rw [stereographic'_target]
  simp

/-- The positive-radius round disc chart is smooth everywhere. -/
theorem roundSphereDiscChart_contMDiff (v : UnitTwoSphere) (r : ℝ) (hr : 0 < r) :
    ContMDiff 𝓘(ℝ, E2) (𝓡 2) ∞ (roundSphereDiscChart v r hr) := by
  have h : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞
      (roundSphereDiscChart v r hr) (roundSphereDiscChart v r hr).source :=
    (stereographic'_symm_contMDiff v).comp_contMDiffOn
      ((scaledBallNeighborhoodChart r hr).smooth.contMDiffOn.mono inter_subset_left)
  rw [roundSphereDiscChart_source] at h
  exact contMDiffOn_univ.mp h

/-- The inverse of the round disc chart is smooth on its exact target. -/
theorem roundSphereDiscChart_symm_contMDiffOn (v : UnitTwoSphere) (r : ℝ) (hr : 0 < r) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ (roundSphereDiscChart v r hr).symm
      (roundSphereDiscChart v r hr).target :=
  (scaledBallNeighborhoodChart r hr).smooth_symm.contMDiffOn.comp
    ((stereographic'_contMDiffOn v).mono inter_subset_left) (fun _ hx => hx.2)

/-- The unit closed disc maps onto the full radius-r stereographic disc. -/
theorem roundSphereDiscChart_image_closedBall (v : UnitTwoSphere) (r : ℝ) (hr : 0 < r) :
    (roundSphereDiscChart v r hr) '' closedBall 0 1 =
      (stereographic' 2 v).symm '' closedBall 0 r := by
  change (fun x => (stereographic' 2 v).symm ((scaledBallNeighborhoodChart r hr).chart x)) ''
    closedBall 0 1 = _
  rw [← image_image (stereographic' 2 v).symm (scaledBallNeighborhoodChart r hr).chart]
  change (stereographic' 2 v).symm '' (scaledBallNeighborhoodChart r hr).closedRegion = _
  rw [scaledBallNeighborhoodChart_closedRegion]

/-- The unit circle maps onto the full radius-r stereographic latitude. -/
theorem roundSphereDiscChart_image_sphere (v : UnitTwoSphere) (r : ℝ) (hr : 0 < r) :
    (roundSphereDiscChart v r hr) '' sphere 0 1 =
      (stereographic' 2 v).symm '' sphere 0 r := by
  change (fun x => (stereographic' 2 v).symm ((scaledBallNeighborhoodChart r hr).chart x)) ''
    sphere 0 1 = _
  rw [← image_image (stereographic' 2 v).symm (scaledBallNeighborhoodChart r hr).chart]
  change (stereographic' 2 v).symm '' (scaledBallNeighborhoodChart r hr).boundary = _
  rw [scaledBallNeighborhoodChart_boundary]

end PoincareMT.M25.Topology3D
