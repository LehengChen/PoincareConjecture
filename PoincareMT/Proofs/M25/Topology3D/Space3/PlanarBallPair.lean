import PoincareMT.Proofs.M25.Topology3D.Space3.PlanarBoundaryCap
import PoincareMT.Proofs.M25.Topology3D.Space3.BallChartReparametrization

/-!
# Standard ball and attaching-disc pairs from the planar service

The norm-preserving disc normalization is absorbed into the coordinates
of a given ball. Its ambient region is unchanged, while the attaching
disc becomes the cap used in the relative compression lemmas. This is
the standard-pair step in Hatcher, Notes on Basic 3-Manifold Topology,
Lemma 1.3, p. 3, using exactly the frozen single-curve planar service.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareMT.M25.Topology3D

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] space3_stereographic_dimension

/-- A planar-service attaching disc becomes a standard cap in new ball
coordinates, with the same inside, closed region, and boundary. -/
theorem ballPair_cap_of_planar (hP : PlanarSchoenfliesService)
    (B : BallNeighborhoodChart E3 F)
    (c : UnitCircle → E2) (hc : IsPlanarEmbedding c) (v : UnitTwoSphere) :
    ∃ D : PlanarSchoenfliesData c, ∃ a : ℝ, a ∈ Ioo (1 / 2 : ℝ) 1 ∧
      ∃ B' : BallNeighborhoodChart E3 F,
        B'.inside = B.inside ∧ B'.closedRegion = B.closedRegion ∧
        B'.boundary = B.boundary ∧
        B'.chart '' {y : E3 | ‖y‖ = 1 ∧ a ≤ ⟪-(v : E3), y⟫_ℝ} =
          B.chart '' ((fun x : E2 => ((stereographic' 2 v).symm (D.chart x) : E3)) ''
            closedBall 0 1) := by
  obtain ⟨D, a, ha, G, hG, himage, _, _, _⟩ := boundaryDisc_cap_of_planar hP c hc v
  let B' := B.normReparametrize G hG
  refine ⟨D, a, ha, B', B.normReparametrize_inside G hG,
    B.normReparametrize_closedRegion G hG, B.normReparametrize_boundary G hG, ?_⟩
  rw [← himage, image_image]
  simp only [B', BallNeighborhoodChart.normReparametrize_apply, G.symm_apply_apply]

end PoincareMT.M25.Topology3D
