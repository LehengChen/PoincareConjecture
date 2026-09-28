import PoincareMT.Proofs.M25.Topology3D.Space3.BallNeighborhood

/-!
# Transporting a saddle ball through an ambient diffeomorphism

Postcomposition transports the full ball-neighborhood certificate and
its exact boundary. This is the final pullback after Hatcher, Notes on
Basic 3-Manifold Topology, Lemma 1.2, pp. 2-3, normalizes a base piece.
See the independently reviewed ball-and-height-transport derivation
of 2026-09-22 in the saddle records.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareMT.M25.Topology3D

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Postcomposition transports an actual ball neighborhood through a
smooth ambient diffeomorphism; Hatcher, Lemma 1.2, pp. 2-3. -/
noncomputable def BallNeighborhoodChart.mapDiffeomorph
    (B : BallNeighborhoodChart E F)
    (g : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, G) F G ∞) : BallNeighborhoodChart E G where
  chart := B.chart.trans g.toHomeomorph.toOpenPartialHomeomorph
  closedBall_subset_source := fun _ hx => ⟨B.closedBall_subset_source hx, mem_univ _⟩
  smooth := g.contDiff.comp_contDiffOn (B.smooth.mono inter_subset_left)
  smooth_symm := B.smooth_symm.comp g.symm.contDiff.contDiffOn (fun _ hy => hy.2)

/-- The transported chart keeps the literal composition as its total
forward map; saddle ball-and-height-transport inventory, item 2. -/
@[simp] theorem BallNeighborhoodChart.mapDiffeomorph_apply
    (B : BallNeighborhoodChart E F)
    (g : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, G) F G ∞) (x : E) :
    (B.mapDiffeomorph g).chart x = g (B.chart x) := rfl

/-- The full boundary is transported by the same ambient map, with
exact image equality; Hatcher, Lemma 1.2, pp. 2-3. -/
theorem BallNeighborhoodChart.mapDiffeomorph_boundary
    (B : BallNeighborhoodChart E F)
    (g : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, G) F G ∞) :
    (B.mapDiffeomorph g).boundary = g '' B.boundary := by
  change (g ∘ B.chart) '' sphere 0 1 = g '' (B.chart '' sphere 0 1)
  exact image_comp _ _ _

/-- The ball interior is transported by the same actual ambient map.
Source: Hatcher, Lemma 1.2, pp. 2-3, height-reversal region transport. -/
theorem BallNeighborhoodChart.mapDiffeomorph_inside
    (B : BallNeighborhoodChart E F)
    (g : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, G) F G ∞) :
    (B.mapDiffeomorph g).inside = g '' B.inside := by
  change (g ∘ B.chart) '' ball 0 1 = g '' (B.chart '' ball 0 1)
  exact image_comp _ _ _

/-- The closed ball region is transported by the same actual ambient map.
Source: Hatcher, Lemma 1.2, pp. 2-3, height-reversal region transport. -/
theorem BallNeighborhoodChart.mapDiffeomorph_closedRegion
    (B : BallNeighborhoodChart E F)
    (g : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, G) F G ∞) :
    (B.mapDiffeomorph g).closedRegion = g '' B.closedRegion := by
  change (g ∘ B.chart) '' closedBall 0 1 = g '' (B.chart '' closedBall 0 1)
  exact image_comp _ _ _

/-- A ball for an actual diffeomorphic image pulls back to a ball
with exactly the original boundary; Hatcher, Lemma 1.2, pp. 2-3. -/
theorem exists_ball_of_diffeomorphic_image
    (g : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, G) F G ∞) (S : Set F)
    (B : BallNeighborhoodChart E G) (hB : B.boundary = g '' S) :
    ∃ B' : BallNeighborhoodChart E F, B'.boundary = S := by
  refine ⟨B.mapDiffeomorph g.symm, ?_⟩
  rw [B.mapDiffeomorph_boundary, hB]
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hzx⟩
    have hzx' : z = x := (g.symm_apply_apply z).symm.trans hzx
    exact hzx' ▸ hz
  · intro hx
    exact ⟨g x, ⟨x, hx, rfl⟩, g.symm_apply_apply x⟩

end PoincareMT.M25.Topology3D
