import PoincareMT.Proofs.M25.Topology3D.Space3.BallNeighborhood

/-!
# Reparametrizing a ball chart without changing its region

A norm-preserving ambient diffeomorphism changes the coordinates of a
ball while retaining its inside, closed region, and boundary. This turns
the attaching-disc normalization into a standard pair, as required in
Hatcher, Notes on Basic 3-Manifold Topology, Lemma 1.3, p. 3.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareMT.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace BallNeighborhoodChart

/-- Change the source coordinates by the inverse of a norm-preserving
diffeomorphism, keeping the entire closed unit ball in the chart source. -/
noncomputable def normReparametrize (B : BallNeighborhoodChart E F)
    (G : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (hG : ∀ x, ‖G x‖ = ‖x‖) :
    BallNeighborhoodChart E F where
  chart := G.symm.toHomeomorph.toOpenPartialHomeomorph.trans B.chart
  closedBall_subset_source := by
    intro x hx
    refine ⟨mem_univ _, B.closedBall_subset_source ?_⟩
    have hn : ‖G.symm x‖ = ‖x‖ := by
      rw [← hG (G.symm x), G.apply_symm_apply]
    change G.symm x ∈ closedBall 0 1
    simpa only [mem_closedBall_zero_iff, hn] using hx
  smooth := B.smooth.comp G.symm.contDiff.contDiffOn (fun _ hx => hx.2)
  smooth_symm := G.contDiff.comp_contDiffOn (B.smooth_symm.mono (fun _ hx => hx.1))

/-- The new ball chart has the exact inverse-reparametrization formula. -/
theorem normReparametrize_apply (B : BallNeighborhoodChart E F)
    (G : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (hG : ∀ x, ‖G x‖ = ‖x‖) (x : E) :
    (B.normReparametrize G hG).chart x = B.chart (G.symm x) := rfl

/-- Reparametrization retains the image of every source set that is
preserved by the chosen diffeomorphism and its inverse. -/
theorem normReparametrize_image (B : BallNeighborhoodChart E F)
    (G : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (hG : ∀ x, ‖G x‖ = ‖x‖)
    {S : Set E} (hS : ∀ x, G x ∈ S ↔ x ∈ S) :
    (B.normReparametrize G hG).chart '' S = B.chart '' S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨G.symm x, ?_, rfl⟩
    apply (hS (G.symm x)).mp
    rwa [G.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨G x, (hS x).mpr hx, ?_⟩
    rw [normReparametrize_apply, G.symm_apply_apply]

/-- The open inside of the ball is unchanged by norm reparametrization. -/
theorem normReparametrize_inside (B : BallNeighborhoodChart E F)
    (G : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (hG : ∀ x, ‖G x‖ = ‖x‖) :
    (B.normReparametrize G hG).inside = B.inside :=
  B.normReparametrize_image G hG (fun x => by simp only [mem_ball_zero_iff, hG x])

/-- The closed ball region is unchanged by norm reparametrization. -/
theorem normReparametrize_closedRegion (B : BallNeighborhoodChart E F)
    (G : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (hG : ∀ x, ‖G x‖ = ‖x‖) :
    (B.normReparametrize G hG).closedRegion = B.closedRegion :=
  B.normReparametrize_image G hG (fun x => by simp only [mem_closedBall_zero_iff, hG x])

/-- The boundary sphere is unchanged by norm reparametrization. -/
theorem normReparametrize_boundary (B : BallNeighborhoodChart E F)
    (G : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (hG : ∀ x, ‖G x‖ = ‖x‖) :
    (B.normReparametrize G hG).boundary = B.boundary :=
  B.normReparametrize_image G hG (fun x => by simp only [mem_sphere_zero_iff_norm, hG x])

end BallNeighborhoodChart
end PoincareMT.M25.Topology3D
