import PoincareMT.Proofs.M25.Topology3D.Space3.PlanarBallPair
import PoincareMT.Proofs.M25.Topology3D.Space3.ChartedRelativeCompression

/-!
# Relative attaching-disc compression from the exact planar service

The planar service chooses a disc, and cap normalization changes only
the coordinates of the given ball. Relative compression then fixes
the original attaching disc pointwise and avoids any closed set meeting
the ball only in that disc. Source: Hatcher, Notes on Basic 3-Manifold
Topology, Lemma 1.3, p. 3; see the relative-cap derivation of 2026-09-22.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareMT.M25.Topology3D

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] space3_stereographic_dimension

/-- The planar-service disc is chosen first. Every neighborhood of that
disc admits a relative ball compression with the prescribed open support. -/
theorem relative_ball_compression_of_planar (hP : PlanarSchoenfliesService)
    (B : BallNeighborhoodChart E3 F)
    (c : UnitCircle → E2) (hc : IsPlanarEmbedding c) (v : UnitTwoSphere) :
    ∃ D : PlanarSchoenfliesData c,
      let Δ : Set F := B.chart ''
        ((fun x : E2 => ((stereographic' 2 v).symm (D.chart x) : E3)) '' closedBall 0 1)
      ∀ V Ω : Set F, IsOpen V → Δ ⊆ V → IsOpen Ω → B.closedRegion \ Δ ⊆ Ω →
        ∃ T : ℝ, 0 ≤ T ∧
          ∃ Ψ : ℝ → Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F F ∞,
            ContDiff ℝ ∞ (fun p : ℝ × F => Ψ p.1 p.2) ∧
            (∀ y, Ψ 0 y = y) ∧
            (∀ t : ℝ, 0 ≤ t → MapsTo (Ψ t) B.closedRegion B.closedRegion) ∧
            MapsTo (Ψ T) B.closedRegion V ∧
            (∀ t y, y ∈ Δ → Ψ t y = y) ∧
            ∃ C : Set F, IsCompact C ∧ C ⊆ Ω \ Δ ∧
              ∀ t y, y ∉ C → Ψ t y = y := by
  obtain ⟨D, a, ha, B', _, hclosed, _, hcap⟩ := ballPair_cap_of_planar hP B c hc v
  refine ⟨D, ?_⟩
  dsimp only
  intro V Ω hV hDV hΩ hBΩ
  have hu : ‖-(v : E3)‖ = 1 := by rw [norm_neg]; exact norm_eq_of_mem_sphere v
  have hDV' : B'.chart '' {x : E3 | ‖x‖ = 1 ∧ a ≤ ⟪-(v : E3), x⟫_ℝ} ⊆ V := by
    rwa [hcap]
  have hBΩ' : B'.closedRegion \
      (B'.chart '' {x : E3 | ‖x‖ = 1 ∧ a ≤ ⟪-(v : E3), x⟫_ℝ}) ⊆ Ω := by
    rwa [hclosed, hcap]
  have h := exists_charted_relative_cap_compression B' (-(v : E3)) hu a ha hV hDV' hΩ hBΩ'
  simpa only [hclosed, hcap] using h

end PoincareMT.M25.Topology3D
