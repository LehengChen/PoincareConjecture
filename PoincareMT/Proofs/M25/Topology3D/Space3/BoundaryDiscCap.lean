import PoincareMT.Proofs.M25.Topology3D.Space3.BoundaryDiscRounding
import PoincareMT.Proofs.M25.Topology3D.Space3.StereographicCap

/-!
# Standardizing an attaching disc as a small spherical cap

The compact norm-preserving disc rounding gives precisely the spherical
cap with threshold in `(1/2,1)` retained by the relative ball-contraction
construction. This is the attaching-disc normalization of Hatcher,
Notes on Basic 3-Manifold Topology, Lemma 1.3, p. 3. Reassembly of the
two balls, including the nested case, is a separate obligation.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareMT.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- A charted attaching disc becomes a small round cap under a compact
ambient diffeomorphism preserving the surrounding sphere and ball. -/
theorem exists_boundary_disc_cap (v : E) (hv : ‖v‖ = 1)
    (D : BallNeighborhoodChart ((ℝ ∙ v)ᗮ) ((ℝ ∙ v)ᗮ))
    (hdim : 1 < Module.rank ℝ ((ℝ ∙ v)ᗮ))
    (hsphere : IsPreconnected (sphere (0 : E) 1)) :
    ∃ a : ℝ, a ∈ Ioo (1 / 2 : ℝ) 1 ∧
      ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
        (∀ y, ‖F y‖ = ‖y‖) ∧
        F '' ((fun w => (stereoInvFun hv w : E)) '' D.closedRegion) =
          {y : E | ‖y‖ = 1 ∧ a ≤ ⟪-v, y⟫_ℝ} ∧
        ∃ C : Set E, IsCompact C ∧ ∀ y, y ∉ C → F y = y := by
  obtain ⟨r, hr, hr1, F, hFnorm, himage, C, hC, hfix⟩ :=
    exists_boundary_disc_round_image v hv D hdim hsphere
  refine ⟨stereographicCapHeight r, stereographicCapHeight_mem_Ioo hr hr1,
    F, hFnorm, ?_, C, hC, hfix⟩
  rw [himage, stereoInvFun_image_closedBall v hv hr hr1]

end PoincareMT.M25.Topology3D
