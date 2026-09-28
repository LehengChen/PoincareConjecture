import PoincareMT.Proofs.M25.Topology3D.Space3.BoundaryDiscCoordinates
import PoincareMT.Proofs.M25.Topology3D.Space3.BallRegionUniqueness

/-!
# Sphere charts for identifying rounded disc regions

Norm-preserving ambient homeomorphisms restrict to the unit sphere.
Composing stereographic coordinates with a disc neighborhood chart
retains an open chart through its closed disc. The stereographic pole
is fixed by every map supported in the radial chart target. These are
the topological identifications in Hatcher, Notes on Basic 3-Manifold
Topology, Lemma 1.3, p. 3, after the explicit boundary rounding.
-/

set_option autoImplicit false

open Set Metric
open scoped InnerProductSpace

namespace PoincareMT.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A norm-preserving ambient homeomorphism restricts to the unit sphere. -/
noncomputable def normPreservingSphereHomeomorph (F : E ≃ₜ E)
    (hF : ∀ y, ‖F y‖ = ‖y‖) : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1 :=
  F.subtype (fun y => by simp only [mem_sphere_zero_iff_norm, hF])

omit [InnerProductSpace ℝ E] in
/-- The restricted sphere homeomorphism retains the ambient formula. -/
theorem normPreservingSphereHomeomorph_apply (F : E ≃ₜ E)
    (hF : ∀ y, ‖F y‖ = ‖y‖) (q : sphere (0 : E) 1) :
    (normPreservingSphereHomeomorph F hF q : E) = F q := rfl

/-- Compact support inside the radial stereographic target leaves its
pole fixed, which identifies the exterior side of a rounded disc. -/
theorem radialStereo_supported_fixes_pole (v : E) (hv : ‖v‖ = 1)
    (f : E → E) {C : Set E} (hC : C ⊆ radialStereoTarget v)
    (hfix : ∀ y, y ∉ C → f y = y) : f v = v := by
  apply hfix
  intro hvC
  have hbad := hC hvC
  change ⟪v, v⟫_ℝ < ‖v‖ at hbad
  rw [real_inner_self_eq_norm_sq, hv] at hbad
  norm_num at hbad

/-- A stereographic disc neighborhood is an open chart into the sphere. -/
noncomputable def sphereDiscChart (v : E) (hv : ‖v‖ = 1)
    (D : BallNeighborhoodChart ((ℝ ∙ v)ᗮ) ((ℝ ∙ v)ᗮ)) :
    OpenPartialHomeomorph ((ℝ ∙ v)ᗮ) (sphere (0 : E) 1) :=
  D.chart.trans (stereographic hv).symm

/-- Sphere disc coordinates extend through the closed unit disc. -/
theorem sphereDiscChart_closedBall_subset_source (v : E) (hv : ‖v‖ = 1)
    (D : BallNeighborhoodChart ((ℝ ∙ v)ᗮ) ((ℝ ∙ v)ᗮ)) :
    closedBall 0 1 ⊆ (sphereDiscChart v hv D).source := by
  intro x hx
  exact ⟨D.closedBall_subset_source hx, mem_univ _⟩

/-- The sphere chart uses the explicit stereographic inverse. -/
theorem sphereDiscChart_apply (v : E) (hv : ‖v‖ = 1)
    (D : BallNeighborhoodChart ((ℝ ∙ v)ᗮ) ((ℝ ∙ v)ᗮ)) (x : (ℝ ∙ v)ᗮ) :
    sphereDiscChart v hv D x = stereoInvFun hv (D.chart x) := rfl

end PoincareMT.M25.Topology3D
