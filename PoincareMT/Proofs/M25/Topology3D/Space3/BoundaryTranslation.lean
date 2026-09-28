import PoincareMT.Proofs.M25.Topology3D.Space3.CompactTrackExtension
import PoincareMT.Proofs.M25.Topology3D.Space3.BoundaryDiscFlow

/-!
# Translating a compact attaching disc in stereographic coordinates

A compactly localized constant field gives an ambient norm-preserving
diffeomorphism inducing any prescribed translation on a compact set in
the stereographic plane. This centers the affine disc in Hatcher, Notes
on Basic 3-Manifold Topology, Lemma 1.3, p. 3, before radial rounding.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareMT.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- Any translation on a compact stereographic set is induced by a
compact ambient diffeomorphism preserving every centered sphere. -/
theorem exists_boundary_translation (v : E) (hv : ‖v‖ = 1)
    {S : Set ((ℝ ∙ v)ᗮ)} (hS : IsCompact S) (a : (ℝ ∙ v)ᗮ) :
    ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (∀ y, ‖F y‖ = ‖y‖) ∧
      (∀ x ∈ S, F (stereoInvFun hv x : E) = (stereoInvFun hv (x + a) : E)) ∧
      ∃ C : Set E, IsCompact C ∧ C ⊆ radialStereoTarget v ∧
        ∀ y, y ∉ C → F y = y := by
  obtain ⟨W, hW, hWc, _, k, l, hk, hl, htrack⟩ := exists_compact_field_tracking hS
    (fun t x => x + t • a)
    ((continuous_snd.add (continuous_fst.smul continuous_const)).continuousOn)
    isOpen_univ (fun _ _ _ _ => mem_univ _) (fun _ => a) contDiffOn_const
    (fun x _ t _ => by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const a).const_add x)
  obtain ⟨Φ, _, _, hnorm, hΦtrack, C, hC, hCt, hfix⟩ :=
    exists_boundaryDisc_ambient_flow v hv W hW hWc hk hl
  refine ⟨Φ 1, hnorm 1, ?_, C, hC, hCt, hfix 1⟩
  intro x hx
  have ht := htrack x hx 1 ⟨zero_le_one, le_rfl⟩
  simp only [zero_smul, add_zero, one_smul] at ht
  rw [hΦtrack, ht]

end PoincareMT.M25.Topology3D
