import PoincareMT.Proofs.M25.Topology3D.Space3.FlowCoincidence

/-!
# Localization on the backward tracks of an unwanted set

To retain a finite-time containment, fields need agree only near the
backward tracks of points outside the target, where these tracks meet
the invariant source region. This avoids imposing agreement on backward
tracks outside the source. It is the localization argument for relative
cap compression, Hatcher, Notes on Basic 3-Manifold Topology,
Lemma 1.3, p. 3; see the derivation of 2026-09-22.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace PoincareMT.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Agreement near the relevant backward tracks transfers a finite-time
containment to a second field whose source region stays invariant. -/
theorem boundedFlow_mapsTo_of_backward_agreement (f g : E → E)
    {kf lf kg lg : ℝ≥0} (hfK : LipschitzWith kf f) (hfL : ∀ x, ‖f x‖ ≤ lf)
    (hgK : LipschitzWith kg g) (hgL : ∀ x, ‖g x‖ ≤ lg)
    {B V : Set E} {T : ℝ} (hT : 0 ≤ T)
    (hB : ∀ t ∈ Icc 0 T, MapsTo (fun x => boundedFlow g hgK hgL x t) B B)
    (hV : MapsTo (fun x => boundedFlow f hfK hfL x T) B V)
    (hnear : ∀ t ∈ Icc 0 T, ∀ y ∈ B \ V,
      boundedFlow f hfK hfL y (-t) ∈ B →
        g =ᶠ[𝓝 (boundedFlow f hfK hfL y (-t))] f) :
    MapsTo (fun x => boundedFlow g hgK hgL x T) B V := by
  intro x hx
  by_contra hyV
  let y := boundedFlow g hgK hgL x T
  have hy : y ∈ B \ V := ⟨hB T ⟨hT, le_rfl⟩ hx, hyV⟩
  let γ := boundedFlow g hgK hgL x
  let η := fun s => boundedFlow f hfK hfL y (s - T)
  have hη (s : ℝ) : HasDerivAt η (f (η s)) s := by
    simpa only [η, Function.comp_def, one_smul, id_eq] using
      (boundedFlow_hasDerivAt f hfK hfL y (s - T)).scomp s
        ((hasDerivAt_id s).sub_const T)
  have heq : EqOn γ η (Icc 0 T) := by
    refine integralCurves_eqOn_of_local_agreement f g hgK γ η
      (boundedFlow_hasDerivAt g hgK hgL x) hη isPreconnected_Icc
      ?_ (t₀ := T) ⟨hT, le_rfl⟩ ?_
    · intro s hs hgs
      have he : η s = boundedFlow f hfK hfL y (-(T - s)) := by
        change boundedFlow f hfK hfL y (s - T) = _
        rw [show s - T = -(T - s) by ring]
      rw [he]
      apply hnear (T - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ y hy
      rw [← he, ← hgs]
      exact hB s hs hx
    · simp only [γ, η, sub_self, boundedFlow_zero, y]
  have hxback : x = boundedFlow f hfK hfL y (-T) := by
    simpa only [γ, η, boundedFlow_zero, zero_sub] using heq ⟨le_rfl, hT⟩
  have hforward : boundedFlow f hfK hfL x T = y := by
    rw [hxback, ← boundedFlow_add, neg_add_cancel, boundedFlow_zero]
  exact hy.2 (hforward ▸ hV hx)

end PoincareMT.M25.Topology3D
