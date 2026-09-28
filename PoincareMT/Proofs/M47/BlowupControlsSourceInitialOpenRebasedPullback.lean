import PoincareMT.Proofs.M47.CanonicalNeckOpenSource

/-!
# Rebasing a supplied initial source to the open-subtype carrier

The terminal realization already supplies the normalized metric pullback on
an unchanged open source.  This helper only rewrites that two-slot readout
after the literal `neckOpenSourceCylinder` rebasing; it constructs no source,
patch, older neck, or canonical control.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M47

open PoincareMT.Proofs.M47

/-- The supplied ordinary readout is unchanged by the open-subtype rebasing.

The source, interval, and terminal readout are explicit hypotheses.  Both
tangent slots are retained in the displayed identity. -/
theorem source_initial_open_rebased_pullback
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {T Q tau : ℝ} (hU : TopologicalSpace.Opens C.carrier)
    (q : hU)
    (e : SurgeryFlowCylinder F C T Q (Icc (-tau) 0) hU)
    (G : RicciFlow 3 hU (Icc (-tau) 0))
    (hread : ∀ (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : hU)
      (v w : TangentSpace (𝓡 3) x),
      (G.metric s).inner x v w = e.pullbackInner s hs x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : hU → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : hU → C.carrier) x w)) :
    ∀ (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : hU)
      (v w : TangentSpace (𝓡 3) x),
      (G.metric s).inner x v w =
        (neckOpenSourceCylinder hU q e).pullbackInner s hs x v w := by
  intro s hs x v w
  have hr := hread s hs x v w
  have hforward := (e.forward_smooth s hs x.val x.property).contMDiffAt
    (hU.isOpen.mem_nhds x.property)
  have hfd := hforward.mdifferentiableAt (by simp)
  have hsub : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : hU → C.carrier) (x : hU) :=
    contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)
  have hv := mfderiv_comp_apply x hfd hsub v
  have hw := mfderiv_comp_apply x hfd hsub w
  rw [neckOpenSourceCylinder_pullbackInner]
  have hePull : e.pullbackInner s hs x.val
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : hU → C.carrier) x v)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : hU → C.carrier) x w) =
      Q * (F.metric (T + s / Q)).inner (e.forward s hs x.val)
        (mfderiv (𝓡 3) (𝓡 3)
          (fun y : hU => e.forward s hs y.val) x v)
        (mfderiv (𝓡 3) (𝓡 3)
          (fun y : hU => e.forward s hs y.val) x w) := by
    unfold SurgeryFlowCylinder.pullbackInner
    rw [← hv, ← hw]
    simp only [Function.comp_def]
  exact hr.trans hePull

end PoincareMT.M47
