import PoincareMT.Proofs.M47.GeneralizedBridgeGeometry

/-!
# Compact closed sets on an actual regular history slice

At a nonsurgery time the actual generalized slice is globally
diffeomorphic to the compact physical slice. The event-time regular
region is only open and is not included in this statement.
Source: Morgan--Tian Proposition 14.12, p. 350, and Claim 17.9, p. 406.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M47

/-- The actual global nonsurgery slice identification makes the closure
of every subset compact, in particular every normalized base ball. -/
theorem regular_history_compact_closure
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {t : ℝ} (ht : t ∈ H.generalized.interval)
    (hRegular : t ∉ F.surgery_times) (U : Set (H.generalized.slice t).carrier) :
    IsCompact (closure U) := by
  let : CompactSpace (F.slice t).carrier :=
    ⟨F.slices_compact t (H.history.time_subset ht)⟩
  let : CompactSpace (H.generalized.slice t).carrier :=
    (regular_history_slice_diffeomorph H t ht hRegular).toHomeomorph.symm.compactSpace
  exact isClosed_closure.isCompact

end PoincareMT.M47
