import PoincareMT.Proofs.M25.Topology3D.Space3.CompactChart
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Interiors and boundaries of closed charted discs

A closed disc contained in a smooth chart has the expected interior
and boundary in the target manifold. These topological identities are
used to identify the common latitude of the two source discs in the
reviewed source-sphere-disc-split derivation of 2026-09-22, following
Hatcher, Notes on Basic 3-Manifold Topology, Theorem 1.1, pp. 1-3.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M25.Topology3D

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable [TopologicalSpace Y] [T2Space Y]

omit [ProperSpace E] [T2Space Y] in
/-- The interior of a closed charted ball is precisely its open ball
image, when the whole closed ball lies in the chart source. -/
theorem compactChart_interior_closedBall (e : OpenPartialHomeomorph E Y) (x : E)
    {r : ℝ} (hr : 0 < r) (hs : closedBall x r ⊆ e.source) :
    interior (e '' closedBall x r) = e '' ball x r := by
  have hi : e.IsImage (closedBall x r) (e '' closedBall x r) := by
    intro z hz
    constructor
    · rintro ⟨w, hw, hwz⟩
      have heq := e.injOn (hs hw) hz hwz
      simpa only [heq] using hw
    · intro hz'
      exact ⟨z, hz', rfl⟩
  have ht : e '' closedBall x r ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source (hs hz)
  have h := hi.interior.image_eq
  rw [interior_closedBall x hr.ne',
    inter_eq_right.mpr (ball_subset_closedBall.trans hs),
    inter_eq_right.mpr (interior_subset.trans ht)] at h
  exact h.symm

/-- The frontier of a compact closed charted ball is its full boundary
sphere image, in the target topology. -/
theorem compactChart_frontier_closedBall (e : OpenPartialHomeomorph E Y) (x : E)
    {r : ℝ} (hr : 0 < r) (hs : closedBall x r ⊆ e.source) :
    frontier (e '' closedBall x r) = e '' sphere x r := by
  have hc : IsClosed (e '' closedBall x r) :=
    ((isCompact_closedBall x r).image_of_continuousOn (e.continuousOn.mono hs)).isClosed
  rw [frontier, hc.closure_eq, compactChart_interior_closedBall e x hr hs,
    ← (e.injOn.mono hs).image_sdiff_subset ball_subset_closedBall, closedBall_sdiff_ball]

end PoincareMT.M25.Topology3D
