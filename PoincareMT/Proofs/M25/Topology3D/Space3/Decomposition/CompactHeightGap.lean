import PoincareMT.Proofs.M25.Topology3D.Space3.CollarHeight
import Mathlib.Topology.Order.Compact

/-!
# A positive height gap for a protected compact set

Compactness chooses the surgery width after the actual protected geometry
is fixed, including when the protected set is empty. Source: Hatcher,
Notes on Basic 3-Manifold Topology, Theorem 1.1, pp. 1-2; reviewed
whole-family surgery selection inventory F1 of 2026-09-22.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareMT.M25.Topology3D

/-- A compact set avoiding a horizontal plane has a positive, arbitrarily small gap. -/
theorem exists_compact_height_gap
    (K : Set E3) (hK : IsCompact K) (u : UnitTwoSphere)
    (t d : ℝ) (hd : 0 < d)
    (hmiss : ∀ y ∈ K, ⟪(u : E3), y⟫_ℝ ≠ t) :
    ∃ w : ℝ, 0 < w ∧ w < d ∧
      ∀ y ∈ K, w ≤ |⟪(u : E3), y⟫_ℝ - t| := by
  have hf : Continuous (fun y : E3 => |⟪(u : E3), y⟫_ℝ - t|) := by
    fun_prop
  obtain ⟨m, hm, hbound⟩ := hK.exists_forall_le' hf.continuousOn
    (fun y hy => abs_pos.mpr (sub_ne_zero.mpr (hmiss y hy)))
  refine ⟨min (d / 2) m, lt_min (by linarith only [hd]) hm, ?_, ?_⟩
  · exact (min_le_left _ _).trans_lt (by linarith only [hd])
  · intro y hy
    exact (min_le_right _ _).trans (hbound y hy)

end PoincareMT.M25.Topology3D
