import PoincareMT.Proofs.M47.TerminalCommonIntervalCapturedRows

/-!
# Gluing the actual compact row limits

Compatibility is the equality proved from the same original maps on row
intersections. Interior coverage proves continuity; compact cofinality
gives convergence on every compact set. Source: reviewed C6c.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

universe u v

namespace PoincareMT.M47

/-- Compatible continuous row limits define one continuous global map
with uniform convergence of the original maps on every compact set. -/
theorem terminalCommonInterval_glue_row_limits
    {M : Type u} {N : Type v} [MetricSpace M] [MetricSpace N]
    (K : ℕ → Set M) (L : ℕ → Set N)
    (hcover : ∀ x, ∃ j, x ∈ interior (K j))
    (f : ∀ j, C(K j, L j))
    (hcompat : ∀ i j (x : M) (hi : x ∈ K i) (hj : x ∈ K j),
      (f i ⟨x, hi⟩).val = (f j ⟨x, hj⟩).val) :
    ∃ t : M → N, Continuous t ∧
      (∀ j (x : K j), t x = (f j x).val) := by
  classical
  let j (x : M) := (hcover x).choose
  have hj (x : M) : x ∈ K (j x) := interior_subset (hcover x).choose_spec
  let t (x : M) := (f (j x) ⟨x, hj x⟩).val
  have ht (i : ℕ) (x : K i) : t x = (f i x).val :=
    hcompat (j x) i x (hj x) x.property
  have hc (i : ℕ) : ContinuousOn t (K i) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp (f i).continuous).congr (fun x => (ht i x).symm)
  refine ⟨t, ?_, ht⟩
  · apply continuous_iff_continuousAt.mpr
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact (hc i x (interior_subset hi)).continuousAt (mem_interior_iff_mem_nhds.mp hi)

end PoincareMT.M47
