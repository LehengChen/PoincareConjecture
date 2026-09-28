import PoincareMT.Proofs.M25.Topology3D.Services
import PoincareMT.Proofs.M25.Topology3D.Space3.BallNeighborhoodNesting

/-!
# Filled sides of a verified crosscut decomposition

The known opposite cell fixes the filled side of an actual ball chart.
Source: Hatcher, Notes on Basic 3-Manifold Topology, Lemmas 1.2-1.3,
pp. 2-3; the nonnested common-cap construction, section 2.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M25.Topology3D

/-- A verified two-cell decomposition and one outside witness determine
the full filled side. Source: Hatcher, Lemmas 1.2-1.3, pp. 2-3. -/
theorem saddle_crosscut_cells_inside_outside
    (B : BallNeighborhoodChart E2 E2)
    (K U V Z : Set E2)
    (hcover : K \ Z = U ∪ V)
    (hboundary : K ∩ B.boundary = Z)
    (hU : IsPreconnected U) (hV : IsPreconnected V)
    (hVoutside : ∃ p ∈ V, p ∉ B.closedRegion)
    (hZinterior : ∃ p ∈ Z, p ∈ interior K) :
    U ⊆ B.inside ∧ V ⊆ B.closedRegionᶜ := by
  have hUK : U ⊆ K \ Z := by
    rw [hcover]
    exact subset_union_left
  have hVK : V ⊆ K \ Z := by
    rw [hcover]
    exact subset_union_right
  have hUd : Disjoint U B.boundary := by
    apply disjoint_left.mpr
    intro p hp hpB
    apply (hUK hp).2
    rw [← hboundary]
    exact ⟨(hUK hp).1, hpB⟩
  have hVd : Disjoint V B.boundary := by
    apply disjoint_left.mpr
    intro p hp hpB
    apply (hVK hp).2
    rw [← hboundary]
    exact ⟨(hVK hp).1, hpB⟩
  have hVo : V ⊆ B.closedRegionᶜ := by
    rcases B.preconnected_subset_inside_or_outside hV hVd with hi | ho
    · obtain ⟨p, hp, hpo⟩ := hVoutside
      exact False.elim (hpo (by
        rw [← B.inside_union_boundary]
        exact Or.inl (hi hp)))
    · exact ho
  obtain ⟨p, hpZ, hpK⟩ := hZinterior
  have hpB : p ∈ B.boundary := by
    have hp := hpZ
    rw [← hboundary] at hp
    exact hp.2
  have hpcl : p ∈ closure B.inside := by
    rw [B.closure_inside, ← B.inside_union_boundary]
    exact Or.inr hpB
  obtain ⟨y, hyK, hyB⟩ := mem_closure_iff.mp hpcl
    (interior K) isOpen_interior hpK
  have hyZ : y ∉ Z := by
    intro hy
    rw [← hboundary] at hy
    exact disjoint_left.mp B.inside_disjoint_boundary hyB hy.2
  have hyUV : y ∈ U ∪ V := by
    rw [← hcover]
    exact ⟨interior_subset hyK, hyZ⟩
  have hyU : y ∈ U := hyUV.resolve_right (fun hyV => hVo hyV (by
    rw [← B.inside_union_boundary]
    exact Or.inl hyB))
  refine ⟨?_, hVo⟩
  rcases B.preconnected_subset_inside_or_outside hU hUd with hi | ho
  · exact hi
  · exact False.elim (ho hyU (by
      rw [← B.inside_union_boundary]
      exact Or.inl hyB))

end PoincareMT.M25.Topology3D
