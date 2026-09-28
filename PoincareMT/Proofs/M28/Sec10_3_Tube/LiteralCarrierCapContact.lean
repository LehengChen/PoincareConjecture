import PoincareMT.Definitions.Ch09.NeckCapTopology
import PoincareMT.Proofs.M28.Mathlib.FrontierCrossing

/-!
# Cap-boundary contact from a literal source carrier

Morgan--Tian Claim 10.4, pp. 249--250.  Before a balanced tube certificate
is constructed, the finite selected-neck carrier is already a preconnected
literal set.  If it contains a point of a cap core and contains two endpoint
points outside the cap carrier, the cap boundary must meet that literal set.
This is the first cap-transport stage; no tube certificate, cylinder model,
path hit, reciprocal overlap, or target-shaped cap conclusion is assumed.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

omit [T2Space M] in
private theorem core_subset_closed_core (K : CapCertificate g) :
    K.core ⊆ K.closed_core := by
  rw [K.core_eq_interior_closed_core]
  exact interior_subset

omit [T2Space M] in
private theorem closed_core_subset_carrier (K : CapCertificate g) :
    K.closed_core ⊆ K.carrier := by
  intro x hx
  rw [K.closed_core_eq_complement_end] at hx
  exact hx.1

private theorem literal_side_cover (K : CapCertificate g) {T0 : Set M}
    (hT : IsPreconnected T0)
    (havoid : Disjoint T0 K.boundary_sphere) :
    T0 ⊆ K.core ∨ T0 ⊆ K.closed_coreᶜ := by
  have hopenCore : IsOpen K.core := by
    rw [K.core_eq_interior_closed_core]
    exact isOpen_interior
  have hclosed : IsClosed K.closed_core := K.closed_core_compact.isClosed
  have hdis : Disjoint K.core K.closed_coreᶜ :=
    disjoint_compl_right.mono_left (core_subset_closed_core K)
  have hcover : T0 ⊆ K.core ∪ K.closed_coreᶜ := by
    intro x hx
    by_cases hclosedx : x ∈ K.closed_core
    · by_cases hcorex : x ∈ K.core
      · exact Or.inl hcorex
      · have hfront : x ∈ frontier K.closed_core := by
          rw [frontier, hclosed.closure_eq]
          refine ⟨hclosedx, ?_⟩
          rw [← K.core_eq_interior_closed_core]
          exact hcorex
        have hboundary : x ∈ K.boundary_sphere := by
          rw [← K.core_frontier_eq_boundary]
          exact hfront
        exact False.elim (Set.disjoint_left.mp havoid hx hboundary)
    · exact Or.inr hclosedx
  exact hT.subset_or_subset hopenCore hclosed.isOpen_compl hdis hcover

/-- A literal finite-list source carrier must meet a cap boundary when it
contains a cap-core point but both retained endpoints lie outside the cap.
The endpoint data is used only for the side contradiction; the theorem does
not consume a prebuilt balanced chain or manufacture a path hit. -/
theorem exists_literal_carrier_cap_boundary_contact
    {T0 : Set M} (K : CapCertificate g)
    (hT : IsPreconnected T0)
    {x p q : M}
    (hxT : x ∈ T0) (hxcore : x ∈ K.core)
    (hpT : p ∈ T0) (hpout : p ∉ K.carrier)
    (hqT : q ∈ T0) (hqout : q ∉ K.carrier) :
    (T0 ∩ K.boundary_sphere).Nonempty := by
  by_contra hnone
  have havoid : Disjoint T0 K.boundary_sphere := by
    apply disjoint_iff_inter_eq_empty.mpr
    exact Set.not_nonempty_iff_eq_empty.mp hnone
  have hend :
      (p ∈ T0 ∧ p ∉ K.carrier) ∧ (q ∈ T0 ∧ q ∉ K.carrier) :=
    ⟨⟨hpT, hpout⟩, ⟨hqT, hqout⟩⟩
  rcases literal_side_cover K hT havoid with hcore | hout
  · have hpcore := hcore hpT
    have hpcarrier := closed_core_subset_carrier K
      (core_subset_closed_core K hpcore)
    exact hend.1.2 hpcarrier
  · have hxout := hout hxT
    exact hxout (core_subset_closed_core K hxcore)

end PoincareMT.M28
