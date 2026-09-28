import PoincareMT.Proofs.M32.Mathlib.ProductCompactBoundary
import PoincareMT.Definitions.Ch09.NeckCapTopology

/-!
# The compact-core obstruction for either cap model

Morgan--Tian Claim 11.35, printed p. 290. The actual frozen cap core
has nonempty interior and compact closure with the prescribed boundary.
The product chart straightening that boundary is a separate geometric input.
Reviewed derivation: `claim11_35-compact-core-obstruction.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareMT.M32

/-- Neither frozen cap model can lie in a product chart taking its
actual core boundary into one fiber. Source: Claim 11.35, printed p. 290.
Only the certificate's compact core and boundary fields are used. -/
theorem cap_not_in_product_chart_with_fiber_boundary
    {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    {g : RiemannianMetric 3 M} (C : CapCertificate g)
    {U : Set M} (hU : IsOpen U) (hCU : C.carrier ⊆ U) (e : U ≃ₜ X × ℝ)
    {a : ℝ}
    (hboundary : e '' ((Subtype.val : U → M) ⁻¹' C.boundary_sphere) ⊆
      {z | z.2 = a}) : False := by
  have hcore : C.closed_core ⊆ U := by
    intro x hx
    rw [C.closed_core_eq_complement_end] at hx
    exact hCU hx.1
  have hint : (interior C.closed_core).Nonempty := by
    rw [← C.core_eq_interior_closed_core]
    exact C.core_nonempty
  have hfront : e '' ((Subtype.val : U → M) ⁻¹' frontier C.closed_core) ⊆
      {z | z.2 = a} := by
    rw [C.core_frontier_eq_boundary]
    exact hboundary
  exact not_isCompact_of_product_chart_frontier hU hcore e hint hfront C.closed_core_compact

end PoincareMT.M32
