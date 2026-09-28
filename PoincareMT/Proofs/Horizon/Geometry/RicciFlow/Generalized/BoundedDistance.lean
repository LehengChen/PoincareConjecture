import PoincareMT.Definitions.M28BoundedDistance
import PoincareMT.Statements.M28BoundedDistance
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Generalized.CanonicalNeighborhood

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Generalized.BoundedDistance`.
Its constants already exist on main in
`PoincareMT.Definitions.M28BoundedDistance`
`PoincareMT.Statements.M28BoundedDistance`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

/-!
# Uniform bounded-distance estimates for generalized flows

Adapted without changing declaration bodies from Mapher commit
`4a6b36794e04c3fac86663910a73a924fed43f23`.
Morgan--Tian, Theorem 10.2, pp. 245--246, and the opening of the proof of
Theorem 11.1, p. 269. The uniform estimate remains an explicit premise.
See `references/ricci-flow/mapher/reviewed-bounded-distance.md`.
-/

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure HorizonRepairedBoundedDistanceTheory : Prop where
  constants : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
    ∀ C : ℝ, 0 < C → ∀ A : ℝ, 0 ≤ A →
      ∃ D₀ D : ℝ, 0 < D₀ ∧ 0 < D ∧
        ∀ F : GeneralizedRicciFlowData.{u},
          F.interval ⊆ Set.Ici 0 →
          generalizedHamiltonIveyPinched F →
          ∀ t, t ∈ F.interval → ∀ x : (F.slice t).carrier,
            D₀ ≤ F.scalar ⟨t, x⟩ →
            generalizedEarlierStrongCanonicalNeighborhoods F epsilon C t x →
            RepairedBoundedDistanceEstimate F A D t x

end PoincareMT
