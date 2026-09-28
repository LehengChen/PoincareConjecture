import PoincareMT.Definitions.Ch03.RicciFlow

/-!
# Short-time existence and geometric uniqueness contracts

These concrete propositions express Morgan-Tian, Theorem 3.11, printed p. 39.
The compactness and separation assumptions belong to the theorems proving
them. Equality concerns metrics on the specified time domain.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable (n : ℕ) (M : Type u) [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Every initial metric starts a Ricci flow for some positive lifetime. -/
def ShortTimeRicciFlowExistence : Prop :=
  ∀ g0 : RiemannianMetric n M,
    ∃ T : ℝ, 0 < T ∧ ∃ F : RicciFlow n M (Set.Ico 0 T), F.metric 0 = g0

/-- Flows starting from the same metric at zero agree on their common forward domain. -/
def RicciFlowUniqueness : Prop :=
  ∀ (J J' : Set ℝ) (F : RicciFlow n M J) (F' : RicciFlow n M J'),
    IsLeast J 0 → IsLeast J' 0 → F.metric 0 = F'.metric 0 →
      Set.EqOn F.metric F'.metric (J ∩ J')

end PoincareMT
