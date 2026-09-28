import PoincareMT.Definitions.M36MetricSurgery

/-!
# M36 repaired metric-surgery statement

Every standard initial metric receives uniform surgery constants and an
operation certificate for each admissible neck.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/- The source contract is Claim 13.1, Theorem 13.2, Definition 13.3, and
   Lemma 13.4 (Morgan--Tian, printed pp. 331--334), specialized to the
   standard initial metric and every admissible epsilon-neck. -/
structure RepairedMetricSurgeryTheory : Prop where
  surgery : ∀ g₀ : StandardInitialMetric,
    Nonempty (RepairedMetricSurgeryData.{u} g₀)

end PoincareMT
