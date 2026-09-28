import PoincareMT.Definitions.M44CapPersistence
import PoincareMT.Statements.M34StandardCapExistence
import PoincareMT.Statements.M35StandardCapUniqueness
import PoincareMT.Statements.M36MetricSurgery
import PoincareMT.Statements.M44Providers

/-!
# M44 repaired surgery-cap persistence statement

Every standard initial metric has a cap-persistence package with the exact
two-way comparison/disappearance alternative from Proposition 16.5. The
parameter prefix is indexed by the package's M36 constants and is required to
use the same standard initial metric.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedCapPersistenceTheory : Prop where
  persistence : RepairedStandardCapExistenceTheory →
    RepairedStandardCapUniquenessTheory →
    RepairedMetricSurgeryTheory.{u} →
    ∀ g₀ : StandardInitialMetric,
      Nonempty (RepairedCapPersistenceData.{u} g₀)

end PoincareMT
