import PoincareMT.Definitions.Ch16.CanonicalInduction
import PoincareMT.Definitions.M46NoncollapseInduction

/-!
# M47 repaired canonical-neighborhood induction data

The canonical step consumes the M46 noncollapsing extension at each finite
prefix and returns the exact Proposition 17.1 extension for that prefix. The
canonical output is indexed by the particular extension selected by the M46
package, rather than by an unrelated extension at the same parameter prefix.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedCanonicalInductionData
    (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S) where
  induction : ∀ (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p),
    Nonempty (SurgeryCanonicalExtension.{u} p
      (Classical.choice (N.induction p hp)))

end PoincareMT
