import PoincareMT.Definitions.M41NonemptyContinuation
import PoincareMT.Definitions.M42VanishingContinuation

/-!
# M43 repaired unified continuation data

The unified output stores exactly one branch certificate. A `Sum` keeps the
nonempty and whole-slice-vanishing alternatives constructor-disjoint while
preserving the detailed branch data for downstream schedule rows.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedUnifiedContinuationData
    {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : RepairedContinuationInput F T)
    (branch : RepairedBranchContinuationData I) where
  terminal : Sum (RepairedNonemptyContinuationData I branch)
    (RepairedVanishingContinuationData I branch)

end PoincareMT
