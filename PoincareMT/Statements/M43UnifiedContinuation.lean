import PoincareMT.Definitions.M43UnifiedContinuation
import PoincareMT.Statements.M41NonemptyContinuation
import PoincareMT.Statements.M42VanishingContinuation

/-!
# M43 repaired unified continuation statement

The M41 and M42 providers select the appropriate constructor on one fixed
M33 continuation by inspecting its supplied controlled-core status. This is
a logical branch assembly; continuation existence remains an M33 obligation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedUnifiedContinuationTheory : Prop where
  continuation : RepairedNonemptyContinuationTheory.{u} →
    RepairedVanishingContinuationTheory.{u} →
    ∀ {F : SurgeryFlowData.{u}} {T : ℝ},
    ∀ (I : RepairedContinuationInput F T) (branch : RepairedBranchContinuationData I),
      Nonempty (RepairedUnifiedContinuationData I branch)

end PoincareMT
