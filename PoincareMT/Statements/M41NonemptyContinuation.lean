import PoincareMT.Definitions.M41NonemptyContinuation

/-!
# M41 repaired nonempty-terminal continuation statement

For a fixed M33 continuation and a nonempty controlled core, select the
nonempty operation on that exact extension with its constructor equality,
post-terminal interval, admissibility and pinching. This is a logical
projection from the supplied M33 data, not a new continuation-existence claim.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedNonemptyContinuationTheory : Prop where
  continuation : ∀ {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : RepairedContinuationInput F T) (branch : RepairedBranchContinuationData I),
    I.controlled_core.Nonempty → Nonempty (RepairedNonemptyContinuationData I branch)

end PoincareMT
