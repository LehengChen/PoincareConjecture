import PoincareMT.Definitions.M42VanishingContinuation

/-!
# M42 repaired vanishing-terminal continuation statement

For a fixed M33 continuation with empty controlled core, select the vanishing
operation with its constructor equality, empty terminal carrier,
post-terminal interval, admissibility and pinching, and an infinite terminal
time. The operation retains strict no-later-surgery control on that continued
time domain. This is a
logical projection from supplied M33 data, not a new continuation theorem.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedVanishingContinuationTheory : Prop where
  continuation : ∀ {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : RepairedContinuationInput F T) (branch : RepairedBranchContinuationData I),
    I.controlled_core = ∅ → Nonempty (RepairedVanishingContinuationData I branch)

end PoincareMT
