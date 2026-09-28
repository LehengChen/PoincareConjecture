import PoincareMT.Proofs.M04
import PoincareMT.Proofs.M06
import PoincareMT.Proofs.M07
import PoincareMT.Proofs.M25
import PoincareMT.Proofs.M28
import PoincareMT.Proofs.M29
import PoincareMT.Proofs.M30

/-!
# Applied predecessors for M30

The checked supplier retains M29's actual universal operation. M30 owns the
geometric construction and selects its common threshold within its admission.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

theorem m30ControlledBlowupPredecessorsFromMilestones :
    M30ControlledBlowupPredecessors.{u} := {
  m04 := ricciFlowCurvatureTheory
  m06 := differentialHarnackAncientTheory_from_M04
  m07 := fun H => pointedRicciFlowCompactness_from_M04 H
  m29 := m29GeneralizedBoundedDistance
    (m28BoundedDistance ⟨ricciFlowCurvatureTheory, m25NeckCapTopology⟩)
}

theorem m30ControlledGeneralizedBlowupLimitsFromMilestones :
    RepairedControlledBlowupLimitTheory.{u} :=
  m30ControlledGeneralizedBlowupLimits m30ControlledBlowupPredecessorsFromMilestones

end PoincareMT
