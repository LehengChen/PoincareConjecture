import PoincareMT.Proofs.M45
import PoincareMT.Proofs.M45.Calibration
import PoincareMT.Proofs.M03
import PoincareMT.Proofs.M04
import PoincareMT.Proofs.M25
import PoincareMT.Proofs.M27.Providers
import PoincareMT.Proofs.M28
import PoincareMT.Proofs.M31
import PoincareMT.Proofs.M32.Providers
import PoincareMT.Proofs.M34
import PoincareMT.Proofs.M35.Providers
import PoincareMT.Proofs.M36
import PoincareMT.Proofs.M44
import PoincareMT.Proofs.M44.Providers

/-!
Supply M45's earlier services once, retaining the prescribed epsilon bound
used by M51/M52. The same selected Appendix A theory supplies M28 and M45.
These applications add no admission and do not prove M45's geometric outputs.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

theorem m45ControlledSchedulesTheoryFromMilestones :
    RepairedControlledSchedulesTheory.{u} := by
  let A : RepairedNeckCapTopologyTheory.{u} := Classical.choice m25NeckCapTopology
  apply repairedControlledSchedules
    (fun M _ _ _ _ _ _ => ricciFlowLocalTheory (n := 3) (M := M))
    ricciFlowCurvatureTheory A m27KappaAlternativesFromMilestones
    (m28BoundedDistance ⟨ricciFlowCurvatureTheory, ⟨A⟩⟩)
    m31SingularRegularLimitTheory m32HornSelectionFromMilestones

theorem m45ControlledSchedulesBelowFromMilestones
    (epsilon_bound : ℝ) (hpositive : 0 < epsilon_bound) :
    ∃ S : RepairedControlledSchedulesData.{u},
      2 * S.setup.epsilon ≤ epsilon_bound :=
  m45ControlledSchedulesTheoryFromMilestones.schedules
    repairedStandardCapExistence m35StandardCapUniquenessFromMilestones
    repairedMetricSurgery m44CapPersistenceFromMilestones epsilon_bound hpositive

theorem m45ControlledSchedulesFromMilestones :
    Nonempty RepairedControlledSchedulesData.{u} := by
  obtain ⟨S, _⟩ := m45ControlledSchedulesBelowFromMilestones 1 zero_lt_one
  exact ⟨S⟩

end PoincareMT
