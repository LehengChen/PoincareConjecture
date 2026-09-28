import PoincareMT.Definitions.Ch16.NoncollapseInduction
import PoincareMT.Definitions.M45ControlledSchedules

/-!
# M46 repaired noncollapsing induction data

The induction package uses the selected M45 setup and initial seeds. It
returns `SurgeryNoncollapseExtension` for every compatible finite prefix,
before any global schedule is chosen.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedNoncollapseInductionData
    (S : RepairedControlledSchedulesData.{u}) where
  induction : ∀ p : SurgeryParameterPrefix S.constants,
    S.SeedCompatible p → Nonempty (SurgeryNoncollapseExtension.{u} p)

/-! The old volume seed is the non-positive-component branch of the actual
prefix controls. Its proof is an admission-free projection; it contains no
analytic estimate and adds no premise to `SeedCompatible`. -/
def OldTestedVolumeControls {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K)
    (F : SurgeryFlowData.{u}) (O : SurgeryObservation F) : Prop :=
  SurgeryTestedVolumeOn F
    (surgeryObservationInterval O ∩ surgeryEpochEntry p.i)
    (p.kappa ⟨p.i, Nat.lt_succ_self _⟩)
    (p.r ⟨p.i, Nat.lt_succ_self _⟩) 16

end PoincareMT
