import PoincareMT.Statements.M50FinitePrefix

/-!
# The selected raw-flow loss and finite-prefix application

The M49 cutoff is chosen before the flow. M50 is applied to that exact raw
flow and the exact selected loss certificate, with no M37 alignment premise.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Apply Lemma 17.12's calibrated loss service and the M50 finite-loss
consequence to the same flow (Morgan--Tian, pp. 410--411). The cutoff guards
remain explicit; choosing a fresh cutoff never establishes them for a flow. -/
theorem m50SelectedLoss_from_M49
    (V49 : RepairedVolumeLossTheory.{u}) (V50 : RepairedFinitePrefixTheory.{u})
    (g₀ : StandardInitialMetric) (K : MetricSurgeryConstants) :
    ∃ deltaUpper : ℝ, 0 < deltaUpper ∧ deltaUpper ≤ K.delta₀ ∧
      ∀ (F : SurgeryFlowData.{u}) (C : RepairedVolumeLossControls F),
        F.standard_initial = g₀ → F.local_constants = K →
        (∀ T ∈ F.surgery_times, F.parameters.delta T ≤ deltaUpper) →
        ∃ V : RepairedVolumeLossData F C,
          Nonempty (RepairedFinitePrefixData F C V) := by
  obtain ⟨deltaUpper, hpos, hle, losses, _count⟩ := V49.calibrated g₀ K
  refine ⟨deltaUpper, hpos, hle, ?_⟩
  intro F C hg₀ hK hdelta
  obtain ⟨V⟩ := losses F C hg₀ hK hdelta
  exact ⟨V, V50.finite_prefix F C V⟩

end PoincareMT
