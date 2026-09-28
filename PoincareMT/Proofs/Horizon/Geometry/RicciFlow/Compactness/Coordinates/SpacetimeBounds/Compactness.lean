import PoincareMT.Proofs.M07
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bounds
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.NormalCharts

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Compactness`.
Its constants already exist on main in
`PoincareMT.Proofs.M07`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

/-! # Pointed Ricci-flow compactness from the supplied curvature theory

The proved metric-jet estimates discharge the normal-chart exhaustion
assembler's remaining analytic hypothesis.
-/

set_option autoImplicit false

namespace PoincareMT

/-- The frozen M07 conclusion needs only the local curvature derivative estimates. -/
theorem pointedRicciFlowCompactness_of_local_derivative_estimates
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hShi : LocalCurvatureDerivativeEstimates.{0}) :
    Nonempty (PointedRicciFlowCompactnessConclusion H) := by
  apply H.pointedRicciFlowCompactness_of_uniform_normalChartCover_bounds
  intro A R ρ a b N hA hρ hρR ha hb I hIcompact hI m
  obtain ⟨B, _, hbound⟩ :=
    H.eventually_normalChartCover_spacetime_jet_bound_of_local_derivative_estimates
      hShi hIcompact hI (N := N) hA hρ hρR ha hb.le m
  exact ⟨B, hbound⟩

end PoincareMT
