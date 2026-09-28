import PoincareMT.Proofs.M30.Thm5_6_PartialLimits.AnalyticSuppliers
import PoincareMT.Proofs.M30.Thm11_8.GeometricLongConvergence

/-!
# Geometric controlled limits on the full backward horizon

M28's included-time analytic theorems close the geometric branch of
M30's retained expanding-window assembly (Morgan--Tian Theorem 11.8,
pp. 272--279).
-/

set_option autoImplicit false

open scoped ENNReal

universe u

namespace PoincareMT.M30

/-- Geometric long controls produce convergence on the entire prescribed
backward horizon, with no remaining analytic service premise
(Morgan--Tian Theorem 11.8, pp. 272--279). -/
theorem exists_geometric_long_convergence
    (P : M30ControlledBlowupPredecessors.{u})
    (S : GeneralizedBlowupSequence.{u}) {T₀ : ℝ≥0∞}
    (H : M30GeometricLongControls S T₀) :
    Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval T₀)) := by
  exact exists_geometric_long_generalizedBlowupConvergence P
    withinFlowJetBoundsService withinBilinearFlowService
    spatialSliceJetConvergenceService S H

end PoincareMT.M30
