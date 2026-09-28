import PoincareMT.Proofs.M76.Horizon.Compatible
import PoincareMT.Statements.M76SmoothingBridge

/-!
# M76 proof entry

The single theorem-owned admission is the Hamilton--Cairns construction.  A
future owner may edit this file and `Proofs/M76/` only; the primitive bridge
definition and statement remain read-only.
-/

-- The historical admission described above is now discharged by the imported continuation.
set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

/-- M76: Hamilton--Cairns compatible smoothing bridge. -/
theorem m76CompatibleSmoothing : M76SmoothingStatement.{u} := by
  exact horizon_m76CompatibleSmoothing

end PoincareMT
