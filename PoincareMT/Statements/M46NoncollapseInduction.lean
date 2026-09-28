import PoincareMT.Definitions.M46NoncollapseInduction
import PoincareMT.Statements.M15Noncollapsing
import PoincareMT.Statements.Ch04.CurvatureTheory
import PoincareMT.Statements.M11GeneralizedFlow
import PoincareMT.Statements.M12GeneralizedEquation
import PoincareMT.Statements.M13Rescaling
import PoincareMT.Statements.M14GeneralizedLGeometry
import PoincareMT.Definitions.M33RegularHistory

/-!
# M46 repaired noncollapsing induction statement

The selected calibrated setup admits the noncollapsing extension at every
finite parameter prefix with the same initial seeds.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-! Direct services used by the M46 proof.  These are named here so imports
and broad chapter conclusions cannot masquerade as actual predecessor
applications. -/
structure M46Predecessors : Prop where
  m04 : RicciFlowCurvatureTheory.{u}
  m11 : GeneralizedSpacetimeGeometryTheory.{u} 3
  m12 : GeneralizedRicciGaugeTheory.{u} 3
  m13 : GeneralizedParabolicRescalingTheory.{u} 3
  m14 : GeneralizedLGeometryTheory.{u} 3
  m15 : GeneralizedNoncollapsingConclusion.{u} 3
  regular_history : ∀ (F : SurgeryFlowData.{u}) (W : M33RegularHistoryWindow F),
    Nonempty (M33RegularHistoryData W)

/-! The source theorem is applied after the dimension-three generalized
noncollapsing and earlier services are fixed at the M46 theorem entry.
Consumers receive an induction service ready to apply to their selected
M45 setup. The selected M45 setup and seeds determine
compatibility with each finite prefix, and its stored M44 cap-persistence
package supplies the selected
same-metric surgery data. They contain no analytic continuation service.
The returned package keeps only the primitive prefix-indexed extension data. -/
structure RepairedNoncollapseInductionTheory : Prop where
  induction : ∀ S : RepairedControlledSchedulesData.{u},
      Nonempty (RepairedNoncollapseInductionData.{u} S)

end PoincareMT
