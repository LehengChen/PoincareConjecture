import PoincareMT.Statements.Ch04.CurvatureTheory
import PoincareMT.Statements.Ch04.Harnack
import PoincareMT.Statements.Ch05.Compactness
import PoincareMT.Statements.M29GeneralizedDistance

/-!
# Earlier services for M30's controlled limits

M04 supplies curvature calculus and local derivative estimates, M06 finite-start
Harnack, M07 common-interval compactness on its existing Type-0 carriers, and
M29 the universal bounded-distance estimate, including rebased applications.
Partial compactness before a common time interval, universe transport and the
remaining supporting geometry are M30-owned obligations in the full contract.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

structure M30ControlledBlowupPredecessors : Prop where
  m04 : RicciFlowCurvatureTheory.{u}
  m06 : HarnackAncientTheory.{u}
  m07 : ∀ {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses 3 T' T),
    Nonempty (PointedRicciFlowCompactnessConclusion H)
  m29 : RepairedGeneralizedBoundedDistanceTheory.{u}

end PoincareMT
