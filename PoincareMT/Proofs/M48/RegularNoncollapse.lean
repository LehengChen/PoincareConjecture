import PoincareMT.Proofs.M48.RegularSpacetime
import PoincareMT.Proofs.M15.RawNoncollapse

/-!
# Noncollapse on the same M48 regular history

The supplied M15 predicate on the retained geometry produces the raw
generalized predicate at the same point with the same constant. Constructing
that M15 predicate from actual configurations remains an upstream obligation.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

theorem M48Predecessors.regular_noncollapsed (P : M48Predecessors.{u})
    {F : SurgeryFlowData.{u}} {T : ℝ} {L : RepairedPreterminalSlab F T}
    (R : M48RegularSpacetimeData L) (p : R.history.generalized.point) (r0 kappa : ℝ)
    (h : M15GeneralizedNoncollapseAt R.geometry.toLGeometry p r0 kappa) :
    GeneralizedKappaNoncollapsedAt R.history.generalized p kappa r0 :=
  Proofs.M15.raw_noncollapse R.geometry P.m13 h

end PoincareMT
