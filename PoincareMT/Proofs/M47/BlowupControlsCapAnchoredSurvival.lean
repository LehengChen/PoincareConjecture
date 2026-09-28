import PoincareMT.Proofs.M47.BlowupControlsCapAnchoredNecks
import PoincareMT.Proofs.M47.BlowupControlsCapSurvival

/-!
# Survival through an anchored neck carrier

The affine anchor supplies an exact old-region carrier identity.  When an
actual open and closed flow cylinder are supplied on that carrier, the
identity transports a selected old-region point into the open source and
the existing M44 trajectory argument excludes disappearance.  Static neck
data do not construct either flow cylinder.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareMT.M47

/-- An actual surviving cylinder on the anchored end cannot disappear.

The point is supplied in the old anchored region; the exact carrier
identity of the affine end neck supplies its membership in the open source.
All temporal and based-cylinder hypotheses remain explicit inputs. -/
theorem cap_not_disappears_of_anchored_carrier
    {F : SurgeryFlowData.{u}} {origin scale tau d : ℝ}
    {N E : EpsilonNeck (F.metric origin)} {b : ℝ}
    {V : Set (F.slice origin).carrier}
    (hcarrier : E.carrier = N.region b N.epsilon⁻¹)
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale
      (Ico 0 tau) E.carrier)
    (f : SurgeryFlowCylinder F (F.slice origin) origin scale
      (Icc 0 d) V)
    (htau : 0 < tau) (htaud : tau < d)
    (y : (F.slice origin).carrier)
    (hyregion : y ∈ N.region b N.epsilon⁻¹) (hyV : y ∈ V)
    (hinitial : ∀ h x, x ∈ V → HEq (f.forward 0 h x) x) :
    ¬ SurgeryBallDisappearsAt F e (origin + tau / scale) := by
  have hyE : y ∈ E.carrier := by
    rw [hcarrier]
    exact hyregion
  exact cap_not_disappears_of_surviving_cylinder e f htau htaud y hyE hyV hinitial

end PoincareMT.M47
