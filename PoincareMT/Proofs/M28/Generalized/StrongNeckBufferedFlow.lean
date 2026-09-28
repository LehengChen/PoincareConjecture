import PoincareMT.Proofs.M28.Generalized.StrongNeckSourceNeck
import PoincareMT.Proofs.M28.Sec10_3_Tube.NeckPrecompactBalls

/-!
# The buffered-window flow of one chosen original strong-neck rescaling

Definition 9.78 and Claims 10.3-10.11. Restrict the supplied raw M12/M13
rescaling itself, retaining its total metric and connection representatives.
Its total representatives are unchanged, but the declared interval is
now [-3/4,0]. See M28 derivations 84 and 125.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.M28

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
  (S : GeneralizedStrongNeck F t epsilon)
  (H : RescaledRawCylinderData (C := F.slice t)
    (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
    (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))

/-- Restrict the supplied normalized source flow to its actual closed
buffered window, without selecting a second rescaling (Definition 9.78). -/
noncomputable def GeneralizedStrongNeck.rescaled_buffered_flow :
    RicciFlow 3 (strongNeckOpen S) (Icc (-(3 / 4 : ℝ)) 0) := by
  let q : ℝ := S.scale⁻¹ ^ 2
  let K := Proofs.M12.cylinderPhysicalInterval t q
    S.time_cylinder.scale_pos strongNeckBackwardInterval
  have hsub : Icc (-(3 / 4 : ℝ)) 0 ⊆
      (parabolicInterval q S.time_cylinder.scale_pos t K).domain := by
    intro s hs
    apply (mem_parabolicInterval_iff q S.time_cylinder.scale_pos t K s).2
    refine ⟨s, ?_, rfl⟩
    exact ⟨by linarith [hs.1], hs.2⟩
  exact Poincare.Geometry.RicciFlow.Harnack.restrictFlow H.rescaling.flow
    hsub ordConnected_Icc
    ⟨-(3 / 4 : ℝ), by norm_num, 0, by norm_num, by norm_num⟩

/-- Every total metric representative is literally the chosen H metric,
including at real times outside the restricted window (Definition 9.78). -/
@[simp] theorem GeneralizedStrongNeck.rescaled_buffered_flow_metric (s : ℝ) :
    (GeneralizedStrongNeck.rescaled_buffered_flow S H).metric s =
      H.rescaling.flow.metric s := rfl

/-- Restriction also keeps the same dependent connection representative
at every real time (Definition 9.78). -/
@[simp] theorem GeneralizedStrongNeck.rescaled_buffered_flow_connection (s : ℝ) :
    (GeneralizedStrongNeck.rescaled_buffered_flow S H).connection s =
      H.rescaling.flow.connection s := rfl


end PoincareMT.M28
