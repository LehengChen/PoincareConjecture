import PoincareMT.Proofs.M03.Existence.BanachVolterraNative

/-!
# Native Banach--Volterra state boundary

The Banach--Volterra solution is represented by an `ODE.FunSpace` fixed point.
This file exposes the two facts needed by the metric producer: every solution
value remains in the prescribed closed state ball, and the derivative already
proved on `Icc` restricts to the half-open forward interval `Ico`.
-/

set_option autoImplicit false

open Set

namespace PoincareMT

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace BanachVolterraProblem

variable (P : BanachVolterraProblem (E := E))

theorem solution_mem_closedBall {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) P.T) :
    P.solution t ∈ Metric.closedBall P.initial P.radius := by
  exact P.fixedPoint.compProj_mem_closedBall (a := P.radius)
    P.toPicardLindelof.mul_max_le

theorem solution_hasDerivWithinAt_Ico {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) P.T) :
    HasDerivWithinAt P.solution
      (P.source t (P.solution t)) (Ico (0 : ℝ) P.T) t := by
  have hIcc := P.solution_hasDerivWithinAt ⟨ht.1, ht.2.le⟩
  exact hIcc.mono (fun s hs => ⟨hs.1, hs.2.le⟩)

end BanachVolterraProblem

end

end PoincareMT
