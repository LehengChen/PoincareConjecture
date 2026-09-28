import PoincareMT.Proofs.M35.RadialGauge.EuclideanGaugeTime

/-!
# Closed-slab continuity of the actual restricted gauge differential

Morgan-Tian Proposition 12.26, pp. 320-322. The constructed R5
solution and its actual derivative are continuous on the same closed
slab. A fixed linear restriction and the literal exponential map
derivative transfer that statement to the R3 gauge, including its tip.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace PoincareMT.M35.RadialGauge

variable {m n : ℕ} {S : Type*} [TopologicalSpace S]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))
local notation "W" => EuclideanSpace ℝ (Fin m)

/-- The actual map and differential after a fixed spatial restriction
retain continuity on the closed parameter domain of the solution. -/
theorem restricted_euclideanGauge_continuous (I : V →L[ℝ] W)
    {u : S → W → ℝ} (hs : ∀ t, ContDiff ℝ ∞ (u t))
    (hu : Continuous (Function.uncurry u))
    (hdu : Continuous (fun p : S × W => fderiv ℝ (u p.1) p.2)) :
    Continuous (fun p : S × V => euclideanGauge (fun x => u p.1 (I x)) p.2) ∧
    Continuous (fun p : S × V => fderiv ℝ (euclideanGauge (fun x => u p.1 (I x))) p.2) := by
  let a (t : S) (x : V) := u t (I x)
  have harg : Continuous (fun p : S × V => (p.1, I p.2)) :=
    continuous_fst.prodMk (I.continuous.comp continuous_snd)
  have ha : Continuous (Function.uncurry a) := hu.comp harg
  have hda : Continuous (fun p : S × V => fderiv ℝ (a p.1) p.2) := by
    have h := (hdu.comp harg).clm_comp (continuous_const (y := I))
    apply h.congr
    intro p
    simpa only [Function.comp_def, ContinuousLinearMap.fderiv] using
      (fderiv_comp p.2 ((hs p.1).differentiable (by simp) (I p.2))
        I.differentiableAt).symm
  have hL := ha.rexp.smul (continuous_const (y := ContinuousLinearMap.id ℝ V))
  have hR := ((ContinuousLinearMap.smulRightL ℝ V V).continuous.comp
    (ha.rexp.smul hda)).clm_apply continuous_snd
  refine ⟨ha.rexp.smul continuous_snd, (hL.add hR).congr ?_⟩
  intro p
  exact (euclideanGauge_hasFDerivAt
    (((hs p.1).comp I.contDiff).differentiable (by simp) p.2)).fderiv.symm

end PoincareMT.M35.RadialGauge
