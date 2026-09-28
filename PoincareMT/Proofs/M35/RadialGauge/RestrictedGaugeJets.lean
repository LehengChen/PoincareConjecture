import PoincareMT.Proofs.M35.RadialGauge.GaugeRestriction
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# The actual finite map jets after R5 to R3 restriction

Morgan-Tian Proposition 12.26, pp. 320-322. Fixed linear restriction
preserves the already proved joint C1 regularity of the actual spatial
jets. Fixed multilinear evaluations recover the genuine first and second
differentials, avoiding any assumption of full joint C2 beforehand.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Set
open scoped ContDiff

namespace PoincareMT.M35.RadialGauge

variable {m n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin m)
local notation "W" => EuclideanSpace ℝ (Fin n)

/-- Joint regularity of actual spatial jets survives the fixed linear
restriction used to pass from the analytic R5 solution to R3. -/
theorem restricted_spatial_jet_joint_c1 (I : V →L[ℝ] W)
    {u : ℝ → W → ℝ} {J : Set ℝ}
    (hs : ∀ t ∈ J, ContDiff ℝ ∞ (u t)) (j : ℕ)
    (hj : ContDiffOn ℝ 1 (fun p : ℝ × W => iteratedFDeriv ℝ j (u p.1) p.2)
      (J ×ˢ univ)) :
    ContDiffOn ℝ 1 (fun p : ℝ × V => iteratedFDeriv ℝ j (fun x => u p.1 (I x)) p.2)
      (J ×ˢ univ) := by
  let A := ContinuousMultilinearMap.compContinuousLinearMapL (F := ℝ) (fun _ : Fin j => I)
  have harg : ContDiffOn ℝ 1 (fun p : ℝ × V => (p.1, I p.2)) (J ×ˢ univ) :=
    contDiffOn_fst.prodMk (I.contDiff.comp_contDiffOn contDiffOn_snd)
  have hm : MapsTo (fun p : ℝ × V => (p.1, I p.2)) (J ×ˢ univ) (J ×ˢ univ) :=
    fun _ hp => ⟨hp.1, mem_univ _⟩
  have hc := A.contDiff.comp_contDiffOn
    (hj.comp harg hm)
  apply hc.congr
  intro p hp
  exact I.iteratedFDeriv_comp_right (hs p.1 hp.1) p.2
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)

/-- The actual first jet has the genuine operator-valued joint C1
regularity required by the map differential formula. -/
theorem fderiv_joint_c1_of_first_jet {u : ℝ → V → ℝ} {J : Set ℝ}
    (hj : ContDiffOn ℝ 1 (fun p : ℝ × V => iteratedFDeriv ℝ 1 (u p.1) p.2)
      (J ×ˢ univ)) :
    ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (u p.1) p.2) (J ×ˢ univ) := by
  apply contDiffOn_clm_apply.mpr
  intro v
  have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => V) ℝ
    (fun _ => v)).contDiff.comp_contDiffOn hj
  simpa only [Function.comp_def, ContinuousMultilinearMap.apply_apply,
    iteratedFDeriv_one_apply] using h

/-- The same conversion for the true second differential uses fixed
two-slot evaluations of the actual second jet. -/
theorem hessian_joint_c1_of_second_jet {u : ℝ → V → ℝ} {J : Set ℝ}
    (hj : ContDiffOn ℝ 1 (fun p : ℝ × V => iteratedFDeriv ℝ 2 (u p.1) p.2)
      (J ×ˢ univ)) :
    ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (fderiv ℝ (u p.1)) p.2)
      (J ×ˢ univ) := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => V) ℝ
    ![v, w]).contDiff.comp_contDiffOn hj
  simpa only [Function.comp_def, ContinuousMultilinearMap.apply_apply,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using h

end PoincareMT.M35.RadialGauge
