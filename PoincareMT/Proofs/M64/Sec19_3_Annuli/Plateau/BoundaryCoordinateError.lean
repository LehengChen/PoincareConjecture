import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryErrorLocalization
import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityAffineWeak

/-!
# Actual coordinate error and its zero-boundary cutoff

Subtracting the C1 boundary extension and applying a real smooth cutoff
constructs a global continuous H1 error. Its weak columns agree with the
literal map columns minus the extension derivative on the smaller disk.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Poincare.Analysis.Sobolev.Weak

namespace PoincareMT

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Subtracting the prescribed C1 extension gives the actual weak error columns and their L2
bounds. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis.
Project derivation: `proof-work/tasks/M64/reports/2026-09-25-annulus-boundary-error.md`. -/
theorem m64BoundaryCoordinate_error_columns
    {u C : LoopPlane → E} {W : Fin 2 → LoopPlane → E} {a : LoopPlane} {R : ℝ}
    (hu : ContinuousOn u (closedBall a R)) (hC : ContDiff ℝ 1 C)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball a R)) :
    let D := fun (i : Fin 2) (p : LoopPlane) => fderiv ℝ C p (EuclideanSpace.single i 1)
    MemLp (fun p => u p - C p) 2 (volume.restrict (ball a R)) ∧
      (∀ i, MemLp (fun p => W i p - D i p) 2 (volume.restrict (ball a R))) ∧
      ∀ i j, HasWeakPartialDeriv i (fun p => (W i p - D i p) j)
        (fun p => (u p - C p) j) (ball a R) := by
  let D := fun (i : Fin 2) (p : LoopPlane) => fderiv ℝ C p (EuclideanSpace.single i 1)
  have huM := m64MemLp_on_ball_of_continuous_closedBall hu 2
  have hCM := m64MemLp_on_ball_of_continuous_closedBall hC.continuous.continuousOn 2
    (a := a) (R := R)
  have hDM (i : Fin 2) : MemLp (D i) 2 (volume.restrict (ball a R)) :=
    m64MemLp_on_ball_of_continuous_closedBall
      ((hC.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn 2
  refine ⟨huM.sub hCM, fun i => (hW i).sub (hDM i), ?_⟩
  intro i j
  let P := EuclideanSpace.proj (𝕜 := ℝ) j
  have hweakC : HasWeakPartialDeriv i (fun p => D i p j) (fun p => C p j)
      (ball a R) := by
    have h := HasWeakPartialDeriv.of_contDiff (Ω := ball a R) isOpen_ball
      (P.contDiff.comp hC) (i := i)
    have hder (p : LoopPlane) : fderiv ℝ (P ∘ C) p = P.comp (fderiv ℝ C p) := by
      rw [fderiv_comp _ P.differentiableAt (hC.differentiable (by simp) _), P.fderiv]
    simp only [hder, ContinuousLinearMap.comp_apply] at h
    exact h
  have h := m64WeakPartial_add (P.comp_memLp' huM)
    ((P.comp_memLp' hCM).const_mul (-1)) (P.comp_memLp' (hW i))
    ((P.comp_memLp' (hDM i)).const_mul (-1)) (hw i j)
    (m64WeakPartial_const_mul hweakC (-1))
  simpa only [neg_one_mul, ← sub_eq_add_neg, PiLp.sub_apply, P, D,
    Function.comp_apply, EuclideanSpace.coe_proj] using h

/-- A genuine smooth cutoff gives a global continuous zero-boundary error with the exact
original error columns on the smaller disk. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; local boundary analysis. Project derivation:
`proof-work/tasks/M64/reports/2026-09-25-annulus-boundary-error.md`. -/
theorem m64BoundaryCoordinate_error_cutoff
    {u C : LoopPlane → E} {W : Fin 2 → LoopPlane → E} {a : LoopPlane} {R : ℝ}
    (hR : 0 < R) (ha : a 1 = 0) (hu : Continuous u) (hC : ContDiff ℝ 1 C)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball a R))
    (htrace : ∀ p ∈ closedBall a R, p 1 ≤ 0 → u p = C p) :
    ∃ (v : LoopPlane → E) (dv : Fin 2 → LoopPlane → E),
      Continuous v ∧ (∀ p : LoopPlane, p 1 < 0 → v p = 0) ∧
      (∀ i, MemLp (dv i) 2 volume) ∧
      (∀ i j, HasWeakPartialDeriv i (fun p => dv i p j) (fun p => v p j) univ) ∧
      ∀ p ∈ ball a (R / 2), v p = u p - C p ∧
        ∀ i, dv i p = W i p - fderiv ℝ C p (EuclideanSpace.single i 1) := by
  let error := fun p => u p - C p
  let D := fun (i : Fin 2) (p : LoopPlane) =>
    W i p - fderiv ℝ C p (EuclideanSpace.single i 1)
  obtain ⟨hm, hD, hd⟩ := m64BoundaryCoordinate_error_columns hu.continuousOn hC hW hw
  obtain ⟨chi, hchi, hc, hs, hone, htests⟩ := m64WeakBoundaryError_localization
    (u := error) (V := D) hR ha (hu.sub hC.continuous).continuousOn hm hD hd
    (fun p hp hp1 => by dsimp [error]; rw [htrace p hp hp1, sub_self])
  let v := fun p => chi p • error p
  let dv := fun (i : Fin 2) (p : LoopPlane) =>
    chi p • D i p + fderiv ℝ chi p (EuclideanSpace.single i 1) • error p
  have hv : Continuous v := hchi.continuous.smul (hu.sub hC.continuous)
  refine ⟨v, dv, hv, ?_, ?_, ?_, ?_⟩
  · intro p hp
    by_cases hpS : p ∈ tsupport chi
    · dsimp [v, error]
      rw [htrace p (ball_subset_closedBall (hs hpS)) hp.le, sub_self, smul_zero]
    · dsimp [v]
      rw [image_eq_zero_of_notMem_tsupport hpS, zero_smul]
  · intro i
    apply memLp_piLp_iff.mpr
    intro j
    simpa only [dv, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using ((htests j).2 i).1
  · intro i j
    simpa only [v, dv, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using ((htests j).2 i).2
  · intro p hp
    have heq := hone p hp
    simp [v, dv, heq.1, heq.2, error, D]

end PoincareMT
