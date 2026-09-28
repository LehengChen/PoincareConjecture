import PoincareMT.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakClassical

/-!
# C1 regularity from continuous reflected weak columns

The reflected scalar/vector equation is handled before this file.  Its
boundary H2/H3 analysis can provide continuous column representatives.  The
actual Sacks--Uhlenbeck mollifier argument in M60 then identifies those
representatives with the classical derivative on an inner disk.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Poincare.Analysis.Sobolev.Weak

namespace PoincareMT

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- A continuous weak map with continuous full weak columns is C1 on the inner disk. The
weak derivatives are supplied on the larger disk; no classical derivative or global
regularity is assumed. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary
analysis. Project derivation:
`proof-work/tasks/M64/reports/2026-09-25-boundary-c1-from-weak-columns.md`. -/
theorem m64Reflected_contDiffOn_of_continuous_weak_columns
    {m : ℕ} {u : Plane → EuclideanSpace ℝ (Fin m)}
    {P : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
    (hu : MemLp u 2 (volume.restrict (Metric.ball (0 : Plane) 2)))
    (hP : ∀ i, MemLp (P i) 2 (volume.restrict (Metric.ball (0 : Plane) 2)))
    (hW : ∀ i b, HasWeakPartialDeriv i (fun x => P i x b)
      (fun x => u x b) (Metric.ball (0 : Plane) 2))
    (huc : ContinuousOn u (Metric.ball (0 : Plane) 2))
    (hPc : ∀ i, ContinuousOn (P i) (Metric.ball (0 : Plane) 2)) :
    ContDiffOn ℝ 1 u (Metric.ball (0 : Plane) 1) ∧
      ∀ x ∈ Metric.ball (0 : Plane) 1, ∀ i : Fin 2,
        fderiv ℝ u x (EuclideanSpace.single i 1) = P i x := by
  have hfd (x : Plane) (hx : x ∈ Metric.ball (0 : Plane) 1) :
      HasFDerivAt u (M60.suPlaneColumns (fun i => P i x)) x :=
    M60.suContinuous_weak_gradient_hasFDerivAt hu hP hW huc hPc x hx
  have hderiv : ContinuousOn (fderiv ℝ u) (Metric.ball (0 : Plane) 1) := by
    apply (M60.suPlaneColumns_continuousOn (fun i =>
      (hPc i).mono (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)))).congr
    intro x hx
    exact (hfd x hx).fderiv
  refine ⟨?_, ?_⟩
  · rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
    exact ⟨fun x hx => (hfd x hx).differentiableAt.differentiableWithinAt,
      by simp, contDiffOn_zero.mpr hderiv⟩
  · intro x hx i
    rw [(hfd x hx).fderiv]
    fin_cases i <;> simp [M60.suPlaneColumns]

end PoincareMT
