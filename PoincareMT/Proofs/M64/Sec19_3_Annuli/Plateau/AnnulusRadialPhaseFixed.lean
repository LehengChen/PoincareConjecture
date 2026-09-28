import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialAffineFilling

/-!
# Literal fixed lower trace after the polar phase shift

The actual polar trace uses angle `x - pi`. Periodicity transports its
closed fixed half to every angle on the lower unit semicircle, exactly
as required by the fixed-diameter H1 filling.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareMT

open Proofs.M58

/-- A pi phase shift transfers the literal prescribed half-period trace to the geometric
lower semicircle. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64Periodic_lower_semicircle_shift
    {M : Type*} (gamma : ℝ → M) (b : LoopPlane → M)
    (hP : Function.Periodic gamma curvePeriod)
    (hfixed : ∀ x ∈ Icc (0 : ℝ) Real.pi, gamma x = b (angularPoint (x - Real.pi))) :
    ∀ t, angularPoint t 1 ≤ 0 → gamma (t + Real.pi) = b (angularPoint t) := by
  have hperiod : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hang : Function.Periodic angularPoint curvePeriod := by
    intro x
    ext i
    fin_cases i <;> simp [angularPoint, curvePeriod]
  have hshift : Function.Periodic (fun x => angularPoint (x - Real.pi)) curvePeriod := by
    intro x
    change angularPoint (x + curvePeriod - Real.pi) = angularPoint (x - Real.pi)
    rw [show x + curvePeriod - Real.pi = (x - Real.pi) + curvePeriod by ring, hang]
  intro t ht
  let y := toIcoMod hperiod 0 (t + Real.pi)
  have hy : y ∈ Ico (0 : ℝ) curvePeriod := toIcoMod_mem_Ico' hperiod _
  have hgy : gamma y = gamma (t + Real.pi) := by
    simpa only [y, toIcoMod, neg_smul, sub_eq_add_neg] using
      (hP.zsmul (-toIcoDiv hperiod 0 (t + Real.pi))) (t + Real.pi)
  have hangle : angularPoint (y - Real.pi) = angularPoint t := by
    have h : angularPoint (y - Real.pi) = angularPoint ((t + Real.pi) - Real.pi) := by
      simpa only [y, toIcoMod, neg_smul, sub_eq_add_neg] using
        (hshift.zsmul (-toIcoDiv hperiod 0 (t + Real.pi))) (t + Real.pi)
    simpa only [add_sub_cancel_right] using h
  have hyle : y ≤ Real.pi := by
    by_contra hn
    have hs := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr (lt_of_not_ge hn))
      (show y - Real.pi < Real.pi by unfold curvePeriod at hy; linarith [hy.2])
    have hpositive : 0 < angularPoint (y - Real.pi) 1 := by
      simpa only [angularPoint, Matrix.cons_val_one, Matrix.cons_val_zero] using hs
    rw [hangle] at hpositive
    exact (not_lt_of_ge ht) hpositive
  rw [← hgy, hfixed y ⟨hy.1, hyle⟩, hangle]

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 gamma : ℝ → M}

/-- Shift the actual lower-extension circle trace to the fixed lower semicircle used by the
disk filling. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem M64ObservedWeakAnnulus.lower_circle_fixed_shift
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hei : IsClosedEmbedding e) (hc0 : Continuous c0) (hgamma : Continuous gamma)
    (hP : Function.Periodic gamma curvePeriod)
    {a : LoopPlane} (ha : a 1 = 0) {r : ℝ} (hr : 0 < r)
    (htrace : gamma =ᵐ[volume.restrict (Icc (0 : ℝ) curvePeriod)]
      (fun x => A.lowerExtensionMap (a + r • angularPoint (x - Real.pi)))) :
    ∀ t, angularPoint t 1 ≤ 0 → gamma (t + Real.pi) = c0 ((a + r • angularPoint t) 0) :=
  m64Periodic_lower_semicircle_shift gamma (fun z => c0 ((a + r • z) 0)) hP
    (fun _ hx => A.lower_circle_fixed_trace hei hc0 hgamma ha hr htrace hx)

/-- The prescribed curve extended horizontally and rescaled on the plane is C1. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64RadialBoundaryPlane_contMDiff
    {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c) (a : LoopPlane) (r : ℝ) :
    ContMDiff (𝓡 2) (𝓡 n) 1 (fun z : LoopPlane => c ((a + r • z) 0)) := by
  have hscalar : ContDiff ℝ 1 (fun z : LoopPlane => (a + r • z) 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp
      (contDiff_const.add (contDiff_id.const_smul r))
  exact hc.comp hscalar.contMDiff

omit [TopologicalSpace M] in
/-- The horizontal prescribed boundary extension is invariant under reflection across the
radial axis. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64RadialBoundaryPlane_reflection (c : ℝ → M) (a : LoopPlane) (r : ℝ)
    (z : LoopPlane) : c ((a + r • m60PlaneReflection z) 0) = c ((a + r • z) 0) := by
  simp only [PiLp.add_apply, PiLp.smul_apply, m60PlaneReflection_apply, if_true]

end PoincareMT
