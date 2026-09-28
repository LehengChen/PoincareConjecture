import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusCurveDisplacement
import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryNormalChart

/-!
# Local target-chart transport of a disjoint displacement

The Euclidean dense-complement argument becomes an honest target-space
perturbation once a single smooth chart contains both boundary curves.  The
chart source/target memberships are explicit: the compact translation-radius
lemma keeps the translated coordinates in the target, and the inverse chart
then gives the M-valued curve.  This file does not claim that an arbitrary pair
of curves lies in one chart.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology Manifold ContDiff

namespace PoincareMT.M64

/-- A common target chart in dimension at least three transports an arbitrarily small
disjoint Euclidean displacement. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp.
447-449. -/
theorem exists_small_chart_displacement_disjoint
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {cchart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hn : 3 ≤ n) {P eps : ℝ} (hP : 0 < P) (heps : 0 < eps)
    {c0 c1 : ℝ → M}
    (_hsource0 : ∀ x, c0 x ∈ cchart.source)
    (hsource1 : ∀ x, c1 x ∈ cchart.source)
    (hcoord0 : ContDiff ℝ 1 (fun x => cchart (c0 x)))
    (hcoord1 : ContDiff ℝ 1 (fun x => cchart (c1 x)))
    (hp0 : Function.Periodic c0 P) (hp1 : Function.Periodic c1 P) :
    ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ < eps ∧
      (∀ x, cchart (c1 x) + v ∈ cchart.target) ∧
      Function.Periodic (fun x => cchart.symm (cchart (c1 x) + v)) P ∧
      Continuous (fun x => cchart.symm (cchart (c1 x) + v)) ∧
      ContDiff ℝ 1 (fun x => cchart (c1 x) + v) ∧
      Disjoint (range c0)
        (range (fun x => cchart.symm (cchart (c1 x) + v))) := by
  let u0 : ℝ → EuclideanSpace ℝ (Fin n) := fun x => cchart (c0 x)
  let u1 : ℝ → EuclideanSpace ℝ (Fin n) := fun x => cchart (c1 x)
  have hu0 : ContDiff ℝ 1 u0 := hcoord0
  have hu1 : ContDiff ℝ 1 u1 := hcoord1
  have hpu0 : Function.Periodic u0 P := by
    intro x
    exact congrArg (fun z : M => cchart z) (hp0 x)
  have hpu1 : Function.Periodic u1 P := by
    intro x
    exact congrArg (fun z : M => cchart z) (hp1 x)
  have hu1target : ∀ x ∈ Icc (0 : ℝ) P, u1 x ∈ cchart.target := by
    intro x hx
    exact cchart.map_source (hsource1 x)
  obtain ⟨δ, hδ, hδε, hroom⟩ :=
    exists_translation_radius_subset_open cchart.open_target hP
      hu1.continuous hpu1 hu1target heps
  obtain ⟨v, hv, hvperiod, hvregular, hvdisjoint⟩ :=
    exists_small_euclidean_periodic_translation_disjoint hn hδ hu0 hu1 hpu0 hpu1
  have hvsmall : ‖v‖ < eps := hv.trans_le hδε
  have hvtarget : ∀ x, u1 x + v ∈ cchart.target := hroom v hv
  have hperiod : Function.Periodic (fun x => cchart.symm (u1 x + v)) P := by
    intro x
    change cchart.symm (u1 (x + P) + v) = cchart.symm (u1 x + v)
    rw [show u1 (x + P) + v = u1 x + v by rw [hpu1 x]]
  have hcontinuous : Continuous (fun x => cchart.symm (u1 x + v)) := by
    apply cchart.continuousOn_symm.comp_continuous
      (hu1.continuous.add continuous_const)
    exact hvtarget
  refine ⟨v, hvsmall, hvtarget, hperiod, hcontinuous, hvregular, ?_⟩
  rw [disjoint_left]
  intro z hz0 hz1
  rcases hz0 with ⟨x, hx⟩
  rcases hz1 with ⟨y, hy⟩
  have heq := congrArg (fun q : M => cchart q) (hx.trans hy.symm)
  have heq' : u0 x = u1 y + v := by
    simpa only [u0, u1, Function.comp_apply, cchart.right_inv (hvtarget y)] using heq
  exact Set.disjoint_left.mp hvdisjoint
    (show u0 x ∈ range u0 from ⟨x, rfl⟩)
    (show u0 x ∈ range (fun x => u1 x + v) from ⟨y, heq'.symm⟩)

/-!
The same displacement has a genuine smooth manifold-valued representative when
the inverse chart is smooth on its target.  This is a transport theorem for
the concrete perturbation above, rather than a regularity assumption on the
target curve.
-/
/-- A C1 inverse chart makes the actual displaced target curve C1 while retaining
disjointness. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem exists_small_chart_displacement_disjoint_smooth
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {cchart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hn : 3 ≤ n) {P eps : ℝ} (hP : 0 < P) (heps : 0 < eps)
    {c0 c1 : ℝ → M}
    (hsource0 : ∀ x, c0 x ∈ cchart.source)
    (hsource1 : ∀ x, c1 x ∈ cchart.source)
    (hcoord0 : ContDiff ℝ 1 (fun x => cchart (c0 x)))
    (hcoord1 : ContDiff ℝ 1 (fun x => cchart (c1 x)))
    (hp0 : Function.Periodic c0 P) (hp1 : Function.Periodic c1 P)
    (hchartSymm : ContMDiffOn (𝓡 n) (𝓡 n) 1 cchart.symm cchart.target) :
    ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ < eps ∧
      (∀ x, cchart (c1 x) + v ∈ cchart.target) ∧
      Function.Periodic (fun x => cchart.symm (cchart (c1 x) + v)) P ∧
      Continuous (fun x => cchart.symm (cchart (c1 x) + v)) ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1
        (fun x => cchart.symm (cchart (c1 x) + v)) ∧
      ContDiff ℝ 1 (fun x => cchart (c1 x) + v) ∧
      Disjoint (range c0)
        (range (fun x => cchart.symm (cchart (c1 x) + v))) := by
  obtain ⟨v, hv, hvtarget, hperiod, hcontinuous, hvregular, hvdisjoint⟩ :=
    exists_small_chart_displacement_disjoint hn hP heps hsource0 hsource1
      hcoord0 hcoord1 hp0 hp1
  have hcoordMD : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1
      (fun x => cchart (c1 x) + v) :=
    contMDiff_iff_contDiff.mpr hvregular
  have htargetMD := hchartSymm.comp_contMDiff hcoordMD
    (fun x => hvtarget x)
  have htargetMD' : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1
      (fun x => cchart.symm (cchart (c1 x) + v)) := by
    simpa only [Function.comp_def] using htargetMD
  exact ⟨v, hv, hvtarget, hperiod, hcontinuous, htargetMD', hvregular,
    hvdisjoint⟩

end PoincareMT.M64
