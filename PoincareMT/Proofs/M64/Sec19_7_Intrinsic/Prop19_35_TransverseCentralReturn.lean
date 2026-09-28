import PoincareMT.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CentralReturnSelection
import PoincareMT.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TransverseRetainedBases

/-!
# Selecting a transverse central circle return

Removing the null set of regular inner-circle tangent contacts preserves
the actual retained base mass. The central-return selector then gives a
transverse circle return with the original capacity budget and central
length bounds. This is a formal tool for the retained-base treatment of
Morgan--Tian, Lemma 19.46, printed pp. 477-478; see
`derivations/2026-09-25-transverse-central-return.md`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology Manifold ContDiff Bundle Matrix

namespace PoincareMT

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- The original endpoint-capacity budget selects an actual central
circle return whose circle tangent and normal-fiber velocity are
independent. The measurable null-set removal adds no hypothesis or loss
to the central selector. This supports the formal retained-base treatment
of Morgan--Tian, Lemma 19.46, printed pp. 477-478. -/
theorem m64Intrinsic_exists_transverse_central_circle_return
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (he : ContDiff ℝ ∞ e) {height : ℝ → ℝ} (hh : Measurable height)
    {a b epsilon : ℝ} (hab : a < b) (hepsilon : 0 < epsilon)
    (harc : 2 * epsilon < intrinsicBoundaryLength N.metric 1 a b)
    {Z : Set ℝ} (hZ : MeasurableSet Z) (hZsub : Z ⊆ Icc a b)
    (hinj : InjOn (fun z => e !₂[z, height z]) Z)
    (hregular : ∀ z ∈ Z, Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[z, height z]))
    {target : ℝ → AnnulusCoordinates} (htarget : ContDiff ℝ ∞ target)
    {rho : ℝ} (hrho : 0 ≤ rho) (htargetInj : InjOn target (Icc 0 rho))
    (hunit : ∀ t ∈ Icc 0 rho,
      N.metric.inner (target t) (deriv target t) (deriv target t) = 1)
    (hend : ∀ z ∈ Z, e !₂[z, height z] ∈
      intrinsicAnnulusBoundary 1 '' Icc a b ∪ target '' Icc 0 rho)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ z ∈ Z, ∀ v : AnnulusCoordinates,
      c ^ 2 * (intrinsicBoundarySpeed N.metric 1 z ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (e !₂[z, height z])
          (fderiv ℝ e !₂[z, height z] v) (fderiv ℝ e !₂[z, height z] v))
    (hbudget : rho < c * ((∫ z in Z, intrinsicBoundarySpeed N.metric 1 z) - 2 * epsilon)) :
    ∃ z ∈ Z, ∃ w ∈ Icc a b,
      z ∈ Ioo a b ∧ e !₂[z, height z] = intrinsicAnnulusBoundary 1 w ∧
      e !₂[z, height z] ∉ target '' Icc 0 rho ∧
      epsilon ≤ intrinsicBoundaryLength N.metric 1 a z ∧
      epsilon ≤ intrinsicBoundaryLength N.metric 1 z b ∧
      LinearIndependent ℝ
        (![deriv (intrinsicAnnulusBoundary 1) w,
          fderiv ℝ e !₂[z, height z] !₂[0, 1]] : Fin 2 → AnnulusCoordinates) := by
  obtain ⟨Y, hY, hYZ, _, _, hmass, htransverse⟩ :=
    m64Intrinsic_exists_transverse_retained_bases e he
      (m64Intrinsic_contDiff_boundary 1) hZ
  have hbudgetY :
      rho < c * ((∫ z in Y, intrinsicBoundarySpeed N.metric 1 z) - 2 * epsilon) := by
    rw [hmass (intrinsicBoundarySpeed N.metric 1)]
    exact hbudget
  obtain ⟨z, hz, w, hw, hzab, hcircle, hnot, hleft, hright⟩ :=
    m64Intrinsic_exists_central_circle_return N e he hh hab hepsilon harc hY
      (hYZ.trans hZsub) (hinj.mono hYZ) (fun z hz => hregular z (hYZ hz))
      htarget hrho htargetInj hunit (fun z hz => hend z (hYZ hz)) hc
      (fun z hz => hbound z (hYZ hz)) hbudgetY
  exact ⟨z, hYZ hz, w, hw, hzab, hcircle, hnot, hleft, hright,
    htransverse z hz (height z) w hcircle (hregular z (hYZ hz))⟩

end PoincareMT
