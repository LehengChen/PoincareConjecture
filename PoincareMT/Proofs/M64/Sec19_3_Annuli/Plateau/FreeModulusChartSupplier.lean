import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusChartUniformization

/-!
# Free modulus supplier from a single smooth target chart

The scalar free-uniformization producer already handles arbitrary admissible
seeds once both boundary curves are `ContMDiff`.  This export derives that
regularity from the coordinate hypotheses used by the target-chart chain, so
the exact public free-boundary quantifiers apply to the original curves.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Topology Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareMT.M64

/-- C1 coordinate curves in a common C1 target chart supply actual free conformal-modulus
approximation. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64FreeConformalModulusApproximation_of_chart_curves
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M}
    {cchart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {d c : ℝ → M}
    (hsourceD : ∀ x, d x ∈ cchart.source)
    (hsourceC : ∀ x, c x ∈ cchart.source)
    (hcoordD : ContDiff ℝ 1 (fun x => cchart (d x)))
    (hcoordC : ContDiff ℝ 1 (fun x => cchart (c x)))
    (hchartSymm : ContMDiffOn (𝓡 n) (𝓡 n) 1 cchart.symm cchart.target) :
    M64FreeConformalModulusApproximation g d c := by
  have hDMD : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 d := by
    have hcoordMD : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1
        (fun x => cchart (d x)) :=
      contMDiff_iff_contDiff.mpr hcoordD
    have hcomp := hchartSymm.comp_contMDiff hcoordMD
      (fun x => cchart.map_source (hsourceD x))
    convert hcomp using 1
    funext x
    exact (cchart.left_inv (hsourceD x)).symm
  have hCMD : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c := by
    have hcoordMD : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1
        (fun x => cchart (c x)) :=
      contMDiff_iff_contDiff.mpr hcoordC
    have hcomp := hchartSymm.comp_contMDiff hcoordMD
      (fun x => cchart.map_source (hsourceC x))
    convert hcomp using 1
    funext x
    exact (cchart.left_inv (hsourceC x)).symm
  exact M64Uniformization.m64FreeConformalModulusApproximation_of_C1
    g hDMD hCMD

end PoincareMT.M64
