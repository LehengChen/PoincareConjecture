import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarFreeModulusApproximation
import PoincareMT.Definitions.M63Ramp

/-!
# Free modulus uniformization for the actual M63 boundary curves

The scalar annular uniformization is proved for C1 boundary curves.  This
file supplies that regularity from the C2 shrinking-curve fields already
present in the M63 contract, so the free-boundary supplier is available at
every included flow time without a new analytic premise.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}

/-- The actual M63 C2 shrinking-curve slices supply the C1 input of free conformal-modulus
approximation. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64FreeConformalModulusApproximation_of_c2_slices
    {circumference : ℝ} (P : M62.CircleProductData F circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) :
    M64FreeConformalModulusApproximation (P.flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t) := by
  have h0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 1 (fun x => c0 x t) :=
    (hc0.spatial_regular t (hc0.domain_subset ht)).of_le (by norm_num)
  have h1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 1 (fun x => c1 x t) :=
    (hc1.spatial_regular t (hc1.domain_subset ht)).of_le (by norm_num)
  exact M64Uniformization.m64FreeConformalModulusApproximation_of_C1
    (n := n + 1) (M := P.charts.Point) (P.flow.metric t) h0 h1

end PoincareMT
