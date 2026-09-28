import PoincareMT.Proofs.M64.Sec19_3_Annuli.ProductRicciTraceBound

/-!
# Sharp product Ricci bound for the actual map energy

Each actual source column obeys the product Ricci quadratic bound. Their
sum is bounded by the energy density, without a positive-rank condition.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

/-- The actual two-column energy Ricci term has coefficient `2*(n-1)`. Degenerate source
differentials require no separate rank argument. Source: Morgan--Tian (2007), Lemma 19.15
and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64CircleProduct_energyRicci_abs_le
    (P : M62.CircleProductData F circumference) (hn : 1 ≤ n)
    (t : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K)
    (f : LoopPlane → P.charts.Point) (p : LoopPlane) :
    let d := mfderiv (𝓡 2) (𝓡 (n + 1)) f p
    |(P.flow.connection t).ricci (f p)
        (d (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (d (EuclideanSpace.basisFun (Fin 2) ℝ 0)) +
      (P.flow.connection t).ricci (f p)
        (d (EuclideanSpace.basisFun (Fin 2) ℝ 1))
        (d (EuclideanSpace.basisFun (Fin 2) ℝ 1))| ≤
      2 * ((n : ℝ) - 1) * K * m60EnergyDensity (P.flow.metric t) f p := by
  let d := mfderiv (𝓡 2) (𝓡 (n + 1)) f p
  let u := fun i : Fin 2 => d (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have h0 := m64CircleProduct_ricci_quadratic_abs_le P hn t hK (f p)
    (hcurv (f p).1) (u 0)
  have h1 := m64CircleProduct_ricci_quadratic_abs_le P hn t hK (f p)
    (hcurv (f p).1) (u 1)
  calc
    _ ≤ |(P.flow.connection t).ricci (f p) (u 0) (u 0)| +
        |(P.flow.connection t).ricci (f p) (u 1) (u 1)| := abs_add_le _ _
    _ ≤ ((n : ℝ) - 1) * K * (P.flow.metric t).inner (f p) (u 0) (u 0) +
        ((n : ℝ) - 1) * K * (P.flow.metric t).inner (f p) (u 1) (u 1) :=
      add_le_add h0 h1
    _ = _ := by
      simp only [m60EnergyDensity, Matrix.trace, Fin.sum_univ_two, m60AreaGram]
      change ((n : ℝ) - 1) * K * (P.flow.metric t).inner (f p) (u 0) (u 0) +
        ((n : ℝ) - 1) * K * (P.flow.metric t).inner (f p) (u 1) (u 1) =
        2 * ((n : ℝ) - 1) * K * ((1 / 2 : ℝ) *
          ((P.flow.metric t).inner (f p) (u 0) (u 0) +
            (P.flow.metric t).inner (f p) (u 1) (u 1)))
      ring

end PoincareMT
