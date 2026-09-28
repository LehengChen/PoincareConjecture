import PoincareMT.Proofs.M64.Sec19_4_Approximation.PolygonCellBoundaryNull

/-!
# Cellwise-to-global column bounds

The open polygon cells cover the annulus domain almost everywhere.  This
adapter lifts any vertical-column inequality established on each cell
interior to the restricted-domain almost-everywhere form consumed by the area
estimate.

Morgan--Tian context: Section 19.4, Definition 19.18 and Claims 19.19-19.22, printed pp.
450-453.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- A vertical-column bound on every open polygon cell holds almost everywhere on the
rectangle. Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp.
450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_vertical_column_ae_of_cellwise
    {N : ℕ} (hN : 0 < N) {f : LoopPlane → M} {K : ℝ}
    (hcell : ∀ j : Fin N, ∀ p ∈ interior (m64PolygonCellSet j),
      g.tangentNorm (f p)
          (mfderiv (𝓡 2) (𝓡 n) f p
            (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ K) :
    ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      g.tangentNorm (f p)
          (mfderiv (𝓡 2) (𝓡 n) f p
            (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ K := by
  filter_upwards [m64_polygon_cells_interior_ae hN] with p hp
  obtain ⟨j, hj⟩ := hp
  exact hcell j p hj

end PoincareMT
