import PoincareMT.Statements.Ch09.NeckCapTopology

/-!
# M25 repaired neck/cap topology data

The redesign keeps the local compatible region certificate separate from the
whole-cover conclusion supplied by the Appendix A statement layer.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

/-- A local neck/cap output retains its region branch and compatibility bounds. -/
structure RepairedNeckCapTopologyData
    (g : RiemannianMetric 3 M) (H : ConnectedNeckCapCover g) where
  region : NeckCapRegion g H.X
  compatible : NeckCapRegionCompatible g H region

end PoincareMT
