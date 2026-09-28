import PoincareMT.Definitions.Ch05.Compactness
import PoincareMT.Proofs.M07.Geometry.Manifold.ZeroDimensional

/-! Compatibility bridge to Mapher's frozen compactness carrier declarations. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

/-- Connected zero-dimensional flow carriers have at most one point. -/
theorem FlowCarrier.subsingleton_zero (C : FlowCarrier 0) : Subsingleton C.carrier := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 0)) C.carrier := C.chartedSpace
  let : PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩
  exact Poincare.subsingleton_of_preconnected_euclidean_zero C.carrier

end PoincareMT
