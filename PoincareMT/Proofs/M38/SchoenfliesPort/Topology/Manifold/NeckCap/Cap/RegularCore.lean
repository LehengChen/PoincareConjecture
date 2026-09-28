import PoincareMT.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceRegularCore
import PoincareMT.Proofs.M38.SchoenfliesPort.Topology.Manifold.NeckCap.Cap.Boundary
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema.FiniteRegularity

/-! Local namespace adaptation for M38.
Original source: the matching relative module in Proofs/Horizon.
Source base: 779d92dc4 (2026-09-25 M38 assignment).
The local copy removes later-owner imports; mathematical proof bodies
and hypotheses are retained. See the generated provenance manifest. -/

open _root_.AddCircle
open _root_.PoincareMT
open _root_.PoincareMT.CapCertificate

namespace M38Schoenflies

/-! Deduplicated bridge for the Horizon snapshot module
`Topology.Manifold.NeckCap.Cap.RegularCore`.
Its constants already exist on main in
`PoincareMT.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceRegularCore`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

/-!
# Regularity of a cap core

The regular defining function at each boundary point rules out an isolated
boundary sheet: the closed core is the closure of its interior.

Reference: Morgan--Tian, Definition 9.72, pp. 230--231, and
Proposition A.21, Claims A.23--A.24, pp. 512--513.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)

theorem frontier_core_eq_boundary : frontier C.core = C.boundary_sphere := by
  rw [frontier, C.closure_core_eq_closed_core, (CapCertificate.isOpen_core C).interior_eq,
    (CapCertificate.boundary_eq_closed_core_diff_core C)]

end PoincareMT.CapCertificate

end M38Schoenflies
