import PoincareMT.Proofs.M60.Def18_17_FillingArea.CollarGluing

/-!
The exact collar data and M60 gluing construction used to attach the projected annulus to an
actual spanning disk.

Morgan--Tian context: Section 19.6, Lemmas 19.30-19.31, printed pp. 461-466.
-/

set_option autoImplicit false

open Set MeasureTheory Metric
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

/-- The exact M60 data needed to attach a collar to one disk. The area bound is separated
from the M60 construction so a projected M64 annulus can be used as the comparison quantity
supplied by the geometric producer. Source: Auxiliary step for MT Lemma 19.30, p. 462; the
actual half-disk collar in `proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
structure M64DiskCollarCertificate
    {gamma0 gamma1 : C1FreeLoopSpace (M := M)}
    (D : LipschitzSpanningDisk g gamma0) (q eta : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  map : LoopPlane → M
  reparameterization : CircleReparameterization
  matching : ∀ z : LoopPlane, ‖z‖ = radius →
    D.map (radius⁻¹ • z) = map z
  boundary : ∀ z : LoopCircle,
    map z = gamma1 (reparameterization.map z)
  lipschitz_constant : ℝ
  lipschitz_nonnegative : 0 ≤ lipschitz_constant
  lipschitz_on_annulus : ∀ x ∈ loopDiskSet ∩ {z | radius ≤ ‖z‖},
    ∀ y ∈ loopDiskSet ∩ {z | radius ≤ ‖z‖},
      g.edist (map x) (map y) ≤
        ENNReal.ofReal lipschitz_constant * ENNReal.ofReal ‖x - y‖
  area_integrable : IntegrableOn (m60AreaDensity g map)
    ((closedBall (0 : LoopPlane) radius)ᶜ ∩ loopDiskSet) volume
  area_bound : (∫ z in (closedBall (0 : LoopPlane) radius)ᶜ ∩ loopDiskSet,
      m60AreaDensity g map z) ≤ q + eta

/-- Glue an exact-boundary disk and its actual outer collar with the retained area bound.
Source: Auxiliary step for MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64DiskWitness_of_collar
    {gamma0 gamma1 : C1FreeLoopSpace (M := M)}
    (D : LipschitzSpanningDisk g gamma0) (q eta : ℝ)
    (C : M64DiskCollarCertificate (gamma1 := gamma1) D q eta) :
    ∃ D' : LipschitzSpanningDisk g gamma1,
      D'.area ≤ D.area + q + eta := by
  obtain ⟨D', _, harea⟩ := m60DiskGluing_of_collar g D
    C.radius_pos C.radius_lt_one C.map C.reparameterization
    C.matching C.boundary C.lipschitz_nonnegative C.lipschitz_on_annulus
    C.area_integrable
  refine ⟨D', ?_⟩
  linarith [harea, C.area_bound]

end PoincareMT
