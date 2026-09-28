import PoincareMT.Proofs.M64.Sec19_4_Approximation.RawBoundaryReparam
import PoincareMT.Proofs.M58.Sec18_4_LoopTopology

/-!
# Joint continuity and nullity of raw polygon boundaries

Every M63 raw approximation uses one flattening profile for the whole
family. Its fixed inverse circle relabeling transports joint continuity
and nullity of the flattened C1 family to the literal polygon boundaries.

Morgan--Tian context: Section 19.4, Definition 19.18 and Claims 19.19-19.22, printed pp.
450-453.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
  {zeta : ℝ}

/-- The fixed inverse flattening relabeling transfers joint continuity to the actual polygon
boundary. Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp.
450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_boundary_continuous_of_M63
    (A : M63RawApproximation F Gamma zeta)
    (boundary : ∀ z, M64PolygonBoundary (A.polygon z)) :
    Continuous (fun p : LoopTwoSphere × LoopCircle => (boundary p.1).map p.2) := by
  let r := m64CircleReparamFromFlattening A.count A.count_positive
  have h : Continuous (fun p : LoopTwoSphere × LoopCircle =>
      (A.family p.1) (r.map p.2)) :=
    Proofs.M58.continuous_loop_eval.comp
      ((A.family.continuous.comp continuous_fst).prodMk
        (r.continuous_map.comp continuous_snd))
  apply h.congr
  intro p
  exact (m64_polygon_boundary_eq_flattened_family A.count_positive
    (boundary := boundary p.1) (A.angular_eq p.1) p.2).symm

/-- The angular lift of the continuous circle boundary is the jointly continuous raw polygon
map. Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453;
project construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_polygon_continuous_of_M63
    (A : M63RawApproximation F Gamma zeta) :
    Continuous (fun p : LoopTwoSphere × ℝ => (A.polygon p.1).map p.2) := by
  let boundary : ∀ z, M64PolygonBoundary (A.polygon z) :=
    fun z => Classical.choice (exists_polygon_boundary (A.polygon z))
  have hangle : Continuous m64LoopCircleParam := by
    change Continuous (fun x : ℝ =>
      (⟨Proofs.M58.angularPoint x, Proofs.M58.norm_angularPoint x⟩ : LoopCircle))
    exact Proofs.M58.contDiff_angularPoint.continuous.subtype_mk _
  have h := (m64_boundary_continuous_of_M63 A boundary).comp
    (continuous_fst.prodMk (hangle.comp continuous_snd))
  apply h.congr
  intro p
  exact (boundary p.1).angular_eq p.2

/-- The same inverse flattening relabeling transports nullity to each raw polygon boundary.
Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project
construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_raw_null_of_M63
    (A : M63RawApproximation F Gamma zeta)
    (boundary : ∀ z, M64PolygonBoundary (A.polygon z)) (z : LoopTwoSphere) :
    M64RawNullLoop (boundary z).map := by
  exact m64RawNullLoop_of_boundary_reparam (A.null_family z)
    (m64CircleReparamFromFlattening A.count A.count_positive)
    (m64_polygon_boundary_eq_flattened_family A.count_positive
      (boundary := boundary z) (A.angular_eq z))

/-- All raw boundary fields follow from M63 once the actual short annuli have been
constructed. Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp.
450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
noncomputable def m64RawBoundaryAnnulusPackage_of_annuli
    [T2Space M] [SecondCountableTopology M]
    (A : M63RawApproximation F Gamma zeta)
    (annulus : ∀ z,
      M64Annulus (F.metric a) (periodicFreeLoop (Gamma z)) (A.polygon z).map)
    (hpiecewise : ∀ z, M64PiecewiseC1Annulus (annulus z))
    (hgeodesic : ∀ z, M64GeodesicAnnulus (F.connection a) (annulus z))
    (harea : ∀ z, 0 ≤ (annulus z).area ∧ (annulus z).area < zeta) :
    M64RawBoundaryAnnulusPackage A := by
  let boundary : ∀ z, M64PolygonBoundary (A.polygon z) :=
    fun z => Classical.choice (exists_polygon_boundary (A.polygon z))
  exact {
    boundary := boundary
    reparam := fun _ => m64CircleReparamFromFlattening A.count A.count_positive
    boundary_eq_family := fun z =>
      m64_polygon_boundary_eq_flattened_family A.count_positive
        (boundary := boundary z) (A.angular_eq z)
    polygon_continuous := m64_polygon_continuous_of_M63 A
    boundary_continuous := m64_boundary_continuous_of_M63 A boundary
    raw_null := m64_raw_null_of_M63 A boundary
    annulus := annulus
    annulus_piecewise := hpiecewise
    annulus_geodesic := hgeodesic
    annulus_area := harea }

end PoincareMT
