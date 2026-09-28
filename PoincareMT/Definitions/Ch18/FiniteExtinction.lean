import PoincareMT.Definitions.Ch18.WidthEvolution
import PoincareMT.Definitions.Ch15.SurgeryFlow
import PoincareMT.Definitions.Ch17.GlobalSurgery
import PoincareMT.Definitions.Ch01.Topology
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Finite extinction for an actual surgery flow

The extinction interface is tied to the changing-carrier flow used in
Chapter 15.  M29 supplies the global flow certificate in Chapter 17.
Component ancestry is represented by the actual `SurgeryComponentPath` used by
the width milestone; no option-valued or unrelated flow is admitted.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

/-! A path component is tied to the actual ambient carrier, metric, and
scalar curvature at every time. -/
structure FlowComponentPath (F : SurgeryFlowData.{u}) (T : ℝ) where
  terminal_mem : T ∈ F.time_domain
  path : SurgeryComponentPath (F.slice 0).carrier 0 T
  ambient_eq : ∀ s : Set.Icc (0 : ℝ) T,
    (path.slice s).ambient = F.slice s.1
  ambient_metric_eq : ∀ s : Set.Icc (0 : ℝ) T,
    HEq (path.slice s).ambient_metric (F.metric s.1)
  scalar_pullback : ∀ (s : Set.Icc (0 : ℝ) T) x,
    (path.slice s).connection.scalarCurvature x =
      (F.connection s.1).scalarCurvature (cast
        (congrArg GeneralizedSliceCarrier.carrier (ambient_eq s))
        ((path.slice s).inclusion x))

def FlowComponentPath.inclusion {F : SurgeryFlowData.{u}} {T : ℝ}
    (P : FlowComponentPath F T) (s : Set.Icc (0 : ℝ) T) :
    (P.path.slice s).carrier.carrier → (F.slice s.1).carrier :=
  fun x => cast (congrArg GeneralizedSliceCarrier.carrier (P.ambient_eq s))
    ((P.path.slice s).inclusion x)

/-! M30's ancestry output.  One fixed initial family/class is transported to
each selected component, and every surviving point is covered by one of the
actual paths. -/
structure SurgeryFlowAncestry (F : SurgeryFlowData.{u}) where
  initial_family : FreeTwoSphereFamily (M := (F.slice 0).carrier)
  initial_class_nonzero : initial_family.homotopy_class ≠ 1
  path_for : ∀ (T : ℝ) (_hT : T ∈ F.time_domain)
      (_x : (F.slice T).carrier),
    FlowComponentPath F T
  component_cover : ∀ (T : ℝ) (hT : T ∈ F.time_domain)
      (x : (F.slice T).carrier),
      x ∈ Set.range ((path_for T hT x).inclusion
        ⟨T, ⟨F.time_domain_nonnegative hT, le_rfl⟩⟩)
  component_simply_connected : ∀ (T : ℝ) (hT : T ∈ F.time_domain)
      (x : (F.slice T).carrier),
      SimplyConnectedSpace
        ((path_for T hT x).path.slice
          ⟨T, ⟨F.time_domain_nonnegative hT, le_rfl⟩⟩).carrier.carrier
  initial_basepoint_agreement : ∀ (T : ℝ) (hT : T ∈ F.time_domain)
      (x : (F.slice T).carrier),
      (path_for T hT x).path.initial_identification initial_family.basepoint =
        ((path_for T hT x).path.slice
          ⟨0, ⟨le_rfl, F.time_domain_nonnegative hT⟩⟩).family.basepoint
  initial_family_agreement : ∀ (T : ℝ) (hT : T ∈ F.time_domain)
      (x : (F.slice T).carrier) (c : LoopTwoSphere) (z : LoopPlane),
      (((path_for T hT x).path.slice
        ⟨0, ⟨le_rfl, F.time_domain_nonnegative hT⟩⟩).family.family c).extension z =
        (path_for T hT x).path.initial_identification
          ((initial_family.family c).extension z)
  initial_width_bound : ∀ (T : ℝ) (hT : T ∈ F.time_domain)
      (x : (F.slice T).carrier),
      componentWidth ((path_for T hT x).path)
          ⟨0, ⟨le_rfl, F.time_domain_nonnegative hT⟩⟩ ≤
        classWidth (F.metric 0) initial_family

/-! The finite-time conclusion keeps the actual empty slice and permanence. -/
structure FiniteExtinctionConclusion (F : SurgeryFlowData.{u}) where
  extinction_time : ℝ
  extinction_mem : extinction_time ∈ F.time_domain
  extinct : IsEmpty (F.slice extinction_time).carrier
  /-- The selected extinction time is an actual singular event, so
  reconstruction can consume that event rather than an arbitrary empty time. -/
  extinction_surgery_mem : extinction_time ∈ F.surgery_times
  permanent_empty : ∀ t : ℝ, ∀ _ht : t ∈ F.time_domain,
    extinction_time ≤ t → IsEmpty (F.slice t).carrier

/-- The terminal event is the flow's actual event at the selected extinction time. -/
def FiniteExtinctionConclusion.terminal_vanishing_event
    {F : SurgeryFlowData.{u}} (E : FiniteExtinctionConclusion F) :
    SurgeryVanishingEventData F.parameters F.slice F.metric E.extinction_time := by
  letI := E.extinct
  exact F.vanishing_event E.extinction_time E.extinction_surgery_mem

end PoincareMT
