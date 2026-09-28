import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceFamilyScales
import PoincareMT.Proofs.M28.Generalized.StrongNeckHalfFlow
import PoincareMT.Proofs.M28.Generalized.StrongNeckSourceMetricSpace

/-!
# The indexed normalized flows of the actual selected source necks

Claims 10.6-10.11, Morgan--Tian pp. 252-255. Choose a point on each actual
retained segment, keep its original strong neck, and select its M12/M13 raw
rescaling once. Every source flow, metric, source neck and center below uses
that same choice. The actual source scalars diverge. This supplies the model
part of the source-family producer; normal covers remain separate geometry.
See M28 derivations 20 and 30.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  (H : CounterexampleNeckFamily E) (v : ℕ → ℝ)
  (hv : ∀ k, v k ∈ Icc (H.segment k).lower (H.segment k).upper)

/-- The literal original strong neck at the chosen retained point;
Claims 10.6-10.11, printed pp. 252-255. -/
def selectedOriginalNeck (k : ℕ) :
    GeneralizedStrongNeck (E (k + H.shift)).flow (E (k + H.shift)).time epsilon :=
  (H.segment k).neckAt (v k) (hv k)

/-- The actual open source carrier of the chosen original neck;
Definition 9.78 and Claims 10.6-10.11, pp. 252-255. -/
abbrev selectedSourceOpen (k : ℕ) :
    TopologicalSpace.Opens ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier :=
  strongNeckOpen (H.selectedOriginalNeck v hv k)

/-- Choose the actual raw M12/M13 rescaling once per source index;
Claims 10.6-10.11, printed pp. 252-255. -/
noncomputable def rawSourceRescaling (k : ℕ) :
    RescaledRawCylinderData (U := H.selectedSourceOpen v hv k)
      (J := strongNeckBackwardInterval)
      (strongNeckCylinder (H.selectedOriginalNeck v hv k))
      (GeneralizedStrongNeck.physical_interval_subset (H.selectedOriginalNeck v hv k)) :=
  Classical.choice (GeneralizedStrongNeck.exists_rescaled_raw_cylinder_flow
    (H.selectedOriginalNeck v hv k))

/-- Every normalized flow has the same literal included half-window and
uses its selected raw rescaling; Claims 10.6-10.11, pp. 252-255. -/
noncomputable def normalizedSourceFlow (k : ℕ) :
    RicciFlow 3 (H.selectedSourceOpen v hv k) (Icc (-(1 / 2 : ℝ)) 0) :=
  GeneralizedStrongNeck.rescaled_half_flow
    (H.selectedOriginalNeck v hv k) (H.rawSourceRescaling v hv k)

/-- The source neck belongs to the exact indexed flow metric at time zero;
Claims 10.6-10.11, printed pp. 252-255. -/
noncomputable def normalizedSourceNeck (k : ℕ) :
    EpsilonNeck ((H.normalizedSourceFlow v hv k).metric 0) :=
  GeneralizedStrongNeck.rescaled_half_source_neck
    (H.selectedOriginalNeck v hv k) (H.rawSourceRescaling v hv k)
      (H.segment k).epsilon_lt_half

/-- The chosen source metric space uses the same actual normalized metric,
with the inherited topology; Claims 10.6-10.11, pp. 252-255. -/
@[instance_reducible] noncomputable def normalizedSourceMetricSpace (k : ℕ) :
    MetricSpace (H.selectedSourceOpen v hv k) :=
  GeneralizedStrongNeck.rescaled_source_metricSpace
    (H.selectedOriginalNeck v hv k) (H.rawSourceRescaling v hv k)

/-- Source inclusion sends each normalized center to the selected point
of its actual retained segment; Claims 10.6-10.11, pp. 252-255. -/
theorem normalizedSourceNeck_center_val (k : ℕ) :
    ((H.normalizedSourceNeck v hv k).center :
      ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier) =
      (H.segment k).path (v k) :=
  (H.segment k).neckAt_center (v k) (hv k)

/-- Every normalized source center has scalar exactly one in its own
chosen flow connection; Claims 10.6-10.11, pp. 252-255. -/
theorem normalizedSourceNeck_scalar_one (k : ℕ) :
    ((H.normalizedSourceFlow v hv k).connection 0).scalarCurvature
      (H.normalizedSourceNeck v hv k).center = 1 :=
  GeneralizedStrongNeck.rescaled_half_scalar_at_center
    (H.selectedOriginalNeck v hv k) (H.rawSourceRescaling v hv k)

/-- Source metric instances retain the actual inherited topology;
the normal-cover input for Claims 10.6-10.11, pp. 252-255. -/
theorem normalizedSourceMetricSpace_topology (k : ℕ) :
    let d := H.normalizedSourceMetricSpace v hv k
    (inferInstance : TopologicalSpace (H.selectedSourceOpen v hv k)) =
      d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :=
  GeneralizedStrongNeck.rescaled_source_metricSpace_topology
    (H.selectedOriginalNeck v hv k) (H.rawSourceRescaling v hv k)

/-- The ordinary source distance is the exact normalized flow distance,
without any ambient-distance replacement; Claims 10.6-10.11, pp. 252-255. -/
theorem normalizedSourceMetricSpace_edist (k : ℕ)
    (x y : H.selectedSourceOpen v hv k) :
    letI := H.normalizedSourceMetricSpace v hv k
    edist x y = ((H.normalizedSourceFlow v hv k).metric 0).edist x y :=
  GeneralizedStrongNeck.rescaled_source_metricSpace_edist
    (H.selectedOriginalNeck v hv k) (H.rawSourceRescaling v hv k) x y

/-- The actual original scalars at these indexed model centers diverge,
so the later pinching argument concerns these same models and centers;
Claim 10.11, printed p. 255. -/
theorem normalizedSource_original_scalar_tendsto_atTop :
    Tendsto (fun k => (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (H.normalizedSourceNeck v hv k).center.val⟩)
      atTop atTop :=
  H.neck_center_scalar_tendsto_atTop v hv

end PoincareMT.M28.CounterexampleNeckFamily
