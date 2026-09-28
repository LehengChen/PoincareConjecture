import PoincareMT.Statements.Ch01.Normalization
import PoincareMT.Proofs.M01.NormalizationMetric
import PoincareMT.Proofs.M01.NormalizationVolume
import PoincareMT.Proofs.M01.NormalizationTensorNorm
import PoincareMT.Proofs.M01.NormalizationScaling
import PoincareMT.Proofs.M01.NormalizationCurvature
import PoincareMT.Proofs.M01.NormalizationScaleChoice
import PoincareMT.Proofs.M01.NormalizationSmallBalls
import PoincareMT.Proofs.M01.NormalizationVolumeScaleChoice
import PoincareMT.Proofs.M01.ConnectionExistence
/-!
# Normalized initial metric existence proof assembly

The compact-manifold scaling, compatible-connection construction, calibrated
volume transport, and time-zero pinching bridge are the single admitted M01
obligation at the skeleton stage.
-/

/-! M01 is the numbered review and proof entry point. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

universe u

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M]

/-- M01: every compact Hausdorff second-countable smooth three-manifold with
its Borel measurable structure admits a complete normalized metric, compatible
connection and calibrated volume. The curvature norm is at most one, the
half-Euclidean volume bound holds for every radius 0 < r <= 1, and the initial
Hamilton-Ivey pinching inequalities hold at time zero.

Sources: Morgan-Tian Definition 4.10, p. 67; Chapter 15, Section 0.6, p. 353;
Corollary 15.10 proof, p. 363. Keep the stronger all-radius condition, as in
MT-NORMALIZATION-RADII, `reviews/errata/2026-09-10-analytic-outline-audit.md`. -/
theorem existsNormalizedInitialMetric
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] :
    Nonempty (NormalizedInitialMetricConclusion (M := M)) := by
  obtain ⟨g⟩ : Nonempty (RiemannianMetric 3 M) :=
    existsM01RiemannianMetric (n := 3) (M := M)
  obtain ⟨D⟩ : Nonempty (LeviCivitaData g) := m01_exists_leviCivitaData g
  obtain ⟨B, _hB, hcurv⟩ := m01_riemannEvaluation_uniform_bound D
  obtain ⟨r₀, hr₀, hball⟩ := m01_normalizedMetricVolume_uniform_lower_bound g
  let c := max (9 * B) ((1 / r₀) ^ 2) + 1
  have hc : 0 < c := by
    have h := le_max_right (9 * B) ((1 / r₀) ^ 2)
    dsimp [c]
    nlinarith [sq_nonneg (1 / r₀)]
  have hcB : 9 * B ≤ c := by
    have h := le_max_left (9 * B) ((1 / r₀) ^ 2)
    dsimp [c]
    linarith
  have hscale : 1 ≤ Real.sqrt c * r₀ := by
    have hs : 1 / r₀ ≤ Real.sqrt c := by
      apply Real.le_sqrt_of_sq_le
      have h := le_max_right (9 * B) ((1 / r₀) ^ 2)
      dsimp [c]
      linarith
    exact (div_le_iff₀ hr₀).mp hs
  let g' := m01RescaledMetric g c hc
  let D' := m01RescaledMetric_connection g D c hc
  suffices hdata : Nonempty (NormalizedInitialMetric (M := M)) by
    obtain ⟨data⟩ := hdata
    exact ⟨{ data := data
             initial_pinching := m01HamiltonIveyPinchedAt_zero_of_norm_le data.connection
               data.full_curvature_bound }⟩
  refine ⟨NormalizedInitialMetric.mk g' D' (normalizedMetricVolume g') rfl
    (m01RescaledMetric_curvatureTensorNorm_le D B hcurv c hc hcB)
    (m01_rescaledMetric_smallBall_lower_bound g r₀ hr₀ hball c hc hscale)
    (m01_normalizedMetricVolume_finite g') ?_⟩
  · unfold normalizedMetricComplete
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g'.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨⟨g'.inner, g'.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
    exact complete_of_compact

end PoincareMT
