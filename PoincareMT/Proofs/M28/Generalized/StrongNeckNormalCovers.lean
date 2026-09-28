import PoincareMT.Proofs.M28.Generalized.StrongNeckCurvatureBounds
import PoincareMT.Proofs.M28.Generalized.StrongNeckVolumeBounds
import PoincareMT.Proofs.M28.Generalized.StrongNeckHalfFlow
import PoincareMT.Proofs.M28.Generalized.StrongNeckSourceMetricSpace
import PoincareMT.Proofs.M28.Thm5_6_PartialLimits.Geometry.UniformNormalCover

/-!
# Actual uniform normal covers of normalized source necks

Theorem 5.6, Morgan--Tian pp. 85-87, and Claims 10.7-10.11, pp. 253-255.
The original strong-neck comparison supplies actual curvature and volume
bounds. The bounded-margin factory then chooses normal radii and a chart
count before the source manifold and index. No normal cover, limit, volume
bound, curvature bound or completeness is an input. See M28 derivation 33.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.M28

/-- Every ball strictly inside the normalized buffered source radius has
an actual normal cover with constants fixed before the original strong
neck and its chosen rescaling; Theorem 5.6, pp. 85-87. -/
theorem exists_strongNeck_source_normal_covers_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∀ r : ℝ, 0 < r → r < epsilon⁻¹ / 16 →
          ∃ R ρ : ℝ, ∃ n : ℕ, 0 < ρ ∧ 2 * ρ < R ∧
            R < (epsilon⁻¹ / 16 - r) / 8 ∧ R < 1 / 8 ∧
            ∀ (F : GeneralizedRicciFlowData.{u}) (t : ℝ)
              (S : GeneralizedStrongNeck F t epsilon)
              (H : RescaledRawCylinderData (C := F.slice t)
                (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
                (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S)),
              Nonempty (NormalChartCover
                (fun _ => (GeneralizedStrongNeck.rescaled_half_flow S H).metric 0)
                (strongNeckSourceCenter S) (-1) 1 r R ρ (1 / 4) (9 / 4) n) := by
  obtain ⟨epsilon₀, hepsilon₀, hthreshold, K, hK, hcurvature⟩ :=
    exists_strongNeck_rescaled_curvature_bound.{u}
  obtain ⟨v, hv, hvolume⟩ := exists_normalized_neck_volume_bounds.{u}
  refine ⟨epsilon₀, hepsilon₀, hthreshold, ?_⟩
  intro epsilon hepsilon hsmall r hr hrb
  let b : ℝ := epsilon⁻¹ / 16
  let s : ℝ := (r + b) / 2
  let δ : ℝ := min (1 / 8 : ℝ) ((b - r) / 8)
  have hδ : 0 < δ := lt_min (by norm_num) (by dsimp only [b]; linarith)
  have hδsmall : δ ≤ 1 / 8 := min_le_left _ _
  have hδmargin : δ ≤ (b - r) / 8 := min_le_right _ _
  have hrs : r < s := by dsimp only [s, b]; linarith
  have hsb : s < epsilon⁻¹ / 16 := by dsimp only [s, b]; linarith
  have hs : 0 < s := hr.trans hrs
  have hmargin : r + 2 * δ ≤ s := by dsimp only [s]; linarith
  obtain ⟨V, hV, hvol⟩ := hvolume s hs
  obtain ⟨R, ρ, n, hρ, hρR, hRδ, hcover⟩ :=
    exists_uniform_normalCover_of_local_noncollapse 3 (by norm_num) hK.le hδ
      (mul_pos hv (pow_pos hδ 3)) hV.le
  refine ⟨R, ρ, n, hρ, hρR, hRδ.trans_le hδmargin,
    hRδ.trans_le hδsmall, ?_⟩
  intro F t S H
  let : PreconnectedSpace (strongNeckOpen S) := strongNeckSource_preconnected S
  let G := GeneralizedStrongNeck.rescaled_half_flow S H
  have hhalf : epsilon < 1 / 2 :=
    lt_of_le_of_lt (hsmall.trans hthreshold) (by norm_num)
  let N := GeneralizedStrongNeck.rescaled_half_source_neck S H hhalf
  obtain ⟨hcompact, hlower, hupper⟩ := hvol (strongNeckOpen S) (G.metric 0) N
    rfl rfl (hsmall.trans hthreshold) hsb.le
  apply hcover (strongNeckOpen S) (G.metric 0) (G.connection 0)
    (strongNeckSourceCenter S) r s hr hmargin hcompact
  · intro x _
    exact hcurvature F t epsilon S H hsmall 0 (by norm_num) x
  · intro q hq
    apply hlower q (hq.trans_le (ENNReal.ofReal_le_ofReal hrs.le)) δ hδ hδsmall
  · exact hupper

end PoincareMT.M28
