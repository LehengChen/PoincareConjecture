import PoincareMT.Proofs.M34.Prop12_7_Asymptotics.StereographicCurvature
import PoincareMT.Proofs.M07.Geometry.RicciFlow.MetricFamily.Coordinates

/-!
# The genuine stereographic shrinking-cylinder flow

The metric has angular coefficient 2*(1-t)*rho and fixed axial coefficient
one on t<1. A positive total representative outside that interval supplies
the frozen flow record without asserting an equation at the collapse time.
This is Morgan-Tian Proposition 12.7, pp. 298-299 and
stereographic-cylinder-euclidean.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- A positive total angular scale, equal to 2*(1-t) on the flow domain
(Proposition 12.7, pp. 298-299). -/
noncomputable def stereographicCylinderScale (t : ℝ) : ℝ :=
  if t < 1 then 2 * (1 - t) else 2

/-- Positivity of the total metric representative
(Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderScale_pos (t : ℝ) : 0 < stereographicCylinderScale t := by
  unfold stereographicCylinderScale
  split_ifs with ht <;> linarith

/-- The actual total family of smooth positive model metrics
(Proposition 12.7, pp. 298-299). -/
noncomputable def stereographicCylinderFlowMetric (t : ℝ) : RiemannianMetric 3 E3 :=
  stereographicCylinderMetric (stereographicCylinderScale t) (stereographicCylinderScale_pos t)

/-- Included-time metric coefficients are the literal shrinking cylinder
(Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderFlowMetric_inner {t : ℝ} (ht : t < 1) (x u v : E3) :
    (stereographicCylinderFlowMetric t).inner x u v =
      stereographicCylinderCoefficients (2 * (1 - t)) x u v := by
  change stereographicCylinderCoefficients (stereographicCylinderScale t) x u v = _
  simp only [stereographicCylinderScale, ht, if_true]

/-- The actual metric section is jointly smooth throughout the open time
domain, with no claim across the excluded collapse time
(Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderFlowMetric_smooth :
    RiemannianMetric.IsSmoothFamilyOn stereographicCylinderFlowMetric (Iio 1) := by
  let B : ℝ × E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    fun z => stereographicCylinderCoefficients (2 * (1 - z.1)) z.2
  apply RiemannianMetric.isSmoothFamilyOn_of_constant_chart (fun _ _ => rfl)
    stereographicCylinderFlowMetric B
  · have hB : ContDiff ℝ ∞ B := by
      have hf : ContDiff ℝ ∞ (fun z : ℝ × E3 => (2 * (1 - z.1), z.2)) := by
        fun_prop
      exact stereographicCylinderCoefficients_contDiff.comp hf
    have hmap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ × E3) ∞
        (fun p : ℝ × E3 => (p.1, p.2)) :=
      contMDiff_fst.prodMk_space contMDiff_snd
    exact hB.contDiffOn.contMDiffOn.comp hmap.contMDiffOn (fun _ hp => hp)
  · intro t ht x u v
    exact stereographicCylinderFlowMetric_inner ht x u v

/-- The actual metric pairing has the cylinder's ordinary time derivative
at every included time (Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderFlowMetric_hasDerivAt {t : ℝ} (ht : t < 1)
    (x u v : E3) :
    HasDerivAt (fun s => (stereographicCylinderFlowMetric s).inner x u v)
      (-2 * stereographicCylinderDensity x * (u 0 * v 0 + u 1 * v 1)) t := by
  have h := (((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).const_mul 2).mul_const
    (stereographicCylinderDensity x)).mul_const (u 0 * v 0 + u 1 * v 1)).add_const
      (u 2 * v 2)
  have he : (fun s => (stereographicCylinderFlowMetric s).inner x u v) =ᶠ[𝓝 t]
      (fun s => 2 * (1 - s) * stereographicCylinderDensity x *
        (u 0 * v 0 + u 1 * v 1) + u 2 * v 2) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    rw [stereographicCylinderFlowMetric_inner hs, stereographicCylinderCoefficients_apply]
  convert! h.congr_of_eventuallyEq he using 1
  ring

/-- The genuine model Ricci flow, carrying the actual compatible
connection and its proved Ricci tensor (Proposition 12.7, pp. 298-299). -/
noncomputable def stereographicCylinderFlow : RicciFlow 3 E3 (Iio 1) where
  metric := stereographicCylinderFlowMetric
  connection t := (stereographicCylinderFlowMetric t).euclideanLeviCivitaData
  interval := ordConnected_Iio
  nontrivial := ⟨-1, by norm_num, 0, by norm_num, by norm_num⟩
  smooth := stereographicCylinderFlowMetric_smooth
  equation t ht x u v := by
    rw [stereographicCylinderRicci (stereographicCylinderScale_pos t)]
    convert! (stereographicCylinderFlowMetric_hasDerivAt ht x u v).hasDerivWithinAt using 1
    ring

end PoincareMT.M34
