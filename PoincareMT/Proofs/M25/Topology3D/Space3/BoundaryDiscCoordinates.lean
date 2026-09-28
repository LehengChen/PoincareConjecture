import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Radial stereographic coordinates near a boundary disc

Inverse stereographic projection times a positive radius gives a smooth
ambient chart off a ray. Its second coordinate is exactly the ambient
norm, so horizontal field moves preserve the sphere and ball. This is
the coordinate construction for attaching-disc standardization in Hatcher,
Notes on Basic 3-Manifold Topology, Lemma 1.3, p. 3.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff InnerProductSpace

namespace PoincareMT.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (v : E) (hv : ‖v‖ = 1)

/-- Radial coordinates over the inverse stereographic sphere chart. -/
noncomputable def radialStereoMap (p : (ℝ ∙ v)ᗮ × ℝ) : E :=
  p.2 • (stereoInvFun hv p.1 : E)

/-- The inverse coordinates project the normalized direction and
retain the positive ambient norm. -/
noncomputable def radialStereoInverse (y : E) : (ℝ ∙ v)ᗮ × ℝ :=
  (stereoToFun v (NormedSpace.normalize y), ‖y‖)

/-- The radial chart excludes the nonnegative ray through its pole. -/
def radialStereoTarget : Set E := {y | ⟪v, y⟫_ℝ < ‖y‖}

/-- Strict Cauchy-Schwarz makes the ray complement open. -/
theorem radialStereoTarget_open : IsOpen (radialStereoTarget v) :=
  isOpen_lt (innerSL ℝ v).continuous continuous_norm

/-- The radial coordinate is exactly the ambient norm when positive. -/
theorem radialStereoMap_norm (p : (ℝ ∙ v)ᗮ × ℝ) (hp : 0 < p.2) :
    ‖radialStereoMap v hv p‖ = p.2 := by
  simp only [radialStereoMap, norm_smul, norm_eq_of_mem_sphere,
    Real.norm_eq_abs, abs_of_pos hp, mul_one]

/-- Radial stereographic coordinates are smooth on the whole source space. -/
theorem radialStereoMap_contDiff : ContDiff ℝ ∞ (radialStereoMap v hv) := by
  exact contDiff_snd.smul ((contDiff_stereoInvFunAux (v := v)).comp
    ((ℝ ∙ v)ᗮ.subtypeL.contDiff.comp contDiff_fst))

/-- The ray complement does not contain zero. -/
theorem radialStereoTarget_ne_zero {y : E} (hy : y ∈ radialStereoTarget v) : y ≠ 0 := by
  intro h
  subst y
  change ⟪v, (0 : E)⟫_ℝ < ‖(0 : E)‖ at hy
  simp only [inner_zero_right, norm_zero, lt_self_iff_false] at hy

/-- Directions in the ray complement avoid the stereographic pole. -/
theorem radialStereoTarget_inner_normalize_lt {y : E} (hy : y ∈ radialStereoTarget v) :
    ⟪v, NormedSpace.normalize y⟫_ℝ < 1 := by
  have hpos : 0 < ‖y‖ := norm_pos_iff.mpr (radialStereoTarget_ne_zero v hy)
  rw [NormedSpace.normalize, real_inner_smul_right]
  simpa only [div_eq_mul_inv, mul_comm] using (div_lt_one hpos).mpr hy

/-- Positive radii map into the ray complement. -/
theorem radialStereoMap_mem_target (p : (ℝ ∙ v)ᗮ × ℝ) (hp : 0 < p.2) :
    radialStereoMap v hv p ∈ radialStereoTarget v := by
  have hq : ‖(stereoInvFun hv p.1 : E)‖ = 1 := norm_eq_of_mem_sphere _
  have hne : v ≠ (stereoInvFun hv p.1 : E) := by
    intro h
    exact stereoInvFun_ne_north_pole hv p.1 (Subtype.ext h.symm)
  have hlt := (inner_lt_one_iff_real_of_norm_eq_one hv hq).mpr hne
  change ⟪v, radialStereoMap v hv p⟫_ℝ < ‖radialStereoMap v hv p‖
  rw [radialStereoMap_norm v hv p hp]
  change ⟪v, p.2 • (stereoInvFun hv p.1 : E)⟫_ℝ < p.2
  rw [real_inner_smul_right]
  simpa only [mul_one] using mul_lt_mul_of_pos_left hlt hp

/-- The explicit inverse is smooth on the ray complement. -/
theorem radialStereoInverse_contDiffOn :
    ContDiffOn ℝ ∞ (radialStereoInverse v) (radialStereoTarget v) := by
  intro y hy
  have hy0 := radialStereoTarget_ne_zero v hy
  have hn : ContDiffAt ℝ ∞ (norm : E → ℝ) y := contDiffAt_norm ℝ hy0
  have hnormalize : ContDiffAt ℝ ∞ (NormedSpace.normalize : E → E) y :=
    (hn.inv (norm_ne_zero_iff.mpr hy0)).smul contDiffAt_id
  have hne : innerSL ℝ v (NormedSpace.normalize y) ≠ 1 :=
    (radialStereoTarget_inner_normalize_lt v hy).ne
  have hopen : IsOpen {x : E | innerSL ℝ v x ≠ 1} :=
    isOpen_ne.preimage (innerSL ℝ v).continuous
  have hstereo : ContDiffAt ℝ ∞ (stereoToFun v) (NormedSpace.normalize y) :=
    contDiffOn_stereoToFun.contDiffAt (hopen.mem_nhds hne)
  exact ((hstereo.comp y hnormalize).prodMk hn).contDiffWithinAt

/-- Inverse followed after the radial parametrization recovers both coordinates. -/
theorem radialStereoInverse_map (p : (ℝ ∙ v)ᗮ × ℝ) (hp : 0 < p.2) :
    radialStereoInverse v (radialStereoMap v hv p) = p := by
  apply Prod.ext
  · change stereoToFun v (NormedSpace.normalize
      (p.2 • (stereoInvFun hv p.1 : E))) = p.1
    rw [NormedSpace.normalize_smul_of_pos hp,
      NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere _)]
    exact stereo_right_inv hv p.1
  · exact radialStereoMap_norm v hv p hp

/-- The radial parametrization recovers every point of the ray complement. -/
theorem radialStereoMap_inverse {y : E} (hy : y ∈ radialStereoTarget v) :
    radialStereoMap v hv (radialStereoInverse v y) = y := by
  have hynorm : ‖NormedSpace.normalize y‖ = 1 :=
    NormedSpace.norm_normalize (radialStereoTarget_ne_zero v hy)
  let q : sphere (0 : E) 1 := ⟨NormedSpace.normalize y, mem_sphere_zero_iff_norm.mpr hynorm⟩
  have hne : (q : E) ≠ v := by
    intro h
    have hlt := radialStereoTarget_inner_normalize_lt v hy
    change ⟪v, (q : E)⟫_ℝ < 1 at hlt
    rw [h, real_inner_self_eq_norm_sq, hv] at hlt
    norm_num at hlt
  have heq : (stereoInvFun hv (stereoToFun v (q : E)) : E) = q :=
    congrArg Subtype.val (stereo_left_inv hv hne)
  change ‖y‖ • (stereoInvFun hv (stereoToFun v (q : E)) : E) = y
  rw [heq]
  exact NormedSpace.norm_smul_normalize y

/-- The smooth ambient chart used to lift attaching-disc moves. -/
noncomputable def radialStereoChart : OpenPartialHomeomorph ((ℝ ∙ v)ᗮ × ℝ) E where
  toFun := radialStereoMap v hv
  invFun := radialStereoInverse v
  source := univ ×ˢ Ioi 0
  target := radialStereoTarget v
  map_source' p hp := radialStereoMap_mem_target v hv p hp.2
  map_target' _ hy := ⟨mem_univ _, norm_pos_iff.mpr (radialStereoTarget_ne_zero v hy)⟩
  left_inv' p hp := radialStereoInverse_map v hv p hp.2
  right_inv' _ hy := radialStereoMap_inverse v hv hy
  open_source := isOpen_univ.prod isOpen_Ioi
  open_target := radialStereoTarget_open v
  continuousOn_toFun := (radialStereoMap_contDiff v hv).continuous.continuousOn
  continuousOn_invFun := (radialStereoInverse_contDiffOn v).continuousOn

/-- Smoothness of the forward radial chart on its domain. -/
theorem radialStereoChart_contDiffOn :
    ContDiffOn ℝ ∞ (radialStereoChart v hv) (radialStereoChart v hv).source :=
  (radialStereoMap_contDiff v hv).contDiffOn

/-- Smoothness of the inverse radial chart on its domain. -/
theorem radialStereoChart_symm_contDiffOn :
    ContDiffOn ℝ ∞ (radialStereoChart v hv).symm (radialStereoChart v hv).target :=
  radialStereoInverse_contDiffOn v

end PoincareMT.M25.Topology3D
