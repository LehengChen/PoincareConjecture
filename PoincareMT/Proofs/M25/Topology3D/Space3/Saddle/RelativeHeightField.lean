import PoincareMT.Proofs.M25.Topology3D.Space3.RegularBandField

/-!
# Relative height fields away from a protected saddle neighborhood

A compact regular part of the central sphere admits a compact ambient
tangent field with unit height speed there. Its full flow preserves the
sphere and fixes any disjoint closed protected set. This supplies the
field for Hatcher's relative verticalization, Notes on Basic 3-Manifold
Topology, Lemma 1.2, pp. 2-3. Complete track coverage remains separate.
See the independently reviewed relative-height-field derivation of
2026-09-22 in the saddle records.
-/

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace NNReal

namespace PoincareMT.M25.Topology3D

/-- A compact regular source set has unit height speed under a smooth
compact ambient field supported away from a prescribed closed set.
Every bounded-flow realization preserves the entire sphere and fixes
that protected set, without asserting that tracks stay in the regular
source set. Source: Hatcher, Lemma 1.2, pp. 2-3, relative-field step. -/
theorem exists_relative_collar_height_field
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ) (u : E3)
    {K : Set UnitTwoSphere} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪u, ψ (p, 0)⟫_ℝ) q ≠ 0)
    {C : Set E3} (hC : IsClosed C)
    (hKC : Disjoint ((fun q : UnitTwoSphere => ψ (q, 0)) '' K) C) :
    ∃ F : E3 → E3, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      tsupport F ⊆ (ψ '' (univ ×ˢ Ioo (-1) 1)) \ C ∧
      (∀ q ∈ K, ⟪u, F (ψ (q, 0))⟫_ℝ = 1) ∧
      ∀ (Kb Lb : ℝ≥0) (hKb : LipschitzWith Kb F) (hLb : ∀ y, ‖F y‖ ≤ Lb),
        (∀ q : UnitTwoSphere, ∀ t : ℝ,
          boundedFlow F hKb hLb (ψ (q, 0)) t ∈
            range (fun p : UnitTwoSphere => ψ (p, 0))) ∧
        ∀ y ∈ C, ∀ t : ℝ, boundedFlow F hKb hLb y t = y := by
  obtain ⟨ρ, hρ, hρψ, hρnz⟩ := exists_sphere_collar_defining_function ψ hψ
  let j : UnitTwoSphere → E3 := fun q => ψ (q, 0)
  let U0 : Set E3 := ψ '' (univ ×ˢ Ioo (-1) 1)
  let U := U0 \ C
  let S := j '' K
  have hj := (collar_central_contMDiff ψ hψ).continuous
  have hU0 : IsOpen U0 := collar_image_open ψ hψ
  have hU : IsOpen U := hU0.sdiff hC
  have hjU0 (q : UnitTwoSphere) : j q ∈ U0 :=
    ⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hS : IsCompact S := hK.image hj
  have hSU : S ⊆ U := by
    rintro y ⟨q, hq, rfl⟩
    exact ⟨hjU0 q, fun hqC => Set.disjoint_left.mp hKC ⟨q, hq, rfl⟩ hqC⟩
  have hn (y : E3) (hy : y ∈ U0) : gradient ρ y ≠ 0 := by
    intro hz
    apply hρnz y hy
    rw [← toDual_gradient, hz, map_zero]
  have hproj : ∀ y ∈ S, ⟪u, y⟫_ℝ ∈ tsupport (fun _ : ℝ => (1 : ℝ)) →
      tangentHeightVector (gradient ρ y) u ≠ 0 := by
    rintro y ⟨q, hq, rfl⟩ _
    exact tangentHeightVector_ne_zero_of_heightCross _ _
      (collar_regular_height_cross_ne_zero ψ hψ ρ hρ hρψ hρnz u q (hreg q hq))
  obtain ⟨F, hF, hFc, hFs, hFρ, hFH⟩ :=
    exists_compact_height_band_field hS hU hSU ρ (hρ.mono sdiff_subset)
      (fun y hy => hn y hy.1) u (fun _ => 1) contDiff_const hproj
  refine ⟨F, hF, hFc, hFs, fun q hq => hFH (j q) ⟨q, hq, rfl⟩, ?_⟩
  intro Kb Lb hKb hLb
  have hzero (y : E3) (hy : y ∉ U0) : F y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hy (hFs hm).1)
  constructor
  · intro q t
    have hflowU := boundedFlow_mapsTo_set F hKb hLb hzero t (hjU0 q)
    have hρflow := boundedFlow_preserves_firstIntegral F hKb hLb hzero ρ
      (fun y hy => (hρ.contDiffAt (hU0.mem_nhds hy)).differentiableAt (by simp))
      (fun y _ => hFρ y) (j q) (hjU0 q) t
    have hρzero : ρ (boundedFlow F hKb hLb (j q) t) = 0 :=
      hρflow.trans (hρψ (q, 0) ⟨mem_univ _, by norm_num⟩)
    obtain ⟨⟨p, r⟩, hpr, heq⟩ := hflowU
    have hr : r = 0 := (hρψ (p, r) hpr).symm.trans ((congrArg ρ heq).trans hρzero)
    subst r
    exact ⟨p, heq⟩
  · intro y hy t
    exact boundedFlow_eq_self F hKb hLb y
      (image_eq_zero_of_notMem_tsupport (fun hm => (hFs hm).2 hy)) t

end PoincareMT.M25.Topology3D
