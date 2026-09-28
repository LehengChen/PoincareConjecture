import PoincareMT.Proofs.M25.Topology3D.Space3.StandardTube
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# A source-sphere disc from the exact planar service

A smooth immersed source circle avoiding a pole is a planar embedding
in the corresponding stereographic chart. Apply the supplied single-curve
service once and compose its exact disc chart with inverse stereographic
projection. The resulting smooth source-disc chart retains the original
boundary parametrization. This is the first source-disc step in Hatcher,
Notes on Basic 3-Manifold Topology, Theorem 1.1, printed pp. 1-3; see the
reviewed source-sphere-disc-split derivation of 2026-09-22.
-/

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareMT.M25.Topology3D

local instance sourceCircle_stereographic_dimension : Fact (Module.finrank ℝ E3 = 2 + 1) :=
  ⟨by simp [E3]⟩

/-- The exact stereographic map is smooth on its source in the existing
sphere atlas. -/
theorem stereographic'_contMDiffOn (v : UnitTwoSphere) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ (stereographic' 2 v) (stereographic' 2 v).source := by
  have hatlas : stereographic' 2 v ∈ atlas E2 UnitTwoSphere := ⟨v, rfl⟩
  exact contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hatlas)

/-- Inverse stereographic projection is smooth on the whole plane,
which is the exact target of the chosen sphere chart. -/
theorem stereographic'_symm_contMDiff (v : UnitTwoSphere) :
    ContMDiff 𝓘(ℝ, E2) (𝓡 2) ∞ (stereographic' 2 v).symm := by
  have hatlas : stereographic' 2 v ∈ atlas E2 UnitTwoSphere := ⟨v, rfl⟩
  have hi : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞
      (stereographic' 2 v).symm (stereographic' 2 v).target :=
    contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hatlas)
  apply contMDiffOn_univ.mp
  simpa only [stereographic'_target] using hi

/-- A smooth injectively immersed sphere circle avoiding the pole
satisfies precisely the planar embedding interface in those coordinates. -/
theorem isPlanarEmbedding_stereographic_projection
    (q : UnitCircle → UnitTwoSphere) (hq : ContMDiff (𝓡 1) (𝓡 2) ∞ q)
    (hqi : Injective q) (hqd : ∀ θ, Injective (mfderiv (𝓡 1) (𝓡 2) q θ))
    (v : UnitTwoSphere) (hv : v ∉ range q) :
    IsPlanarEmbedding (fun θ => stereographic' 2 v (q θ)) := by
  let σ := stereographic' 2 v
  let g : UnitCircle → E2 := fun θ => σ (q θ)
  have hsource (θ : UnitCircle) : q θ ∈ σ.source := by
    change q θ ∈ (stereographic' 2 v).source
    rw [stereographic'_source]
    change q θ ≠ v
    exact fun heq => hv ⟨θ, heq⟩
  have hg : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞ g := by
    apply contMDiffOn_univ.mp
    exact (stereographic'_contMDiffOn v).comp hq.contMDiffOn (fun θ _ => hsource θ)
  have hrec : σ.symm ∘ g = q := funext fun θ => σ.left_inv (hsource θ)
  refine ⟨hg, ?_, ?_⟩
  · intro θ η hθη
    exact hqi (σ.injOn (hsource θ) (hsource η) hθη)
  · intro θ
    have hd := ((stereographic'_symm_contMDiff v).mdifferentiable
      (by simp) (g θ)).hasMFDerivAt.comp θ
        (hg.mdifferentiable (by simp) θ).hasMFDerivAt
    rw [hrec] at hd
    intro a b hab
    apply hqd θ
    rw [hd.mfderiv]
    exact congrArg (mfderiv 𝓘(ℝ, E2) (𝓡 2) σ.symm (g θ)) hab

/-- One planar-service witness gives a smooth disc chart through its
closed disc in the source sphere. The witness and exact composed chart
are retained for normalization, with the original boundary map pointwise. -/
theorem exists_source_circle_disc_chart (hP : PlanarSchoenfliesService)
    (q : UnitCircle → UnitTwoSphere) (hq : ContMDiff (𝓡 1) (𝓡 2) ∞ q)
    (hqi : Injective q) (hqd : ∀ θ, Injective (mfderiv (𝓡 1) (𝓡 2) q θ))
    (v : UnitTwoSphere) (hv : v ∉ range q) :
    ∃ D : PlanarSchoenfliesData (fun θ => stereographic' 2 v (q θ)),
      ∃ e : OpenPartialHomeomorph E2 UnitTwoSphere,
        e = D.discChart.trans (stereographic' 2 v).symm ∧
        closedBall 0 1 ⊆ e.source ∧
        ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source ∧
        ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target ∧
        ∀ θ : UnitCircle, e θ.1 = q θ := by
  obtain ⟨D⟩ := hP.1 _ (isPlanarEmbedding_stereographic_projection q hq hqi hqd v hv)
  let e := D.discChart.trans (stereographic' 2 v).symm
  refine ⟨D, e, rfl, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨D.closedBall_subset_discChart_source hx, ?_⟩
    change D.discChart x ∈ (stereographic' 2 v).target
    rw [stereographic'_target]
    exact mem_univ _
  · exact (stereographic'_symm_contMDiff v).comp_contMDiffOn
      (D.discChart_contDiffOn.contMDiffOn.mono inter_subset_left)
  · exact D.discChart_symm_contDiffOn.contMDiffOn.comp
      ((stereographic'_contMDiffOn v).mono inter_subset_left) (fun _ hy => hy.2)
  · intro θ
    change (stereographic' 2 v).symm (D.chart θ.1) = q θ
    rw [D.chart_boundary θ]
    apply (stereographic' 2 v).left_inv
    rw [stereographic'_source]
    change q θ ≠ v
    exact fun heq => hv ⟨θ, heq⟩

end PoincareMT.M25.Topology3D
