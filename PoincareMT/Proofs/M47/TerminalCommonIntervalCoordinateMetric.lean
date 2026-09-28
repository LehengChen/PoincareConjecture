import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Coordinates.Composition
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Exact coordinate metric identity for the actual cross maps

The two physical maps enter the same metric. Their actual partial
inverses identify the coordinate composite on its open source.
MT Theorem 5.11; terminal-common-smooth-identification.md, B2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareMT.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

/-- Original source and target charts give a smooth coordinate cross
map and the exact pullback identity in both physical metric slots. -/
theorem terminalCommonInterval_actual_coordinate_metric
    {M : Type u} {N : Type v} {X : Type w}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace E N] [IsManifold (𝓡 3) ∞ N]
    [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 X)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) N X ∞)
    (a : PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞)
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) N E ∞) :
    let T := ((a.symm.trans e).trans f.symm).trans b
    ContDiffOn ℝ ∞ T T.source ∧
      ∀ x ∈ T.source, ∀ v w,
        g.pullbackCoefficients (f ∘ b.symm) (T x)
            (fderiv ℝ T x v) (fderiv ℝ T x w) =
          g.pullbackCoefficients (e ∘ a.symm) x v w := by
  let T := ((a.symm.trans e).trans f.symm).trans b
  refine ⟨contMDiffOn_iff_contDiffOn.mp T.contMDiffOn_toFun, ?_⟩
  intro x hx v w
  have heq : (f ∘ b.symm) ∘ T =ᶠ[𝓝 x] e ∘ a.symm := by
    filter_upwards [T.open_source.mem_nhds hx] with y hy
    change ((y ∈ a.target ∧ a.symm y ∈ e.source) ∧
      e (a.symm y) ∈ f.target) ∧ f.symm (e (a.symm y)) ∈ b.source at hy
    change f (b.symm (b (f.symm (e (a.symm y))))) = e (a.symm y)
    have hb : b.symm (b (f.symm (e (a.symm y)))) = f.symm (e (a.symm y)) :=
      b.toPartialEquiv.left_inv hy.2
    exact (congrArg (fun z => f z) hb).trans (f.toPartialEquiv.right_inv hy.1.2)
  have hx' := hx
  change ((x ∈ a.target ∧ a.symm x ∈ e.source) ∧
    e (a.symm x) ∈ f.target) ∧ f.symm (e (a.symm x)) ∈ b.source at hx'
  have hq : T x ∈ (b.symm.trans f).source := by
    change b (f.symm (e (a.symm x))) ∈ b.target ∧
      b.symm (b (f.symm (e (a.symm x)))) ∈ f.source
    refine ⟨b.map_source hx'.2, ?_⟩
    have hb : b.symm (b (f.symm (e (a.symm x)))) = f.symm (e (a.symm x)) :=
      b.toPartialEquiv.left_inv hx'.2
    exact hb.symm ▸ f.map_target hx'.1.2
  exact g.pullbackCoefficients_comp_of_eventuallyEq
    ((b.symm.trans f).mdifferentiableAt (by simp) hq)
    (mdifferentiableAt_iff_differentiableAt.mp (T.mdifferentiableAt (by simp) hx))
    heq v w

end PoincareMT.M47
