import PoincareMT.Proofs.M47.TerminalCommonIntervalExhaustionMap
import PoincareMT.Definitions.Ch01.RiemannianMetric

/-!
# Identifying the chosen terminal metric by both chart slots

The preliminary terminal metric may be hidden behind an existential.
Its original chart readouts identify it with the canonical quotient
metric without selecting another metric. Source: reviewed C6b.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

universe u v w

namespace PoincareMT.M47

/-- Equality in both derivative slots on a covering family of actual
local diffeomorphisms determines the whole chosen metric. -/
theorem terminalCommonInterval_metric_eq_of_chart_readouts
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {ι : Type w} {P : ι → Type v} [∀ i, TopologicalSpace (P i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (P i)]
    [∀ i, IsManifold (𝓡 3) ∞ (P i)]
    (g h : RiemannianMetric 3 M) (c : ∀ i, P i → M)
    (hc : ∀ i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (c i))
    (hcover : ∀ x, ∃ i y, c i y = x)
    (hreadout : ∀ i (y : P i) (v w : TangentSpace (𝓡 3) y),
      g.inner (c i y) (mfderiv (𝓡 3) (𝓡 3) (c i) y v)
        (mfderiv (𝓡 3) (𝓡 3) (c i) y w) =
      h.inner (c i y) (mfderiv (𝓡 3) (𝓡 3) (c i) y v)
        (mfderiv (𝓡 3) (𝓡 3) (c i) y w)) : g = h := by
  have hi : g.inner = h.inner := by
    funext x
    obtain ⟨i, y, rfl⟩ := hcover x
    ext v w
    let L := (hc i y).mfderivToContinuousLinearEquiv (by simp)
    have hv : mfderiv (𝓡 3) (𝓡 3) (c i) y (L.symm v) = v := L.apply_symm_apply v
    have hw : mfderiv (𝓡 3) (𝓡 3) (c i) y (L.symm w) = w := L.apply_symm_apply w
    simpa only [hv, hw] using hreadout i y (L.symm v) (L.symm w)
  cases g
  cases h
  cases hi
  rfl

end PoincareMT.M47
