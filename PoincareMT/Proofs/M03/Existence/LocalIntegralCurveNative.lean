import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import PoincareMT.Definitions.Ch01.RiemannianMetric

/-!
# Native local vector-field flow boundary

Mathlib's local integral-curve theorem is exposed on the PoincareMT tangent
bundle.  This is the geometric ODE boundary used by a conjugating-flow
producer; it does not package a Ricci-flow solver or assume one.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem exists_local_integralCurve
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (hV : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 1
      (fun x : M => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) x (V x)))
    (x₀ : M) :
    ∃ γ : ℝ → M, γ 0 = x₀ ∧ IsMIntegralCurveAt γ V 0 := by
  exact exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    (t₀ := 0) (x₀ := x₀) (v := V) (hV x₀)

end PoincareMT
