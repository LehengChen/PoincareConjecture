import PoincareMT.Definitions.Ch04.Harnack
import PoincareMT.Definitions.Ch04.Pinching
import PoincareMT.Definitions.Ch09.NeckCapTopology

/-!
Proposition 2.19, printed pp. 31--33: sufficiently small necks in a connected,
complete, strictly positively sectionally curved three-manifold have a positive
lower scale bound. The bound depends on the selected metric and epsilon.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

def M45SmallNeckScaleBound (epsilon₁ : ℝ) : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
    ∀ (g : RiemannianMetric 3 M) (D : LeviCivitaData g),
      MetricComplete g →
      (∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair g x v w →
          0 < D.sectionalCurvature x v w) →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₁ →
        ∃ scale₀ : ℝ, 0 < scale₀ ∧
          ∀ N : EpsilonNeck g, N.connection = D → N.epsilon = epsilon →
            scale₀ ≤ N.scale

end PoincareMT
