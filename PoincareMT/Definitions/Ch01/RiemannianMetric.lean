import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Explicit Riemannian metric and connection data

The chosen metric is an argument of each operation, including extended distance.
This follows Morgan-Tian, printed pp. 3-4, using Mathlib's tangent bundle and
connection conventions. The distance uses C^1 paths; transport to the book's
smooth-path convention is a separate obligation. See reviews/contracts/metric-v1.md.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT

/-- A smooth positive-definite symmetric metric on a manifold without boundary. -/
abbrev RiemannianMetric (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] :=
  Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace RiemannianMetric

/-- The norm of a tangent vector in the explicitly chosen metric. -/
noncomputable def tangentNorm (g : RiemannianMetric n M) (x : M)
    (v : TangentSpace (𝓡 n) x) : ℝ :=
  Real.sqrt (g.inner x v v)

/-- The derivative-integral functional; geometric length requires a regular path. -/
noncomputable def pathELength (g : RiemannianMetric n M) (γ : ℝ → M)
    (a b : ℝ) : ℝ≥0∞ :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  Manifold.pathELength (𝓡 n) γ a b

/-- The infimum of C^1 path lengths, retaining infinity between path components. -/
noncomputable def edist (g : RiemannianMetric n M) (x y : M) : ℝ≥0∞ :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist (𝓡 n) x y

/-- An open metric ball, with the empty set as its value for nonpositive radii. -/
def ball (g : RiemannianMetric n M) (x : M) (r : ℝ) : Set M :=
  {y | g.edist x y < ENNReal.ofReal r}

end RiemannianMetric

/-- A smooth torsion-free connection compatible with the specified metric.

This retains actual connection data and makes no existence or uniqueness claim.
Geometric uniqueness must be stated on sufficiently regular sections or germs.
-/
structure LeviCivitaData (g : RiemannianMetric n M) where
  /-- The covariant derivative, applied as `connection Y x (X x)` for ∇_X Y. -/
  connection : CovariantDerivative (𝓡 n) (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _)
  /-- The connection maps smooth sections to smooth covariant derivatives. -/
  smooth : CovariantDerivative.ContMDiffCovariantDerivative connection ∞
  /-- The torsion tensor vanishes. -/
  torsion_eq_zero : connection.torsion = 0
  /-- Differentiating the chosen metric obeys the metric-compatibility identity. -/
  metricCompatible :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    connection.IsMetricCompatible

end PoincareMT
