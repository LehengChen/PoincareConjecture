import PoincareMT.Definitions.M21AsymptoticVolume
import PoincareMT.Statements.Ch01.CurvatureCalculus

/-!
# M21 asymptotic volume ratio statement

The statement quantifies the Bishop--Gromov package over every ancient flow,
dimension, time slice, and basepoint.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ}

/-- M04's static tensor calculus on the actual metric and connection.
This is the only earlier theorem service used by the M21 slice argument. -/
def AsymptoticVolumeRatioPredecessors (n : ℕ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g), D.CurvatureTensorCalculus

/-- The M21 slice-by-slice asymptotic volume ratio theory. The numbered
theorem supplies its predecessors once, before any slice is selected. -/
structure AsymptoticVolumeRatioTheory (n : ℕ) : Prop where
  slice : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) (t : ℝ), t ≤ 0 →
    Nonempty (AsymptoticVolumeRatioSliceData K t)

end PoincareMT
