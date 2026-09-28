import PoincareMT.Definitions.M25NeckCapTopology
import PoincareMT.Statements.Ch09.NeckCapTopology

/-!
# M25 repaired neck/cap topology statement

The statement exposes the corrected A.19 and A.20 neck-only conclusions, the
local A.21 cap/neck region certificate, and the global A.25 whole-cover
alternatives directly as primitive properties of a supplied metric and cover.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedNeckCapTopologyTheory where
  epsilon₀ : ℝ
  epsilon₀_pos : 0 < epsilon₀
  epsilon₀_le_one_two_hundred : epsilon₀ ≤ 1 / 200
  /-- Corrected Proposition A.19: separating central spheres produce a tube. -/
  a19 : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M],
    ∀ g : RiemannianMetric 3 M,
      ∀ H : NeckOnlyCover g, H.epsilon ≤ epsilon₀ →
        ∀ hsep, AppendixA19Theory g H hsep
  /-- Corrected Lemma A.20: the separating branch is a tube and the
      nonseparating branch is an S²-bundle over the circle.
      The uniform labels on all input necks also use Proposition A.11(5),
      pp. 503-504: nearby centered necks have ambient-isotopic central
      spheres, so separation is locally constant. The whole connected
      center cover makes it constant on all `H.necks`. Include A.11's
      smallness bound in the universal threshold. This additional argument
      belongs to M25's proof obligation; see
      `reviews/contracts/2026-09-20-m25-uniform-separation.md`. -/
  a20 : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M],
    ∀ g : RiemannianMetric 3 M,
      ∀ H : NeckOnlyCover g, H.epsilon ≤ epsilon₀ →
        ∀ hwhole : H.X = Set.univ, AppendixA20Theory g H hwhole
  /-- Proposition A.21: a compatible local cap/neck region. -/
  a21 : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M],
    ∀ g : RiemannianMetric 3 M,
      ∀ H : ConnectedNeckCapCover g, H.epsilon ≤ epsilon₀ →
        Nonempty (RepairedNeckCapTopologyData g H)
  /-- Proposition A.25: the four global cap/neck alternatives. -/
  a25 : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M],
    ∀ g : RiemannianMetric 3 M,
      ∀ H : ConnectedNeckCapCover g, H.epsilon ≤ epsilon₀ → H.isWhole →
        Nonempty (GlobalNeckCapConclusion g H.epsilon H.cap_constant)

end PoincareMT
