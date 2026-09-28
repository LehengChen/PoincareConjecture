import PoincareMT.Statements.Ch03.ShortTime

/-!
# Curvature-controlled continuation and the local flow theory

Morgan-Tian, Proposition 4.12, printed p. 68, gives continuation on a compact
manifold under one spacetime curvature bound. The local theory combines this
with the two concrete claims of Theorem 3.11. Theorems supply compactness and
separation assumptions; these propositions have no admitted dependencies.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable (n : ℕ) (M : Type u) [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- A uniform spacetime curvature bound allows extension beyond a finite positive time. -/
def RicciFlowContinuation : Prop :=
  ∀ T : ℝ, 0 < T → ∀ F : RicciFlow n M (Set.Ico 0 T),
    (∃ C : ℝ, ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      (F.connection t).curvatureTensorNorm x ≤ C) →
    ∃ T' : ℝ, T < T' ∧ ∃ F' : RicciFlow n M (Set.Ico 0 T'),
      Set.EqOn F.metric F'.metric (Set.Ico 0 T)

/-- The three concrete local-flow claims of milestone M03. -/
def RicciFlowLocalTheory : Prop :=
  ShortTimeRicciFlowExistence n M ∧ RicciFlowUniqueness n M ∧
    RicciFlowContinuation n M

end PoincareMT
