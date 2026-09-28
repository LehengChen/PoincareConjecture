import PoincareMT.Proofs.Ch01.Koszul
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Connection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Local.Connection.Koszul`.
Its constants already exist on main in
`PoincareMT.Proofs.Ch01.Koszul`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

/- Adapted from Mapher `PoincareMT/Proofs/Ch01/Koszul.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/


/-!
# Local Koszul formula and uniqueness on regular sections

The formula follows from the metric-compatibility and torsion identities in
Morgan-Tian, Theorem 1.2, printed pp. 3-4. These results require differentiability
only at the evaluation point. They do not assert existence or equality of
connection operators on arbitrary nondifferentiable sections.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Metric compatibility with the specified metric visible in the scalar derivative. -/
theorem localTheory_mvfderiv_inner (D : LeviCivitaData g)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) =
      g.inner x (D.connection Y x (X x)) (Z x) +
        g.inner x (Y x) (D.connection Z x (X x)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact D.metricCompatible.mvfderiv_inner_eq X hY hZ

end PoincareMT.LeviCivitaData
