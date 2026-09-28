import PoincareMT.Proofs.M03.Existence.ChartStateSourceSmoothNative
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Uniform chart-source Lipschitz estimates

The finite-dimensional Ricci--DeTurck source is `C¹` on the nonsingular
positive-metric locus.  On a compact convex state region this gives a single
Lipschitz constant by the pinned Mathlib mean-value theorem.  This is the
coefficient estimate needed by a local Volterra iteration.
-/

set_option autoImplicit false

noncomputable section

namespace PoincareMT.DeTurckNative

open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

theorem contDiffOn_chartStateSource
    (background : MetricJet2 (n := n))
    (K : Set (ChartState (n := n)))
    (hpos : ∀ p ∈ K, p.1.PosDef) (i j : Fin n) :
    ContDiffOn ℝ 1 (fun p : ChartState (n := n) =>
      chartStateSource background p i j) K := by
  intro p hp
  exact (contDiffAt_chartStateSource background p (hpos p hp) i j).contDiffWithinAt

theorem exists_chartStateSource_lipschitzOnWith
    (background : MetricJet2 (n := n))
    (K : Set (ChartState (n := n)))
    (hconv : Convex ℝ K) (hcompact : IsCompact K)
    (hpos : ∀ p ∈ K, p.1.PosDef) (i j : Fin n) :
    ∃ L : NNReal, LipschitzOnWith L
      (fun p : ChartState (n := n) => chartStateSource background p i j) K := by
  exact (contDiffOn_chartStateSource background K hpos i j).exists_lipschitzOnWith
    one_ne_zero hconv hcompact

end PoincareMT.DeTurckNative

end
