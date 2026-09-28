import PoincareMT.Proofs.M05.Analysis.ODE.Linear
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall

/-!
# Global existence for linear ODEs with continuous coefficient

Mathlib's Picard–Lindelöf theory (`Mathlib.Analysis.ODE.PicardLindelof`) proves only
*local* existence: from `IsPicardLindelof` one gets a solution on a time interval short
enough that the a-priori bound keeps the trajectory inside a fixed ball. For a **linear**
ODE `V'(t) = A(t) V(t)` with a continuous bounded coefficient `A : ℝ → (E →L[ℝ] E)` the
solution exists on *any* compact interval, but that global statement is not in mathlib.

This file supplies it, as reusable infrastructure:

* `Riemannian.LinearODE.exists_hasDerivWithinAt_of_small` — short-time existence: on `[a,b]`
  with `(b-a)·‖A‖ ≤ 1/2` a solution with prescribed left-endpoint value exists (a direct
  `IsPicardLindelof` application).
* `Riemannian.LinearODE.exists_hasDerivWithinAt_Icc` — global existence on an arbitrary
  compact `[a,b]`, obtained by chopping `[a,b]` into finitely many short pieces, solving
  each with the short-time lemma, and gluing the pieces at the junctions.

The parallel-transport ODE `V' = -Γ(u', V)(u)` (do Carmo Ch. 2, Prop. 2.6) is the special
case `A(t) = -chartChristoffelContractionRight g α (u' t) (u t)`; see
`DoCarmoLib/Riemannian/Geodesic/CovariantDerivative.lean`.
-/

/-! This entry reuses the identical declaration block from the existing local
M05 provider above. Lean rejects duplicate data declarations even when their
types and bodies agree. Original imports and attribution are retained;
the provider retains its existing semantic and provenance review status. -/
