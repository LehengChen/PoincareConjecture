import PoincareMT.Statements.M41NonemptyContinuation

/-!
# M41 logical nonempty-branch extraction

An existing M33 branch supplies the continuation and its geometric controls.
This entry selects its nonempty terminal constructor.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-
Fix a preterminal surgery input I and a concrete M33 continuation branch B.
If I's controlled terminal core is nonempty, B's time-T carrier is nonempty
and its terminal operation is the nonempty constructor. Select that exact
operation with its constructor equality, a positive surgery-free interval
after T, admissibility, and curvature pinching on the same extension.

Logical derivation: use B's equivalence between nonemptiness of the controlled
core and nonemptiness of the continued carrier. Inspect B's terminal
operation; its vanishing constructor contradicts that nonemptiness. Copy the
operation and remaining fields from B in the nonempty case.

This is a logical adapter, not an independent source theorem. M33 owns the
continuation from Morgan--Tian Lemma 15.11 (printed p. 364) and its nonempty
application on pp. 409--410. The correction in
`reviews/errata/2026-09-14-local-continuation-controls.md` retains the local
cutoff and metric-surgery premises and assigns post-surgery canonical and
noncollapsing control to the later Chapters 16--17 induction.
-/
theorem repairedNonemptyContinuation : RepairedNonemptyContinuationTheory.{u} := by
  refine ⟨?_⟩
  intro F T I branch hcore
  have hpost : Nonempty (branch.conclusion.extension.extended.slice T).carrier :=
    (branch.conclusion.terminal_nonempty_iff).mp hcore
  cases hoperation : branch.conclusion.terminal_operation with
  | nonempty hpost' operation =>
      exact ⟨⟨hpost', operation, hoperation, branch.conclusion.post_terminal_interval,
        branch.conclusion.admissible, branch.conclusion.pinched⟩⟩
  | vanishing hempty _operation =>
      cases hpost with
      | intro x => exact (hempty.false x).elim

end PoincareMT
