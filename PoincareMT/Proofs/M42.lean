import PoincareMT.Statements.M42VanishingContinuation

/-!
# M42 logical vanishing-branch extraction

An existing M33 branch supplies the continuation and its geometric controls.
This entry selects its vanishing terminal constructor.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-
Fix a preterminal surgery input I and a concrete M33 continuation branch B.
If I's controlled core is empty, select B's exact vanishing terminal operation
with its constructor equality, empty continued carrier, positive surgery-free
interval after T, admissibility and curvature pinching, and the source's
infinite terminal time. The selected operation retains its strict
no-later-surgery property on the continued time domain.

Logical derivation: B's terminal-empty equivalence makes its continued
carrier empty. Inspect its terminal operation; the nonempty constructor
contradicts this emptiness, while the vanishing constructor supplies its
empty-carrier witness and exact operation. B's terminal-empty endpoint rule
gives infinite lifetime; its other projections supply the interval,
admissibility and pinching. No new extension or operation is constructed.

This is a logical adapter, not an independent source theorem. M33 owns the
continuation from Morgan--Tian Lemma 15.11 (printed p. 364) and the degenerate
case of Theorem 15.9 (pp. 409--410). Applicable local controls are recorded in
`reviews/errata/2026-09-14-local-continuation-controls.md`; later canonical and
noncollapsing propagation remains in Chapters 16--17.
-/
theorem repairedVanishingContinuation : RepairedVanishingContinuationTheory.{u} := by
  refine ⟨?_⟩
  intro F T I branch hcore
  have hempty : IsEmpty (branch.conclusion.extension.extended.slice T).carrier :=
    (branch.conclusion.terminal_empty_iff).mp hcore
  cases hoperation : branch.conclusion.terminal_operation with
  | nonempty hpost _operation =>
      cases hpost with
      | intro x => exact (hempty.false x).elim
  | vanishing hempty' operation =>
      exact ⟨⟨hempty', operation, hoperation,
        branch.conclusion.terminal_empty_end_time_top hcore,
        branch.conclusion.post_terminal_interval,
        branch.conclusion.admissible, branch.conclusion.pinched⟩⟩

end PoincareMT
