import PoincareMT.Proofs.M34
import PoincareMT.Proofs.M62
import PoincareMT.Proofs.M63

/-!
# Standard-cap and curve-estimate axiom guards

These guards distinguish the numbered contracts from their admitted proofs.
-/

set_option autoImplicit false

open Lean in
run_cmd do
  let foundation := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``PoincareMT.RepairedStandardCapExistenceTheory,
      ``PoincareMT.M62CurveEvolutionTheory, ``PoincareMT.M63RampEstimatesTheory] do
    for axiomName in <- collectAxioms name do
      unless foundation.contains axiomName do
        throwError "Unapproved contract axiom {name}: {axiomName}"
  for name in #[``PoincareMT.m62CorrectedCurveEvolution,
      ``PoincareMT.repairedStandardCapExistence_of_predecessors] do
    for axiomName in <- collectAxioms name do
      unless foundation.contains axiomName do
        throwError "Unapproved theorem axiom {name}: {axiomName}"
  for name in #[``PoincareMT.m63RampEstimates] do
    let axioms <- collectAxioms name
    for axiomName in axioms do
      unless foundation.contains axiomName do
        throwError "Unapproved theorem axiom {name}: {axiomName}"
