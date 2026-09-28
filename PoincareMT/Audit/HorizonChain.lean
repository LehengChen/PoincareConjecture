import PoincareMT.Proofs.M06
import PoincareMT.Proofs.M16
import PoincareMT.Proofs.M17
import PoincareMT.Proofs.M18
import PoincareMT.Proofs.M19
import PoincareMT.Proofs.M20
import PoincareMT.Proofs.M24
import PoincareMT.Proofs.M33.Providers
import Lean.Util.CollectAxioms

open Lean Elab Command

set_option maxRecDepth 100000
set_option maxHeartbeats 0

run_cmd do
  let names := #[
    ``PoincareMT.differentialHarnackAncientTheory,
    ``PoincareMT.ancientKappaStructuralConsequences,
    ``PoincareMT.ancientBlowupSequenceSetup,
    ``PoincareMT.ancientAsymptoticSolitonLimits,
    ``PoincareMT.twoDimensionalAncientAndShrinkingSolitonClassification,
    ``PoincareMT.threeDimensionalAncientAndShrinkingSolitonClassification,
    ``PoincareMT.m24ModelCertificates,
    ``PoincareMT.repairedBranchContinuation,
    ``PoincareMT.m33BranchContinuationFromMilestones]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Forbidden axiom {axiomName} in complete closure of {name}"
    logInfo m!"PASS: {name}: {axioms}"
