import PoincareMT.Proofs.M47.SeedFirstFailureSequence
import PoincareMT.Proofs.M47.FirstFailureActual

/-!
# The counterexample family from the original induction inputs

The proved actual standard cover discharges the last internal N6 input.
The selected family keeps its original true first failures and density.
MT pp. 395-402; seed-preliminary-volume.md, C.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareMT.Proofs.M47

/-- Failure of the original canonical extension gives the actual
counterexample sequence without a geometric producer premise. -/
theorem exists_seed_actual_counterexample_sequence
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (hno : ¬ Nonempty (SurgeryCanonicalExtension p (Classical.choice (N.induction p hp)))) :
    ∃ k : ℝ, 0 < k ∧ ∀ c : ℕ → ℝ, (∀ n, 0 < c n) →
      ∃ (r delta : ℕ → ℝ) (F : ℕ → SurgeryFlowData.{u})
        (O : ∀ n, SurgeryObservation (F n)) (t : ℕ → ℝ)
        (x : ∀ n, ((F n).slice (t n)).carrier),
        (∀ n, r n = p.r (Fin.last p.i) / ((n : ℝ) + 1)) ∧
        Tendsto r atTop (𝓝 0) ∧ Tendsto delta atTop (𝓝 0) ∧
        Tendsto (fun n => ((F n).connection (t n)).scalarCurvature (x n)) atTop atTop ∧
        ∀ n, 0 < r n ∧ r n ≤ p.r (Fin.last p.i) ∧
          0 < delta n ∧ delta n ≤ c n ∧
          delta n ≤ (Classical.choice (N.induction p hp)).cutoff (r n) ∧
          SurgeryObservationIsNextEpoch p (O n) ∧ SurgeryPrefixControls p (F n) (O n) ∧
          SurgeryFlowAdmissible (F n) ∧ SurgeryFlowPinched (F n) ∧
          SurgeryFlowTerminalPolicyOn (F n) (surgeryObservationInterval (O n)) ∧
          SurgeryPostPrefixScales p (F n) (O n) (r n) (delta n) ∧
          (∀ s ∈ surgeryObservationInterval (O n) ∩
            Ico (surgeryEpochStart (p.i - 1)) (O n).H, (F n).parameters.delta s ≤ delta n) ∧
          t n ∈ Ico (surgeryEpochStart p.i) (O n).H ∧
          t n = sInf (canonicalFailureTimes (F n) (O n) (r n)) ∧
          SurgeryCanonicalOn (F n) (Ico 0 (t n)) (r n) ∧
          (r n)⁻¹ ^ 2 ≤ ((F n).connection (t n)).scalarCurvature (x n) ∧
          ¬ SurgeryCanonicalControl (F n) (t n) (x n)
            (F n).parameters.epsilon (F n).parameters.C ∧
          SurgeryVolumeControlOn (F n) (Icc (surgeryEpochStart p.i) (t n)) k
            (fun _ _ => True) := by
  exact exists_seed_firstFailure_counterexample_sequence P S N p hp
    (fun _ hs _ hdistance => standard_tip_locus_setup_cap S hs hdistance) hno

end PoincareMT.Proofs.M47
