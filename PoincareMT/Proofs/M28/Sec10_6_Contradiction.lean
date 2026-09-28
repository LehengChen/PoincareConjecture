import PoincareMT.Proofs.M28.Sec10_3_Tube.LimitData
import PoincareMT.Proofs.M28.Thm10_2_SameTime

/-!
# Conditional assembly of the tube contradiction

The two geometric producers remain explicit: construct the actual
limiting tube from counterexamples, then exclude that tube by the cone
and local flow argument. This records the consumer interface of
Morgan--Tian sections 10.3-10.6, pp. 247-265; see task derivation 12.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.M28

/-- Construction and impossibility of the actual tube imply the frozen
same-time estimate. Both geometric steps are hypotheses of this
conditional assembly, not newly assumed predecessor fields. -/
theorem same_time_of_tube_contradiction {epsilon₀ : ℝ}
    (hproduce : ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
      ∀ C : ℝ, 0 < C → ∀ A : ℝ, 0 ≤ A →
        (∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)) →
            Nonempty (SingularNeckTubeWitness (2 * epsilon)))
    (hexclude : ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
      SingularNeckTubeWitness (2 * epsilon) → False) :
    M28SameTimeEstimateStatement.{u} epsilon₀ := by
  apply same_time_of_counterexample_exclusion
  intro epsilon hepsilon hsmall C hC A hA E
  obtain ⟨T⟩ := hproduce epsilon hepsilon hsmall C hC A hA E
  exact hexclude epsilon hepsilon hsmall T

end PoincareMT.M28
