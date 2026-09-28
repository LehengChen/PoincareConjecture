import PoincareMT.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionBudgetChoice
import PoincareMT.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionBudgetDisjunction

/-!
# Quantified region budget alternative

The proof selects a positive area threshold using only K and delta, then
applies the curvature-area budget to the supplied candidate. The exported
adapter quantifies that candidate before its existential cutoff. The
independent before-annulus cutoff is supplied by RegionBudgetChoice and
the later uniform comparison assembly.

Context: Morgan--Tian Proposition 19.35, printed pp. 467-481, and Lemma 19.46, printed
p. 474.
-/

set_option autoImplicit false

namespace PoincareMT

/-- For a supplied candidate, use the cutoff chosen from K and delta to obtain the
area-or-turning alternative. The exported adapter quantifies the candidate before its
existential cutoff. Source/construction:
proof-work/tasks/M64/derivations/2026-09-25-region-budget-alternative.md; exported
per-candidate quantifiers. -/
theorem m64Intrinsic_exists_region_budget_alternative
    {K delta area curvature turning : ℝ}
    (hdelta : 0 < delta) (hdelta_pi : delta < Real.pi / 2)
    (hcurvature : Real.pi / 2 - turning ≤ curvature)
    (hupper : curvature ≤ max K 0 * area) :
    ∃ mu : ℝ, 0 < mu ∧ (mu ≤ area ∨ delta ≤ turning) := by
  obtain ⟨mu, hmu, hbudget⟩ := m64Intrinsic_exists_region_budget
    hdelta hdelta_pi
  exact ⟨mu, hmu,
    m64Intrinsic_region_budget_disjunction hcurvature hupper hbudget⟩

end PoincareMT
