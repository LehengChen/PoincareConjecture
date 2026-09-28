import PoincareMT.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionBudget

/-!
# Region budget alternative

The curvature-area budget contradiction has a useful contrapositive form:
under the curvature lower and upper estimates and a fixed `pi/2` budget, a
candidate region cannot be simultaneously below the area cutoff and below the
turning cutoff.  This is the branch selector used by collision-region
producers.

Context: Morgan--Tian Proposition 19.35, printed pp. 467-481, and Lemma 19.46, printed
p. 474.
-/

set_option autoImplicit false

namespace PoincareMT

/-- Either the candidate region reaches the area budget or its boundary turning reaches the
prescribed threshold. Source/construction: Morgan--Tian Lemma 19.46, printed p. 474,
curvature-area contradiction. -/
theorem m64Intrinsic_region_budget_disjunction
    {K mu delta area curvature turning : ℝ}
    (hcurvature : Real.pi / 2 - turning ≤ curvature)
    (hupper : curvature ≤ max K 0 * area)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2) :
    mu ≤ area ∨ delta ≤ turning := by
  by_cases harea : mu ≤ area
  · exact Or.inl harea
  · right
    by_contra hturn
    exact m64Intrinsic_region_budget_contradiction
      (lt_of_not_ge harea) hcurvature hupper (lt_of_not_ge hturn) hbudget

end PoincareMT
