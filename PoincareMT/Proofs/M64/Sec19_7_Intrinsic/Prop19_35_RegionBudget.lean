import PoincareMT.Statements.M64Comparison

/-!
# Curvature-area budget contradiction

The collision-region argument combines a lower curvature estimate, a Gaussian
area upper bound, and the short-arc turning estimate.  This small consumer
keeps that final strict arithmetic independent of the geometric region
construction.

Context: Morgan--Tian Proposition 19.35, printed pp. 467-481, and Lemma 19.46, printed
p. 474.
-/

set_option autoImplicit false

namespace PoincareMT

/-- A `pi/2` curvature budget excludes a region whose boundary turning is strictly below
`delta` and whose area is below `mu`. Source/construction: Morgan--Tian Lemma 19.46, printed
p. 474, curvature-area contradiction. -/
theorem m64Intrinsic_region_budget_contradiction
    {K mu delta area curvature turning : ℝ}
    (harea : area < mu)
    (hcurvature : Real.pi / 2 - turning ≤ curvature)
    (hupper : curvature ≤ max K 0 * area)
    (hturning : turning < delta)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2) :
    False := by
  have hscale : max K 0 * area ≤ max K 0 * mu := by
    exact mul_le_mul_of_nonneg_left harea.le (le_max_right K 0)
  linarith

end PoincareMT
