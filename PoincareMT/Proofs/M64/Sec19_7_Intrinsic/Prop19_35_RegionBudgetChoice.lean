import PoincareMT.Statements.M64Comparison

/-! A positive area cutoff can be chosen before the intrinsic annulus.

Context: Morgan--Tian Proposition 19.35, printed pp. 467-481, and Lemma 19.46, printed
p. 474.
-/

set_option autoImplicit false

namespace PoincareMT

/-- Choose a positive area budget for the `pi/2` curvature contradiction.
Source/construction: Morgan--Tian Proposition 19.35, printed p. 467, constants chosen before
the annulus. -/
theorem m64Intrinsic_exists_region_budget
    {K delta : ℝ} (_hdelta : 0 < delta)
    (hdelta_pi : delta < Real.pi / 2) :
    ∃ mu : ℝ, 0 < mu ∧ max K 0 * mu + delta ≤ Real.pi / 2 := by
  let c : ℝ := max K 0
  let mu : ℝ := (Real.pi / 2 - delta) / (c + 1)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact le_max_right K 0
  have hnum : 0 < Real.pi / 2 - delta := by
    linarith [Real.pi_pos]
  have hden : 0 < c + 1 := by linarith
  refine ⟨mu, by dsimp [mu]; positivity, ?_⟩
  have hmul : c * mu ≤ Real.pi / 2 - delta := by
    dsimp [mu]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hmul' : max K 0 * mu ≤ Real.pi / 2 - delta := by
    simpa only [c] using hmul
  linarith

end PoincareMT
