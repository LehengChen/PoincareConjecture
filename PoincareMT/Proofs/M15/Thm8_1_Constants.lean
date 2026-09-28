import PoincareMT.Proofs.M15.Thm8_1_Reduction

/-!
# The numerical conclusion of Theorem 8.1

Morgan-Tian, the deduction of Theorem 8.1 from Proposition 8.2, p. 170.
The constant uses the uniform lower bound from equation (8.1), not a value
chosen after the tested ball. Geometric proofs of the alternatives in the
volume-ratio estimate remain the content of Proposition 8.2.
-/

set_option autoImplicit false

namespace PoincareMT.Proofs.M15

/-- The positive uniform constant in the repaired deduction on p. 170.
The source-dependent lower bound is the only input besides n and epsilon0. -/
noncomputable def theorem81Kappa (n : ℕ) (epsilon0 lower : ℝ) : ℝ :=
  min (epsilon0 ^ n) (lower ^ 2 / 9)

/-- Both entries of the minimum defining the Theorem 8.1 constant are
positive. Source: the deduction following Proposition 8.2, p. 170. -/
theorem theorem81Kappa_pos {n : ℕ} {epsilon0 lower : ℝ}
    (hepsilon0 : 0 < epsilon0) (hlower : 0 < lower) :
    0 < theorem81Kappa n epsilon0 lower := by
  exact lt_min (pow_pos hepsilon0 _) (div_pos (sq_pos_of_pos hlower) (by norm_num))

/-- Either a large volume ratio or the Proposition 8.2 comparison bounds
the same kappa by the volume ratio. Source: Theorem 8.1, p. 170. -/
theorem theorem81Kappa_le_ratio {n : ℕ} {epsilon0 lower epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon0) (hlower : 0 ≤ lower) (hepsilon : 0 < epsilon)
    (halternative : epsilon0 ≤ epsilon ∨
      lower ≤ 3 * Real.rpow epsilon ((n : ℝ) / 2)) :
    theorem81Kappa n epsilon0 lower ≤ epsilon ^ n := by
  rcases halternative with hlarge | hsmall
  · exact (min_le_left _ _).trans (pow_le_pow_left₀ hepsilon0 hlarge n)
  · have hsquare : (Real.rpow epsilon ((n : ℝ) / 2)) ^ 2 = epsilon ^ n := by
      calc
        (Real.rpow epsilon ((n : ℝ) / 2)) ^ 2 =
            Real.rpow epsilon ((n : ℝ) / 2 * 2) := by
          simp only [Real.rpow_eq_pow]
          rw [Real.rpow_mul hepsilon.le, Real.rpow_two]
        _ = epsilon ^ n := by
          simp only [Real.rpow_eq_pow]
          rw [div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_natCast]
    apply (min_le_right _ _).trans
    have hsq := mul_self_le_mul_self hlower hsmall
    nlinarith [hsquare]

end PoincareMT.Proofs.M15
