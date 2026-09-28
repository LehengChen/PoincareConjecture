import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

/-!
# Actual scalar target products preserve rapid radial decay

Morgan-Tian pp. 313-320. The restart target coefficient is f0 f0'/r.
The binomial derivative identity shows that bounded jets times rapidly
decaying jets retain every polynomial decay order. The actual reciprocal
radius derivatives are uniformly bounded on the exterior half-line.
-/

set_option autoImplicit false

open Set
open scoped ContDiff BigOperators

namespace PoincareMT.M35.RadialGauge

/-- Multiplication by a family with bounded actual jets preserves every
polynomial decay order of actual scalar derivatives on the exterior. -/
theorem scalar_rapid_product {A : Type*} {f g : A → ℝ → ℝ}
    (hf : ∀ a, ContDiffOn ℝ ∞ (f a) (Ioi 0))
    (hg : ∀ a, ContDiffOn ℝ ∞ (g a) (Ioi 0))
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      |iteratedDeriv j (f a) r| ≤ C)
    (hr : ∀ j N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      (1 + r) ^ N * |iteratedDeriv j (g a) r| ≤ C) :
    ∀ j N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      (1 + r) ^ N * |iteratedDeriv j (fun s => f a s * g a s) r| ≤ C := by
  classical
  choose B hB0 hB using hb
  intro j N
  choose D hD0 hD using fun i => hr i N
  let C := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * D (j - i)
  refine ⟨C, Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB0 i)) (hD0 (j - i))), ?_⟩
  intro a r hrad
  have hpos : 0 < r := lt_of_lt_of_le zero_lt_one hrad
  have hfa := ((hf a) r hpos).contDiffAt (Ioi_mem_nhds hpos)
  have hga := ((hg a) r hpos).contDiffAt (Ioi_mem_nhds hpos)
  rw [iteratedDeriv_fun_mul (hfa.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j))
    (hga.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j))]
  have hw : 0 ≤ (1 + r) ^ N := by positivity
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hw).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have hm := mul_le_mul
    (mul_le_mul_of_nonneg_left (hB i a r hrad) (Nat.cast_nonneg (j.choose i)))
    (hD (j - i) a r hrad) (mul_nonneg hw (abs_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _) (hB0 i))
  convert! hm using 1
  ring

/-- The literal reciprocal radius has bounded actual derivatives of
every order on r >= 1; the tip is excluded in this exterior statement. -/
theorem reciprocal_radius_jet_bound (j : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    |iteratedDeriv j (fun s : ℝ => 1 / s) r| ≤ (j.factorial : ℝ) := by
  have hformula := iteratedDerivWithin_one_div (𝕜 := ℝ) j isOpen_univ (mem_univ r)
  simp only [iteratedDerivWithin_univ] at hformula
  rw [hformula, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (zpow_nonneg (le_trans zero_le_one hr) _)]
  have hp : r ^ (-1 - (j : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hr (by omega)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg j.factorial)

end PoincareMT.M35.RadialGauge
