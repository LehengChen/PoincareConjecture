import PoincareMT.Proofs.M34.Sec12_5_RotationInvariance.TranslatedEnergyCutoffs

/-!
# Quantitative neighboring cutoff cover

Each end support band is covered by three neighboring plateau regions.
The core and initial end band are covered by the core and the first two
end plateaus. Squaring the cutoff values gives the lower bound needed
before comparing actual coordinate densities on chart overlaps.
This is Morgan-Tian Section 12.5, pp. 309-319 and energy-cutoff-cover.md.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

/-- Away from index zero, three neighboring plateaus cover the whole
closed support band (Section 12.5, pp. 309-319). -/
theorem translatedEnergyCutoff_neighbor_plateau (e : StandardCylindricalEnd g)
    {j : ℕ} (hj : 0 < j) {x : StandardCapSpace}
    (hx : endExhaustion e x - (j : ℝ) ∈ Icc (41 / 10 : ℝ) (59 / 10)) :
    translatedEnergyCutoff e (j - 1) x = 1 ∨ translatedEnergyCutoff e j x = 1 ∨
      translatedEnergyCutoff e (j + 1) x = 1 := by
  by_cases hl : endExhaustion e x - (j : ℝ) < 22 / 5
  · left
    have hn : j - 1 + 1 = j := Nat.sub_add_cancel (by omega)
    have hr := congrArg (fun k : ℕ => (k : ℝ)) hn
    simp only [Nat.cast_add, Nat.cast_one] at hr
    apply translatedEnergyCutoff_eq_one e (j - 1)
    constructor <;> linarith [hx.1]
  · right
    by_cases hu : endExhaustion e x - (j : ℝ) ≤ 28 / 5
    · left
      exact translatedEnergyCutoff_eq_one e j ⟨le_of_not_gt hl, hu⟩
    · right
      apply translatedEnergyCutoff_eq_one e (j + 1)
      simp only [Nat.cast_add, Nat.cast_one]
      constructor <;> linarith [hx.2]

/-- Neighboring squared cutoff weights dominate one on each positive
index's support band (Section 12.5, pp. 309-319). -/
theorem translatedEnergyCutoff_neighbor_squares (e : StandardCylindricalEnd g)
    {j : ℕ} (hj : 0 < j) {x : StandardCapSpace}
    (hx : endExhaustion e x - (j : ℝ) ∈ Icc (41 / 10 : ℝ) (59 / 10)) :
    1 ≤ translatedEnergyCutoff e (j - 1) x ^ 2 + translatedEnergyCutoff e j x ^ 2 +
      translatedEnergyCutoff e (j + 1) x ^ 2 := by
  rcases translatedEnergyCutoff_neighbor_plateau e hj hx with h | h | h
  · rw [h]
    nlinarith [sq_nonneg (translatedEnergyCutoff e j x),
      sq_nonneg (translatedEnergyCutoff e (j + 1) x)]
  · rw [h]
    nlinarith [sq_nonneg (translatedEnergyCutoff e (j - 1) x),
      sq_nonneg (translatedEnergyCutoff e (j + 1) x)]
  · rw [h]
    nlinarith [sq_nonneg (translatedEnergyCutoff e (j - 1) x),
      sq_nonneg (translatedEnergyCutoff e j x)]

/-- The core and the first two end plateaus cover the whole height-six
sublevel (Section 12.5, pp. 309-319). -/
theorem energyCutoffs_initial_plateau (e : StandardCylindricalEnd g) {x : StandardCapSpace}
    (hx : endExhaustion e x ≤ 6) :
    coreEnergyCutoff e x = 1 ∨ translatedEnergyCutoff e 0 x = 1 ∨
      translatedEnergyCutoff e 1 x = 1 := by
  by_cases hc : endExhaustion e x ≤ 5
  · exact Or.inl (coreEnergyCutoff_eq_one e hc)
  · right
    by_cases h0 : endExhaustion e x ≤ 28 / 5
    · left
      apply translatedEnergyCutoff_eq_one e 0
      norm_num only [Nat.cast_zero, sub_zero]
      constructor <;> linarith
    · right
      apply translatedEnergyCutoff_eq_one e 1
      norm_num only [Nat.cast_one]
      constructor <;> linarith

/-- The core and first two squared end cutoffs dominate one on the core
and initial end support bands (Section 12.5, pp. 309-319). -/
theorem energyCutoffs_initial_squares (e : StandardCylindricalEnd g) {x : StandardCapSpace}
    (hx : endExhaustion e x ≤ 6) :
    1 ≤ coreEnergyCutoff e x ^ 2 + translatedEnergyCutoff e 0 x ^ 2 +
      translatedEnergyCutoff e 1 x ^ 2 := by
  rcases energyCutoffs_initial_plateau e hx with h | h | h
  · rw [h]
    nlinarith [sq_nonneg (translatedEnergyCutoff e 0 x),
      sq_nonneg (translatedEnergyCutoff e 1 x)]
  · rw [h]
    nlinarith [sq_nonneg (coreEnergyCutoff e x),
      sq_nonneg (translatedEnergyCutoff e 1 x)]
  · rw [h]
    nlinarith [sq_nonneg (coreEnergyCutoff e x),
      sq_nonneg (translatedEnergyCutoff e 0 x)]

end PoincareMT.M34
