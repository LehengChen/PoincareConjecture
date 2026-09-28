import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# A subsequence with fixed finite labels

The subsequence step on Morgan--Tian p. 456. In M65 derivation 20 the
interval endpoints are fixed in advance, so only their finite good labels
must be held constant along a subsequence.
-/

set_option autoImplicit false

open Filter

namespace PoincareMT.M65

/-- A sequence in a fixed finite set has a strictly increasing constant
subsequence; the finite-label selection on Morgan--Tian p. 456. -/
theorem exists_constant_subsequence_of_mem_finset {α : Type*} (values : Finset α)
    (labels : ℕ → α) (hlabels : ∀ i, labels i ∈ values) :
    ∃ value ∈ values, ∃ select : ℕ → ℕ,
      StrictMono select ∧ ∀ i, labels (select i) = value := by
  let labels' : ℕ → values := fun i => ⟨labels i, hlabels i⟩
  obtain ⟨value, hvalue⟩ := Finite.exists_infinite_fiber labels'
  have hfreq : ∃ᶠ i in atTop, labels' i = value :=
    Nat.frequently_atTop_iff_infinite.mpr (Set.infinite_coe_iff.mp hvalue)
  obtain ⟨select, hselect, hconstant⟩ := extraction_of_frequently_atTop hfreq
  exact ⟨value.val, value.property, select, hselect,
    fun i => congrArg Subtype.val (hconstant i)⟩

end PoincareMT.M65
