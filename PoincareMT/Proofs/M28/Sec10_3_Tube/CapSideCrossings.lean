import PoincareMT.Proofs.M28.Mathlib.FrontierCrossing

/-!
# Actual endpoint sphere returns from a supplied closed cap side

Morgan--Tian Claim 10.3, pp. 248-249. The cap geometry constructs one
compact side C whose frontier lies in the selected endpoint sphere S.
These lemmas produce the before/after sphere hits for both orientations
of an actual tested path. They construct neither C nor a confinement set.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.M28

variable {M : Type u} [TopologicalSpace M]

/-- From the cap side to a sphere endpoint, an actual exterior excursion
has sphere hits before and after it. The final hit is the actual endpoint
(Claim 10.3, pp. 248-249). -/
theorem exists_cap_to_sphere_return_times
    {C S : Set M} (hC : IsClosed C) (hfront : frontier C ⊆ S)
    {γ : ℝ → M} {a t b : ℝ} (hat : a ≤ t) (htb : t ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (ha : γ a ∈ C) (hb : γ b ∈ S)
    (ht : γ t ∉ C) :
    ∃ c d : ℝ, a ≤ c ∧ c ≤ t ∧ t ≤ d ∧ d ≤ b ∧ γ c ∈ S ∧ γ d ∈ S := by
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl htb
  obtain ⟨c, hc, hf⟩ := (hγ.mono hsub).exists_frontier_crossing_before hC hat ha ht
  exact ⟨c, b, hc.1, hc.2.le, htb, le_rfl, hfront hf, hb⟩

/-- From a sphere endpoint to the cap side, an actual exterior excursion
has sphere hits before and after it. The first hit is the actual endpoint
(Claim 10.3, pp. 248-249). -/
theorem exists_sphere_to_cap_return_times
    {C S : Set M} (hC : IsClosed C) (hfront : frontier C ⊆ S)
    {γ : ℝ → M} {a t b : ℝ} (hat : a ≤ t) (htb : t ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (ha : γ a ∈ S) (hb : γ b ∈ C)
    (ht : γ t ∉ C) :
    ∃ c d : ℝ, a ≤ c ∧ c ≤ t ∧ t ≤ d ∧ d ≤ b ∧ γ c ∈ S ∧ γ d ∈ S := by
  have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc hat le_rfl
  obtain ⟨d, hd, hf⟩ := (hγ.mono hsub).exists_frontier_crossing_after hC htb ht hb
  exact ⟨a, d, le_rfl, hat, hd.1.le, hd.2, ha, hfront hf⟩

end PoincareMT.M28
