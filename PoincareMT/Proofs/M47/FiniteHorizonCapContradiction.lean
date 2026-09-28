import PoincareMT.Proofs.M47.TerminalCommonIntervalHorizon

/-!
# The finite-horizon cap contradiction interfaces

The endpoint argument is split into the three logical steps used in the
finite-horizon proof.  The first step extracts a frequently failing radius
from maximality of the common horizon.  The second is the Claim 17.10
cap-contact step and keeps the pointwise canonical producer explicit.  The
third applies the line scalar estimate and cap persistence at the contact.
No canonical extension or extra seed hypothesis is hidden in these interfaces.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal

universe u

namespace PoincareMT.M47

/- The finite slab supplied by Theorem 11.8 would put its duration below the
   horizon, so it cannot exist strictly above a finite maximal horizon. -/
theorem terminalCommonInterval_slab_fails_above_horizon
    {V : GeneralizedBlowupSequence.{u}} {T : ℝ} (hT : 0 < T)
    (habove : terminalCommonIntervalHorizon V < ENNReal.ofReal T) :
    ¬ TerminalCommonIntervalSlab V T := by
  intro hslab
  have hmem : ENNReal.ofReal T ∈ TerminalCommonIntervalHorizons V := by
    intro U hU hUT
    exact terminalCommonInterval_slab_mono hslab
      ((ENNReal.ofReal_lt_ofReal_iff hT).mp hUT).le
  exact (not_lt_of_ge (le_sSup hmem)) habove

/-- A finite maximal horizon leaves one radius with a frequently failing
neighborhood test.  The `thm11_8` argument is the strict-below-horizon slab
construction; it is intentionally an input rather than a new premise of the
M47 induction statement. -/
theorem finiteHorizon_neighborhood_fails
    {V : GeneralizedBlowupSequence.{u}} (Nbhd : ℕ → ℝ → ℝ → Prop)
    (thm11_8 : ∀ t : ℝ, 0 < t →
      (∀ A : ℝ, 0 < A → ∀ᶠ k in atTop, Nbhd k A t) →
      ∀ T : ℝ, 0 < T → T < t → TerminalCommonIntervalSlab V T)
    {t : ℝ} (ht : 0 < t)
    (hT : terminalCommonIntervalHorizon V < ENNReal.ofReal t) :
    ∃ A : ℝ, 0 < A ∧ ∃ᶠ k in atTop, ¬ Nbhd k A t := by
  by_contra hnone
  push Not at hnone
  have hall : ∀ A : ℝ, 0 < A → ∀ᶠ k in atTop, Nbhd k A t := by
    intro A hA
    exact hnone A hA
  have hreal : (terminalCommonIntervalHorizon V).toReal < t :=
    ENNReal.toReal_lt_of_lt_ofReal hT
  let T : ℝ := (terminalCommonIntervalHorizon V).toReal / 2 + t / 2
  have hTpos : 0 < T := by
    dsimp [T]
    have hnonneg : 0 ≤ (terminalCommonIntervalHorizon V).toReal :=
      ENNReal.toReal_nonneg
    linarith
  have hTlt : T < t := by
    dsimp [T]
    linarith
  have habove : terminalCommonIntervalHorizon V < ENNReal.ofReal T := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt (ne_top_of_lt hT)).mpr
    dsimp [T]
    linarith
  exact terminalCommonInterval_slab_fails_above_horizon hTpos habove
    (thm11_8 t ht hall T hTpos hTlt)

/-- The Claim 17.10 step: a frequently failing neighborhood produces a
frequent backward line meeting a cap.  The supplied `cap_contact` is the
pointwise source-or-cap/canonical comparison, so the finite-horizon proof does
not introduce a separate `hnoCap` assumption. -/
theorem finiteHorizon_cap_contact_of_failed_neighborhood
    {Nbhd Contact : ℕ → ℝ → ℝ → Prop} {t : ℝ}
    (failure : ∃ A : ℝ, 0 < A ∧ ∃ᶠ k in atTop, ¬ Nbhd k A t)
    (cap_contact : ∀ A : ℝ, 0 < A →
      ∀ᶠ k in atTop, ¬ Nbhd k A t → Contact k A t) :
    ∃ A : ℝ, 0 < A ∧ ∃ᶠ k in atTop, Contact k A t := by
  obtain ⟨A, hA, hfail⟩ := failure
  refine ⟨A, hA, ?_⟩
  exact (hfail.and_eventually (cap_contact A hA)).mono
    (fun k hk => hk.2 hk.1)

/-- Lemma 11.2 followed by Lemma 17.7 contradicts the first-failure point.
The contact and scalar-line hypotheses are consumed in order, and the
canonical conclusion remains an explicit output of cap persistence. -/
theorem finiteHorizon_cap_persistence_contradiction
    {Contact LineBound Canonical : ℕ → ℝ → Prop}
    (hbad : ∀ k A, ¬ Canonical k A)
    (cap : ∃ A : ℝ, 0 < A ∧ ∃ᶠ k in atTop, Contact k A)
    (line_bound : ∀ A : ℝ, 0 < A →
      ∀ᶠ k in atTop, Contact k A → LineBound k A)
    (cap_persistence : ∀ A : ℝ, 0 < A →
      ∀ᶠ k in atTop, Contact k A → LineBound k A → Canonical k A) :
    False := by
  obtain ⟨A, hA, hcontact⟩ := cap
  have hline := line_bound A hA
  have hpersist := cap_persistence A hA
  have hcanonical : ∀ᶠ k in atTop, Contact k A → Canonical k A := by
    filter_upwards [hline, hpersist] with k hk_line hk_persist hk_contact
    exact hk_persist hk_contact (hk_line hk_contact)
  obtain ⟨k, hk_contact, hk_canonical⟩ :=
    (hcontact.and_eventually hcanonical).exists
  exact hbad k A (hk_canonical hk_contact)

end PoincareMT.M47
