import PoincareMT.Proofs.M25.Topology3D.Space3.FlowInvariants
import PoincareMT.Proofs.M25.Topology3D.Space3.FieldLocalization
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Horizontal fields in radial disc coordinates

A compact radial cutoff lifts a compactly supported disc field to a
product neighborhood without changing its radial coordinate. On the
unit-radius slice the original flow is recovered exactly. These are the
source-coordinate tracks for Hatcher's attaching-disc standardization,
Notes on Basic 3-Manifold Topology, Lemma 1.3, p. 3.
-/

set_option autoImplicit false

open Set
open scoped ContDiff NNReal

namespace PoincareMT.M25.Topology3D

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Lift a disc field horizontally, localizing it in the radial variable. -/
noncomputable def horizontalFieldLift (χ : ℝ → ℝ) (f : P → P) (p : P × ℝ) : P × ℝ :=
  (χ p.2 • f p.1, 0)

/-- The horizontal lift of smooth data is smooth. -/
theorem horizontalFieldLift_contDiff (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (f : P → P) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (horizontalFieldLift χ f) :=
  (((hχ.comp contDiff_snd).smul (hf.comp contDiff_fst)).prodMk contDiff_const)

/-- Both cutoffs constrain the closed support of the horizontal lift. -/
theorem horizontalFieldLift_tsupport (χ : ℝ → ℝ) (f : P → P) :
    tsupport (horizontalFieldLift χ f) ⊆ tsupport f ×ˢ tsupport χ := by
  apply closure_minimal _ ((isClosed_tsupport f).prod (isClosed_tsupport χ))
  intro p hp
  constructor
  · apply subset_tsupport
    intro h
    exact hp (by simp only [horizontalFieldLift, h, smul_zero, Prod.mk_zero_zero])
  · apply subset_tsupport
    intro h
    exact hp (by simp only [horizontalFieldLift, h, zero_smul, Prod.mk_zero_zero])

/-- Compact support in each factor gives compact support in the product. -/
theorem horizontalFieldLift_hasCompactSupport (χ : ℝ → ℝ) (hχ : HasCompactSupport χ)
    (f : P → P) (hf : HasCompactSupport f) :
    HasCompactSupport (horizontalFieldLift χ f) :=
  (hf.isCompact.prod hχ.isCompact).of_isClosed_subset
    (isClosed_tsupport _) (horizontalFieldLift_tsupport χ f)

variable [CompleteSpace P]

/-- Every trajectory of the lifted field retains its radial coordinate. -/
theorem horizontalFieldLift_flow_snd (χ : ℝ → ℝ) (f : P → P) {K L : ℝ≥0}
    (hK : LipschitzWith K (horizontalFieldLift χ f))
    (hL : ∀ p, ‖horizontalFieldLift χ f p‖ ≤ L) (p : P × ℝ) (t : ℝ) :
    (boundedFlow (horizontalFieldLift χ f) hK hL p t).2 = p.2 :=
  boundedFlow_preserves_linear (horizontalFieldLift χ f) hK hL
    (ContinuousLinearMap.snd ℝ P ℝ) (fun _ => rfl) p t

/-- Where the radial cutoff equals one, the lifted flow agrees exactly
with the original disc flow and the constant radial coordinate. -/
theorem horizontalFieldLift_flow_slice (χ : ℝ → ℝ) (f : P → P)
    {k l K L : ℝ≥0} (hk : LipschitzWith k f) (hl : ∀ x, ‖f x‖ ≤ l)
    (hK : LipschitzWith K (horizontalFieldLift χ f))
    (hL : ∀ p, ‖horizontalFieldLift χ f p‖ ≤ L)
    (r : ℝ) (hr : χ r = 1) (x : P) (t : ℝ) :
    boundedFlow (horizontalFieldLift χ f) hK hL (x, r) t =
      (boundedFlow f hk hl x t, r) := by
  have hd (s : ℝ) : HasDerivAt (fun u => (boundedFlow f hk hl x u, r))
      (horizontalFieldLift χ f (boundedFlow f hk hl x s, r)) s := by
    simpa only [horizontalFieldLift, hr, one_smul] using
      (boundedFlow_hasDerivAt f hk hl x s).prodMk (hasDerivAt_const s r)
  have heq := boundedField_solution_unique (horizontalFieldLift χ f) hK
    (boundedFlow_hasDerivAt (horizontalFieldLift χ f) hK hL (x, r)) hd
    (by simp only [boundedFlow_zero])
  exact congrFun heq t

end PoincareMT.M25.Topology3D
