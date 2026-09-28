import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Smooth diffeomorphisms from small Lipschitz perturbations

A smooth perturbation of the identity with Lipschitz constant below one
is a global diffeomorphism. A bounded smooth time parameter gives a
compactly supported isotopy when the perturbation has compact support.
This supplies the local chart straightening step in Hatcher, Notes on
Basic 3-Manifold Topology, Lemma 1.3, p. 3. The quantitative cutoff
argument is recorded in the local-chart-straightening derivation.
-/

set_option autoImplicit false

open Set
open scoped ContDiff Manifold NNReal

namespace PoincareMT.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A smooth globally small Lipschitz perturbation of the identity has
an invertible derivative at every point, by the geometric series. -/
theorem smallPerturbation_invertible_derivative (g : E → E)
    (hg : ContDiff ℝ ∞ g) {L : ℝ≥0} (hL : L < 1) (hlip : LipschitzWith L g)
    (x : E) : ∃ A : E ≃L[ℝ] E,
      HasFDerivAt (fun y => y + g y) (A : E →L[ℝ] E) x := by
  have hnorm : ‖-fderiv ℝ g x‖ < 1 := by
    rw [norm_neg]
    exact (norm_fderiv_le_of_lipschitz ℝ hlip).trans_lt (by exact_mod_cast hL)
  let A := ContinuousLinearEquiv.ofUnit (Units.oneSub (-fderiv ℝ g x) hnorm)
  refine ⟨A, ?_⟩
  change HasFDerivAt (fun y => y + g y) (1 - (-fderiv ℝ g x)) x
  simpa only [sub_neg_eq_add, ContinuousLinearMap.one_def, id_eq] using
    (hasFDerivAt_id x).fun_add (((hg.differentiable (by simp)) x).hasFDerivAt)

/-- Global smooth inverse for a perturbation with Lipschitz constant
strictly below one; used to straighten a sufficiently small chart germ. -/
noncomputable def smallPerturbationDiffeomorph (g : E → E)
    (hg : ContDiff ℝ ∞ g) {L : ℝ≥0} (hL : L < 1) (hlip : LipschitzWith L g) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ := by
  have happ : ApproximatesLinearOn (fun x => x + g x)
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) univ L := by
    intro x _ y _
    have heq : (x + g x) - (y + g y) - (x - y) = g x - g y := by abel
    simpa only [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply, heq] using
      hlip.norm_sub_le x y
  have hbound : Subsingleton E ∨
      L < ‖((ContinuousLinearEquiv.refl ℝ E).symm : E →L[ℝ] E)‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    · exact Or.inr (by simpa using hL)
  let e : E ≃ₜ E := happ.toHomeomorph (fun x => x + g x) hbound
  have he : ContDiff ℝ ∞ (e : E → E) := contDiff_id.add hg
  have hd := fun x => smallPerturbation_invertible_derivative g hg hL hlip x
  let A := fun x => (hd x).choose
  have hA : ∀ x, HasFDerivAt e (A x : E →L[ℝ] E) x := fun x => (hd x).choose_spec
  exact {
    toEquiv := e.toEquiv
    contMDiff_toFun := he.contMDiff
    contMDiff_invFun := (e.contDiff_symm hA he).contMDiff }

/-- The small-perturbation diffeomorphism retains its explicit formula. -/
theorem smallPerturbationDiffeomorph_apply (g : E → E)
    (hg : ContDiff ℝ ∞ g) {L : ℝ≥0} (hL : L < 1) (hlip : LipschitzWith L g) (x : E) :
    smallPerturbationDiffeomorph g hg hL hlip x = x + g x := rfl

omit [CompleteSpace E] in
/-- A bounded scalar multiple retains the original Lipschitz bound. -/
theorem lipschitz_smul_of_abs_le_one (g : E → E) {L : ℝ≥0}
    (hlip : LipschitzWith L g) (a : ℝ) (ha : |a| ≤ 1) :
    LipschitzWith L (fun x => a • g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs]
  calc
    |a| * ‖g x - g y‖ ≤ 1 * ‖g x - g y‖ :=
      mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    _ ≤ L * dist x y := by simpa only [one_mul, dist_eq_norm] using hlip.norm_sub_le x y

/-- Smooth straight-line isotopy with stationary time tails and one
compact support, for the local attaching-disc chart correction. -/
theorem exists_smallPerturbation_isotopy (g : E → E)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {L : ℝ≥0} (hL : L < 1) (hlip : LipschitzWith L g) :
    ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      (∀ t x, Φ t x = x + Real.smoothTransition t • g x) ∧
      (∀ t x, t ≤ 0 → Φ t x = x) ∧
      (∀ t x, 1 ≤ t → Φ t x = x + g x) ∧
      ∃ C : Set E, IsCompact C ∧ ∀ t x, x ∉ C → Φ t x = x := by
  have hbound (t : ℝ) : |Real.smoothTransition t| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg t)]
    exact Real.smoothTransition.le_one t
  let Φ := fun t => smallPerturbationDiffeomorph
    (fun x => Real.smoothTransition t • g x) (contDiff_const.smul hg)
    hL (lipschitz_smul_of_abs_le_one g hlip _ (hbound t))
  refine ⟨Φ, ?_, (fun _ _ => rfl), ?_, ?_, tsupport g, hgc, ?_⟩
  · exact contDiff_snd.add
      ((Real.smoothTransition.contDiff.comp contDiff_fst).smul (hg.comp contDiff_snd))
  · intro t x ht
    change x + Real.smoothTransition t • g x = x
    rw [Real.smoothTransition.zero_of_nonpos ht, zero_smul, add_zero]
  · intro t x ht
    change x + Real.smoothTransition t • g x = x + g x
    rw [Real.smoothTransition.one_of_one_le ht, one_smul]
  · intro t x hx
    change x + Real.smoothTransition t • g x = x
    rw [image_eq_zero_of_notMem_tsupport hx, smul_zero, add_zero]

end PoincareMT.M25.Topology3D
