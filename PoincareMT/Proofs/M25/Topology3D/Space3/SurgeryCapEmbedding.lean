import PoincareMT.Proofs.M25.Topology3D.Space3.SurgeryCapCoordinates
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The actual smooth immersed rounded cap in a tube chart

An explicit affine ambient diffeomorphism places the flat-cap model in
the tube coordinates. Together with the height-coordinate equivalence
and the native sphere inclusion, it proves injectivity and immersion
of the placed coordinates on the entire sphere. The retained horizontal
radius bound puts every point in the supplied tube chart's source.

Source: equation (7) and the southern immersion argument in
`proof-work/tasks/M25/schoenflies/derivations/2026-09-22-regular-disc-surgery.md`,
following Hatcher, Notes on Basic 3-Manifold Topology, Theorem 1.1 and
Lemma 1.3, pp. 1-3. No ball-bounding or collar conclusion is assumed.
-/

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareMT.M25.Topology3D

/-- The exact affine vertical placement is an ambient diffeomorphism
whenever its sign and vertical scale are nonzero. -/
noncomputable def surgeryCapPlacementDiffeomorph (m sigma c l : ℝ)
    (hsigma : sigma ≠ 0) (hl : l ≠ 0) :
    Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2 × ℝ) (E2 × ℝ) (E2 × ℝ) ∞ where
  toEquiv := {
    toFun := fun p => (p.1, m + sigma * (c + l * p.2))
    invFun := fun p => (p.1, l⁻¹ * (sigma⁻¹ * (p.2 - m) - c))
    left_inv := fun p => Prod.ext rfl (by dsimp; field_simp [hsigma, hl]; ring)
    right_inv := fun p => Prod.ext rfl (by dsimp; field_simp [hsigma, hl]; ring) }
  contMDiff_toFun :=
    (contDiff_fst.prodMk (contDiff_const.add
      (contDiff_const.mul (contDiff_const.add (contDiff_const.mul contDiff_snd))))).contMDiff
  contMDiff_invFun :=
    (contDiff_fst.prodMk (contDiff_const.mul
      ((contDiff_const.mul (contDiff_snd.sub contDiff_const)).sub contDiff_const))).contMDiff

/-- The placement diffeomorphism has the prescribed total affine formula. -/
@[simp] theorem surgeryCapPlacementDiffeomorph_apply (m sigma c l : ℝ)
    (hsigma : sigma ≠ 0) (hl : l ≠ 0) (p : E2 × ℝ) :
    surgeryCapPlacementDiffeomorph m sigma c l hsigma hl p =
      (p.1, m + sigma * (c + l * p.2)) := rfl

/-- The inverse placement divides by the original two nonzero scales. -/
@[simp] theorem surgeryCapPlacementDiffeomorph_symm_apply (m sigma c l : ℝ)
    (hsigma : sigma ≠ 0) (hl : l ≠ 0) (p : E2 × ℝ) :
    (surgeryCapPlacementDiffeomorph m sigma c l hsigma hl).symm p =
      (p.1, l⁻¹ * (sigma⁻¹ * (p.2 - m) - c)) := rfl

variable (a : ℝ → ℝ) (b : E2 → ℝ)
variable (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
variable (ha0 : ∀ z, a z ≠ 0) (hb0 : ∀ x, b x ≠ 0)

/-- The placed cap coordinates extend to an actual ambient
diffeomorphism from Euclidean three-space to the tube-coordinate space. -/
noncomputable def surgeryCapAmbientDiffeomorph (m sigma c l : ℝ)
    (hsigma : sigma ≠ 0) (hl : l ≠ 0) :
    Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E2 × ℝ) E3 (E2 × ℝ) ∞ :=
  (heightCoordinates.toDiffeomorph.trans (flatCapDiffeomorph a b ha hb ha0 hb0)).trans
    (surgeryCapPlacementDiffeomorph m sigma c l hsigma hl)

/-- Restriction of the ambient diffeomorphism retains exactly the
already defined cap coordinates on every native sphere point. -/
theorem surgeryCapCoordinates_eq_ambient (m sigma c l : ℝ)
    (hsigma : sigma ≠ 0) (hl : l ≠ 0) (q : UnitTwoSphere) :
    surgeryCapCoordinates a b ha hb ha0 hb0 m sigma c l q =
      surgeryCapAmbientDiffeomorph a b ha hb ha0 hb0 m sigma c l hsigma hl (q : E3) := rfl

/-- Nonzero affine scales make the cap coordinates injective on the
whole unit sphere, including both hemispheres and the equator. -/
theorem surgeryCapCoordinates_injective (m sigma c l : ℝ)
    (hsigma : sigma ≠ 0) (hl : l ≠ 0) :
    Injective (surgeryCapCoordinates a b ha hb ha0 hb0 m sigma c l) := by
  let D := surgeryCapAmbientDiffeomorph a b ha hb ha0 hb0 m sigma c l hsigma hl
  intro p q hpq
  apply Subtype.ext
  exact D.toEquiv.injective hpq

/-- The derivative of the actual placed cap coordinates is injective
at every point, by the ambient diffeomorphism and native sphere inclusion. -/
theorem surgeryCapCoordinates_mfderiv_injective (m sigma c l : ℝ)
    (hsigma : sigma ≠ 0) (hl : l ≠ 0) (q : UnitTwoSphere) :
    Injective (mfderiv (𝓡 2) 𝓘(ℝ, E2 × ℝ)
      (surgeryCapCoordinates a b ha hb ha0 hb0 m sigma c l) q) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let D := surgeryCapAmbientDiffeomorph a b ha hb ha0 hb0 m sigma c l hsigma hl
  let i : UnitTwoSphere → E3 := fun p => (p : E3)
  have hi : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ i := contMDiff_coe_sphere
  have hdi : Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) i q) := by
    intro v w hvw
    exact injective_mvfderiv_subtypeVal_sphere q
      (congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (q : E3)) hvw)
  have hD : Injective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E2 × ℝ) D (q : E3)) :=
    (D.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective (mem_univ _)
  change Injective (mfderiv (𝓡 2) 𝓘(ℝ, E2 × ℝ) (D ∘ i) q)
  rw [mfderiv_comp q (D.mdifferentiable (by simp) (q : E3))
    (hi.mdifferentiable (by simp) q)]
  exact hD.comp hdi

/-- The actual placed sphere in the given tube chart, with its exact
total parametrization retained for subsequent northern-southern pasting. -/
noncomputable def surgeryCapMap (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (m sigma c l : ℝ) (q : UnitTwoSphere) : E3 :=
  T (surgeryCapCoordinates a b ha hb ha0 hb0 m sigma c l q)

/-- The cap map is literally the supplied tube chart applied to the
previously constructed rounded-cap coordinates. -/
@[simp] theorem surgeryCapMap_apply (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (m sigma c l : ℝ) (q : UnitTwoSphere) :
    surgeryCapMap a b ha hb ha0 hb0 T m sigma c l q =
      T (surgeryCapCoordinates a b ha hb ha0 hb0 m sigma c l q) := rfl

/-- The whole cap-coordinate sphere lies in the actual source of a
tube chart containing the closed unit-disc cylinder. -/
theorem surgeryCapCoordinates_mem_tube_source
    (hapos : ∀ z, 0 < a z)
    (habound : ∀ z, |z| < 1 → a z ≤ (Real.sqrt (1 - z ^ 2))⁻¹)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall 0 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (m sigma c l : ℝ) (q : UnitTwoSphere) :
    surgeryCapCoordinates a b ha hb ha0 hb0 m sigma c l q ∈ T.source :=
  hsource ⟨mem_closedBall_zero_iff.mpr
    (surgeryCapCoordinates_fst_norm_le a b ha hb ha0 hb0 hapos habound m sigma c l q),
    mem_univ _⟩

/-- Every point of the parametrized cap sphere lies in the actual
target of the supplied tube chart. -/
theorem surgeryCapMap_range_subset_target
    (hapos : ∀ z, 0 < a z)
    (habound : ∀ z, |z| < 1 → a z ≤ (Real.sqrt (1 - z ^ 2))⁻¹)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall 0 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (m sigma c l : ℝ) :
    range (surgeryCapMap a b ha hb ha0 hb0 T m sigma c l) ⊆ T.target := by
  rintro _ ⟨q, rfl⟩
  exact T.map_source
    (surgeryCapCoordinates_mem_tube_source a b ha hb ha0 hb0 hapos habound
      T hsource m sigma c l q)

/-- The actual cap map is globally smooth on the native unit sphere. -/
theorem surgeryCapMap_contMDiff
    (hapos : ∀ z, 0 < a z)
    (habound : ∀ z, |z| < 1 → a z ≤ (Real.sqrt (1 - z ^ 2))⁻¹)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall 0 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source) (m sigma c l : ℝ) :
    ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ (surgeryCapMap a b ha hb ha0 hb0 T m sigma c l) := by
  apply contMDiffOn_univ.mp
  exact hT.contMDiffOn.comp
    (surgeryCapCoordinates_contMDiff a b ha hb ha0 hb0 m sigma c l).contMDiffOn
    (fun q _ => surgeryCapCoordinates_mem_tube_source a b ha hb ha0 hb0 hapos habound
      T hsource m sigma c l q)

/-- Chart injectivity and nonzero affine scales give injectivity of
the actual cap map on the full sphere. -/
theorem surgeryCapMap_injective
    (hapos : ∀ z, 0 < a z)
    (habound : ∀ z, |z| < 1 → a z ≤ (Real.sqrt (1 - z ^ 2))⁻¹)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall 0 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (m sigma c l : ℝ) (hsigma : sigma ≠ 0) (hl : l ≠ 0) :
    Injective (surgeryCapMap a b ha hb ha0 hb0 T m sigma c l) := by
  intro p q hpq
  apply surgeryCapCoordinates_injective a b ha hb ha0 hb0 m sigma c l hsigma hl
  exact T.injOn
    (surgeryCapCoordinates_mem_tube_source a b ha hb ha0 hb0 hapos habound
      T hsource m sigma c l p)
    (surgeryCapCoordinates_mem_tube_source a b ha hb ha0 hb0 hapos habound
      T hsource m sigma c l q) hpq

/-- A smooth tube chart with smooth inverse preserves the injective
derivative of the cap coordinates at every native sphere point. -/
theorem surgeryCapMap_mfderiv_injective
    (hapos : ∀ z, 0 < a z)
    (habound : ∀ z, |z| < 1 → a z ≤ (Real.sqrt (1 - z ^ 2))⁻¹)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall 0 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source) (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (m sigma c l : ℝ) (hsigma : sigma ≠ 0) (hl : l ≠ 0) (q : UnitTwoSphere) :
    Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3)
      (surgeryCapMap a b ha hb ha0 hb0 T m sigma c l) q) := by
  let f := surgeryCapCoordinates a b ha hb ha0 hb0 m sigma c l
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, E2 × ℝ) ∞ f :=
    surgeryCapCoordinates_contMDiff a b ha hb ha0 hb0 m sigma c l
  have hq : f q ∈ T.source :=
    surgeryCapCoordinates_mem_tube_source a b ha hb ha0 hb0 hapos habound
      T hsource m sigma c l q
  have hTd : T.MDifferentiable 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E3) :=
    ⟨hT.contMDiffOn.mdifferentiableOn (by simp),
      hTi.contMDiffOn.mdifferentiableOn (by simp)⟩
  change Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) (T ∘ f) q)
  rw [mfderiv_comp q (hTd.mdifferentiableAt hq) (hf.mdifferentiable (by simp) q)]
  exact (hTd.mfderiv_injective hq).comp
    (surgeryCapCoordinates_mfderiv_injective a b ha hb ha0 hb0 m sigma c l hsigma hl q)

end PoincareMT.M25.Topology3D
