import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamRectangleFlux

/-!
# The literal periodized replacement map

A local patch and its positive translate are inserted into the fundamental
rectangle. When the patch and its translate are disjoint, the observed
map is the old map plus the two translated, zero-extended corrections.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareMT

local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusSeamDomain
local notation "v" => m64AnnulusSeamTranslation

/-- Insert a local competitor and its period translate into the fundamental annular
rectangle. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
def m64AnnulusSeamPatch {E : Type*} (K : Set LoopPlane)
    (f g : LoopPlane → E) (p : LoopPlane) : E := by
  classical
  exact if p ∈ K then f p else if p - v ∈ K then f (p - v) else g p

/-- Observation commutes with the literal two-piece annular seam patch. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusSeamPatch_comp {E F : Type*} (K : Set LoopPlane)
    (f g : LoopPlane → E) (h : E → F) :
    h ∘ m64AnnulusSeamPatch K f g = m64AnnulusSeamPatch K (h ∘ f) (h ∘ g) := by
  funext p
  simp only [m64AnnulusSeamPatch, Function.comp_def]
  split_ifs <;> rfl

/-- A separated seam patch equals the old map plus its two translated indicator corrections.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusSeamPatch_eq_add
    {E : Type*} [AddCommGroup E] {K : Set LoopPlane}
    (hsep : Disjoint K ((fun p : LoopPlane => p - v) ⁻¹' K))
    (f g : LoopPlane → E) {p : LoopPlane} (hp : p ∈ S) :
    m64AnnulusSeamPatch K f g p = g p +
      K.indicator (f - m64AnnulusSeamExtend g) p +
      K.indicator (f - m64AnnulusSeamExtend g) (p - v) := by
  classical
  by_cases hpK : p ∈ K
  · have hqK : p - v ∉ K := fun hq => disjoint_left.mp hsep hpK hq
    simp only [m64AnnulusSeamPatch, if_pos hpK, indicator_of_mem hpK,
      indicator_of_notMem hqK, Pi.sub_apply, m64AnnulusSeamExtend_right g hp, add_zero]
    abel
  · by_cases hqK : p - v ∈ K
    · simp only [m64AnnulusSeamPatch, if_neg hpK, if_pos hqK, indicator_of_notMem hpK,
        indicator_of_mem hqK, Pi.sub_apply, m64AnnulusSeamExtend_sub g hp, add_zero]
      abel
    · simp only [m64AnnulusSeamPatch, if_neg hpK, if_neg hqK, indicator_of_notMem hpK,
        indicator_of_notMem hqK, add_zero]

/-- Separated periodized patching preserves actual Lp integrability. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusSeamPatch_memLp
    {E : Type*} [NormedAddCommGroup E] {q : ENNReal} {K : Set LoopPlane}
    (hK : MeasurableSet K) (hKO : K ⊆ O)
    (hsep : Disjoint K ((fun p : LoopPlane => p - v) ⁻¹' K))
    {f g : LoopPlane → E}
    (hf : MemLp f q (volume.restrict K)) (hg : MemLp g q (volume.restrict S)) :
    MemLp (m64AnnulusSeamPatch K f g) q (volume.restrict S) := by
  let d := K.indicator (f - m64AnnulusSeamExtend g)
  have hd : MemLp d q volume := (memLp_indicator_iff_restrict hK).mpr
    (hf.sub ((m64AnnulusSeamExtend_memLp hg).mono_measure (Measure.restrict_mono hKO le_rfl)))
  have hdshift : MemLp (fun p => d (p - v)) q volume := by
    have h := hd.comp_measurePreserving
      (measurePreserving_add_right (volume : Measure LoopPlane) (-v))
    simpa only [sub_eq_add_neg, Function.comp_def] using h
  apply ((hg.add (hd.mono_measure Measure.restrict_le_self)).add
    (hdshift.mono_measure Measure.restrict_le_self)).ae_eq
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
  exact (m64AnnulusSeamPatch_eq_add hsep f g hp).symm

/-- A patch in the open centered period strip is disjoint from its period translate. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusSeam_disjoint_of_angular_width {K : Set LoopPlane}
    (hK : ∀ p ∈ K, -curvePeriod / 2 < p 0 ∧ p 0 < curvePeriod / 2) :
    Disjoint K ((fun p : LoopPlane => p - v) ⁻¹' K) := by
  apply disjoint_left.mpr
  intro p hp hq
  have h0 := (hK p hp).2
  have h1 := (hK (p - v) hq).1
  simp only [PiLp.sub_apply, m64AnnulusSeamTranslation, annulusPoint, Matrix.cons_val_zero] at h1
  linarith

end PoincareMT
