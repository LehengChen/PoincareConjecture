import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialReplacementEnergy
import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusReplacement

/-!
# Actual weighted replacement across the lower annular boundary

The fixed lower half of the disk contributes exactly the same weighted
energy to the old and new maps. Cancellation of the constructed upper-half
competitor therefore gives a full-disk comparison. Positive-modulus
ellipticity converts it to the unweighted comparison needed for Morrey growth.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold ContDiff

namespace PoincareMT

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusLowerDomain
local notation "L" => m64AnnulusLowerStrip

set_option maxHeartbeats 800000 in
-- Replacement, weighted cancellation, and ellipticity are elaborated together.
/-- An actual matching-flux replacement and weighted minimality bound the original lower
half-disk energy. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem M64ObservedWeakAnnulus.weighted_lower_local_energy_le_of_matching_flux
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hc0 : ContDiff ℝ 1 (e ∘ c0))
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hbound : ∀ q, ‖Q q‖ ≤ C) (hpos : ∀ q v, 0 ≤ Q q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus)
    (a : LoopPlane) (r : ℝ) (hKO : ball a r ⊆ O)
    (f : LoopPlane → M) (V : Fin 2 → LoopPlane → E)
    (hf : MemLp (e ∘ f) 2 (volume.restrict (ball a r)))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball a r)))
    (ht : ∀ i, ∀ᵐ p ∂volume.restrict (ball a r),
      V i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f p)))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun p => V i p b) (fun p => e (f p) b) (ball a r))
    (hfixed : ∀ p ∈ ball a r, p 1 < 0 → f p = c0 (p 0))
    (hgreen : ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi → ∀ i : Fin 2,
      (∫ p in ball a r, phi p • V i p) +
        (∫ p in ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (f p)) =
      (∫ p in ball a r, phi p • A.lowerExtensionColumn i p) +
        (∫ p in ball a r,
          fderiv ℝ phi p (EuclideanSpace.single i 1) • e (A.lowerExtensionMap p))) :
    (∫ p in ball a r,
      (Q (A.lowerExtensionMap p) (A.lowerExtensionColumn 0 p) (A.lowerExtensionColumn 0 p) +
        Q (A.lowerExtensionMap p) (A.lowerExtensionColumn 1 p) (A.lowerExtensionColumn 1 p)) / 2) ≤
      (max modulus modulus⁻¹) ^ 2 *
        ∫ p in ball a r, (Q (f p) (V 0 p) (V 0 p) + Q (f p) (V 1 p) (V 1 p)) / 2 := by
  classical
  let : TopologicalSpace.PseudoMetrizableSpace M := hei.isInducing.pseudoMetrizableSpace
  let K := ball a r
  let old := fun p =>
    (modulus * Q (A.lowerExtensionMap p) (A.lowerExtensionColumn 0 p) (A.lowerExtensionColumn 0 p) +
      modulus⁻¹ * Q (A.lowerExtensionMap p)
        (A.lowerExtensionColumn 1 p) (A.lowerExtensionColumn 1 p)) / 2
  let new := fun p =>
    (modulus * Q (f p) (V 0 p) (V 0 p) + modulus⁻¹ * Q (f p) (V 1 p) (V 1 p)) / 2
  have hfmeas : AEStronglyMeasurable f (volume.restrict K) :=
    hei.aestronglyMeasurable_comp_iff.mp hf.aestronglyMeasurable
  have hold := A.lower_extension_memLp hc0
  have holdmeas : AEStronglyMeasurable A.lowerExtensionMap (volume.restrict K) :=
    hei.aestronglyMeasurable_comp_iff.mp
      (hold.1.mono_measure (Measure.restrict_mono hKO le_rfl)).aestronglyMeasurable
  have holdcol (i : Fin 2) := m64VariableModulus_column_integrable Q hQ hbound
    A.lowerExtensionMap holdmeas (A.lowerExtensionColumn i)
    ((hold.2 i).mono_measure (Measure.restrict_mono hKO le_rfl))
  have hnewcol (i : Fin 2) :=
    m64VariableModulus_column_integrable Q hQ hbound f hfmeas (V i) (hV i)
  have holdint : IntegrableOn old K volume :=
    (((holdcol 0).const_mul modulus).add ((holdcol 1).const_mul modulus⁻¹)).div_const 2
  have hnewint : IntegrableOn new K volume :=
    (((hnewcol 0).const_mul modulus).add ((hnewcol 1).const_mul modulus⁻¹)).div_const 2
  obtain ⟨B, hmap, hcol⟩ := A.lower_replace hc0 a r hKO f V hf hV ht hw hfixed hgreen
  have hE := m64VariableModulus_replacement_energy Q hQ hei hbound modulus A B
    (measurableSet_ball.inter isOpen_interior.measurableSet) inter_subset_right f
    (hfmeas.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)) V
    (fun i => (hV i).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)) hmap hcol
  have hupperOld : (∫ p in K ∩ S, old p) =
      ∫ p in K ∩ S, (modulus * Q (A.map p) (A.column 0 p) (A.column 0 p) +
        modulus⁻¹ * Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem
      (measurableSet_ball.inter isOpen_interior.measurableSet)] with p hp
    simp only [old, M64ObservedWeakAnnulus.lowerExtensionMap,
      M64ObservedWeakAnnulus.lowerExtensionColumn, m64AnnulusLowerExtend_right _ _ hp.2]
  have hupper : (∫ p in K ∩ S, old p) ≤ ∫ p in K ∩ S, new p := by
    rw [hupperOld]
    have hm := hmin B
    dsimp only [new]
    linarith
  obtain ⟨hvalue, hcolumns⟩ := A.lower_fixed_columns hc0 a r hKO f V hV hw hfixed
  have hlower : (∫ p in K ∩ L, old p) = ∫ p in K ∩ L, new p := by
    apply integral_congr_ae
    filter_upwards [hvalue, hcolumns 0, hcolumns 1] with p hp h0 h1
    simp only [old, new, hp, h0, h1]
  have hweighted : (∫ p in K, old p) ≤ ∫ p in K, new p := by
    rw [m64AnnulusLower_integral_local measurableSet_ball hKO old holdint,
      m64AnnulusLower_integral_local measurableSet_ball hKO new hnewint, hlower]
    exact add_le_add hupper le_rfl
  have hD : 0 ≤ max modulus modulus⁻¹ := hmodulus.le.trans (le_max_left _ _)
  have hu := (m64VariableModulus_integral_comparison (holdcol 0) (holdcol 1)
    (Eventually.of_forall fun p => hpos (A.lowerExtensionMap p) (A.lowerExtensionColumn 0 p))
    (Eventually.of_forall fun p => hpos (A.lowerExtensionMap p) (A.lowerExtensionColumn 1 p))
    hmodulus).1
  have hv := (m64VariableModulus_integral_comparison (hnewcol 0) (hnewcol 1)
    (Eventually.of_forall fun p => hpos (f p) (V 0 p))
    (Eventually.of_forall fun p => hpos (f p) (V 1 p)) hmodulus).2
  exact (hu.trans (mul_le_mul_of_nonneg_left hweighted hD)).trans
    ((mul_le_mul_of_nonneg_left hv hD).trans_eq (by ring))

end PoincareMT
