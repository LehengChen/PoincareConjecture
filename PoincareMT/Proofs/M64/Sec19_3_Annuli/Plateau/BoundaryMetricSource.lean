import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryRaisedSourceIntegrable
import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeightedSource

/-!
# The literal variational source supplies the raised-source data

The metric derivative applied twice to the actual weak columns is L1
and has quadratic growth. Its raised source therefore has the analytic
properties required by the mixed boundary C1 theorem, with no separate
source estimate assumed. Source: MT Lemma 19.15, pp. 447-449; Lemaire
1982, p. 102; M64 raised-source derivation.
-/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff ENNReal

namespace PoincareMT

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64BoundaryMetricSource_bilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64BoundaryMetricSource_bilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance m64BoundaryMetricSource_trilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64BoundaryMetricSource_trilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The actual metric-variation source is bounded by the original quadratic column energy.
Source: MT Lemma 19.15 coordinate variation; the M64 raised-source derivation. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis. Project derivation:
`proof-work/tasks/M64/derivations/2026-09-26-raised-boundary-source.md`. -/
theorem m64WeightedMetricSource_bound (w : Fin 2 → ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (V : Fin 2 → E)
    {L Lambda : ℝ} (hLambda : 0 ≤ Lambda)
    (hD : ‖D‖ ≤ L) (hw : ∀ i, |w i| ≤ Lambda) (j : Fin n) :
    |m64WeightedQuadraticSource w D (V 0, V 1) (EuclideanSpace.single j 1)| ≤
      (Lambda * L / 2) * ∑ i : Fin 2, ‖V i‖ ^ 2 := by
  have hd (i : Fin 2) : |D (EuclideanSpace.single j 1) (V i) (V i)| ≤ L * ‖V i‖ ^ 2 := by
    simpa only [PiLp.norm_single, Real.norm_eq_abs, abs_one, mul_one, pow_two, mul_assoc] using
      m64Trilinear_mixed_norm_bound D hD (EuclideanSpace.single j 1) (V i) (V i)
  have hh (i : Fin 2) : |w i * D (EuclideanSpace.single j 1) (V i) (V i)| ≤
      Lambda * L * ‖V i‖ ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul (hw i) (hd i) (abs_nonneg _) hLambda).trans_eq (by ring)
  change |(-1 / 2 : ℝ) * (w 0 * D (EuclideanSpace.single j 1) (V 0) (V 0) +
    w 1 * D (EuclideanSpace.single j 1) (V 1) (V 1))| ≤ _
  rw [abs_mul, Fin.sum_univ_two]
  norm_num only [abs_div, abs_neg, abs_one]
  have hs := (abs_add_le _ _).trans (add_le_add (hh 0) (hh 1))
  nlinarith

/-- A compact coordinate range and L2 columns give integrability of the literal
metric-variation source. Source: the raised-source derivation. Source: Morgan--Tian (2007),
Lemma 19.15, pp. 447-449; local boundary analysis. Project derivation:
`proof-work/tasks/M64/derivations/2026-09-26-raised-boundary-source.md`. -/
theorem m64WeightedMetricSource_integrable
    {S : Set LoopPlane} (hS : MeasurableSet S) {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} (hG : ContDiffOn ℝ ∞ G U)
    (w : Fin 2 → ℝ) {u : LoopPlane → E} (hu : ContinuousOn u S) (hmap : MapsTo u S K)
    {V : Fin 2 → LoopPlane → E} (hV : ∀ i, MemLp (V i) 2 (volume.restrict S)) :
    ∀ j, IntegrableOn (fun p => m64WeightedQuadraticSource w (fderiv ℝ G (u p))
      (V 0 p, V 1 p) (EuclideanSpace.single j 1)) S := by
  have hD := (hG.continuousOn_fderiv_of_isOpen hU (by simp)).mono hKU
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn hD
  have hDM : MemLp (fun p => fderiv ℝ G (u p)) ⊤ (volume.restrict S) :=
    memLp_top_of_bound ((hD.comp hu hmap).aestronglyMeasurable hS) L (by
      filter_upwards [ae_restrict_mem hS] with p hp
      exact hL (u p) (hmap hp))
  intro j
  have hDG : MemLp (fun p => fderiv ℝ G (u p) (EuclideanSpace.single j 1)) ⊤
      (volume.restrict S) :=
    ((ContinuousLinearMap.apply ℝ (E →L[ℝ] E →L[ℝ] ℝ) («E» := E))
      (EuclideanSpace.single j 1)).comp_memLp' hDM
  have hquad (i : Fin 2) : IntegrableOn
      (fun p => fderiv ℝ G (u p) (EuclideanSpace.single j 1) (V i p) (V i p)) S := by
    have hfirst := (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) («E» := E)).memLp_of_bilin
      (p := 2) (q := ⊤) 2 (hV i) hDG
    exact memLp_one_iff_integrable.mp
      ((ContinuousLinearMap.apply ℝ ℝ («E» := E)).memLp_of_bilin
        (p := 2) (q := 2) 1 (hV i) hfirst)
  exact (((hquad 0).const_mul (w 0)).add ((hquad 1).const_mul (w 1))).const_mul (-1 / 2)

/-- The literal variational source, after inverse-metric testing, has
both L1 integrability and a common quadratic bound in the actual weak
columns. No source-growth assumption is retained. Source: MT Lemma 19.15,
pp. 447-449; Lemaire 1982, p. 102; raised-source derivation. -/
theorem m64BoundaryMetricRaisedSource_data
    {S : Set LoopPlane} (hS : MeasurableSet S) {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} (hG : ContDiffOn ℝ ∞ G U)
    (hpos : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v)
    (w : Fin 2 → ℝ) {u : LoopPlane → E} (hu : ContinuousOn u S) (hmap : MapsTo u S K)
    {V : Fin 2 → LoopPlane → E} (hV : ∀ i, MemLp (V i) 2 (volume.restrict S)) :
    let b := fun j p => m64WeightedQuadraticSource w (fderiv ℝ G (u p))
      (V 0 p, V 1 p) (EuclideanSpace.single j 1)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k,
      IntegrableOn (fun p => m64BoundaryRaisedSource G w (u p)
        (fun i => V i p) (fun j => b j p) k) S ∧
      ∀ᵐ p ∂volume.restrict S,
        |m64BoundaryRaisedSource G w (u p) (fun i => V i p) (fun j => b j p) k| ≤
          C * ∑ j : Fin n, ∑ i : Fin 2, (V i p j) ^ 2 := by
  let b := fun j p => m64WeightedQuadraticSource w (fderiv ℝ G (u p))
    (V 0 p, V 1 p) (EuclideanSpace.single j 1)
  have hb : ∀ j, IntegrableOn (b j) S :=
    m64WeightedMetricSource_integrable hS hU hK hKU hG w hu hmap hV
  obtain ⟨L, hL, hbound⟩ := m64BoundaryMetric_inverse_coefficient_bounds hU hK hKU hG hpos
  let Lambda := |w 0| + |w 1|
  have hLambda : 0 ≤ Lambda := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hw (i : Fin 2) : |w i| ≤ Lambda := by
    fin_cases i
    · exact le_add_of_nonneg_right (abs_nonneg (w 1))
    · exact le_add_of_nonneg_left (abs_nonneg (w 0))
  let Cb := Lambda * L / 2
  have hCb : 0 ≤ Cb := by dsimp only [Cb]; positivity
  let C := (n : ℝ) * L * (Cb + Lambda * L)
  refine ⟨C, by dsimp only [C]; positivity, fun k => ⟨?_, ?_⟩⟩
  · exact m64BoundaryRaisedSource_integrable hS hU hK hKU hG hpos w hu hmap hV hb k
  · filter_upwards [ae_restrict_mem hS] with p hp
    have hmetric := hbound (u p) (hmap hp)
    have hraw (j : Fin n) : |b j p| ≤ Cb * ∑ i : Fin 2, ‖V i p‖ ^ 2 :=
      m64WeightedMetricSource_bound w (fderiv ℝ G (u p)) (fun i => V i p)
        hLambda hmetric.2.1 hw j
    have hh := m64BoundaryRaisedSource_bound G w (u p) (fun i => V i p) (fun j => b j p) k
      hL.le hLambda hCb hmetric.1 hw (hmetric.2.2 k) hraw
    rw [show (∑ i : Fin 2, ‖V i p‖ ^ 2) = ∑ j : Fin n, ∑ i : Fin 2, (V i p j) ^ 2 by
      simp_rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.sum_comm] at hh
    exact hh

end PoincareMT
