import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryFaceZeroExtension

/-!
# Indicator coefficients in the face-zero equation

This is the exact coefficient shape consumed by the mixed tangential quotient
estimate: local chart flux and source data are restricted to the upper
half-ball, and the resulting equation is extended to smooth tests which only
vanish on the flat face.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace PoincareMT

/-- The literal upper-neighborhood indicator coefficients satisfy the full face-zero test
identity. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis.
Project derivation: `proof-work/tasks/M64/reports/2026-09-25-boundary-zero-tests.md`. -/
theorem m64NaturalGrowth_indicator_face_zero_test
    {O : Set LoopPlane} (hO : IsOpen O)
    {flux : Fin 2 → LoopPlane → ℝ} {source : LoopPlane → ℝ}
    (hflux : ∀ i, MemLp (flux i) 2 (volume.restrict O))
    (hsource : IntegrableOn source O)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ O)
    (hzero : ∀ p : LoopPlane, p 1 = 0 → phi p = 0)
    (hscalar : ∀ psi : LoopPlane → ℝ, ContDiff ℝ ∞ psi →
      HasCompactSupport psi →
      tsupport psi ⊆ O ∩ {p : LoopPlane | 0 < p 1} →
      (∫ p, ∑ i : Fin 2, (O ∩ {p : LoopPlane | 0 < p 1}).indicator
        (flux i) p * fderiv ℝ psi p (EuclideanSpace.single i 1)) =
        ∫ p, (O ∩ {p : LoopPlane | 0 < p 1}).indicator source p * psi p) :
    (∫ p, ∑ i : Fin 2, (O ∩ {p : LoopPlane | 0 < p 1}).indicator
      (flux i) p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
      ∫ p, (O ∩ {p : LoopPlane | 0 < p 1}).indicator source p * phi p := by
  let H : Set LoopPlane := {p : LoopPlane | 0 < p 1}
  let S : Set LoopPlane := O ∩ H
  have hH : IsOpen H := isOpen_lt continuous_const
    (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous
  have hS : MeasurableSet S := hO.measurableSet.inter hH.measurableSet
  have hF : ∀ i, MemLp (S.indicator (flux i)) 2 volume := by
    intro i
    apply (memLp_indicator_iff_restrict hS).mpr
    exact (hflux i).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have hB : Integrable (S.indicator source) := by
    apply (integrable_indicator_iff hS).mpr
    exact hsource.mono_set inter_subset_left
  have hFzero : ∀ i p, p 1 ≤ 0 → S.indicator (flux i) p = 0 := by
    intro i p hp0
    have hnot : p ∉ S := by
      intro hpS
      exact (not_lt_of_ge hp0) hpS.2
    simp only [indicator_of_notMem hnot]
  have hBzero : ∀ p, p 1 ≤ 0 → S.indicator source p = 0 := by
    intro p hp0
    have hnot : p ∉ S := by
      intro hpS
      exact (not_lt_of_ge hp0) hpS.2
    simp only [indicator_of_notMem hnot]
  have hbridge := m64NaturalGrowth_face_zero_extension_test
    (O := O) hO hF hB hp hc hs hzero hFzero hBzero (by
      intro psi hpsi hpsic hpsis
      exact hscalar psi hpsi hpsic (by simpa only [S, H] using hpsis))
  simpa only [S, H] using hbridge

end PoincareMT
