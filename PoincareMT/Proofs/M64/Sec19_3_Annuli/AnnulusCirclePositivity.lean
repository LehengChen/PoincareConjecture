import PoincareMT.Proofs.M64.Sec19_3_Annuli.CircleCurrentLaplacian
import PoincareMT.Proofs.M64.Sec19_3_Annuli.AnnulusCirclePeriodicity
import PoincareMT.Proofs.M64.Sec19_3_Annuli.PeriodicHarmonicTransport

/-!
# Positivity of the actual angular circle current

The actual harmonic equation from conformal area minimality extends
through the periodic seam. Nonnegative boundary current and a nonzero
value then give strict positivity throughout the open covering strip,
so the horizontal differential cannot vanish there. Boundary-current
conditions are supplied separately by the positive-degree ramp lifts.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory InnerProductSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

/-- The angular current of the actual conformal area minimum is harmonic on the full
covering strip, including every translated seam. Source: Morgan--Tian (2007), Lemma 19.15
and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64AnnulusCircleCurrent_harmonic_strip_of_conformal_minimum
    (P : M62.CircleProductData F circumference) (hcirc : 0 < circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t) c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram (P.flow.metric t) A.map p 0 0 = m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    (hA : ∀ p ∈ m64AnnulusDomain, ContMDiffAt (𝓡 2) (𝓡 (n + 1)) ∞ A.map p) :
    HarmonicOnNhd (m64AnnulusCircleCurrent P t A.map 0) m64AnnulusOpenStrip := by
  apply m64PeriodicScalar_harmonicOnNhd_strip
    (fun p hp => m64AnnulusCircleCurrent_contDiffAt P t (hA p hp) 0)
    (m64AnnulusCircleCurrent_periodic P t A 0)
  apply m64AnnulusCircleCurrent_horizontal_harmonic_of_conformal_minimum
    P hcirc t A hminimum hconformal
  intro p hp
  have hsub : m64AnnulusInterior ⊆ m64AnnulusDomain := by
    rw [← m64AnnulusInterior_closure]
    exact subset_closure
  exact (hA p (hsub hp)).contMDiffWithinAt

/-- Nonnegative, nontrivial boundary phase current of an actual conformal minimum gives a
strictly positive angular current everywhere inside. There is no assumed harmonicity or
interior sign. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449;
project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64AnnulusCircleCurrent_positive_of_boundary_nonneg
    (P : M62.CircleProductData F circumference) (hcirc : 0 < circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t) c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram (P.flow.metric t) A.map p 0 0 = m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    (hA : ∀ p ∈ m64AnnulusDomain, ContMDiffAt (𝓡 2) (𝓡 (n + 1)) ∞ A.map p)
    (hlower : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 ≤ m64AnnulusCircleCurrent P t A.map 0 (annulusPoint x 0))
    (hupper : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 ≤ m64AnnulusCircleCurrent P t A.map 0 (annulusPoint x 1))
    (hnonzero : ∃ p ∈ m64AnnulusDomain, m64AnnulusCircleCurrent P t A.map 0 p ≠ 0) :
    ∀ p ∈ m64AnnulusOpenStrip,
      0 < m64AnnulusCircleCurrent P t A.map 0 p := by
  exact m64PeriodicHarmonic_pos_of_boundary_nonneg
    (fun p hp =>
      (m64AnnulusCircleCurrent_contDiffAt P t (hA p hp) 0).continuousAt.continuousWithinAt)
    (m64AnnulusCircleCurrent_harmonic_strip_of_conformal_minimum P hcirc t A
      hminimum hconformal hA)
    (m64AnnulusCircleCurrent_periodic P t A 0) hlower hupper hnonzero

omit [T2Space M] [CompactSpace M] in
/-- Positive actual circle current excludes vanishing of the horizontal column, without
presupposing immersion of the annulus. Source: Morgan--Tian (2007), Lemma 19.15 and
Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64Annulus_horizontal_column_ne_zero_of_circleCurrent_pos
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {f : LoopPlane → P.charts.Point} {p : LoopPlane}
    (hpos : 0 < m64AnnulusCircleCurrent P t f 0 p) :
    mfderiv (𝓡 2) (𝓡 (n + 1)) f p (EuclideanSpace.single (0 : Fin 2) 1) ≠ 0 := by
  intro hzero
  simp only [m64AnnulusCircleCurrent, hzero, map_zero, zero_apply] at hpos
  exact lt_irrefl (0 : ℝ) hpos

end PoincareMT
