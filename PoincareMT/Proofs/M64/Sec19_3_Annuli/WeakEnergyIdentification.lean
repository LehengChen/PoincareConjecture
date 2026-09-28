import PoincareMT.Proofs.M64.Sec19_3_Annuli.DouglasMorreyPipeline

/-!
# Identifying the weak and classical annular energies

The direct-method record stores the weak coordinate columns before the limit
map is admitted.  Once a regularity producer identifies their pullback Gram
entries with the classical Gram entries, the two displayed energy densities
and their set integrals agree by a.e. congruence.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {f : LoopPlane → M}

/-- An actual weak Gram identification gives pointwise equality of weak and classical energy
densities. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449;
project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64WeakEnergyDensity_eq_classical_of_gram_eq
    (V : M64AnnulusWeakGradient g f)
    {p : LoopPlane}
    (hgram : ∀ i j : Fin 2,
      g.pullbackCoefficients
          (extChartAt (𝓡 n) V.chart_center).symm
          (V.coordinate p) (V.column i p) (V.column j p) =
        m60AreaGram g f p i j) :
    m64AnnulusWeakEnergyDensity g V p = m60EnergyDensity g f p := by
  unfold m64AnnulusWeakEnergyDensity m60EnergyDensity
  rw [Matrix.trace_fin_two]
  rw [Fin.sum_univ_two]
  rw [hgram 0 0, hgram 1 1]

/-- An almost-everywhere weak Gram identification gives equality of the corresponding actual
energy integrals. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449;
project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64WeakEnergy_integral_eq_classical_of_ae_gram_eq
    (V : M64AnnulusWeakGradient g f)
    {s : Set LoopPlane}
    (hgram : ∀ᵐ p ∂volume.restrict s, ∀ i j : Fin 2,
      g.pullbackCoefficients
          (extChartAt (𝓡 n) V.chart_center).symm
          (V.coordinate p) (V.column i p) (V.column j p) =
        m60AreaGram g f p i j) :
    (∫ p in s, m64AnnulusWeakEnergyDensity g V p) =
      ∫ p in s, m60EnergyDensity g f p := by
  apply integral_congr_ae
  filter_upwards [hgram] with p hp
  exact m64WeakEnergyDensity_eq_classical_of_gram_eq V hp

end PoincareMT
