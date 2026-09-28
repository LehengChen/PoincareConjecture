import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.UnrestrictedLabels

/-!
# The classical energy infimum with unrestricted degree-one labels

Every unrestricted classical candidate restores to the literal boundary
class by actual zero-area collars. The existing monotone epsilon supplier
provides the reverse infimum inequality. This enlargement changes no
frozen contract and asserts neither a weak minimizer nor its regularity.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareMT.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "S" => m64AnnulusDomain

/-- The genuine integrable classical weighted energy range with unrestricted Lipschitz
degree-one labels. Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-25-free-label-compactness.md`. -/
def unrestrictedFreeClassicalEnergyRange
    (g : RiemannianMetric n M) (c0 c1 : ℝ → M) : Set ℝ :=
  {x | ∃ r : ℝ, 0 < r ∧ ∃ sigma0 sigma1 : LipschitzDegreeOneLabel,
    ∃ A : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map),
      IntegrableOn (fun p => (r * m60AreaGram g A.map p 0 0 +
        r⁻¹ * m60AreaGram g A.map p 1 1) / 2) S volume ∧
      x = m64ClassicalWeightedGramEnergy g A r}

/-- The monotone free energy range lies in the unrestricted classical range. Source:
Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation `2026-09-25-free-label-compactness.md`. -/
theorem free_energy_range_subset_unrestricted
    (g : RiemannianMetric n M) (c0 c1 : ℝ → M) :
    m64FreeClassicalWeightedGramEnergyRange g c0 c1 ⊆
      unrestrictedFreeClassicalEnergyRange g c0 c1 := by
  rintro x ⟨r, hr, sigma0, sigma1, A, hA, hx⟩
  exact ⟨r, hr, .ofMonotone sigma0, .ofMonotone sigma1, A, hA, hx⟩

/-- The actual unrestricted classical energy range is bounded below by zero. Source:
Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation `2026-09-25-free-label-compactness.md`. -/
theorem unrestricted_energy_range_bddBelow
    (g : RiemannianMetric n M) (c0 c1 : ℝ → M) :
    BddBelow (unrestrictedFreeClassicalEnergyRange g c0 c1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨r, hr, sigma0, sigma1, A, hA, rfl⟩
  unfold m64ClassicalWeightedGramEnergy
  apply integral_nonneg
  intro p
  exact div_nonneg (add_nonneg
    (mul_nonneg hr.le (m60AreaGram_diagonal_nonneg g A.map p 0))
    (mul_nonneg (inv_nonneg.mpr hr.le) (m60AreaGram_diagonal_nonneg g A.map p 1)))
    (by norm_num)

variable [T2Space M] (g : RiemannianMetric n M) {c0 c1 : ℝ → M}
  (hc0 : Continuous c0) (hp0 : Function.Periodic c0 curvePeriod)
  (hL0 : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y,
    g.edist (c0 x) (c0 y) ≤ ENNReal.ofReal L * ENNReal.ofReal |x - y|)
  (hc1 : Continuous c1) (hp1 : Function.Periodic c1 curvePeriod)
  (hL1 : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y,
    g.edist (c1 x) (c1 y) ≤ ENNReal.ofReal L * ENNReal.ofReal |x - y|)

include hc0 hp0 hL0 hc1 hp1 hL1

/-- Literal zero-area collars bound least annulus area by each unrestricted weighted energy.
Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-25-free-label-compactness.md`. -/
theorem least_area_le_unrestricted_weightedEnergy
    (sigma0 sigma1 : LipschitzDegreeOneLabel)
    (A : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map))
    {r : ℝ} (hr : 0 < r)
    (hA : IntegrableOn (fun p => (r * m60AreaGram g A.map p 0 0 +
      r⁻¹ * m60AreaGram g A.map p 1 1) / 2) S volume) :
    m64LeastAnnulusArea g c0 c1 ≤ m64ClassicalWeightedGramEnergy g A r := by
  obtain ⟨B, hB⟩ := unrestricted_label_area_transport g hc0 hp0 hL0 hc1 hp1 hL1
    sigma0 sigma1 A
  calc
    m64LeastAnnulusArea g c0 c1 ≤ B.area := m64LeastAnnulusArea_le_annulus B
    _ = A.area := hB
    _ ≤ m64ClassicalWeightedGramEnergy g A r := A.area_le_weightedGramEnergy hr hA

/-- An actual free conformal approximation identifies the unrestricted energy infimum with
least annulus area. Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-25-free-label-compactness.md`. -/
theorem least_area_eq_unrestricted_energy_sInf
    (A0 : M64Annulus g c0 c1)
    (hconf : M64FreeConformalModulusApproximation g c0 c1) :
    m64LeastAnnulusArea g c0 c1 =
      sInf (unrestrictedFreeClassicalEnergyRange g c0 c1) := by
  have hbelow := unrestricted_energy_range_bddBelow g c0 c1
  have hne : (unrestrictedFreeClassicalEnergyRange g c0 c1).Nonempty := by
    obtain ⟨r, hr, sigma0, sigma1, A, hA, -⟩ := hconf A0 1 one_pos
    exact ⟨_, free_energy_range_subset_unrestricted g c0 c1
      ⟨r, hr, sigma0, sigma1, A, hA, rfl⟩⟩
  apply le_antisymm
  · apply le_csInf hne
    rintro _ ⟨r, hr, sigma0, sigma1, A, hA, rfl⟩
    exact least_area_le_unrestricted_weightedEnergy g hc0 hp0 hL0 hc1 hp1 hL1
      sigma0 sigma1 A hr hA
  · apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    obtain ⟨A, hA⟩ := m64LeastAnnulusArea_near_minimizer A0 (half_pos hepsilon)
    obtain ⟨r, hr, sigma0, sigma1, B, hB, henergy⟩ :=
      hconf A (epsilon / 2) (half_pos hepsilon)
    have hle := csInf_le hbelow (free_energy_range_subset_unrestricted g c0 c1
      ⟨r, hr, sigma0, sigma1, B, hB, rfl⟩)
    linarith

end PoincareMT.M64
