import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.FreeUniformizationEnergy

/-!
# Rigidity of the annular area-energy inequality

At every positive cylinder modulus, equality in the integrated area-energy
comparison forces equality of the two weighted Gram diagonals and vanishing
of the mixed entry almost everywhere. This supplies conformality after the
weak minimum has been admitted; conformality is not an input to this result.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Pointwise equality of area and positive-modulus energy forces balanced weighted Gram
diagonals and zero mixed entry. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary
19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m60AreaGram_modulus_conformal_of_density_eq
    (g : RiemannianMetric n M) (f : LoopPlane → M) (p : LoopPlane)
    {r : ℝ} (hr : 0 < r)
    (heq : m60AreaDensity g f p =
      (r * m60AreaGram g f p 0 0 + r⁻¹ * m60AreaGram g f p 1 1) / 2) :
    r * m60AreaGram g f p 0 0 = r⁻¹ * m60AreaGram g f p 1 1 ∧
      m60AreaGram g f p 0 1 = 0 := by
  let x := r * m60AreaGram g f p 0 0
  let y := r⁻¹ * m60AreaGram g f p 1 1
  let z := m60AreaGram g f p 0 1
  have hprod : x * y = m60AreaGram g f p 0 0 * m60AreaGram g f p 1 1 := by
    dsimp only [x, y]
    calc
      _ = (r * r⁻¹) * (m60AreaGram g f p 0 0 * m60AreaGram g f p 1 1) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hr.ne', one_mul]
  have hsquare : (m60AreaDensity g f p) ^ 2 = x * y - z ^ 2 := by
    unfold m60AreaDensity
    rw [max_eq_right (m60AreaGram_det_nonneg g f p),
      Real.sq_sqrt (m60AreaGram_det_nonneg g f p), Matrix.det_fin_two,
      m60AreaGram_symm g f p 1 0, ← hprod]
    dsimp only [z]
    ring
  have hsum : (x - y) ^ 2 + 4 * z ^ 2 = 0 := by
    change m60AreaDensity g f p = (x + y) / 2 at heq
    rw [heq] at hsquare
    nlinarith [hsquare]
  have hxy : x - y = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg z])
  have hz : z = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (x - y)])
  exact ⟨sub_eq_zero.mp hxy, hz⟩

/-- Equality of actual integrated area and weighted energy forces modulus conformality
almost everywhere. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp.
447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem M64Annulus.ae_modulus_conformal_of_weightedEnergy_eq_area
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hE : IntegrableOn (fun p =>
      (r * m60AreaGram g A.map p 0 0 + r⁻¹ * m60AreaGram g A.map p 1 1) / 2)
        m64AnnulusDomain volume)
    (heq : m64ClassicalWeightedGramEnergy g A r = A.area) :
    ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0 := by
  have hae : (fun p => m60AreaDensity g A.map p) =ᵐ[volume.restrict m64AnnulusDomain]
      (fun p =>
        (r * m60AreaGram g A.map p 0 0 + r⁻¹ * m60AreaGram g A.map p 1 1) / 2) :=
    (integral_eq_iff_of_ae_le A.area_integrable hE
      (Eventually.of_forall fun p => m60AreaDensity_le_weightedGram g A.map p hr)).mp
        heq.symm
  filter_upwards [hae] with p hp
  exact m60AreaGram_modulus_conformal_of_density_eq g A.map p hr hp

end PoincareMT
