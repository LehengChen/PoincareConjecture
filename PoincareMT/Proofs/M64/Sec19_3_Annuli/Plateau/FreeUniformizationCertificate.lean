import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.FreeUniformizationEnergy

/-!
# Certificate for free annular uniformization

The lower annular API proves fixed-modulus weak compactness and the weighted
Gram/area identity, but it does not construct a positive modulus together with
free monotone degree-one boundary lifts.  This file records that missing
Douglas--Morrey output with the exact quantifiers of
`M64FreeConformalModulusApproximation`.  No existence theorem is asserted.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareMT

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- One free-boundary epsilon-uniformization candidate. The boundary lifts are literal data
in the annulus type, and the a.e. Gram relations identify its weighted energy with area.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
structure M64FreeMorreyUniformizationCandidate
    (g : RiemannianMetric n M) (c0 c1 : ℝ → M)
    (A : M64Annulus g c0 c1) (ε : ℝ) where
  modulus : ℝ
  modulus_pos : 0 < modulus
  sigma0 : M64PeriodicDegreeOneLift
  sigma1 : M64PeriodicDegreeOneLift
  annulus : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map)
  weighted_integrable : IntegrableOn (fun p =>
    (modulus * m60AreaGram g annulus.map p 0 0 +
      modulus⁻¹ * m60AreaGram g annulus.map p 1 1) / 2)
    m64AnnulusDomain volume
  ae_modulus_conformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
    modulus * m60AreaGram g annulus.map p 0 0 =
        modulus⁻¹ * m60AreaGram g annulus.map p 1 1 ∧
      m60AreaGram g annulus.map p 0 1 = 0
  energy_le : m64ClassicalWeightedGramEnergy g annulus modulus ≤ A.area + ε

/-- The supplied candidate's actual weighted Gram energy equals its annulus area. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem M64FreeMorreyUniformizationCandidate.weightedEnergy_eq_area
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    {A : M64Annulus g c0 c1} {ε : ℝ}
    (C : M64FreeMorreyUniformizationCandidate g c0 c1 A ε) :
    m64ClassicalWeightedGramEnergy g C.annulus C.modulus = C.annulus.area := by
  exact m64_weightedEnergy_eq_area_of_ae_modulus_conformal C.annulus
    C.modulus_pos C.ae_modulus_conformal

/-- The free Douglas--Morrey supplier, with all seed and epsilon quantifiers exposed. This
is a producer interface rather than an existence claim. Proof expansion for Morgan-Tian
(2007), Lemma 19.15, pp. 447-449. -/
structure M64FreeMorreyUniformizationCertificate
    (g : RiemannianMetric n M) (c0 c1 : ℝ → M) where
  candidate : ∀ A : M64Annulus g c0 c1, ∀ ε : ℝ, 0 < ε →
    M64FreeMorreyUniformizationCandidate g c0 c1 A ε

/-- Any genuine free uniformization certificate supplies the public free conformal-modulus
approximation predicate. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64FreeConformalModulusApproximation_of_morrey_certificate
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (C : M64FreeMorreyUniformizationCertificate g c0 c1) :
    M64FreeConformalModulusApproximation g c0 c1 := by
  intro A ε hε
  let W := C.candidate A ε hε
  exact ⟨W.modulus, W.modulus_pos, W.sigma0, W.sigma1, W.annulus,
    W.weighted_integrable, W.energy_le⟩

end PoincareMT
