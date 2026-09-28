import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.ModulusConfinementInterval

/-!
# Assemble the explicit compact modulus interval

This theorem only composes the two conditional arithmetic producers.  It
returns the positive interval and the guarded confinement premise needed by
the compact-modulus minimizer; no approximation or lower-bound geometry is
constructed here.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareMT

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "S" => m64AnnulusDomain

/-- Assemble a positive nonempty modulus interval from explicitly supplied approximation and
two opposite energy lower bounds. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp.
447-449. -/
theorem m64WeightedModulusConfinement_exists_of_approximation_and_bounds
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A0 : M64Annulus g c0 c1)
    (hconf : M64ConformalModulusApproximation g c0 c1)
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hlower : ∀ (r : ℝ), 0 < r → ∀ A : M64Annulus g c0 c1,
      IntegrableOn (fun p => (r * m60AreaGram g A.map p 0 0 +
        r⁻¹ * m60AreaGram g A.map p 1 1) / 2) S volume →
      alpha * r ≤ m64ClassicalWeightedGramEnergy g A r ∧
        beta * r⁻¹ ≤ m64ClassicalWeightedGramEnergy g A r) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧
      M64WeightedModulusConfinement g c0 c1 lo hi := by
  have hleast : 0 ≤ m64LeastAnnulusArea g c0 c1 :=
    m64LeastAnnulusArea_nonneg A0
  have hlevel : 0 < m64LeastAnnulusArea g c0 c1 + 1 := by
    linarith
  let lo := beta / (m64LeastAnnulusArea g c0 c1 + 1)
  let hi := (m64LeastAnnulusArea g c0 c1 + 1) / alpha
  refine ⟨lo, hi, ?_, ?_, ?_⟩
  · dsimp [lo]
    exact div_pos hbeta hlevel
  · dsimp [lo, hi]
    exact m64WeightedModulusConfinement_interval_nonempty_of_approximation
      A0 hconf halpha hbeta hlower
  · dsimp [lo, hi]
    exact m64WeightedModulusConfinement_of_two_sided_lower_bounds
      A0 halpha hbeta hlower

end PoincareMT
