import PoincareMT.Proofs.M35.Uniqueness.Heat.LocalizedDivergence

/-!
# Quantitative interior second derivatives of the actual compact field

Morgan-Tian, Section 12.5, p. 304: the literal cutoff equation and
actual graph first derivatives instantiate the lower difference
quotient theorem. The cutoff's thickened support must stay in an
elliptic region; no boundary regularity is asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Metric
open scoped SchwartzMap

namespace PoincareMT.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem exists_localized_dirichlet_secondDerivatives (K : Set V)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (η : 𝓢(V, ℝ))
    (hη : HasCompactSupport η) (hηK : tsupport η ⊆ K)
    (u : dirichletForm K) (G : L2)
    (heq : ∀ φ : supportedTests K, principalEnergy K A u (intoDirichletForm K φ) =
      inner ℝ G ((φ : 𝓢(V, ℝ)).toLp 2 volume))
    {r ell B : ℝ} (hr : 0 < r) (hEll : 0 < ell) (hB : 0 ≤ B)
    (hell : ∀ x ∈ cthickening (3 * r) (tsupport η), ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (hAB : ∀ i j x, ‖fderiv ℝ (A i j) x‖ ≤ B) :
    ∃ W : Fin n → Fin n → L2, ∀ i k,
      ‖W i k‖ ≤ (‖localizedDivergenceSource K A η u G‖ +
        (n : ℝ) * B * (∑ j, ‖localizedDirichletPartial K η u j‖)) / ell ∧
      HasWeakSchwartzDerivative (localizedDirichletPartial K η u i)
        (W i k) (EuclideanSpace.single k (1 : ℝ)) :=
  exists_secondDerivatives_of_weak_first (localizedDirichletValue K η u)
    (localizedDirichletPartial K η u) (localizedDirichletPartial_weak K η u)
    hη (localizedDirichletValue_ae_support K η u) A hr hEll hB hell hAB
    (localizedDivergenceSource K A η u G)
    (fun φ _ _ => localized_dirichlet_divergence K A η hηK u G heq φ)

end PoincareMT.M35.Uniqueness.Heat
