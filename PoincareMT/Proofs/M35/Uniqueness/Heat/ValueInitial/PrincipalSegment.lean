import PoincareMT.Proofs.M35.Uniqueness.Heat.ValueInitial.PrincipalInitial

/-!
# An actual compact vector heat segment

Morgan-Tian Section 12.5, p. 304; derivations/15. Retain both the tested
time derivative and its genuine integral identity when joining segments.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareMT.M35.Uniqueness.Heat.ValueInitial

open SpectralHeatNative

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

def PrincipalValueHeat (K : Set V) (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    (L : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K)) (r T : ℝ)
    (u₀ : PiLp 2 (fun _ : Fin m => dirichletValue K))
    (v : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K))
    (U : ℝ → PiLp 2 (fun _ : Fin m => dirichletValue K)) : Prop :=
  MemLp v 2 (timeMeasure T) ∧ U 0 = u₀ ∧ ContinuousOn U (Icc 0 T) ∧
    (∀ᵐ t ∂timeMeasure T, finiteHilbertMap (dirichletInclusion K) (v t) = U t) ∧
    (∀ᵐ t ∂timeMeasure T, ∀ w : PiLp 2 (fun _ : Fin m => dirichletForm K),
      HasDerivWithinAt (fun s => inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (U s))
        (inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (L (r + t) (v t)) -
          principalVectorEnergy K (A (r + t)) w (v t)) (Icc 0 T) t) ∧
    (∀ t ∈ Icc 0 T, ∀ w : PiLp 2 (fun _ : Fin m => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (U t) =
        inner ℝ (finiteHilbertMap (dirichletInclusion K) w) u₀ +
        ∫ s in (0 : ℝ)..t, inner ℝ (finiteHilbertMap (dirichletInclusion K) w)
          (L (r + s) (v s)) - principalVectorEnergy K (A (r + s)) w (v s))

end PoincareMT.M35.Uniqueness.Heat.ValueInitial
