import PoincareMT.Proofs.M35.Uniqueness.Heat.FiniteHilbertEquiv
import PoincareMT.Proofs.M35.Uniqueness.Heat.PrincipalFormOperator

/-!
# The literal vector principal-energy operator

Morgan-Tian, Section 12.5, p. 304: inverse metric diffusion acts on each
vector component. The finite Hilbert lift is linear and continuous in
the actual scalar coefficient operator, and its pairing is the sum of
the actual scalar Dirichlet energies.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap

namespace PoincareMT.M35.Uniqueness.Heat

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {m : ℕ}

def finiteHilbertMapLinear : (E →L[ℝ] F) →ₗ[ℝ]
    (PiLp 2 (fun _ : Fin m => E) →L[ℝ] PiLp 2 (fun _ : Fin m => F)) where
  toFun := finiteHilbertMap
  map_add' := by intro A B; ext u i; rfl
  map_smul' := by intro c A; ext u i; rfl

def finiteHilbertMapOperator : (E →L[ℝ] F) →L[ℝ]
    (PiLp 2 (fun _ : Fin m => E) →L[ℝ] PiLp 2 (fun _ : Fin m => F)) :=
  (finiteHilbertMapLinear (E := E) (F := F)).mkContinuous 1
    (fun A => by
      change ‖finiteHilbertMap (m := m) A‖ ≤ 1 * ‖A‖
      simpa only [one_mul] using norm_finiteHilbertMap_le (m := m) A)

@[simp] theorem finiteHilbertMapOperator_apply (A : E →L[ℝ] F) :
    finiteHilbertMapOperator (m := m) A = finiteHilbertMap A := rfl

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

def principalVectorEnergy (K : Set V) (A : Fin n → Fin n → 𝓢(V, ℝ))
    (u v : PiLp 2 (fun _ : Fin m => dirichletForm K)) : ℝ :=
  ∑ i, principalEnergy K A (u i) (v i)

theorem principalVectorEnergy_pairing (K : Set V)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (u v : PiLp 2 (fun _ : Fin m => dirichletForm K)) :
    inner ℝ u (finiteHilbertMap (principalFormOperator K A) v) =
      principalVectorEnergy K A u v := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun i _ => principalFormOperator_pairing K A (u i) (v i))

end PoincareMT.M35.Uniqueness.Heat
