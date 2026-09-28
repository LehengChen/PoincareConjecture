import Mathlib.Analysis.ODE.ExistUnique

/-!
# Native local Picard bridge

This file isolates the ordinary local fixed-point step used by a quasilinear
construction.  It is deliberately independent of the Ricci-flow predicates:
the geometric work still has to provide the concrete Banach-space vector field
and its `IsPicardLindelof` bounds.  The result packages Mathlib's differential
Picard theorem in a small proposition that can be consumed by a later native
PoincareMT construction.
-/

set_option autoImplicit false

open Set
open scoped NNReal

namespace PoincareMT

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A differential solution on the closed interval used by the Picard theorem. -/
def IsPicardIntervalSolution
    (f : ℝ → E → E) (tmin tmax : ℝ) (t₀ : Icc tmin tmax) (x₀ : E)
    (α : ℝ → E) : Prop :=
  α t₀ = x₀ ∧
    ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t

/-- Mathlib's local Picard--Lindelof solution, in the native bridge predicate. -/
theorem exists_picardIntervalSolution
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E}
    {a L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ a 0 L K) :
    ∃ α : ℝ → E, IsPicardIntervalSolution f tmin tmax t₀ x₀ α := by
  obtain ⟨α, hα₀, hα⟩ :=
    IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ hf
  exact ⟨α, hα₀, hα⟩

end PoincareMT
