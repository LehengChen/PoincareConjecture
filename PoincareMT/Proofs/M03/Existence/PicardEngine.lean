import Mathlib.Analysis.ODE.ExistUnique

/-!
# Local Picard engine on a Banach state space

The DeTurck coefficient construction reduces its time evolution to a
time-dependent vector field on a complete normed state space.  This native
bridge exposes the pinned Mathlib Picard--Lindelof theorem in the forward
interval convention used by the M03 work.  The coefficient-specific bounds
remain separate obligations; this file supplies the actual fixed-point step.
-/

set_option autoImplicit false

open scoped NNReal

namespace PoincareMT

theorem picard_solution_on_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {T : ℝ} {x₀ : E}
    (hT : 0 < T) {a r L K : ℝ≥0}
    (hf : IsPicardLindelof f ⟨0, le_rfl, hT.le⟩ x₀ a r L K) :
    ∃ α : ℝ → E, α 0 = x₀ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt α (f t (α t)) (Set.Icc (0 : ℝ) T) t := by
  exact IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt hf
    (Metric.mem_closedBall_self (by positivity))

theorem picard_solution_on_Ico
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {T : ℝ} {x₀ : E}
    (hT : 0 < T) {a r L K : ℝ≥0}
    (hf : IsPicardLindelof f ⟨0, le_rfl, hT.le⟩ x₀ a r L K) :
    ∃ α : ℝ → E, α 0 = x₀ ∧
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt α (f t (α t)) (Set.Ico (0 : ℝ) T) t := by
  obtain ⟨α, hα0, hα⟩ := picard_solution_on_Icc hT hf
  refine ⟨α, hα0, ?_⟩
  intro t ht
  exact (hα t ⟨ht.1, ht.2.le⟩).mono (fun s hs => ⟨hs.1, hs.2.le⟩)

end PoincareMT
