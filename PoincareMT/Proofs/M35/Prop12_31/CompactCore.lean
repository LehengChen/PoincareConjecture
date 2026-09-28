import PoincareMT.Proofs.M35.Prop12_31.ScalarPositivity
import PoincareMT.Statements.Ch04.CurvatureTheory
import Mathlib.Topology.Order.Compact

/-!
# A uniform scalar floor on the compact early core

Morgan-Tian, Proposition 12.31, printed pp. 325-326, with the explicit
compact spacetime minimum required by the corrected scalar-rate argument.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.RepairedStandardCapExistenceData

/-- Proposition 12.31, pp. 325-326: one positive constant controls every point of a
compact core at every time of a fixed closed preterminal strip. -/
theorem exists_scalar_floor_on_compact
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {T : ℝ} (hT : T ∈ Ico 0 E.flow.base.lifetime)
    {K : Set StandardCapSpace} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc 0 T, ∀ x ∈ K,
      B ≤ (E.flow.connection t).scalarCurvature x := by
  have hsub : Icc 0 T ×ˢ K ⊆ Ico 0 E.flow.base.lifetime ×ˢ univ :=
    fun _ hp => ⟨⟨hp.1.1, hp.1.2.trans_lt hT.2⟩, mem_univ _⟩
  have hcont : ContinuousOn
      (fun p : ℝ × StandardCapSpace => (E.flow.connection p.1).scalarCurvature p.2)
      (Icc 0 T ×ˢ K) :=
    (P.scalar_regular 3 StandardCapSpace _ E.flow.base.flow).continuousOn.mono hsub
  obtain ⟨B, hB, hbound⟩ := (isCompact_Icc.prod hK).exists_forall_le' hcont
    (fun p hp => E.scalar_pos ⟨hp.1.1, hp.1.2.trans_lt hT.2⟩ p.2)
  exact ⟨B, hB, fun t ht x hx => hbound (t, x) ⟨ht, hx⟩⟩

/-- Proposition 12.31, pp. 325-326: the compact-core minimum combines with a uniform
exterior floor to control an entire closed preterminal spacetime strip. -/
theorem exists_scalar_floor_of_exterior_bound
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {T : ℝ} (hT : T ∈ Ico 0 E.flow.base.lifetime)
    {K : Set StandardCapSpace} (hK : IsCompact K) {B : ℝ} (hB : 0 < B)
    (hext : ∀ t ∈ Icc 0 T, ∀ x : StandardCapSpace, x ∉ K →
      B ≤ (E.flow.connection t).scalarCurvature x) :
    ∃ b : ℝ, 0 < b ∧ ∀ t ∈ Icc 0 T, ∀ x : StandardCapSpace,
      b ≤ (E.flow.connection t).scalarCurvature x := by
  obtain ⟨b, hb, hcore⟩ := E.exists_scalar_floor_on_compact P hT hK
  refine ⟨min b B, lt_min hb hB, ?_⟩
  intro t ht x
  by_cases hx : x ∈ K
  · exact (min_le_left b B).trans (hcore t ht x hx)
  · exact (min_le_right b B).trans (hext t ht x hx)

end PoincareMT.RepairedStandardCapExistenceData
