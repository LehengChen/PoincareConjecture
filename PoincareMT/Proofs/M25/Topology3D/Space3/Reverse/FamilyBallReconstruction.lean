import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FamilySurgeryHistory
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReconstruction

/-!
# Backward ball reconstruction through an actual surgery history

The existing history fold and parent-ball construction preserve the
literal indexed collar boundaries. Source: Hatcher, Notes on Basic
3-Manifold Topology, Theorem 1.1 and Lemma 1.3, pp. 1-3; reviewed RH1
inventory and preproof of 2026-09-22.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareMT.M25.Topology3D

/-- Actual terminal balls reconstruct a ball for every original collar in the history. -/
theorem FamilySurgeryHistory.exists_initial_balls
    {u : UnitTwoSphere} {n m : ℕ}
    {psi : Fin n → UnitTwoSphere × ℝ → E3}
    {phi : Fin m → UnitTwoSphere × ℝ → E3}
    (history : FamilySurgeryHistory u psi phi)
    (hfinal : ∀ i : Fin m, ∃ B : BallNeighborhoodChart E3 E3,
      B.boundary = phi i '' (univ ×ˢ ({0} : Set ℝ))) :
    ∀ i : Fin n, ∃ B : BallNeighborhoodChart E3 E3,
      B.boundary = psi i '' (univ ×ˢ ({0} : Set ℝ)) := by
  let P (chi : UnitTwoSphere × ℝ → E3) : Prop :=
    ∃ B : BallNeighborhoodChart E3 E3,
      B.boundary = chi '' (univ ×ˢ ({0} : Set ℝ))
  have hstep : ∀ (parent : UnitTwoSphere × ℝ → E3)
      (E : RegularSurgeryEvent parent u),
      P (E.child 0) → P (E.child 1) → P parent := by
    intro parent E h0 h1
    obtain ⟨B0, h0⟩ := h0
    obtain ⟨B1, h1⟩ := h1
    let A : Fin 2 → BallNeighborhoodChart E3 E3 := ![B0, B1]
    have hboundary : ∀ k : Fin 2,
        (A k).boundary = E.child k '' (univ ×ˢ ({0} : Set ℝ)) := by
      intro k
      fin_cases k
      · exact h0
      · exact h1
    obtain ⟨B, hB, _⟩ := E.exists_parent_ball_of_children A hboundary
    exact ⟨B, hB⟩
  exact FamilySurgeryHistory.fold P hstep history hfinal

end PoincareMT.M25.Topology3D
