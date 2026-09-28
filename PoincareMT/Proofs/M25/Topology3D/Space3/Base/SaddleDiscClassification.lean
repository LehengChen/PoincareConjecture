import PoincareMT.Proofs.M25.Topology3D.Space3.BallNeighborhoodNesting
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.SaddleLowerLevelSelection

/-!
# The actual nested or nonnested saddle picture

The lead's proved disc trichotomy and witness-preserving case decision
combine with S4 independently of either saddle-ball leaf. Source: Hatcher,
Lemma 1.2 and Figure 1.2, pp. 2-3; disc-classification extraction, 2026-09-23.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareMT.M25.Topology3D

/-- Disjoint boundaries of two supplied planar ball charts give the three
region relations. Hatcher, Lemma 1.2, pp. 2-3; the lead's Alexander skeleton. -/
theorem BallNeighborhoodChart.planar_closedRegion_trichotomy
    (A B : BallNeighborhoodChart E2 E2)
    (hdis : Disjoint A.boundary B.boundary) :
    Disjoint A.closedRegion B.closedRegion ∨
      A.closedRegion ⊆ B.inside ∨ B.closedRegion ⊆ A.inside := by
  have hdim : 1 < Module.rank ℝ E2 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E2])
  have hAc := A.boundary_connected hdim
  have hBc := B.boundary_connected hdim
  rcases B.preconnected_subset_inside_or_outside hAc.isPreconnected hdis with hAB | hAo
  · exact Or.inr (Or.inl (B.closedRegion_subset_inside_of_boundary_subset A
      hBc.isPreconnected hAc hdis.symm hAB))
  rcases A.preconnected_subset_inside_or_outside hBc.isPreconnected hdis.symm with
      hBA | hBo
  · exact Or.inr (Or.inr (A.closedRegion_subset_inside_of_boundary_subset B
      hAc.isPreconnected hBc hdis hBA))
  have hinsideDisjoint : Disjoint A.inside B.boundary := by
    apply disjoint_left.mpr
    intro y hyA hyB
    exact hBo hyB (image_mono ball_subset_closedBall hyA)
  have hout : A.inside ⊆ B.closedRegionᶜ := by
    rcases B.preconnected_subset_inside_or_outside
        A.inside_connected.isPreconnected hinsideDisjoint with hin | ho
    · have hclosed := closure_mono hin
      rw [A.closure_inside, B.closure_inside] at hclosed
      obtain ⟨y, hy⟩ := hAc.nonempty
      exact False.elim (hAo hy (hclosed (image_mono sphere_subset_closedBall hy)))
    · exact ho
  left
  apply disjoint_left.mpr
  intro y hyA hyB
  rw [← A.inside_union_boundary] at hyA
  exact hyA.elim (fun hy => hout hy hyB) (fun hy => hAo hy hyB)

/-- A lower-level datum with disjoint disc boundaries is non-nested or
nested; Hatcher, Lemma 1.2, the two saddle pictures of Figure 1.2. -/
theorem SaddlePieceData.nonnested_or_nested_of_disjoint_discs
    {ψ : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (D : SaddlePieceData ψ u) (W : SaddleLowerLevelData D)
    (hdis : Disjoint (W.disc 0).boundary (W.disc 1).boundary) :
    D.nonnested ∨ D.nested := by
  rcases BallNeighborhoodChart.planar_closedRegion_trichotomy (W.disc 0) (W.disc 1) hdis
    with h | h | h
  · exact Or.inl ⟨W, h⟩
  · exact Or.inr ⟨W, Or.inl h⟩
  · exact Or.inr ⟨W, Or.inr h⟩

/-- S4 selects one of the two actual saddle pictures, possibly in the
opposite height direction. Hatcher, Lemma 1.2 and Figure 1.2, pp. 2-3. -/
theorem SaddlePieceData.nonnested_or_nested_or_reflected
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u) :
    (D.nonnested ∨ D.nested) ∨
      ∃ D' : SaddlePieceData psi (-u), D'.nonnested ∨ D'.nested := by
  rcases D.exists_lowerLevelData_or_reflected hP psi hpsi u with
      ⟨W, hW⟩ | ⟨D', W, hW⟩
  · exact Or.inl (D.nonnested_or_nested_of_disjoint_discs W hW)
  · exact Or.inr ⟨D', D'.nonnested_or_nested_of_disjoint_discs W hW⟩

end PoincareMT.M25.Topology3D
