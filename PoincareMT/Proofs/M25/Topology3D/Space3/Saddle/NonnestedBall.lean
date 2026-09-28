import PoincareMT.Proofs.M25.Topology3D.Space3.Saddle.NonnestedBridge
import PoincareMT.Proofs.M25.Topology3D.Space3.Saddle.ShortPiece
import PoincareMT.Proofs.M25.Topology3D.Space3.Saddle.BallTransport
import PoincareMT.Proofs.M25.Topology3D.Space3.Saddle.ReferenceBallChart

/-!
# A ball for a nonnested saddle piece

Shorten the actual collar, construct its complete reference boundary
comparison, and pull the reference ball back by the actual inverse.
Source: Hatcher, Notes on Basic 3-Manifold Topology, Lemma 1.2, pp. 2-3;
reviewed terminal nonnested consumer of 2026-09-24.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareMT.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

/-- The literal central image is the range of the central collar map.
Source: Hatcher, Lemma 1.2; reviewed terminal consumer, central-image identity. -/
theorem image_univ_prod_singleton_zero (ψ : UnitTwoSphere × ℝ → E3) :
    ψ '' (Set.univ ×ˢ ({0} : Set ℝ)) =
      Set.range (fun q : UnitTwoSphere => ψ (q, 0)) := by
  ext y
  constructor
  · rintro ⟨⟨q, t⟩, ⟨-, ht⟩, rfl⟩
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨(q, 0), ⟨Set.mem_univ _, rfl⟩, rfl⟩

/-- Pull the known reference ball back through the complete bridge and
shortening maps. Source: Hatcher, Lemma 1.2, pp. 2-3. -/
theorem exists_ball_of_bridge_witness
    (ψ : UnitTwoSphere × ℝ → E3) (Gshort Kmid : D3) (Sshort : Set E3)
    (Bref : BallNeighborhoodChart E3 E3)
    (hshort : Sshort = Gshort '' Set.range (fun q : UnitTwoSphere => ψ (q, 0)))
    (hbridge : Kmid '' Sshort = Bref.boundary) :
    ∃ B : BallNeighborhoodChart E3 E3, B.boundary = ψ '' (Set.univ ×ˢ {0}) := by
  rw [image_univ_prod_singleton_zero]
  refine exists_ball_of_diffeomorphic_image (Gshort.trans Kmid) _ Bref ?_
  rw [← hbridge, hshort, Diffeomorph.coe_trans, Set.image_comp]

/-- Non-nested case: below `c` the two level circles bound disjoint planar discs.
Source: Hatcher, Lemma 1.2, pp. 2-3; the exact GOAL-SADDLE target. -/
theorem exists_ball_of_saddle_piece_nonnested (hP : PlanarSchoenfliesService)
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ) (u : UnitTwoSphere)
    (D : SaddlePieceData ψ u) (hD : D.nonnested) :
    ∃ B : BallNeighborhoodChart E3 E3, B.boundary = ψ '' (Set.univ ×ˢ {0}) := by
  -- S1: shorten the piece (unit budget) and retain `G = I 1`.
  obtain ⟨_, _, G, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, Dnew,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnewCollar, hrange, _, hshort, _, _, hpoint,
    _, _, _, _, hnn, _⟩ := exists_short_saddle_piece ψ hψ u D 1 one_pos
  obtain ⟨Wnew, hWnew⟩ := hnn hD
  -- The short piece is short about its own saddle height (beta-reduced form).
  have hc : ⟪(u : E3), G (ψ (Dnew.point, 0))⟫_ℝ = ⟪(u : E3), ψ (D.point, 0)⟫_ℝ := hpoint
  have hshort' : ∀ q : UnitTwoSphere,
      |⟪(u : E3), G (ψ (q, 0))⟫_ℝ - ⟪(u : E3), G (ψ (Dnew.point, 0))⟫_ℝ| < 1 :=
    fun q => by rw [hc]; exact hshort q
  -- B1 on the short piece.
  obtain ⟨d, hd, A, Kmid, hbridge⟩ :=
    exists_saddle_nonnested_bridge_witness hP (fun p => G (ψ p)) hnewCollar u Dnew Wnew
      hWnew 1 one_pos hshort'
  -- Assembly through `G.trans Kmid`.
  refine exists_ball_of_bridge_witness ψ G Kmid _
    ((nonnestedReferenceBallChart 0 d hd).mapDiffeomorph A) hrange ?_
  rw [BallNeighborhoodChart.mapDiffeomorph_boundary]
  exact hbridge

end PoincareMT.M25.Topology3D
