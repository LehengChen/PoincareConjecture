import PoincareMT.Proofs.M25.Topology3D.Space3.Base.SaddleTwoCircleSide
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.SaddleLowerLevelData
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.SaddleHeightReflection

/-!
# Lower saddle discs in one of the two height directions

Choose a single offset within both original and reflected cap-gap budgets.
The two-circle-side theorem then supplies the actual lower datum and
disjoint disc boundaries in one direction. Source: Hatcher, Lemma 1.2,
pp. 2-3; SLD2 and S4 assembly derivation of 2026-09-23.
-/

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareMT.M25.Topology3D

/-- S4: every raw saddle has lower disc data with disjoint boundaries,
possibly after reversing the height direction. Hatcher, Lemma 1.2,
pp. 2-3; SLD2 and S4 assembly derivation of 2026-09-23. -/
theorem SaddlePieceData.exists_lowerLevelData_or_reflected
    (hP : PlanarSchoenfliesService)
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ) (u : UnitTwoSphere)
    (D : SaddlePieceData ψ u) :
    (∃ W : SaddleLowerLevelData D,
      Disjoint (W.disc 0).boundary (W.disc 1).boundary) ∨
    ∃ D' : SaddlePieceData ψ (-u), ∃ W : SaddleLowerLevelData D',
      Disjoint (W.disc 0).boundary (W.disc 1).boundary := by
  classical
  obtain ⟨epsilon, hepsilon, hdata⟩ :=
    exists_saddle_lowerLevelData_of_two_circles hP ψ hψ u D
  obtain ⟨epsilonR, hepsilonR, hdataR⟩ :=
    exists_saddle_lowerLevelData_of_two_circles hP ψ hψ (-u) D.reverseHeight
  obtain ⟨delta, hdelta, hsmall, hside⟩ :=
    exists_saddle_two_circle_side ψ hψ u D (min epsilon epsilonR)
      (lt_min hepsilon hepsilonR)
  rcases hside with ⟨q, hq, hdis, hlevel⟩ | ⟨q, hq, hdis, hlevel⟩
  · obtain ⟨W, _hlevelW, _htopW, _hlabelsW, hW⟩ := hdata delta hdelta
      (hsmall.trans_le (min_le_left _ _)) q hq hdis hlevel
    exact Or.inl ⟨W, hW⟩
  · have hlevelR : (⋃ b : Fin 2, range (q b)) =
        {p : UnitTwoSphere | ⟪((-u : UnitTwoSphere) : E3), ψ (p, 0)⟫_ℝ =
          ⟪((-u : UnitTwoSphere) : E3), ψ (D.reverseHeight.point, 0)⟫_ℝ - delta} := by
      rw [hlevel]
      ext p
      change (⟪(u : E3), ψ (p, 0)⟫_ℝ =
          ⟪(u : E3), ψ (D.point, 0)⟫_ℝ + delta) ↔
        (⟪((-u : UnitTwoSphere) : E3), ψ (p, 0)⟫_ℝ =
          ⟪((-u : UnitTwoSphere) : E3), ψ (D.point, 0)⟫_ℝ - delta)
      rw [coe_neg_sphere, inner_neg_left, inner_neg_left]
      constructor <;> intro h <;> linarith
    obtain ⟨W, _hlevelW, _htopW, _hlabelsW, hW⟩ := hdataR delta hdelta
      (hsmall.trans_le (min_le_right _ _)) q hq hdis hlevelR
    exact Or.inr ⟨D.reverseHeight, W, hW⟩

end PoincareMT.M25.Topology3D
