import PoincareMT.Proofs.M25.Topology3D.Space3.Saddle.PieceData

/-!
# Disjoint boundaries of the actual lower-level planar discs

The two full source legs are disjoint, and the collar is injective at
time zero. Source: Hatcher, Notes on Basic 3-Manifold Topology,
Lemma 1.2, pp. 2-3; reviewed disc-boundary inventory of 2026-09-23.
-/

set_option autoImplicit false

open Set
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareMT.M25.Topology3D

/-- The actual lower-leg planar boundary curves are disjoint.
Source: Hatcher, Lemma 1.2; the two lower legs and central collar injection. -/
theorem SaddleLowerLevelData.disc_boundaries_disjoint
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    {D : SaddlePieceData psi u} (W : SaddleLowerLevelData D)
    (hpsi : IsCollarEmbedding psi) :
    Disjoint (W.disc 0).boundary (W.disc 1).boundary := by
  apply disjoint_left.mpr
  intro x hx0 hx1
  let y : E3 := (heightPlaneCoordinates u).symm (x, W.level)
  have himage (b : Fin 2) (hx : x ∈ (W.disc b).boundary) :
      y ∈ range (fun theta => psi (W.leg b (theta, W.level), 0)) := by
    rw [← W.disc_boundary b]
    exact ⟨x, hx, rfl⟩
  obtain ⟨theta0, h0⟩ := himage 0 hx0
  obtain ⟨theta1, h1⟩ := himage 1 hx1
  have hp : W.leg 0 (theta0, W.level) = W.leg 1 (theta1, W.level) :=
    congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ (h0.trans h1.symm))
  have htop (b : Fin 2) (theta : UnitCircle) :
      (theta, W.level) ∈ (univ : Set UnitCircle) ×ˢ Icc
        ((D.cap (W.label b)).cutHeight +
          (D.cap (W.label b)).sign * (D.cap (W.label b)).removal) W.level :=
    ⟨mem_univ _, (W.lower_seams_lt_level _ (W.label_lower b)).le, le_rfl⟩
  exact disjoint_left.mp W.leg_disjoint
    ⟨(theta0, W.level), htop 0 theta0, rfl⟩
    ⟨(theta1, W.level), htop 1 theta1, hp.symm⟩

end PoincareMT.M25.Topology3D
