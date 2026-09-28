import PoincareMT.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareMT.Proofs.M25.Topology3D.Space3.NorthSphereChart
import PoincareMT.Proofs.M25.Topology3D.Space3.SourceCircleDisc

/-!
# The entire tagged cap in actual child-ball parameters

The antipodal northern chart gives the whole southern disc, including
its rim, before changing by the actual boundary parametrization.
Source: Hatcher, Notes on Basic 3-Manifold Topology, Lemma 1.3, p. 3;
the reviewed normalized-child-ball inventory of 2026-09-22.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareMT.M25.Topology3D

attribute [local instance] sourceCircle_stereographic_dimension

/-- The actual source cap is a smooth closed disc in the given sphere
parameters, with both partial-chart domains and inverse order retained. -/
theorem exists_child_cap_source_disc
    (ψ : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (tag : SurgeryCapTag ψ u)
    (g : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞) :
    ∃ e : OpenPartialHomeomorph E2 UnitTwoSphere,
      e.source = {X : E2 | -northSpherePoint X ∈ tag.sourceChart.source} ∧
      e.target = {q : UnitTwoSphere |
        g.symm q ∈ tag.sourceChart.target ∧
        -(tag.sourceChart.symm (g.symm q)) ∈ northSphereDomain} ∧
      (∀ X : E2, e X = g (tag.sourceChart (-northSpherePoint X))) ∧
      (∀ q : UnitTwoSphere, e.symm q =
        northSphereCoordinate (-(tag.sourceChart.symm (g.symm q)))) ∧
      closedBall (0 : E2) 1 ⊆ e.source ∧
      ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target ∧
      e '' closedBall (0 : E2) 1 = g '' tag.sourceCap := by
  let N : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞ := {
    toEquiv := {
      toFun := fun q => -q
      invFun := fun q => -q
      left_inv := neg_neg
      right_inv := neg_neg }
    contMDiff_toFun := contMDiff_neg_sphere
    contMDiff_invFun := contMDiff_neg_sphere }
  let P := northSphereChart.symm.trans N.toHomeomorph.toOpenPartialHomeomorph
  let J := P.trans tag.sourceChart
  let e := J.trans g.toHomeomorph.toOpenPartialHomeomorph
  have hPs : P.source = univ := by
    ext X
    change (X ∈ (univ : Set E2) ∧
      northSpherePoint X ∈ (univ : Set UnitTwoSphere)) ↔ X ∈ univ
    simp only [mem_univ, true_and]
  have hPt : P.target = {q : UnitTwoSphere | -q ∈ northSphereDomain} := by
    ext q
    change (q ∈ (univ : Set UnitTwoSphere) ∧ -q ∈ northSphereDomain) ↔ _
    simp only [mem_univ, true_and, mem_ofPred_eq]
  have hPm : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ P P.source :=
    (N.contMDiff.comp northSphereChart_symm_contMDiff).contMDiffOn
  have hPi : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ P.symm P.target :=
    northSphereChart_contMDiffOn.comp N.symm.contMDiff.contMDiffOn (fun _ hq => hq.2)
  have hJm : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ J J.source :=
    tag.source_smooth.comp (hPm.mono inter_subset_left) (fun _ hX => hX.2)
  have hJi : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ J.symm J.target :=
    hPi.comp (tag.source_inverse.mono inter_subset_left) (fun _ hq => hq.2)
  have hem : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source :=
    g.contMDiff.comp_contMDiffOn (hJm.mono inter_subset_left)
  have hei : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target :=
    hJi.comp g.symm.contMDiff.contMDiffOn (fun _ hq => hq.2)
  have hes : e.source = {X : E2 | -northSpherePoint X ∈ tag.sourceChart.source} := by
    ext X
    change ((X ∈ P.source ∧ -northSpherePoint X ∈ tag.sourceChart.source) ∧
      J X ∈ (univ : Set UnitTwoSphere)) ↔ _
    rw [hPs]
    simp only [mem_univ, true_and, and_true, mem_ofPred_eq]
  have het : e.target = {q : UnitTwoSphere |
      g.symm q ∈ tag.sourceChart.target ∧
      -(tag.sourceChart.symm (g.symm q)) ∈ northSphereDomain} := by
    ext q
    change (q ∈ (univ : Set UnitTwoSphere) ∧
      (g.symm q ∈ tag.sourceChart.target ∧
        tag.sourceChart.symm (g.symm q) ∈ P.target)) ↔ _
    rw [hPt]
    simp only [mem_univ, true_and, mem_ofPred_eq]
  have hnegative : (fun q : UnitTwoSphere => -q) ''
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} =
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      change (heightCoordinates (-(p : E3))).2 ≤ 0
      rw [map_neg]
      change -(heightCoordinates (p : E3)).2 ≤ 0
      exact neg_nonpos.mpr hp
    · intro hq
      refine ⟨-q, ?_, neg_neg q⟩
      change 0 ≤ (heightCoordinates (-(q : E3))).2
      rw [map_neg]
      change 0 ≤ -(heightCoordinates (q : E3)).2
      exact neg_nonneg.mpr hq
  have hPcap : P '' closedBall (0 : E2) 1 =
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} := by
    calc
      P '' closedBall (0 : E2) 1 =
          (fun q : UnitTwoSphere => -q) ''
            (northSpherePoint '' closedBall (0 : E2) 1) := by
        rw [image_image]
        rfl
      _ = _ := by rw [northSpherePoint_image_closedBall, hnegative]
  have hclosed : closedBall (0 : E2) 1 ⊆ e.source := by
    intro X hX
    rw [hes]
    change P X ∈ tag.sourceChart.source
    apply tag.south_mem_source
    have hPX : P X ∈ P '' closedBall (0 : E2) 1 := ⟨X, hX, rfl⟩
    rwa [hPcap] at hPX
  refine ⟨e, hes, het, fun _ => rfl, fun _ => rfl, hclosed, hem, hei, ?_⟩
  calc
    e '' closedBall (0 : E2) 1 =
        g '' (tag.sourceChart '' (P '' closedBall (0 : E2) 1)) := by
      simp only [image_image]
      rfl
    _ = g '' tag.sourceCap := by rw [hPcap]; rfl

end PoincareMT.M25.Topology3D
