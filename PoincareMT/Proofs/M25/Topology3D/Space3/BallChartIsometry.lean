import PoincareMT.Proofs.M25.Topology3D.Space3.BallNeighborhood

/-!
# Changing orthonormal coordinates of a ball chart

Conjugation by a linear isometry retains a smooth neighborhood chart of
the closed unit ball. This changes the planar service coordinates to the
orthogonal stereographic plane for Hatcher's attaching-disc move,
Notes on Basic 3-Manifold Topology, Lemma 1.3, p. 3.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff

namespace PoincareMT.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Conjugate a ball chart by a linear isometry of its coordinates. -/
noncomputable def BallNeighborhoodChart.isometryConjugate
    (B : BallNeighborhoodChart E E) (U : F ≃ₗᵢ[ℝ] E) : BallNeighborhoodChart F F where
  chart := (U.toHomeomorph.toOpenPartialHomeomorph.trans B.chart).trans
    U.symm.toHomeomorph.toOpenPartialHomeomorph
  closedBall_subset_source := by
    intro x hx
    refine ⟨⟨mem_univ _, B.closedBall_subset_source ?_⟩, mem_univ _⟩
    change U x ∈ closedBall (0 : E) 1
    simpa only [mem_closedBall_zero_iff, U.norm_map] using hx
  smooth := U.symm.contDiff.comp_contDiffOn
    (B.smooth.comp U.contDiff.contDiffOn (fun _ hx => hx.1.2))
  smooth_symm := U.symm.contDiff.comp_contDiffOn
    (B.smooth_symm.comp U.contDiff.contDiffOn (fun _ hy => hy.2.1))

/-- The conjugated chart has the expected orthonormal coordinate formula. -/
@[simp] theorem BallNeighborhoodChart.isometryConjugate_apply
    (B : BallNeighborhoodChart E E) (U : F ≃ₗᵢ[ℝ] E) (x : F) :
    (B.isometryConjugate U).chart x = U.symm (B.chart (U x)) := rfl

end PoincareMT.M25.Topology3D
