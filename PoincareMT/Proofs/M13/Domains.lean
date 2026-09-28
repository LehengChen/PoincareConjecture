import PoincareMT.Proofs.M13.Geometry
import PoincareMT.Statements.M13DomainTransport

/-!
# The domain transport record

The equivalences retain every supplied map and its exact affine interval.
The spatial source universe is independent of the spacetime universe.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareMT.M13

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X}

noncomputable def domainTransport (R : GeneralizedFlowCarrierConclusion A)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    ParabolicDomainTransport.{u, v} (spacetimeRescaling R Q hQ a) where
  worldlineEquiv := worldlineEquiv
  worldline_forward _ _ _ := rfl
  worldline_inverse _ _ _ := rfl
  embeddingEquiv := embeddingEquiv
  embedding_forward _ _ _ _ _ _ := rfl
  embedding_inverse _ _ _ _ _ _ := rfl
  cylinderEquiv := cylinderEquiv
  cylinder_forward _ _ _ _ _ _ _ _ := rfl
  cylinder_inverse _ _ _ _ _ _ _ _ := rfl
  cylinder_embedding _ _ _ _ _ _ := by
    apply compatibleEmbedding_ext
    rfl

end PoincareMT.M13
