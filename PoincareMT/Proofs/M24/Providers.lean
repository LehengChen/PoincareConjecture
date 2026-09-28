import PoincareMT.Proofs.M24
import PoincareMT.Proofs.M20.Providers

/-!
# M24 applications to the actual M20 models

Choices stay inside theorem proofs. The complete source derivation and
same-object requirements are in the M24 contract and round-one review.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- Produce both the covering transports and one normal form of this exact q. -/
theorem m24QuotientRefinement
    {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}
    (q : QuotientSphereLineCertificate G) :
    Nonempty (M24QuotientFlowTransport q × M24QuotientNormalForm q) := by
  obtain ⟨certificate, hmatch⟩ :=
    (m24ModelCertificates (.quotientSphereLine q)).certificate
  cases certificate with
  | sphericalSpaceForm _ => exact False.elim hmatch
  | sphereLine _ => exact False.elim hmatch
  | quotientSphereLine q' transport normal =>
    change q' = q at hmatch
    subst q'
    exact ⟨transport, normal⟩

/-- Apply M20's closed producer to S, then refine its actual selected model.
The returned classification datum fixes both the flow and the M20 branch. -/
theorem m24ModelCertificatesFromMilestones
    (S : GradientShrinkingSolitonData 3 M) :
    ∃ D : ThreeDimensionalClassificationData S,
      RepairedModelCertificateTheory (M24ModelInput.ofM20Model D.conclusion.model) := by
  obtain ⟨D⟩ := m20ClassificationFromMilestones.classify S
  exact ⟨D, m24ModelCertificates (M24ModelInput.ofM20Model D.conclusion.model)⟩

end PoincareMT
