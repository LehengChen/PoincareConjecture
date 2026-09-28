import PoincareMT.Definitions.M24ModelCertificates

/-!
# M24 model-certificate statement

Refine the supplied M20 model on its actual shrinking flow. Every quotient
receives a projective-or-twisted normal form; no specialized applicability
witness is an input. The full ancient-kappa alternatives remain M26--M27.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- Refine one actual model, preserving its flow and exact product/quotient. -/
structure RepairedModelCertificateTheory
    {S : GradientShrinkingSolitonData 3 M}
    {G : ShrinkingSolitonFlow S}
    (input : M24ModelInput G) : Prop where
  certificate : ∃ c : RepairedKappaModelCertificate G,
    M24CertificateMatches input c

end PoincareMT
