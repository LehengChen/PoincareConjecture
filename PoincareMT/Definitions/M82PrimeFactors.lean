import PoincareMT.Definitions.M73SphereFactors

/-!
# M82 prime-factor ledger adapter

M72 owns the finite reverse-time reconstruction and M73 classifies its exact
non-survivor pieces.  This auxiliary record gives later reviewers one stable
ledger carrying those same indices, carriers and kinds, together with sphere
maps and a reconstruction assembly. The checked constructor reuses the maps
and assembly supplied by M73 and M72. This is a project-local projection
boundary, not a second reconstruction or an endpoint theorem.

Source context: the Poincare specialization of the supplied blueprint node
`MT.03.prime_decomposition_interfaces` and Morgan--Tian Corollary 15.4,
printed pp. 358-359. This adapter asserts no prime-decomposition uniqueness
or general geometrization theorem.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure M82PrimeFactorLedger
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N)
    (C : M72ReconstructionConclusion I)
    (F : M73SphereFactorConclusion I C) where
  source : Fin C.summand_count → M72SummandIndex I C.ledger
  source_bijective : Function.Bijective source
  source_eq : source = C.summand_index
  pieces : Fin C.summand_count → GeneralizedSliceCarrier := C.pieces
  piece_eq : ∀ j,
    pieces j =
      (M72EventTopology I C.ledger (source j).1).conclusion.piece
        (source j).2.1
  non_survivor : ∀ j,
    (M72EventTopology I C.ledger (source j).1).conclusion.kind
      (source j).2.1 ≠ .survivor
  spaceform : ∀ j,
    (M72EventTopology I C.ledger (source j).1).conclusion.kind
      (source j).2.1 = .spaceform
  sphere_map : ∀ j, Diffeomorph (𝓡 3) (𝓡 3) (pieces j).carrier ThreeSphere ∞
  assembly : SmoothFiniteConnectedSumAssembly pieces
    (I.global.certificate.flow.slice 0)

end PoincareMT
