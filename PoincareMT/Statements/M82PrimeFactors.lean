import PoincareMT.Definitions.M82PrimeFactors

/-!
# M82 prime-factor ledger statement

Natural-language statement: for an already constructed M72 reconstruction and
its M73 factor classification, expose a finite bijective ledger whose entries
are exactly the M72 non-survivor event pieces.  Every ledger entry is a
positive spaceform and carries a diffeomorphism to the unit three-sphere;
the ledger has an assembly of these pieces into the same time-zero slice.
The checked proof reuses M73's maps and M72's assembly, although the record
does not require equality to those particular witnesses. This adapter does
not derive a reconstruction, identify the original manifold with a sphere,
or state either Poincare endpoint.

Source context: Morgan--Tian Corollary 15.4, pp. 358-359, and the Poincare
specialization of blueprint node `MT.03.prime_decomposition_interfaces`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

def M82PrimeFactorLedgerStatement : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N)
    (C : M72ReconstructionConclusion I),
    (F : M73SphereFactorConclusion I C) →
      Nonempty (M82PrimeFactorLedger I C F)

end PoincareMT
