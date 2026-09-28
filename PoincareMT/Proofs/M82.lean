import PoincareMT.Definitions.M82PrimeFactors
import PoincareMT.Statements.M73SphereFactors
import PoincareMT.Statements.M82PrimeFactors

/-!
# M82 prime-factor ledger adapter proof

This is a checked projection from supplied M72 and M73 conclusion data.
It reuses their indices, carriers, maps and assembly directly; no theorem
service is invoked and no new admission is needed at this auxiliary boundary.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Given an actual M72 reconstruction and M73 classification of its factors,
construct a finite bijective ledger of those exact non-survivor event pieces,
with their spaceform kinds, sphere diffeomorphisms and an assembly into the
same time-zero slice. This proof reuses the supplied maps and assembly.

Project-local logical adapter for the Poincare specialization of blueprint
node `MT.03.prime_decomposition_interfaces`; source context is Morgan--Tian
Corollary 15.4, printed pp. 358-359. The applicable event-provenance corrections
are recorded in `reviews/errata/2026-09-16-raw-m38-m72.md`; no new source theorem
or endpoint admission is asserted here. -/
theorem m82PrimeFactorLedger : M82PrimeFactorLedgerStatement.{u} := by
  intro M _ _ _ _ _ _ _ _ N I C F
  let L : M82PrimeFactorLedger I C F :=
    { source := C.summand_index
      source_bijective := C.summand_index_bijective
      source_eq := rfl
      pieces := C.pieces
      piece_eq := by
        intro j
        simpa using C.piece_eq j
      non_survivor := by
        intro j
        simpa using C.piece_kind j
      spaceform := by
        intro j
        simpa using F.factor_kind j
      sphere_map := by
        intro j
        simpa using F.factor_sphere j
      assembly := C.assembly }
  exact ⟨L⟩

end PoincareMT
