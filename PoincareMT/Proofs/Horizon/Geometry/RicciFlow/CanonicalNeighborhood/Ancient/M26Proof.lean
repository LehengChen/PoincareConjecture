import PoincareMT.Statements.M26CanonicalNeighborhoods
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Producer
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Producer

/-!
# M26 and M27 proof entries

The source theorem constructions are intentionally owned by these numbered
entries.  Their predecessor bundles remain hypotheses, so downstream users
cannot accidentally treat a certificate as a proved predecessor service.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/- The M26 geometric construction is the Corollary 9.88/Theorem 9.89
   argument from Morgan--Tian, pp. 239--241. -/
theorem horizon_m26CanonicalNeighborhoods
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    RepairedCanonicalNeighborhoodTheory.{u} := by
  exact ⟨noncompactKappaSolutionAlternatives P, compactKappaSolutionAlternatives P⟩

theorem horizon_m26CanonicalNeighborhoodTheory
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    RepairedCanonicalNeighborhoodTheory.{u} :=
  horizon_m26CanonicalNeighborhoods P

end PoincareMT
