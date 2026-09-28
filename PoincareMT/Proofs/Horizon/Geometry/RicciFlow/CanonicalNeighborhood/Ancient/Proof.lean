import PoincareMT.Statements.M27KappaAlternatives
import PoincareMT.Statements.M27Providers
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Producer
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Producer
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactAssembly
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactCoverage.Alternatives

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

/- The M27 construction is Theorem 9.93 and Corollary 9.94, pp. 242--243. -/
theorem horizon_m27KappaAlternatives
    (P : M27KappaAlternativePredecessors.{u}) :
    RepairedKappaAlternativeTheory.{u} := by
  exact m27KappaAlternatives_of_compact_classification P (compact_positive_classification_of_m27 P)

end PoincareMT
