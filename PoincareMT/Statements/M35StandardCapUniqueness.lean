import PoincareMT.Definitions.M35StandardCapUniqueness

/-!
# M35 repaired standard-cap uniqueness and estimates statement

Every M34 standard-cap existence package satisfies the repaired uniqueness,
including common-domain equality with every compatible partial standard flow,
as well as the scalar lower rate and canonical-alternative package on its
selected flow.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedStandardCapUniquenessTheory : Prop where
  estimates : ∀ g₀ : StandardInitialMetric,
    ∀ E : RepairedStandardCapExistenceData g₀,
      Nonempty (RepairedStandardCapUniquenessData g₀ E)

end PoincareMT
