import PoincareMT.Definitions.M35StandardCapUniqueness
import PoincareMT.Proofs.M34.Sec12_5_RotationInvariance.Uniqueness

/-!
# Common-domain metric uniqueness from the published lower proof

Morgan-Tian Theorem 12.5(1), pp. 295-296, and Section 12.5.
M34's native finite-neighbor energy proof applies to every actual
partial standard-cap flow. Its inputs are the prescribed initial
estimate and cylindrical end; no raw symmetry or gauge is assumed.
-/

set_option autoImplicit false

namespace PoincareMT.RepairedStandardCapExistenceData

theorem partial_metric_unique (P : RicciFlowCurvatureTheory.{0})
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (G : PartialStandardCapFlow g₀) {t : ℝ}
    (ht : t ∈ Set.Ico 0 E.flow.base.lifetime ∩ Set.Ico 0 G.lifetime) :
    E.flow.metric t = G.flow.metric t :=
  M34.partialStandardCapFlow_metric_unique P E.initial_estimate E.flow.base G
    g₀.cylindrical_end ht

end PoincareMT.RepairedStandardCapExistenceData
