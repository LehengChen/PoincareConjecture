import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.SmoothTime.Main
import PoincareMT.Statements.M66
import PoincareMT.Proofs.M61
import PoincareMT.Proofs.M65

/-!
# M66 Proposition 18.18 proof entry

M66 owns the ordinary-slab width differential argument: near-minimizer
families, M65 deformation, the Ricci-flow area variation and the integrating
factor.  Surgery jumps and their chronological composition belong to M67--M69.
Earlier M61 and M65 files are read-only; optional helpers belong under
`PoincareMT/Proofs/M66/`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal intervalIntegral

universe u

namespace PoincareMT

/-- M66: smooth-time forward-difference comparison for the M61 free-class
width, with the nontrivial class and trivial `pi₂` hypotheses stated on the
actual raw family.  Source: Morgan--Tian Proposition 18.18, pp. 431--432,
and its Proposition 18.24 reduction, pp. 433--434. -/
theorem m66SmoothTimeWidthComparison
    (hM61 : M61RawWidthCore.{u})
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61 hM64) :
    M66SmoothTimeTheory hM61 hM58 hM65 :=
  horizon_m66_smooth_time_theory hM61 hM58 hM65

/-- Concrete M61/M65 application for later consumers. -/
theorem m66SmoothTimeWidthComparison_from_predecessors :
    ∃ hM61 : M61RawWidthCore.{u},
      ∃ hM58 : RepairedShortLoopTrivialityTheory.{u},
      ∃ hM64 : M64ComparisonTheory.{u},
        ∃ hM65 : M65DeformationTheory hM61 hM64,
          M66SmoothTimeTheory hM61 hM58 hM65 := by
  obtain ⟨hM61, hM64, hM65⟩ :=
    m65LoopFamilyDeformation_from_predecessors
  exact ⟨hM61, repairedShortLoopTriviality, hM64, hM65,
    m66SmoothTimeWidthComparison hM61 repairedShortLoopTriviality hM65⟩

end PoincareMT
