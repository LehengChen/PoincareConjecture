import PoincareMT.Proofs.M64.Sec19_3_Annuli.CurvatureSupremum
import PoincareMT.Statements.M63RampEstimates

/-!
# Curvature fields from the selected M63 geometry

The M63 flow conclusion selects the actual ambient geometry.  On a compact
time slab, the full curvature range is bounded above and its supremum is
nonnegative and continuous.  The annular attainment and variation fields are
separate producers and are intentionally not constructed here.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- The selected M63 geometry has bounded full-curvature range and a continuous nonnegative
curvature supremum on the compact time slab. Source: Morgan--Tian (2007), Lemma 19.15 and
Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64CurvatureFields_of_M63
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}
    (hM63 : M63RampEstimatesTheory.{u})
    (hcompact : IsCompact (Set.univ : Set M)) :
    ∃ _G : M63AmbientGeometry F,
      (∀ t ∈ Set.Icc a b,
        BddAbove (Set.range (fun x : M =>
          (F.connection t).curvatureTensorNorm x))) ∧
      (∀ t ∈ Set.Icc a b, 0 ≤ m64CurvatureSupremum F t) ∧
      ContinuousOn (m64CurvatureSupremum F) (Set.Icc a b) := by
  obtain ⟨C⟩ := hM63.2.1 n M a b F hcompact
  refine ⟨C.geometry, ?_, ?_, ?_⟩
  · intro t ht
    exact m64CurvatureRange_bddAbove_of_compact hcompact ht
  · intro t ht
    exact m64CurvatureSupremum_nonneg
      (m64CurvatureRange_bddAbove_of_compact hcompact ht)
  · exact m64CurvatureSupremum_continuous_of_compact hcompact

end PoincareMT
