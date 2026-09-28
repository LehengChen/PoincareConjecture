import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryLifts
import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusReduction

/-!
# Fixed-to-free modulus bridge

The free candidate class includes the identity boundary lifts.  Consequently
an actual fixed-trace conformal approximation immediately supplies the public
free-trace predicate, with no change to the annulus map or its energy fields.
This is a logical bridge only; the fixed-trace approximation itself still
requires its analytic Douglas--Morrey producer.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- The identity degree-one lifts embed a supplied fixed-trace modulus approximation into
the free-trace candidate class. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the
explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-boundary-lifts.md`. -/
theorem m64FreeConformalModulusApproximation_of_fixed
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (hfixed : M64ConformalModulusApproximation g c0 c1) :
    M64FreeConformalModulusApproximation g c0 c1 := by
  intro A ε hε
  obtain ⟨r, hr, A', hAint, henergy⟩ := hfixed A ε hε
  refine ⟨r, hr, scalarIdentityDegreeOneLift, scalarIdentityDegreeOneLift,
    A', ?_, ?_⟩
  · simpa only [scalarIdentityDegreeOneLift] using hAint
  · simpa only [scalarIdentityDegreeOneLift] using henergy

end PoincareMT
