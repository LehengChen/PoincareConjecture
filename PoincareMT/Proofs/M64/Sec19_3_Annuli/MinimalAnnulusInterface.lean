import PoincareMT.Proofs.M64.Sec19_3_Annuli.Infimum

/-!
# The minimal-annulus producer interface

The area infimum is an order-theoretic object; its attainment and regularity
are separate geometric obligations.  This record names the data used by the
later first-variation argument without importing a Plateau theorem or
asserting existence by fiat.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {c0 c1 : ℝ → M}

/-- A genuine minimal annulus together with the regularity used by the first-variation
argument. The record is a producer interface: existence is proved separately from the
elementary infimum facts below. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary
19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
structure M64MinimalAnnulusData where
  annulus : M64Annulus g c0 c1
  area_minimal : annulus.area = m64LeastAnnulusArea g c0 c1
  piecewise_c1 : M64PiecewiseC1Annulus annulus
  interior_smooth : ContMDiffOn (𝓡 2) (𝓡 n) ∞ annulus.map
    (interior m64AnnulusDomain)

/-- The retained minimal annulus has nonnegative actual area. Source: Morgan--Tian (2007),
Lemma 19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem M64MinimalAnnulusData.area_nonneg
    (A : M64MinimalAnnulusData (g := g) (c0 := c0) (c1 := c1)) :
    0 ≤ A.annulus.area :=
  A.annulus.area_nonneg

/-- The retained attainment identity is the infimum of the original admissible area range.
Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project
derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem M64MinimalAnnulusData.area_eq_sInf
    (A : M64MinimalAnnulusData (g := g) (c0 := c0) (c1 := c1)) :
    A.annulus.area = sInf (m64AnnulusAreaRange g c0 c1) :=
  A.area_minimal

/-- The retained minimal annulus has area no greater than any actual competitor. Source:
Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem M64MinimalAnnulusData.area_le
    (A : M64MinimalAnnulusData (g := g) (c0 := c0) (c1 := c1))
    (B : M64Annulus g c0 c1) :
    A.annulus.area ≤ B.area := by
  rw [A.area_minimal]
  exact m64LeastAnnulusArea_le_annulus B

/-- The retained actual minimal annulus witnesses a nonempty area range. Source:
Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64MinimalAnnulus_areaRange_nonempty
    (A : M64MinimalAnnulusData (g := g) (c0 := c0) (c1 := c1)) :
    (m64AnnulusAreaRange g c0 c1).Nonempty :=
  m64AnnulusAreaRange_nonempty A.annulus

/-- The original admissible area range is bounded below by nonnegative area. Source:
Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64MinimalAnnulus_areaRange_bddBelow
    : BddBelow (m64AnnulusAreaRange g c0 c1) :=
  m64AnnulusAreaRange_bddBelow g c0 c1

end PoincareMT
