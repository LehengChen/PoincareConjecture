import PoincareMT.Proofs.M64.Sec19_3_Annuli.ModulusFreeBoundaryTransport
import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarFreeModulusApproximation

/-!
# Free-modulus suppliers for actual shrinking curves

At an included time, the C2 shrinking-curve fields give the regularity of
both boundary traces.  The scalar uniformization construction therefore
supplies the free positive-modulus approximation, while the zero-area collar
construction transports every lifted-boundary annulus back to the literal
boundary class without changing its area.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- The actual C2 shrinking curves supply free positive-modulus approximation and zero-area
transport to their literal boundary class. Source: Morgan--Tian (2007), Lemma 19.15 and
Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64C2ShrinkingCurves_free_modulus_suppliers
    {a b : ℝ} (F : RicciFlow n M (Icc a b))
    {c0 c1 : ℝ → ℝ → M}
    (hc0 : M63C2ShrinkingCurveOn F c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn F c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) :
    M64FreeConformalModulusApproximation (F.metric t)
        (fun x => c0 x t) (fun x => c1 x t) ∧
      M64FreeBoundaryAreaTransport (F.metric t)
        (fun x => c0 x t) (fun x => c1 x t) := by
  have h0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun x => c0 x t) :=
    (hc0.spatial_regular t ht).of_le (by norm_num)
  have h1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun x => c1 x t) :=
    (hc1.spatial_regular t ht).of_le (by norm_num)
  refine ⟨?_, ?_⟩
  · exact M64Uniformization.m64FreeConformalModulusApproximation_of_C1
      (F.metric t) h0 h1
  · exact m64C2ShrinkingCurves_freeBoundaryAreaTransport F hc0 hc1 ht

end PoincareMT
