import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryOddReflection
import PoincareMT.Proofs.Horizon.Analysis.Sobolev.Boundary.NormalDerivative

/-!
# H2 regularity for an actual odd reflection

The zero-trace odd reflection carries the genuine weak first derivatives of a
half-domain map across the flat face.  Once the parent variation/metric chain
has supplied a smooth uniformly elliptic scalar equation and tangential weak
second derivatives, the lower boundary normal-recovery theorem supplies the
missing normal derivative.  No C1 or global regularity of the original map is
used here.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.BoundaryTangential
open Poincare.Analysis.Sobolev.BoundaryExtension

namespace PoincareMT

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- H2 regularity of the actual odd reflection on a compact inner ball. The equation is
deliberately an input: it is the scalar equation produced by the weighted first-variation
and inverse-metric chain. The theorem only performs the analytic normal-recovery step, with
the tangential Hessians and all integrability hypotheses checked explicitly. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis. Project derivation:
`proof-work/tasks/M64/reports/2026-09-25-boundary-reflected-h2.md`. -/
theorem m64OddBoundaryReflect_memWkp_two_of_weakEquation
    (B : Poincare.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm 2 univ)
    {O : Set Plane} (hO : IsOpen O) (hOc : IsCompact (closure O))
    {u : Plane → ℝ} {v : Fin 2 → Plane → ℝ} {f : Plane → ℝ}
    (hu : Continuous u)
    (hzero : ∀ p : Plane, p 0 = 0 → u p = 0)
    (huHalf : MemLp u 2 (volume.restrict (halfSpace 2)))
    (hvHalf : ∀ i : Fin 2, MemLp (v i) 2 (volume.restrict (halfSpace 2)))
    (hwHalf : ∀ i : Fin 2, HasWeakPartialDeriv i (v i) u (halfSpace 2))
    (hf : MemLp f 2 (volume.restrict O))
    (htan : ∀ k : Fin 2, k ≠ 0 → ∀ i : Fin 2,
      ∃ q : Plane → ℝ, MemLp q 2 (volume.restrict O) ∧
        HasWeakPartialDeriv k q
          (m64BoundaryReflect (-coordinateSign i) (v i)) O)
    (heq : ∀ phi : Plane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O →
      (∫ x in O, ∑ i : Fin 2, ∑ j : Fin 2,
        B.a x i j * m64BoundaryReflect (-coordinateSign j) (v j) x *
          fderiv ℝ phi x (EuclideanSpace.single i 1)) =
        ∫ x in O, f x * phi x) :
    MemWkp 2 2 (m64ContinuousBoundaryReflect (-1) u) O := by
  let U : Plane → ℝ := m64ContinuousBoundaryReflect (-1) u
  let P : Fin 2 → Plane → ℝ := fun i =>
    m64BoundaryReflect (-coordinateSign i) (v i)
  have hUall : MemLp U 2 volume := by
    simpa only [U] using m64ContinuousBoundaryReflect_memLp huHalf (-1)
  have hPall (i : Fin 2) : MemLp (P i) 2 volume := by
    simpa only [P] using m64BoundaryReflect_memLp (hvHalf i) (-coordinateSign i)
  have hU : MemLp U 2 (volume.restrict O) :=
    (show MemLp U 2 (volume.restrict (Set.univ : Set Plane)) by
      simpa only [Measure.restrict_univ] using hUall).mono_measure
      (Measure.restrict_mono_set volume (subset_univ O))
  have hP (i : Fin 2) : MemLp (P i) 2 (volume.restrict O) :=
    (show MemLp (P i) 2 (volume.restrict (Set.univ : Set Plane)) by
      simpa only [Measure.restrict_univ] using hPall i).mono_measure
      (Measure.restrict_mono_set volume (subset_univ O))
  have hW (i : Fin 2) :
      HasWeakPartialDeriv i (P i) U O := by
    have h := m64OddBoundaryReflect_weak i hu hzero huHalf (hvHalf i) (hwHalf i)
    simpa only [P, U] using h.restrict hO (subset_univ O)
  apply Poincare.Analysis.Sobolev.BoundaryNormal.memWkp_two_of_tangential_weakDerivatives
    B hO hOc hU hf hP hW
  · simpa only [P] using htan
  · simpa only [P, U] using heq

end PoincareMT
