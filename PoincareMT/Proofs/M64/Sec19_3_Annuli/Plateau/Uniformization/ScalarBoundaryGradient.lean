import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarHalfSpaceGradient
import PoincareMT.Proofs.Horizon.Analysis.Sobolev.Boundary.Localization.Sobolev

/-!
# Continuous gradients from local annular H3 data

The boundary regularity producer is local on a chart half-space.  A compact
smooth cutoff moves its H3 estimate to the whole half-space, where the
continuous weak-gradient theorem applies.  The result is an actual
continuous representative of both weak first derivatives, with no gradient
or trace premise added to the scalar construction.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareMT.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
private def scalarHalfSpace : Set Plane := {x | 0 < x.ofLp 0}
local notation "Half" => scalarHalfSpace

open Poincare.Analysis.Sobolev
open Weak Euclidean
open BoundaryTangential BoundaryLocalization

/-- A compactly supported smooth cutoff turns local H3 regularity on a half-space chart into
continuous representatives of both weak derivatives. The cutoff and the local H3 function
are retained explicitly so the result can be applied to the constructed annular correction.
Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-boundary-regularity.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem exists_continuous_halfSpace_gradient_of_local_H3
    {V : Set Plane} (hV : IsOpen V)
    {u : Plane → ℝ} (hu : MemWkp 3 2 u (V ∩ Half))
    {χ : Plane → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ V) :
    ∃ G : Fin 2 → Plane → ℝ,
      (∀ i, Continuous (G i)) ∧
      ∀ i, chosenWeakPartial' 2 i (fun z => χ z * u z) Half =ᵐ[
        volume.restrict Half] G i := by
  have hH : IsOpen Half := by
    exact isOpen_lt continuous_const (by fun_prop)
  have hcut : MemWkp 3 2 (fun z => χ z * u z) Half :=
    memWkp_mul_smooth_of_tsupport_subset 3 hH hV hu hχ hc hs
  have hcompact : HasCompactSupport (fun z => χ z * u z) := hc.mul_right
  exact scalar_halfSpace_H3_continuous_gradient hcompact hcut

end PoincareMT.M64Uniformization
