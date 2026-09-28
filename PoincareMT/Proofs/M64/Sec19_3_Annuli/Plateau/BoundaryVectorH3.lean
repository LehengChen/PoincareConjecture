import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarHalfSpaceGradient

/-!
# Vector-valued boundary H3 columns

The scalar half-space Sobolev theorem is coordinatewise.  This file packages
its actual continuous representatives into one Euclidean target column field,
which can be consumed by the reflected C1 bridge.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryTangential

namespace PoincareMT

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Half" => BoundaryTangential.halfSpace 2

/-- Coordinatewise H3 data on a half-space has one continuous representative for each weak
derivative column. The construction is coordinatewise, but the result is a single
Euclidean-valued field, so its columns can be used in the vector mollifier regularity
theorem. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis.
Project derivation: `proof-work/tasks/M64/reports/2026-09-25-boundary-vector-h3.md`. -/
theorem m64Vector_halfSpace_H3_continuous_gradient
    {m : ℕ} {u : Plane → EuclideanSpace ℝ (Fin m)}
    (hc : HasCompactSupport u)
    (hu : ∀ b : Fin m, Euclidean.MemWkp 3 2 (fun x => u x b) Half) :
    ∃ G : Fin 2 → Plane → EuclideanSpace ℝ (Fin m),
      (∀ i, Continuous (G i)) ∧
      ∀ i b, chosenWeakPartial' 2 i (fun x => u x b) Half =ᵐ[
        volume.restrict Half] (fun x => G i x b) := by
  have hcoord (b : Fin m) : HasCompactSupport (fun x => u x b) := by
    have hcomp := hc.comp_left (EuclideanSpace.proj (𝕜 := ℝ) b).map_zero
    change HasCompactSupport ((EuclideanSpace.proj (𝕜 := ℝ) b) ∘ u)
    exact hcomp
  choose G hGc hG using fun b : Fin m =>
    M64Uniformization.scalar_halfSpace_H3_continuous_gradient (hcoord b) (hu b)
  let V : Fin 2 → Plane → EuclideanSpace ℝ (Fin m) := fun i x =>
    WithLp.toLp 2 (fun b => G b i x)
  have hVc (i : Fin 2) : Continuous (V i) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp
    apply continuous_pi
    intro b
    exact (hGc b i).comp continuous_id
  refine ⟨V, hVc, ?_⟩
  intro i b
  simpa only [V] using hG b i

end PoincareMT
