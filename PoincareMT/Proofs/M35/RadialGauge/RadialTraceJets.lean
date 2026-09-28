import PoincareMT.Proofs.M35.RadialGauge.RadialProfileCalculus
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Actual radial trace jets of the Euclidean solution

Morgan-Tian pp. 316-320. Restricting along a unit ray controls every
ordinary radial derivative by the actual Euclidean Frechet jet. Thus
the proved closed-slab weighted estimates and derivative tails apply
to the actual logarithmic displacement used in the radius map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace PoincareMT.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

/-- Actual ordinary radial derivatives are bounded by the actual
Euclidean jet, including at the tip and on the negative ray. -/
theorem radialTrace_iteratedDeriv_norm_le {u : V → ℝ} (hu : ContDiff ℝ ∞ u)
    {e : V} (he : ‖e‖ = 1) (j : ℕ) (r : ℝ) :
    |iteratedDeriv j (fun s : ℝ => u (s • e)) r| ≤
      ‖iteratedFDeriv ℝ j u (r • e)‖ := by
  let I : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight e
  have h := I.iteratedFDeriv_comp_right hu r
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
  change iteratedFDeriv ℝ j (fun s : ℝ => u (s • e)) r = _ at h
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, h]
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro v
  change ‖iteratedFDeriv ℝ j u (r • e) (fun i => v i • e)‖ ≤ _
  simpa only [norm_smul, he, mul_one] using
    (iteratedFDeriv ℝ j u (r • e)).le_opNorm (fun i => v i • e)

/-- The corrected weight is unchanged by restriction to a unit ray. -/
theorem radialTrace_weighted_jet_le {u : V → ℝ} (hu : ContDiff ℝ ∞ u)
    {e : V} (he : ‖e‖ = 1) (j : ℕ) (r : ℝ) :
    (1 + |r|) * |iteratedDeriv j (fun s : ℝ => u (s • e)) r| ≤
      (1 + ‖r • e‖) * ‖iteratedFDeriv ℝ j u (r • e)‖ := by
  simpa only [norm_smul, Real.norm_eq_abs, he, mul_one] using
    mul_le_mul_of_nonneg_left (radialTrace_iteratedDeriv_norm_le hu he j r)
      (show 0 ≤ 1 + |r| by positivity)

/-- Uniform little-o jet bounds on a Euclidean end yield the same
bounds for the actual radial trace on the entire parameter family. -/
theorem radialTrace_weighted_jet_vanishes_uniformly
    {A : Type*} {u : A → V → ℝ} (hu : ∀ a, ContDiff ℝ ∞ (u a))
    {e : V} (he : ‖e‖ = 1) (j : ℕ)
    (hend : ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ, 0 ≤ R ∧
      ∀ a x, R ≤ ‖x‖ → (1 + ‖x‖) * ‖iteratedFDeriv ℝ j (u a) x‖ ≤ epsilon) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ, 0 ≤ R ∧
      ∀ a r, R ≤ |r| →
        (1 + |r|) * |iteratedDeriv j (fun s : ℝ => u a (s • e)) r| ≤ epsilon := by
  intro epsilon hepsilon
  obtain ⟨R, hR, hb⟩ := hend epsilon hepsilon
  refine ⟨R, hR, fun a r hr => ?_⟩
  apply (radialTrace_weighted_jet_le (hu a) he j r).trans
  apply hb a (r • e)
  simpa only [norm_smul, Real.norm_eq_abs, he, mul_one] using hr

end PoincareMT.M35.RadialGauge
