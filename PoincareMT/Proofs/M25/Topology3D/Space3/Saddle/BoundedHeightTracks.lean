import PoincareMT.Proofs.M25.Topology3D.Space3.ClockFlow
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Uniform signed height tracks from a compact safe set

A global norm bound controls displacement before any height equation
is used. Compact containment then yields a common positive and negative
time interval of unit-height tracks. These are the bounded transport
steps in Hatcher, Notes on Basic 3-Manifold Topology, Lemma 1.2, pp. 2-3,
as specified in the reviewed saddle transport-core inventory.
-/

set_option autoImplicit false

open Set Metric
open scoped NNReal

namespace PoincareMT.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A bounded field controls displacement for every initial point and
every signed time. Source: Hatcher, Lemma 1.2, pp. 2-3, bounded transport. -/
theorem boundedFlow_norm_sub_le (F : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K F) (hL : ∀ y, ‖F y‖ ≤ L) (y : E) (t : ℝ) :
    ‖boundedFlow F hK hL y t - y‖ ≤ (L : ℝ) * |t| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (univ : Set ℝ))
    (fun s _ => (boundedFlow_hasDerivAt F hK hL y s).hasDerivWithinAt)
    (fun s _ => hL (boundedFlow F hK hL y s)) (convex_univ : Convex ℝ (univ : Set ℝ))
    (mem_univ (0 : ℝ)) (mem_univ t)
  simpa only [boundedFlow_zero, sub_zero, Real.norm_eq_abs] using h

/-- A compact safe set in an open unit-speed region has one common
interval of positive and negative unit-height tracks in that region.
Only the safe set is compact; the invariant carrier may be arbitrary.
Source: Hatcher, Lemma 1.2, pp. 2-3, bounded relative transport. -/
theorem exists_boundedFlow_unit_height_interval (F : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K F) (hL : ∀ y, ‖F y‖ ≤ L)
    (H : E →L[ℝ] ℝ) {S A U : Set E}
    (hA : IsCompact A) (hU : IsOpen U) (hASU : A ⊆ S ∩ U)
    (hS : ∀ y ∈ S, ∀ t : ℝ, boundedFlow F hK hL y t ∈ S)
    (hunit : ∀ y ∈ S ∩ U, H (F y) = 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ y ∈ A, ∀ t : ℝ, |t| ≤ τ →
      boundedFlow F hK hL y t ∈ U ∧
      H (boundedFlow F hK hL y t) = H y + t := by
  obtain ⟨η, hη, hηU⟩ := hA.exists_thickening_subset_open hU
    (fun _ hy => (hASU hy).2)
  let τ := η / (2 * ((L : ℝ) + 1))
  have hden : 0 < 2 * ((L : ℝ) + 1) := by positivity
  have hτ : 0 < τ := div_pos hη hden
  have hτmul : τ * (2 * ((L : ℝ) + 1)) = η := div_mul_cancel₀ η hden.ne'
  have hLτ : (L : ℝ) * τ < η := by
    nlinarith [mul_nonneg L.coe_nonneg hτ.le]
  have hstay (y : E) (hy : y ∈ A) (t : ℝ) (ht : |t| ≤ τ) :
      boundedFlow F hK hL y t ∈ U := by
    apply hηU
    apply mem_thickening_iff.mpr
    refine ⟨y, hy, ?_⟩
    rw [dist_eq_norm]
    exact (boundedFlow_norm_sub_le F hK hL y t).trans_lt
      ((mul_le_mul_of_nonneg_left ht L.coe_nonneg).trans_lt hLτ)
  refine ⟨τ, hτ, ?_⟩
  intro y hy t ht
  refine ⟨hstay y hy t ht, ?_⟩
  have hd (s : ℝ) (hs : s ∈ Icc (-τ) τ) : HasDerivAt
      (fun r => H (boundedFlow F hK hL y r) - r) 0 s := by
    have hflow : boundedFlow F hK hL y s ∈ S ∩ U :=
      ⟨hS y (hASU hy).1 s, hstay y hy s (abs_le.mpr hs)⟩
    have hH := H.hasFDerivAt.comp_hasDerivAt s (boundedFlow_hasDerivAt F hK hL y s)
    convert! hH.sub (hasDerivAt_id s) using 1
    simp only [hunit _ hflow, sub_self]
  have hzero : ‖(H (boundedFlow F hK hL y t) - t) -
      (H (boundedFlow F hK hL y 0) - 0)‖ ≤ 0 := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hd s hs).hasDerivWithinAt)
      (fun _ _ => show ‖(0 : ℝ)‖ ≤ 0 by simp) (convex_Icc (-τ) τ)
      (show (0 : ℝ) ∈ Icc (-τ) τ from ⟨by linarith, hτ.le⟩) (abs_le.mp ht)
    simpa only [zero_mul] using h
  have heq := sub_eq_zero.mp (norm_le_zero_iff.mp hzero)
  simp only [boundedFlow_zero, sub_zero] at heq
  linarith

/-- The planar part of a bounded clock flow has the same signed-time
displacement bound. Source: Hatcher, Lemma 1.2, pp. 2-3, bounded transport. -/
theorem clockEvolution_norm_sub_le (V : ℝ × E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K (clockField V)) (hL : ∀ p, ‖clockField V p‖ ≤ L)
    (s t : ℝ) (x : E) :
    ‖clockEvolution V hK hL s t x - x‖ ≤ (L : ℝ) * |t - s| := by
  exact (norm_snd_le (boundedFlow (clockField V) hK hL (s, x) (t - s) - (s, x))).trans
    (boundedFlow_norm_sub_le (clockField V) hK hL (s, x) (t - s))

end PoincareMT.M25.Topology3D
