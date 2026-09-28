import PoincareMT.Proofs.M25.Topology3D.Space3.CircleRadialChart
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Uniform neighborhoods for surgery formulas

Compactness makes a neighborhood of a zero level contain a uniform
height band, and a neighborhood of the unit circle contain a uniform
radial band. These are the parameter choices before equations (6)-(8)
in the reviewed regular-disc-surgery derivation of 2026-09-22, following
Hatcher, Notes on Basic 3-Manifold Topology, Theorem 1.1, pp. 1-3.
-/

set_option autoImplicit false

open Set Metric Filter
open scoped Topology

namespace PoincareMT.M25.Topology3D

/-- A neighborhood of the full zero level of a continuous function on
a compact space contains one uniform open band about zero. -/
theorem exists_uniform_zero_level_band
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (h : X → ℝ) (hh : Continuous h) {U : Set X} (hU : IsOpen U)
    (hz : {x | h x = 0} ⊆ U) :
    ∃ d > (0 : ℝ), ∀ x, |h x| < d → x ∈ U := by
  have hc : IsClosed (h '' Uᶜ) := (hU.isClosed_compl.isCompact.image hh).isClosed
  have hzero : (0 : ℝ) ∈ (h '' Uᶜ)ᶜ := by
    rintro ⟨x, hx, hx0⟩
    exact hx (hz hx0)
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp (hc.isOpen_compl.mem_nhds hzero)
  refine ⟨d, hd, ?_⟩
  intro x hx
  by_contra hn
  apply hball (show h x ∈ ball 0 d by simpa [Real.dist_eq] using hx)
  exact ⟨x, hn, rfl⟩

/-- An open neighborhood of a closed upper half contains a slightly
larger open upper half. No regularity of the zero level is needed. -/
theorem exists_uniform_upper_level_band
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (h : X → ℝ) (hh : Continuous h) {U : Set X} (hU : IsOpen U)
    (hz : {x | 0 ≤ h x} ⊆ U) :
    ∃ d > (0 : ℝ), ∀ x, -d < h x → x ∈ U := by
  obtain ⟨d, hd, hb⟩ := exists_uniform_zero_level_band h hh hU
    (fun x hx => hz (by change h x = 0 at hx; simp [hx]))
  refine ⟨d, hd, ?_⟩
  intro x hx
  by_cases hpos : 0 ≤ h x
  · exact hz hpos
  · exact hb x (abs_lt.mpr ⟨hx, lt_trans (lt_of_not_ge hpos) hd⟩)

/-- A set-neighborhood of the unit circle contains every point whose
norm is sufficiently close to one. Direction at zero is harmless. -/
theorem exists_circle_radial_band {P : E2 → Prop}
    (hP : ∀ᶠ x in 𝓝ˢ (sphere (0 : E2) 1), P x) :
    ∃ d > (0 : ℝ), ∀ x : E2, |‖x‖ - 1| < d → P x := by
  obtain ⟨d, hd, hband⟩ :=
    (Metric.hasBasis_nhdsSet_thickening (isCompact_sphere (0 : E2) 1)).mem_iff.mp hP
  refine ⟨d, hd, fun x hx => hband ?_⟩
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(circleDirection x : E2), (circleDirection x).2, ?_⟩
  rw [dist_eq_norm]
  have he : x - (circleDirection x : E2) =
      (‖x‖ - 1) • (circleDirection x : E2) := by
    rw [sub_smul, one_smul, circleDirection_norm_smul]
  rw [he, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one]
  exact hx

end PoincareMT.M25.Topology3D
