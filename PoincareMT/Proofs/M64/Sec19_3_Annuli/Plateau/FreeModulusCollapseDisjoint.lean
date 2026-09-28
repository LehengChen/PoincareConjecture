import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusCollapseTrace

/-!
# Disjointness excludes a common trace in the zero-modulus branch

The Helly collapse theorem only gives equality of the two limiting traces
almost everywhere on one positive-length period.  This file records the exact
measure-theoretic consequence needed by the free-boundary consumers: if the
original curve images are disjoint, that AE equality is impossible.  No
continuity or full-image equality of the monotone limiting labels is used.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareMT.M64

/-- Disjoint curve images exclude almost-everywhere equality of any two traces on a
positive-length period. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem not_ae_common_trace_of_disjoint_periodic_images
    {X : Type*} {P : ℝ} (hP : 0 < P)
    {c0 c1 : ℝ → X}
    (hdisjoint : Disjoint (range c0) (range c1))
    {L0 L1 : ℝ → ℝ}
    (hcommon : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) P), c0 (L0 x) = c1 (L1 x)) :
    False := by
  obtain ⟨x, hxI, htrace⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (show volume (Icc (0 : ℝ) P) ≠ 0 by
      rw [Real.volume_Icc]
      exact (ENNReal.ofReal_pos.mpr (by simpa using hP)).ne') hcommon
  exact Set.disjoint_left.mp hdisjoint
    (show c0 (L0 x) ∈ range c0 from ⟨L0 x, rfl⟩)
    ⟨L1 x, htrace.symm⟩

end PoincareMT.M64
