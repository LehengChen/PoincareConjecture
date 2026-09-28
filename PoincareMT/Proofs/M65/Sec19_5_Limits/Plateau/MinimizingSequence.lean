import PoincareMT.Definitions.Ch18.LoopSpaceWidth
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# A minimizing sequence of genuine admissible filling disks

Select actual frozen-class competitors approaching the actual filling
infimum. Their carried maps, boundary homeomorphisms, Lipschitz estimates
and Jacobian integrals are retained. This is the exact-class starting
point for Morrey ICM pp. 181-182, used in MT Lemma 19.2, pp. 437-439.
It does not assert attainment or a uniform Dirichlet-energy bound.
See M65 derivation 28.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

/-- The literal filling infimum has a sequence of actual admissible
Lipschitz disks with the displayed vanishing area errors. This precedes
normalization and energy compactness in Morrey ICM pp. 181-182; it is
not a minimum-attainment assertion. See MT Lemma 19.2 and derivation 28. -/
theorem m65Plateau_minimizingSequence (g : RiemannianMetric 3 M)
    (gamma : C1FreeLoopSpace (M := M)) (hfill : Nonempty (LipschitzSpanningDisk g gamma)) :
    ∃ disks : ℕ → LipschitzSpanningDisk g gamma,
      (∀ n, fillingArea g gamma ≤ (disks n).area ∧
        (disks n).area < fillingArea g gamma + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n => (disks n).area) atTop (𝓝 (fillingArea g gamma)) := by
  classical
  have hne : (range fun D : LipschitzSpanningDisk g gamma => D.area).Nonempty :=
    ⟨hfill.some.area, mem_range_self hfill.some⟩
  have hbelow : BddBelow (range fun D : LipschitzSpanningDisk g gamma => D.area) :=
    ⟨0, by rintro _ ⟨D, rfl⟩; exact D.area_nonnegative⟩
  have hchoose (n : ℕ) : ∃ D : LipschitzSpanningDisk g gamma,
      D.area < fillingArea g gamma + 1 / ((n : ℝ) + 1) := by
    have herr : 0 < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨_, ⟨D, rfl⟩, hD⟩ := exists_lt_of_csInf_lt hne
      (show sInf (range fun D : LipschitzSpanningDisk g gamma => D.area) <
        fillingArea g gamma + 1 / ((n : ℝ) + 1) from lt_add_of_pos_right _ herr)
    exact ⟨D, hD⟩
  choose disks hdisks using hchoose
  have hlow (n : ℕ) : fillingArea g gamma ≤ (disks n).area :=
    csInf_le hbelow (mem_range_self (disks n))
  refine ⟨disks, fun n => ⟨hlow n, hdisks n⟩, ?_⟩
  have hupp : Tendsto (fun n : ℕ => fillingArea g gamma + 1 / ((n : ℝ) + 1)) atTop
      (𝓝 (fillingArea g gamma)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := fillingArea g gamma)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupp
    hlow (fun n => (hdisks n).le)

end PoincareMT
