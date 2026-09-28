import PoincareMT.Definitions.Ch09.NeckCapTopology
import Mathlib.Topology.Order.Compact

/-!
# Coordinate tails and compact slabs of the displayed cylinder

These facts expose the guarded coordinate calculations used in the cap/tube
collars of Morgan--Tian A.21, pp. 510-514. They use only the frozen cylinder
record and compactness of the sphere and a real closed interval. See the
cylinder-coordinate-basics-plan in the M25 task records.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M25

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} (T : OpenCylinderModel U)

/-- Tail membership uses the actual carrier and the inverse height there.
MT A.21, pp. 510-514; cylinder-coordinate-basics-plan, CY1. -/
theorem openCylinderModel_mem_tail_iff (side : Bool) {a : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (x : M) :
    x ∈ T.tail side a ↔
      x ∈ U ∧ (if side then a < (T.inverse x).2 else (T.inverse x).2 < a) := by
  have hmap {z : RoundCylinderSpace} (hz : z ∈ univ ×ˢ Ioo (0 : ℝ) 1) :
      T.coordinate z ∈ U := by
    have hm := (T.homeomorph (z.1, ⟨z.2, hz.2⟩)).property
    rwa [T.coordinate_eq] at hm
  cases side
  · change x ∈ T.coordinate '' (univ ×ˢ Ioo 0 a) ↔ x ∈ U ∧ (T.inverse x).2 < a
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzs : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
        ⟨mem_univ _, hz.2.1, hz.2.2.trans ha.2⟩
      refine ⟨hmap hzs, ?_⟩
      rw [T.left_inverse hzs]
      exact hz.2.2
    · rintro ⟨hx, hheight⟩
      exact ⟨T.inverse x, ⟨mem_univ _, (T.inverse_mem x hx).2.1, hheight⟩,
        T.right_inverse hx⟩
  · change x ∈ T.coordinate '' (univ ×ˢ Ioo a 1) ↔ x ∈ U ∧ a < (T.inverse x).2
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzs : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
        ⟨mem_univ _, ha.1.trans hz.2.1, hz.2.2⟩
      refine ⟨hmap hzs, ?_⟩
      rw [T.left_inverse hzs]
      exact hz.2.1
    · rintro ⟨hx, hheight⟩
      exact ⟨T.inverse x, ⟨mem_univ _, hheight, (T.inverse_mem x hx).2.2⟩,
        T.right_inverse hx⟩

/-- A strict cylinder tail lies in its actual carrier.
MT A.21, pp. 510-514; cylinder-coordinate-basics-plan, CY2. -/
theorem openCylinderModel_tail_subset (side : Bool) {a : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) : T.tail side a ⊆ U :=
  fun x hx => ((openCylinderModel_mem_tail_iff T side ha x).mp hx).1

/-- A closed slab with interior endpoints lies in the cylinder carrier,
including an empty slab. MT A.21, pp. 510-514; coordinate plan, CY3. -/
theorem openCylinderModel_coordinate_slab_subset {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) :
    T.coordinate '' ((Set.univ : Set UnitTwoSphere) ×ˢ Set.Icc a b) ⊆ U := by
  rintro x ⟨z, hz, rfl⟩
  have hzs : z.2 ∈ Ioo (0 : ℝ) 1 :=
    ⟨ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩
  have hm := (T.homeomorph (z.1, ⟨z.2, hzs⟩)).property
  rwa [T.coordinate_eq] at hm

/-- A retained closed slab is compact in the ambient topology, without
a Hausdorff premise. MT A.21, pp. 510-514; coordinate plan, CY4. -/
theorem openCylinderModel_isCompact_coordinate_slab {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) :
    IsCompact (T.coordinate '' ((Set.univ : Set UnitTwoSphere) ×ˢ Set.Icc a b)) := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply T.coordinate_smooth.continuousOn.mono
  intro z hz
  exact ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩

end PoincareMT.M25
