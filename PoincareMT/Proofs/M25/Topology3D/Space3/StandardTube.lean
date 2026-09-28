import PoincareMT.Proofs.M25.Topology3D.Services
import PoincareMT.Proofs.M25.Topology3D.Space3.CompactChart
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Standard tube charts from the planar service

The chart in the single-curve planar service extends smoothly past the
closed disc and has a smooth inverse. Its product with the height coordinate
provides the standard horizontal disc neighborhoods needed in Hatcher,
Notes on Basic 3-Manifold Topology, Lemmas 1.2-1.3, pp. 2-3.

This constructs a product neighborhood, not the general Alexander theorem.
See `proof-work/tasks/M25/schoenflies/derivations/2026-09-21-standard-tube.md`.
-/

set_option autoImplicit false

open scoped ContDiff
open Set Metric

namespace PoincareMT.M25.Topology3D
namespace PlanarSchoenfliesData

variable {c : UnitCircle → E2} (D : PlanarSchoenfliesData c)

/-- The planar service chart as an open partial homeomorphism. The supplied
left inverse is a two-sided inverse on the image; Hatcher, Lemma 1.2, p. 2. -/
noncomputable def discChart : OpenPartialHomeomorph E2 E2 where
  toFun := D.chart
  invFun := Classical.choose D.chart_inverse
  source := ball 0 D.radius
  target := D.chart '' ball 0 D.radius
  map_source' := fun x hx => mem_image_of_mem D.chart hx
  map_target' := by
    rintro y ⟨x, hx, rfl⟩
    simpa only [(Classical.choose_spec D.chart_inverse).2 x hx] using hx
  left_inv' := (Classical.choose_spec D.chart_inverse).2
  right_inv' := by
    rintro y ⟨x, hx, rfl⟩
    rw [(Classical.choose_spec D.chart_inverse).2 x hx]
  open_source := isOpen_ball
  open_target := D.chart_open_map
  continuousOn_toFun := D.chart_smooth.continuousOn
  continuousOn_invFun := (Classical.choose_spec D.chart_inverse).1.continuousOn

/-- The partial homeomorphism has the original forward map. -/
@[simp] theorem discChart_apply (x : E2) : D.discChart x = D.chart x := rfl

/-- The planar chart is defined on a ball strictly larger than the unit disc. -/
@[simp] theorem discChart_source : D.discChart.source = ball 0 D.radius := rfl

/-- The target is exactly the image of the larger ball. -/
@[simp] theorem discChart_target :
    D.discChart.target = D.chart '' ball 0 D.radius := rfl

/-- Smoothness of the forward planar neighborhood chart. -/
theorem discChart_contDiffOn : ContDiffOn ℝ ∞ D.discChart D.discChart.source :=
  D.chart_smooth

/-- Smoothness of the inverse planar neighborhood chart. -/
theorem discChart_symm_contDiffOn :
    ContDiffOn ℝ ∞ D.discChart.symm D.discChart.target :=
  (Classical.choose_spec D.chart_inverse).1

/-- The entire closed attaching disc lies in the open chart domain. -/
theorem closedBall_subset_discChart_source : closedBall 0 1 ⊆ D.discChart.source :=
  closedBall_subset_ball D.one_lt_radius

/-- The image of the standard boundary circle is exactly the prescribed
curve, including its parametrization; Hatcher, Theorem 1.1, pp. 1-2. -/
theorem discChart_image_sphere : D.discChart '' sphere 0 1 = range c := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, (D.chart_boundary ⟨x, hx⟩).symm⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, q.2, D.chart_boundary q⟩

/-- The filled closed disc consists of the inside and its prescribed
boundary curve; Hatcher's surgery discs, Theorem 1.1, pp. 1-2. -/
theorem discChart_image_closedBall :
    D.discChart '' closedBall 0 1 = D.inside ∪ range c := by
  rw [← ball_union_sphere, image_union, D.discChart_image_sphere]
  change D.chart '' ball 0 1 ∪ range c = D.inside ∪ range c
  rw [D.chart_image_inside]

/-- The inside's closure is exactly the image of the standard closed disc. -/
theorem closure_inside_eq_discChart_image :
    closure D.inside = D.discChart '' closedBall 0 1 := by
  rw [← D.chart_image_inside]
  exact compactChart_closure_ball D.discChart 0 zero_lt_one
    D.closedBall_subset_discChart_source

/-- The frontier of the bounded inside is exactly the prescribed curve. -/
theorem frontier_inside_eq_range : frontier D.inside = range c := by
  rw [← D.chart_image_inside, ← D.discChart_image_sphere]
  exact compactChart_frontier_ball D.discChart 0 zero_lt_one
    D.closedBall_subset_discChart_source

/-- The product chart extends through every horizontal cap level. This is
the fixed-disc tube model in Hatcher, Lemma 1.2, pp. 2-3. -/
noncomputable def cylinderChart : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ) :=
  D.discChart.prod (OpenPartialHomeomorph.refl ℝ)

/-- Product coordinates preserve the height exactly. -/
@[simp] theorem cylinderChart_apply (p : E2 × ℝ) :
    D.cylinderChart p = (D.chart p.1, p.2) := rfl

/-- The tube chart has a uniform disc domain at every height. -/
@[simp] theorem cylinderChart_source :
    D.cylinderChart.source = ball 0 D.radius ×ˢ (univ : Set ℝ) := rfl

/-- The tube chart covers the product of its planar target with all heights. -/
@[simp] theorem cylinderChart_target :
    D.cylinderChart.target = (D.chart '' ball 0 D.radius) ×ˢ (univ : Set ℝ) := rfl

/-- Joint smoothness of the tube coordinates, including at horizontal caps. -/
theorem cylinderChart_contDiffOn :
    ContDiffOn ℝ ∞ D.cylinderChart D.cylinderChart.source :=
  D.discChart_contDiffOn.prodMap contDiff_id.contDiffOn

/-- Joint smoothness of the inverse tube coordinates. -/
theorem cylinderChart_symm_contDiffOn :
    ContDiffOn ℝ ∞ D.cylinderChart.symm D.cylinderChart.target :=
  D.discChart_symm_contDiffOn.prodMap contDiff_id.contDiffOn

/-- On a horizontal boundary circle, the product chart agrees with the
prescribed curve parametrization; Hatcher, Theorem 1.1, pp. 1-2. -/
theorem cylinderChart_boundary (q : UnitCircle) (z : ℝ) :
    D.cylinderChart (q.1, z) = (c q, z) := by
  simp only [cylinderChart_apply, D.chart_boundary]

/-- The filled open tube is the image of the standard open-disc product.
This equality also applies to singleton cap levels and empty height sets. -/
theorem cylinderChart_image_inside (s : Set ℝ) :
    D.cylinderChart '' (ball 0 1 ×ˢ s) = D.inside ×ˢ s := by
  change Prod.map D.chart id '' (ball 0 1 ×ˢ s) = D.inside ×ˢ s
  rw [prodMap_image_prod, D.chart_image_inside, image_id]

end PlanarSchoenfliesData
end PoincareMT.M25.Topology3D
