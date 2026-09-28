import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Conjugation inside an open chart

An equivalence fixing the complement of the chart source transports to
an ambient equivalence by conjugation in the chart target and the
identity elsewhere. This is the algebraic part of the compact chart
transport used in Hatcher, Notes on Basic 3-Manifold Topology, Lemma 1.3,
p. 3; see the chart-isotopy-transport derivation in the task records.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M25.Topology3D

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

omit [TopologicalSpace X] in
/-- An equivalence fixing the complement of a set preserves that set. -/
theorem equiv_mapsTo_of_fixed_compl (f : X ≃ X) {S : Set X}
    (hf : ∀ x ∉ S, f x = x) : MapsTo f S S := by
  intro x hx
  by_contra hfx
  have heq : f x = x := f.injective (hf (f x) hfx)
  exact hfx (heq.symm ▸ hx)

omit [TopologicalSpace X] in
/-- A point fixed by an equivalence is also fixed by its inverse. -/
theorem equiv_symm_fixed_of_fixed (f : X ≃ X) {x : X} (hx : f x = x) : f.symm x = x := by
  apply f.injective
  rw [f.apply_symm_apply, hx]

/-- Chart conjugation is defined on the target and extended by the
identity outside. Its total values use the inverse only in the target. -/
noncomputable def chartConjugateMap (e : OpenPartialHomeomorph X Y) (f : X → X) : Y → Y := by
  classical
  exact fun y => if y ∈ e.target then e (f (e.symm y)) else y

/-- On the chart target, conjugation has its usual coordinate formula. -/
theorem chartConjugateMap_of_mem (e : OpenPartialHomeomorph X Y) (f : X → X)
    {y : Y} (hy : y ∈ e.target) : chartConjugateMap e f y = e (f (e.symm y)) := by
  classical
  simp only [chartConjugateMap, if_pos hy]

/-- The conjugated map agrees with the transported map on the source. -/
theorem chartConjugateMap_apply_chart (e : OpenPartialHomeomorph X Y) (f : X → X)
    {x : X} (hx : x ∈ e.source) : chartConjugateMap e f (e x) = e (f x) := by
  rw [chartConjugateMap_of_mem e f (e.map_source hx), e.left_inv hx]

/-- Conjugation moves no points outside the image of a common support. -/
theorem chartConjugateMap_eq_self (e : OpenPartialHomeomorph X Y) (f : X → X)
    {C : Set X} (hf : ∀ x ∉ C, f x = x) {y : Y} (hy : y ∉ e '' C) :
    chartConjugateMap e f y = y := by
  classical
  by_cases hyt : y ∈ e.target
  · have hx : e.symm y ∉ C := fun h => hy ⟨e.symm y, h, e.right_inv hyt⟩
    rw [chartConjugateMap_of_mem e f hyt, hf _ hx, e.right_inv hyt]
  · simp only [chartConjugateMap, if_neg hyt]

/-- Two source-preserving inverse maps remain inverses after chart
conjugation and identity extension. -/
theorem chartConjugateMap_leftInverse (e : OpenPartialHomeomorph X Y)
    (f g : X → X) (hf : MapsTo f e.source e.source) (hg : Function.LeftInverse g f) :
    Function.LeftInverse (chartConjugateMap e g) (chartConjugateMap e f) := by
  classical
  intro y
  by_cases hy : y ∈ e.target
  · rw [chartConjugateMap_of_mem e f hy,
      chartConjugateMap_apply_chart e g (hf (e.map_target hy)), hg, e.right_inv hy]
  · simp only [chartConjugateMap, if_neg hy]

/-- An equivalence preserving the chart source in both directions
extends by chart conjugation to an ambient equivalence. -/
noncomputable def chartConjugateEquiv (e : OpenPartialHomeomorph X Y) (f : X ≃ X)
    (hf : MapsTo f e.source e.source) (hi : MapsTo f.symm e.source e.source) : Y ≃ Y where
  toFun := chartConjugateMap e f
  invFun := chartConjugateMap e f.symm
  left_inv := chartConjugateMap_leftInverse e f f.symm hf f.symm_apply_apply
  right_inv := chartConjugateMap_leftInverse e f.symm f hi f.apply_symm_apply

end PoincareMT.M25.Topology3D
