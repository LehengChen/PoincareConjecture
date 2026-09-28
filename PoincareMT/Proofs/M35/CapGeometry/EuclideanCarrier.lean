import PoincareMT.Proofs.M35.CapGeometry.CarrierTopology

/-!
# The actual Euclidean parametrization of a cap carrier

Morgan-Tian Definition 9.72 and Theorem 12.32, pp. 326-327.
The frozen Euclidean cap model supplies both smooth global coordinate
maps required by the final standard-cap carrier. This says nothing
extra about its designated closed core.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.CapModelEquivalence

/-- Theorem 12.32: the Euclidean cap model yields the exact global
carrier map, inverse, and both smoothness directions of the final cap. -/
theorem exists_euclidean_parametrization
    {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {p : RealProjectiveThree} {U : Set M} (C : CapModelEquivalence .euclidean p U) :
    ∃ f : StandardCapSpace → M, ∃ inv : M → StandardCapSpace,
      range f = U ∧ Function.LeftInverse inv f ∧ LeftInvOn f inv U ∧
      ContMDiff (𝓡 3) (𝓡 3) ∞ f ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ inv U := by
  let : TopologicalSpace C.model := C.model_topology
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.model := C.model_charted
  have : IsManifold (𝓡 3) ∞ C.model := C.model_manifold
  obtain ⟨e⟩ := C.standard_smooth
  let f : StandardCapSpace → M := C.inverse ∘ e.symm
  let inv : M → StandardCapSpace := e ∘ C.forward
  refine ⟨f, inv, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact C.inverse_mem (e.symm y)
    · intro hx
      refine ⟨e (C.forward x), ?_⟩
      change C.inverse (e.symm (e (C.forward x))) = x
      rw [e.symm_apply_apply, C.left_inverse x hx]
  · intro y
    change e (C.forward (C.inverse (e.symm y))) = y
    rw [C.right_inverse, e.apply_symm_apply]
  · intro x hx
    change C.inverse (e.symm (e (C.forward x))) = x
    rw [e.symm_apply_apply, C.left_inverse x hx]
  · exact (contMDiffOn_univ.mp C.inverse_smooth).comp e.symm.contMDiff
  · exact e.contMDiff.comp_contMDiffOn C.forward_smooth

end PoincareMT.CapModelEquivalence
