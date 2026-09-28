import PoincareMT.Proofs.M02.SmallHomologyMapMono
import PoincareMT.Proofs.M02.SmallHomologyMapEpi

/-!
# Positive-degree small-chain homology comparison
-/

set_option autoImplicit false

open CategoryTheory

universe u v

namespace PoincareMT.Proofs.M02

noncomputable section

variable {X : Type u} [TopologicalSpace X] {I : Type v}

/-- The inclusion of small integral singular chains induces an isomorphism in
every positive degree. -/
theorem integral_small_inclusion_homologyMap_isIso_succ
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (n : Nat) :
    IsIso (HomologicalComplex.homologyMap
      (PoincareMT.Proofs.M02.Topology.integralSmallChainInclusion U) (n + 1)) := by
  let f := PoincareMT.Proofs.M02.Topology.integralSmallChainInclusion U
  have : Mono (HomologicalComplex.homologyMap f (n + 1)) := by
    exact integral_small_inclusion_homologyMap_mono_succ U hU hcover n
  have : Epi (HomologicalComplex.homologyMap f (n + 1)) := by
    exact integral_small_inclusion_homologyMap_epi_succ U hU hcover n
  exact isIso_of_mono_of_epi _

end

end PoincareMT.Proofs.M02
