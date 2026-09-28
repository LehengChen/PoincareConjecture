import PoincareMT.Proofs.M02.HurewiczRepresentatives
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Hurewicz injectivity adapter

An explicit zero integral homology object and an explicit injective Hurewicz
map force the corresponding positive homotopy group to be subsingleton.
-/

set_option autoImplicit false

open CategoryTheory Limits

universe w

namespace PoincareMT.Proofs.M02

/-- An explicitly injective integral Hurewicz map into a zero homology object
forces the source homotopy group to be subsingleton. -/
theorem subsingleton_homotopyGroupPi_of_integral_hurewicz_injective_isZero
    (X : TopCat.{w}) (n : ℕ) (x : X)
    (hzero : IsZero ((TopCat.toSSet.obj X).homology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)))
    (hinj : Function.Injective
      (homotopyGroupSingularHomologyMap
        (ModuleCat.of ℤ (ULift.{w} ℤ)) X n x)) :
    Subsingleton (HomotopyGroup.Pi (n + 1) X x) := by
  constructor
  intro a b
  apply hinj
  exact hzero.eq_of_tgt _ _

end PoincareMT.Proofs.M02
