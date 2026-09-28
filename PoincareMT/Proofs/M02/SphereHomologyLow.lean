import PoincareMT.Proofs.M02.HurewiczRepresentatives
import PoincareMT.Proofs.M02.SphereConnectivity
import PoincareMT.Statement

/-!
# Low-dimensional integral homology of the standard three-sphere

The sphere connectivity construction supplies the vanishing homotopy groups
needed by the integral Hurewicz representative theorem.  This file records
the resulting first and second homology vanishing without introducing any
duality or classification premise.
-/

set_option autoImplicit false

open CategoryTheory Limits

namespace PoincareMT.Proofs.M02

noncomputable section

open PoincareMT

private noncomputable abbrev threeSphereType :=
  PoincareMT.ThreeSphere

private noncomputable abbrev threeSphereBasepoint : TopCat :=
  TopCat.of threeSphereType

private noncomputable abbrev threeSpherePoint : threeSphereType :=
  Classical.choice (NormedSpace.sphere_nonempty.mpr zero_le_one).coe_sort

/-- The first integral singular homology of the standard three-sphere is zero. -/
theorem isZero_integral_threeSphere_homology_one :
      IsZero ((TopCat.toSSet.obj threeSphereBasepoint).homology
      (ModuleCat.of ℤ (ULift ℤ)) 1) := by
  let : SimplyConnectedSpace threeSphereType :=
    sphere_simplyConnectedSpace_of_two_lt_finrank (E := EuclideanSpace ℝ (Fin 4)) (by simp)
  exact isZero_integral_singularHomology_of_homotopy_vanishing
    threeSphereBasepoint threeSpherePoint 0 (by
      intro k hk hk1
      have hk' : k = 1 := by omega
      subst k
      exact sphere_homotopyGroup_subsingleton_of_dim_lt
        (N := Fin 1) (E := EuclideanSpace ℝ (Fin 4)) (by simp) threeSpherePoint)

/-- The second integral singular homology of the standard three-sphere is zero. -/
theorem isZero_integral_threeSphere_homology_two :
      IsZero ((TopCat.toSSet.obj threeSphereBasepoint).homology
      (ModuleCat.of ℤ (ULift ℤ)) 2) := by
  let : SimplyConnectedSpace threeSphereType :=
    sphere_simplyConnectedSpace_of_two_lt_finrank (E := EuclideanSpace ℝ (Fin 4)) (by simp)
  exact isZero_integral_singularHomology_of_homotopy_vanishing
    threeSphereBasepoint threeSpherePoint 1 (by
      intro k hk hk2
      rcases k with _ | k
      · omega
      · rcases k with _ | k
        · exact sphere_homotopyGroup_subsingleton_of_dim_lt
            (N := Fin 1) (E := EuclideanSpace ℝ (Fin 4)) (by simp) threeSpherePoint
        · rcases k with _ | k
          · exact sphere_homotopyGroup_subsingleton_of_dim_lt
              (N := Fin 2) (E := EuclideanSpace ℝ (Fin 4)) (by simp) threeSpherePoint
          · omega)

end

end PoincareMT.Proofs.M02
