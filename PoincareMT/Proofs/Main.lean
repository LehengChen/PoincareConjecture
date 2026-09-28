import PoincareMT.Proofs.M90

/-!
The checked M90 suppliers assemble both original Mathlib-only endpoints from
the numbered milestone skeleton. The smooth branch applies M75 directly;
the topological branch projects the final package. Main has no predecessor-package argument
and no admission of its own. Earlier inventoried milestone admissions remain;
this is a formalization skeleton, not a completed proof without admissions.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Every compact Hausdorff second-countable simply connected smooth
three-manifold is diffeomorphic to the standard three-sphere. Source:
Morgan--Tian Corollary 0.2(a), assembled through the numbered skeleton. -/
theorem smoothPoincareSkeleton : SmoothPoincare.{u} := by
  exact m75SmoothPoincare m90SmoothEndpointInputs

/-- Every compact Hausdorff second-countable simply connected topological
three-manifold is homeomorphic to the standard three-sphere. Apply smooth
Poincare through M76's compatible smoothing and the checked M77--M90 route;
no smoothness hypothesis is imposed on the original manifold. -/
theorem topologicalPoincareSkeleton : TopologicalPoincare.{u} := by
  obtain ⟨C⟩ := m90FinalAssemblyFromMilestones.{u}
  exact C.topological

end PoincareMT
