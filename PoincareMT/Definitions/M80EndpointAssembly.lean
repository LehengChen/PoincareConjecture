import PoincareMT.Statement

/-!
# M80 endpoint assembly adapter

M80 packages the two independently produced primitive endpoint propositions.
It performs no mathematical proof and introduces no new endpoint premise.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

structure M80EndpointConclusion where
  smooth : SmoothPoincare.{u}
  topological : TopologicalPoincare.{u}

end PoincareMT
