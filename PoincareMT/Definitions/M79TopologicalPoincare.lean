import PoincareMT.Statements.M76SmoothingBridge
import PoincareMT.Statements.M77Transport
import PoincareMT.Statements.M78EndpointTransport
import PoincareMT.Statement

/-!
# M79 universal topological endpoint assembly

M79 is a checked composition boundary.  It introduces the primitive
topological Poincare variables and applies the separately reviewed M76--M78
services; it does not admit or repackage an endpoint as an input.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

def M79TopologicalPoincareStatement : Prop :=
  ∀ (_h76 : M76SmoothingStatement.{u})
    (_h77 : M77TransportStatement.{u})
    (_h75 : SmoothPoincare.{u})
    (_h78 : M78EndpointTransportStatement.{u}),
    TopologicalPoincare.{u}

end PoincareMT
