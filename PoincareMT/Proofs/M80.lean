import PoincareMT.Statements.M80EndpointAssembly

/-!
# M80 proof entry

This is a closed packaging adapter.  The actual endpoint mathematics belongs
to M75 and M79; M80 only stores their outputs for the final assembly.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- M80: package the supplied smooth and topological Poincare proofs as
the two exact fields of the endpoint conclusion. This is checked logical
packaging of the original propositions in `PoincareMT.Statement`, with no
additional mathematical theorem or admission. -/
theorem m80EndpointAssembly : M80EndpointAssemblyStatement.{u} := by
  intro h75 h79
  exact ⟨{ smooth := h75, topological := h79 }⟩

end PoincareMT
