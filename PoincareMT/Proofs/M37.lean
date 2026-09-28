import PoincareMT.Statements.M37SurgeryFlow

/-!
# M37 logical surgery-flow compatibility adapter

The supplied compatibility record already contains every field of the
returned package. This entry copies those fields without constructing a flow,
performing surgery, or proving continuation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-
Fix the M36 and M33 services S and B, an actual changing-carrier surgery flow
F, and a compatibility witness W for those same objects. Return W's surgery
data, its equality to F, its equality to the selected M36 result, and its
exact M33 branch application as a RepairedSurgeryFlowPackage. The proof is
fieldwise identity; it does not establish the availability of W or strengthen
the event-operation alignment assumed by W.

This is a logical adapter, not an independent Morgan--Tian theorem. The
inherited geometric vocabulary comes from Definition 15.5 (printed p. 359),
Assumptions (1)--(7) (pp. 354--357), Definition 15.8 (pp. 361--362), and
Lemma 15.11 (p. 364). The global existence assertion of Theorem 15.9
(pp. 363--364) remains a separate obligation. Applicable source corrections
are recorded in `reviews/errata/2026-09-10-surgery-extinction-audit.md`.
-/
theorem repairedSurgeryFlow : RepairedSurgeryFlowTheory.{u} := by
  refine ⟨?_⟩
  intro S B F compatibility
  exact ⟨{
    data := compatibility.data.toRepairedSurgeryFlowData
    flow_eq := compatibility.flow_eq
    compatibility_data := compatibility.data
    core_eq := rfl
    metric_surgery_source := compatibility.metric_surgery_source
    branch_application := compatibility.branch_application
  }⟩

end PoincareMT
