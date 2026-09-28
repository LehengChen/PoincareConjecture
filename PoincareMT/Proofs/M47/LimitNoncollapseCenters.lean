import PoincareMT.Proofs.M47.LimitNoncollapseWorldlines

/-!
# Literal source-center identities

The convergence center and every finite-slab center are compared as actual
dependent spacetime points.  The inverse of the selected cylinder supplies
injectivity on its open source; no center matching premise is added.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

/-- A literal point-map equality at one cylinder time is injective on the
actual open source. -/
theorem limitNoncollapse_pointMap_injective_at
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (s : ℝ) (hs : s ∈ I) {x y : C.carrier}
    (hx : x ∈ U) (hy : y ∈ U)
    (hxy : e.pointMap s hs x = e.pointMap s hs y) : x = y := by
  have hsp : e.forward s hs x = e.forward s hs y := by
    exact eq_of_heq (Sigma.mk.inj_iff.mp hxy).2
  calc
    x = e.inverse s hs (e.forward s hs x) := (e.left_inverse s hs hx).symm
    _ = e.inverse s hs (e.forward s hs y) := by rw [hsp]
    _ = y := e.left_inverse s hs hy

/-- The selected convergence embedding retains its exact dependent base
identity at the included zero endpoint. -/
theorem limitNoncollapse_convergence_center_identity
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (Cnv : GeneralizedBlowupConvergence S J) (k : ℕ)
    (h0 : 0 ∈ Icc (-Cnv.exhaustion.time k) 0) :
    (Cnv.embedding k).pointMap 0 h0 Cnv.limit.base = S.base (Cnv.subsequence k) :=
  Cnv.base_preserving k h0

end PoincareMT.M47
