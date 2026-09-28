import PoincareMT.Definitions.Ch15.SurgeryTopology
import PoincareMT.Statement

/-!
# M74 connected-sum reduction

The input is a genuine finite connected-sum assembly and an explicit
per-factor sphere identification.  M74 owns the finite relation induction
that reduces that assembly to one sphere.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

structure M74ReductionInput {n : ℕ}
    (pieces : Fin n → GeneralizedSliceCarrier.{u})
    (C : GeneralizedSliceCarrier.{u}) where
  assembly : SmoothFiniteConnectedSumAssembly pieces C
  target_nonempty : Nonempty C.carrier
  target_connected : IsConnected (Set.univ : Set C.carrier)
  factor_sphere : ∀ i, Nonempty
    (Diffeomorph (𝓡 3) (𝓡 3) (pieces i).carrier ThreeSphere ∞)

structure M74ReductionConclusion (C : GeneralizedSliceCarrier.{u}) where
  reduction : Nonempty
    (Diffeomorph (𝓡 3) (𝓡 3) C.carrier ThreeSphere ∞)

end PoincareMT
