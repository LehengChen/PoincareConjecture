import PoincareMT.Proofs.M02.Topology.AmbientFiniteSlabAvoidance
import PoincareMT.Proofs.M02.Topology.AmbientGridPerturbation

/-!
The prescribed clearance ratios for the finite ambient-grid construction.
-/

set_option autoImplicit false

noncomputable section

namespace PoincareMT.Proofs.M02.Topology

def ambientGridSlabRatio (N : Nat) : Real :=
  1 / (4 * (N + 1 : Real) ^ 2 * (ambientGridStarBound N + 1 : Real))

def ambientGridGap (N r : Nat) : Real :=
  (ambientGridMoveRatio N * ambientGridSlabRatio N / 2) *
    (ambientGridMoveRatio N * ambientGridSlabRatio N /
      (8 * (N + 1 : Real))) ^ r

end PoincareMT.Proofs.M02.Topology
