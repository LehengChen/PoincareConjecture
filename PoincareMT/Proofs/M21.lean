import PoincareMT.Statements.M21AsymptoticVolume
import PoincareMT.Proofs.M04.CurvatureCalculus
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Volume.BishopGromov

/-!
# M21 asymptotic volume ratio proof assembly

Earlier milestone files and the M21 definition/statement boundary are
read-only inputs.  Future proof helpers belong in `Proofs/M21/`.
-/

set_option autoImplicit false

open scoped Manifold ContMDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- The actual M04 component supplies the dimension-fixed static service. -/
theorem m21Predecessors_from_M04 (n : ℕ) :
    AsymptoticVolumeRatioPredecessors.{u} n := by
  intro M _ _ _ g D
  exact D.curvatureTensorCalculus

/-- M21: given M04's static tensor calculus, every n-dimensional ancient
kappa-solution K and time t <= 0 have the following properties on the actual
metric K.flow.metric t. The calibrated volume of its ball of radius r,
divided by r^n, is antitone for r > 0. It tends at infinity to the infimum
over those positive radii, and this limit is independent of the basepoint.

Apply the supplied tensor calculus to the actual slice connection to deduce
nonnegative Ricci curvature from the nonnegative curvature operator. M21 owns
the completeness-to-compact-balls and volume-calibration arguments, the
Bishop--Gromov comparison, the monotone limit and the shifted-ball basepoint
comparison. These use one fixed metric slice. Universal noncollapse and
zero asymptotic volume are separate M22 obligations.

Sources: Morgan--Tian Theorem 1.34, p. 19; Definition 9.1, pp. 180-181;
Chapter 9 Section 6, "Asymptotic volume", p. 221. The 2015 Section 19.2
correction does not affect this result. The corrected source/dependency
derivation is in reviews/contracts/2026-09-15-m21-static-round1.md. -/
theorem asymptoticVolumeRatioBishopGromov (n : ℕ)
    (P : AsymptoticVolumeRatioPredecessors.{u} n) :
    AsymptoticVolumeRatioTheory.{u} n := by
  exact horizon_asymptoticVolumeRatioBishopGromov n P

/-- Compatibility assembly for an explicitly supplied static service. -/
theorem asymptoticVolumeRatioTheory (n : ℕ)
    (P : AsymptoticVolumeRatioPredecessors.{u} n) :
    AsymptoticVolumeRatioTheory.{u} n :=
  asymptoticVolumeRatioBishopGromov n P

/-- Closed M21 assembly from the actual M04 theorem. -/
theorem m21AsymptoticVolumeRatioFromMilestones (n : ℕ) :
    AsymptoticVolumeRatioTheory.{u} n :=
  asymptoticVolumeRatioBishopGromov n (m21Predecessors_from_M04 n)

end PoincareMT
