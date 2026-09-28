import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryModulus

/-!
# Actual degree-one boundary lifts

The canonical angular lift is a genuine monotone Lipschitz degree-one
lift. It is the boundary reparametrization used by the polar annular
coordinates; no free-boundary admission is hidden in this construction.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace PoincareMT

/-- The canonical identity lift of the angular parameter. Source: Morgan--Tian (2007), Lemma
19.15, pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-boundary-lifts.md`. -/
def scalarIdentityDegreeOneLift : M64PeriodicDegreeOneLift where
  map := id
  monotone := monotone_id
  period_shift := by intro x; dsimp
  lipschitz_constant := 1
  lipschitz_nonnegative := by norm_num
  lipschitz_on := by intro x y; simp

/-- The canonical degree-one lift is literally the identity angular map. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit project construction is recorded
in `proof-work/tasks/M64/reports/annular-boundary-lifts.md`. -/
theorem scalarIdentityDegreeOneLift_apply (x : ℝ) :
    scalarIdentityDegreeOneLift.map x = x := rfl

/-- The canonical identity lift retains the exact real curve-period increment. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit project construction is recorded
in `proof-work/tasks/M64/reports/annular-boundary-lifts.md`. -/
theorem scalarIdentityDegreeOneLift_period :
    ∀ x : ℝ, scalarIdentityDegreeOneLift.map (x + curvePeriod) =
      scalarIdentityDegreeOneLift.map x + curvePeriod :=
  scalarIdentityDegreeOneLift.period_shift

/-- Both boundary circles admit actual degree-one angular lifts. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-boundary-lifts.md`. -/
theorem exists_scalar_boundary_degree_one_lifts :
    ∃ (sigma0 sigma1 : M64PeriodicDegreeOneLift),
      sigma0.map = id ∧ sigma1.map = id := by
  exact ⟨scalarIdentityDegreeOneLift, scalarIdentityDegreeOneLift,
    rfl, rfl⟩

end PoincareMT
