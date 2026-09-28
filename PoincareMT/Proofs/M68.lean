import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.ScalarClock.Assembly
import PoincareMT.Statements.M68

/-!
# M68 scalar clock proof entry

The sole M68 theorem-owned placeholder is the finite induction over the
ordered surgery list.  Earlier M67 files are read-only support; future
calculus and comparison helpers belong under `Proofs/M68/`.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- For the actual M67 width and its nonnegativity, scalar lower bound,
forward-difference estimate, regular continuity, surgery lower limit and
post-surgery right continuity, every ordered subinterval [T1,T2] with T1 >= 0
has the explicit profile in M68ProfileConclusion. It starts at W(T1), solves
z' = -2*pi + 3*z/(1+4*t), and bounds the width including surgery endpoints.
Source: Morgan--Tian Lemma 2.22, p. 33; Proposition 18.18 and Theorem 18.1,
pp. 431--432; Definition 18.23, p. 433, and Claim 18.26, p. 434. The p. 432
second-term T0 is corrected to T1. Compare separately on continuous pieces
and restart using the surgery lower limit and right continuity. -/
theorem m68ScalarClockTheory : M68ScalarClockStatement.{u} :=
  horizon_m68_scalar_clock_statement


end PoincareMT
