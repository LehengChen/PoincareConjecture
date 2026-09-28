import PoincareMT.Statements.M62CurveEvolution
import PoincareMT.Proofs.M04.CurvatureCalculus
import PoincareMT.Proofs.M62.Sec19_3_Assembly

/-!
# M62 corrected curve-evolution proof entry

The corrected construction assembles the actual geometry, evolution and
uniform bounds. Its earlier theorem input is M04's actual curvature-calculus
component; geometric outputs retain no earlier theorem bundle.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- The exact component supplying M04's tensor_calculus field. -/
theorem m62CurvatureService_from_M04 : M62CurvatureService.{u} := by
  intro n M _ _ _ g D
  exact D.curvatureTensorCalculus

/-- M62: given the universal M04 curvature-calculus service, every actual Ricci
flow on a compact Hausdorff second-countable smooth manifold over [a,b]
admits its genuine open spacetime metric g(t)+dt^2 and Levi-Civita connection,
with the mixed connection and Gauss/Codazzi identities. Its ambient curvature,
covariant Ricci derivative and Ricci tensor have nonnegative uniform bounds
K0,K1,K2, chosen before any curve or circle circumference.

For every immersed periodic curve-shortening family that is smooth in the
interior, C2 on endpoint slices, and has continuous actual curve, velocity
and curvature through the endpoints, these objects give the speed evolution,
parameter commutator, full corrected spacetime curvature equation and its
equivalent spatial equation. The full normal square equals the spatial
normal square plus Ric(S,H)^2. With
C0=2*K0+6*K2+2*K2^2+6*K1 and C1=C0/2, the full and spatial curvature bounds
retain C0*(k^2+k). The positive regularization sqrt(k^2+epsilon^2) satisfies
the corrected gradient and evolution bounds, including at k=0. Length has
its classical interior derivative. Total curvature has the corrected integral
and upper-forward bounds, with the C1*length forcing term retained.

For every positive circumference the same ambient bounds apply to the actual
product with the quotient circle, whose fixed unit field is parallel in both
the spatial product and its own spacetime and annihilates mixed Ricci terms.
For every such shrinking curve, its slope u against this field has |u|<=1
and satisfies u_t=u_ss+(k^2+Ric(S,S))*u. The lower inequality
u_t>=u_ss-K2*u is asserted only where u>=0. No ramp-preservation or global
curve-existence theorem is included in this milestone.

Sources: Morgan--Tian Lemma 19.6, pp. 441-442, and Claim 19.11 and product
geometry, pp. 445-446; the 2015 Section 19.2 correction, (0.1)-(0.2), Lemmas
0.1-0.2, Corollary 0.3, (0.4), and Lemma 0.4, pp. 2-8. The full derivation
is in reviews/contracts/M62-round1.md. Apply the local textual, limiting and
slope-sign repairs in reviews/errata/2026-09-14-m62-curve-evolution.md. -/
theorem m62CorrectedCurveEvolution (hM04 : M62CurvatureService.{u}) :
    M62CurveEvolutionTheory.{u} := by
  have construction : M62CurvatureService.{u} → M62CurveEvolutionTheory.{u} := by
    intro _ n M _ _ _ _ _ a b F hcompact
    exact M62.nonempty_flowConclusion F hcompact
  exact construction hM04

/-- Concrete assembly from M04's owned component, with no further admission. -/
theorem m62CorrectedCurveEvolution_from_predecessors : M62CurveEvolutionTheory.{u} :=
  m62CorrectedCurveEvolution m62CurvatureService_from_M04

end PoincareMT
