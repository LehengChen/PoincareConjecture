import PoincareMT.Statements.M16StructuralKappa
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Structure

/-!
# M16 structural ancient-kappa theorem

The numbered file is the review and proof entry point. The definitions,
statement, and imported Horizon proof are admission-free.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-
M16: given the M04 curvature tensor calculus, M06 ancient differential and
integrated Harnack estimates, and M13 positive parabolic rescaling, every
connected complete nonflat ancient kappa-solution in any dimension has
positive scalar curvature, full curvature norm bounded by scalar curvature
and by its dimension multiple, nonnegative Ricci curvature with the trace
bound, nondecreasing scalar curvature, and nonincreasing metric, selected
Riemannian distance, and metric balls.  A scalar bound on a fixed spatial set
at a terminal time controls the full curvature norm on that same set at every
earlier time, and each terminal slice gives a solution-dependent bound on its
entire past.  At any specified point p and time b <= 0, the positive scale
Q = R(p,b) produces an actual same-carrier ancient kappa-solution with
metric Q * g(b + s/Q), the same kappa, and scalar curvature one at (p,0).

Sources: Morgan--Tian Chapter 9, Section 1 and Definitions 9.1--9.2,
pp. 179--180; Theorem 4.40, p. 82; Definition 3.40, p. 61; and the exact
curvature conventions of Definitions 1.4 and 1.6--1.8, pp. 5--7.  The
endpoint-safe ancient Harnack formulation and fixed-set interpretation follow
`reviews/errata/2026-09-10-analytic-outline-audit.md` and
`reviews/errata/2026-09-13-reduced-length-source.md`.  Nonflatness is retained
at every ancient time.  No asymptotic limit, classification, asymptotic
volume ratio, or family-uniform neighborhood estimate is concluded.
-/
theorem ancientKappaStructuralConsequences
    (n : ℕ)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hM06 : HarnackAncientTheory.{u})
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n) :
    AncientKappaStructuralConclusion.{u} n := by
  exact horizon_ancientKappaStructuralConsequences n hM04 hM06 hM13

end PoincareMT
