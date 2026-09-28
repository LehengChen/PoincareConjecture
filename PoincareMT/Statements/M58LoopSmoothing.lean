import PoincareMT.Definitions.M58LoopSmoothing

/-!
# M58 short-loop triviality and small-area disk statement

The data package contains both the original decorated-family formulation of
Lemma 18.27 and its raw continuous-map reformulation.  The raw service is
needed by M65's output and is consumed by the ordinary width argument in M66;
it is not a second class predicate.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-
Natural-language theorem: for a compact connected Riemannian three-manifold
with trivial based pi2, there is a positive threshold such that any continuous
two-sphere family of null-homotopic C1 loops whose individual lengths are below
that threshold represents the identity in the based pi2 of the C1 free-loop
space.  Independently, for every positive area tolerance there is a smaller
positive length threshold such that every C1 loop below it has a Lipschitz
spanning disk of area below the tolerance.

Source: Morgan--Tian Lemma 18.27 (printed p. 434;
`references/derived/MT2007.txt:21255-21276`) and Corollary 18.28
(`21280-21282`).  The source's loop-space identification with pi3 is Claim
18.16 and belongs to M59; this milestone therefore states the class-trivial
conclusion in the explicit loop-space type.  The disk uses the
reparameterization convention in Definition 18.17 (`21070-21079`).
The active surgery/loop-regularity qualification is recorded in
`reviews/errata/2026-09-10-surgery-extinction-audit.md:68-75`.

M58 has no M40/M57 theorem bundle and no Chapter 19 ramp-smoothing conclusion:
those are separate typed consumers.  Its only theorem-owned proof placeholder
is the data package below; definitions and this statement remain
admission-free.
-/
structure RepairedShortLoopTrivialityTheory : Prop where
  short_loop : RepairedShortLoopTrivialityData.{u}

end PoincareMT
