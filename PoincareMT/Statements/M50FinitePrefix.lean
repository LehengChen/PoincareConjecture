import PoincareMT.Definitions.M50FinitePrefix
import PoincareMT.Statements.M49VolumeLoss

/-!
# M50 repaired finite-prefix flow statement

Selected positive losses at cap events, together with the separate component
count, rule out finite accumulation on the same changing-carrier flow.
Finite epoch extension is the separate M48 step.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-!
Natural-language theorem: for a raw changing-carrier flow `F` with primitive
M49 controls `C` and exact event-loss certificate `V`, weighted volume loss
and the separate component count yield compact-set finiteness and no finite
accumulation. No extension service,
infinite-time endpoint or global schedule is asserted here.

Source: Morgan--Tian Theorem 15.9, pp. 363--366 and the finite-prefix argument
around Lemma 17.12, MT2007ArxivV2.txt lines 18856--18957 (pp. 395--397 in the
arXiv pagination; the book pagination is pp. 408--411, with Lemma 17.12 on
p. 410).  The volume-loss input is the corrected M49 certificate; the printed
`h^2 / delta` term is corrected to `h^3 / delta` by
`reviews/errata/2026-09-10-surgery-extinction-audit.md`.
-/
structure RepairedFinitePrefixTheory : Prop where
  finite_prefix : ∀ F : SurgeryFlowData.{u},
    ∀ C : RepairedVolumeLossControls F,
      ∀ V : RepairedVolumeLossData F C,
        Nonempty (RepairedFinitePrefixData F C V)

end PoincareMT
