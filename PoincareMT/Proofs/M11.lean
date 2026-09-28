import PoincareMT.Statements.M11GeneralizedFlow
import PoincareMT.Proofs.M11.CarrierAssembly
import PoincareMT.Proofs.M11.OrdinaryAssembly

/-!
# M11 spacetime realization proof

This numbered entry owns the checked interval, atlas, bundle, slice and
compatible domain construction.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- M11: compatible adapted topological boxes with jointly smooth positive
metric coefficients on a Hausdorff second-countable carrier determine an
actual smooth (n+1)-dimensional spacetime on that same carrier, topology and
time map. Its boundary is exactly the included time endpoints. The actual
normalized time vector, literal ker(dt) bundle, smooth projection and metric,
boundaryless slices, and supplied slice labels satisfy the stated differential
and metric identities. Compatible worldlines are unique; valid restrictions
and relatively open gluing preserve the actual maps and retained base data.
Relatively open interval inclusions have smooth local inverses on the same
selected interval system, including their retained endpoints.
Supplied smooth cylinders have jointly smooth positive pullback metrics.
A given smooth metric family on a nonempty smooth n-manifold also gives this
geometry on exactly I times that manifold, with the stated product and slice
identifications. These assertions include n=0 and open, closed, half-open and
unbounded nontrivial intervals. They assert no Ricci PDE or uniform survival
time for a noncompact source.

Sources: Morgan-Tian Definitions 3.34-3.35, pp. 59-60; ordinary-product
observation and Definition 3.38, p. 61; Theorem 5.11 and Definitions 5.12-5.13,
pp. 89-90. The atlas/descent argument is project-derived, explicitly given in
`reviews/contracts/M11-repair-contract.md`, not a separate numbered MT theorem.
Theorem 11.19(3), pp. 279-280, Definition 11.22, p. 281, and Proposition 14.12,
p. 350, describe later applications whose topology and terminal regularity
remain later obligations. Apply the endpoint and compactness qualifications in
`reviews/errata/2026-09-10-source-audit.md`; the 2015 Chapter 19 correction
does not replace these geometric definitions. -/
theorem generalizedSpacetimeGeometry (n : ℕ) :
    GeneralizedSpacetimeGeometryTheory.{u} n := by
  constructor
  · intro X _ _ _ A
    exact ⟨Proofs.M11.adaptedCarrierConclusion A⟩
  · intro M _ _ _ _ _ _ g I hg
    exact ⟨Proofs.M11.ordinaryProductConclusion g I hg⟩

end PoincareMT
