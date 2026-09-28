import PoincareMT.Statements.M20ThreeDimensionalClassification
import PoincareMT.Proofs.M03
import PoincareMT.Proofs.M19
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Classification.Assembly

/-!
# M20 three-dimensional classification proof assembly

Earlier milestone modules are read-only inputs.  Any future analytic and
geometric helpers for this milestone belong in `Proofs/M20/`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Supply M03 on each actual compact carrier, including the two-dimensional
factor and three-dimensional compact limit in Corollary 9.54. -/
theorem m20CompactLocalFlowProvider_from_M03 :
    ∀ (n : ℕ) (N : Type u) [TopologicalSpace N] [T2Space N]
      [SecondCountableTopology N]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
      [IsManifold (𝓡 n) ∞ N] [CompactSpace N],
      RicciFlowLocalTheory n N := by
  intro n N _ _ _ _ _ _
  exact ricciFlowLocalTheory (n := n) (M := N)

/-! Supply M19's prerequisites once when assembling M20. The returned
service applies directly to each chosen two-dimensional carrier and object;
its classification result is precisely the existing M19 theorem. -/
theorem m20TwoDimensionalProvider_from_M19
    (hP : ∀ {N : Type u} [TopologicalSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
      [IsManifold (𝓡 2) ∞ N] [MeasurableSpace N] [BorelSpace N]
      [T2Space N] [T3Space N] [SecondCountableTopology N] [ConnectedSpace N],
      TwoDimensionalClassificationPredecessors (M := N)) :
    ∀ {N : Type u} [TopologicalSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
      [IsManifold (𝓡 2) ∞ N] [MeasurableSpace N] [BorelSpace N]
      [T2Space N] [T3Space N] [SecondCountableTopology N] [ConnectedSpace N],
      TwoDimensionalClassificationTheory (M := N) := by
  intro N _ _ _ _ _ _ _ _ _
  exact twoDimensionalAncientAndShrinkingSolitonClassification hP

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-!
Given the reviewed M03, M04, M06, M07, M18, and M19 predecessor services,
with M03 available on every compact carrier and M19 already applied to
its dimension-two prerequisites,
classify every complete nonflat three-dimensional gradient shrinking soliton
with bounded nonnegative curvature, the Definition 9.41 metric
noncollapsing bound, and `Ric + Hess f = g / 2`.  Construct the ancient flow
by (9.19), with its `-1` slice equal to the input and each slice homothetic to
it.  Return exactly the three Theorem 9.42 models: compact round, a shrinking
round `S^2` times a line, or a quotient by a free isometric involution. The
quotient includes both `RP^2 x R` and the twisted quotient; no orientation
condition is imposed on that involution.
The product uses one fixed sphere diffeomorphism and the metric
`(-2 * t) * g_unitSphere + ds^2`, with its tangent components given by the
actual smooth product projections. The quotient flow's metric and connection
are the same chosen data used by its pullback certificate on negative time.

For each three-dimensional rescaling sequence, construct and classify a
limit of that exact sequence. Derive the static Definition 9.41 bound at `t = -1`, then use
Corollary 9.53 to obtain bounded curvature on every negative slice.  Apply
Theorem 9.42 and use Corollary 9.54 to identify that constructed model flow
with the actual M18 limit. Its compact branch and compact surface factors
use M03. Whole-flow splitting and the metric ODE on the classified round
factors supply the all-negative-time identification; these supporting
arguments belong to this proof obligation. Forward uniqueness from time -1
alone does not imply equality at earlier times. The
certificate therefore cannot be supplied by an unrelated desired limit.

Before applying M19 to a surface factor, derive its per-slice curvature
bound. Inherit noncollapse and scalar monotonicity from the actual M18 limit,
then point-pick and apply dimension-two M07 at a buffered interior time.
M04's local derivative estimates preserve a nonzero basepoint curvature;
Proposition 3.21 transports the long triangles to that same time, where
Toponogov and splitting give the flat-limit contradiction. The finite-order
transfer of necks back to the fixed terminal slice in Corollary 9.53 also
belongs to this proof. These constructions use no terminal convergence
or later M23 input. M07 is supplied in all dimensions through its actual
earlier theorem. See `reviews/contracts/2026-09-15-m20-factor-bounds.md`
for the derivation from Proposition 9.39, pp. 203--205, Theorem 5.35,
pp. 100--102, and Proposition 3.21, pp. 45--49.

Sources: Morgan--Tian Definition 9.41, Theorem 9.42 and construction (9.19),
pp. 206--208; Claims 9.43 and 9.45, pp. 208--209; Proposition 9.46 and
Corollary 9.49, pp. 209--213; Corollary 9.50, pp. 213--214; Corollary 9.52,
p. 216; Corollaries 9.53--9.54, pp. 217--218; Theorem 9.11 and Remark 9.12,
pp. 183--185; Hamilton Theorem 4.23, pp. 74--75, and Proposition 5.21 of
[13], cited p. 208.  The M18 actual-sequence boundary is retained from
`reviews/contracts/M18-repair-contract.md` and `reviews/declarations/M18-round2.md`;
the dimension-two factor is supplied by
`reviews/contracts/M19-repair-contract.md` and
`reviews/declarations/M19-round2.md`.  The open correction records
`MT-COMPACTNESS-5.15`, `MT-HARNACK-ANCIENT`,
`MT-POSITIVE-RICCI-ROUNDNESS`, and `MT-SOLITON-STAGING` remain binding.
The printed Corollary 9.50 Proposition 9.50 typo is corrected in M19 and is
not treated as a new M20 source result.  Chapter 12 standard-cap and later
canonical-neighborhood claims are outside this milestone.
The quotient condition follows Theorem 9.42(3), p. 207, and its proof, p. 216;
the orientation-preserving example on p. 206 is not an extra hypothesis.
See `reviews/contracts/2026-09-15-m20-quotient-repair.md` for this correction.
The literal product and chosen quotient data are reviewed in
`reviews/contracts/2026-09-15-m20-product-design.md`.
The closed application of every earlier service is in `Proofs/M20/Providers.lean`,
following `reviews/contracts/2026-09-15-m20-provider-audit.md`.
-/
theorem threeDimensionalAncientAndShrinkingSolitonClassification
    (P : ThreeDimensionalClassificationPredecessors.{u}) :
    ThreeDimensionalClassificationTheory (M := M) := by
  exact horizon_threeDimensionalAncientAndShrinkingSolitonClassification P

/-! No-sorry assembly for the complete M20 predecessor bundle. -/
theorem threeDimensionalClassificationTheory
    (P : ThreeDimensionalClassificationPredecessors.{u}) :
    ThreeDimensionalClassificationTheory (M := M) := by
  exact threeDimensionalAncientAndShrinkingSolitonClassification P

end PoincareMT
