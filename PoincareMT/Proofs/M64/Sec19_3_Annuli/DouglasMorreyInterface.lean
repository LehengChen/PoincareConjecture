import PoincareMT.Proofs.M64.Sec19_3_Annuli.MinimizingSequence

/-!
# Douglas--Morrey annular producer interfaces

The guarded infimum and a minimizing sequence do not provide a limit map.
This file separates the missing direct-method, regularity, and branch-aware
first-variation outputs.  No Plateau or harmonic-annulus existence theorem
is asserted here.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {c0 c1 : ℝ → M}

/-- The direct-method output for fixed annular boundary maps. The `sequence_tendsto_limit`
records the map-level compactness output, while the `limit_area_le` field is the
lower-semicontinuity inequality; together with the infimum comparison it forces exact
attainment. The sequence fields are kept so a producer cannot silently replace a minimizing
sequence by an unrelated candidate annulus. Source: Morgan--Tian (2007), Lemma 19.15 and
Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
structure M64DouglasMorreyAttainmentCertificate where
  sequence : ℕ → M64Annulus g c0 c1
  sequence_antitone : Antitone (fun k => (sequence k).area)
  sequence_tendsto_infimum :
    Tendsto (fun k => (sequence k).area) atTop
      (𝓝 (m64LeastAnnulusArea g c0 c1))
  limit : M64Annulus g c0 c1
  sequence_tendsto_limit : ∀ p ∈ m64AnnulusDomain,
    Tendsto (fun k => (sequence k).map p) atTop (𝓝 (limit.map p))
  limit_area_le : limit.area ≤ m64LeastAnnulusArea g c0 c1

/-- The admitted limit's lower area bound and the guarded infimum comparison give exact
attainment. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449;
project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem M64DouglasMorreyAttainmentCertificate.limit_area_eq_infimum
    (C : M64DouglasMorreyAttainmentCertificate (g := g) (c0 := c0) (c1 := c1)) :
    C.limit.area = m64LeastAnnulusArea g c0 c1 := by
  exact le_antisymm C.limit_area_le
    (m64LeastAnnulusArea_le_annulus C.limit)

/-- Once a candidate limit and its lower-semicontinuity inequality are available, the
already-proved order-theoretic sequence completes the Douglas--Morrey attainment
certificate. Pointwise map convergence and lower-semicontinuity remain explicit hypotheses.
Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project
derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
noncomputable def m64DouglasMorreyAttainmentCertificate_of_limit
    (seed : M64Annulus g c0 c1) (limit : M64Annulus g c0 c1)
    (hpointwise : ∀ p ∈ m64AnnulusDomain,
      Tendsto (fun k => (Classical.choose
        (m64Annulus_exists_minimizing_sequence seed) k).map p) atTop
        (𝓝 (limit.map p)))
    (hlimit : limit.area ≤ m64LeastAnnulusArea g c0 c1) :
    M64DouglasMorreyAttainmentCertificate (g := g) (c0 := c0) (c1 := c1) :=
  let witness := Classical.choose (m64Annulus_exists_minimizing_sequence seed)
  let properties := Classical.choose_spec (m64Annulus_exists_minimizing_sequence seed)
  { sequence := witness
    sequence_antitone := properties.1
    sequence_tendsto_infimum := properties.2
    limit := limit
    sequence_tendsto_limit := hpointwise
    limit_area_le := hlimit }

/-- The branch set uses the actual differential of the candidate map and is restricted to
the annulus interior. This matches the branch convention used by the lower minimal-sphere
structures while retaining the annular domain. Source: Morgan--Tian (2007), Lemma 19.15 and
Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
noncomputable def m64AnnulusBranchSet
    (A : M64Annulus g c0 c1) : Set LoopPlane :=
  {p | p ∈ interior m64AnnulusDomain ∧
    mfderiv (𝓡 2) (𝓡 n) A.map p = 0}

/-- Regularity and branch-aware stationarity needed after annular attainment. The variation
predicate fixes both prescribed boundary curves at every slice; the derivative assertion is
therefore the fixed-boundary first variation. Finite branching and injectivity away from the
actual differential-zero set are separate fields, so no branch exclusion is smuggled into
stationarity. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449;
project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
def M64AnnulusAreaStationary
    (A : M64Annulus g c0 c1) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∀ variation : ℝ × LoopPlane → M,
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ variation
        (Ioo (-epsilon) epsilon ×ˢ m64AnnulusDomain) →
      (∀ s ∈ Ioo (-epsilon) epsilon,
        ∃ B : M64Annulus g c0 c1, B.map = fun p => variation (s, p)) →
      (∀ p ∈ m64AnnulusDomain, variation (0, p) = A.map p) →
      HasDerivAt
        (fun s => m64AnnulusArea g (fun p => variation (s, p))) 0 0

/-- Separate regularity, area stationarity and actual differential branch data for an
already supplied annulus. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp.
447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
structure M64AnnulusBranchAwareFirstVariationCertificate
    (A : M64Annulus g c0 c1) : Prop where
  regularity : M64AnnulusRegularityCertificate A
  area_stationary : M64AnnulusAreaStationary A
  finite_branch_set : (m64AnnulusBranchSet A).Finite
  injective_off_branch_set : ∀ p ∈ interior m64AnnulusDomain,
    p ∉ m64AnnulusBranchSet A →
      Function.Injective (mfderiv (𝓡 2) (𝓡 n) A.map p)

/-- Assemble the existing minimal-annulus record from the direct-method and branch-aware
producer certificates. The branch fields remain available to the first-variation consumers;
the public minimal record receives the regularity fields it currently requires. Source:
Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
def m64MinimalAnnulusData_of_douglasMorrey
    (attainment : M64DouglasMorreyAttainmentCertificate
      (g := g) (c0 := c0) (c1 := c1))
    (variation : M64AnnulusBranchAwareFirstVariationCertificate
      attainment.limit) :
    M64MinimalAnnulusData (g := g) (c0 := c0) (c1 := c1) := by
  exact m64MinimalAnnulusData_of_certificates attainment.limit
    attainment.limit_area_eq_infimum variation.regularity

/-- Supplied attainment and branch-aware regularity certificates yield the stated actual
minimal annulus. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449;
project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem exists_m64MinimalAnnulus
    (attainment : M64DouglasMorreyAttainmentCertificate
      (g := g) (c0 := c0) (c1 := c1))
    (variation : M64AnnulusBranchAwareFirstVariationCertificate
      attainment.limit) :
    ∃ B : M64Annulus g c0 c1, B.area = m64LeastAnnulusArea g c0 c1 ∧
      M64PiecewiseC1Annulus B ∧
      ContMDiffOn (𝓡 2) (𝓡 n) ∞ B.map (interior m64AnnulusDomain) := by
  refine ⟨attainment.limit, attainment.limit_area_eq_infimum,
    variation.regularity.piecewise_c1, variation.regularity.interior_smooth⟩

end PoincareMT
