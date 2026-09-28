import PoincareMT.Proofs.M64.Sec19_3_Annuli.ElementaryFields
import PoincareMT.Proofs.M64.Sec19_3_Annuli.ForwardMinimalCompetitor
import PoincareMT.Proofs.M64.Sec19_3_Annuli.MinimalAnnulusInterface

/-!
# Time-indexed minimal-annulus producer

This file keeps the variational producer separate from the evolution
consumer.  A producer supplies an attained, regular annulus at
each time together with the eventual swept competitor estimate.  The two
consumer lemmas below then expose the exact forward derivative and the three
elementary area fields.  No Plateau or first-variation existence statement is
asserted here.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}

/-- Time-indexed attainment, regularity, and first-variation input for an annular area
evolution. The competitor estimate is stated against the actual least area, so it is
independent of the chosen minimizing witness. Source: Morgan--Tian (2007), Lemma 19.15 and
Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
structure M64MinimalAnnulusFamily
    {circumference : ℝ} (P : M62.CircleProductData F circumference)
    (c0 c1 : ℝ → ℝ → P.charts.Point) (rate : ℝ → ℝ) where
  data : ∀ t ∈ Set.Icc a b,
    M64MinimalAnnulusData
      (g := P.flow.metric t)
      (c0 := fun x => c0 x t) (c1 := fun x => c1 x t)
  competitor : ∀ t ∈ Set.Ico a b, ∀ eta : ℝ, 0 < eta →
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∃ B : M64Annulus (P.flow.metric (t + h))
          (fun x => c0 x (t + h)) (fun x => c1 x (t + h)),
        B.area ≤ m64FlowAnnulusArea P c0 c1 t + h * (rate t + eta)

/-- A minimal family and its swept competitors give the forward Dini bound. Source:
Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64AnnulusFlow_forward_of_minimal_family
    {circumference : ℝ} {P : M62.CircleProductData F circumference}
    {c0 c1 : ℝ → ℝ → P.charts.Point} {rate : ℝ → ℝ}
    (E : M64MinimalAnnulusFamily P c0 c1 rate) :
    ∀ t ∈ Set.Ico a b,
      AnnulusForwardDerivativeBound (m64FlowAnnulusArea P c0 c1) (rate t) t := by
  intro t ht
  have htcc : t ∈ Set.Icc a b := ⟨ht.1, le_of_lt ht.2⟩
  let A := E.data t htcc
  have hmin : A.annulus.area = m64FlowAnnulusArea P c0 c1 t := by
    simpa only [A, m64FlowAnnulusArea] using A.area_minimal
  apply m64AnnulusForward_of_minimal_competitors A.annulus hmin
  intro eta heta
  simpa only [hmin] using E.competitor t ht eta heta

/-- The annular family immediately supplies the nonempty, bounded-below and nonnegative
fields required by the evolution conclusion. Source: Morgan--Tian (2007), Lemma 19.15 and
Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64AnnulusFlow_elementary_fields_of_minimal_family
    {circumference : ℝ} {P : M62.CircleProductData F circumference}
    {c0 c1 : ℝ → ℝ → P.charts.Point} {rate : ℝ → ℝ}
    (E : M64MinimalAnnulusFamily P c0 c1 rate) :
    (∀ t ∈ Set.Icc a b,
      Nonempty (M64Annulus (P.flow.metric t)
        (fun x => c0 x t) (fun x => c1 x t))) ∧
    (∀ t ∈ Set.Icc a b,
      BddBelow (m64AnnulusAreaRange (P.flow.metric t)
        (fun x => c0 x t) (fun x => c1 x t))) ∧
    (∀ t ∈ Set.Icc a b,
      0 ≤ m64FlowAnnulusArea P c0 c1 t) := by
  apply m64AnnulusFlow_elementary_fields
  intro t ht
  exact ⟨(E.data t ht).annulus⟩

/-- The elementary fields need only pointwise minimal-annulus data; no competitor estimate
or rate is required for this part of the evolution. Source: Morgan--Tian (2007), Lemma 19.15
and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64AnnulusFlow_elementary_fields_of_minimal_data
    {circumference : ℝ} {P : M62.CircleProductData F circumference}
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (data : ∀ t ∈ Set.Icc a b,
      M64MinimalAnnulusData
        (g := P.flow.metric t)
        (c0 := fun x => c0 x t) (c1 := fun x => c1 x t)) :
    (∀ t ∈ Set.Icc a b,
      Nonempty (M64Annulus (P.flow.metric t)
        (fun x => c0 x t) (fun x => c1 x t))) ∧
    (∀ t ∈ Set.Icc a b,
      BddBelow (m64AnnulusAreaRange (P.flow.metric t)
        (fun x => c0 x t) (fun x => c1 x t))) ∧
    (∀ t ∈ Set.Icc a b,
      0 ≤ m64FlowAnnulusArea P c0 c1 t) := by
  apply m64AnnulusFlow_elementary_fields
  intro t ht
  exact ⟨(data t ht).annulus⟩

end PoincareMT
