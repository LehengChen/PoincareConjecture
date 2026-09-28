import PoincareMT.Statements.M64Comparison
import PoincareMT.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_Assembly
import PoincareMT.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GlobalAssembly

/-!
# Conditional reduction of Lemma 19.31 to Proposition 19.35

The producer for Lemma 19.31 must transport an arbitrary product annulus to
an intrinsic annulus coming from a regular minimal branch.  This file keeps
the two geometric gaps explicit: the Gauss equation bounds the intrinsic
Gaussian term by an ambient sectional-curvature field, and the transported
annulus preserves the two boundary lengths, turning bound, and area cutoff.
The final theorem is only the quantifier and arithmetic assembly.

Morgan--Tian context: Section 19.6, Lemmas 19.30-19.31, printed pp. 461-466.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}

/-- Data transported from one product annulus to a regular intrinsic branch.
`gauss_equation` is the minimal-surface inequality `K_intrinsic ≤ K_ambient`;
`ambient_sectional_bound` is the separate ambient curvature estimate. Their composition is
the public Gaussian bound. Source: MT Lemma 19.31, p. 462 and proof on pp. 464-466;
conditional transport reduction. -/
structure M64RampIntrinsicTransportWitness
    {circumference : ℝ} (G : M63AmbientGeometry F)
    (P : M62.CircleProductData F circumference) (t : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (A : M64Annulus (P.flow.metric t) gamma0 gamma1)
    (r mu : ℝ) where
  intrinsic : IntrinsicAnnulus
  ambient_sectional : AnnulusCoordinates → ℝ
  gauss_equation : ∀ p ∈ standardAnnulusDomain,
    intrinsic.connection.scalarCurvature p / 2 ≤ ambient_sectional p
  ambient_sectional_bound : ∀ p ∈ standardAnnulusDomain,
    ambient_sectional p ≤ G.K0
  first_length_strict : r / 2 <
    intrinsicBoundaryLength intrinsic.metric 1 0 rampPeriod
  first_length_eq :
    intrinsicBoundaryLength intrinsic.metric 1 0 rampPeriod =
      m62Length P.flow (fun x _ => gamma0 x) t
  second_length_eq :
    intrinsicBoundaryLength intrinsic.metric 2 0 rampPeriod =
      m62Length P.flow (fun x _ => gamma1 x) t
  small_turning : intrinsic.SmallBoundaryTurning (1 / 200 : ℝ) (r / 2)
  area_le_source : intrinsicAnnulusArea intrinsic.metric ≤ A.area

/-- Compose the minimal-surface Gauss inequality with the actual ambient sectional-curvature
bound. Source: MT Lemma 19.31, p. 462 and proof on pp. 464-466; conditional transport
reduction. -/
theorem M64RampIntrinsicTransportWitness.gaussian_bound
    {circumference : ℝ} {G : M63AmbientGeometry F}
    {P : M62.CircleProductData F circumference} {t : ℝ}
    {gamma0 gamma1 : ℝ → P.charts.Point}
    {A : M64Annulus (P.flow.metric t) gamma0 gamma1}
    {r mu : ℝ} (W : M64RampIntrinsicTransportWitness G P t gamma0 gamma1 A r mu) :
    W.intrinsic.GaussianCurvatureBound G.K0 := by
  intro p hp
  exact (W.gauss_equation p hp).trans (W.ambient_sectional_bound p hp)

/-- Uniform product-to-intrinsic transport at the cutoff supplied by Proposition 19.35. The
public small-turning hypothesis remains an input to the producer; no product curvature or
boundary regularity is inferred here. Source: MT Lemma 19.31, p. 462 and proof on pp.
464-466; conditional transport reduction. -/
def M64RampIntrinsicTransport (G : M63AmbientGeometry F) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ mu : ℝ, 0 < mu →
    ∃ muRamp : ℝ, 0 < muRamp ∧ muRamp ≤ mu ∧
      ∀ circumference (h : 0 < circumference),
        let P := G.product circumference h
        ∀ t ∈ Set.Icc a b, ∀ gamma0 gamma1 : ℝ → P.charts.Point,
          Function.Periodic gamma0 curvePeriod →
          Function.Periodic gamma1 curvePeriod →
          ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0 →
          ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1 →
          M63IsRampAt P gamma0 t → M63IsRampAt P gamma1 t →
          r ≤ m62Length P.flow (fun x _ => gamma0 x) t →
          (∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
            m63ArcLength P.flow (fun x _ => gamma0 x) t alpha beta ≤ r →
              m63ArcTotalCurvature P.flow (fun x _ => gamma0 x) t alpha beta <
                (1 / 200 : ℝ)) →
          ∀ A : M64Annulus (P.flow.metric t) gamma0 gamma1, A.area < muRamp →
            Nonempty (M64RampIntrinsicTransportWitness G P t gamma0 gamma1 A r mu)

/-- Proposition 19.35 plus a sound product-to-intrinsic transport producer gives the exact
public Lemma 19.31 conclusion. The radius is halved only to turn the public non-strict
length premise into the strict hypothesis required by Proposition 19.35. Source: MT Lemma
19.31, p. 462 and proof on pp. 464-466; conditional transport reduction. -/
theorem m64RampSmallAnnulusComparison_of_intrinsic_transport
    {G : M63AmbientGeometry F}
    (hIntrinsic : M64IntrinsicAnnulusComparison)
    (htransport : M64RampIntrinsicTransport G) :
    M64RampSmallAnnulusComparison G := by
  intro hn r hr
  have hdelta_pos : 0 < (1 / 200 : ℝ) := by norm_num
  have hdelta_small : (1 / 200 : ℝ) < 1 / 100 := by norm_num
  have hrhalf : 0 < r / 2 := by linarith
  obtain ⟨muIntrinsic, hmuIntrinsic, hcomparison⟩ :=
    hIntrinsic (1 / 200 : ℝ) (r / 2) G.K0
      hdelta_pos hdelta_small hrhalf
  obtain ⟨muRamp, hmuRamp, hmuRamp_le, hproducer⟩ :=
    htransport r hr muIntrinsic hmuIntrinsic
  refine ⟨muRamp, hmuRamp, ?_⟩
  intro circumference hcirc
  dsimp
  intro t ht gamma0 gamma1 hperiod0 hperiod1 hregular0 hregular1
    hramp0 hramp1 hlength hturn A hA
  obtain ⟨W⟩ := hproducer circumference hcirc t ht gamma0 gamma1
    hperiod0 hperiod1 hregular0 hregular1 hramp0 hramp1 hlength hturn A hA
  have harea : intrinsicAnnulusArea W.intrinsic.metric < muIntrinsic := by
    exact W.area_le_source.trans_lt (hA.trans_le hmuRamp_le)
  have hbound := hcomparison W.intrinsic W.gaussian_bound
    W.first_length_strict W.small_turning harea
  rw [W.first_length_eq, W.second_length_eq] at hbound
  exact hbound

/-- The same reduction starting from the existing conditional Proposition 19.35 global-strip
producer. Its length-loss consumer is the only source of the intrinsic comparison used here;
no new admission is introduced. Source: MT Lemma 19.31, p. 462 and proof on pp. 464-466;
conditional transport reduction. -/
theorem m64RampSmallAnnulusComparison_of_global_strip_transport
    {G : M63AmbientGeometry F}
    (hcontrol : ∀ delta r K : ℝ, 0 < delta → delta < 1 / 100 → 0 < r →
      ∃ mu : ℝ, 0 < mu ∧
        ∀ N : IntrinsicAnnulus,
          N.GaussianCurvatureBound K →
          r < intrinsicBoundaryLength N.metric 1 0 rampPeriod →
          N.SmallBoundaryTurning delta r →
          intrinsicAnnulusArea N.metric < mu →
          Nonempty (M64IntrinsicGlobalStripCertificate N delta r K mu))
    (htransport : M64RampIntrinsicTransport G) :
    M64RampSmallAnnulusComparison G := by
  apply m64RampSmallAnnulusComparison_of_intrinsic_transport
  · exact m64IntrinsicAnnulusComparison_of_length_loss_estimates
      (m64Intrinsic_length_loss_estimates_of_global_strip_control hcontrol)
  · exact htransport

end PoincareMT
