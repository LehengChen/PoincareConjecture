import PoincareMT.Definitions.M26CanonicalNeighborhoods
import PoincareMT.Statements.Ch04.CurvatureTheory
import PoincareMT.Statements.M16StructuralKappa
import PoincareMT.Statements.M17BlowupSetup
import PoincareMT.Statements.M19TwoDimensionalClassification
import PoincareMT.Statements.M20ThreeDimensionalClassification
import PoincareMT.Statements.M22UniversalNoncollapsing
import PoincareMT.Statements.M23NormalizedKappaCompactness
import PoincareMT.Statements.M24ModelCertificates
import PoincareMT.Statements.M25NeckCapTopology

/-!
# M26 repaired canonical-neighborhood statement

The theorem fixes separate quantitative constants before ranging over the
ancient three-dimensional kappa-solutions. It exposes Corollary 9.88's
noncompact tube/capped-tube branch and Theorem 9.89's compact three-way
branch; the stronger all-time pointwise conclusion is deferred to M27.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-! These methods are applied earlier outputs. In particular, they do not
leave earlier predecessor bundles for the M26 owner to reconstruct. -/
def M26BlowupSetupProvider : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
    ∀ (K : AncientKappaSolution 3 M) (reference : M) (tau : ℕ → ℝ),
      (∀ k, 0 < tau k) → Filter.Tendsto tau Filter.atTop Filter.atTop →
        AncientBlowupSetupConclusion K reference tau

def M26AsymptoticClassificationProvider : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
    ∀ (K : AncientKappaSolution 3 M) (S : AncientRescalingSequence K),
      ∃ L : AncientAsymptoticSolitonLimitData S,
        ThreeDimensionalAsymptoticClassificationCertificate S L

/-! Fourteen actual services. M04 supplies only the displayed analytic
properties; M16 supplies past control and normalization, which also implies
scalar positivity. M19 applies to an actual bounded two-dimensional factor.
M20 and M24 retain the chosen sequence, limit, flow and model. M22/M25
constants are chosen before the solutions/covers. M23 retains its Type0
carrier boundary; coherent small-representative transports are internal M26
proof work. See reviews/contracts/2026-09-15-m26-complete-contract.md. -/
structure M26CanonicalNeighborhoodPredecessors : Prop where
  tensor_calculus :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      (g : RiemannianMetric n M) (D : LeviCivitaData g), D.CurvatureTensorCalculus
  scalar_regular :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J),
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × M ↦ (F.connection p.1).scalarCurvature p.2) (J ×ˢ Set.univ)
  scalar_evolution :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J) (t : ℝ), t ∈ J → ∀ x : M,
      HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x)
        ((F.connection t).laplacian (F.connection t).scalarCurvature x +
          2 * (F.connection t).ricciNormSq x) J t
  curvature_evolution :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J) (t : ℝ), t ∈ J →
      ∀ (x : M) (v₁ v₂ v₃ v₄ : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s ↦ (F.connection s).curvatureTensor x v₁ v₂ v₃ v₄)
        ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x
          ![v₁, v₂, v₃, v₄] + (F.connection t).curvatureReaction x v₁ v₂ v₃ v₄) J t
  ricci_evolution :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J) (t : ℝ), t ∈ J →
      ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s ↦ (F.connection s).ricci x v w)
        ((F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![v, w] +
          (F.connection t).ricciReaction x v w) J t
  past_norm_le_scalar :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M),
      ∀ t b : ℝ, t ≤ b → b ≤ 0 → ∀ x : M,
        (K.flow.connection t).curvatureTensorNorm x ≤
          (K.flow.connection b).scalarCurvature x
  normalization :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M) (p : M) (b : ℝ), b ≤ 0 →
        Nonempty (AncientKappaNormalization K p b)
  blowup_setup : M26BlowupSetupProvider.{u}
  two_dimensional_classification :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 2 M),
      Nonempty (TwoDimensionalAncientRoundCertificate K)
  classified_limit : M26AsymptoticClassificationProvider.{u}
  universal_noncollapsing :
    ∃ kappa₀ : ℝ, 0 < kappa₀ ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M),
        ¬ IsRoundAncientKappaSolution K → AncientKappaNoncollapsed K.flow kappa₀
  normalized_compactness :
    ∀ N : NormalizedKappaCompactnessData,
      Nonempty (RedesignNormalizedKappaCompactnessConclusion N)
  model_refinement :
    ∀ {M₃ : Type u} [TopologicalSpace M₃]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₃]
      [IsManifold (𝓡 3) ∞ M₃] [MeasurableSpace M₃] [BorelSpace M₃]
      [T2Space M₃] [T3Space M₃] [SecondCountableTopology M₃]
      [ConnectedSpace M₃]
      {S : GradientShrinkingSolitonData 3 M₃}
      (G : ShrinkingSolitonFlow S),
      ∀ input : M24ModelInput G, RepairedModelCertificateTheory input
  global_neck_cap :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        (g : RiemannianMetric 3 M) (H : ConnectedNeckCapCover g),
        H.epsilon ≤ epsilon₀ → H.isWhole →
          Nonempty (GlobalNeckCapConclusion g H.epsilon H.cap_constant)

structure RepairedCanonicalNeighborhoodTheory : Prop where
  /- Corollary 9.88: the no-trivial-normal-RP2 noncompact branch. -/
  corollary_9_88 :
    ∃ epsilon₂ : ℝ, 0 < epsilon₂ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₂ →
        ∃ C₀ : ℝ, 0 < C₀ ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M]
            [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M,
              ¬ IsCompact (Set.univ : Set M) →
              NoEmbeddedTrivialNormalProjectivePlane K →
              Nonempty (KappaNine88Conclusion K epsilon C₀)
  /- Theorem 9.89: the compact three-way zero-slice branch. -/
  theorem_9_89 :
    ∃ epsilon₃ : ℝ, 0 < epsilon₃ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₃ →
        ∃ C₁ : ℝ, 0 < C₁ ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M]
            [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M,
              IsCompact (Set.univ : Set M) →
              Nonempty (RepairedCanonicalNeighborhoodCertificate K epsilon C₁)

end PoincareMT
