import PoincareMT.Definitions.M20ThreeDimensionalClassification
import PoincareMT.Statements.Ch04.Continuation
import PoincareMT.Statements.Ch04.CurvatureTheory
import PoincareMT.Statements.Ch04.Harnack
import PoincareMT.Statements.Ch05.Compactness
import PoincareMT.Statements.M18AsymptoticSoliton
import PoincareMT.Statements.M19TwoDimensionalClassification

/-!
# M20 three-dimensional classification statement

This milestone packages Morgan--Tian Theorem 9.42 and its asymptotic-limit
consumers (Corollaries 9.52--9.54). The predecessor fields name the compact
M03 and ordinary M04/M06/M07 services, the actual generic M18 limit service, and the typed
M19 two-dimensional result.  No desired limit or old asymptotic-soliton
field is stored as an input.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-! The direct ordinary-flow services used while proving Theorem 9.42 and
Corollaries 9.52--9.54. The M18 and M19 fields are applied services;
their earlier theorem dependencies were supplied when constructing them. -/
structure ThreeDimensionalClassificationPredecessors : Prop where
  local_flow :
    ∀ (n : ℕ) (N : Type u) [TopologicalSpace N] [T2Space N]
      [SecondCountableTopology N]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
      [IsManifold (𝓡 n) ∞ N] [CompactSpace N],
      RicciFlowLocalTheory n N
  curvature : RicciFlowCurvatureTheory.{u}
  harnack : HarnackAncientTheory.{u}
  pointed_compactness :
    ∀ {n : ℕ} {T' T : ℝ}, T' < 0 → 0 < T →
      ∀ H : PointedRicciFlowCompactnessHypotheses n T' T,
        Nonempty (PointedRicciFlowCompactnessConclusion H)
  m18 : AncientAsymptoticSolitonTheory.{u} 3
  two_dimensional :
    ∀ {N : Type u} [TopologicalSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
      [IsManifold (𝓡 2) ∞ N] [MeasurableSpace N] [BorelSpace N]
      [T2Space N] [T3Space N] [SecondCountableTopology N]
      [ConnectedSpace N],
      TwoDimensionalClassificationTheory (M := N)

/-! The actual M18 branch of M20. The sequence and limit witness refer to
the same objects, so this service cannot classify an
unrelated prebuilt limit. -/
structure ThreeDimensionalAsymptoticClassificationTheory
    (K : AncientKappaSolution 3 M) : Prop where
  classify :
    ∀ S : AncientRescalingSequence K,
      ∃ L : AncientAsymptoticSolitonLimitData S,
        ThreeDimensionalAsymptoticClassificationCertificate S L

/-! The complete M20 output: static three-dimensional shrinking-soliton
classification, and construction and classification of a limit of each
prescribed rescaling sequence. -/
structure ThreeDimensionalClassificationTheory : Prop where
  classify : ∀ S : GradientShrinkingSolitonData 3 M,
    Nonempty (ThreeDimensionalClassificationData S)
  asymptotic_classify : ∀ K : AncientKappaSolution 3 M,
    Nonempty (ThreeDimensionalAsymptoticClassificationTheory K)

end PoincareMT
