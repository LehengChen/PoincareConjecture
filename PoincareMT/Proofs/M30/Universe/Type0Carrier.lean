import PoincareMT.Definitions.Ch11.BlowupLimits
import PoincareMT.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.Small

/-!
# Universe-zero models of generalized slices

The Type-0 compactness route in the reviewed M30 contract uses ordinary
representatives of the slices before Morgan--Tian Theorem 5.11 and Proposition
5.14, pp. 89--91. The existing countable-basis shrinking equivalence transports
the smooth atlas and the actual metric, including empty or disconnected
slices. Extended distance, completeness, curvature, and volume are retained.

The lower services are `Poincare.Manifold.shrinkDiffeomorph` and
`RiemannianMetric.shrink`. Their application to the frozen slice carrier is
recorded in `proof-work/tasks/M30/derivations/universe-route.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

attribute [local instance] RiemannianMetric.smallCarrier
  RiemannianMetric.smallChartedSpace RiemannianMetric.smallIsManifold
  RiemannianMetric.smallT3Space RiemannianMetric.smallMeasurableSpace
  RiemannianMetric.smallBorelSpace

/-- The universe-zero representative used for the compactness steps of
Theorem 5.11 and Proposition 5.14, pp. 89--91. No point or connectedness is
required of the original generalized slice. -/
noncomputable def smallSliceCarrier (C : GeneralizedSliceCarrier.{u}) :
    GeneralizedSliceCarrier.{0} where
  carrier := Shrink.{0} C.carrier
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := (Poincare.Topology.SecondCountable.homeomorphShrink C.carrier).t2Space
  t3Space := inferInstance
  secondCountable := by
    let e := Poincare.Topology.SecondCountable.homeomorphShrink C.carrier
    exact e.symm.isEmbedding.secondCountableTopology

/-- The smooth equivalence to the selected small slice, with precisely the
transported atlas used before Theorem 5.11, pp. 89--90. -/
noncomputable def smallSliceDiffeomorph (C : GeneralizedSliceCarrier.{u}) :
    C.carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (smallSliceCarrier C).carrier :=
  Poincare.Manifold.shrinkDiffeomorph (𝓡 3) C.carrier

/-- The representative's smooth equivalence is the canonical shrinking
equivalence (the Type-0 compactness route for Theorem 5.11, pp. 89--90). -/
@[simp] theorem smallSliceDiffeomorph_toEquiv (C : GeneralizedSliceCarrier.{u}) :
    (smallSliceDiffeomorph C).toEquiv = equivShrink C.carrier := rfl

/-- Pull back the retained metric to the small slice, as required for the
ordinary compactness representation in Theorem 5.11, pp. 89--90. -/
noncomputable def smallSliceMetric (C : GeneralizedSliceCarrier.{u})
    (g : RiemannianMetric 3 C.carrier) :
    RiemannianMetric 3 (smallSliceCarrier C).carrier :=
  g.shrink

/-- The actual tangent inner product is the pullback by the inverse smooth
equivalence (Definition 5.12, p. 90). -/
@[simp] theorem smallSliceMetric_inner (C : GeneralizedSliceCarrier.{u})
    (g : RiemannianMetric 3 C.carrier) (x : (smallSliceCarrier C).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (smallSliceMetric C g).inner x v w =
      g.inner ((smallSliceDiffeomorph C).symm x)
        (mfderiv (𝓡 3) (𝓡 3) (smallSliceDiffeomorph C).symm x v)
        (mfderiv (𝓡 3) (𝓡 3) (smallSliceDiffeomorph C).symm x w) := rfl

/-- Intrinsic extended distances, including infinite distances between
components, are retained in the representative (Theorem 5.11, pp. 89--90). -/
@[simp] theorem smallSliceMetric_edist (C : GeneralizedSliceCarrier.{u})
    (g : RiemannianMetric 3 C.carrier) (x y : (smallSliceCarrier C).carrier) :
    (smallSliceMetric C g).edist x y =
      g.edist ((smallSliceDiffeomorph C).symm x) ((smallSliceDiffeomorph C).symm y) :=
  g.shrink_edist x y

/-- Corresponding metric balls have exactly the same real radius in the
compactness representative (Theorem 5.11, pp. 89--90). -/
theorem smallSliceMetric_image_ball (C : GeneralizedSliceCarrier.{u})
    (g : RiemannianMetric 3 C.carrier) (x : (smallSliceCarrier C).carrier) (r : ℝ) :
    (smallSliceDiffeomorph C).symm '' (smallSliceMetric C g).ball x r =
      g.ball ((smallSliceDiffeomorph C).symm x) r :=
  g.shrink_image_ball x r

/-- Completeness is preserved in both directions by the small metric model
used for Theorem 5.11 and Proposition 5.14, pp. 89--91. -/
@[simp] theorem smallSliceMetric_metricComplete_iff (C : GeneralizedSliceCarrier.{u})
    (g : RiemannianMetric 3 C.carrier) :
    MetricComplete (smallSliceMetric C g) ↔ MetricComplete g :=
  g.shrink_metricComplete_iff

/-- The representative's actual Levi-Civita data retain the original scalar
curvature for every compatible connection (Theorem 5.11, pp. 89--90). -/
@[simp] theorem smallSliceMetric_scalarCurvature (C : GeneralizedSliceCarrier.{u})
    (g : RiemannianMetric 3 C.carrier) (D : LeviCivitaData g)
    (x : (smallSliceCarrier C).carrier) :
    (smallSliceMetric C g).leviCivitaData.scalarCurvature x =
      D.scalarCurvature ((smallSliceDiffeomorph C).symm x) :=
  g.shrink_scalarCurvature D x

/-- The selected intrinsic volumes agree on every corresponding set, for
the noncollapsing input to Theorem 5.11, pp. 89--90. -/
theorem smallSliceMetric_volumeMeasure_image (C : GeneralizedSliceCarrier.{u})
    (g : RiemannianMetric 3 C.carrier) (s : Set (smallSliceCarrier C).carrier) :
    g.volumeMeasure ((smallSliceDiffeomorph C).symm '' s) =
      (smallSliceMetric C g).volumeMeasure s :=
  RiemannianMetric.volumeMeasure_image_diffeomorph (smallSliceMetric C g) g
    (smallSliceDiffeomorph C).symm (smallSliceMetric_inner C g) s

/-- The actual volume of each metric ball is preserved in the Type-0
compactness representative (Theorem 5.11, pp. 89--90). -/
@[simp] theorem smallSliceMetric_volumeMeasure_ball (C : GeneralizedSliceCarrier.{u})
    (g : RiemannianMetric 3 C.carrier) (x : (smallSliceCarrier C).carrier) (r : ℝ) :
    (smallSliceMetric C g).volumeMeasure ((smallSliceMetric C g).ball x r) =
      g.volumeMeasure (g.ball ((smallSliceDiffeomorph C).symm x) r) :=
  RiemannianMetric.volumeMeasure_ball_diffeomorph (smallSliceMetric C g) g
    (smallSliceDiffeomorph C).symm (smallSliceMetric_inner C g) x r

end PoincareMT.M30
