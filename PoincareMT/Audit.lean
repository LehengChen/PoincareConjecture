import PoincareMT.Statement
import PoincareMT.Definitions.Ch01.RiemannianMetric
import PoincareMT.Definitions.Ch03.RicciFlow
import PoincareMT.Proofs.Ch01.Curvature
import PoincareMT.Proofs.Ch01.Koszul
import PoincareMT.Proofs.M03.ConnectionRegularity
import PoincareMT.Proofs.Ch01.CurvatureConnection
import PoincareMT.Proofs.M03.ConnectionExistence
import PoincareMT.Proofs.M01
import PoincareMT.Proofs.M02
import PoincareMT.Proofs.M03.ShortTime
import PoincareMT.Proofs.M03
import PoincareMT.Proofs.Ch01.ScalarOperators
import PoincareMT.Proofs.Ch04.ScalarBounds
import PoincareMT.Proofs.M04
import PoincareMT.Proofs.M05
import PoincareMT.Proofs.M06
import PoincareMT.Proofs.M07
import PoincareMT.Definitions.Ch06.LGeometry
import PoincareMT.Statements.Ch06.LGeometry
import PoincareMT.Proofs.M08
import PoincareMT.Definitions.Ch06.ReducedLength
import PoincareMT.Statements.Ch06.ReducedLength
import PoincareMT.Proofs.M09
import PoincareMT.Definitions.Ch06.ReducedVolume
import PoincareMT.Statements.Ch06.ReducedVolume
import PoincareMT.Proofs.M10
import PoincareMT.Definitions.M14Exponential
import PoincareMT.Definitions.M14GeneralizedLGeometry
import PoincareMT.Definitions.M14MeasureTransport
import PoincareMT.Definitions.M14PathCalculus
import PoincareMT.Statements.M14Exponential
import PoincareMT.Statements.M14GeneralizedLGeometry
import PoincareMT.Statements.M14PathCalculus
import PoincareMT.Proofs.M14
import PoincareMT.Definitions.M15Noncollapsing
import PoincareMT.Statements.M15Noncollapsing
import PoincareMT.Proofs.M15
import PoincareMT.Definitions.M16StructuralKappa
import PoincareMT.Statements.M16StructuralKappa
import PoincareMT.Proofs.M16
import PoincareMT.Definitions.M17BlowupSetup
import PoincareMT.Statements.M17BlowupSetup
import PoincareMT.Proofs.M17
import PoincareMT.Definitions.Ch09.AsymptoticSoliton
import PoincareMT.Definitions.M18AsymptoticSoliton
import PoincareMT.Statements.M18AsymptoticSoliton
import PoincareMT.Proofs.M18
import PoincareMT.Definitions.M19TwoDimensionalClassification
import PoincareMT.Statements.M19TwoDimensionalClassification
import PoincareMT.Proofs.M19
import PoincareMT.Definitions.M20ThreeDimensionalClassification
import PoincareMT.Statements.M20ThreeDimensionalClassification
import PoincareMT.Proofs.M20
import PoincareMT.Definitions.M21AsymptoticVolume
import PoincareMT.Statements.M21AsymptoticVolume
import PoincareMT.Proofs.M21
import PoincareMT.Definitions.M22UniversalNoncollapsing
import PoincareMT.Statements.M22UniversalNoncollapsing
import PoincareMT.Proofs.M22
import PoincareMT.Definitions.M23NormalizedKappaCompactness
import PoincareMT.Statements.M23NormalizedKappaCompactness
import PoincareMT.Proofs.M23
import PoincareMT.Definitions.M24ModelCertificates
import PoincareMT.Statements.M24ModelCertificates
import PoincareMT.Proofs.M24
import PoincareMT.Definitions.M25NeckCapTopology
import PoincareMT.Statements.M25NeckCapTopology
import PoincareMT.Proofs.M25
import PoincareMT.Definitions.M26CanonicalNeighborhoods
import PoincareMT.Statements.M26CanonicalNeighborhoods
import PoincareMT.Proofs.M26
import PoincareMT.Definitions.Ch09.ShrinkingSoliton
import PoincareMT.Definitions.Ch09.AsymptoticVolume
import PoincareMT.Definitions.Ch09.NormalizedKappaCompactness
import PoincareMT.Definitions.Ch09.NeckCapTopology
import PoincareMT.Statements.Ch09.NeckCapTopology
import PoincareMT.Definitions.Ch09.CanonicalNeighborhoods
import PoincareMT.Definitions.Ch11.BlowupLimits
import PoincareMT.Definitions.Ch11.SingularLimits
import PoincareMT.Definitions.M33BranchContinuation
import PoincareMT.Statements.M33BranchContinuation
import PoincareMT.Proofs.M33
import PoincareMT.Definitions.M34StandardCapExistence
import PoincareMT.Statements.M34StandardCapExistence
import PoincareMT.Proofs.M34
import PoincareMT.Definitions.M35StandardCapUniqueness
import PoincareMT.Statements.M35StandardCapUniqueness
import PoincareMT.Proofs.M35
import PoincareMT.Definitions.M36MetricSurgery
import PoincareMT.Statements.M36MetricSurgery
import PoincareMT.Proofs.M36
import PoincareMT.Proofs.M36.NeckCurvatureJet
import PoincareMT.Proofs.M36.SurgeryNeckSectional
import PoincareMT.Definitions.M37SurgeryFlow
import PoincareMT.Statements.M37SurgeryFlow
import PoincareMT.Proofs.M37
import PoincareMT.Definitions.M38LocalTopology
import PoincareMT.Statements.M38LocalTopology
import PoincareMT.Proofs.M38
import PoincareMT.Definitions.M39ComparisonMap
import PoincareMT.Statements.M39ComparisonMap
import PoincareMT.Proofs.M39
import PoincareMT.Definitions.M40ComparisonHomotopy
import PoincareMT.Statements.M40ComparisonHomotopy
import PoincareMT.Proofs.M40
import PoincareMT.Definitions.Ch18.LoopSpaceWidth
import PoincareMT.Statements.Ch18.LoopSpaceWidth
import PoincareMT.Definitions.Ch19.CurveEvolution
import PoincareMT.Statements.Ch19.CurveEvolution
import PoincareMT.Audit.CurveAndCap
import PoincareMT.Audit.Continuation
import PoincareMT.Audit.Kappa
import PoincareMT.Audit.Schedules
import PoincareMT.Audit.M83

/-! # Current declaration dependency audit

The audit records foundational axiom guards for accepted definitions and
explicit `sorryAx` guards for admitted proof milestones.
-/

set_option autoImplicit false

/-- info: 'PoincareMT.ThreeSphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ThreeSphere

/-- info: 'PoincareMT.RepairedPreterminalSlab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedPreterminalSlab

/-- info: 'PoincareMT.RepairedContinuationInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedContinuationInput

/-- info: 'PoincareMT.RepairedBranchContinuationData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedBranchContinuationData

/-- info: 'PoincareMT.repairedBranchContinuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedBranchContinuation

/-- info: 'PoincareMT.RepairedStandardCapExistenceData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedStandardCapExistenceData

/-- info: 'PoincareMT.repairedStandardCapExistence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedStandardCapExistence

/-- info: 'PoincareMT.RepairedStandardCapUniquenessData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedStandardCapUniquenessData

/-- info: 'PoincareMT.repairedStandardCapUniqueness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedStandardCapUniqueness

/-- info: 'PoincareMT.RepairedMetricSurgeryData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedMetricSurgeryData

/-- info: 'PoincareMT.repairedMetricSurgery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedMetricSurgery

/-- info: 'PoincareMT.RepairedSurgeryFlowData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedSurgeryFlowData

/-- info: 'PoincareMT.repairedSurgeryFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedSurgeryFlow

/-- info: 'PoincareMT.RepairedLocalSurgeryTopologyData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedLocalSurgeryTopologyData

/-- info: 'PoincareMT.repairedLocalSurgeryTopology' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedLocalSurgeryTopology

/-- info: 'PoincareMT.RepairedComparisonMapData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedComparisonMapData

/-- info: 'PoincareMT.repairedComparisonMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedComparisonMap

/-- info: 'PoincareMT.RepairedComparisonHomotopyData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedComparisonHomotopyData

/-- info: 'PoincareMT.repairedComparisonHomotopy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedComparisonHomotopy

/-- info: 'PoincareMT.SmoothPoincare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.SmoothPoincare

/-- info: 'PoincareMT.TopologicalPoincare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.TopologicalPoincare

/-- info: 'PoincareMT.OrientationCompatibleAtlas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.OrientationCompatibleAtlas

/-- info: 'PoincareMT.ClosedSimplyConnectedThreeManifoldConclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ClosedSimplyConnectedThreeManifoldConclusion

/-- info: 'PoincareMT.closedSimplyConnectedThreeManifoldTopology' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.closedSimplyConnectedThreeManifoldTopology

/-- info: 'PoincareMT.RiemannianMetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RiemannianMetric

/-- info: 'PoincareMT.RiemannianMetric.tangentNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RiemannianMetric.tangentNorm

/-- info: 'PoincareMT.euclideanUnitBallLebesgueVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.euclideanUnitBallLebesgueVolume

/-- info: 'PoincareMT.euclideanUnitBallHausdorffVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.euclideanUnitBallHausdorffVolume

/-- info: 'PoincareMT.euclideanHausdorffCalibration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.euclideanHausdorffCalibration

/-- info: 'PoincareMT.RiemannianMetric.hausdorffVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RiemannianMetric.hausdorffVolume

/-- info: 'PoincareMT.normalizedMetricVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.normalizedMetricVolume

/-- info: 'PoincareMT.normalizedMetricComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.normalizedMetricComplete

/-- info: 'PoincareMT.RiemannianMetric.pathELength' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RiemannianMetric.pathELength

/-- info: 'PoincareMT.RiemannianMetric.edist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RiemannianMetric.edist

/-- info: 'PoincareMT.RiemannianMetric.ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RiemannianMetric.ball

/-- info: 'PoincareMT.LeviCivitaData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData

/-- info: 'PoincareMT.RiemannianMetric.orthonormalBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RiemannianMetric.orthonormalBasis

/-- info: 'PoincareMT.LeviCivitaData.curvatureOnFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.curvatureOnFields

/-- info: 'PoincareMT.LeviCivitaData.curvature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.curvature

/-- info: 'PoincareMT.LeviCivitaData.curvatureTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.curvatureTensor

/-- info: 'PoincareMT.LeviCivitaData.ricci' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.ricci

/-- info: 'PoincareMT.LeviCivitaData.scalarCurvature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.scalarCurvature

/-- info: 'PoincareMT.LeviCivitaData.sectionalCurvature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.sectionalCurvature

/-- info: 'PoincareMT.LeviCivitaData.curvatureTensorNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.curvatureTensorNorm

/-- info: 'PoincareMT.LeviCivitaData.curvatureOnFields_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.curvatureOnFields_swap

/-- info: 'PoincareMT.LeviCivitaData.curvature_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.curvature_swap

/-- info: 'PoincareMT.LeviCivitaData.mvfderiv_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.mvfderiv_inner

/-- info: 'PoincareMT.LeviCivitaData.koszul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.koszul

/-- info: 'PoincareMT.LeviCivitaData.connection_eq_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.connection_eq_at

/-- info: 'PoincareMT.LeviCivitaData.contMDiffOn_connection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.contMDiffOn_connection

/-- info: 'PoincareMT.LeviCivitaData.contMDiffOn_connection_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.contMDiffOn_connection_apply

/-- info: 'PoincareMT.LeviCivitaData.curvatureOnFields_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.curvatureOnFields_eq

/-- info: 'PoincareMT.LeviCivitaData.curvature_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.curvature_eq

/-- info: 'PoincareMT.LeviCivitaData.curvatureTensor_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.curvatureTensor_eq

/-- info: 'PoincareMT.LeviCivitaData.ricci_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.ricci_eq

/-- info: 'PoincareMT.LeviCivitaData.scalarCurvature_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.scalarCurvature_eq

/-- info: 'PoincareMT.LeviCivitaData.sectionalCurvature_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.sectionalCurvature_eq

/-- info: 'PoincareMT.LeviCivitaData.curvatureTensorNorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.curvatureTensorNorm_eq

/-- info: 'PoincareMT.RiemannianMetric.IsSmoothFamilyOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RiemannianMetric.IsSmoothFamilyOn

/-- info: 'PoincareMT.RicciFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RicciFlow

/-- info: 'PoincareMT.exists_leviCivitaData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.exists_leviCivitaData

/-- info: 'PoincareMT.ShortTimeRicciFlowExistence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ShortTimeRicciFlowExistence

/-- info: 'PoincareMT.RicciFlowUniqueness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RicciFlowUniqueness

/-- info: 'PoincareMT.exists_ricciFlow_metricFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.exists_ricciFlow_metricFamily

/-- info: 'PoincareMT.shortTimeRicciFlowExistence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.shortTimeRicciFlowExistence

/-- info: 'PoincareMT.ricciFlowUniqueness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ricciFlowUniqueness

/-- info: 'PoincareMT.RicciFlowContinuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RicciFlowContinuation

/-- info: 'PoincareMT.RicciFlowLocalTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RicciFlowLocalTheory

/-- info: 'PoincareMT.ricciFlowContinuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ricciFlowContinuation

/-- info: 'PoincareMT.ricciFlowLocalTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ricciFlowLocalTheory

/-- info: 'PoincareMT.LeviCivitaData.hessianOnFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.hessianOnFields

/-- info: 'PoincareMT.LeviCivitaData.hessian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.hessian

/-- info: 'PoincareMT.LeviCivitaData.laplacian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.laplacian

/-- info: 'PoincareMT.LeviCivitaData.ricciNormSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.ricciNormSq

/-- info: 'PoincareMT.LeviCivitaData.hessianOnFields_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.hessianOnFields_eq

/-- info: 'PoincareMT.LeviCivitaData.hessian_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.hessian_eq

/-- info: 'PoincareMT.LeviCivitaData.laplacian_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.laplacian_eq

/-- info: 'PoincareMT.LeviCivitaData.ricciNormSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.ricciNormSq_nonneg

/-- info: 'PoincareMT.LeviCivitaData.scalarCurvature_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.scalarCurvature_sq_le

/-- info: 'PoincareMT.compact_min_velocity_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.compact_min_velocity_lower_bound

/-- info: 'PoincareMT.LeviCivitaData.ricciNormSq_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.ricciNormSq_eq

/--
info: 'PoincareMT.LeviCivitaData.hessian_nonneg_of_isLocalMin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.hessian_nonneg_of_isLocalMin

/--
info: 'PoincareMT.LeviCivitaData.laplacian_nonneg_of_isLocalMin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.laplacian_nonneg_of_isLocalMin

/-- info: 'PoincareMT.RicciFlow.contMDiffOn_scalarCurvature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RicciFlow.contMDiffOn_scalarCurvature

/-- info: 'PoincareMT.RicciFlow.contMDiff_scalarCurvature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RicciFlow.contMDiff_scalarCurvature

/--
info: 'PoincareMT.RicciFlow.hasDerivWithinAt_scalarCurvature' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.RicciFlow.hasDerivWithinAt_scalarCurvature

/--
info: 'PoincareMT.RicciFlow.scalarCurvature_velocity_lowerBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.RicciFlow.scalarCurvature_velocity_lowerBound

/-- info: 'PoincareMT.RicciFlow.scalarCurvature_lowerBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RicciFlow.scalarCurvature_lowerBound

/--
info: 'PoincareMT.RicciFlow.scalarCurvature_lowerBound_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.RicciFlow.scalarCurvature_lowerBound_three

/--
info: 'PoincareMT.CovariantTensorEvaluation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.CovariantTensorEvaluation

/--
info: 'PoincareMT.LeviCivitaData.covariantTensorDerivative' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.covariantTensorDerivative

/--
info: 'PoincareMT.LeviCivitaData.curvatureDerivativeNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.curvatureDerivativeNorm

/--
info: 'PoincareMT.LeviCivitaData.iteratedCovariantTensorDerivative' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.iteratedCovariantTensorDerivative

/--
info: 'PoincareMT.LeviCivitaData.NonnegativeRicciCurvature' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.NonnegativeRicciCurvature

/--
info: 'PoincareMT.LeviCivitaData.NonnegativeSectionalCurvature' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.NonnegativeSectionalCurvature

/--
info: 'PoincareMT.LeviCivitaData.ricciEvaluation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.ricciEvaluation

/--
info: 'PoincareMT.LeviCivitaData.riemannEvaluation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.riemannEvaluation

/--
info: 'PoincareMT.LeviCivitaData.tensorLaplacian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.tensorLaplacian

/--
info: 'PoincareMT.RiemannianMetric.tensorNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.RiemannianMetric.tensorNorm

/--
info: 'PoincareMT.IsSmoothCovariantTensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.IsSmoothCovariantTensor

/--
info: 'PoincareMT.LeviCivitaData.curvatureB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.curvatureB

/--
info: 'PoincareMT.LeviCivitaData.curvatureReaction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.curvatureReaction

/--
info: 'PoincareMT.LeviCivitaData.ricciReaction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.ricciReaction

/--
info: 'PoincareMT.LeviCivitaData.curvatureTensorCalculus' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.curvatureTensorCalculus

/--
info: 'PoincareMT.LeviCivitaData.curvatureDerivativeNorm_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.curvatureDerivativeNorm_zero

/--
info: 'PoincareMT.local_curvatureDerivative_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.local_curvatureDerivative_bound

/--
info: 'PoincareMT.local_curvatureDerivative_bound_of_initial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.local_curvatureDerivative_bound_of_initial

/--
info: 'PoincareMT.RicciFlow.metric_comparison_of_curvature_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.RicciFlow.metric_comparison_of_curvature_bound

/--
info: 'PoincareMT.RicciFlow.hasDerivWithinAt_curvatureTensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.RicciFlow.hasDerivWithinAt_curvatureTensor

/--
info: 'PoincareMT.RicciFlow.hasDerivWithinAt_ricci' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.RicciFlow.hasDerivWithinAt_ricci

/--
info: 'PoincareMT.RicciFlow.flat_of_scalarCurvature_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.RicciFlow.flat_of_scalarCurvature_eq_zero

/--
info: 'PoincareMT.RicciFlow.nonnegativeRicciCurvature_preserved' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.RicciFlow.nonnegativeRicciCurvature_preserved

/--
info: 'PoincareMT.RicciFlow.nonnegativeSectionalCurvature_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.RicciFlow.nonnegativeSectionalCurvature_preserved

/--
info: 'PoincareMT.LeviCivitaData.CurvatureTensorCalculus' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.CurvatureTensorCalculus

/--
info: 'PoincareMT.RicciFlowCurvatureTheory' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.RicciFlowCurvatureTheory

/--
info: 'PoincareMT.ricciFlowCurvatureTheory' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.ricciFlowCurvatureTheory

/-- info: 'PoincareMT.LeviCivitaData.IsOrthonormalPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.IsOrthonormalPair

/-- info: 'PoincareMT.LeviCivitaData.leastSectionalCurvature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.leastSectionalCurvature

/-- info: 'PoincareMT.LeviCivitaData.negativeCurvaturePart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.negativeCurvaturePart

/-- info: 'PoincareMT.HamiltonIveyPinchedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.HamiltonIveyPinchedAt

/-- info: 'PoincareMT.HamiltonIveyPinchedOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.HamiltonIveyPinchedOn

/-- info: 'PoincareMT.HamiltonIveyPinchingConclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.HamiltonIveyPinchingConclusion

/-- info: 'PoincareMT.hamiltonIveyPinching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.hamiltonIveyPinching

/-- info: 'PoincareMT.hamiltonIveyPinching_from_M04' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.hamiltonIveyPinching_from_M04

/-- info: 'PoincareMT.MetricComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.MetricComplete

/-- info: 'PoincareMT.LeviCivitaData.IsSkewCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.IsSkewCoefficient

/-- info: 'PoincareMT.LeviCivitaData.curvatureOperatorQuadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.curvatureOperatorQuadratic

/-- info: 'PoincareMT.LeviCivitaData.NonnegativeCurvatureOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.NonnegativeCurvatureOperator

/-- info: 'PoincareMT.LeviCivitaData.CurvatureOperatorBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LeviCivitaData.CurvatureOperatorBound

/-- info: 'PoincareMT.spacetimeEnergy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.spacetimeEnergy

/-- info: 'PoincareMT.HarnackAncientTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.HarnackAncientTheory

/-- info: 'PoincareMT.differentialHarnackAncientTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.differentialHarnackAncientTheory

/--
 info: 'PoincareMT.differentialHarnackAncientTheory_from_M04' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.differentialHarnackAncientTheory_from_M04

/-- info: 'PoincareMT.FlowCarrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.FlowCarrier

/-- info: 'PoincareMT.FlowCarrier.metricNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.FlowCarrier.metricNorm

/-- info: 'PoincareMT.FlowCarrier.coordinateCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.FlowCarrier.coordinateCoefficient

/-- info: 'PoincareMT.FlowCarrier.metricHausdorffVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.FlowCarrier.metricHausdorffVolume

/-- info: 'PoincareMT.FlowCarrier.metricComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.FlowCarrier.metricComplete

/-- info: 'PoincareMT.BasedFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.BasedFlow

/-- info: 'PoincareMT.BasedFlow.zeroBall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.BasedFlow.zeroBall

/-- info: 'PoincareMT.BasedFlow.ballAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.BasedFlow.ballAt

/-- info: 'PoincareMT.BasedFlow.zeroBallVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.BasedFlow.zeroBallVolume

/-- info: 'PoincareMT.BasedFlow.metricAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.BasedFlow.metricAt

/-- info: 'PoincareMT.BasedFlow.volumeCompatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.BasedFlow.volumeCompatible

/-- info: 'PoincareMT.SmoothSpacetimeEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.SmoothSpacetimeEmbedding

/-- info: 'PoincareMT.SpacetimeEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.SpacetimeEmbedding

/-- info: 'PoincareMT.CurvatureBoundOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.CurvatureBoundOn

/-- info: 'PoincareMT.PointedFlowSequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.PointedFlowSequence

/-- info: 'PoincareMT.pullbackInnerValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.pullbackInnerValue

/-- info: 'PoincareMT.MetricJet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.MetricJet

/-- info: 'PoincareMT.PointedGeometricConvergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.PointedGeometricConvergence

/-- info: 'PoincareMT.PointedRicciFlowCompactnessHypotheses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.PointedRicciFlowCompactnessHypotheses

/-- info: 'PoincareMT.PointedRicciFlowCompactnessConclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.PointedRicciFlowCompactnessConclusion

/-- info: 'PoincareMT.pointedRicciFlowCompactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.pointedRicciFlowCompactness

/-- info: 'PoincareMT.pointedRicciFlowCompactness_from_M04' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.pointedRicciFlowCompactness_from_M04

/-- info: 'PoincareMT.NormalizedInitialMetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.NormalizedInitialMetric

/-- info: 'PoincareMT.NormalizedInitialMetricConclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.NormalizedInitialMetricConclusion

/-- info: 'PoincareMT.existsNormalizedInitialMetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.existsNormalizedInitialMetric

/-- info: 'PoincareMT.BackwardTimePath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.BackwardTimePath

/-- info: 'PoincareMT.SmoothAlongCurveExtensionOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.SmoothAlongCurveExtensionOn

/-- info: 'PoincareMT.LGeodesicTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.LGeodesicTheory

/-- info: 'PoincareMT.lGeodesicExistenceAndVariation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.lGeodesicExistenceAndVariation

/-- info: 'PoincareMT.ReducedLengthRegularPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ReducedLengthRegularPoint

/-- info: 'PoincareMT.ReducedLengthDifferentialTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ReducedLengthDifferentialTheory

/-- info: 'PoincareMT.reducedLengthDifferentialInequalities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.reducedLengthDifferentialInequalities

/-- info: 'PoincareMT.reducedLengthDifferentialInequalities_from_M04_M08' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.reducedLengthDifferentialInequalities_from_M04_M08

/-- info: 'PoincareMT.ReducedVolumeTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ReducedVolumeTheory

/-- info: 'PoincareMT.reducedVolumeMonotonicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.reducedVolumeMonotonicity

/-- info: 'PoincareMT.reducedVolumeMonotonicity_from_M08_M09' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.reducedVolumeMonotonicity_from_M08_M09




/-- info: 'PoincareMT.noncollapsingGeneralizedAndCompact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.noncollapsingGeneralizedAndCompact

/-- info: 'PoincareMT.SingularTimeAssumptions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.SingularTimeAssumptions
/-- info: 'PoincareMT.SingularLimitConclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.SingularLimitConclusion
/-- info: 'PoincareMT.C1FreeLoopSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.C1FreeLoopSpace
/-- info: 'PoincareMT.FreeTwoSphereClassCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.FreeTwoSphereClassCertificate
