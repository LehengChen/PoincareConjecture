import PoincareMT.Proofs.M18
import PoincareMT.Proofs.M19
import PoincareMT.Proofs.M20
import PoincareMT.Proofs.M21
import PoincareMT.Proofs.M22
import PoincareMT.Proofs.M23
import PoincareMT.Proofs.M24
import PoincareMT.Proofs.M25
import PoincareMT.Proofs.M26
import PoincareMT.Proofs.M27
import PoincareMT.Proofs.M28
import PoincareMT.Proofs.M29

/-!
# Chapter 9 declaration dependency audit

Definitions and statement types use the conventional foundational axioms.
The numbered skeleton theorems retain their explicitly inventoried admissions.
-/

set_option autoImplicit false

/-- info: 'PoincareMT.AncientCompactTimeConvergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.AncientCompactTimeConvergence

/-- info: 'PoincareMT.AncientAsymptoticSolitonLimitData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.AncientAsymptoticSolitonLimitData

/-- info: 'PoincareMT.AncientAsymptoticSolitonPredecessors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.AncientAsymptoticSolitonPredecessors

/-- info: 'PoincareMT.AncientAsymptoticSolitonConclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.AncientAsymptoticSolitonConclusion

/-- info: 'PoincareMT.AncientAsymptoticSolitonTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.AncientAsymptoticSolitonTheory

/--  info: 'PoincareMT.ancientAsymptoticSolitonLimits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ancientAsymptoticSolitonLimits

/--  info: 'PoincareMT.ancientAsymptoticSolitonTheory_from_predecessors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ancientAsymptoticSolitonTheory_from_predecessors

/-- info: 'PoincareMT.TwoDimensionalAncientRoundCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.TwoDimensionalAncientRoundCertificate

/-- info: 'PoincareMT.TwoDimensionalAsymptoticRoundCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.TwoDimensionalAsymptoticRoundCertificate

/-- info: 'PoincareMT.TwoDimensionalClassificationPredecessors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.TwoDimensionalClassificationPredecessors

/-- info: 'PoincareMT.TwoDimensionalAsymptoticRoundTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.TwoDimensionalAsymptoticRoundTheory

/-- info: 'PoincareMT.TwoDimensionalClassificationTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.TwoDimensionalClassificationTheory

set_option linter.style.longLine false
/--
info: 'PoincareMT.twoDimensionalAncientAndShrinkingSolitonClassification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.twoDimensionalAncientAndShrinkingSolitonClassification
set_option linter.style.longLine true

/-- info: 'PoincareMT.twoDimensionalClassificationTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.twoDimensionalClassificationTheory

/-- info: 'PoincareMT.ThreeDimensionalSolitonModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ThreeDimensionalSolitonModel

/-- info: 'PoincareMT.ThreeDimensionalClassificationData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ThreeDimensionalClassificationData

set_option linter.style.longLine false
/--
info: 'PoincareMT.ThreeDimensionalAsymptoticClassificationCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.ThreeDimensionalAsymptoticClassificationCertificate
set_option linter.style.longLine true

/-- info: 'PoincareMT.ThreeDimensionalClassificationPredecessors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ThreeDimensionalClassificationPredecessors

/-- info: 'PoincareMT.m20TwoDimensionalProvider_from_M19' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m20TwoDimensionalProvider_from_M19

/-- info: 'PoincareMT.m20CompactLocalFlowProvider_from_M03' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m20CompactLocalFlowProvider_from_M03

/-- info: 'PoincareMT.ThreeDimensionalAsymptoticClassificationTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ThreeDimensionalAsymptoticClassificationTheory

/-- info: 'PoincareMT.ThreeDimensionalClassificationTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ThreeDimensionalClassificationTheory

set_option linter.style.longLine false
/--
info: 'PoincareMT.threeDimensionalAncientAndShrinkingSolitonClassification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.threeDimensionalAncientAndShrinkingSolitonClassification
set_option linter.style.longLine true

/-- info: 'PoincareMT.threeDimensionalClassificationTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.threeDimensionalClassificationTheory

/-- info: 'PoincareMT.AsymptoticVolumeRatioSliceData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.AsymptoticVolumeRatioSliceData

/-- info: 'PoincareMT.AsymptoticVolumeRatioPredecessors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.AsymptoticVolumeRatioPredecessors

/-- info: 'PoincareMT.AsymptoticVolumeRatioTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.AsymptoticVolumeRatioTheory

/-- info: 'PoincareMT.asymptoticVolumeRatioBishopGromov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.asymptoticVolumeRatioBishopGromov

/-- info: 'PoincareMT.asymptoticVolumeRatioTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.asymptoticVolumeRatioTheory

/-- info: 'PoincareMT.UniversalNoncollapsingData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.UniversalNoncollapsingData

/-- info: 'PoincareMT.M22UniversalNoncollapsingPredecessors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M22UniversalNoncollapsingPredecessors

/-- info: 'PoincareMT.UniversalNoncollapsingConclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.UniversalNoncollapsingConclusion

/-- info: 'PoincareMT.m22UniversalNoncollapsingAndZeroAVR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m22UniversalNoncollapsingAndZeroAVR

/-- info: 'PoincareMT.m22UniversalNoncollapsingConclusionTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m22UniversalNoncollapsingConclusionTheory

/-- info: 'PoincareMT.NormalizedKappaCompactnessData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.NormalizedKappaCompactnessData

/-- info: 'PoincareMT.M23InteriorConvergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M23InteriorConvergence

/-! M24 model definitions remain admission-free; the quotient normal form is
produced under the existing numbered theorem's skeleton admission. -/
/-- info: 'PoincareMT.M24QuotientFlowTransport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M24QuotientFlowTransport

/-- info: 'PoincareMT.M24TwistedSphereLineCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M24TwistedSphereLineCertificate

/-- info: 'PoincareMT.M24QuotientNormalForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M24QuotientNormalForm

/-- info: 'PoincareMT.M24ProjectivePlaneLineCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M24ProjectivePlaneLineCertificate

/-- info: 'PoincareMT.M24SphericalSpaceFormCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M24SphericalSpaceFormCertificate

/-- info: 'PoincareMT.M24ModelInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M24ModelInput

/-- info: 'PoincareMT.RepairedKappaModelCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedKappaModelCertificate

/-- info: 'PoincareMT.M24CertificateMatches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M24CertificateMatches

/-- info: 'PoincareMT.RepairedModelCertificateTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedModelCertificateTheory

/-- info: 'PoincareMT.m24ModelCertificates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m24ModelCertificates

/-- info: 'PoincareMT.m24ModelCertificateTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m24ModelCertificateTheory

/-! M25 neck/cap topology definitions and statements are admission-free; only
the numbered theorem and its forwarding wrapper carry the intentional
skeleton admission. -/
/-- info: 'PoincareMT.RepairedNeckCapTopologyData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedNeckCapTopologyData

/-- info: 'PoincareMT.RepairedNeckCapTopologyTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedNeckCapTopologyTheory

/-- info: 'PoincareMT.m25NeckCapTopology' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m25NeckCapTopology

/-- info: 'PoincareMT.m25NeckCapTopologyTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m25NeckCapTopologyTheory

/-- info: 'PoincareMT.M23NormalizedKappaCompactnessPredecessors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M23NormalizedKappaCompactnessPredecessors

/-- info: 'PoincareMT.M23LocalCurvatureEstimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M23LocalCurvatureEstimate

/-- info: 'PoincareMT.M23AllTimeCurvatureControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M23AllTimeCurvatureControl

/-- info: 'PoincareMT.M23LimitBoundedCurvature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M23LimitBoundedCurvature

/-- info: 'PoincareMT.M23TerminalNoncollapsing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M23TerminalNoncollapsing

/-- info: 'PoincareMT.M23TerminalCompleteAtZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M23TerminalCompleteAtZero

/-- info: 'PoincareMT.M23TerminalBoundedAtZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M23TerminalBoundedAtZero

/-- info: 'PoincareMT.M23TerminalNormalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M23TerminalNormalization

/-- info: 'PoincareMT.M23TerminalExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M23TerminalExtension

/-- info: 'PoincareMT.RedesignNormalizedKappaCompactnessConclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RedesignNormalizedKappaCompactnessConclusion

/-- info: 'PoincareMT.m23NormalizedKappaCompactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m23NormalizedKappaCompactness

/-- info: 'PoincareMT.m23NormalizedKappaCompactnessConclusionTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m23NormalizedKappaCompactnessConclusionTheory

/-- info: 'PoincareMT.AncientKappaSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.AncientKappaSolution

/-- info: 'PoincareMT.AncientRescalingSequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.AncientRescalingSequence

/-- info: 'PoincareMT.AncientGeometricConvergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.AncientGeometricConvergence

/-- info: 'PoincareMT.AsymptoticSolitonLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.AsymptoticSolitonLimit




/-- info: 'PoincareMT.GradientShrinkingSolitonData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.GradientShrinkingSolitonData

/-- info: 'PoincareMT.ShrinkingSolitonFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ShrinkingSolitonFlow














/-- info: 'PoincareMT.RepairedCanonicalNeighborhoodTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedCanonicalNeighborhoodTheory

/-- info: 'PoincareMT.M26CanonicalNeighborhoodPredecessors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M26CanonicalNeighborhoodPredecessors

/-- info: 'PoincareMT.m26CanonicalNeighborhoods' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m26CanonicalNeighborhoods

/-- info: 'PoincareMT.M27StrongCanonicalNeighborhood' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M27StrongCanonicalNeighborhood

/-- info: 'PoincareMT.RepairedKappaAlternativeTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedKappaAlternativeTheory

/-- info: 'PoincareMT.M27KappaAlternativePredecessors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M27KappaAlternativePredecessors

/-- info: 'PoincareMT.m27KappaAlternatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m27KappaAlternatives

/-- info: 'PoincareMT.RepairedBoundedDistanceEstimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedBoundedDistanceEstimate

/-- info: 'PoincareMT.RepairedBoundedDistanceTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedBoundedDistanceTheory

/-- info: 'PoincareMT.M28BoundedDistancePredecessors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M28BoundedDistancePredecessors

/-- info: 'PoincareMT.m28BoundedDistance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m28BoundedDistance

/-- info: 'PoincareMT.GeneralizedBoundedDistanceHypotheses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.GeneralizedBoundedDistanceHypotheses

/-- info: 'PoincareMT.GeneralizedCanonicalControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.GeneralizedCanonicalControl

/-- info: 'PoincareMT.RepairedGeneralizedBoundedDistanceTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedGeneralizedBoundedDistanceTheory

/-- info: 'PoincareMT.m29GeneralizedBoundedDistance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m29GeneralizedBoundedDistance
