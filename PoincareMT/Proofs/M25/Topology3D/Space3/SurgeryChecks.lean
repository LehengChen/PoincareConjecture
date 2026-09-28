import PoincareMT.Proofs.M25.Topology3D.Space3.RegularSurgeryData
import PoincareMT.Proofs.M25.Topology3D.Space3.SurgeryMatchingProfile
import PoincareMT.Proofs.M25.Topology3D.Space3.NorthSphereChart
import PoincareMT.Proofs.M25.Topology3D.Space3.CrossCofactor
import PoincareMT.Proofs.M25.Topology3D.Space3.SurgeryCapIntersection
import PoincareMT.Proofs.M25.Topology3D.Space3.SurgeryNorthChart
import PoincareMT.Proofs.M25.Topology3D.Space3.SurgeryNeighborhood
import PoincareMT.Proofs.M25.Topology3D.Space3.SurgeryPasting
import PoincareMT.Proofs.M25.Topology3D.Space3.SurgeryReplacement
import PoincareMT.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareMT.Proofs.M25.Topology3D.Space3.RegularSurgeryFromTube
import PoincareMT.Proofs.M25.Topology3D.Space3.SurgerySmoothReplacement
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsFamily
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallCommonCap
import PoincareMT.Proofs.M25.Topology3D.Space3.ImmersedSphereNormal
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReferenceProfile
import PoincareMT.Proofs.M25.Topology3D.Space3.SurgeryPair
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsProfilePath
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReferenceVertical
import PoincareMT.Proofs.M25.Topology3D.Space3.TransverseSphereCollar
import PoincareMT.Proofs.M25.Topology3D.Space3.RegularDiscSurgery
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsProfileFlow
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReferenceModel
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReferenceChart
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCanonicalEvolution
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.NativeCapCore
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.RetainedCapPlacement
import PoincareMT.Proofs.M25.Topology3D.Space3.SurgeryEventRegions
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallNativeCapChart
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallCorrectedChart
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallCapNormalization
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsScaleTransport
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReunionMap
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.EventCapInheritance
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FamilySurgeryEvent
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FamilyInnermostTube
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FamilyLevelDeletion
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FiniteHeightCuts
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.CriticalHeightIsolation
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.InitialLevelFamily
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.EventMorseTransport
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCanonicalNormalization
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallEventReunion
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FamilySurgeryReindex
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FiniteFamilySurgeryStep
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCapInheritance
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsAnnularChart
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsAnnularEvolution
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsRadialPhase
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsRadialization
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsRadialCap
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsAnnularSupport
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsSupportedMatching
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsSupportedCap
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsClampedTransition
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsOriginalProfileAlignment
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsPhysicalAlignment
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsFullCapAlignment
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallEventReferenceModel
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallEventContainment
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FamilySurgeryHistory
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCutPreservation
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallDiscLinear
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallDiscExtension
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallCapGermCorrection
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallEventCapGerm
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCapEnd
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsEndLabels
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCapEndCaller
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsLevels
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseProduct
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsTubeLabels
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMatching
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCapTransfer
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsBallModel
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallEventSupport
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallEventCompression
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReconstruction
import PoincareMT.Proofs.M25.Topology3D.Space3.Reverse.FamilyBallReconstruction
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCutState
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCutStateStep
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCutHistory
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.InitialCollarCutState
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCutSides
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FamilySourceAtlas
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsTwoEnds
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsTwoCaps
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsBall
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCoreGeometry
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FamilySourceAtlasHistory
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.FamilySourceMorse
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.TerminalCollarMorseFamily
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.RegularCoreExtrema
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.RegularCoreFlowData
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.RegularCoreTransport
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreProtection
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreDisc
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreComplement
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.RegularCompactSurfaceFlow
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.RegularCoreSeamFlow
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.RegularCoreEnds
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.RegularTerminalBall
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreMiddleGeometry
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreTransport
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreSeamNeighborhoods
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreSeamFlow
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreHeightBarriers
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreEnds
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseMeridian
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseGraphShear
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseProjection
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseProjectionRegular
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseGraph
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseNormalization
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.ExtremumRegularBand
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.ExtremumTerminalBall
import PoincareMT.Proofs.M25.Topology3D.Space3.Decomposition.TerminalSaddleData
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.SaddleDiscClassification
import PoincareMT.Proofs.M25.Topology3D.Space3.Base.SaddleLowerLevelAssembly
import PoincareMT.Proofs.M25.Topology3D.Space3.SurgeryTerminalChecks

/-!
# Axiom checks for the regular-surgery constructions

Declaration-complete audit of the source collars, rectified discs, and
explicit surgery coordinates. Mathematical source: Hatcher, Notes on
Basic 3-Manifold Topology, Theorem 1.1 and Lemmas 1.2-1.3, pp. 1-3, and
the reviewed regular-disc-surgery derivation of 2026-09-22.
-/

set_option autoImplicit false

-- This audit module intentionally prints each checked declaration's axiom dependencies.
set_option linter.hashCommand false

#print axioms PoincareMT.M25.Topology3D.exists_collar_surface_source_pullback
#print axioms PoincareMT.M25.Topology3D.tube_boundary_smooth_immersion
#print axioms PoincareMT.M25.Topology3D.exists_manifold_patch_local_inverse
#print axioms PoincareMT.M25.Topology3D.manifold_patch_isOpen_image
#print axioms PoincareMT.M25.Topology3D.manifold_patch_isOpenMap_restrict
#print axioms PoincareMT.M25.Topology3D.manifoldPatchChart
#print axioms PoincareMT.M25.Topology3D.manifoldPatchChart_apply
#print axioms PoincareMT.M25.Topology3D.manifoldPatchChart_source
#print axioms PoincareMT.M25.Topology3D.manifoldPatchChart_target
#print axioms PoincareMT.M25.Topology3D.manifoldPatchChart_symm_contMDiffOn
#print axioms PoincareMT.M25.Topology3D.exists_source_tube_chart
#print axioms PoincareMT.M25.Topology3D.source_collar_slice_smooth_immersion
#print axioms PoincareMT.M25.Topology3D.collar_complement_halves
#print axioms PoincareMT.M25.Topology3D.sourceDisc_boundary_image
#print axioms PoincareMT.M25.Topology3D.source_disc_collar_halves
#print axioms PoincareMT.M25.Topology3D.circleDirection
#print axioms PoincareMT.M25.Topology3D.circleDirection_coe
#print axioms PoincareMT.M25.Topology3D.circleDirection_smul
#print axioms PoincareMT.M25.Topology3D.circleDirection_coe_unit
#print axioms PoincareMT.M25.Topology3D.circleDirection_norm_smul
#print axioms PoincareMT.M25.Topology3D.circleDirection_contMDiffOn
#print axioms PoincareMT.M25.Topology3D.circleRadialMap
#print axioms PoincareMT.M25.Topology3D.circleRadialMap_norm
#print axioms PoincareMT.M25.Topology3D.circleRadialMap_contMDiff
#print axioms PoincareMT.M25.Topology3D.circleRadialInverse_contMDiffOn
#print axioms PoincareMT.M25.Topology3D.circleRadialChart
#print axioms PoincareMT.M25.Topology3D.circleRadialChart_apply
#print axioms PoincareMT.M25.Topology3D.circleRadialChart_symm_apply
#print axioms PoincareMT.M25.Topology3D.circleRadialChart_source
#print axioms PoincareMT.M25.Topology3D.circleRadialChart_target
#print axioms PoincareMT.M25.Topology3D.circleRadialChart_contMDiffOn
#print axioms PoincareMT.M25.Topology3D.circleRadialChart_symm_contMDiffOn
#print axioms PoincareMT.M25.Topology3D.radiusToCollarTime
#print axioms PoincareMT.M25.Topology3D.source_disc_collar_rectification
#print axioms PoincareMT.M25.Topology3D.exists_rectified_source_disc_chart
#print axioms PoincareMT.M25.Topology3D.circleTimeTranslation
#print axioms PoincareMT.M25.Topology3D.exists_centered_source_collar
#print axioms PoincareMT.M25.Topology3D.circleTimeReflection
#print axioms PoincareMT.M25.Topology3D.exists_reflected_source_collar
#print axioms PoincareMT.M25.Topology3D.source_sphere_signed_discs_of_planar
#print axioms PoincareMT.M25.Topology3D.source_disc_nonpositive_exterior
#print axioms PoincareMT.M25.Topology3D.RectifiedSourceDiscPair
#print axioms PoincareMT.M25.Topology3D.exists_rectified_source_disc_pair
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryData
#print axioms PoincareMT.M25.Topology3D.exists_regular_surgery_data
#print axioms PoincareMT.M25.Topology3D.surgeryMatchingRadius
#print axioms PoincareMT.M25.Topology3D.surgeryMatchingRadius_contDiff
#print axioms PoincareMT.M25.Topology3D.surgeryMatchingRadius_one
#print axioms PoincareMT.M25.Topology3D.surgeryMatchingRadius_hasDerivAt_one
#print axioms PoincareMT.M25.Topology3D.surgeryMatchingCollar
#print axioms PoincareMT.M25.Topology3D.surgeryMatchingCollar_contDiffOn
#print axioms PoincareMT.M25.Topology3D.surgeryMatchingCollar_fixed
#print axioms PoincareMT.M25.Topology3D.surgeryMatchingCollar_fderiv_normal
#print axioms PoincareMT.M25.Topology3D.exists_surgery_matching_diffeomorph
#print axioms PoincareMT.M25.Topology3D.northSphereVector
#print axioms PoincareMT.M25.Topology3D.northSphereVector_norm
#print axioms PoincareMT.M25.Topology3D.northSpherePoint
#print axioms PoincareMT.M25.Topology3D.northSpherePoint_coordinates
#print axioms PoincareMT.M25.Topology3D.northSphereCoordinate
#print axioms PoincareMT.M25.Topology3D.northSphereDomain
#print axioms PoincareMT.M25.Topology3D.northSpherePoint_mem_domain
#print axioms PoincareMT.M25.Topology3D.northSphereCoordinate_point
#print axioms PoincareMT.M25.Topology3D.sphere_height_coordinates_sq
#print axioms PoincareMT.M25.Topology3D.northSpherePoint_coordinate
#print axioms PoincareMT.M25.Topology3D.northSphereVector_contDiff
#print axioms PoincareMT.M25.Topology3D.northSpherePoint_contMDiff
#print axioms PoincareMT.M25.Topology3D.northSphereDomain_isOpen
#print axioms PoincareMT.M25.Topology3D.northSphereCoordinate_contMDiffOn
#print axioms PoincareMT.M25.Topology3D.northSphereChart
#print axioms PoincareMT.M25.Topology3D.northSphereChart_contMDiffOn
#print axioms PoincareMT.M25.Topology3D.northSphereChart_symm_contMDiff
#print axioms PoincareMT.M25.Topology3D.northSpherePoint_height_nonneg_iff
#print axioms PoincareMT.M25.Topology3D.northSpherePoint_image_closedBall
#print axioms PoincareMT.M25.Topology3D.northSpherePoint_equator
#print axioms PoincareMT.M25.Topology3D.northern_hemisphere_subset_chart_source
#print axioms PoincareMT.M25.Topology3D.northSphereChart_image_northern_hemisphere
#print axioms PoincareMT.M25.Topology3D.mulVec_crossProduct_cofactor
#print axioms PoincareMT.M25.Topology3D.contDiff_adjugate_fin_three
#print axioms PoincareMT.M25.Topology3D.contDiff_adjugate_transpose_mulVec
#print axioms PoincareMT.M25.Topology3D.surgeryCapModel
#print axioms PoincareMT.M25.Topology3D.surgeryCapModel_contMDiff
#print axioms PoincareMT.M25.Topology3D.surgeryCapModel_fst_norm_le
#print axioms PoincareMT.M25.Topology3D.surgeryCapModel_cylinder
#print axioms PoincareMT.M25.Topology3D.surgeryCapModel_flat_south
#print axioms PoincareMT.M25.Topology3D.surgeryCapModel_snd_nonpos_iff
#print axioms PoincareMT.M25.Topology3D.surgeryCapModel_snd_neg_iff
#print axioms PoincareMT.M25.Topology3D.surgeryCapModel_snd_pos_iff
#print axioms PoincareMT.M25.Topology3D.surgeryCapModel_exists_height_bound
#print axioms PoincareMT.M25.Topology3D.surgeryCapCoordinates
#print axioms PoincareMT.M25.Topology3D.surgeryCapCoordinates_contMDiff
#print axioms PoincareMT.M25.Topology3D.surgeryCapCoordinates_fst_norm_le
#print axioms PoincareMT.M25.Topology3D.surgeryCapCoordinates_cylinder
#print axioms PoincareMT.M25.Topology3D.surgeryCapCoordinates_flat_south
#print axioms PoincareMT.M25.Topology3D.surgeryCapCoordinates_signed_height
#print axioms PoincareMT.M25.Topology3D.surgeryCapCoordinates_south_height_bounds
#print axioms PoincareMT.M25.Topology3D.surgeryCapPlacementDiffeomorph
#print axioms PoincareMT.M25.Topology3D.surgeryCapPlacementDiffeomorph_apply
#print axioms PoincareMT.M25.Topology3D.surgeryCapPlacementDiffeomorph_symm_apply
#print axioms PoincareMT.M25.Topology3D.surgeryCapAmbientDiffeomorph
#print axioms PoincareMT.M25.Topology3D.surgeryCapCoordinates_eq_ambient
#print axioms PoincareMT.M25.Topology3D.surgeryCapCoordinates_injective
#print axioms PoincareMT.M25.Topology3D.surgeryCapCoordinates_mfderiv_injective
#print axioms PoincareMT.M25.Topology3D.surgeryCapMap
#print axioms PoincareMT.M25.Topology3D.surgeryCapMap_apply
#print axioms PoincareMT.M25.Topology3D.surgeryCapCoordinates_mem_tube_source
#print axioms PoincareMT.M25.Topology3D.surgeryCapMap_range_subset_target
#print axioms PoincareMT.M25.Topology3D.surgeryCapMap_contMDiff
#print axioms PoincareMT.M25.Topology3D.surgeryCapMap_injective
#print axioms PoincareMT.M25.Topology3D.surgeryCapMap_mfderiv_injective
#print axioms PoincareMT.M25.Topology3D.surgeryNorthChart
#print axioms PoincareMT.M25.Topology3D.surgeryNorthChart_apply
#print axioms PoincareMT.M25.Topology3D.surgeryNorthChart_source
#print axioms PoincareMT.M25.Topology3D.surgeryNorthChart_contMDiffOn
#print axioms PoincareMT.M25.Topology3D.surgeryNorthChart_symm_contMDiffOn
#print axioms PoincareMT.M25.Topology3D.surgeryNorthChart_contains_hemisphere
#print axioms PoincareMT.M25.Topology3D.surgeryNorthChart_image_hemisphere
#print axioms PoincareMT.M25.Topology3D.surgeryNorthChart_mfderiv_injective
#print axioms PoincareMT.M25.Topology3D.northSphereCoordinate_height
#print axioms PoincareMT.M25.Topology3D.surgeryMatchingRadius_north
#print axioms PoincareMT.M25.Topology3D.surgeryNorthChart_collar_formula
#print axioms PoincareMT.M25.Topology3D.exists_uniform_zero_level_band
#print axioms PoincareMT.M25.Topology3D.exists_uniform_upper_level_band
#print axioms PoincareMT.M25.Topology3D.exists_circle_radial_band
#print axioms PoincareMT.M25.Topology3D.levelPaste
#print axioms PoincareMT.M25.Topology3D.levelPaste_of_nonneg
#print axioms PoincareMT.M25.Topology3D.levelPaste_of_neg
#print axioms PoincareMT.M25.Topology3D.levelPaste_eqOn_upper
#print axioms PoincareMT.M25.Topology3D.levelPaste_eqOn_lower
#print axioms PoincareMT.M25.Topology3D.levelPaste_contMDiff
#print axioms PoincareMT.M25.Topology3D.levelPaste_mfderiv_injective
#print axioms PoincareMT.M25.Topology3D.levelPaste_range
#print axioms PoincareMT.M25.Topology3D.levelPaste_injective
#print axioms PoincareMT.M25.Topology3D.sourceDisc_collar_mem_retained_iff
#print axioms PoincareMT.M25.Topology3D.surgeryCapMap_mem_retained_iff
#print axioms PoincareMT.M25.Topology3D.surgeryNorthChart_equator_formula
#print axioms PoincareMT.M25.Topology3D.surgeryReplacementMap
#print axioms PoincareMT.M25.Topology3D.surgeryReplacementMap_injective
#print axioms PoincareMT.M25.Topology3D.SurgeryCapProfile
#print axioms PoincareMT.M25.Topology3D.exists_surgery_cap_profile
#print axioms PoincareMT.M25.Topology3D.SurgeryCapProfile.model
#print axioms PoincareMT.M25.Topology3D.SurgeryCapProfile.model_eq
#print axioms PoincareMT.M25.Topology3D.SurgeryCapProfile.model_contMDiff
#print axioms PoincareMT.M25.Topology3D.SurgeryCapProfile.model_fst_norm_le
#print axioms PoincareMT.M25.Topology3D.SurgeryCapProfile.capMap
#print axioms PoincareMT.M25.Topology3D.SurgeryCapProfile.capMap_apply
#print axioms PoincareMT.M25.Topology3D.SurgeryCapProfile.capMap_contMDiff
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.sourceCap
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.sourceSeam
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.cap
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.seam
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.south_mem_source
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.cap_eq_image
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.seam_eq_image
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.sourceCap_isCompact
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.sourceSeam_isCompact
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.cap_isCompact
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.seam_isCompact
#print axioms PoincareMT.M25.Topology3D.exists_regular_surgery_data_of_tube
#print axioms PoincareMT.M25.Topology3D.northSphereCoordinate_circleDirection
#print axioms PoincareMT.M25.Topology3D.exists_surgery_replacement_overlap
#print axioms PoincareMT.M25.Topology3D.surgeryNorthMap_mfderiv_injective
#print axioms PoincareMT.M25.Topology3D.surgeryReplacementMap_smooth_closedEmbedding
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesFamilyData.graph
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesFamilyData.graph_contDiffOn
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesFamilyData.graph_invertible_derivative
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesFamilyData.exists_graphChart_near_compact
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesFamilyData.nonempty_graphChart
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.chart_apply
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.height_mem_interval
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.mem_source
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.inverse_fst
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.fiber_contDiffOn
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.fiberInverse_contDiffOn
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.fiberChart
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.fiberChart_apply
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.fiberChart_symm_apply
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.fiberChart_source
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.fiberChart_target
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.fiberBallNeighborhood
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.fiberChart_boundary
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.fiberBallNeighborhood_boundary
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.fiber_inside_eq
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.fiber_closedRegion_eq
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.ambientChart
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.ambientChart_apply
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.ambientChart_source
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.closedDiscStack_subset_source
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.ambientChart_contDiffOn
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.ambientChart_symm_contDiffOn
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.ambientChart_height
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.ambientChart_inverse_height
#print axioms PoincareMT.M25.Topology3D.PlanarFamilyGraphChart.ambientChart_boundary
#print axioms PoincareMT.M25.Topology3D.exists_ball_transport_of_common_cap_germ
#print axioms PoincareMT.M25.Topology3D.cofactorNormalMatrix
#print axioms PoincareMT.M25.Topology3D.cofactorNormal
#print axioms PoincareMT.M25.Topology3D.cofactorNormal_smul
#print axioms PoincareMT.M25.Topology3D.contDiff_cofactorNormal
#print axioms PoincareMT.M25.Topology3D.cofactorNormal_nonzero_orthogonal
#print axioms PoincareMT.M25.Topology3D.immersedSphereRadialExtension
#print axioms PoincareMT.M25.Topology3D.immersedSphereRadialExtension_contDiffOn
#print axioms PoincareMT.M25.Topology3D.immersedSphereRadialExtension_smul
#print axioms PoincareMT.M25.Topology3D.immersedSphereRadialExtension_coe
#print axioms PoincareMT.M25.Topology3D.immersedSphereRadialExtension_fderiv_radial
#print axioms PoincareMT.M25.Topology3D.immersedSphereRadialExtension_fderiv_comp
#print axioms PoincareMT.M25.Topology3D.immersedSphereRadialExtension_fderiv_injOn
#print axioms PoincareMT.M25.Topology3D.immersedSphereRadialExtension_fderiv_contMDiff
#print axioms PoincareMT.M25.Topology3D.immersedSphereRawNormal
#print axioms PoincareMT.M25.Topology3D.immersedSphereRawNormal_contMDiff
#print axioms PoincareMT.M25.Topology3D.immersedSphereRawNormal_nonzero_orthogonal
#print axioms PoincareMT.M25.Topology3D.exists_immersed_sphere_unit_normal
#print axioms PoincareMT.M25.Topology3D.referenceCapScale
#print axioms PoincareMT.M25.Topology3D.referenceCapScale_pos
#print axioms PoincareMT.M25.Topology3D.referenceCapScale_sq
#print axioms PoincareMT.M25.Topology3D.exists_reference_cap_profile
#print axioms PoincareMT.M25.Topology3D.reference_profile_horizontal_norm_le
#print axioms PoincareMT.M25.Topology3D.exists_surgery_pair_parameters
#print axioms PoincareMT.M25.Topology3D.SurgeryCapProfile.replacementMap
#print axioms PoincareMT.M25.Topology3D.SurgeryCapProfile.replacementMap_range
#print axioms PoincareMT.M25.Topology3D.SurgeryCapProfile.capMap_old_surface_source
#print axioms PoincareMT.M25.Topology3D.SurgeryCapProfile.replacementMap_disjoint_pair
#print axioms PoincareMT.M25.Topology3D.exists_smooth_surgery_pair
#print axioms PoincareMT.M25.Topology3D.stackProfileBlend
#print axioms PoincareMT.M25.Topology3D.stackProfileBlend_contDiff
#print axioms PoincareMT.M25.Topology3D.stackProfileBlend_pos
#print axioms PoincareMT.M25.Topology3D.stackProfileBlend_le
#print axioms PoincareMT.M25.Topology3D.stackProfileBlend_of_nonpos
#print axioms PoincareMT.M25.Topology3D.stackProfileBlend_of_one_le
#print axioms PoincareMT.M25.Topology3D.stackProfileBlend_eq_of_eq
#print axioms PoincareMT.M25.Topology3D.stackCapProfilePath
#print axioms PoincareMT.M25.Topology3D.stackCapProfilePathDiffeomorph
#print axioms PoincareMT.M25.Topology3D.stackCapProfilePathDiffeomorph_apply
#print axioms PoincareMT.M25.Topology3D.stackCapProfilePathDiffeomorph_symm_apply
#print axioms PoincareMT.M25.Topology3D.stackCapProfilePathDiffeomorph_time
#print axioms PoincareMT.M25.Topology3D.stackCapProfilePath_eq_flatCapDiffeomorph
#print axioms PoincareMT.M25.Topology3D.stackCapProfilePath_native_contMDiff
#print axioms PoincareMT.M25.Topology3D.stackCapProfilePath_fst_norm_le
#print axioms PoincareMT.M25.Topology3D.stackCapProfilePath_snd_nonpos
#print axioms PoincareMT.M25.Topology3D.stackCapProfilePath_snd_neg_iff
#print axioms PoincareMT.M25.Topology3D.exists_stackCapProfilePath_height_bound
#print axioms PoincareMT.M25.Topology3D.exists_stackCapProfilePath_common_ambient_germ
#print axioms PoincareMT.M25.Topology3D.exists_reference_vertical_diffeomorph
#print axioms PoincareMT.M25.Topology3D.exists_manifold_source_regular_neighborhood
#print axioms PoincareMT.M25.Topology3D.exists_compact_product_regular_tube
#print axioms PoincareMT.M25.Topology3D.mfderiv_sphere_product_time
#print axioms PoincareMT.M25.Topology3D.sphere_product_mfderiv_bijective_of_normal
#print axioms PoincareMT.M25.Topology3D.exists_transverse_sphere_collar
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.flatChart_mem_sourceCap
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.exists_source_band_mem
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.pullback
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.pullback_cap
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.pullback_seam
#print axioms PoincareMT.M25.Topology3D.southSpherePoint
#print axioms PoincareMT.M25.Topology3D.southSpherePoint_coordinates
#print axioms PoincareMT.M25.Topology3D.southSpherePoint_contMDiffOn
#print axioms PoincareMT.M25.Topology3D.southSpherePoint_coordinate
#print axioms PoincareMT.M25.Topology3D.southSphereChart
#print axioms PoincareMT.M25.Topology3D.southSphereChart_contMDiff
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.of_cap_patch
#print axioms PoincareMT.M25.Topology3D.contMDiffOn_sphere_supported_smul
#print axioms PoincareMT.M25.Topology3D.exists_two_sphere_cutoffs
#print axioms PoincareMT.M25.Topology3D.contMDiffOn_sphere_time_velocity
#print axioms PoincareMT.M25.Topology3D.exists_sphere_candidate_time_sign
#print axioms PoincareMT.M25.Topology3D.weightedSphereTimeMap
#print axioms PoincareMT.M25.Topology3D.weightedSphereTimeMap_properties
#print axioms PoincareMT.M25.Topology3D.exists_weighted_sphere_collar
#print axioms PoincareMT.M25.Topology3D.sphere_horizontal_mvfderiv_bijective
#print axioms PoincareMT.M25.Topology3D.north_collar_candidate_regular
#print axioms PoincareMT.M25.Topology3D.flat_tube_candidate_regular
#print axioms PoincareMT.M25.Topology3D.surgery_collar_patch_geometry
#print axioms PoincareMT.M25.Topology3D.exists_surgery_north_collar_band
#print axioms PoincareMT.M25.Topology3D.exists_surgery_replacement_weighted_collar
#print axioms PoincareMT.M25.Topology3D.exists_retained_collar_chart
#print axioms PoincareMT.M25.Topology3D.exists_surgery_replacement_tagged_collar
#print axioms PoincareMT.M25.Topology3D.exists_regular_disc_surgery
#print axioms PoincareMT.M25.Topology3D.exists_compact_timeField_extension_away
#print axioms PoincareMT.M25.Topology3D.exists_ambient_evolution_of_localField_away
#print axioms PoincareMT.M25.Topology3D.stackPlacedProfileChart
#print axioms PoincareMT.M25.Topology3D.stackPlacedProfileChart_apply
#print axioms PoincareMT.M25.Topology3D.stackPlacedProfileChart_source
#print axioms PoincareMT.M25.Topology3D.stackPlacedProfileChart_target
#print axioms PoincareMT.M25.Topology3D.stackPlacedProfileChart_symm_apply
#print axioms PoincareMT.M25.Topology3D.stackPlacedProfileChart_contDiffOn
#print axioms PoincareMT.M25.Topology3D.stackPlacedProfileChart_time
#print axioms PoincareMT.M25.Topology3D.stackPlacedProfileCap
#print axioms PoincareMT.M25.Topology3D.stackPlacedProfileCoordinates_mem_source
#print axioms PoincareMT.M25.Topology3D.stackPlacedProfileCap_contMDiff
#print axioms PoincareMT.M25.Topology3D.stackPlacedProfileCap_hasDerivAt
#print axioms PoincareMT.M25.Topology3D.stackPlacedProfileCap_endpoints
#print axioms PoincareMT.M25.Topology3D.stackPlacedProfileCap_isCompact_track
#print axioms PoincareMT.M25.Topology3D.exists_stackPlacedProfileChart_common_germ
#print axioms PoincareMT.M25.Topology3D.stackPlacedProfileCap_signed_height
#print axioms PoincareMT.M25.Topology3D.exists_stackPlacedProfileEvolution
#print axioms PoincareMT.M25.Topology3D.exists_stackPlacedProfileEvolution_in_height_strip
#print axioms PoincareMT.M25.Topology3D.referenceCapHeight
#print axioms PoincareMT.M25.Topology3D.referenceCapPoint
#print axioms PoincareMT.M25.Topology3D.referenceCapHeight_contDiff
#print axioms PoincareMT.M25.Topology3D.referenceCapPoint_contDiff
#print axioms PoincareMT.M25.Topology3D.referenceCapPoint_mem_sphere
#print axioms PoincareMT.M25.Topology3D.referenceCapPoint_cap_iff
#print axioms PoincareMT.M25.Topology3D.referenceCapPoint_rim_iff
#print axioms PoincareMT.M25.Topology3D.referenceCapPoint_image_closedBall
#print axioms PoincareMT.M25.Topology3D.referenceFlatteningDiffeomorph
#print axioms PoincareMT.M25.Topology3D.referenceFlatteningDiffeomorph_apply
#print axioms PoincareMT.M25.Topology3D.referenceFlatteningDiffeomorph_symm_apply
#print axioms PoincareMT.M25.Topology3D.referenceFlattening_snd_mem_Icc
#print axioms PoincareMT.M25.Topology3D.referenceFlattening_snd_neg
#print axioms PoincareMT.M25.Topology3D.referenceFlattening_capPoint
#print axioms PoincareMT.M25.Topology3D.referenceCompressedDiffeomorph
#print axioms PoincareMT.M25.Topology3D.referenceCompressedDiffeomorph_apply
#print axioms PoincareMT.M25.Topology3D.referenceCompressedDiffeomorph_symm_apply
#print axioms PoincareMT.M25.Topology3D.exists_reference_chart_cylinder
#print axioms PoincareMT.M25.Topology3D.referenceCompressedDiffeomorph_model_bounds
#print axioms PoincareMT.M25.Topology3D.referenceCompressedDiffeomorph_cap_germ
#print axioms PoincareMT.M25.Topology3D.exists_reference_ball_chart
#print axioms PoincareMT.M25.Topology3D.reference_ball_regions_of_side
#print axioms PoincareMT.M25.Topology3D.stackCanonicalFactor
#print axioms PoincareMT.M25.Topology3D.stackCanonicalFactor_spec
#print axioms PoincareMT.M25.Topology3D.stackCanonicalHorizontal
#print axioms PoincareMT.M25.Topology3D.stackCanonicalVertical
#print axioms PoincareMT.M25.Topology3D.stackCanonicalMeridian
#print axioms PoincareMT.M25.Topology3D.stackCanonicalHorizontal_spec
#print axioms PoincareMT.M25.Topology3D.stackCanonicalVertical_spec
#print axioms PoincareMT.M25.Topology3D.stackCanonicalMeridian_formula
#print axioms PoincareMT.M25.Topology3D.stackCanonicalMeridian_regular
#print axioms PoincareMT.M25.Topology3D.stackCanonicalModel_southern_geometry
#print axioms PoincareMT.M25.Topology3D.stackCanonicalModel_flat_disc
#print axioms PoincareMT.M25.Topology3D.stackCanonicalModel_reflection_height
#print axioms PoincareMT.M25.Topology3D.exists_stackCanonicalRadii
#print axioms PoincareMT.M25.Topology3D.exists_stackCanonicalProfile_common_germ
#print axioms PoincareMT.M25.Topology3D.exists_stackCanonicalProfile_small_scale
#print axioms PoincareMT.M25.Topology3D.exists_stackCanonicalProfileEvolution
#print axioms PoincareMT.M25.Topology3D.compact_connected_diff_of_connected_seam
#print axioms PoincareMT.M25.Topology3D.compact_connected_diff_finite_caps
#print axioms PoincareMT.M25.Topology3D.compact_connected_retained_of_cap_cover
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.sourceCapInterior
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.sourceCapInterior_isOpen
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.sourceCapInterior_subset
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.sourceCap_diff_interior
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.sourceCap_isConnected
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.sourceSeam_isConnected
#print axioms PoincareMT.M25.Topology3D.tagged_source_complement_compact_connected
#print axioms PoincareMT.M25.Topology3D.tagged_retained_core_compact_connected
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.cap_abs_height_bounds
#print axioms
  PoincareMT.M25.Topology3D.SurgeryCapTag.exists_unique_retained_disc_of_height_avoidance
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.cap_disjoint_of_height_avoidance
#print axioms PoincareMT.M25.Topology3D.surgery_parent_region_identities
#print axioms PoincareMT.M25.Topology3D.surgery_cap_equator_image
#print axioms PoincareMT.M25.Topology3D.surgery_retained_cap_intersection
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent
#print axioms PoincareMT.M25.Topology3D.exists_regular_surgery_event
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.parameter_bounds
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.region_identities
#print axioms PoincareMT.M25.Topology3D.referenceCapSphereChart
#print axioms PoincareMT.M25.Topology3D.referenceCapSphereChart_spec
#print axioms PoincareMT.M25.Topology3D.nativeCapSourceChart
#print axioms PoincareMT.M25.Topology3D.nativeCapSourceChart_spec
#print axioms PoincareMT.M25.Topology3D.nativeCapAmbientDiffeomorph
#print axioms PoincareMT.M25.Topology3D.nativeCapAmbientDiffeomorph_spec
#print axioms PoincareMT.M25.Topology3D.nativeCapRadialChart
#print axioms PoincareMT.M25.Topology3D.nativeCapRadialChart_spec
#print axioms PoincareMT.M25.Topology3D.exists_cap_chart_side_buffer
#print axioms PoincareMT.M25.Topology3D.exists_native_cap_chart
#print axioms PoincareMT.M25.Topology3D.referenceFlattening_height_factor
#print axioms PoincareMT.M25.Topology3D.referenceCapTransition
#print axioms PoincareMT.M25.Topology3D.referenceCapTransition_spec
#print axioms PoincareMT.M25.Topology3D.referenceCapTransition_oriented_patch
#print axioms PoincareMT.M25.Topology3D.exists_sphere_fixed_patch_extension
#print axioms PoincareMT.M25.Topology3D.exists_reference_cap_corrected_chart
#print axioms PoincareMT.M25.Topology3D.exists_child_cap_source_disc
#print axioms PoincareMT.M25.Topology3D.exists_sphere_disc_plane_chart
#print axioms PoincareMT.M25.Topology3D.exists_sphere_disc_vertical_cap
#print axioms PoincareMT.M25.Topology3D.exists_normalized_child_cap_ball
#print axioms PoincareMT.M25.Topology3D.stackCapScale
#print axioms PoincareMT.M25.Topology3D.stackCapScale_spec
#print axioms PoincareMT.M25.Topology3D.stackCapScalePlacementDiffeomorph
#print axioms PoincareMT.M25.Topology3D.stackCapScalePlacementDiffeomorph_spec
#print axioms PoincareMT.M25.Topology3D.stackCapScaleChart
#print axioms PoincareMT.M25.Topology3D.stackCapScaleChart_spec
#print axioms PoincareMT.M25.Topology3D.stackCapScaleCap
#print axioms PoincareMT.M25.Topology3D.stackCapScaleCap_spec
#print axioms PoincareMT.M25.Topology3D.stackCapScaleChart_field_tube
#print axioms PoincareMT.M25.Topology3D.exists_stackCapCoreNeighborhood
#print axioms PoincareMT.M25.Topology3D.exists_stackCapScaleCutoff
#print axioms PoincareMT.M25.Topology3D.clockEvolution_image_Icc_of_zero_endpoints
#print axioms PoincareMT.M25.Topology3D.stackCapScaleCylinderField
#print axioms PoincareMT.M25.Topology3D.stackCapScaleCylinderField_spec
#print axioms PoincareMT.M25.Topology3D.stackCapScaleCylinder_clock_tracks
#print axioms PoincareMT.M25.Topology3D.stackCapScaleField_preserves_core
#print axioms PoincareMT.M25.Topology3D.exists_stackCapScale_tracking_widths
#print axioms PoincareMT.M25.Topology3D.exists_stackCapScaleEvolution
#print axioms PoincareMT.M25.Topology3D.exists_stackCapScaleTransport
#print axioms PoincareMT.M25.Topology3D.exists_stackCapTag_transport_of_fixed_neighborhood
#print axioms PoincareMT.M25.Topology3D.exists_protected_chart_evolution
#print axioms PoincareMT.M25.Topology3D.reunionReflectedHorizontal
#print axioms PoincareMT.M25.Topology3D.reunionReflectedHorizontal_spec
#print axioms PoincareMT.M25.Topology3D.reunion_reflected_model_spec
#print axioms PoincareMT.M25.Topology3D.exists_reunion_reflection_diffeomorph
#print axioms PoincareMT.M25.Topology3D.reunionAxialCutoff
#print axioms PoincareMT.M25.Topology3D.reunionAxialCutoff_spec
#print axioms PoincareMT.M25.Topology3D.reunionAxialHeight
#print axioms PoincareMT.M25.Topology3D.reunionAxialHeight_spec
#print axioms PoincareMT.M25.Topology3D.exists_reunion_axial_spacetime_diffeomorph
#print axioms PoincareMT.M25.Topology3D.exists_reunion_axial_chart
#print axioms PoincareMT.M25.Topology3D.reunion_axial_endpoint_image
#print axioms PoincareMT.M25.Topology3D.exists_reunion_axial_diffeomorph
#print axioms PoincareMT.M25.Topology3D.exists_reunion_diffeomorph
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.exists_inherited_cap
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.inherited_cap_disjoint_new
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.exists_inherited_cap_family
#print axioms PoincareMT.M25.Topology3D.exists_compact_height_gap
#print axioms PoincareMT.M25.Topology3D.exists_family_tube_owner
#print axioms PoincareMT.M25.Topology3D.exists_innermost_family_tube
#print axioms PoincareMT.M25.Topology3D.exists_family_surgery_event
#print axioms PoincareMT.M25.Topology3D.exists_family_surgery_event_avoiding
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.children_middle_band
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.children_middle_level
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.children_outside_band
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.family_horizontal_levels_delete
#print axioms PoincareMT.M25.Topology3D.exists_regular_separating_height_cuts
#print axioms PoincareMT.M25.Topology3D.exists_separated_regular_height_buffers
#print axioms PoincareMT.M25.Topology3D.critical_source_subsingleton_of_cut_avoidance
#print axioms PoincareMT.M25.Topology3D.exists_regular_collar_level_family
#print axioms PoincareMT.M25.Topology3D.exists_regular_collar_band_family
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.retained_central_eq
#print axioms
  PoincareMT.M25.Topology3D.RegularSurgeryEvent.exists_unique_retained_disc_of_height_avoidance
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.retained_height_critical_iff
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.retained_morse_chart
#print axioms PoincareMT.M25.Topology3D.stackCapCanonicalEndpoint
#print axioms PoincareMT.M25.Topology3D.exists_stackCapCanonicalNormalization
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.reunionTube
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.reunionTube_spec
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.reunion_core_isCompact
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.reunion_core_disjoint_strip
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.reunionTube_capMap
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.reunion_region_identities
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.exists_event_reunion_diffeomorph
#print axioms PoincareMT.M25.Topology3D.exists_family_surgery_reindex
#print axioms PoincareMT.M25.Topology3D.exists_finite_family_surgery_step
#print axioms PoincareMT.M25.Topology3D.exists_reindexed_surgery_cap_family
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.cap_avoids_separated_cuts
#print axioms PoincareMT.M25.Topology3D.stackAnnularInterpolation
#print axioms PoincareMT.M25.Topology3D.stackAnnularInterpolation_invertible_derivative
#print axioms PoincareMT.M25.Topology3D.exists_stackAnnularInterpolationChart
#print axioms PoincareMT.M25.Topology3D.exists_stackAnnularCutoff
#print axioms PoincareMT.M25.Topology3D.stackPassiveHeightFiber
#print axioms PoincareMT.M25.Topology3D.exists_stackAnnularEvolution
#print axioms PoincareMT.M25.Topology3D.SurgeryCapProfile.closedBall_model_bounds
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.canonicalCapBall
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.canonicalCapBall_spec
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.closedRegion_trichotomy
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.exists_movable_child_axis_outside
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.exists_canonical_child_containment
#print axioms PoincareMT.M25.Topology3D.FamilySurgeryHistory
#print axioms PoincareMT.M25.Topology3D.FamilySurgeryHistory.length
#print axioms PoincareMT.M25.Topology3D.FamilySurgeryHistory.card_eq_length
#print axioms PoincareMT.M25.Topology3D.FamilySurgeryHistory.fold
#print axioms PoincareMT.M25.Topology3D.family_levels_preserved_at_separated_cut
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.cap_outside_other_cut_buffer
#print axioms PoincareMT.M25.Topology3D.exists_boundary_linear_realization
#print axioms PoincareMT.M25.Topology3D.exists_sphere_disc_pointwise_extension
#print axioms PoincareMT.M25.Topology3D.fderiv_normal_pos_of_local_interior
#print axioms PoincareMT.M25.Topology3D.exists_ball_chart_common_germ_of_sphere_patch
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.exists_canonical_cap_parameter_alignment
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.exists_common_cap_ball_charts
#print axioms PoincareMT.M25.Topology3D.stackCapEndChart
#print axioms PoincareMT.M25.Topology3D.stackCapEndChart_spec
#print axioms PoincareMT.M25.Topology3D.stackCapEndFiber
#print axioms PoincareMT.M25.Topology3D.stackCapEndFiber_spec
#print axioms PoincareMT.M25.Topology3D.exists_stackCapEndLabels
#print axioms PoincareMT.M25.Topology3D.exists_stackClippedCircleLabels
#print axioms PoincareMT.M25.Topology3D.exists_stackCapEndFamily
#print axioms PoincareMT.M25.Topology3D.stackCanonicalEndpoint_capEndChart
#print axioms PoincareMT.M25.Topology3D.SurgeryCapTag.cap_seam_signed_height
#print axioms PoincareMT.M25.Topology3D.exists_stackCircleFamily_of_connected_regular_band
#print axioms PoincareMT.M25.Topology3D.exists_stackCircleFamily_of_two_caps
#print axioms PoincareMT.M25.Topology3D.exists_stackMorseProduct
#print axioms PoincareMT.M25.Topology3D.exists_stackMorseEndTube
#print axioms PoincareMT.M25.Topology3D.exists_stackTubeEndLabels
#print axioms PoincareMT.M25.Topology3D.exists_stackAnnularMatchedChart
#print axioms PoincareMT.M25.Topology3D.stackCanonicalCap_image_eq_of_annular_match
#print axioms PoincareMT.M25.Topology3D.exists_stackCapNormalization_in_matched_chart
#print axioms PoincareMT.M25.Topology3D.exists_stackCanonicalBallModel
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.exists_reunion_core_tube_buffer
#print axioms
  PoincareMT.M25.Topology3D.RegularSurgeryEvent.closedAnnulus_inter_closedRegion_subset_cap
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.mid_outside_of_movable_child
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.exists_compression_support_domain
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.exists_supported_child_compression
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.exists_parent_ball_of_children
#print axioms PoincareMT.M25.Topology3D.FamilySurgeryHistory.exists_initial_balls
#print axioms PoincareMT.M25.Topology3D.FamilyCutState
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.measure
#print axioms PoincareMT.M25.Topology3D.exists_initial_family_cut_state
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.exists_surgery_step
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.exists_terminal_history
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.height_gap_of_count_eq_zero
#print axioms PoincareMT.M25.Topology3D.exists_initial_collar_cut_state
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.component_cut_side
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.cap_points_on_birth_side
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.sourceCore
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.sourceCore_mem_and_seams
#print axioms PoincareMT.M25.Topology3D.FamilySourceAtlas
#print axioms PoincareMT.M25.Topology3D.RegularSurgeryEvent.newCap_native_source
#print axioms PoincareMT.M25.Topology3D.FamilySourceAtlas.exists_initial
#print axioms PoincareMT.M25.Topology3D.FamilySourceAtlas.exists_surgery_step
#print axioms PoincareMT.M25.Topology3D.exists_stackTwoCapMatchedChart
#print axioms PoincareMT.M25.Topology3D.exists_stackTwoCapCanonicalNormalization
#print axioms PoincareMT.M25.Topology3D.exists_ball_of_classified_two_caps
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.retainedCore
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.sourceCore_compact_connected
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.retainedCore_geometry
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.core_of_no_owned_caps
#print axioms PoincareMT.M25.Topology3D.FamilySourceAtlas.exists_terminal_history
#print axioms PoincareMT.M25.Topology3D.FamilySourceAtlas.height_critical_iff
#print axioms PoincareMT.M25.Topology3D.FamilySourceAtlas.morse_chart
#print axioms PoincareMT.M25.Topology3D.FamilySourceAtlas.sourceCore_critical_subsingleton
#print axioms PoincareMT.M25.Topology3D.exists_terminal_collar_morse_family
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.sourceCore_mem_nhds_of_not_seam
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.sourceCore_extremum_on_seam
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.exists_sourceCore_height_ends
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.exists_common_seam_height
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.exists_seam_source_half_neighborhood
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.exists_regular_core_flow_data
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.retainedCore_of_affine_height_path
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.regular_core_flow_segment
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.regular_core_middle_retraction
#print axioms PoincareMT.M25.Topology3D.FamilySourceAtlas.critical_protected_neighborhood
#print axioms PoincareMT.M25.Topology3D.nativeDiscChart_geometry
#print axioms PoincareMT.M25.Topology3D.FamilySourceAtlas.exists_extremum_core_disc
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.seam_height_gaps_of_buffer_avoidance
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.morse_disc_complement_geometry
#print axioms PoincareMT.M25.Topology3D.exists_regular_compact_surface_flow
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.regular_core_seam_middle_image
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.regular_core_cap_eq_of_sign_eq
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.exists_regular_core_two_ends
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.exists_ball_of_regular_core
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.morse_disc_middle_geometry
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.morse_rest_flow_segment
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.morse_rest_middle_retraction
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.exists_morse_rest_old_seam_neighborhood
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.exists_morse_rest_new_seam_neighborhood
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.morse_rest_seam_middle_images
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.morse_rest_height_barriers
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.morse_rest_cap_sign_and_unique
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.exists_morse_core_one_end
#print axioms PoincareMT.M25.Topology3D.stackMorseMeridian_geometry
#print axioms PoincareMT.M25.Topology3D.stackMorseMeridian_pole_and_seam
#print axioms PoincareMT.M25.Topology3D.exists_stackMorseGraphDisplacement
#print axioms PoincareMT.M25.Topology3D.exists_stackMorseGraphShear
#print axioms PoincareMT.M25.Topology3D.stackMorseProjection_geometry
#print axioms PoincareMT.M25.Topology3D.stackMorseProjection_regular
#print axioms PoincareMT.M25.Topology3D.exists_stackMorseCap_graph
#print axioms PoincareMT.M25.Topology3D.exists_stackMorseGraphNormalization
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.exists_morse_rest_regular_band
#print axioms PoincareMT.M25.Topology3D.FamilyCutState.exists_morse_rest_circle_family

-- Numeric private-name components are resolved from the compiled environment.
run_cmd do
  let wanted : List String := [
    "PoincareMT.M25.Topology3D.cofactorNormalMatrix_mulVec",
    "PoincareMT.M25.Topology3D.normalCross",
    "PoincareMT.M25.Topology3D.normalCross_inner_left",
    "PoincareMT.M25.Topology3D.normalCross_inner_right",
    "PoincareMT.M25.Topology3D.normalCross_ne_zero",
    "PoincareMT.M25.Topology3D.normalCross_map",
    "PoincareMT.M25.Topology3D.inner_map_eq_zero_of_plane_basis",
    "PoincareMT.M25.Topology3D.plane_basis_pair_independent",
    "PoincareMT.M25.Topology3D.immersedSphereRadialExtension_differentiableAt",
    "PoincareMT.M25.Topology3D.profile_base_radial",
    "PoincareMT.M25.Topology3D.profile_rational_radial",
    "PoincareMT.M25.Topology3D.profile_base_comparison",
    "PoincareMT.M25.Topology3D.reference_vertical_cutoff_integral_le",
    "PoincareMT.M25.Topology3D.reference_vertical_primitive_smooth",
    "PoincareMT.M25.Topology3D.reference_model_comparison",
    "PoincareMT.M25.Topology3D.reference_cap_point_eq_north"]
  let names := (← Lean.getEnv).constants.toList.filterMap fun (name, _) =>
    if wanted.contains (Lean.privateToUserName name).toString then some name else none
  unless names.length == 16 do
    throwError "Expected sixteen private helper declarations, got {names.length}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    if axioms.isEmpty then
      Lean.logInfo m!"'{name.toString}' does not depend on any axioms"
    else
      Lean.logInfo m!"'{name.toString}' depends on axioms: {axioms.toList}"
