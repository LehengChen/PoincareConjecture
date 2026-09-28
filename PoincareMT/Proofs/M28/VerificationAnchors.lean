import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceMinimizerAnchors
import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceSuccessorOrientation
import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceOrientedTransfer
import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceEdgeCommonOrientation
import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceMinimizerEdgePacket
import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceActualLaterCuts

/-! Kernel audits for whole-path anchors and the actual transition sign. -/

set_option autoImplicit false
-- Printing kernel dependencies is the purpose of this audit module.
set_option linter.hashCommand false

#print axioms PoincareMT.M28.pathELength_eq_integral_fixed_segment_speed
#print axioms PoincareMT.M28.continuousOn_pathELength_left
#print axioms PoincareMT.M28.continuousOn_pathELength_right
#print axioms PoincareMT.M28.exists_pathELength_left_anchor
#print axioms PoincareMT.M28.exists_pathELength_right_anchor
#print axioms PoincareMT.M28.exists_source_minimizer_anchors_accuracy
#print axioms PoincareMT.M28.pathELength_eq_intrinsicEDist_subsegment
#print axioms PoincareMT.M28.successor_exit_sign_eq_one_of_minimizer
#print axioms PoincareMT.M28.exists_uniform_oriented_forward_reciprocal_sign
#print axioms PoincareMT.M28.exists_source_edge_common_orientation_packet
#print axioms PoincareMT.M28.exists_source_minimizer_edge_packet_accuracy
#print axioms PoincareMT.M28.backward_anchor_height_le_of_positive_transition
#print axioms PoincareMT.M28.exists_later_negative_cut_accuracy
#print axioms PoincareMT.M28.two_source_edges_pathELength_lower
#print axioms PoincareMT.M28.SourceEdgePacket.later_negative_cut
#print axioms PoincareMT.M28.exists_actual_later_negative_cut_accuracy
