import PoincareMT.Proofs.M25.Topology3D.Space3.Base.SaddleDiscClassification

/-!
# Complete native audit of the lower-data and saddle-classification packets

The seventeen source modules are identified by native imported module index.
Every authored, private and generated declaration is checked against the
allowed axioms. This does not assert completion of the saddle-ball leaves
or Alexander's theorem. Source: Hatcher, Lemma 1.2, pp. 2-3; the SLD/S4
capture packets and disc-classification extraction of 2026-09-23.
-/

set_option autoImplicit false

-- This audit module intentionally enumerates native declarations and prints their axioms.
set_option linter.hashCommand false

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let anchors : List (Name × Nat) := [
    (``PoincareMT.M25.Topology3D.exists_source_circle_flow_chart, 1),
    (``PoincareMT.M25.Topology3D.exists_saddle_lower_source_legs, 3),
    (``PoincareMT.M25.Topology3D.exists_saddle_lowerLevelData_of_two_circles, 1),
    (``PoincareMT.M25.Topology3D.SaddleOrientation.triple_ne_zero_of_transverse, 8),
    (``PoincareMT.M25.Topology3D.SaddleOrientation.collar_arc_orientation, 3),
    (``PoincareMT.M25.Topology3D.SaddleOrientation.collar_chart_orientation, 3),
    (``PoincareMT.M25.Topology3D.SaddleOrientation.saddle_arc_opposite_port_products, 6),
    (``PoincareMT.M25.Topology3D.SaddleOrientation.port_sign_product_neg_of_scaled, 4),
    (``PoincareMT.M25.Topology3D.exists_saddle_exterior_upper_matching, 4),
    (``PoincareMT.M25.Topology3D.exists_two_circles_of_ambient_partition, 3),
    (``PoincareMT.M25.Topology3D.saddle_source_disc_arc_geometry, 2),
    (``PoincareMT.M25.Topology3D.exists_saddle_transported_two_pieces, 11),
    (``PoincareMT.M25.Topology3D.exists_saddle_one_circle_exterior_matching, 1),
    (``PoincareMT.M25.Topology3D.exists_saddle_two_level_transport, 3),
    (``PoincareMT.M25.Topology3D.exists_saddle_two_circle_side, 2),
    (``PoincareMT.M25.Topology3D.SaddlePieceData.exists_lowerLevelData_or_reflected, 1),
    (``PoincareMT.M25.Topology3D.BallNeighborhoodChart.planar_closedRegion_trichotomy, 3)]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut seen := #[]
  let mut total := 0
  for (anchor, expected) in anchors do
    let some moduleIndex := env.getModuleIdxFor? anchor
      | throwError "Classification anchor has no imported module index: {anchor}"
    if seen.contains moduleIndex then
      throwError "Duplicate classification module anchor: {anchor}"
    seen := seen.push moduleIndex
    let names := (env.constants.toList.filterMap fun (name, _) =>
      if env.getModuleIdxFor? name == some moduleIndex then some name else none).mergeSort
        (fun a b => decide (a.toString ≤ b.toString))
    unless names.length == expected && names.contains anchor do
      throwError "Classification module count mismatch at {anchor}: {names.length}"
    logInfo m!"CLASSIFICATION_MODULE {anchor.toString} COUNT {names.length}"
    total := total + names.length
    for name in names do
      let axioms ← collectAxioms name
      unless axioms.toList.all allowed.contains do
        throwError "Unexpected classification axiom at {name}: {axioms.toList}"
      logInfo m!"CLASSIFICATION_DECLARATION {name.toString} AXIOMS {axioms.toList}"
  unless seen.size == 17 && total == 59 do
    throwError "Incomplete classification audit: modules={seen.size}, declarations={total}"
  logInfo m!"CLASSIFICATION_COMPLETE modules={seen.size} declarations={total}"
