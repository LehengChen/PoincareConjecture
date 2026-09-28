import PoincareMT.Proofs.M05.Geometry.Riemannian.Curvature.SecondBianchi

/-!
# Shared differential second Bianchi identity

M07 reuses the existing local connection and curvature implementation from
M05. The copied declaration block was identical after aligning the name
`mvfderiv_inner_on_fields`; keeping one implementation avoids duplicate data
definitions when both milestone proofs are imported.

The original adaptation is from Chow-Liao-Qin, revision
`1b535dd102b94cc42b107cca27059687888f08b3`,
`DifferentialGeometry/Geometry/Curvature/CurvatureOperator/SecondBianchi.lean`,
`second_bianchi_levi_civita`. Its provenance and semantic review remain governed
by the M05 declaration records; this forwarding module grants no new approval.
-/
