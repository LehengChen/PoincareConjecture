import PoincareMT.Statements.M24ModelCertificates
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Certificates

/-!
# M24 model-certificate proof entry

The numbered theorem below exposes the imported M24 proof. Earlier definitions
and statements are read-only inputs; future native proof helpers belong in
`Proofs/M24/`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-
M24: For a connected smooth three-manifold, an actual gradient shrinking
soliton S, its shrinking flow G, and one of M20's three model certificates,
produce a refined certificate on that same G. Compact-round input yields a
finite free SO(4) quotient with a fixed smooth quotient map, the literal
(-4t) unit-sphere metric, and all-negative-time metric/curvature transports.
Sphere-line input is preserved exactly.

For every supplied quotient q, preserve q itself and produce its normal form:
antipodal on the sphere times either the identity on the line or reflection
about one fixed center. Produce the commuting RP2 product coordinates or the
punctured standard RP3 homeomorphism and smooth cover, respectively. Also
produce local diffeomorphism of q's actual quotient map and both sectional
transports, using one fixed flow identification for all t < 0. No orientation
or projective applicability premise is supplied by the caller.

Internal proof work includes the compact potential-extremum/metric-ODE
argument, the finite space-form quotient, the two-time isometry subtraction,
the chartwise inverse function theorem, quotient topology and curvature
naturality. The imported proof supplies all of these constructions. The checked
helper in Proofs/M24/Providers.lean applies M20 to S and refines that exact
chosen flow/model. Quantitative neighborhoods and the original ancient flow
at time zero remain the separate M26/M27 obligations.

Sources: Morgan--Tian Theorem 1.11 and its space-form consequence, pp. 8--9;
Definition 9.41, Theorem 9.42 and (9.19), pp. 206--208; Section 9.4.5, p. 216;
the three-model list in the proof of Proposition 9.58, pp. 220--221;
Theorem 9.93(1),(5)--(7), p. 242. The project contract correction is
MT-M24-PROJECTIVE-PRODUCER in reviews/errata/2026-09-15-m24-projective-producer.md.
The M20 quotient-orientation, literal-product and upstream soliton-staging
corrections remain in force. Full derivation and source review:
reviews/contracts/2026-09-15-m24-complete-contract.md and
reviews/contracts/2026-09-15-m24-complete-round1.md. The authors' Section 19.2
correction has no local application.
-/
theorem m24ModelCertificates
    {S : GradientShrinkingSolitonData 3 M}
    {G : ShrinkingSolitonFlow S}
    (input : M24ModelInput G) :
    RepairedModelCertificateTheory input := by
  exact horizon_m24ModelCertificates input

/-! Downstream imports use the named theory wrapper without introducing a
second admission. -/
theorem m24ModelCertificateTheory
    {S : GradientShrinkingSolitonData 3 M}
    {G : ShrinkingSolitonFlow S}
    (input : M24ModelInput G) :
    RepairedModelCertificateTheory input :=
  m24ModelCertificates input

end PoincareMT
