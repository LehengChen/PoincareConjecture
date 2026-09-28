import PoincareMT.Statements.M13Rescaling
import PoincareMT.Proofs.M12
import PoincareMT.Proofs.M13.Rescaling
import PoincareMT.Proofs.M13.OrdinaryFlow
import PoincareMT.Proofs.M13.OrdinaryProduct

/-!
# M13 parabolic rescaling proof

One admitted theorem owns the complete construction and transport calculus.
Its checked supplier consumes the actual M12 theorem, including its earlier
metric and spacetime prerequisites. No admitted definition constructs data.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- M13: given M12's intrinsic Ricci and ordinary-gauge theory in dimension n,
for every realized spacetime, positive Q and real a, construct its parabolic
rescaling on the same smooth carrier with time Q*(t-a), metric Q*G and time
vector chi/Q. The actual raw atlas retains its spatial overlaps. The literal
horizontal kernels and actual slices are identified, with metric, curvature,
calibrated-volume and regular-connection transport. The intrinsic Ricci
equations are equivalent for all compatible slice-connection choices, whose
existence is supplied. Norms and lengths gain sqrt(Q), volume gains Q^(n/2),
and the full curvature norm and its square gain Q^(-1) and Q^(-2), respectively.
Supplied compatible domains reparameterize in both directions, preserving
base maps, restrictions, gluing, conditional maximality and actual ball
neighborhoods. Quantitative curvature and volume bounds have the corresponding
scaled radii. Backward differential and horizontal-energy formulas hold on
their actual domains, including within derivatives with unique derivative at
included endpoints. An ordinary Ricci flow rescales to Q*g(a+s/Q) on the exact
affine image interval, even for an empty carrier; fixed nonempty product
witnesses are compared by the actual map (s,x) -> (a+s/Q,x). All dimensions,
including zero, retain the explicit Q>0 hypothesis. No limit is extracted.

Sources: Morgan-Tian Definition 3.40, p. 61; Definitions 3.38/3.41, pp. 61-62;
Theorem 1.2 and Definitions 1.4-1.8, pp. 3-7; Lemma 6.72 and Corollary 6.74,
pp. 141-142, for differential and metric scale conventions; Definition 9.1,
p. 180, and Section 9.2.1, p. 185, for scale bounds. These combined transport
consequences are derived in `reviews/contracts/M13-repair-contract.md`.
Retain MT-TIME-ENDPOINTS from `reviews/errata/2026-09-10-source-audit.md` and
MT-L-RIGIDITY-NORM-SCALING from `reviews/errata/2026-09-13-reduced-length-source.md`:
the full norm scales by
Q^(-1), its square by Q^(-2). The archived 2015 Chapter 19 correction does not
alter Definition 3.40. Generalized L-action and exponential transport belong
to M14. -/
theorem generalizedParabolicRescaling (n : ℕ)
    (hEquation : GeneralizedRicciGaugeTheory.{u} n) :
    GeneralizedParabolicRescalingTheory.{u} n := by
  refine {
    rescale := ?_
    metric_homothety := ?_
    coordinate_metric_homothety := ?_
    ordinary_flow := ?_
    ordinary_product_comparison := ?_ }
  · intro X _ A R Q hQ a
    exact ⟨M13.generalizedRescaling hEquation R Q hQ a⟩
  · intro M N _ _ _ _ _ _ _ _ _ _ _ _ g h f Q hQ hf
    exact M13.metricHomothetyCalculus g h f Q hQ hf
  · intro M N _ _ _ _ _ _ _ _ _ _ _ _ g h f Q hQ hf
    exact M13.metricHomothetyCalculus g h f Q hQ hf
  · intro M _ _ _ _ _ I F Q hQ a
    exact M13.ordinaryParabolicRescaling I F Q hQ a
  · intro M _ _ _ _ I F Q hQ a R source target
    exact M13.ordinaryParabolicProductComparison F Q hQ a R source target

/-- M13's complete positive-rescaling theorem supplied by the actual M12
intrinsic equation, regular horizontal calculus and ordinary product theorem.
It constructs the same geometries and identities as the core statement and
adds no admission. Sources: Morgan-Tian Definition 3.40, p. 61, with metric
conventions pp. 3-7 and domain conventions pp. 61-62; retain the endpoint and
full-curvature-norm corrections cited above. -/
theorem generalizedParabolicRescaling_from_M12 (n : ℕ) :
    GeneralizedParabolicRescalingTheory.{u} n :=
  generalizedParabolicRescaling n (generalizedRicciGaugeGeometry_from_M03_M04_M11 n)

end PoincareMT
