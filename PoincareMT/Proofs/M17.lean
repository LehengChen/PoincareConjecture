import PoincareMT.Statements.M17BlowupSetup
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Rescaling.Construction

/-!
# M17 blow-up sequence proof assembly

The imported theorem below is the fixed-carrier sequence portion of
Morgan--Tian Theorem 9.11. It is deliberately separated from the later
pointed-limit extraction and asymptotic soliton equation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-!
Given an ancient kappa-solution `K`, a fixed reference point, and arbitrary
positive scales `tau k` tending to infinity, choose at each scale a point
minimizing the reduced length from `(reference,0)`.  The M10 minimum bound
gives reduced length at most `n/2`; M13 supplies the actual rescaled flow with
metric `tau⁻¹ * g (tau * t)` on the open ancient interval.  The output is the
corresponding `AncientRescalingSequence`, tied to the supplied reference and
scale sequence.  This theorem asserts no limit, subsequence, bounded-distance
estimate, AVR conclusion, or soliton equation.

Sources: Morgan--Tian Theorem 7.10 and Claim 7.11, pp. 154--156;
Corollary 6.74, p. 142; Definition 9.1, p. 180; Theorem 9.11 and
Remark 9.12, pp. 183--185; and the rescaling convention in Definition 3.40,
p. 61.
The minimum-bound and full-norm conventions follow
`reviews/contracts/M17-repair-contract.md` and
`reviews/errata/2026-09-13-reduced-length-source.md`.
-/
theorem ancientBlowupSequenceSetup (n : ℕ)
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) (reference : M) (tau : ℕ → ℝ)
    (tau_pos : ∀ k, 0 < tau k)
    (tau_tendsto : Filter.Tendsto tau Filter.atTop Filter.atTop)
    (hM10 : AncientReducedVolumeMinimumProvider K)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n) :
    AncientBlowupSetupConclusion K reference tau := by
  exact horizon_ancientBlowupSequenceSetup n M K reference tau tau_pos
    tau_tendsto hM10 hM13

/-! Relative assembly from the same two reviewed predecessor interfaces. -/
theorem ancientBlowupSequenceSetupTheory (n : ℕ)
    (hM10 : ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
      [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution n M) (_reference : M),
      AncientReducedVolumeMinimumProvider K)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n) :
    AncientBlowupSetupTheory.{u} n := by
  refine ⟨?_⟩
  intro M _ _ _ _ _ _ _ _ _ K reference tau tau_pos tau_tendsto
  exact ancientBlowupSequenceSetup n M K reference tau tau_pos tau_tendsto
    (hM10 M K reference) hM13

end PoincareMT
