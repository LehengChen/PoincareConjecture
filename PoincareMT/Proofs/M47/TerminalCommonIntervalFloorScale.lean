import PoincareMT.Proofs.M47.TerminalCommonIntervalStopped
import PoincareMT.Proofs.M47.BlowupControlsScales

/-!
# Terminal floor before the common interval

The terminal curvature floor fixes the analytic bound before the common
backward duration is selected.  First-failure radii retain their literal
threshold inequality; no equality of the scalar with that threshold is used.
Source: terminal-common-interval-floor-scale.md.
-/

set_option autoImplicit false

open Set Filter

universe u

namespace PoincareMT.M47

/-- A terminal curvature floor precedes the common-duration scale package.

The radius threshold and both first-failure normalization identities remain
literal outputs, so this adapter does not insert a Claim 17.9 equality.
-/
theorem terminalCommonInterval_after_terminal_curvature_floor
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (V : GeneralizedBlowupSequence.{u})
    {K : ℝ} (hK : 1 ≤ K) {eta : ℝ}
    (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (hthreshold : ∀ k, (r k)⁻¹ ^ 2 ≤ V.scale k) :
    ∃ Delta : ℝ, Delta = terminalCommonIntervalDuration S B K ∧
      0 < Delta ∧ Delta ≤ 1 ∧
      ∀ᶠ k in atTop,
        64 * (2 * Delta + 1) ≤ V.scale k ∧
        B.curvature_threshold ≤ V.scale k ∧
        blowupPinchingThreshold (8 * K) eta ≤ V.scale k ∧
        (r k)⁻¹ ^ 2 ≤ V.scale k ∧
        0 < V.scale k ∧
        0 < (V.scale k * (r k) ^ 2)⁻¹ ∧
        (V.scale k * (r k) ^ 2)⁻¹ ≤ 1 ∧
        (r k)⁻¹ ^ 2 / V.scale k = (V.scale k * (r k) ^ 2)⁻¹ ∧
        (V.scale k)⁻¹ = (V.scale k * (r k) ^ 2)⁻¹ * (r k) ^ 2 := by
  let Delta : ℝ := terminalCommonIntervalDuration S B K
  have hDelta := terminalCommonInterval_duration_bounds S B hK
  refine ⟨Delta, rfl, hDelta.1, hDelta.2.1, ?_⟩
  have hlarge := terminalCommonInterval_eventually_large S B V K eta
  filter_upwards [hlarge] with k hk
  obtain ⟨hQ, htheta, hthetaLe, hratio, hinverse⟩ :=
    first_failure_blowup_scale (hr k) (hthreshold k)
  refine ⟨?_, hk.2.1, hk.2.2, hthreshold k, hQ, htheta, hthetaLe,
    hratio, hinverse⟩
  simpa only [Delta] using hk.1

end PoincareMT.M47
