import PoincareMT.Definitions.Ch11.SingularLimits

/-! # Terminal accuracy calibration from the pinned M31 donor -/

set_option autoImplicit false

namespace PoincareMT

/-- Room for the strict chart shortening in the same-core construction. -/
theorem four_lt_terminalAccuracyFactor : 4 < terminalAccuracyFactor := by
  unfold terminalAccuracyFactor; norm_num

/-- The terminal factor absorbs the checked linear scalar-ratio coefficient
in the translated normalized-cylinder jet estimate. -/
theorem terminalAccuracyFactor_scalar_ratio_budget :
    (32 : ℝ) + 6 * (2000000000004 : ℝ) ^ 2 < terminalAccuracyFactor ^ 2 := by
  unfold terminalAccuracyFactor; norm_num

end PoincareMT
