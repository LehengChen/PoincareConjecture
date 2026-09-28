import PoincareMT.Statements.M64Comparison

/-!
# Proposition 19.35: quantitative assembly

This file contains the arithmetic and quantifier assembly at the end of the
small-annulus argument.  The geometric inputs are deliberately exposed as a
separate interface: the polar Jacobi comparison, focusing estimate, and area
cutoff each return a length loss.  The constants follow the corrected proof
bookkeeping: the three losses are bounded by `L / 50`, `3 * L / 50`, and
`L / 10`, respectively, leaving more than three quarters of the first
boundary length.  No Plateau or higher-milestone module is imported.

Source: Morgan--Tian Proposition 19.35, pp. 467--481; the absolute-turning
and factor-two repairs recorded in the M64 erratum.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-! ## The explicit loss budget -/

/-- The numerical loss budget used in Proposition 19.35. Keeping this as a separate lemma
makes the final factor `3 / 4` independent of the geometric implementation of the three
exceptional sets. Source: MT Proposition 19.35, pp. 480-481;
`reports/2026-09-23-intrinsic-assembly.md`. -/
theorem m64Intrinsic_length_loss_budget
    {L L₂ c f a : ℝ}
    (hL : 0 ≤ L)
    (hc : c ≤ L / 50)
    (hf : f ≤ 3 * L / 50)
    (ha : a ≤ L / 10)
    (hremaining : L - c - f - a ≤ L₂) :
    (3 / 4 : ℝ) * L ≤ L₂ := by
  linarith

/-- A variant using a single total-loss bound. Source: MT Proposition 19.35, pp. 480-481;
`reports/2026-09-23-intrinsic-assembly.md`. -/
theorem m64Intrinsic_total_loss_budget
    {L L₂ e : ℝ}
    (hL : 0 ≤ L)
    (he : e ≤ (9 : ℝ) * L / 50)
    (hremaining : L - e ≤ L₂) :
    (3 / 4 : ℝ) * L ≤ L₂ := by
  linarith

/-! ## Geometric estimate interface -/

/-- The output of the polar-coordinate, Jacobi, focusing, and area-cutoff estimates for one
intrinsic annulus. `first_length` is retained explicitly because the strict hypothesis `r <
first_length` is needed before any of the three loss estimates can be applied. The bounds on
`curvature_loss`, `focusing_loss`, and `area_loss` are the corrected constants from the
source. The structure only packages inequalities; it does not assert existence of a minimal
annulus or identify a branch. Those analytic/geometric obligations belong to the producers
of this interface. Source: MT Proposition 19.35, pp. 480-481;
`reports/2026-09-23-intrinsic-assembly.md`. -/
structure M64IntrinsicLengthLossWitness (N : IntrinsicAnnulus)
    (delta r K mu : ℝ) where
  first_length : ℝ
  first_length_eq : first_length =
    intrinsicBoundaryLength N.metric 1 0 rampPeriod
  curvature_loss : ℝ
  focusing_loss : ℝ
  area_loss : ℝ
  curvature_loss_bound : curvature_loss ≤ first_length / 50
  focusing_loss_bound : focusing_loss ≤ 3 * first_length / 50
  area_loss_bound : area_loss ≤ first_length / 10
  remaining_length :
    first_length - curvature_loss - focusing_loss - area_loss ≤
      intrinsicBoundaryLength N.metric 2 0 rampPeriod

/-- Explicit loss estimates instantiate the witness used by the public comparison. This
constructor keeps the three geometric losses separate, so the polar/Jacobi, focusing, and
area producers can discharge their own fields without changing the consumer interface.
Source: MT Proposition 19.35, pp. 480-481; `reports/2026-09-23-intrinsic-assembly.md`. -/
theorem m64Intrinsic_length_loss_witness_of_explicit_losses
    (N : IntrinsicAnnulus) (delta r K mu : ℝ)
    (curvature_loss focusing_loss area_loss : ℝ)
    (hcurvature : curvature_loss ≤
      intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50)
    (hfocusing : focusing_loss ≤
      3 * intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50)
    (harea : area_loss ≤
      intrinsicBoundaryLength N.metric 1 0 rampPeriod / 10)
    (hremaining : intrinsicBoundaryLength N.metric 1 0 rampPeriod -
        curvature_loss - focusing_loss - area_loss ≤
      intrinsicBoundaryLength N.metric 2 0 rampPeriod) :
    Nonempty (M64IntrinsicLengthLossWitness N delta r K mu) := by
  exact ⟨{
    first_length := intrinsicBoundaryLength N.metric 1 0 rampPeriod
    first_length_eq := rfl
    curvature_loss := curvature_loss
    focusing_loss := focusing_loss
    area_loss := area_loss
    curvature_loss_bound := hcurvature
    focusing_loss_bound := hfocusing
    area_loss_bound := harea
    remaining_length := hremaining
  }⟩

/-- The explicit-loss constructor closes the final numerical comparison once the strict
first-boundary-length hypothesis supplies nonnegativity. Source: MT Proposition 19.35, pp.
480-481; `reports/2026-09-23-intrinsic-assembly.md`. -/
theorem m64Intrinsic_comparison_of_explicit_losses
    (N : IntrinsicAnnulus) {r : ℝ} (hr : 0 < r)
    (hfirst : r < intrinsicBoundaryLength N.metric 1 0 rampPeriod)
    (curvature_loss focusing_loss area_loss : ℝ)
    (hcurvature : curvature_loss ≤
      intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50)
    (hfocusing : focusing_loss ≤
      3 * intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50)
    (harea : area_loss ≤
      intrinsicBoundaryLength N.metric 1 0 rampPeriod / 10)
    (hremaining : intrinsicBoundaryLength N.metric 1 0 rampPeriod -
        curvature_loss - focusing_loss - area_loss ≤
      intrinsicBoundaryLength N.metric 2 0 rampPeriod) :
    (3 / 4 : ℝ) * intrinsicBoundaryLength N.metric 1 0 rampPeriod ≤
      intrinsicBoundaryLength N.metric 2 0 rampPeriod := by
  have hL : 0 ≤ intrinsicBoundaryLength N.metric 1 0 rampPeriod := by
    linarith
  exact m64Intrinsic_length_loss_budget hL hcurvature hfocusing harea hremaining

/-- The quantitative interface needed to assemble Proposition 19.35. A producer proves this
using the exponential chart and the intrinsic Jacobi comparison; the present theorem
performs only the logical and numerical assembly. Source: MT Proposition 19.35, pp. 480-481;
`reports/2026-09-23-intrinsic-assembly.md`. -/
def M64IntrinsicLengthLossEstimates : Prop :=
  ∀ delta r K : ℝ, 0 < delta → delta < 1 / 100 → 0 < r →
    ∃ mu : ℝ, 0 < mu ∧
      ∀ N : IntrinsicAnnulus,
        N.GaussianCurvatureBound K →
        r < intrinsicBoundaryLength N.metric 1 0 rampPeriod →
        N.SmallBoundaryTurning delta r →
        intrinsicAnnulusArea N.metric < mu →
          Nonempty (M64IntrinsicLengthLossWitness N delta r K mu)

/-- A witness from the geometric estimates implies the exact public Proposition 19.35
statement. Source: MT Proposition 19.35, pp. 480-481;
`reports/2026-09-23-intrinsic-assembly.md`. -/
theorem m64IntrinsicAnnulusComparison_of_length_loss_estimates
    (h : M64IntrinsicLengthLossEstimates) :
    M64IntrinsicAnnulusComparison := by
  intro delta r K hdelta_pos hdelta_small hr
  obtain ⟨mu, hmu_pos, hmu⟩ := h delta r K hdelta_pos hdelta_small hr
  refine ⟨mu, hmu_pos, ?_⟩
  intro N hcurv hfirst hturn harea
  obtain ⟨W⟩ := hmu N hcurv hfirst hturn harea
  have hL : 0 ≤ W.first_length := by
    rw [W.first_length_eq]
    linarith [hr, hfirst]
  have hbound := m64Intrinsic_length_loss_budget hL
    W.curvature_loss_bound W.focusing_loss_bound W.area_loss_bound
    W.remaining_length
  simpa [W.first_length_eq] using hbound

end PoincareMT
