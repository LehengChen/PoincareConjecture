import PoincareMT.Proofs.M60.Mathlib.SURegularizedQuadratic
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Paired weak derivative columns

The summed quadratic form and paired L2 weak convergence used in the
Sacks-Uhlenbeck direct method, Theorem 2.1 and Proposition 2.4, pp. 6-8.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace PoincareMT.M60

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The metric on two derivative columns is their actual summed quadratic form. -/
def suPairMetric (B : E →L[ℝ] E →L[ℝ] ℝ) : (E × E) →L[ℝ] (E × E) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.fst ℝ E E).precomp ℝ).comp
      (B.comp (ContinuousLinearMap.fst ℝ E E)) +
    ((ContinuousLinearMap.snd ℝ E E).precomp ℝ).comp
      (B.comp (ContinuousLinearMap.snd ℝ E E))

/-- Evaluation is the sum of the two original metric pairings. -/
theorem suPairMetric_apply (B : E →L[ℝ] E →L[ℝ] ℝ) (v w : E × E) :
    suPairMetric B v w = B v.1 w.1 + B v.2 w.2 := rfl

/-- A positive metric remains positive on every nonzero pair. -/
theorem suPairMetric_pos (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v ≠ 0, 0 < B v v) {v : E × E} (hv : v ≠ 0) :
    0 < suPairMetric B v v := by
  rw [suPairMetric_apply]
  have hn (w : E) : 0 ≤ B w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact (hB w hw).le
  by_cases h1 : v.1 = 0
  · have h2 : v.2 ≠ 0 := by
      intro h2
      apply hv
      exact Prod.ext h1 h2
    exact add_pos_of_nonneg_of_pos (hn _) (hB _ h2)
  · exact add_pos_of_pos_of_nonneg (hB _ h1) (hn _)

/-- Pairing the finite-dimensional coefficient forms is continuous. -/
theorem suPairMetric_continuous [FiniteDimensional ℝ E] :
    Continuous (suPairMetric (E := E)) := by
  apply continuous_clm_apply.mpr
  intro v
  apply continuous_clm_apply.mpr
  intro w
  change Continuous (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v.1 w.1 + B v.2 w.2)
  exact ((continuous_id.clm_apply continuous_const).clm_apply continuous_const).add
    ((continuous_id.clm_apply continuous_const).clm_apply continuous_const)

variable {X : Type*} [MeasurableSpace X] {mu : Measure X}

/-- A pair of genuine L2 columns, with the product norm used only for its topology. -/
def suPairLp (u v : Lp E 2 mu) : Lp (E × E) 2 mu :=
  (ContinuousLinearMap.inl ℝ E E).compLpL 2 mu u +
    (ContinuousLinearMap.inr ℝ E E).compLpL 2 mu v

/-- The paired L2 class is represented by the pair almost everywhere. -/
theorem suPairLp_coe (u v : Lp E 2 mu) :
    suPairLp u v =ᵐ[mu] fun x => (u x, v x) := by
  filter_upwards [Lp.coeFn_add ((ContinuousLinearMap.inl ℝ E E).compLpL 2 mu u)
      ((ContinuousLinearMap.inr ℝ E E).compLpL 2 mu v),
    (ContinuousLinearMap.inl ℝ E E).coeFn_compLpL u,
    (ContinuousLinearMap.inr ℝ E E).coeFn_compLpL v] with x hadd hu hv
  change ((ContinuousLinearMap.inl ℝ E E).compLpL 2 mu u +
    (ContinuousLinearMap.inr ℝ E E).compLpL 2 mu v) x = _
  rw [hadd, Pi.add_apply, hu, hv]
  ext <;> simp

/-- Separate weak convergence of the two actual derivative columns gives
weak convergence of the pair used by the intrinsic energy density. -/
theorem suPairLp_weak {u w : ℕ → Lp E 2 mu} {v z : Lp E 2 mu}
    (hu : ∀ L : StrongDual ℝ (Lp E 2 mu),
      Tendsto (fun n => L (u n)) atTop (𝓝 (L v)))
    (hw : ∀ L : StrongDual ℝ (Lp E 2 mu),
      Tendsto (fun n => L (w n)) atTop (𝓝 (L z)))
    (L : StrongDual ℝ (Lp (E × E) 2 mu)) :
    Tendsto (fun n => L (suPairLp (u n) (w n))) atTop (𝓝 (L (suPairLp v z))) := by
  have h1 := hu (L.comp ((ContinuousLinearMap.inl ℝ E E).compLpL 2 mu))
  have h2 := hw (L.comp ((ContinuousLinearMap.inr ℝ E E).compLpL 2 mu))
  simpa only [suPairLp, map_add, ContinuousLinearMap.comp_apply] using h1.add h2

end PoincareMT.M60
