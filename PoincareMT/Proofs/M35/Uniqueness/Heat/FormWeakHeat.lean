import PoincareMT.Proofs.M35.Uniqueness.Heat.FormDualResponse

/-!
# Actual weak heat for arbitrary form-dual forcing

Morgan-Tian, Section 12.5, p. 304: the Riesz form representative of
the variable-coefficient forcing is arbitrary time-L2 data. Encoding
and decoding the actual form basis transports the constructed spectral
response to that forcing space, preserving its quantitative bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace PoincareMT.M35.Uniqueness.Heat

open HilbertResolventNative SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

def formWeakHeatOperator (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) : Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T) :=
  (formDualResponseOperator J hc hd hi hn hT).comp
    ((formEigenbasis J hc hd hi).repr.toContinuousLinearEquiv.toContinuousLinearMap.compLpL
      2 (timeMeasure T))

theorem norm_formWeakHeatOperator_le (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) : ‖formWeakHeatOperator J hc hd hi hn hT‖ ≤ T + 1 := by
  have hB : ‖(formEigenbasis J hc hd hi).repr.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 :=
    (formEigenbasis J hc hd hi).repr.toLinearIsometry.norm_toContinuousLinearMap_le
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (norm_formDualResponseOperator_le J hc hd hi hn hT)
      (ContinuousLinearMap.norm_compLpL_le _ |>.trans hB)
      (ContinuousLinearMap.opNorm_nonneg _)
      (by positivity)).trans_eq (mul_one _))

/-- Actual weak heat in the form dual, with its zero initial trace,
time derivative and literal variational generator equation. -/
theorem formWeakHeat_equation (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (F : Lp V 2 (timeMeasure T)) :
    ∃ P D : ℝ → V,
      P 0 = 0 ∧ ContinuousOn P (Icc (0 : ℝ) T) ∧ MemLp D 2 (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt P (D t) t) ∧
      (∀ᵐ t ∂timeMeasure T,
        J.adjoint (J (formWeakHeatOperator J hc hd hi hn hT F t)) = P t) ∧
      (∀ᵐ t ∂timeMeasure T,
        D t + formWeakHeatOperator J hc hd hi hn hT F t - P t = F t) := by
  let B := (formEigenbasis J hc hd hi).repr
  let C := B.toContinuousLinearEquiv.toContinuousLinearMap
  let E := C.compLpL 2 (timeMeasure T) F
  obtain ⟨P, D, hP0, hPc, hD, hderiv, hgraph, heq⟩ :=
    formDualResponse_weak_equation J hc hd hi hn hT E
  refine ⟨P, D, hP0, hPc, hD, hderiv, hgraph, ?_⟩
  filter_upwards [heq, C.coeFn_compLpL F] with t ht hEt
  change D t + formDualResponseOperator J hc hd hi hn hT E t - P t = F t
  rw [ht, hEt]
  exact B.symm_apply_apply (F t)

end PoincareMT.M35.Uniqueness.Heat
