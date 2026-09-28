import PoincareMT.Proofs.M35.Uniqueness.Heat.WeakValuePath
import PoincareMT.Proofs.M35.Uniqueness.Heat.FormIntegral

/-!
# The linear continuous value path retains the actual Bochner equation

Morgan-Tian, Section 12.5, p. 304: equality of continuous traces
identifies the bounded linear realization with the actual spectral
primitive at every time of the slab.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareMT.M35.Uniqueness.Heat

open SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

theorem weakValueFunction_integral (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (F : Lp V 2 (timeMeasure T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    J.adjoint (weakValueFunction J hc hd hi hn hT F t) =
      ∫ s in (0 : ℝ)..t, F s - formWeakHeatOperator J hc hd hi hn hT F s +
        J.adjoint (J (formWeakHeatOperator J hc hd hi hn hT F s)) := by
  obtain ⟨U, hU0, hUc, hUg, hUi⟩ := formWeakHeat_integral_value_trace J hc hd hi hn hT F
  have hW := weakValueFunction_spec J hc hd hi hn hT F
  have he := continuous_time_trace_eq (hW.1.trans hU0.symm) hW.2.1 hUc (by
    filter_upwards [hW.2.2.1, hUg] with s hw hu
    exact hw.symm.trans hu)
  rw [he t ht]
  exact hUi t ht

theorem weakValuePathOperator_apply (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (F : Lp V 2 (timeMeasure T)) (t : Icc (0 : ℝ) T) :
    weakValuePathOperator J hc hd hi hn hT F t = weakValueFunction J hc hd hi hn hT F t.val := rfl

end PoincareMT.M35.Uniqueness.Heat
