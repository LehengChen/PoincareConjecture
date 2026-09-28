import PoincareMT.Proofs.M63.Sec19_1_LocalFlow.PeriodicGaussianSpectral
import PoincareMT.Proofs.M63.Sec19_1_LocalFlow.PeriodicGaussianC2
import PoincareMT.Proofs.M63.Sec19_1_LocalFlow.PeriodicInitialCoordinates

/-!
# C2 initial trace of the actual homogeneous spectral heat path

The actual first two spatial derivatives converge uniformly through time
zero for C2 initial circle data. MT2007 Claim 19.1, p. 437; contract block 8
and `2026-09-21-periodic-gaussian-initial-trace.md`, statement 13.
This theorem concerns the homogeneous path only.
-/

set_option autoImplicit false

open PoincareMT.SpectralHeatNative Filter
open scoped Topology

namespace PoincareMT.M63

variable {L : ℝ} [Fact (0 < L)]

/-- The actual homogeneous M03 heat path has continuous uniform first
and second jets through its exact C2 initial curve. MT2007 Claim 19.1,
p. 437; Gaussian trace derivation, statement 13. Only C2 regularity of
the actual initial function is required. -/
theorem exists_initialHeat_c2_jets (f : C(AddCircle L, ℝ))
    (hf : ContDiff ℝ 2 (fun x : ℝ => f (x : AddCircle L)))
    (w : State (ℤ × Fin 2))
    (hw : realPeriodicJet (L := L) 0 0 (by omega)
      (shiftedBaseMultiplier (periodicSpectrum L) w) = f) :
    let q0 := fun t : NNReal => realPeriodicJet (L := L) 0 0 (by omega)
      (heat (periodicSpectrum L) t (shiftedBaseMultiplier (periodicSpectrum L) w))
    ∃ q1 q2 : NNReal → C(AddCircle L, ℝ),
      Continuous q0 ∧ Continuous q1 ∧ Continuous q2 ∧ q0 0 = f ∧
      (∀ t : NNReal, ContDiff ℝ 2 (fun x : ℝ => q0 t (x : AddCircle L)) ∧
        (∀ x : ℝ, HasDerivAt (fun y : ℝ => q0 t (y : AddCircle L)) (q1 t (x : AddCircle L)) x) ∧
        (∀ x : ℝ, HasDerivAt (fun y : ℝ => q1 t (y : AddCircle L)) (q2 t (x : AddCircle L)) x)) ∧
      Tendsto (fun t : NNReal => ‖q0 t - q0 0‖) (𝓝 0) (𝓝 0) ∧
      Tendsto (fun t : NNReal => ‖q1 t - q1 0‖) (𝓝 0) (𝓝 0) ∧
      Tendsto (fun t : NNReal => ‖q2 t - q2 0‖) (𝓝 0) (𝓝 0) := by
  dsimp only
  obtain ⟨f1, f2, _, _, hG⟩ := exists_periodicGaussian_c2_jets f hf
  let q0 := fun t : NNReal => realPeriodicJet (L := L) 0 0 (by omega)
    (heat (periodicSpectrum L) t (shiftedBaseMultiplier (periodicSpectrum L) w))
  have hq0 (t : NNReal) : q0 t = periodicGaussianHeat (t : ℝ) f := by
    dsimp only [q0]
    rw [realPeriodicJet_heat, hw]
  let q1 := fun t : NNReal => periodicGaussianHeat (t : ℝ) f1
  let q2 := fun t : NNReal => periodicGaussianHeat (t : ℝ) f2
  have hc0 : Continuous q0 := by
    simpa only [funext hq0, Function.comp_def] using
      (periodicGaussianHeat_properties f).2.2.comp NNReal.continuous_coe
  have hc1 : Continuous q1 :=
    (periodicGaussianHeat_properties f1).2.2.comp NNReal.continuous_coe
  have hc2 : Continuous q2 :=
    (periodicGaussianHeat_properties f2).2.2.comp NNReal.continuous_coe
  refine ⟨q1, q2, hc0, hc1, hc2, ?_, ?_, ?_, ?_, ?_⟩
  · change q0 0 = f
    rw [hq0]
    exact (periodicGaussianHeat_properties f).2.1
  · intro t
    simpa only [realPeriodicJet_heat, hw, q1, q2] using hG (t : ℝ)
  · simpa only [Pi.sub_apply, sub_self, norm_zero] using
      (hc0.sub (continuous_const : Continuous (fun _ : NNReal => q0 0))).norm.tendsto (0 : NNReal)
  · simpa only [Pi.sub_apply, sub_self, norm_zero] using
      (hc1.sub (continuous_const : Continuous (fun _ : NNReal => q1 0))).norm.tendsto (0 : NNReal)
  · simpa only [Pi.sub_apply, sub_self, norm_zero] using
      (hc2.sub (continuous_const : Continuous (fun _ : NNReal => q2 0))).norm.tendsto (0 : NNReal)

end PoincareMT.M63
