import PoincareMT.Proofs.M35.RadialGauge.HeatTimeGain

/-!
# The actual source only needs measurability on its closed time slab

Morgan-Tian pp. 316-320. Extending a slab-measurable source by zero
gives the global measurable integrand used by the heat lemmas. Its actual
Duhamel integral agrees as a spatial function on every time in the slab,
so the actual spatial derivatives agree as well. No behavior outside the
flow's valid time interval is added as an assumption.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareMT.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin n)

/-- The literal zero extension of a source from its closed time slab. -/
noncomputable def slabSourceExtension (T : ℝ) (f : ℝ → V → F) (s : ℝ) (x : V) : F :=
  if s ∈ Icc 0 T then f s x else 0

omit [NormedSpace ℝ F] in
/-- The extension is exactly the original source throughout the slab. -/
theorem slabSourceExtension_of_mem {T s : ℝ} (hs : s ∈ Icc 0 T)
    (f : ℝ → V → F) : slabSourceExtension T f s = f s := by
  funext x
  simp only [slabSourceExtension, if_pos hs]

omit [NormedSpace ℝ F] in
/-- Subtype measurability on the actual time slab suffices for a globally
strongly measurable zero extension. -/
theorem slabSourceExtension_stronglyMeasurable {T : ℝ} {f : ℝ → V → F}
    (hf : StronglyMeasurable (fun p : Icc (0 : ℝ) T × V => f p.1.1 p.2)) :
    StronglyMeasurable (Function.uncurry (slabSourceExtension T f)) := by
  classical
  let S : Set (ℝ × V) := {p | p.1 ∈ Icc 0 T}
  have hS : MeasurableSet S := measurableSet_Icc.preimage measurable_fst
  have hbranch : StronglyMeasurable (fun p : S => f p.1.1 p.1.2) :=
    hf.comp_measurable
      (g := fun p : S => ((⟨p.1.1, p.2⟩ : Icc (0 : ℝ) T), p.1.2)) (by fun_prop)
  have h := hbranch.dite (g := fun _ : ↑(Sᶜ) => (0 : F)) stronglyMeasurable_const hS
  convert h using 1
  funext p
  dsimp only [Function.uncurry, slabSourceExtension, S]
  simp only [Set.mem_ofPred_eq]
  split_ifs <;> rfl

/-- On every actual time in the slab, the literal Duhamel integral is
unchanged as a function of the spatial variable. -/
theorem heatDuhamel_slabSourceExtension {T t : ℝ} (ht : t ∈ Icc 0 T)
    (f : ℝ → V → F) : heatDuhamel (slabSourceExtension T f) t = heatDuhamel f t := by
  funext x
  unfold heatDuhamel
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  change heatAverage (t - s) (slabSourceExtension T f s) x =
    heatAverage (t - s) (f s) x
  rw [slabSourceExtension_of_mem ⟨hs.1, hs.2.trans ht.2⟩]

/-- The actual total derivative agrees because the spatial functions agree. -/
theorem fderiv_heatDuhamel_slabSourceExtension {T t : ℝ} (ht : t ∈ Icc 0 T)
    (f : ℝ → V → F) :
    fderiv ℝ (heatDuhamel (slabSourceExtension T f) t) = fderiv ℝ (heatDuhamel f t) := by
  rw [heatDuhamel_slabSourceExtension ht]

/-- The explicit gradient-kernel integral also agrees on the actual slab. -/
theorem heatDuhamelGradient_slabSourceExtension {T t : ℝ} (ht : t ∈ Icc 0 T)
    (f : ℝ → V → F) :
    heatDuhamelGradient (slabSourceExtension T f) t = heatDuhamelGradient f t := by
  funext x
  unfold heatDuhamelGradient
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  change heatGradientKernel (t - s) (slabSourceExtension T f s) x =
    heatGradientKernel (t - s) (f s) x
  rw [slabSourceExtension_of_mem ⟨hs.1, hs.2.trans ht.2⟩]

end PoincareMT.M35.RadialGauge
