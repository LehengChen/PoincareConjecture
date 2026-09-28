import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth extension by a supported time cutoff

Sections 3-4 of the P2 planar-transfer skeleton. A closed support band
inside the open regular time domain gives a full zero neighborhood
where the original map need not be smooth.
See `smale/derivations/2026-09-22-smooth-time-cutoff.md`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareMT.M25.Topology3D

/-- A smooth cutoff supported in a closed subset of the open regular
time domain makes the actual product globally smooth; P2 skeleton, sections 3-4. -/
theorem contDiff_timeCutoff
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K J : Set ℝ} (hK : IsClosed K) (hJ : IsOpen J) (hKJ : K ⊆ J)
    {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (hzero : ∀ z ∉ K, τ z = 0)
    {F : ℝ × V → E} (hF : ContDiffOn ℝ ∞ F (J ×ˢ univ)) :
    ContDiff ℝ ∞ (fun p : ℝ × V => τ p.1 • F p) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.1 ∈ J
  · exact (hτ.comp contDiff_fst).contDiffAt.smul
      (hF.contDiffAt ((hJ.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩))
  · have hpK : p.1 ∉ K := fun h => hp (hKJ h)
    have hn : ∀ᶠ q : ℝ × V in 𝓝 p, q.1 ∉ K :=
      (hK.isOpen_compl.preimage continuous_fst).mem_nhds hpK
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × V => (0 : E)) p).congr_of_eventuallyEq
    filter_upwards [hn] with q hq
    simp only [hzero q.1 hq, zero_smul]

end PoincareMT.M25.Topology3D
