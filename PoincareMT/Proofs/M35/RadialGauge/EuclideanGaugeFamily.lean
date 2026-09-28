import PoincareMT.Proofs.M35.RadialGauge.DiffeomorphInverseTime
import PoincareMT.Proofs.M35.RadialGauge.EuclideanGaugeTime

/-!
# The constructed gauge as one actual family of diffeomorphisms

Morgan-Tian Proposition 12.26, pp. 320-322. The literal forward map
determines each smooth diffeomorphism and its inverse. Choosing those
slice witnesses preserves the proved joint regularity and the actual
forward and inverse time equations; the unused total family is identity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

/-- The same scalar solution gives a single actual smooth-diffeomorphism
family with jointly C1 forward and inverse maps on the slab interior. -/
theorem exists_euclideanGauge_family
    {u : ℝ → V → ℝ} {T : ℝ}
    (hc : ContDiffOn ℝ 1 (Function.uncurry u) (Ioo 0 T ×ˢ univ))
    (hs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (u t))
    (hv : ∀ t ∈ Icc 0 T, ∀ x, (1 + ‖x‖) * |u t x| ≤ 1 / 8)
    (hd : ∀ t ∈ Icc 0 T, ∀ x, (1 + ‖x‖) * ‖fderiv ℝ (u t) x‖ ≤ 1 / 8) :
    ∃ Φ : ℝ → Diffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) V V ∞,
      (∀ t ∈ Icc 0 T, (Φ t : V → V) = euclideanGauge (u t)) ∧
      ContDiffOn ℝ 1 (fun p : ℝ × V => Φ p.1 p.2) (Ioo 0 T ×ˢ univ) ∧
      ContDiffOn ℝ 1 (fun p : ℝ × V => (Φ p.1).symm p.2) (Ioo 0 T ×ˢ univ) := by
  classical
  have hex (t : ℝ) : ∃ Φ : Diffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) V V ∞,
      t ∈ Icc 0 T → (Φ : V → V) = euclideanGauge (u t) := by
    by_cases ht : t ∈ Icc 0 T
    · obtain ⟨Φ, hΦ⟩ := exists_euclideanGauge_diffeomorph (hs t ht) (hv t ht) (hd t ht)
      exact ⟨Φ, fun _ => hΦ⟩
    · exact ⟨Diffeomorph.refl (𝓡 (n + 1)) V ∞, fun h => (ht h).elim⟩
  choose Φ hΦ using hex
  have hforward : ContDiffOn ℝ 1 (fun p : ℝ × V => Φ p.1 p.2) (Ioo 0 T ×ˢ univ) := by
    apply (hc.exp.smul contDiffOn_snd).congr
    intro p hp
    exact congrFun (hΦ p.1 ⟨hp.1.1.le, hp.1.2.le⟩) p.2
  refine ⟨Φ, hΦ, hforward, ?_⟩
  intro p hp
  exact (diffeomorph_family_symm_contDiffAt isOpen_Ioo hforward hp.1).contDiffWithinAt

/-- A literal scalar time equation remains the actual time equation
after choosing the slice diffeomorphism witnesses. -/
theorem euclideanGauge_family_hasDerivAt_time
    {u : ℝ → V → ℝ} {T t q : ℝ} {x : V}
    {Φ : ℝ → Diffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) V V ∞}
    (hΦ : ∀ s ∈ Icc 0 T, (Φ s : V → V) = euclideanGauge (u s))
    (ht : t ∈ Ioo 0 T) (hu : HasDerivAt (fun s => u s x) q t) :
    HasDerivAt (fun s => Φ s x) ((Real.exp (u t x) * q) • x) t := by
  apply (euclideanGauge_hasDerivAt_time hu).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact congrFun (hΦ s ⟨hs.1.le, hs.2.le⟩) x

/-- The inverse family inherits the negative differential-weighted
velocity of the literal gauge, including at the fixed origin. -/
theorem euclideanGauge_family_symm_hasDerivAt_time
    {u : ℝ → V → ℝ} {T t q : ℝ} {x : V}
    {Φ : ℝ → Diffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) V V ∞}
    (hΦ : ∀ s ∈ Icc 0 T, (Φ s : V → V) = euclideanGauge (u s))
    (hc : ContDiffOn ℝ 1 (fun p : ℝ × V => Φ p.1 p.2) (Ioo 0 T ×ˢ univ))
    (ht : t ∈ Ioo 0 T)
    (hu : HasDerivAt (fun s => u s ((Φ t).symm x)) q t) :
    HasDerivAt (fun s => (Φ s).symm x)
      (-(fderiv ℝ ((Φ t).symm : V → V) x
        ((Real.exp (u t ((Φ t).symm x)) * q) • (Φ t).symm x))) t := by
  exact diffeomorph_family_symm_hasDerivAt isOpen_Ioo hc ht
    (euclideanGauge_family_hasDerivAt_time hΦ ht hu)

end PoincareMT.M35.RadialGauge
