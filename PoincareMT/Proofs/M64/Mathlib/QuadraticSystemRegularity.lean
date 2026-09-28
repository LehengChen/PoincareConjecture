import PoincareMT.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityTomiRegularity
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Vector regularity from the quadratic weak system

The standalone M65 Tomi theorem supplies each scalar component's C1
regularity from the weak equation and the original energy decay. This
assembles the actual Euclidean vector representative on the open domain,
as needed for reflected annulus charts in the Morrey--Lemaire argument.
Source: Tomi 1969, pp. 215-217; MT Lemma 19.2, p. 438. The M65 reuse is
authorized and audited in `derivations/2026-09-26-m65-analytic-reuse.md`.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff SchwartzMap LineDeriv InnerProductSpace

namespace PoincareMT

open EuclideanTranslationNative

/-- A continuous Holder representative of a quadratic weak system is C1
throughout its open domain when its original energy decays locally.
No continuous weak derivative is assumed. Source: Tomi 1969, pp. 215-217,
via the independent M65 component theorem; see the M65-reuse derivation. -/
theorem m64QuadraticSystem_contDiffOn {N : ℕ} (u : Fin N → ScalarL2 2)
    (d : Fin N → Fin 2 → ScalarL2 2) (f : Fin N → LoopPlane → ℝ)
    (v : LoopPlane → EuclideanSpace ℝ (Fin N))
    (hf : ∀ j, Integrable (f j)) {U : Set LoopPlane} (hU : IsOpen U)
    {S : ℝ} (hfs : ∀ j, Function.support (f j) ⊆ closedBall (0 : LoopPlane) S)
    (hweak : ∀ j i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d j i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u j z * fderiv ℝ φ z (EuclideanSpace.single i 1)))
    (heq : ∀ j (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f j z * φ z))
    {C B H β : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H) (hβ : 0 < β)
    (hgrowth : ∀ j, ∀ᵐ z ∂volume, z ∈ U →
      |f j z| ≤ C * (∑ k : Fin N, ∑ i : Fin 2, (d k i z) ^ 2))
    (hbound : ∀ j, ∀ᵐ z ∂volume, ‖u j z‖ ≤ B)
    (hv : ContinuousOn v U)
    (huv : ∀ j, (u j : LoopPlane → ℝ) =ᵐ[volume.restrict U] fun z => v z j)
    (hholder : ∀ x ∈ U, ∀ z ∈ U, ∀ j, |v z j - v x j| ≤ H * ‖z - x‖ ^ β)
    (hdecay : ∀ p ∈ U, ∃ Λ ≥ 0, ∃ R > 0,
      ∀ x ∈ ball p R, ∀ r : ℝ, 0 < r → r ≤ R →
        (∫ z in closedBall x r, ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) ≤
          Λ * r ^ (2 * β)) :
    ContDiffOn ℝ 1 v U := by
  intro p hp
  obtain ⟨Λ, hΛ, R, hR, henergy⟩ := hdecay p hp
  have hcoord := M65Boundary.quadratic_holder_contDiffAt u d f
    (fun j z => v z j) hf hU hfs hweak heq hC hH hβ hΛ hR hgrowth hbound
    (fun j => (EuclideanSpace.proj j).continuous.comp_continuousOn hv)
    huv hholder hp henergy
  exact ((contDiffAt_piLp 2).mpr hcoord).contDiffWithinAt

end PoincareMT
