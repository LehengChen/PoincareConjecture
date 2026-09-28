import PoincareMT.Definitions.Ch03.RicciFlow
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Native global metric-section decoder

The coordinate construction ultimately has to return one spacetime section of
the tangent-cotangent bundle.  This file isolates the purely geometric
decoding step: once a globally defined section has the pointwise metric
properties and the required smoothness, it is assembled into the public
`RiemannianMetric.IsSmoothFamilyOn` family predicate.  The analytic producer
still has to construct this section and prove its bounds.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Manifold ContDiff Bundle
open Bornology

noncomputable section

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "ModelE" => EuclideanSpace ℝ (Fin n)
local notation "FiberBilin" =>
  fun x : M => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ

/-- A globally defined smooth metric section on a time set.

The `inner` field is already a section of the bundle of continuous bilinear
forms.  The two bundle-boundedness fields are exactly the remaining fields of
`Bundle.ContMDiffRiemannianMetric`; keeping them in this record prevents the
decoder from hiding positivity or finite-dimensional control.
-/
structure GlobalMetricSection (J : Set ℝ) where
  inner : ℝ → ∀ x : M, FiberBilin x
  symm : ∀ (t : ℝ) (x : M) (v w : TangentSpace (𝓡 n) x),
    inner t x v w = inner t x w v
  pos : ∀ (t : ℝ) (x : M) (v : TangentSpace (𝓡 n) x),
    v ≠ 0 → 0 < inner t x v v
  isVonNBounded : ∀ (t : ℝ) (x : M),
    IsVonNBounded ℝ {v : TangentSpace (𝓡 n) x | inner t x v v < 1}
  slice_smooth : ∀ t : ℝ,
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, ModelE →L[ℝ] ModelE →L[ℝ] ℝ)) ∞
      (fun x : M => (⟨x, inner t x⟩ :
        Bundle.TotalSpace (ModelE →L[ℝ] ModelE →L[ℝ] ℝ) FiberBilin))
  joint_smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, ModelE →L[ℝ] ModelE →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, inner p.1 p.2⟩ :
        Bundle.TotalSpace (ModelE →L[ℝ] ModelE →L[ℝ] ℝ) FiberBilin))
      (J ×ˢ Set.univ)

structure GlobalMetricSectionOf (g₀ : RiemannianMetric n M) (J : Set ℝ)
    extends GlobalMetricSection (n := n) (M := M) J where
  initial_eq : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
    inner 0 x v w = g₀.inner x v w

namespace GlobalMetricSectionOf

variable {g₀ : RiemannianMetric n M} {J : Set ℝ}
  (S : GlobalMetricSectionOf (n := n) (M := M) g₀ J)

/-- The constant section is a concrete sanity instance of the decoder. -/
noncomputable def constant (g₀ : RiemannianMetric n M) (J : Set ℝ) :
    GlobalMetricSectionOf (n := n) (M := M) g₀ J where
  inner := fun _ x => g₀.inner x
  symm := by
    intro t x v w
    exact g₀.symm x v w
  pos := by
    intro t x v hv
    exact g₀.pos x v hv
  isVonNBounded := by
    intro t x
    exact g₀.isVonNBounded x
  slice_smooth := by
    intro t
    simpa using g₀.contMDiff
  joint_smooth := by
    have hs : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 n) ∞
        (Prod.snd : ℝ × M → M) :=
      by exact contMDiff_snd
    have h := g₀.contMDiff.comp hs
    change ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, ModelE →L[ℝ] ModelE →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, g₀.inner p.2⟩ :
        Bundle.TotalSpace (ModelE →L[ℝ] ModelE →L[ℝ] ℝ) FiberBilin)) at h
    exact h.contMDiffOn
  initial_eq := by
    intro x v w
    rfl

/-- Decode one time slice into the native smooth Riemannian metric type. -/
noncomputable def metric (t : ℝ) : RiemannianMetric n M where
  inner x := S.inner t x
  symm x v w := S.symm t x v w
  pos x v hv := S.pos t x v hv
  isVonNBounded x := S.isVonNBounded t x
  contMDiff := S.slice_smooth t

@[simp] theorem metric_inner (t : ℝ) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    (S.metric t).inner x v w = S.inner t x v w := rfl

theorem metric_initial : S.metric 0 = g₀ := by
  have hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      (S.metric 0).inner x v w = g₀.inner x v w := by
    intro x v w
    rw [S.metric_inner, S.initial_eq]
  cases h₁ : S.metric 0
  cases h₂ : g₀
  simp only [Bundle.ContMDiffRiemannianMetric.mk.injEq]
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simpa only [h₁, h₂] using hinner x v w

theorem metric_isSmoothFamilyOn :
    RiemannianMetric.IsSmoothFamilyOn S.metric J := by
  change ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
    ((𝓡 n).prod 𝓘(ℝ, ModelE →L[ℝ] ModelE →L[ℝ] ℝ)) ∞
    (fun p : ℝ × M => (⟨p.2, (S.metric p.1).inner p.2⟩ :
      Bundle.TotalSpace (ModelE →L[ℝ] ModelE →L[ℝ] ℝ) FiberBilin))
    (J ×ˢ Set.univ)
  exact S.joint_smooth

end GlobalMetricSectionOf

end PoincareMT

end
