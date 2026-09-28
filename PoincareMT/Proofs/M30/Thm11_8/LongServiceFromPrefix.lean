import PoincareMT.Proofs.M30.Thm11_8.FiniteSlabContinuation
import PoincareMT.Proofs.M30.Thm11_8.LongSlabService
import PoincareMT.Definitions.M30ControlledBlowupLimits

/-!
# Uniform-prefix input for the long slab service

This adapter isolates the finite continuation step in Claim 11.17.  A
uniform scalar prefix coefficient, chosen before the terminal radius and
defect tolerance, produces the frozen `M30LongSlabControlService`.  The
remaining endpoint and horizon argument is deliberately left to its caller.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

/-- A uniform scalar prefix producer supplies the long slab service after the
finite guarded continuation.  The coefficient `D` is selected before every
source radius and defect tolerance (Morgan--Tian Claim 11.17, pp. 277--278).
The supplied prefix cylinders retain the original open-left finite slab and
their terminal identity; `eventually_finiteSlab_bounds_of_uniform_prefix_scalar`
adds the closed buffer and totalizes only the source map outside its ball.
-/
theorem longSlabControlService_of_uniform_prefix
    (hC : RicciFlowCurvatureTheory.{u})
    {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ} {T₀ : ℝ≥0∞}
    (H : M30LongBlowupControls S epsilon canonicalConstant kappa r₀ mu T₀)
    (hprefix : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T₀ →
      ∃ Tplus : ℝ, ∃ hTplus : T < Tplus,
        ENNReal.ofReal Tplus < T₀ ∧
        ∃ D : ℝ, 4 ≤ D ∧
          ∀ A : ℝ, 0 < A → ∀ t : ℝ, 0 < t → ∀ htT : t < T,
            ∀ᶠ k : ℕ in atTop,
              ∃ e : M30FiniteHorizonSlab S k A Tplus kappa r₀,
                ∀ s (hs : s ∈ Icc (-t) 0)
                  (x : ((S.flow k).slice (S.base k).1).carrier),
                  x ∈ S.baseBall k A →
                    (S.flow k).scalar
                    ((FiniteHorizonSlab.closedEmbedding e hTplus).pointMap s
                      (show s ∈ Icc (-T) 0 from
                        ⟨(neg_le_neg (le_of_lt htT)).trans hs.1, hs.2⟩) x) ≤
                    D * S.scale k) :
    M30LongSlabControlService S kappa r₀ T₀ := by
  refine { bounds := ?_ }
  intro T hT hTT
  obtain ⟨Tplus, hTplus, hTplusT₀, D, hD, hprefixTD⟩ :=
    hprefix T hT hTT
  have hTplusPos : 0 < Tplus := hT.trans hTplus
  refine ⟨26 * D, by positivity, ?_⟩
  intro A hA eta heta
  have hprefixA : ∀ t : ℝ, 0 < t → ∀ htT : t < T,
      ∀ᶠ k : ℕ in atTop,
        ∃ e : M30FiniteHorizonSlab S k A Tplus kappa r₀,
          ∀ s (hs : s ∈ Icc (-t) 0)
            (x : ((S.flow k).slice (S.base k).1).carrier),
            x ∈ S.baseBall k A →
              (S.flow k).scalar
                ((FiniteHorizonSlab.closedEmbedding e
                  (htT.trans hTplus)).pointMap s hs x) ≤
                D * S.scale k := by
    intro t ht htT
    exact hprefixTD A hA t ht htT
  obtain ⟨hdeltaA, hbufferA, hfamilyA⟩ :=
    eventually_finiteSlab_bounds_of_uniform_prefix_scalar hC
      H.toM30CommonBlowupControls A T Tplus D hA hT hTplus hD hprefixA
  filter_upwards [hfamilyA eta heta] with k hk
  obtain ⟨e, hcurv, hdefect⟩ := hk
  refine ⟨Tplus, hTplusPos, hTplus, hTplusT₀,
    ⟨e, ?_, ?_⟩⟩
  · intro s hs x _hx
    have hs' : s ∈ Icc (-(T +
        min (T / 4) (min ((Tplus - T) / 4)
          (1 / (32 * H.analytic_constant * D))))) 0 := by
      exact ⟨by linarith [hs.1, hdeltaA], hs.2⟩
    have hpoint :
        (FiniteHorizonSlab.closedEmbedding e hbufferA).pointMap s hs' x =
          (FiniteHorizonSlab.closedEmbedding e hTplus).pointMap s hs x := by
      change e.embedding.pointMap s _ x = e.embedding.pointMap s _ x
      rfl
    rw [← hpoint]
    exact hcurv s hs' x
  · intro s hs x _hx
    have hs' : s ∈ Icc (-(T +
        min (T / 4) (min ((Tplus - T) / 4)
          (1 / (32 * H.analytic_constant * D))))) 0 := by
      exact ⟨by linarith [hs.1, hdeltaA], hs.2⟩
    have hpoint :
        (FiniteHorizonSlab.closedEmbedding e hbufferA).pointMap s hs' x =
          (FiniteHorizonSlab.closedEmbedding e hTplus).pointMap s hs x := by
      change e.embedding.pointMap s _ x = e.embedding.pointMap s _ x
      rfl
    rw [← hpoint]
    exact hdefect s hs' x

end PoincareMT.M30
