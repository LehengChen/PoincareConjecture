import PoincareMT.Proofs.M47.TerminalCommonIntervalCoherence
import PoincareMT.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckSpatialMap

/-!
# Exact original cross maps throughout their common history

The actual zero-time inverse identifies the original cylinders at all
included past times. Differentiation on its open source retains both
metric slots. MT Theorem 5.11; original-coherence.md, B11a-b.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

/-- The literal terminal cross map gives exact past point and two-slot
metric identities in the same selected regular history. -/
theorem terminalCommonInterval_original_cross_coherence
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {C D : GeneralizedSliceCarrier.{u}}
    {origin Q a : ℝ} {I J : Set ℝ} {U : Set C.carrier} {V : Set D.carrier}
    (e : GeneralizedFlowCylinder H.generalized C origin Q I U)
    (f : GeneralizedFlowCylinder H.generalized D origin Q J V)
    (hIc : I.OrdConnected) (hJc : J.OrdConnected) (hU : IsOpen U) (hV : IsOpen V)
    (ha : a ≤ 0) (hI : Icc a 0 ⊆ I) (hJ : Icc a 0 ⊆ J) :
    let e0 := e.spatialOpenPartialHomeomorph hU 0 (hI ⟨ha, le_rfl⟩)
    let f0 := f.spatialOpenPartialHomeomorph hV 0 (hJ ⟨ha, le_rfl⟩)
    let T := e0.trans f0.symm
    (∀ x ∈ T.source,
      e.forward a (hI ⟨le_rfl, ha⟩) x = f.forward a (hJ ⟨le_rfl, ha⟩) (T x)) ∧
      ∀ x ∈ T.source, ∀ v w : TangentSpace (𝓡 3) x,
        e.pullbackInner a (hI ⟨le_rfl, ha⟩) x v w =
          f.pullbackInner a (hJ ⟨le_rfl, ha⟩) (T x)
            (mfderiv (𝓡 3) (𝓡 3) T x v) (mfderiv (𝓡 3) (𝓡 3) T x w) := by
  let e0 := e.spatialOpenPartialHomeomorph hU 0 (hI ⟨ha, le_rfl⟩)
  let f0 := f.spatialOpenPartialHomeomorph hV 0 (hJ ⟨ha, le_rfl⟩)
  let T := e0.trans f0.symm
  have hmem (x : C.carrier) (hx : x ∈ T.source) : T x ∈ V := f0.map_target hx.2
  have hmaps (x : C.carrier) (hx : x ∈ T.source) :
      e.forward a (hI ⟨le_rfl, ha⟩) x = f.forward a (hJ ⟨le_rfl, ha⟩) (T x) := by
    apply terminalCommonInterval_generalized_eq H e f hIc hJc hU hV ha hI hJ
      x hx.1 (T x) (hmem x hx)
    apply congrArg (fun y => (⟨origin + 0 / Q, y⟩ : H.generalized.point))
    exact (f0.right_inv hx.2).symm
  have hsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ T T.source :=
    (f.spatialOpenPartialHomeomorph_symm_contMDiffOn hV 0 (hJ ⟨ha, le_rfl⟩)).comp
      ((e.spatialOpenPartialHomeomorph_contMDiffOn hU 0
        (hI ⟨ha, le_rfl⟩)).mono (fun _ hx => hx.1)) (fun _ hx => hx.2)
  refine ⟨hmaps, ?_⟩
  intro x hx v w
  have heq : e.forward a (hI ⟨le_rfl, ha⟩) =ᶠ[𝓝 x]
      f.forward a (hJ ⟨le_rfl, ha⟩) ∘ T := by
    filter_upwards [T.open_source.mem_nhds hx] with y hy
    exact hmaps y hy
  have hf := (f.forward_smooth a (hJ ⟨le_rfl, ha⟩) (T x) (hmem x hx)).contMDiffAt
    (hV.mem_nhds (hmem x hx))
  have hT := (hsmooth x hx).contMDiffAt (T.open_source.mem_nhds hx)
  unfold GeneralizedFlowCylinder.pullbackInner
  rw [heq.self_of_nhds, heq.mfderiv_eq,
    mfderiv_comp x (hf.mdifferentiableAt (by simp)) (hT.mdifferentiableAt (by simp))]
  rfl

end PoincareMT.M47
