import PoincareMT.Proofs.M65.Sec19_5_Limits.Lemma19_4.ManifoldSecondFundamental
import PoincareMT.Proofs.M65.Sec19_5_Limits.Lemma19_4.ConformalBilinearTrace
import PoincareMT.Proofs.M65.Sec19_5_Limits.Lemma19_4.ChartMetricRealization

/-!
# Actual harmonic tension and the genuine metric trace

The ambient coordinate metric is constructed from the given metric. The
actual connection defect is bilinear, and the genuine source orthonormal
trace equals the reciprocal conformal factor times the frozen tension.
Source: Morgan--Tian Lemma 19.2, printed p. 438;
M65 derivation 24, twelfth stage.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareMT

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {h : RiemannianMetric 2 LoopPlane}

/-- For a genuine smooth disk and conformal source metric, the actual
metric trace of the connection defect is the reciprocal conformal factor
times the actual harmonic tension. The conformal factor is automatically
positive because the source metric is Riemannian.
Source: MT Lemma 19.2, p. 438; derivation 24, twelfth stage. -/
theorem m65PlaneSecondFundamentalForm_metricTrace
    (D : LeviCivitaData g) (Ds : LeviCivitaData h)
    {f : LoopPlane → M} {U : Set LoopPlane} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f U) {x : LoopPlane} (hx : x ∈ U)
    {c : LoopPlane → ℝ}
    (hconf : ∀ᶠ y in 𝓝 x, ∀ i j : Fin 2,
      h.inner y (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ j) = if i = j then c y else 0) :
    (∑ i, m65PlaneSecondFundamentalForm D Ds f x
      (h.orthonormalBasis x i) (h.orthonormalBasis x i)) =
      (c x)⁻¹ • m65PlaneTension D f x := by
  obtain ⟨gE, DE, hE⟩ := m65Exists_chartMetric g (f x)
  let q := chartAt (EuclideanSpace ℝ (Fin n)) (f x)
  have hmetric : ∀ᶠ y in 𝓝 (q (f x)), ∀ a b : EuclideanSpace ℝ (Fin n),
      gE.inner y a b = g.inner (q.symm y)
        (mfderiv (𝓡 n) (𝓡 n) q.symm y a)
        (mfderiv (𝓡 n) (𝓡 n) q.symm y b) := by
    simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, q] using hE
  let BC := M65Gauss.secondFundamentalFormBilinear DE Ds (q ∘ f) x
  let L := (mfderiv (𝓡 n) (𝓡 n) q.symm (q (f x))).toLinearMap
  let B : LoopPlane →ₗ[ℝ] LoopPlane →ₗ[ℝ] TangentSpace (𝓡 n) (f x) :=
    LinearMap.mk₂ ℝ (fun u v => L (BC u v))
      (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  have hB (u v : LoopPlane) : B u v = m65PlaneSecondFundamentalForm D Ds f x u v := by
    exact (m65PlaneSecondFundamentalForm_chart D Ds DE (f x) hU hf hx
      (mem_chart_source (EuclideanSpace ℝ (Fin n)) (f x)) hmetric u v).symm
  have hc : 0 < c x := by
    have hz := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.ne_zero (0 : Fin 2)
    have hp := h.pos x (EuclideanSpace.basisFun (Fin 2) ℝ 0) hz
    have he := hconf.self_of_nhds (0 : Fin 2) 0
    simpa only [ite_true] using hp.trans_eq he
  have ht := M65Gauss.bilinear_conformal_trace x B hc hconf.self_of_nhds
  simp_rw [hB] at ht
  rw [m65PlaneSecondFundamentalForm_euclideanTrace D Ds f hconf] at ht
  exact ht

end PoincareMT
