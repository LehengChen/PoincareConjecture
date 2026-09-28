import PoincareMT.Proofs.M62.Sec19_1_PullbackCurvature
import PoincareMT.Proofs.M04.FlowTensorRegularity
import PoincareMT.Proofs.M04.ConnectionVariation

/-!
# Actual connection coefficients in real time

The actual spatial chart Christoffel coefficients are jointly smooth, and
their fixed-metric time pairing is the covariant Ricci variation. These
are the moving-connection inputs to the spatial form of MT2015Correction
Lemma 0.2, pp. 4-6. See `2026-09-20-moving-connection.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareMT.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

/-- Actual chart connection coefficients are jointly smooth through the
included time endpoints; MT2015Correction Lemma 0.2, pp. 4-6. -/
theorem flow_chartChristoffel_smooth [T2Space M]
    (F : RicciFlow n M J) (p : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        M04.shiChartChristoffel (F.connection z.1)
          (chartAt (EuclideanSpace ℝ (Fin n)) p) z.2)
      (J ×ˢ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) := by
  let E := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let e := chartAt E p
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart
  have hi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
  rw [contDiffOn_clm_apply]
  intro u
  rw [contDiffOn_clm_apply]
  intro v
  apply (contDiffOn_piLp 2).mpr
  intro i
  let L : (z : ℝ × M) → TangentSpace (𝓡 n) z.2 →L[ℝ] ℝ := fun z =>
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).comp
      (mfderiv (𝓡 n) (𝓡 n) e z.2)
  have hL : ∀ (V : Set M), IsOpen V → V ⊆ e.source →
      ∀ (Z : (y : M) → TangentSpace (𝓡 n) y),
        ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞ (T% Z) V →
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
          (fun z : ℝ × M => L z (Z z.2)) (J ×ˢ V) := by
    intro V hV hVU Z hZ
    have hs : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun z : ℝ × M => M04.shiChartCoordinate e i z.2) (J ×ˢ V) :=
      ((M04.shiChartCoordinate_smooth he i).mono hVU).comp contMDiffOn_snd
        (fun z hz => hz.2)
    apply (M04.contMDiffOn_mvfderiv_spatial hV hs hZ).congr
    intro z hz
    change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i)
      (mfderiv (𝓡 n) (𝓡 n) e z.2 (Z z.2)) =
      mvfderiv (𝓡 n) (M04.shiChartCoordinate e i) z.2 (Z z.2)
    exact (M04.shiChartCoordinate_derivative he (hVU hz.2) i (Z z.2)).symm
  have hconn := M04.contMDiffOn_flow_linear_connection F e.open_source L hL
    (M04.shiChartField_smooth he hi u) (M04.shiChartField_smooth he hi v)
  have hparam : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun z : ℝ × E => (z.1, e.symm z.2)) (J ×ˢ e.target) :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      (hi.comp contDiff_snd.contMDiff.contMDiffOn (fun z hz => hz.2))
  have hcomp := hconn.comp hparam (fun z hz => ⟨hz.1, e.map_target hz.2⟩)
  apply hcomp.contDiffOn.congr
  intro z hz
  change (M04.shiChartChristoffel (F.connection z.1) e z.2 u v) i =
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i)
      (mfderiv (𝓡 n) (𝓡 n) e (e.symm z.2)
      ((F.connection z.1).connection (M04.shiChartField e v) (e.symm z.2)
        (M04.shiChartField e u (e.symm z.2))))
  rw [M04.shiChartChristoffel_connection (F.connection z.1) he hi hz.2,
    ← M04.shiChartField_at_inverse he hi hz.2]
  rfl

/-- Real-time differentiation of the actual connection, with the metric
and test fields fixed; MT2015Correction Lemma 0.2, pp. 4-6. -/
theorem hasDerivAt_flow_chartChristoffel_pair [T2Space M]
    (F : RicciFlow n M J) (p : M) {t : ℝ} {y : M}
    (ht : t ∈ interior J)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (u v w : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt
      (fun r => (F.metric t).inner y
        (PoincareMT.Proofs.M09.chartVectorField p
          (M04.shiChartChristoffel (F.connection r)
            (chartAt (EuclideanSpace ℝ (Fin n)) p)
            ((chartAt (EuclideanSpace ℝ (Fin n)) p) y) u v) y)
        (PoincareMT.Proofs.M09.chartVectorField p w y))
      (let X := PoincareMT.Proofs.M09.chartVectorField p u y;
       let Y := PoincareMT.Proofs.M09.chartVectorField p v y;
       let Z := PoincareMT.Proofs.M09.chartVectorField p w y;
       let D := F.connection t;
       -D.covariantTensorDerivative D.ricciEvaluation y ![X, Y, Z] -
         D.covariantTensorDerivative D.ricciEvaluation y ![Y, X, Z] +
         D.covariantTensorDerivative D.ricciEvaluation y ![Z, X, Y]) t := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := chartAt E p
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart
  have hi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
  have hconn (r : ℝ) :
      PoincareMT.Proofs.M09.chartVectorField p
        (M04.shiChartChristoffel (F.connection r) e (e y) u v) y =
      (F.connection r).connection (PoincareMT.Proofs.M09.chartVectorField p v) y
        (PoincareMT.Proofs.M09.chartVectorField p u y) := by
    apply ((mdifferentiable_chart (I := 𝓡 n) p).mfderiv hy).injective
    change mfderiv (𝓡 n) (𝓡 n) e y _ = mfderiv (𝓡 n) (𝓡 n) e y _
    erw [M04.shiChartField_duality he hi hy]
    have h := M04.shiChartChristoffel_connection (F.connection r) he hi
      (e.map_source hy) u v
    rw [← M04.shiChartField_at_inverse he hi (e.map_source hy), e.left_inv hy] at h
    exact h
  have h := M04.hasDerivAt_connection_pairing F e.open_source
    (PoincareMT.Proofs.M09.chartVectorField_smooth p u)
    (PoincareMT.Proofs.M09.chartVectorField_smooth p v)
    (PoincareMT.Proofs.M09.chartVectorField_smooth p w) ht hy
  apply h.congr_of_eventuallyEq
  filter_upwards [] with r
  rw [hconn]

end PoincareMT.M62
