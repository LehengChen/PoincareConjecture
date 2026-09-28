import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.ClassicalCircleCurrent

/-!
# Positive ramp current survives actual classical weak extraction

The current of every classical free ramp annulus is at least one period.
Its literal linear observation converges by strong L2 values and weak L2
columns, so the limit retains this positive current. The source maps in
this theorem are explicitly globally C1; a weak phase supplier is not
silently inferred from the existing classical covering theorem.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareMT.M64

open Poincare.Analysis.Sobolev.WeakCompactness

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

/-- A classical free ramp sequence retains a positive actual circle current in its
strong-value weak-column limit. Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-25-free-label-compactness.md`. -/
theorem classical_free_ramp_current_weak_limit
    (P : M62.CircleProductData F circumference) (t : ℝ) (gamma : ℝ → P.charts.Point)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) (hramp : M63IsRampAt P gamma t)
    (e : P.charts.Point → E) (he : ContMDiff (𝓡 (n + 1)) (𝓡 m) 1 e)
    (R : E →L[ℝ] LoopPlane) (hR : ∀ q, R (e q) = planarCircleObservation q.2)
    (sigma : ℕ → M64PeriodicDegreeOneLift) (f : ℕ → LoopPlane → P.charts.Point)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 (n + 1)) 1 (f j))
    (hper : ∀ j x s, f j (annulusPoint (x + curvePeriod) s) = f j (annulusPoint x s))
    (hlower : ∀ j x, f j (annulusPoint x 0) = gamma ((sigma j).map x))
    (u v : ℕ → Lp E 2 mu) (U V : Lp E 2 mu)
    (hvalue : ∀ j, ∀ᵐ p ∂mu, u j p = e (f j p))
    (hcolumn : ∀ j, ∀ᵐ p ∂mu, v j p = fderiv ℝ (e ∘ f j) p e0)
    (hu : Tendsto u atTop (𝓝 U)) (hv : WeakConverges v V)
    {C : ℝ} (hC : ∀ j, ‖v j‖ ≤ C) :
    curvePeriod ≤ ∫ p in S, planarCircleCurrent (R (U p)) (R (V p)) := by
  have hder (j : ℕ) (p : LoopPlane) :
      R (fderiv ℝ (e ∘ f j) p e0) =
        fderiv ℝ (fun q => planarCircleObservation (f j q).2) p e0 := by
    have hobs : DifferentiableAt ℝ (e ∘ f j) p :=
      (contMDiff_iff_contDiff.mp (he.comp (hf j))).differentiable (by simp) p
    have heq : R ∘ (e ∘ f j) = fun q => planarCircleObservation (f j q).2 :=
      funext fun q => hR (f j q)
    rw [← heq, fderiv_comp p R.differentiableAt hobs, R.fderiv]
    rfl
  have hbound (j : ℕ) : curvePeriod ≤
      ∫ p in S, planarCircleCurrent (R (u j p)) (R (v j p)) := by
    have heq : (∫ p in S, planarCircleCurrent (R (u j p)) (R (v j p))) =
        ∫ p in S, planarCircleCurrent (planarCircleObservation (f j p).2)
          (fderiv ℝ (fun q => planarCircleObservation (f j q).2) p e0) := by
      apply integral_congr_ae
      filter_upwards [hvalue j, hcolumn j] with p hp hq
      rw [hp, hq, hR, hder]
    obtain ⟨degree, hd, hcurrent, -⟩ := classical_free_ramp_current_positive
      P t gamma hgamma hperiod hramp (sigma j) (f j) (hf j) (hper j) (hlower j)
    rw [heq, hcurrent]
    have hd1 : (1 : ℝ) ≤ degree := by exact_mod_cast Nat.succ_le_of_lt hd
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd1
      (show (0 : ℝ) ≤ curvePeriod by unfold curvePeriod; positivity)
  exact ge_of_tendsto (planarProjection_current_integral_tendsto R hu hv hC)
    (Eventually.of_forall hbound)

end PoincareMT.M64
