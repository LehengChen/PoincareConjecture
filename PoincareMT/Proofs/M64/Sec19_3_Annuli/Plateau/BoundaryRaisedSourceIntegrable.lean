import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryRaisedSourceBounds
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrability of the actual raised boundary source

Bounded inverse coefficients multiply the original L1 source. Their bounded
derivatives applied to the L2 weak columns pair with the L2 flux. This
proves L1 integrability of the literal raised source before using its weak
equation. Source: Lemaire 1982, p. 102; raised-source derivation.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff ENNReal

namespace PoincareMT

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64BoundaryRaisedSourceIntegrable_bilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64BoundaryRaisedSourceIntegrable_bilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The literal raised source is integrable on the actual coordinate domain, using its
compact target range and the original L2 columns and L1 source. Source: the M64
raised-boundary-source derivation. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449;
local boundary analysis. Project derivation:
`proof-work/tasks/M64/derivations/2026-09-26-raised-boundary-source.md`. -/
theorem m64BoundaryRaisedSource_integrable
    {S : Set LoopPlane} (hS : MeasurableSet S)
    {U K : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hG : ContDiffOn ℝ ∞ G U)
    (hpos : ∀ z ∈ U, ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 → 0 < G z v v)
    (w : Fin 2 → ℝ)
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)} (hu : ContinuousOn u S)
    (hmap : MapsTo u S K)
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)}
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict S))
    {b : Fin n → LoopPlane → ℝ} (hb : ∀ j, IntegrableOn (b j) S) :
    ∀ k, IntegrableOn
      (fun p => m64BoundaryRaisedSource G w (u p) (fun i => V i p) (fun j => b j p) k) S := by
  let A : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun k j z =>
    (m64BoundaryMetricInverse (G z) (EuclideanSpace.single k 1)) j
  have hA (k j : Fin n) : ContDiffOn ℝ ∞ (A k j) U :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn
      ((m64BoundaryMetricInverse_smooth hG hpos).clm_apply contDiffOn_const)
  obtain ⟨L, _, hL⟩ := m64BoundaryMetric_inverse_coefficient_bounds hU hK hKU hG hpos
  have hGM : MemLp (fun p => G (u p)) ⊤ (volume.restrict S) :=
    memLp_top_of_bound (((hG.continuousOn.mono hKU).comp hu hmap
      ).aestronglyMeasurable hS) L (by
        filter_upwards [ae_restrict_mem hS] with p hp
        exact (hL (u p) (hmap hp)).1)
  have hAM (k j : Fin n) : MemLp (fun p => A k j (u p)) ⊤ (volume.restrict S) :=
    memLp_top_of_bound ((((hA k j).continuousOn.mono hKU).comp hu hmap
      ).aestronglyMeasurable hS) L (by
        filter_upwards [ae_restrict_mem hS] with p hp
        exact (hL (u p) (hmap hp)).2.2 k j |>.1)
  have hDM (k j : Fin n) : MemLp (fun p => fderiv ℝ (A k j) (u p)) ⊤
      (volume.restrict S) :=
    memLp_top_of_bound (((((hA k j).continuousOn_fderiv_of_isOpen hU (by simp)
      ).mono hKU).comp hu hmap).aestronglyMeasurable hS) L (by
        filter_upwards [ae_restrict_mem hS] with p hp
        exact (hL (u p) (hmap hp)).2.2 k j |>.2)
  have hflux (j : Fin n) (i : Fin 2) : MemLp
      (fun p => w i * G (u p) (V i p) (EuclideanSpace.single j 1)) 2
        (volume.restrict S) := by
    have hGV := (ContinuousLinearMap.apply ℝ
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) («E» := EuclideanSpace ℝ (Fin n))).memLp_of_bilin
        (p := 2) (q := ⊤) 2 (hV i) hGM
    exact (((ContinuousLinearMap.apply ℝ ℝ («E» := EuclideanSpace ℝ (Fin n)))
      (EuclideanSpace.single j 1)).comp_memLp' hGV).const_mul _
  have hDV (k j : Fin n) (i : Fin 2) : MemLp
      (fun p => fderiv ℝ (A k j) (u p) (V i p)) 2 (volume.restrict S) :=
    (ContinuousLinearMap.apply ℝ ℝ («E» := EuclideanSpace ℝ (Fin n))).memLp_of_bilin
      (p := 2) (q := ⊤) 2 (hV i) (hDM k j)
  intro k
  have hfirst : IntegrableOn (fun p => ∑ j : Fin n, b j p * A k j (u p)) S := by
    apply integrable_finsetSum
    intro j _
    exact memLp_one_iff_integrable.mp
      ((hAM k j).mul' (memLp_one_iff_integrable.mpr (hb j)))
  have hsecond : IntegrableOn (fun p => ∑ i : Fin 2, ∑ j : Fin n,
      (w i * G (u p) (V i p) (EuclideanSpace.single j 1)) *
        fderiv ℝ (A k j) (u p) (V i p)) S := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    exact (hflux j i).integrable_mul (hDV k j i)
  exact hfirst.sub hsecond

end PoincareMT
