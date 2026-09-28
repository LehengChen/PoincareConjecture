import PoincareMT.Proofs.M35.RadialGauge.TensionDomainPullback
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# The actual first two jets after intrinsic-coordinate composition

Morgan-Tian Proposition 12.26, pp. 320-322. The ordinary first and
second chain rules transfer joint C1 regularity of the actual spatial
jets to the actual composition. This is used for the original raw gauge
and its genuine native harmonic tension, without assuming joint C2
regularity before the time equation supplies it.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Set
open scoped ContDiff

namespace PoincareMT.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

/-- The actual first differential of the composition is jointly C1
from the stated actual map and differential regularity. -/
theorem composed_map_fderiv_joint_c1
    {F H : ℝ → V → V} {J : Set ℝ}
    (hFs : ∀ t ∈ J, ContDiff ℝ ∞ (F t))
    (hHs : ∀ t ∈ J, ContDiff ℝ ∞ (H t))
    (hH : ContDiffOn ℝ 1 (Function.uncurry H) (J ×ˢ univ))
    (hDF : ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (F p.1) p.2) (J ×ˢ univ))
    (hDH : ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (H p.1) p.2) (J ×ˢ univ)) :
    ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (F p.1 ∘ H p.1) p.2) (J ×ˢ univ) := by
  have hDFH := hDF.comp (contDiffOn_fst.prodMk hH) (fun _ hp => ⟨hp.1, mem_univ _⟩)
  apply (hDFH.clm_comp hDH).congr
  intro p hp
  exact fderiv_comp p.2 ((hFs p.1 hp.1).differentiable (by simp) (H p.1 p.2))
    ((hHs p.1 hp.1).differentiable (by simp) p.2)

/-- The actual second differential of the composition has the needed
joint C1 regularity from the actual first two spatial jets. -/
theorem composed_map_hessian_joint_c1
    {F H : ℝ → V → V} {J : Set ℝ}
    (hFs : ∀ t ∈ J, ContDiff ℝ ∞ (F t))
    (hHs : ∀ t ∈ J, ContDiff ℝ ∞ (H t))
    (hH : ContDiffOn ℝ 1 (Function.uncurry H) (J ×ˢ univ))
    (hDF : ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (F p.1) p.2) (J ×ˢ univ))
    (hDH : ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (H p.1) p.2) (J ×ˢ univ))
    (hDDF : ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (fderiv ℝ (F p.1)) p.2)
      (J ×ˢ univ))
    (hDDH : ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (fderiv ℝ (H p.1)) p.2)
      (J ×ˢ univ)) :
    ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (fderiv ℝ (F p.1 ∘ H p.1)) p.2)
      (J ×ˢ univ) := by
  have hDFH := hDF.comp (contDiffOn_fst.prodMk hH) (fun _ hp => ⟨hp.1, mem_univ _⟩)
  have hDDFH := hDDF.comp (contDiffOn_fst.prodMk hH) (fun _ hp => ⟨hp.1, mem_univ _⟩)
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  have hv := hDH.clm_apply (contDiffOn_const (c := v))
  have hw := hDH.clm_apply (contDiffOn_const (c := w))
  have hdd := (hDDH.clm_apply (contDiffOn_const (c := v))).clm_apply (contDiffOn_const (c := w))
  apply (((hDDFH.clm_apply hv).clm_apply hw).add (hDFH.clm_apply hdd)).congr
  intro p hp
  exact hessian_comp_apply (hFs p.1 hp.1) (hHs p.1 hp.1) p.2 v w

end PoincareMT.M35.RadialGauge
