import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusEnergy
import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusClass
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Modulus stationarity of an attained weak free limit

The compact-interval weak minimizer is minimized over the cylinder modulus as
well as over maps.  At an interior modulus, differentiating the explicit
weighted column formula gives the scalar weighted-conformality identity.  This
is an integrated identity; pointwise Hopf regularity remains a separate
analytic step.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareMT.M64

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin m)

/-- Differentiating an attained interior modulus minimum gives the integrated weighted
column balance. Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-25-free-label-compactness.md`. -/
theorem observedWeakAnnulus_modulus_stationarity_of_interior_minimum
    {e : M → E} {c0 c1 : ℝ → M}
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K)
    {lo hi r : ℝ} (hlo : 0 < lo) (hrlo : lo < r) (hrhi : r < hi)
    (hmin : ∀ s ∈ Icc lo hi,
      A.weightedEnergy B r ≤ A.weightedEnergy B s) :
    r * (∫ p in interior m64AnnulusDomain,
      B (A.map p) (A.column 0 p) (A.column 0 p)) / 2 =
      r⁻¹ * (∫ p in interior m64AnnulusDomain,
        B (A.map p) (A.column 1 p) (A.column 1 p)) / 2 := by
  let I0 : ℝ := ∫ p in interior m64AnnulusDomain,
    B (A.map p) (A.column 0 p) (A.column 0 p)
  let I1 : ℝ := ∫ p in interior m64AnnulusDomain,
    B (A.map p) (A.column 1 p) (A.column 1 p)
  let F : ℝ → ℝ := fun s => (s / 2) * I0 + (s⁻¹ / 2) * I1
  have henergy (s : ℝ) : A.weightedEnergy B s = F s := by
    rw [A.weightedEnergy_eq_column_integrals B hB hei hb s]
  have hlocal : IsLocalMin F r := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hrlo, hrhi⟩] with s hs
    rw [← henergy r, ← henergy s]
    exact hmin s ⟨hs.1.le, hs.2.le⟩
  have hrpos : 0 < r := lt_trans hlo hrlo
  have hderiv : HasDerivAt F
      ((1 / 2 : ℝ) * I0 + (-(r⁻¹) ^ 2 / 2) * I1) r := by
    convert! (((hasDerivAt_id r).div_const 2).mul_const I0).add
      (((hasDerivAt_inv hrpos.ne').div_const 2).mul_const I1) using 1
    all_goals ring
  have hzero : (1 / 2 : ℝ) * I0 + (-(r⁻¹) ^ 2 / 2) * I1 = 0 :=
    hlocal.hasDerivAt_eq_zero hderiv
  dsimp only [I0, I1] at hzero ⊢
  field_simp [hrpos.ne'] at hzero ⊢
  nlinarith

end PoincareMT.M64
