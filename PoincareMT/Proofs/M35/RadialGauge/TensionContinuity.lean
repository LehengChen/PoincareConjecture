import PoincareMT.Proofs.M35.Sec12_4_Uniqueness.HarmonicTension
import PoincareMT.Proofs.M35.Uniqueness.Heat.RawPrincipalExtension
import Mathlib.Topology.ClusterPt

/-!
# Actual smoothness of the harmonic tension at the tip

Morgan-Tian Proposition 12.26, pp. 320-322. The genuine map Hessian
uses smooth retained connection coefficients and actual map jets. Its
trace in one fixed Euclidean basis is therefore smooth without choosing
a varying orthonormal frame. Punctured radial identities consequently
extend to the actual tip by continuity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareMT.M35.RadialGauge

open Uniqueness Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

/-- The retained covariant map Hessian has smooth actual components
in constant Euclidean directions, including at the origin. -/
theorem mapCovariantHessian_contDiff_apply
    {g b : RiemannianMetric n V} (D : LeviCivitaData g) (B : LeviCivitaData b)
    {F : V → V} (hF : ContDiff ℝ ∞ F) (u v : V) :
    ContDiff ℝ ∞ (fun x => mapCovariantHessian D B F x u v) := by
  have hd := (contDiff_infty_iff_fderiv.mp hF).2
  have hdd := (contDiff_infty_iff_fderiv.mp hd).2
  have h1 := (hdd.clm_apply (contDiff_const (c := u))).clm_apply (contDiff_const (c := v))
  have h2 := (((rawConnectionCoefficient_contDiff B).comp hF).clm_apply
    (hd.clm_apply (contDiff_const (c := u)))).clm_apply
      (hd.clm_apply (contDiff_const (c := v)))
  have h3 := hd.clm_apply
    (((rawConnectionCoefficient_contDiff D).clm_apply (contDiff_const (c := u))).clm_apply
      (contDiff_const (c := v)))
  exact (h1.add h2).sub h3

/-- The actual harmonic tension is smooth in a fixed inverse-Gram trace,
so no regularity of an arbitrary orthonormal-basis choice is used. -/
theorem mapTension_contDiff
    {g b : RiemannianMetric n V} (D : LeviCivitaData g) (B : LeviCivitaData b)
    {F : V → V} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (mapTension D B F) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have he (i : Fin n) : e i = EuclideanSpace.single i (1 : ℝ) :=
    EuclideanSpace.basisFun_apply (Fin n) ℝ i
  have htrace : mapTension D B F = fun x => ∑ i, ∑ j,
      (rawCoordinateGram g x)⁻¹ i j • mapCovariantHessian D B F x (e i) (e j) := by
    funext x
    rw [mapTension_eq_inverse_gram D B F x e.toBasis]
    have hgram : Matrix.of (fun i j => g.inner x (e.toBasis i) (e.toBasis j)) =
        rawCoordinateGram g x := by
      ext i j
      simp only [Matrix.of_apply, OrthonormalBasis.coe_toBasis, he, rawCoordinateGram]
    rw [hgram]
    rfl
  rw [htrace]
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (raw_inverseGram_entry_contDiff g i j).smul
    (mapCovariantHessian_contDiff_apply D B hF (e i) (e j))

/-- A punctured-space identity for the actual tension extends through
the tip when the supplied actual velocity is continuous there. -/
theorem mapTension_eq_of_punctured
    {g b : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g) (B : LeviCivitaData b)
    {F W : StandardCapSpace → StandardCapSpace} (hF : ContDiff ℝ ∞ F) (hV : Continuous W)
    (heq : ∀ x ≠ 0, mapTension D B F x = W x) : mapTension D B F = W := by
  apply Continuous.ext_on (dense_compl_singleton (0 : StandardCapSpace))
    (mapTension_contDiff D B hF).continuous hV
  intro x hx
  exact heq x (by simpa only [mem_compl_iff, mem_singleton_iff] using hx)

end PoincareMT.M35.RadialGauge
