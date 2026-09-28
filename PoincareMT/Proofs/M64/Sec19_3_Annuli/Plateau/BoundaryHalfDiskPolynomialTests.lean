import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.DiskGreenGeometry
import PoincareMT.Definitions.Ch19.AnnulusComparison

/-!
# Polynomial Cartesian tests for a lower half-disk shell

The radial cosine moments are realized by polynomial vector fields.  This
avoids an angle inverse and all derivatives of a norm.  The next transport
lemma combines these fields with the observed annulus Green identities.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff

namespace PoincareMT

open Proofs.M58

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- The quarter-turn of a Cartesian point. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; project boundary constructions in
`proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`, Polynomial Shell
Derivation. -/
def m64HalfDiskJ (q : LoopPlane) : LoopPlane := !₂[-q 1, q 0]

/-- The polynomial radial variable used by the shell tests. Source: Morgan--Tian (2007),
Lemma 19.15, pp. 447-449; project boundary constructions in
`proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`, Polynomial Shell
Derivation. -/
def m64HalfDiskQuadratic (q : LoopPlane) : ℝ := q 0 ^ 2 + q 1 ^ 2

/-- The divergence-free polynomial test field. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; project boundary constructions in
`proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`, Polynomial Shell
Derivation. -/
def m64HalfDiskPolynomialTestZero (psi : ℝ → ℝ) (q : LoopPlane) : LoopPlane :=
  psi (m64HalfDiskQuadratic q) • m64HalfDiskJ q

/-- The polynomial test field whose divergence is the vertical source. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; project boundary constructions in
`proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`, Polynomial Shell
Derivation. -/
def m64HalfDiskPolynomialTestOne (psi : ℝ → ℝ) (q : LoopPlane) : LoopPlane :=
  (psi (m64HalfDiskQuadratic q) * q 0) • m64HalfDiskJ q

/-- Translate the polynomial tests to a shell centered at `x` on the lower edge of the
annulus. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project boundary
constructions in `proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`,
Polynomial Shell Derivation. -/
def m64HalfDiskPolynomialTestZeroAt (x : ℝ) (psi : ℝ → ℝ) (p : LoopPlane) : LoopPlane :=
  m64HalfDiskPolynomialTestZero psi (p - !₂[x, 0])

/-- The second actual polynomial vector test is translated to the original lower-edge
center. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project boundary
constructions in `proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`,
Polynomial Shell Derivation. -/
def m64HalfDiskPolynomialTestOneAt (x : ℝ) (psi : ℝ → ℝ) (p : LoopPlane) : LoopPlane :=
  m64HalfDiskPolynomialTestOne psi (p - !₂[x, 0])

private theorem m64HalfDisk_contDiff_coord (i : Fin 2) :
    ContDiff ℝ ∞ (fun q : LoopPlane => q i) := by
  change ContDiff ℝ ∞ (EuclideanSpace.proj (𝕜 := ℝ) i)
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

private theorem m64HalfDisk_contDiff_J :
    ContDiff ℝ ∞ m64HalfDiskJ := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · exact (m64HalfDisk_contDiff_coord 1).neg
  · exact m64HalfDisk_contDiff_coord 0

private theorem m64HalfDisk_contDiff_quadratic :
    ContDiff ℝ ∞ m64HalfDiskQuadratic := by
  exact ((m64HalfDisk_contDiff_coord 0).pow 2).add
    ((m64HalfDisk_contDiff_coord 1).pow 2)

/-- A C1 radial coefficient gives two genuine C1 Cartesian polynomial test fields. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project boundary constructions in
`proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`, Polynomial Shell
Derivation. -/
theorem m64HalfDisk_polynomialTest_contDiff
    {psi : ℝ → ℝ} (hpsi : ContDiff ℝ 1 psi) :
    ContDiff ℝ 1 (m64HalfDiskPolynomialTestZero psi) ∧
      ContDiff ℝ 1 (m64HalfDiskPolynomialTestOne psi) := by
  have hrad : ContDiff ℝ 1 m64HalfDiskQuadratic :=
    m64HalfDisk_contDiff_quadratic.of_le (by simp)
  have hJ : ContDiff ℝ 1 m64HalfDiskJ :=
    m64HalfDisk_contDiff_J.of_le (by simp)
  have hzero : ContDiff ℝ 1 (fun q : LoopPlane =>
      psi (m64HalfDiskQuadratic q)) := hpsi.comp hrad
  have hcoord : ContDiff ℝ 1 (fun q : LoopPlane => q 0) :=
    (m64HalfDisk_contDiff_coord 0).of_le (by simp)
  exact ⟨hzero.smul hJ, (hzero.mul hcoord).smul hJ⟩

private theorem m64HalfDisk_quadratic_hasFDerivAt (q : LoopPlane) :
    HasFDerivAt m64HalfDiskQuadratic
      ((2 * q 0) • (EuclideanSpace.proj (𝕜 := ℝ) 0) +
        (2 * q 1) • (EuclideanSpace.proj (𝕜 := ℝ) 1)) q := by
  convert! (((EuclideanSpace.proj (𝕜 := ℝ) 0).hasFDerivAt (x := q)).pow 2).add
    (((EuclideanSpace.proj (𝕜 := ℝ) 1).hasFDerivAt (x := q)).pow 2) using 1
  ext v
  simp only [smul_apply, smul_eq_mul, add_apply, EuclideanSpace.coe_proj]
  ring

/-- The actual first polynomial test is divergence free. Source: Morgan--Tian (2007), Lemma
19.15, pp. 447-449; project boundary constructions in
`proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`, Polynomial Shell
Derivation. -/
theorem m64HalfDisk_polynomialTestZero_divergence
    {psi : ℝ → ℝ} (hpsi : ContDiff ℝ 1 psi) (q : LoopPlane) :
    fderiv ℝ (fun z => m64HalfDiskPolynomialTestZero psi z 0) q
        (EuclideanSpace.single 0 1) +
      fderiv ℝ (fun z => m64HalfDiskPolynomialTestZero psi z 1) q
        (EuclideanSpace.single 1 1) = 0 := by
  have ha := (hpsi.differentiable (by simp) (m64HalfDiskQuadratic q)).hasFDerivAt.comp
    q (m64HalfDisk_quadratic_hasFDerivAt q)
  have h0 := ha.neg.mul ((EuclideanSpace.proj (𝕜 := ℝ) 1).hasFDerivAt (x := q))
  have h1 := ha.mul ((EuclideanSpace.proj (𝕜 := ℝ) 0).hasFDerivAt (x := q))
  have heq0 : (fun z : LoopPlane => m64HalfDiskPolynomialTestZero psi z 0) =
      (fun z => -(psi (m64HalfDiskQuadratic z) * z 1)) := by
    funext z
    simp [m64HalfDiskPolynomialTestZero, m64HalfDiskJ, smul_eq_mul]
  have heq1 : (fun z : LoopPlane => m64HalfDiskPolynomialTestZero psi z 1) =
      (fun z => psi (m64HalfDiskQuadratic z) * z 0) := by
    funext z
    simp [m64HalfDiskPolynomialTestZero, m64HalfDiskJ, smul_eq_mul]
  rw [heq0, heq1]
  have hfun0 : (fun z : LoopPlane => -(psi (m64HalfDiskQuadratic z) * z 1)) =
      (-psi ∘ m64HalfDiskQuadratic * ⇑(EuclideanSpace.proj (𝕜 := ℝ) 1)) := by
    funext z
    simp only [Pi.mul_apply, EuclideanSpace.coe_proj]
    simp only [Function.comp_def]
    simp only [Pi.neg_apply]
    ring
  have hfun1 : (fun z : LoopPlane => psi (m64HalfDiskQuadratic z) * z 0) =
      (psi ∘ m64HalfDiskQuadratic * ⇑(EuclideanSpace.proj (𝕜 := ℝ) 0)) := by
    funext z
    simp only [Function.comp_apply, Pi.mul_apply, EuclideanSpace.coe_proj]
  rw [congrArg (fun f => fderiv ℝ f q) hfun0,
    congrArg (fun f => fderiv ℝ f q) hfun1, h0.fderiv, h1.fderiv]
  simp [ContinuousLinearMap.comp_apply]
  ring

/-- The actual second polynomial test has the displayed negative vertical source. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project boundary constructions in
`proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`, Polynomial Shell
Derivation. -/
theorem m64HalfDisk_polynomialTestOne_divergence
    {psi : ℝ → ℝ} (hpsi : ContDiff ℝ 1 psi) (q : LoopPlane) :
    fderiv ℝ (fun z => m64HalfDiskPolynomialTestOne psi z 0) q
        (EuclideanSpace.single 0 1) +
      fderiv ℝ (fun z => m64HalfDiskPolynomialTestOne psi z 1) q
        (EuclideanSpace.single 1 1) =
      -(psi (m64HalfDiskQuadratic q) * q 1) := by
  have ha := (hpsi.differentiable (by simp) (m64HalfDiskQuadratic q)).hasFDerivAt.comp
    q (m64HalfDisk_quadratic_hasFDerivAt q)
  have ha0 := ha.mul ((EuclideanSpace.proj (𝕜 := ℝ) 0).hasFDerivAt (x := q))
  have h00 := ha0.neg.mul ((EuclideanSpace.proj (𝕜 := ℝ) 1).hasFDerivAt (x := q))
  have h11 := ha0.mul ((EuclideanSpace.proj (𝕜 := ℝ) 0).hasFDerivAt (x := q))
  have heq0 : (fun z : LoopPlane => m64HalfDiskPolynomialTestOne psi z 0) =
      (fun z => -((psi (m64HalfDiskQuadratic z) * z 0) * z 1)) := by
    funext z
    simp [m64HalfDiskPolynomialTestOne, m64HalfDiskJ, smul_eq_mul]
  have heq1 : (fun z : LoopPlane => m64HalfDiskPolynomialTestOne psi z 1) =
      (fun z => (psi (m64HalfDiskQuadratic z) * z 0) * z 0) := by
    funext z
    simp [m64HalfDiskPolynomialTestOne, m64HalfDiskJ, smul_eq_mul]
  have hfun0 : (fun z : LoopPlane => -((psi (m64HalfDiskQuadratic z) * z 0) * z 1)) =
      (-((psi ∘ m64HalfDiskQuadratic) * ⇑(EuclideanSpace.proj (𝕜 := ℝ) 0)) *
        ⇑(EuclideanSpace.proj (𝕜 := ℝ) 1)) := by
    funext z
    simp only [Pi.mul_apply, EuclideanSpace.coe_proj, Function.comp_def, Pi.neg_apply]
    ring
  have hfun1 : (fun z : LoopPlane => (psi (m64HalfDiskQuadratic z) * z 0) * z 0) =
      ((psi ∘ m64HalfDiskQuadratic * ⇑(EuclideanSpace.proj (𝕜 := ℝ) 0)) *
        ⇑(EuclideanSpace.proj (𝕜 := ℝ) 0)) := by
    funext z
    simp only [Pi.mul_apply, EuclideanSpace.coe_proj, Function.comp_def]
  rw [heq0, heq1,
    congrArg (fun f => fderiv ℝ f q) hfun0,
    congrArg (fun f => fderiv ℝ f q) hfun1, h00.fderiv, h11.fderiv]
  simp [ContinuousLinearMap.comp_apply]
  ring

/-- The actual Cartesian polynomial fields equal the displayed angular vectors with their
exact radial factors. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project
boundary constructions in
`proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`, Polynomial Shell
Derivation. -/
theorem m64HalfDisk_polynomialTest_polar
    {psi : ℝ → ℝ} (r theta : ℝ) :
    m64HalfDiskPolynomialTestZero psi (r • angularPoint theta) =
        (psi (r ^ 2) * r) • angularVector theta ∧
      m64HalfDiskPolynomialTestOne psi (r • angularPoint theta) =
        (psi (r ^ 2) * r ^ 2 * Real.cos theta) • angularVector theta := by
  have hq : m64HalfDiskQuadratic (r • angularPoint theta) = r ^ 2 := by
    change (r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2 = r ^ 2
    nlinarith [Real.sin_sq_add_cos_sq theta]
  have hJ : m64HalfDiskJ (r • angularPoint theta) = r • angularVector theta := by
    ext i
    fin_cases i <;> simp [m64HalfDiskJ, angularPoint, angularVector]
  constructor
  · rw [m64HalfDiskPolynomialTestZero, hq, hJ, smul_smul]
  · rw [m64HalfDiskPolynomialTestOne, hq, hJ, smul_smul]
    congr 1
    change psi (r ^ 2) * (r * Real.cos theta) * r = _
    ring

/-- The actual polynomial fields have the displayed lower-axis traces. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; project boundary constructions in
`proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`, Polynomial Shell
Derivation. -/
theorem m64HalfDisk_polynomialTest_axis
    {psi : ℝ → ℝ} (x : ℝ) :
    (m64HalfDiskPolynomialTestZero psi (!₂[x, 0] : LoopPlane)) 1 = psi (x ^ 2) * x ∧
      (m64HalfDiskPolynomialTestOne psi (!₂[x, 0] : LoopPlane)) 1 =
        psi (x ^ 2) * x ^ 2 := by
  constructor
  · simp [m64HalfDiskPolynomialTestZero, m64HalfDiskJ, m64HalfDiskQuadratic,
      smul_eq_mul]
  · simp [m64HalfDiskPolynomialTestOne, m64HalfDiskJ, m64HalfDiskQuadratic,
      smul_eq_mul]
    ring

/-- Translation preserves C1 regularity of both actual polynomial test fields. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project boundary constructions in
`proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`, Polynomial Shell
Derivation. -/
theorem m64HalfDisk_polynomialTestAt_contDiff
    {psi : ℝ → ℝ} (hpsi : ContDiff ℝ 1 psi) (x : ℝ) :
    ContDiff ℝ 1 (m64HalfDiskPolynomialTestZeroAt x psi) ∧
      ContDiff ℝ 1 (m64HalfDiskPolynomialTestOneAt x psi) := by
  have hshift : ContDiff ℝ 1 (fun p : LoopPlane => p - !₂[x, 0]) := by
    fun_prop
  obtain ⟨hzero, hone⟩ := m64HalfDisk_polynomialTest_contDiff hpsi
  exact ⟨hzero.comp hshift, hone.comp hshift⟩

/-- The translated first actual polynomial field remains divergence free. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project boundary constructions in
`proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`, Polynomial Shell
Derivation. -/
theorem m64HalfDisk_polynomialTestAt_divergence_zero
    {psi : ℝ → ℝ} (hpsi : ContDiff ℝ 1 psi) (x : ℝ) (p : LoopPlane) :
    fderiv ℝ (fun z => m64HalfDiskPolynomialTestZeroAt x psi z 0) p
        (EuclideanSpace.single 0 1) +
      fderiv ℝ (fun z => m64HalfDiskPolynomialTestZeroAt x psi z 1) p
        (EuclideanSpace.single 1 1) = 0 := by
  change fderiv ℝ (fun z : LoopPlane =>
      m64HalfDiskPolynomialTestZero psi (z - !₂[x, 0]) 0) p
        (EuclideanSpace.single 0 1) +
      fderiv ℝ (fun z : LoopPlane =>
        m64HalfDiskPolynomialTestZero psi (z - !₂[x, 0]) 1) p
        (EuclideanSpace.single 1 1) = 0
  have h0 := fderiv_comp_sub (𝕜 := ℝ)
    (f := fun z : LoopPlane => m64HalfDiskPolynomialTestZero psi z 0)
    (!₂[x, 0] : LoopPlane) (x := p)
  have h1 := fderiv_comp_sub (𝕜 := ℝ)
    (f := fun z : LoopPlane => m64HalfDiskPolynomialTestZero psi z 1)
    (!₂[x, 0] : LoopPlane) (x := p)
  rw [h0, h1]
  exact m64HalfDisk_polynomialTestZero_divergence hpsi (p - !₂[x, 0])

/-- The translated second actual polynomial field retains its exact vertical divergence.
Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project boundary constructions in
`proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`, Polynomial Shell
Derivation. -/
theorem m64HalfDisk_polynomialTestAt_divergence_one
    {psi : ℝ → ℝ} (hpsi : ContDiff ℝ 1 psi) (x : ℝ) (p : LoopPlane) :
    fderiv ℝ (fun z => m64HalfDiskPolynomialTestOneAt x psi z 0) p
        (EuclideanSpace.single 0 1) +
      fderiv ℝ (fun z => m64HalfDiskPolynomialTestOneAt x psi z 1) p
        (EuclideanSpace.single 1 1) =
      -(psi (m64HalfDiskQuadratic (p - !₂[x, 0])) * (p - !₂[x, 0]) 1) := by
  change fderiv ℝ (fun z : LoopPlane =>
      m64HalfDiskPolynomialTestOne psi (z - !₂[x, 0]) 0) p
        (EuclideanSpace.single 0 1) +
      fderiv ℝ (fun z : LoopPlane =>
        m64HalfDiskPolynomialTestOne psi (z - !₂[x, 0]) 1) p
          (EuclideanSpace.single 1 1) = _
  have h0 := fderiv_comp_sub (𝕜 := ℝ)
    (f := fun z : LoopPlane => m64HalfDiskPolynomialTestOne psi z 0)
    (!₂[x, 0] : LoopPlane) (x := p)
  have h1 := fderiv_comp_sub (𝕜 := ℝ)
    (f := fun z : LoopPlane => m64HalfDiskPolynomialTestOne psi z 1)
    (!₂[x, 0] : LoopPlane) (x := p)
  rw [h0, h1]
  exact m64HalfDisk_polynomialTestOne_divergence hpsi (p - !₂[x, 0])

/-- The translated actual polynomial fields have the required traces on the original lower
annular edge. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project boundary
constructions in `proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`,
Polynomial Shell Derivation. -/
theorem m64HalfDisk_polynomialTestAt_axis
    {psi : ℝ → ℝ} (x r : ℝ) :
    (m64HalfDiskPolynomialTestZeroAt x psi (annulusPoint (x + r) 0)) 1 =
        psi (r ^ 2) * r ∧
      (m64HalfDiskPolynomialTestOneAt x psi (annulusPoint (x + r) 0)) 1 =
        psi (r ^ 2) * r ^ 2 := by
  have hpoint : annulusPoint (x + r) 0 - !₂[x, 0] = !₂[r, 0] := by
    ext i
    fin_cases i <;> simp [annulusPoint]
  rw [m64HalfDiskPolynomialTestZeroAt, m64HalfDiskPolynomialTestOneAt, hpoint]
  exact m64HalfDisk_polynomialTest_axis (psi := psi) r

/-- Support in the actual squared-radius interval makes both polynomial fields vanish
outside that interval. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project
boundary constructions in
`proof-work/tasks/M64/reviews/2026-09-27-round1-plateau-boundary-phase.md`, Polynomial Shell
Derivation. -/
theorem m64HalfDisk_polynomialTest_eq_zero
    {psi : ℝ → ℝ} {s : Set ℝ} (hs : Function.support psi ⊆ s)
    {q : LoopPlane} (hq : m64HalfDiskQuadratic q ∉ s) :
    m64HalfDiskPolynomialTestZero psi q = 0 ∧
      m64HalfDiskPolynomialTestOne psi q = 0 := by
  have hp : psi (m64HalfDiskQuadratic q) = 0 := by
    by_contra hp
    exact hq (hs hp)
  simp [m64HalfDiskPolynomialTestZero, m64HalfDiskPolynomialTestOne, hp]

end PoincareMT
