import PoincareMT.Proofs.M64.Sec19_3_Annuli.DouglasMorreyInterface

/-!
# Conformal Gram input for the annular branch-aware interface

The lower M60 branch argument has an algebraic part which is independent of
the sphere source: a nonzero conformal factor makes the manifold differential
injective.  This file transports that part to the annulus.  Harmonicity,
Hopf vanishing, finiteness of the branch set, and the first variation remain
producer inputs; none is asserted here.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

/-- Pointwise weak conformality on the annulus interior. A Hopf/harmonic producer may
discharge this field; the branch adapter below only uses the displayed Gram identity.
Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project
derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
def M64AnnulusConformalGram (A : M64Annulus g c0 c1) : Prop :=
  ∀ p ∈ interior m64AnnulusDomain, ∃ scale : ℝ, 0 ≤ scale ∧
    ∀ v w : TangentSpace (𝓡 2) p,
      g.inner (A.map p)
          (mfderiv (𝓡 2) (𝓡 n) A.map p v)
          (mfderiv (𝓡 2) (𝓡 n) A.map p w) =
        scale * inner ℝ v w

/-- A nonzero conformal factor gives an injective differential away from the actual
differential-zero set. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp.
447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64Annulus_injective_off_branch_of_conformal
    (A : M64Annulus g c0 c1)
    (hconformal : M64AnnulusConformalGram A)
    {p : LoopPlane} (hp : p ∈ interior m64AnnulusDomain)
    (hbranch : p ∉ m64AnnulusBranchSet A) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 n) A.map p) := by
  let d := mfderiv (𝓡 2) (𝓡 n) A.map p
  let : NormedAddCommGroup (TangentSpace (𝓡 2) p) :=
    inferInstanceAs (NormedAddCommGroup LoopPlane)
  let : InnerProductSpace ℝ (TangentSpace (𝓡 2) p) :=
    inferInstanceAs (InnerProductSpace ℝ LoopPlane)
  obtain ⟨scale, hscale, hpair⟩ := hconformal p hp
  have hscale_pos : 0 < scale := by
    by_contra hnot
    have hscale_zero : scale = 0 := le_antisymm (not_lt.mp hnot) hscale
    apply hbranch
    change p ∈ interior m64AnnulusDomain ∧ d = 0
    refine ⟨hp, ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    by_contra hv
    have hpos := g.pos (A.map p) (d v) hv
    have hzero := hpair v v
    rw [hscale_zero, zero_mul] at hzero
    rw [hzero] at hpos
    exact (lt_irrefl 0 hpos)
  intro v w hvw
  apply sub_eq_zero.mp
  have hzero : d (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  by_contra hne
  have hinner : 0 < inner ℝ (v - w) (v - w) :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr (by
      intro h
      apply hne
      simp [h]))
  have hpair_sub := hpair (v - w) (v - w)
  have hprod_zero : scale * inner ℝ (v - w) (v - w) = 0 := by
    rw [← hpair_sub, hzero]
    simp
  exact (ne_of_gt (mul_pos hscale_pos hinner)) hprod_zero

/-- The explicit annular producer package needed by the branch-aware first-variation
interface. In particular, finiteness and stationarity are kept as independent geometric
inputs rather than inferred from conformality. Source: Morgan--Tian (2007), Lemma 19.15 and
Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
structure M64AnnulusConformalBranchAwareCertificate
    (A : M64Annulus g c0 c1) : Prop where
  regularity : M64AnnulusRegularityCertificate A
  area_stationary : M64AnnulusAreaStationary A
  finite_branch_set : (m64AnnulusBranchSet A).Finite
  conformal_gram : M64AnnulusConformalGram A

/-- Convert the explicit conformal Gram package into the existing branch-aware
first-variation certificate. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16,
pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem M64AnnulusConformalBranchAwareCertificate.toBranchAware
    {A : M64Annulus g c0 c1}
    (C : M64AnnulusConformalBranchAwareCertificate A) :
    M64AnnulusBranchAwareFirstVariationCertificate A :=
  { regularity := C.regularity
    area_stationary := C.area_stationary
    finite_branch_set := C.finite_branch_set
    injective_off_branch_set := fun _p hp hbranch =>
      m64Annulus_injective_off_branch_of_conformal A C.conformal_gram hp hbranch }

end

end PoincareMT
