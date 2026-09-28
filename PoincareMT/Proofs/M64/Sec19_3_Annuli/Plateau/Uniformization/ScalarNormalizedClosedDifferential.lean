import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverBoundaryDifferential

/-!
# Closed-strip differential of the normalized scalar covering map

The scalar H3 boundary construction and the conjugate extension give a
genuine derivative on the closed polar strip.  This file records the
corresponding product derivative for the normalized potential/conjugate map,
including both radial boundary lines.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace PoincareMT.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

/-- The normalized potential/conjugate covering map has its actual closed-strip derivative.
The second column is scaled by the inverse conjugate period, exactly as in
`scalarNormalizedCoverMap`. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the
explicit project construction is recorded in
`proof-work/tasks/M64/reports/2026-09-25-scalar-normalized-closed-differential.md`. -/
theorem exists_scalarNormalizedCoverMap_closed_differential
    {H : Plane → ℝ} {V : Cover → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    (P : ℝ) (hdeck : ∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P) :
    ∃ (J : Plane → Plane →L[ℝ] ℝ) (K : ℝ≥0) (W : Cover → ℝ),
      ContinuousOn J (closure scalarAnnulus) ∧
      EqOn J (fderiv ℝ H) scalarAnnulus ∧
      (∀ x ∈ closure scalarAnnulus, x ∉ scalarAnnulus → J x ≠ 0) ∧
      LipschitzWith K W ∧ EqOn W V scalarCoverStrip ∧
      ContinuousOn (scalarCoverFormOfDifferential g J) (closure scalarCoverStrip) ∧
      (∀ z ∈ closure scalarCoverStrip, W (z + (0, 1)) = W z + P) ∧
      ∀ z ∈ closure scalarCoverStrip,
        HasFDerivWithinAt (scalarNormalizedCoverMap H W P)
          ((scalarCoverPotentialDifferential J z).prod
            (P⁻¹ • scalarCoverFormOfDifferential g J z))
          (closure scalarCoverStrip) z := by
  obtain ⟨J, K, W, hJc, hJeq, hJn, hW, hWV, hBc, hperiod, hWder⟩ :=
    exists_scalar_conjugate_closed_differential D hHc hHs hlap hinner houter hdV P hdeck
  refine ⟨J, K, W, hJc, hJeq, hJn, hW, hWV, hBc, hperiod, ?_⟩
  intro z hz
  have hHder := scalarCoverPotential_hasFDerivWithinAt_closure
    hHc hHs hJc hJeq hz
  have hVder := (hWder z hz).const_smul P⁻¹
  have hprod := hHder.prodMk hVder
  change HasFDerivWithinAt
    (fun y => ((H ∘ scalarCoverMap) y, P⁻¹ • W y))
    ((scalarCoverPotentialDifferential J z).prod
      (P⁻¹ • scalarCoverFormOfDifferential g J z))
    (closure scalarCoverStrip) z at hprod
  change HasFDerivWithinAt
    (fun y => (H (scalarCoverMap y), W y / P))
    ((scalarCoverPotentialDifferential J z).prod
      (P⁻¹ • scalarCoverFormOfDifferential g J z))
    (closure scalarCoverStrip) z
  convert hprod using 1
  funext y
  congr 1
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

end PoincareMT.M64Uniformization
