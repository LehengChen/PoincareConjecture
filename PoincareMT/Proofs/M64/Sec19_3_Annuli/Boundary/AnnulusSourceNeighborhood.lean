import PoincareMT.Proofs.M64.Sec19_3_Annuli.Boundary.AnnulusSourceCoordinates

/-! Actual closed half disks inside a prescribed annular coordinate
neighborhood. The center lies on a radial face away from the angular cut.
Source: MT Lemma 19.15, pp. 447-449; M64 finite collar derivation. -/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter Metric
open scoped Topology

namespace PoincareMT.M64

/-- A genuine boundary neighborhood contains a sufficiently small closed half disk in the
actual modulus-scaled source coordinate. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
theorem annulusBoundarySource_radius {r x : ℝ} (hr : 0 < r)
    (hx : x ∈ Ioo 0 curvePeriod) (upper : Bool) {O : Set LoopPlane}
    (hO : IsOpen O) (ha : annulusPoint x (if upper then 1 else 0) ∈ O) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧ r * R < x ∧ x + r * R < curvePeriod ∧
      MapsTo (annulusBoundarySource r hr.ne' upper x)
        (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) O := by
  have hcont : Continuous (annulusBoundarySource r hr.ne' upper x) :=
    continuous_const.add (annulusBoundaryLinear r hr.ne' upper).continuous
  have hcenter : annulusBoundarySource r hr.ne' upper x 0 ∈ O := by
    simpa only [annulusBoundarySource, map_zero, add_zero] using ha
  obtain ⟨e, he, hesub⟩ := nhds_basis_closedBall.mem_iff.mp
    (hcont.continuousAt.eventually (hO.mem_nhds hcenter))
  let R := min (min e 1) (min (x / r) ((curvePeriod - x) / r)) / 2
  have hmin : 0 < min (min e 1) (min (x / r) ((curvePeriod - x) / r)) :=
    lt_min (lt_min he zero_lt_one) (lt_min (div_pos hx.1 hr) (div_pos (sub_pos.mpr hx.2) hr))
  have hR : 0 < R := half_pos hmin
  have hsmall : R < min (min e 1) (min (x / r) ((curvePeriod - x) / r)) :=
    half_lt_self hmin
  have hRe : R < e := hsmall.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hR1 : R < 1 := hsmall.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hRx : R < x / r := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hRP : R < (curvePeriod - x) / r :=
    hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨R, hR, hR1, ?_, ?_, fun z hz => hesub (closedBall_subset_closedBall hRe.le hz.1)⟩
  · simpa only [mul_comm] using (lt_div_iff₀ hr).mp hRx
  · have h := (lt_div_iff₀ hr).mp hRP
    nlinarith

end PoincareMT.M64
