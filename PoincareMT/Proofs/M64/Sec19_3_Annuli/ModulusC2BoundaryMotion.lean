import PoincareMT.Proofs.M63.Sec19_1_LocalFlow.ArbitraryC2IntrinsicRegularity
import PoincareMT.Proofs.M63.Sec19_1_LocalFlow.FixedRelabelingAssembly
import PoincareMT.Proofs.M63.Sec19_1_LocalFlow.SmoothUpgradeFixedLabels
import PoincareMT.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry

/-!
# Actual smooth local motions of anchored C2 shrinking curves

A smooth reference slice removes the fixed C2 label obstruction by the
closed M63 relabeling and smooth-anchor theorems. The resulting local
motion has the supplied curve's literal labels and actual curvature
velocity. This supplies the boundary construction for MT2007 Lemma 19.15,
pp. 447-449, without promoting arbitrary C2 labels to smooth labels.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

/-- A smooth actual anchor slice upgrades the original C2 labels on a closed positive-time
slab containing that slice in its interior. Source: Morgan--Tian (2007), Lemma 19.15 and
Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64C2ShrinkingCurve_smooth_near_smooth_slice
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b)
    (hct : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c x t)) :
    ∃ tau s : ℝ, a < tau ∧ tau < t ∧ t < s ∧ s < b ∧
      M63SmoothShrinkingCurveOn F c (Icc tau s) := by
  let : Nonempty M := ⟨c 0 t⟩
  have hi := M63.c2ShrinkingCurve_intrinsic_regularity F isCompact_univ
    (ht.1.trans ht.2) le_rfl (Or.inl rfl) hc
  let tau := (a + t) / 2
  let s := (t + b) / 2
  have hat : a < tau := by dsimp only [tau]; linarith [ht.1]
  have htt : tau < t := by dsimp only [tau]; linarith [ht.1]
  have hts : t < s := by dsimp only [s]; linarith [ht.2]
  have hsb : s < b := by dsimp only [s]; linarith [ht.2]
  have hslab : Icc tau s ⊆ Icc a b := Icc_subset_Icc hat.le hsb.le
  obtain ⟨phi, d, hphi, _hbij, _hpos, _hshift, hd, hdslices, hrel⟩ :=
    M63.exists_fixed_smooth_relabeling F isCompact_univ hc hi hat (htt.trans hts) hslab
  obtain ⟨N, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨U, rho, hU, heU, hrho, hrhoe, _hmin, _huniq⟩ :=
    M63.exists_smooth_compact_embedded_retraction e hemb he hinj
  have hanchor : t ∈ Icc tau s := ⟨htt.le, hts.le⟩
  obtain ⟨_hphis, hsmooth⟩ :=
    M63.smoothShrinkingCurve_of_fixed_relabeling_and_smooth_slice
      F he hU heU hrho hrhoe hanchor (M63.c2_restrict hc hslab) hd
        hct (hdslices t hanchor) hphi.continuous hrel
  exact ⟨tau, s, hat, htt, hts, hsb, hsmooth⟩

/-- The actual C2 shrinking curve supplies a smooth centered boundary motion once its
reference slice is smooth. Periodicity and curvature velocity come from the supplied curve,
not from a motion certificate. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16,
pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64C2ShrinkingCurve_exists_centered_motion_of_smooth_slice
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b)
    (hct : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c x t)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ f : ℝ → ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (fun q => f q.1 q.2)
        (Ioo (-epsilon) epsilon ×ˢ univ) ∧
      (∀ z x, f z (x + curvePeriod) = f z x) ∧
      (∀ z ∈ Ioo (-epsilon) epsilon, ∀ x, f z x = c x (t + z)) ∧
      ∀ x, curveVelocity (fun z => f z x) 0 = m62CurvatureVector F c t x := by
  classical
  obtain ⟨tau, s, hat, htt, hts, hsb, hsmooth⟩ :=
    m64C2ShrinkingCurve_smooth_near_smooth_slice F hc ht hct
  let epsilon := min (t - tau) (s - t) / 2
  have hepsilon : 0 < epsilon :=
    half_pos (lt_min (sub_pos.mpr htt) (sub_pos.mpr hts))
  have hshift (z : ℝ) (hz : z ∈ Ioo (-epsilon) epsilon) : t + z ∈ Ioo tau s := by
    dsimp only [epsilon] at hz
    constructor <;>
      linarith [min_le_left (t - tau) (s - t), min_le_right (t - tau) (s - t),
        hz.1, hz.2]
  have hshift_full (z : ℝ) (hz : z ∈ Ioo (-epsilon) epsilon) : t + z ∈ Icc a b :=
    ⟨(hat.trans (hshift z hz).1).le, ((hshift z hz).2.trans hsb).le⟩
  let f : ℝ → ℝ → M := fun z x => c x (if t + z ∈ Icc a b then t + z else t)
  have hagree (z : ℝ) (hz : z ∈ Ioo (-epsilon) epsilon) (x : ℝ) :
      f z x = c x (t + z) := by simp only [f, if_pos (hshift_full z hz)]
  have hjoint : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => c q.1 q.2) (univ ×ˢ Ioo tau s) := by
    simpa only [interior_Icc] using hsmooth.2
  have hraw : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => c q.2 (t + q.1)) (Ioo (-epsilon) epsilon ×ˢ univ) :=
    hjoint.comp (contDiff_snd.prodMk
      (contDiff_const.add contDiff_fst)).contMDiff.contMDiffOn
        (fun q hq => ⟨mem_univ _, hshift q.1 hq.1⟩)
  have hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (fun q => f q.1 q.2)
      (Ioo (-epsilon) epsilon ×ˢ univ) :=
    hraw.congr (fun q hq => hagree q.1 hq.1 q.2)
  have hperiodic (z x : ℝ) : f z (x + curvePeriod) = f z x := by
    unfold f
    split_ifs with hz
    · exact hc.periodic _ hz x
    · exact hc.periodic t (Ioo_subset_Icc_self ht) x
  refine ⟨epsilon, hepsilon, f, hf, hperiodic, hagree, ?_⟩
  intro x
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have heq : (fun z => f z x) =ᶠ[𝓝 (0 : ℝ)] fun z => c x (t + z) := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with z hz
    exact hagree z hz x
  have hvelocity : curveVelocity (fun z => f z x) 0 =
      curveVelocity (fun z => c x (t + z)) 0 :=
    congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1)
      (heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n))
  have htime : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun z => c x z) t :=
    (hjoint.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (x, t) ∈ univ ×ˢ Ioo tau s from ⟨mem_univ _, htt, hts⟩))).comp t
        (contDiffAt_const.prodMk contDiffAt_id).contMDiffAt
  have hchain := M63.curveVelocity_comp
    (gamma := fun z => c x z) (phi := fun z => t + z)
    (by simpa only [add_zero] using htime.mdifferentiableAt (by simp))
    ((hasDerivAt_id (0 : ℝ)).const_add t)
  have hchain' : curveVelocity (n := n) (fun z => c x (t + z)) 0 =
      curveVelocity (n := n) (fun z => c x z) (t + 0) := by
    simpa only [one_smul] using hchain
  have ht0 := congrArg (fun s : ℝ =>
    (curveVelocity (n := n) (fun z => c x z) s : EuclideanSpace ℝ (Fin n))) (add_zero t)
  exact hvelocity.trans (hchain'.trans (ht0.trans
    (hc.equation t (by simpa only [interior_Icc] using ht) x)))

end PoincareMT
