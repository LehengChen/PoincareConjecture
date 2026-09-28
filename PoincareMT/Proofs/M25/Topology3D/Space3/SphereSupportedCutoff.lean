import PoincareMT.Proofs.M25.Topology3D.Services
import PoincareMT.Proofs.M25.Topology3D.Space3.FieldLocalization

/-!
# Native sphere cutoffs for replacement collars

Supported local maps extend smoothly on the native sphere-time strip.
Two disjoint open patches have smooth weights with disjoint closed
supports and sum at most one. Source: G1-G2 of the independently reviewed
2026-09-22 weighted-collar implementation inventory, for Hatcher,
Notes on Basic 3-Manifold Topology, Theorem 1.1 and Lemma 1.3, pp. 1-3.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Manifold Topology BigOperators

namespace PoincareMT.M25.Topology3D

/-- A smooth native weight with closed support inside the candidate
patch extends the weighted candidate smoothly over the entire strip.
Weighted-collar inventory G1; Hatcher, Theorem 1.1 and Lemma 1.3, pp. 1-3. -/
theorem contMDiffOn_sphere_supported_smul
    (w : UnitTwoSphere → ℝ) (hw : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ w)
    {V : Set UnitTwoSphere} (hV : IsOpen V) (hs : tsupport w ⊆ V)
    (f : UnitTwoSphere × ℝ → E3) {eta : ℝ}
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ f
      (V ×ˢ Ioo (-eta) eta)) :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞
      (fun z => w z.1 • f z) (univ ×ˢ Ioo (-eta) eta) := by
  intro z hz
  by_cases hzw : z.1 ∈ tsupport w
  · have hzf : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ f z :=
      hf.contMDiffAt ((hV.prod isOpen_Ioo).mem_nhds ⟨hs hzw, hz.2⟩)
    exact (((hw.comp contMDiff_fst).contMDiffAt).smul hzf).contMDiffWithinAt
  · have hzero : (fun y : UnitTwoSphere × ℝ => w y.1 • f y) =ᶠ[𝓝 z]
        fun _ => (0 : E3) := by
      have hnear : ∀ᶠ y : UnitTwoSphere × ℝ in 𝓝 z, y.1 ∉ tsupport w :=
        continuous_fst.continuousAt.eventually
          ((isClosed_tsupport w).isOpen_compl.mem_nhds hzw)
      filter_upwards [hnear] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    exact (contMDiffAt_const.congr_of_eventuallyEq hzero).contMDiffWithinAt

/-- Two disjoint native open patches have weights equal to one near
their compact prescribed sets, with disjoint closed supports and sum
at most one. Weighted-collar inventory G2; Hatcher, Lemma 1.3, pp. 2-3. -/
theorem exists_two_sphere_cutoffs
    (K V : Fin 2 → Set UnitTwoSphere)
    (hK : ∀ i, IsCompact (K i)) (hV : ∀ i, IsOpen (V i))
    (hKV : ∀ i, K i ⊆ V i) (hdis : Disjoint (V 0) (V 1)) :
    ∃ w : Fin 2 → UnitTwoSphere → ℝ,
      (∀ i, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (w i)) ∧
      (∀ i, tsupport (w i) ⊆ V i) ∧
      (∀ i, ∀ᶠ p in 𝓝ˢ (K i), w i p = 1) ∧
      (∀ i p, w i p ∈ Icc 0 1) ∧
      Disjoint (tsupport (w 0)) (tsupport (w 1)) ∧
      ∀ p, (∑ i : Fin 2, w i p) ≤ 1 := by
  classical
  have hcutoff (i : Fin 2) : ∃ w : UnitTwoSphere → ℝ,
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ w ∧ tsupport w ⊆ V i ∧
      (∀ᶠ p in 𝓝ˢ (K i), w p = 1) ∧ ∀ p, w p ∈ Icc 0 1 := by
    obtain ⟨L, hL, hKL, hLV⟩ := exists_compact_between (hK i) (hV i) (hKV i)
    obtain ⟨w, hnear, hzero, hrange⟩ :=
      exists_contMDiffMap_one_nhds_of_subset_interior (𝓡 2)
        (hK i).isClosed hKL (n := (⊤ : ℕ∞))
    have hs : Function.support w ⊆ L := by
      intro p hp
      by_contra hpL
      exact hp (hzero p hpL)
    exact ⟨w, w.contMDiff, (closure_minimal hs hL.isClosed).trans hLV,
      hnear, hrange⟩
  choose w hw hs hnear hrange using hcutoff
  have hd : Disjoint (tsupport (w 0)) (tsupport (w 1)) :=
    hdis.mono (hs 0) (hs 1)
  refine ⟨w, hw, hs, hnear, hrange, hd, ?_⟩
  intro p
  rw [Fin.sum_univ_two]
  by_cases hp : w 0 p = 0
  · simpa only [hp, zero_add] using (hrange 1 p).2
  · have hp1 : w 1 p = 0 := image_eq_zero_of_notMem_tsupport
      (Set.disjoint_left.mp hd (subset_tsupport (w 0) hp))
    simpa only [hp1, add_zero] using (hrange 0 p).2

end PoincareMT.M25.Topology3D
