import PoincareMT.Proofs.M25.Topology3D.Space3.FieldLocalization
import PoincareMT.Proofs.M25.Topology3D.Space3.CompactField
import PoincareMT.Proofs.M25.Topology3D.Space3.FlowAlgebra

/-!
# Compact localization retaining a family of finite-time tracks

An autonomous field defined near a compact family of tracks extends to
a global compact field without changing those tracks on the closed time
interval. This is the explicit localization used to translate and round
attaching discs in Hatcher, Notes on Basic 3-Manifold Topology, Lemma 1.3,
p. 3. No general isotopy-extension theorem is assumed.
-/

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Topology NNReal

namespace PoincareMT.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {P : Type*} [TopologicalSpace P]

/-- Localizing an autonomous field near a compact family of solution
curves preserves every curve throughout the closed unit time interval. -/
theorem exists_compact_field_tracking {S : Set P} (hS : IsCompact S)
    (γ : ℝ → P → E)
    (hγ : ContinuousOn (fun p : ℝ × P => γ p.1 p.2) (Icc 0 1 ×ˢ S))
    {U : Set E} (hU : IsOpen U)
    (hγU : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ S, γ t x ∈ U)
    (V : E → E) (hV : ContDiffOn ℝ ∞ V U)
    (hder : ∀ x ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s => γ s x) (V (γ t x)) t) :
    ∃ W : E → E, ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧ tsupport W ⊆ U ∧
      ∃ k l : ℝ≥0, ∃ hk : LipschitzWith k W, ∃ hl : ∀ y, ‖W y‖ ≤ l,
        ∀ x ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
          boundedFlow W hk hl (γ 0 x) t = γ t x := by
  let C := (fun p : ℝ × P => γ p.1 p.2) '' (Icc 0 1 ×ˢ S)
  have hC : IsCompact C := (isCompact_Icc.prod hS).image_of_continuousOn hγ
  have hCU : C ⊆ U := by
    rintro y ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    exact hγU t ht x hx
  obtain ⟨W, hW, hWc, hWs, hnear⟩ := exists_compactField_extension hC hU hCU V hV
  obtain ⟨k, l, hk, hl⟩ := compactField_bounds W hW hWc
  refine ⟨W, hW, hWc, hWs, k, l, hk, hl, ?_⟩
  intro x hx
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => γ s x) (W (γ t x)) t := by
    have heq := (eventually_nhdsSet_iff_forall.mp hnear (γ t x)
      ⟨(t, x), ⟨ht, hx⟩, rfl⟩).self_of_nhds
    rw [heq]
    exact hder x hx t ht
  have heq : EqOn (boundedFlow W hk hl (γ 0 x)) (fun s => γ s x) (Icc 0 1) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ y => W y) (s := fun _ => univ) (fun _ _ => hk.lipschitzOnWith)
    · exact fun s _ =>
        (boundedFlow_hasDerivAt W hk hl (γ 0 x) s).continuousAt.continuousWithinAt
    · exact fun s _ => (boundedFlow_hasDerivAt W hk hl (γ 0 x) s).hasDerivWithinAt
    · exact fun _ _ => mem_univ _
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt
    · exact fun _ _ => mem_univ _
    · exact boundedFlow_zero W hk hl (γ 0 x)
  exact fun _ ht => heq ht

end PoincareMT.M25.Topology3D
