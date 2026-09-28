import PoincareMT.Proofs.M28.Thm5_6_PartialLimits.Geometry.Parabolic.CommonCollar

/-!
# Compact source-ball covers from finite limit-chart families

The shared export supplies a compact exhaustion stage for each radius below
the cutoff.  If one actual family of coordinate pieces covers every such
stage in the limit carrier, and the source maps are the corresponding actual
embeddings, the finite compact-cover field of the parabolic application
follows.  No cross-index distance limit or transition estimate is assumed.
-/

set_option autoImplicit false

open Set Filter Metric
open scoped Manifold ContDiff Topology
open Poincare.Gluing

universe u

namespace PoincareMT.M28

variable {M : ℕ → Type u}
  [∀ k, TopologicalSpace (M k)]
  [∀ k, T2Space (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)]
  {tau : ℝ} {F : ∀ k, RicciFlow 3 (M k) (Icc (-tau) 0)}
  {p : ∀ k, M k} {A : ℝ}

/-- Finite compact pieces in one fixed family of limit charts convert the
actual shared collar into the eventual finite source-ball cover required by
`SelectedParabolicApplicationData.compact_cover`.  The source maps are
explicitly tied to `E.limit.embedding`; they are not an abstract target
sequence.
-/
theorem PartialLimitWindowExport.exists_eventual_compact_cover_of_chart_family
    (E : PartialLimitWindowExport F p A)
    {U : ℕ → Set (EuclideanSpace ℝ (Fin 3))}
    (chart : ∀ i, Piece U i → E.limit.limitCarrier.carrier)
    (s : ℕ → Finset ℕ) (K : ℕ → ∀ i, Set (Piece U i))
    (hK : ∀ l i, i ∈ s l → IsCompact (K l i))
    (hcover : ∀ l, E.limit.exhaustion l ⊆
      ⋃ i ∈ s l, chart i '' K l i)
    (e : ∀ k i, Piece U i → M (E.limit.subsequence k))
    (hsource : ∀ k i z, e k i z = E.limit.embedding k (chart i z))
    (i₀ : ℕ) (z₀ : Piece U i₀)
    (hbase : chart i₀ z₀ = E.limit.base) :
    ∀ B : ℝ, 0 < B → B < A → ∃ l : Finset ℕ,
      ∃ K' : ∀ i, Set (Piece U i),
        (∀ i ∈ l, IsCompact (K' i)) ∧
        ∀ᶠ k in atTop,
          ((F (E.limit.subsequence k)).metric 0).ball
              (e k i₀ z₀) B ⊆
            ⋃ i ∈ l, e k i '' K' i := by
  intro B hB hBA
  obtain ⟨lstage, _, hball⟩ := E.exists_eventual_compact_collar hB hBA
  refine ⟨s lstage, K lstage, ?_, ?_⟩
  · exact hK lstage
  · filter_upwards [hball] with k hk x hx
    have hcenter : e k i₀ z₀ = p (E.limit.subsequence k) := by
      rw [hsource k i₀ z₀, hbase, E.limit.base_preserving k]
    have hx' : x ∈ ((F (E.limit.subsequence k)).metric 0).ball
        (p (E.limit.subsequence k)) B := by
      simpa only [hcenter] using hx
    obtain ⟨y, hy, hxy⟩ := hk hx'
    have hycover := hcover lstage hy
    obtain ⟨i, hi, z, hz, hzy⟩ := mem_iUnion₂.mp hycover
    refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, z, hz, ?_⟩⟩
    calc
      e k i z = E.limit.embedding k (chart i z) := hsource k i z
      _ = E.limit.embedding k y := congrArg (E.limit.embedding k) hzy
      _ = x := hxy

end PoincareMT.M28
