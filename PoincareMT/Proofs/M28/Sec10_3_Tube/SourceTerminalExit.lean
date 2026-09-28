import PoincareMT.Proofs.M28.Mathlib.FrontierCrossing
import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceTubeData

/-!
# The terminal source-neck exit

The retained path ends in one active source neck.  If its forward endpoint
has already left that neck's closure, the compact first-exit argument gives a
literal frontier time and keeps the preceding path segment in the same
carrier.  This is the short terminal walk used by Claim 10.6.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.M28

variable {epsilon C A D₀ D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
  {S : CounterexampleNeckSegment E}

/-- A retained path segment in an active neck has a genuine first exit before
the original path endpoint, provided that endpoint is outside the neck
closure.  The conclusion is independent of the chosen orientation of the
active neck. -/
theorem exists_source_neck_forward_exit
    (T : SourceTubeData S) {i : ℤ} (_hi : i ∈ T.chain.shape.active)
    {a : ℝ} (ha : a ∈ Icc S.lower S.upper)
    (hpath : MapsTo S.path (Icc a S.upper) (T.chain.neck i).carrier)
    (hend : S.path 1 ∉ closure (T.chain.neck i).carrier) :
    ∃ v ∈ Ioo a 1, S.path v ∈ frontier (T.chain.neck i).carrier ∧
      MapsTo S.path (Ico a v) (T.chain.neck i).carrier := by
  have haa : a < 1 := lt_of_le_of_lt ha.2 S.upper_lt_one
  have hstart : S.path a ∈ (T.chain.neck i).carrier :=
    hpath (left_mem_Icc.mpr ha.2)
  have hγ : ContinuousOn S.path (Icc a 1) :=
    S.path_smooth.continuousOn.mono
      (Icc_subset_Icc (S.lower_pos.le.trans ha.1) le_rfl)
  obtain ⟨v, hv, hvfront, hvpath⟩ :=
    ContinuousOn.exists_first_frontier_before_endpoint
      (T.chain.neck i).carrier_open haa hγ hstart hend
  refine ⟨v, hv, hvfront, ?_⟩
  intro t ht
  by_cases htu : t ≤ S.upper
  · exact hpath ⟨ht.1, htu⟩
  · exact hvpath ht

end PoincareMT.M28
