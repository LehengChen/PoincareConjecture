import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceWholeNeckBackwardBounds
import PoincareMT.Proofs.M28.Generalized.StrongNeckBufferedPinching
import PoincareMT.Proofs.M28.Mathlib.LogPinching

/-!
# Vanishing original pinching error on the whole-neck source family

The same original physical cylinder supplies logarithmic pinching
through both endpoints of the half-scale window. Its normalized error
vanishes through every later strict source selection.
Source: Morgan--Tian Claim 10.11, p. 255; M28 derivation 126.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily.WholeNeckBackwardData

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  {H : CounterexampleNeckFamily E} {W : CriticalBallSourcePacket H}
  {G : RegularPointedMetricConvergence
    (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
    (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))}
  {sigma : ℕ → ℕ}
  {V : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    EpsilonNeck G.limitMetric}

variable (D : WholeNeckBackwardData H W G sigma V)

/-- Every retained index preserves the original strict order.
Source: Claim 10.11; M28 derivation 126. -/
theorem sourceIndex_strictMono (hsigma : StrictMono sigma) : StrictMono D.sourceIndex :=
  W.high_index_strictMono.comp (G.subsequence_strictMono.comp
    (hsigma.comp (fun _ _ h => Nat.add_lt_add_right h D.offset)))

/-- The original base normalizations still tend to infinity after the
common prefix and strict extractions. Source: Claim 10.11; derivation 126. -/
theorem normalization_tendsto_atTop (hsigma : StrictMono sigma) :
    Tendsto D.normalization atTop atTop :=
  H.base_scalar_tendsto_atTop.comp (D.sourceIndex_strictMono hsigma).tendsto_atTop

/-- The actual original spacetime point corresponding to a tested
buffered source point. Source: Claim 10.11; M28 derivation 126. -/
def originalPoint (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (s : ℝ), s ∈ Icc (-(V.scale ^ 2 / 2)) 0 →
      strongNeckOpen (D.neck k) → (E (D.sourceIndex k + H.shift)).flow.point := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro s hs x
  exact GeneralizedStrongNeck.buffered_global_original_point (D.neck k)
    (D.normalization k) (D.normalization_pos k)
    (V.scale ^ 2 / 2) (D.half_window k) s hs x

/-- The negative part at the original physical point, divided by the
unchanged base scalar. Source: Claim 10.11; M28 derivation 126. -/
def pinchingError (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (s : ℝ), s ∈ Icc (-(V.scale ^ 2 / 2)) 0 →
      strongNeckOpen (D.neck k) → ℝ := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro s hs x
  exact LeviCivitaData.negativeCurvaturePart
    ((E (D.sourceIndex k + H.shift)).flow.connection (D.originalPoint k s hs x).1)
    (D.originalPoint k s hs x).2 / D.normalization k

set_option maxHeartbeats 1200000 in
-- The physical point retains the dependent original slice throughout the limit.
/-- Original logarithmic pinching and a uniform source curvature bound
make the normalized error vanish at arbitrary retained source points.
Source: Claim 10.11; M28 derivation 126. -/
theorem pinchingError_tendsto_zero (P : RicciFlowCurvatureTheory.{u})
    (hsigma : StrictMono sigma) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ K : ℝ, 0 ≤ K →
      (∀ k s, s ∈ Icc (-(V.scale ^ 2 / 2)) 0 →
        ∀ x : strongNeckOpen (D.neck k),
          ((D.sourceFlow k).connection s).curvatureTensorNorm x ≤ K) →
      ∀ (s : ℝ) (hs : s ∈ Icc (-(V.scale ^ 2 / 2)) 0)
        (x : ∀ k, strongNeckOpen (D.neck k)),
        Tendsto (fun k => D.pinchingError k s hs (x k)) atTop (𝓝 0) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro K hK hcurv s hs x
  have ha := half_pos (sq_pos_of_pos V.scale_pos)
  apply Real.tendsto_zero_of_log_pinching (B := 9 * K) (by positivity)
    (D.normalization_tendsto_atTop hsigma)
  · exact Eventually.of_forall fun _ => le_max_right _ _
  · apply Eventually.of_forall
    intro k
    exact GeneralizedStrongNeck.buffered_global_original_scalar_le_of_curvature_bound
      (D.neck k) (D.raw k) (D.normalization k) (D.normalization_pos k) P
      (V.scale ^ 2 / 2) ha (D.half_window k) s hs (x k) (hcurv k s hs (x k))
  · apply Eventually.of_forall
    intro k
    have htime := GeneralizedStrongNeck.buffered_global_original_point_time_mem
      (D.neck k) (D.normalization k) (D.normalization_pos k)
      (V.scale ^ 2 / 2) (D.half_window k) s hs (x k)
    exact ((E (D.sourceIndex k + H.shift)).pinched _ htime
      (D.originalPoint k s hs (x k)).2).2

/-- The original negative-part error controls the actual source plane
tensor on the whole half-scale window. Source: Claim 10.11; derivation 126. -/
theorem sourceFlow_plane_lower (P : RicciFlowCurvatureTheory.{u}) (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (s : ℝ) (hs : s ∈ Icc (-(V.scale ^ 2 / 2)) 0)
      (x : strongNeckOpen (D.neck k)) (v w : TangentSpace (𝓡 3) x),
      -D.pinchingError k s hs x * M04.metricGram ((D.sourceFlow k).metric s) x v w ≤
        ((D.sourceFlow k).connection s).curvatureTensor x v w v w := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro s hs x v w
  exact GeneralizedStrongNeck.buffered_global_flow_plane_lower (D.neck k) (D.raw k)
    (D.normalization k) (D.normalization_pos k) P
    (V.scale ^ 2 / 2) (half_pos (sq_pos_of_pos V.scale_pos))
    (D.half_window k) s hs x v w

/-- The same Gram-weighted error holds after the fixed spatial
pullback on the whole neighborhood. Source: Claim 10.11; derivation 126. -/
theorem fixedFlow_plane_lower (P : RicciFlowCurvatureTheory.{u}) (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (s : ℝ) (hs : s ∈ Icc (-(V.scale ^ 2 / 2)) 0)
      (x : D.fixedDomain) (v w : TangentSpace (𝓡 3) x),
      -D.pinchingError k s hs (D.neckMap k x) *
          M04.metricGram ((D.fixedFlow k).metric s) x v w ≤
        ((D.fixedFlow k).connection s).curvatureTensor x v w v w := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro s hs x v w
  have hread := ((D.fixedFlow k).connection s).curvatureTensor_eq_of_local_isometry
    ((D.sourceFlow k).connection s) isOpen_univ
    (D.neckMap_localDiffeomorph k).contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x) v w v w
  rw [hread]
  exact D.sourceFlow_plane_lower P k s hs (D.neckMap k x)
    (mfderiv (𝓡 3) (𝓡 3) (D.neckMap k) x v)
    (mfderiv (𝓡 3) (𝓡 3) (D.neckMap k) x w)

end PoincareMT.M28.CounterexampleNeckFamily.WholeNeckBackwardData
