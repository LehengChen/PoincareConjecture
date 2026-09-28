import PoincareMT.Proofs.M47.LimitCanonicalControl

/-!
# Ancient package forwarder

The geometric-control package, infinite-horizon convergence, and all-scale
noncollapse predicate stay explicit on the same selected blowup family.  The
four-case canonical consumer is forwarded without reindexing or rebuilding
any of those inputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.M47

/-- Forward the reviewed ancient package to the unchanged four-case consumer.
The M30 control is retained as typed provenance for the same selected family;
the convergence and all-scale noncollapse inputs are consumed literally. -/
theorem limitCanonical_eventually_selected_control_of_ancient_package
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (F : ℕ → SurgeryFlowData.{u})
    (W : ∀ k, M33RegularHistoryWindow (F k))
    (history : ∀ k, M33RegularHistoryData (W k))
    (baseTime : ℕ → ℝ)
    (hbaseTime : ∀ k, baseTime k ∈ (history k).generalized.interval)
    (basePoint : ∀ k, ((history k).generalized.slice (baseTime k)).carrier)
    (hPositive : ∀ k,
      0 < ((F k).connection (baseTime k)).scalarCurvature
        ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
    (hDiverges : Tendsto
      (fun k => ((F k).connection (baseTime k)).scalarCurvature
        ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
      atTop atTop)
    (_C : M30GeometricLongControls
      (regularHistoryBlowupSequence F W history baseTime hbaseTime
        basePoint hPositive hDiverges) ⊤)
    (G : GeneralizedBlowupConvergence
      (regularHistoryBlowupSequence F W history baseTime hbaseTime
        basePoint hPositive hDiverges)
      (blowupBackwardInterval ⊤))
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hnc : BlowupLimitNoncollapsed G.limit kappa) :
    ∀ᶠ k in atTop,
      SurgeryCanonicalControl (F (G.subsequence k))
        (baseTime (G.subsequence k))
        ((history (G.subsequence k)).history.forward
          (baseTime (G.subsequence k))
          (hbaseTime (G.subsequence k))
          (basePoint (G.subsequence k)))
        S.setup.epsilon S.setup.C := by
  exact limitCanonical_eventually_selected_control
    (F := F) (W := W) (history := history) (baseTime := baseTime)
    (hbaseTime := hbaseTime) (basePoint := basePoint)
    (hPositive := hPositive) (hDiverges := hDiverges) (G := G)
    P S hkappa hnc

end PoincareMT.M47
