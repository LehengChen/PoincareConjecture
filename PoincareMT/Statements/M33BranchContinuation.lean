import PoincareMT.Definitions.M33BranchContinuation
import PoincareMT.Definitions.M33RegularHistory
import PoincareMT.Statements.Ch04.Continuation
import PoincareMT.Statements.Ch04.Pinching
import PoincareMT.Statements.M31SingularRegularLimit
import PoincareMT.Statements.M32HornSelection

/-!
# M33 repaired branch-correct continuation statement

The predecessor services give compact local Ricci flow and Hamilton--Ivey
pinching from the actual nonnegative restart time. Given an admissible,
pinched, canonical and noncollapsed preterminal flow on [0,T), a concrete
singular limit and its horn data, construct an extension past T preserving
the old flow, admissibility and pinching. A nonempty controlled core gives
the actual terminal cut-and-cap operation; an empty core gives permanent
extinction with end time infinity. The attached ordinary restart is maximal
and has no subsequent surgery. At a finite endpoint its actual preterminal
slab starts at T and has arbitrarily late curvature blowup.
Earlier nonempty events retain their terminal carrier, limit geometry,
neck family and retained terminal image; earlier vanishing events retain
their reference time, pre-carrier and pre-flow. These literal-data outputs
yield checked preservation of the terminal policy on the old history.

The shared regular-history clause constructs the maximal regular generalized
subset on any nontrivial interval containing zero, with nonempty actual
slices and finitely many included surgery times. Its slice maps have exactly
the full regular slices and retained interiors as their images. It retains
curvature and volume, regular-time distance, and the actual cylinders in
both directions on open spatial domains lying in this regular part.

The bridge retains the actual Appendix A theory A with
terminalAccuracyFactor * H.epsilon <= A.epsilon0 and 1 <= H.constant, the metric and core
identification on the late reference window, and a metric-preserving
realization of the generalized flow in the entire earlier surgery history.
The latter follows the raw regular-slab transports and retention maps, so
the selected M32 neck's whole backward cylinder belongs to this same flow.
Applied deep-horn and local metric-surgery results concern the selected
terminal limit. Producing those results and the primitive bridge is a
separate application obligation, including M36.

Sources: Morgan--Tian, Theorem 3.11 and Proposition 3.12, pp. 39-40;
Proposition 4.12, p. 68; Theorem 4.32, pp. 79-80; Theorems 11.19 and 11.31,
pp. 279-292; Theorem 13.2, pp. 332-334; Chapter 14, pp. 343-350;
Definition 15.8, pp. 361-362; Lemma 15.11, p. 364; the empty-flow convention,
p. 409; and the corrected Appendix A.19-A.21/A.25 interfaces, pp. 507-514.
The complete derivation is in
`reviews/contracts/2026-09-17-m33-full-contract.md`; the retained maximal
restart is reviewed in
`reviews/contracts/2026-09-19-m33-maximal-restart-contract.md`.
The old-event preservation construction is reviewed in
`reviews/contracts/2026-09-20-surgery-policy-literal-copy.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Compact restart and pinching at the actual absolute start time. These
services are uniform over the compact three-manifolds constructed by M33. -/
structure M33Predecessors : Prop where
  local_flow : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M],
      RicciFlowLocalTheory 3 M
  pinching : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M],
    ∀ a b : ℝ, 0 ≤ a → a < b → ∀ F : RicciFlow 3 M (Set.Ico a b),
      HamiltonIveyPinchedAt (F.connection a) a → HamiltonIveyPinchingConclusion a b F

structure RepairedBranchContinuationTheory : Prop where
  regular_history : ∀ (F : SurgeryFlowData.{u}) (W : M33RegularHistoryWindow F),
    Nonempty (M33RegularHistoryData W)
  continuation : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M],
    ∀ {F : SurgeryFlowData.{u}} {T : ℝ},
    ∀ I : RepairedContinuationInput F T,
    ∀ {G : GeneralizedRicciFlowData.{u}},
    ∀ H : SingularTimeAssumptions G T M,
    ∀ L : RepairedSingularRegularLimitData H,
    ∀ N : RepairedHornSelectionData H,
    RepairedContinuationLimitBridge H L N I →
      Nonempty (RepairedBranchContinuationData I)

end PoincareMT
