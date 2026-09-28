import PoincareMT.Proofs.M47.TerminalSourceCountableFiniteGerms
import PoincareMT.Proofs.M47.TerminalCurvatureFiniteGermsFloor

/-!
# Terminal curvature from the countable finite-germ package

This is the downstream adapter for the actual countable finite-germ result.
It deliberately does not instantiate the all-raw-index source consumer:
the source patch remains indexed by `max k j` upstream. The physical
high-point readout is consumed as an explicit output of its selected-tail
source construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

/-- Forward the reviewed countable finite-germ result to the normalized
terminal curvature consumer. Connectedness is carried separately because the
result proposition intentionally stores the exhaustion as open sets only. -/
theorem terminalCurvature_bound_of_countable_finite_germs
    {epsilon1 epsilon A H : ℝ} (hM45 : M45SmallNeckScaleBound.{u} epsilon1)
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ epsilon1)
    (hcalibrated : epsilon ≤ 1 / 200) (hA : 0 < A)
    {P : ℕ → Type u} {X : Type u}
    [∀ n, TopologicalSpace (P n)] [TopologicalSpace X]
    [∀ n, ChartedSpace E (P n)] [ChartedSpace E X]
    [∀ n, IsManifold (𝓡 3) ∞ (P n)] [IsManifold (𝓡 3) ∞ X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X] [T3Space X]
    [SecondCountableTopology X] [ConnectedSpace X]
    (tau : ℕ → ℝ) (G : ∀ n, RicciFlow 3 (P n) (Icc (-tau n) 0))
    (q : ∀ n, P n → X) (gX : RiemannianMetric 3 X)
    (K : ℕ → Set X) (hK : ∀ m, IsOpen (K m))
    (hconnected : ∀ m, IsConnected (K m))
    (hfinite : TerminalSourceCountableFiniteGermsResult tau G q gX K hK)
    (D : LeviCivitaData gX) (hC : RicciFlowCurvatureTheory.{u})
    (hcomplete : MetricComplete gX) (p : X) (hscalar : D.scalarCurvature p ≠ 0)
    (hreadout : ∀ x, H ≤ D.scalarCurvature x →
      (∃ N : EpsilonNeck gX, N.connection = D ∧ N.epsilon = epsilon ∧
        D.scalarCurvature x ≤ A * D.scalarCurvature N.center) ∨
      IsCompact (univ : Set X)) :
    ∃ K0 : ℝ, 1 ≤ K0 ∧ ∀ x, D.curvatureTensorNorm x ≤ K0 := by
  let U : ℕ → Opens X := fun m => ⟨K m, hK m⟩
  let : ∀ m, ConnectedSpace (U m) := fun m =>
    isConnected_iff_connectedSpace.mp (hconnected m)
  obtain ⟨s, delta, hsne, hcover, hdelta, htime, rest⟩ := hfinite
  obtain ⟨flows, rest⟩ := rest
  obtain ⟨hmetric, rest⟩ := rest
  obtain ⟨hchart, rest⟩ := rest
  obtain ⟨hcompat, rest⟩ := rest
  obtain ⟨htriple, rest⟩ := rest
  obtain ⟨hlocal, hambient⟩ := rest
  have hoperator : ∀ x, D.NonnegativeCurvatureOperator x := fun x => hambient D x
  exact terminalCurvature_bound_of_finite_germs_floor
    hM45 hepsilon hsmall hcalibrated hA D hC hcomplete hoperator p hscalar
    U delta hdelta flows hmetric hlocal htriple hreadout

end PoincareMT.M47
