import PoincareMT.Proofs.M28.Sec10_3_Tube.CapScalarBand

/-!
# Off-path cap-core exclusion

Morgan--Tian Claim 10.4, pp. 249--250.  The scalar-band barrier is applied
to a trimmed subsegment of an actual minimizing path.  The minimizer interval
and retained scalar-band interval are kept separate: the low endpoint of the
former is below the band, so the statement is not vacuous.  An A.11
boundary-crossing producer may then use the resulting disjointness from the
closed cap core.  No quarter, side, or no-return conclusion is used here.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.M28

/-- At one universal tolerance, a candidate cap's closed core is disjoint from
the retained scalar-band subsegment of an actual minimizing path.  The path
interval `[a,b]` is the interval on which the intrinsic minimum is taken,
while `[s,t]` is a retained interval with its own component and scalar-band
hypotheses.  Thus the low endpoint need not satisfy the band lower bound.
This is the cap barrier used after an actual A.11 boundary hit; the theorem
does not manufacture that hit (Claim 10.4, pp. 249--250). -/
theorem exists_off_path_cap_core_exclusion_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
        (epsilon C Q : ℝ),
        0 < epsilon → epsilon ≤ epsilon₀ → 0 < C → 0 < Q →
        ∀ (N : CapCertificate g), N.epsilon = epsilon →
          N.cap_constant ≤ C →
          ∀ {U : Set M} {γ : ℝ → M} {a b s t : ℝ},
            a ≤ b → s ≤ t → Icc s t ⊆ Icc a b →
            ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b) →
            MapsTo γ (Icc a b) U →
            g.pathELength γ a b ≠ ⊤ →
            g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b) →
            D.scalarCurvature (γ a) ≤ 8 * Q →
            (∀ v ∈ Icc s t,
              connectedComponentIn {p : M | 4 * Q < D.scalarCurvature p}
                (γ v) ⊆ U) →
            (∀ v ∈ Icc s t,
              16 * (max C 2) * Q ≤ D.scalarCurvature (γ v) ∧
                D.scalarCurvature (γ v) ≤
                  D.scalarCurvature (γ b) / (2 * max C 2)) →
            Disjoint N.closed_core (γ '' Icc s t) := by
  let epsilon₀ := min neckShorteningEpsilon (1 / 200 : ℝ)
  refine ⟨epsilon₀, lt_min neckShorteningEpsilon_pos (by norm_num),
    min_le_right _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g D epsilon C Q _hε hsmall _hC hQ N hNepsilon hNconstant
    U γ a b s t _hab _hst hsub hγ hγU hfinite hmin hstart hcomponent hband
  have hshort : N.epsilon ≤ neckShorteningEpsilon := by
    calc
      N.epsilon = epsilon := hNepsilon
      _ ≤ epsilon₀ := hsmall
      _ ≤ neckShorteningEpsilon := min_le_left _ _
  apply disjoint_left.mpr
  rintro x hxcore ⟨v, hv, rfl⟩
  have hvab : v ∈ Icc a b := hsub hv
  have hclosed := hxcore
  have hclosedCarrier : γ v ∈ N.carrier := by
    rw [N.closed_core_eq_complement_end] at hclosed
    exact hclosed.1
  have hNU : N.carrier ⊆ U :=
    (N.carrier_subset_scalar_component D
      (hNconstant.trans (le_max_left C 2)) hQ hclosedCarrier
      (hband v hv).1).trans (hcomponent v hv)
  have hendpoints := N.endpoints_not_mem_of_scalar_band D
    (hNconstant.trans (le_max_left C 2)) hQ hclosedCarrier hstart
      (hband v hv).1 (hband v hv).2
  rcases N.endpoint_mem_of_intrinsic_minimizer hshort hNU hvab hγ hγU
      hfinite hmin hclosed with ha | hb
  · exact (hendpoints.1 ha).elim
  · exact (hendpoints.2 hb).elim

end PoincareMT.M28
