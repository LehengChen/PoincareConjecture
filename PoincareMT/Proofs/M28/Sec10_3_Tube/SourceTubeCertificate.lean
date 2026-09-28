import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceBalancedChainAssembly
import PoincareMT.Proofs.M28.Sec10_3_Tube.LocalFiniteCertificate

/-!
# Source tube certificate after finite chain assembly

The finite gluing closure is ported into M28-owned modules.  This wrapper
keeps the lower theorem's threshold existential and exposes the exact carrier
and chain equalities needed by the later cap transport.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

/-- The finite balanced source chain has an actual frozen tube certificate.
The subset `X` is the source set already shown to lie in the literal chain
union; the local finite gluing theorem constructs the cylinder and isotopies. -/
theorem exists_source_tube_certificate_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {ε : ℝ} (C : BalancedNeckChain g ε), ε ≤ ε₀ →
        ∀ {a b : ℤ}, C.shape = .finite a b →
          ∀ (X : Set M), X ⊆ C.unionOpen →
            ∃ T : EpsilonTubeCertificate g X,
              T.epsilon = ε ∧ HEq T.chain C ∧ T.carrier = C.unionOpen := by
  obtain ⟨ε₀, hε₀, hsmall, hcertificate⟩ :=
    BalancedNeckChain.exists_finite_tubeCertificate_threshold_m28
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro ε C hε a b hshape X hX
  exact hcertificate C hε a b hshape X hX

end PoincareMT.M28
