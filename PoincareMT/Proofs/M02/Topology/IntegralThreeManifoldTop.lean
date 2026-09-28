import PoincareMT.Proofs.M02.Topology.IntegralTopCoefficient
import PoincareMT.Proofs.M02.Topology.IntegralSupportUniv
import PoincareMT.Proofs.M02.Topology.IntegralManifoldOrientation
import PoincareMT.Proofs.M02.Topology.IntegralManifoldSupport

/-!
# Top integral homology of a compact simply connected three-manifold

The local orientation covering supplies coherent generators. Compact support
gluing and point detection identify the coefficient of each global class,
and the pair with empty subspace identifies supported and absolute homology.
-/

set_option autoImplicit false

noncomputable section

open Set

universe u

namespace PoincareMT.Proofs.M02.Topology

theorem nonempty_integralThreeManifoldTop_equiv_int
    {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [SimplyConnectedSpace M] (x0 : M) :
    Nonempty (integralHomology M 3 ≃ₗ[Int] Int) := by
  obtain ⟨omega, hgen, hlocal⟩ :=
    exists_integralThreeLocallyRepresentedGenerators x0
  obtain ⟨e⟩ := nonempty_integralSupportHomologyUniv_equiv_int x0 3
    (fun K hK => (integralThreeManifoldCompactSupport K hK).2) omega hgen hlocal
  exact ⟨(integralHomologySupportUnivIso M 3).toLinearEquiv.trans e⟩

end PoincareMT.Proofs.M02.Topology
