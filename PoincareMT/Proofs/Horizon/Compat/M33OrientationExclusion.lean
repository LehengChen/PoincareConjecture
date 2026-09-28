import PoincareMT.Definitions.Ch17.GlobalSurgery
import PoincareMT.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Atlas.OpenEmbedding
import PoincareMT.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Atlas.LocalOrientation
import PoincareMT.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Nonorientable

/-! Orientation excludes a projective-plane product neighborhood.

The signed atlas supplies local orientation, whose pullback would orient
the nonorientable projective-plane product. Adapted from Horizon
`1e68e1700661486fd1b953051b30a642ad9788b5`, `Topology/Manifold/Orientation/ProjectivePlane/Exclusion.lean`,
with the statement expanded and the independent proof reused directly.
Source: Morgan--Tian, Theorem 0.3, footnote 2, p. xii;
Hatcher, Section 3.3, pp. 233-235 and Exercise 5, p. 257. -/

set_option autoImplicit false
open scoped Manifold ContDiff Topology
universe u
namespace PoincareMT

theorem m33OrientationExclusion
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (A : OrientationCompatibleAtlas M) :
    NoTrivialNormalProjectivePlane (M := M) := by
  rintro ⟨f, hf⟩
  let X := RealProjectiveTwo × Poincare.Topology.Orientation.ProjectivePlane.NormalInterval
  let : Nonempty X := Nonempty.map Poincare.Topology.Orientation.ProjectivePlane.projectivePlaneCover inferInstance
  let : T2Space X := hf.isEmbedding.t2Space
  let : SecondCountableTopology X := hf.isEmbedding.secondCountableTopology
  let P := Poincare.Topology.Orientation.ProjectivePlane.positiveThreeAtlasOpenEmbedding f hf
    (Poincare.Topology.positiveThreeAtlasOfSigned M A)
  let : ChartedSpace (EuclideanSpace Real (Fin 3)) X := P.charts
  let : LocallyCompactSpace X :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace Real (Fin 3)) X
  obtain ⟨O⟩ := Poincare.Topology.Orientation.ProjectivePlane.exists_localOrientation_of_positiveThreeAtlas P
  exact Poincare.Topology.Orientation.ProjectivePlane.projectivePlaneThickening_not_orientable O

end PoincareMT
