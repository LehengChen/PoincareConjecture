import PoincareMT.Proofs.M59.Sec4_1_Whiskering.Service
import PoincareMT.Proofs.M59.Mathlib.CubeSphereHomotopy

/-!
# Free sphere homotopy under transport along constant loops

The actual cubical transport homotopy descends through the common sphere
parameter. The endpoint based classes may live at different points; the
conclusion is raw free homotopy, since the decorated project relation also
requires equal basepoints. Sources: MT Claim 18.16, p. 430; Hatcher, Section
4.1, pp. 341-342. See the M59 cube-model derivation for this distinction.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology unitInterval

namespace PoincareMT

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- The actual based cube carried by a regular sphere family.
Source: MT Claim 18.16 and Definition 18.17, p. 430. -/
def m59FamilyCube (Gamma : FreeTwoSphereFamily (M := M)) :
    GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop Gamma.basepoint) :=
  ⟨Gamma.class_certificate.cube_representative, Gamma.class_certificate.boundary_const⟩

/-- Transport along a path of constant loops induces raw free sphere homotopy
when the endpoint families use the same sphere parameter and transported class.
Source: MT Claim 18.16, p. 430; Hatcher, Section 4.1, pp. 341-342. -/
theorem whisker_constantLoopPath_freeHomotopic
    (q : M59SphereQuotient) (Gamma Delta : FreeTwoSphereFamily (M := M))
    (hGamma : Gamma.class_certificate.sphere_parameter = q.map)
    (hDelta : Delta.class_certificate.sphere_parameter = q.map)
    (p : Path Gamma.basepoint Delta.basepoint) (P : M59ConstantLoopPath p)
    (hclass : (m59HigherBasepointTransport (C1FreeLoopSpace (M := M)) 2).map
      P.loop Gamma.homotopy_class = Delta.homotopy_class) :
    (m59FamilyMap Gamma).Homotopic (m59FamilyMap Delta) := by
  have hclasses : (⟦GenLoop.boundaryTransport P.loop (m59FamilyCube Gamma)⟧ :
      HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop Delta.basepoint)) =
        ⟦m59FamilyCube Delta⟧ := by
    change (m59HigherBasepointTransport (C1FreeLoopSpace (M := M)) 2).map P.loop
      (Quotient.mk' (m59FamilyCube Gamma)) = Quotient.mk' (m59FamilyCube Delta)
    exact (congrArg ((m59HigherBasepointTransport (C1FreeLoopSpace (M := M)) 2).map P.loop)
      Gamma.class_certificate.class_eq.symm).trans (hclass.trans Delta.class_certificate.class_eq)
  obtain ⟨K⟩ : GenLoop.Homotopic
      (GenLoop.boundaryTransport P.loop (m59FamilyCube Gamma)) (m59FamilyCube Delta) :=
    Quotient.exact hclasses
  let H := (GenLoop.boundaryTransportHomotopy P.loop (m59FamilyCube Gamma)).trans
    (GenLoop.HomotopyAlong.ofRel K)
  apply H.descend_sphere q.map q.surjective q.exact_fibers
  · intro v
    change Gamma.class_certificate.cube_representative v = Gamma.family (q.map v)
    rw [← hGamma]
    exact Gamma.class_certificate.family_agreement v
  · intro v
    change Delta.class_certificate.cube_representative v = Delta.family (q.map v)
    rw [← hDelta]
    exact Delta.class_certificate.family_agreement v

end PoincareMT
