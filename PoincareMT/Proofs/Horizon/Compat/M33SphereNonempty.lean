import PoincareMT.Definitions.Ch09.RoundCylinderGeometry

/-! The donor's horn proofs use the round two-sphere as a nonempty type. -/

namespace PoincareMT

instance m33UnitTwoSphereNonempty : Nonempty UnitTwoSphere :=
  ⟨⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by simp⟩⟩

end PoincareMT
