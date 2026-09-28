import PoincareMT.Proofs.M04.ShiJoinedDensity

/-!
# All-parameter identity for joined Shi energy

The finite coordinate density and the literal actual-path density agree once
the joined position and within-time velocity agree for every parameter.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

universe u

namespace PoincareMT.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "End" => E →L[ℝ] E
local notation "Data" => ℝ × ((E × (E × End)) × ((E × End) × (E × End)))

theorem shiJoinedDensity_eq_actual_derivWithin
    [T2Space M] (D : LeviCivitaData g)
    (c cL cR : OpenPartialHomeomorph M E) (a b t : ℝ)
    (p : Data) (F : ℝ → E → E)
    (hpos : ∀ z, F t z = shiJoinedPosition D c cL cR a b p z)
    (hvel : ∀ z, derivWithin (fun s => F s z) (Icc a b) t =
      shiJoinedVelocity D c cL cR a b p z) (z : E) :
    shiJoinedDensity g D c cL cR a b p z =
      shiChartMetric g c (F t z)
        (derivWithin (fun s => F s z) (Icc a b) t)
        (derivWithin (fun s => F s z) (Icc a b) t) := by
  simp only [shiJoinedDensity]
  rw [hpos z, hvel z]

end PoincareMT.M04

#print axioms PoincareMT.M04.shiJoinedDensity_eq_actual_derivWithin
