import PoincareMT.Proofs.M64.Sec19_3_Annuli.AnnulusSliceDifferential

/-!
# Positive boundary energy from actual immersion

A nonzero horizontal boundary velocity is an actual nonzero source
column, so its positive metric norm makes the annular energy positive.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Boundary immersion supplies the positive energy required by the logarithmic boundary
limit, without an additional conformal-factor bound. Source: Morgan--Tian (2007), Lemma
19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64Annulus_energyDensity_pos_of_horizontal_immersed
    (g : RiemannianMetric n M) {f : LoopPlane → M} {x s : ℝ}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f (annulusPoint x s))
    (himm : curveVelocity (n := n) (fun y => f (annulusPoint y s)) x ≠ 0) :
    0 < m60EnergyDensity g f (annulusPoint x s) := by
  let u0 := mfderiv (𝓡 2) (𝓡 n) f (annulusPoint x s)
    (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  let u1 := mfderiv (𝓡 2) (𝓡 n) f (annulusPoint x s)
    (EuclideanSpace.basisFun (Fin 2) ℝ 1)
  have hvel : curveVelocity (n := n) (fun y => f (annulusPoint y s)) x = u0 := by
    simpa only [u0, EuclideanSpace.basisFun_apply] using m64Annulus_horizontal_velocity hf
  have hu0 : u0 ≠ 0 := fun h => himm (hvel.trans h)
  have hpos := g.pos (f (annulusPoint x s)) u0 hu0
  have hnonneg : 0 ≤ g.inner (f (annulusPoint x s)) u1 u1 := by
    by_cases h : u1 = 0
    · simp [h]
    · exact (g.pos _ _ h).le
  simp only [m60EnergyDensity, Matrix.trace, Fin.sum_univ_two, m60AreaGram]
  change 0 < (1 / 2 : ℝ) *
    (g.inner (f (annulusPoint x s)) u0 u0 + g.inner (f (annulusPoint x s)) u1 u1)
  linarith

end PoincareMT
