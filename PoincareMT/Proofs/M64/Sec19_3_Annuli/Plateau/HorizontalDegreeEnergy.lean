import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.CylinderModulusBound

/-!
# Horizontal energy forced by a lifted circle degree

The M62 circle product metric and a real phase lift turn one nonzero
winding increment into a quantitative horizontal Gram-energy lower bound.
This theorem deliberately exposes the lift as an input; supplying it for
the weak limit is the separate harmonic-circle producer.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareMT

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

/-- The actual phase winding yields its quantitative horizontal weighted-energy
contribution. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64WeightedGramEnergy_ge_phase_degree
    (P : M62.CircleProductData F circumference) (t : ℝ)
    (f : LoopPlane → P.charts.Point) (hf : ContMDiff (𝓡 2) (𝓡 (n + 1)) 1 f)
    (L : LoopPlane → ℝ) (hL : ContDiff ℝ 1 L)
    (hquot : ∀ p, P.circle.quotient (L p) = (f p).2)
    {d : ℝ} (hd : d ≠ 0)
    (hshift : ∀ x s, L (annulusPoint (x + curvePeriod) s) =
      L (annulusPoint x s) + d)
    {r E : ℝ} (hr : 0 < r)
    (hE : (∫ p in interior m64AnnulusDomain,
      (r * m60AreaGram (P.flow.metric t) f p 0 0 +
        r⁻¹ * m60AreaGram (P.flow.metric t) f p 1 1) / 2) ≤ E) :
    r * d ^ 2 / (2 * curvePeriod) ≤ E := by
  have hbound := m64CirclePhase_cylinder_modulus_bound P t f hf L hL hquot hd hshift hr hE
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
  have hden : 0 < 2 * curvePeriod := by positivity
  apply (div_le_iff₀ hden).mpr
  have hh : r * d ^ 2 ≤ (2 * curvePeriod * E) :=
    (le_div_iff₀ hd2).mp hbound
  nlinarith

end PoincareMT
