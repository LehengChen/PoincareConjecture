import PoincareMT.Proofs.M64.Sec19_3_Annuli.SmoothAnnulusAdmission
import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusLipschitzSeed

/-!
# Admission and observed seed for a supplied free replacement

This is the first owner-side bridge after the Morrey--Lemaire replacement
producer.  The replacement may have its own traces and map; no equality with
an earlier weak representative is required.  The replacement producer and
its value/free-class conclusions remain separate obligations.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareMT

universe u

variable {n m : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)

/-- A supplied replacement with its own C1 strip and traces admits its own annulus and
observed weak seed. Local target-chart covers are internal to the admission theorem; no rank
or unbranchedness premise is needed. Proof expansion for Morgan-Tian (2007), Lemma 19.15,
pp. 447-449. -/
theorem m64FreeReplacement_admit_ownObservedSeed
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    {f : LoopPlane → M} {U : Set LoopPlane}
    (hU : IsOpen U) (hdom : m64AnnulusDomain ⊆ U)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f U)
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hlower : ∀ x, f (annulusPoint x 0) = c0 x)
    (hupper : ∀ x, f (annulusPoint x 1) = c1 x)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) :
    ∃ A : M64Annulus g c0 c1, A.map = f ∧
      ∃ W : M64ObservedWeakAnnulus (n := n) e c0 c1,
        W.map = f ∧
          ∀ i, ∀ᵐ p ∂volume.restrict (interior m64AnnulusDomain),
            W.column i p =
              fderiv ℝ (e ∘ f) p (EuclideanSpace.single i 1) := by
  obtain ⟨A, hA⟩ := m64Annulus_exists_eq_of_contMDiffOn g hU hdom hf
    hperiodic hlower hupper
  obtain ⟨W, hW, hcolumn⟩ := m64ObservedWeakAnnulus_of_annulus A e he
  refine ⟨A, hA, W, ?_, ?_⟩
  · simpa only [hA] using hW
  · intro i
    filter_upwards [hcolumn i] with p hp
    simpa only [hA] using hp

end PoincareMT
