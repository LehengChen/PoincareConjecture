import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.FreeUniformizationCertificate
import PoincareMT.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusLipschitzSeed

/-!
# Observed weak map for a classical free replacement

This is the first downstream bridge after the Morrey--Lemaire replacement
step in Morgan--Tian pp. 464-466 and the accepted M64 Section 2 map.  A
classical replacement may have its own modulus and monotone boundary lifts;
the weak seed is built for those traces and retains the replacement map.
This file does not construct the replacement or its boundary regularity.

Morgan--Tian context: the proof of Lemma 19.31, Section 7, printed pp. 464-466.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff

namespace PoincareMT

universe u

variable {n m : ℕ} {M : Type u} [TopologicalSpace M]
  [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)

/-- A supplied classical free replacement receives its own observed weak map. The
replacement's boundary curves are the two lifted traces carried by the candidate. No
equality with a preceding weak representative is needed. The map follows the Lipschitz
rectangle Green construction in `WeakAnnulusLipschitzSeed.lean`; the source-backed
replacement itself is the separate Morrey--Lemaire producer. Proof expansion for Morgan-Tian
(2007), Lemma 19.15, pp. 447-449. -/
theorem m64FreeMorreyCandidate_ownObservedWeakMap
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    {A : M64Annulus g c0 c1} {eps : ℝ}
    (C : M64FreeMorreyUniformizationCandidate g c0 c1 A eps)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) :
    ∃ W : M64ObservedWeakAnnulus (n := n) e
        (c0 ∘ C.sigma0.map) (c1 ∘ C.sigma1.map),
      W.map = C.annulus.map ∧
      ∀ i, ∀ᵐ p ∂volume.restrict (interior m64AnnulusDomain),
        W.column i p =
          fderiv ℝ (e ∘ C.annulus.map) p
            (EuclideanSpace.single i 1) := by
  obtain ⟨W, hW, hcolumn⟩ := m64ObservedWeakAnnulus_of_annulus C.annulus e he
  exact ⟨W, hW, hcolumn⟩

end PoincareMT
