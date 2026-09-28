import PoincareMT.Proofs.M64.Sec19_3_Annuli.MinimalAnnulusInterface

/-!
# Annular minimizing sequences and regularity certificates

The area range is nonempty and bounded below as soon as one admissible
annulus is supplied.  This is enough for a genuine minimizing sequence, but
not for a convergent annulus or for Plateau regularity.  The latter data are
therefore exposed as separate internal certificates and assembled only when
their producers are available.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {c0 c1 : ℝ → M}

/-- Every nonempty annular area class has an antitone sequence converging to its guarded
infimum. This is the order-theoretic part of the direct method; it does not assert a limit
map or minimizer attainment. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16,
pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64Annulus_exists_minimizing_sequence
    (A : M64Annulus g c0 c1) :
    ∃ seq : ℕ → M64Annulus g c0 c1,
      Antitone (fun k => (seq k).area) ∧
        Tendsto (fun k => (seq k).area) atTop
          (𝓝 (m64LeastAnnulusArea g c0 c1)) := by
  have hnonempty := m64AnnulusAreaRange_nonempty A
  have hbounded := m64AnnulusAreaRange_bddBelow g c0 c1
  obtain ⟨u, huanti, hlim, humem⟩ := exists_seq_tendsto_sInf hnonempty hbounded
  choose seq hseq using humem
  refine ⟨seq, ?_, ?_⟩
  · simpa only [hseq] using huanti
  · simpa only [hseq, m64LeastAnnulusArea] using hlim

/-- Regularity data supplied by the annular Plateau producer. The piecewise-C1 field
includes the boundary strips and the interior field is smooth. Source: Morgan--Tian (2007),
Lemma 19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
structure M64AnnulusRegularityCertificate
    (A : M64Annulus g c0 c1) : Prop where
  piecewise_c1 : M64PiecewiseC1Annulus A
  interior_smooth : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map
    (interior m64AnnulusDomain)

/-- Assemble the internal minimal-annulus record from independently produced attainment and
regularity certificates. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp.
447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
def m64MinimalAnnulusData_of_certificates
    (A : M64Annulus g c0 c1)
    (hmin : A.area = m64LeastAnnulusArea g c0 c1)
    (regularity : M64AnnulusRegularityCertificate A) :
    M64MinimalAnnulusData (g := g) (c0 := c0) (c1 := c1) :=
  { annulus := A
    area_minimal := hmin
    piecewise_c1 := regularity.piecewise_c1
    interior_smooth := regularity.interior_smooth }

/-- An actual least-area annulus and its supplied regularity assemble the internal
minimal-annulus data. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp.
447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
def m64MinimalAnnulusData_of_isLeast
    (B : M64Annulus g c0 c1)
    (hB : ∀ C : M64Annulus g c0 c1, B.area ≤ C.area)
    (regularity : M64AnnulusRegularityCertificate B) :
    M64MinimalAnnulusData (g := g) (c0 := c0) (c1 := c1) :=
  m64MinimalAnnulusData_of_certificates B
    (m64LeastAnnulusArea_eq_of_isLeast B hB) regularity

end PoincareMT
