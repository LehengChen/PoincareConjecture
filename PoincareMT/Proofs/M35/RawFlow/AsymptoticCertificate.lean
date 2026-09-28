import PoincareMT.Proofs.M35.RawFlow.InitialDerivativeBounds
import PoincareMT.Proofs.M34.Prop12_7_Asymptotics.PartialAsymptoticPatches

/-!
# The isolated qualitative raw-end interface

Morgan-Tian Proposition 12.7, pp. 298-299; OPERATING section 3;
derivations/14-raw-end-and-radial-controls.md. The isolated producer
types are now inhabited by the published lower M34 theorems. The partial
producer retains the arbitrary-flow quantifier and the full closed slab.
Neither interface includes M35's separate polynomial restart-target decay.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M35.Uniqueness

/-- The unchanged lower maximal-flow producer type. -/
abbrev RawMaximalAsymptoticProducer : Prop :=
  ∀ (_P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (_E₀ : StandardCapEstimate g₀) (F : MaximalStandardCapFlow g₀)
    (A : StandardCylinderAtlas) {epsilon t₀ : ℝ},
    0 < epsilon → t₀ ∈ Ico 0 F.base.lifetime →
      Nonempty (StandardFlowAsymptoticCertificate A F epsilon t₀)

/-- Literal fixed-patch cylinder comparison on one whole closed raw slab. -/
def PartialFlowCylinderEnd (A : StandardCylinderAtlas) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (epsilon t₀ : ℝ) : Prop :=
  0 < epsilon ∧ t₀ ∈ Ico 0 G.lifetime ∧
    ∃ K : Set StandardCapSpace, IsCompact K ∧
      ∀ x : StandardCapSpace, x ∉ K →
        ∃ N : StandardCylinderPatch epsilon⁻¹ x,
          StandardSpacetimeCylinderClose A G.flow.metric epsilon 0 1 (Icc 0 t₀) N

/-- The arbitrary-partial-flow producer required by comparison. -/
abbrev RawPartialAsymptoticProducer : Prop :=
  ∀ (_P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (_E₀ : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    (A : StandardCylinderAtlas) {epsilon t₀ : ℝ},
    0 < epsilon → t₀ ∈ Ico 0 G.lifetime →
      PartialFlowCylinderEnd A G epsilon t₀

theorem rawMaximalAsymptoticProducer : RawMaximalAsymptoticProducer := by
  intro P g₀ E₀ F A epsilon t₀ he ht
  exact M34.standardFlowAsymptoticCertificate_exists P E₀ F A he ht

theorem rawPartialAsymptoticProducer : RawPartialAsymptoticProducer := by
  intro P g₀ E₀ G A epsilon t₀ he ht
  exact ⟨he, ht, M34.partialStandardCapFlow_asymptoticPatches_exists P E₀ G A he ht⟩

/-- At a maximal flow the local geometric interface is exactly the frozen
certificate, including its original clock and full closed time interval. -/
theorem partialFlowCylinderEnd_iff_maximal_certificate
    (A : StandardCylinderAtlas) {g₀ : StandardInitialMetric}
    (F : MaximalStandardCapFlow g₀) (epsilon t₀ : ℝ) :
    PartialFlowCylinderEnd A F.base epsilon t₀ ↔
      Nonempty (StandardFlowAsymptoticCertificate A F epsilon t₀) := by
  constructor
  · rintro ⟨he, ht, K, hK, hpatch⟩
    exact ⟨{ epsilon_pos := he
             t₀_mem := ht
             compact_set := K
             compact := hK
             patches := hpatch }⟩
  · rintro ⟨C⟩
    exact ⟨C.epsilon_pos, C.t₀_mem, C.compact_set, C.compact, C.patches⟩

end PoincareMT.M35.Uniqueness
