import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceCriticalBallWholeNeighborhoodProducer
import PoincareMT.Proofs.M28.Generalized.StrongNeckBufferedGlobalBounds

/-!
# Original whole-neck source data on one common backward window

One finite prefix retains the same original neck family, its raw
cylinders, the fixed spatial embedding domains and all capture bounds.
The four-fifths scale floor preserves exactly half of the limiting
squared scale in backward time. Source: Morgan--Tian Claim 10.11,
p. 255; M28 derivations 108 and 126.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

set_option maxHeartbeats 1600000 in
-- The fixed neck is on the retained limit carrier with its actual instances.
/-- The original source family on a fixed whole-neck neighborhood,
after one common finite prefix. Source: Claim 10.11; derivation 126. -/
structure WholeNeckBackwardData
    (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k)))
    (sigma : ℕ → ℕ)
    (V : letI := G.limitCarrier.topologicalSpace
      letI := G.limitCarrier.chartedSpace
      letI := G.limitCarrier.isManifold
      EpsilonNeck G.limitMetric) where
  /-- One prefix for capture, scale bounds and the smooth source domains. -/
  offset : ℕ
  /-- The original accuracy remains in the ordinary top-neck range. -/
  epsilon_small : epsilon < 1 / 2
  /-- The limit neck keeps the transferred three-halves accuracy. -/
  epsilon_limit : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    V.epsilon = 3 * epsilon / 2
  /-- The original strong neck, with the same retained spatial index. -/
  neck : ∀ k, GeneralizedStrongNeck
    (E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).flow
    (E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).time epsilon
  /-- A single raw cylinder per original source, shared by all charts. -/
  raw : ∀ k, RescaledRawCylinderData
    (C := (E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).flow.slice
      (E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).time)
    (U := strongNeckOpen (neck k)) (J := strongNeckBackwardInterval)
    (strongNeckCylinder (neck k)) (GeneralizedStrongNeck.physical_interval_subset (neck k))
  /-- The actual original neck remains centered at the retained image. -/
  center_eq : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ k, (neck k).center =
    (G.embedding (sigma (k + offset)) V.center).val.val
  /-- Smoothness is justified on the whole fixed limit neck at every index. -/
  exhaustion : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ k, V.carrier ⊆ G.exhaustion (sigma (k + offset))
  /-- The source time buffer retains the required half-scale interval. -/
  scale_lower : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ k, (4 / 5 : ℝ) * V.scale ^ 2 ≤
    (E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).flow.scalar
      ⟨(E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).time,
        (E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).basepoint⟩ *
          (neck k).scale ^ 2
  /-- The same source scales also have a finite uniform upper bound. -/
  scale_upper : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ k,
    (E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).flow.scalar
      ⟨(E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).time,
        (E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).basepoint⟩ *
          (neck k).scale ^ 2 ≤ (6 / 5 : ℝ) * V.scale ^ 2
  /-- One whole closed strip is captured by the same original neck at each index. -/
  capture : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ k y, y ∈ V.carrier →
    |(V.coordinate_inverse y).2| ≤ 3 * epsilon⁻¹ / 5 →
      (G.embedding (sigma (k + offset)) y).val.val ∈ (neck k).carrier ∧
      |((neck k).coordinate_inverse (G.embedding (sigma (k + offset)) y).val.val).2| <
        3 * epsilon⁻¹ / 4

set_option maxHeartbeats 2400000 in
-- A single eventual conjunction supplies all fields at the identical offset.
/-- The proved retained source family constructs all whole-neck backward
data; no common interval or domain is assumed separately. Source:
Claim 10.11; M28 derivation 126, finite-prefix audit. -/
theorem exists_whole_neck_backward_data
    (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (sigma : ℕ → ℕ), StrictMono sigma →
      ∀ (V : EpsilonNeck G.limitMetric), V.epsilon = 3 * epsilon / 2 →
      (∃ j : ℕ, V.carrier ⊆ G.exhaustion j) →
      ∀ (J : ∀ k, GeneralizedStrongNeck
        (E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow
        (E (W.high_index (G.subsequence (sigma k)) + H.shift)).time epsilon),
        (∀ k, (J k).center = (G.embedding (sigma k) V.center).val.val) →
        Tendsto (fun k =>
          (E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.scalar
            ⟨(E (W.high_index (G.subsequence (sigma k)) + H.shift)).time,
              (E (W.high_index (G.subsequence (sigma k)) + H.shift)).basepoint⟩ *
                (J k).scale ^ 2) atTop (𝓝 (V.scale ^ 2)) →
        (∀ᶠ k in atTop, ∀ y ∈ V.carrier,
          |(V.coordinate_inverse y).2| ≤ 3 * epsilon⁻¹ / 5 →
            (G.embedding (sigma k) y).val.val ∈ (J k).carrier ∧
            |((J k).coordinate_inverse (G.embedding (sigma k) y).val.val).2| <
              3 * epsilon⁻¹ / 4) →
        Nonempty (WholeNeckBackwardData H W G sigma V) := by
  classical
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro sigma hsigma V hV hj J hcenter hconv hcapture
  obtain ⟨j, hstage⟩ := hj
  have hpos : 0 < V.scale ^ 2 := sq_pos_of_pos V.scale_pos
  have hlower := hconv.eventually
    (eventually_ge_nhds (show (4 / 5 : ℝ) * V.scale ^ 2 < V.scale ^ 2 by linarith))
  have hupper := hconv.eventually
    (eventually_le_nhds (show V.scale ^ 2 < (6 / 5 : ℝ) * V.scale ^ 2 by linarith))
  have hindices := hsigma.tendsto_atTop.eventually (eventually_ge_atTop j)
  obtain ⟨offset, hoffset⟩ := eventually_atTop.mp
    (hcapture.and (hlower.and (hupper.and hindices)))
  have htail (k : ℕ) := hoffset (k + offset) (by omega)
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun k => subset_closure.trans (G.exhaustion_step k))
  exact ⟨{
    offset := offset
    epsilon_small := by linarith [V.epsilon_lt_half]
    epsilon_limit := hV
    neck := fun k => J (k + offset)
    raw := fun k => Classical.choice
      (GeneralizedStrongNeck.exists_rescaled_raw_cylinder_flow (J (k + offset)))
    center_eq := fun k => hcenter (k + offset)
    exhaustion := fun k => hstage.trans (hmono (htail k).2.2.2)
    scale_lower := fun k => (htail k).2.1
    scale_upper := fun k => (htail k).2.2.1
    capture := fun k => (htail k).1 }⟩

end PoincareMT.M28.CounterexampleNeckFamily
