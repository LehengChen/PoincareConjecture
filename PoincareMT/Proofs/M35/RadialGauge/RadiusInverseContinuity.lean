import PoincareMT.Proofs.M35.RadialGauge.RadiusInverseFamily

/-!
# The actual inverse radius is continuous on the closed gauge slab

Morgan-Tian Proposition 12.26, pp. 320-322. The literal inverse is
bracketed by the strictly increasing forward maps. This establishes
joint continuity at the initial time without extending the PDE or
invoking an interior implicit function theorem there.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareMT.M35.RadialGauge

/-- Joint continuity of the actual radius inverse on any retained time
set, including the endpoints of the common closed slab. -/
theorem mapRadiusInverse_continuousOn
    {w : ℝ → ℝ → ℝ} {J : Set ℝ}
    (hc : ContinuousOn (Function.uncurry w) (J ×ˢ univ))
    (hs : ∀ t ∈ J, ContDiff ℝ ∞ (w t))
    (hv : ∀ t ∈ J, ∀ r, (1 + |r|) * |w t r| ≤ 1 / 8)
    (hd : ∀ t ∈ J, ∀ r, (1 + |r|) * |deriv (w t) r| ≤ 1 / 8) :
    ContinuousOn (Function.uncurry (mapRadiusInverse w)) (J ×ˢ univ) := by
  have hm (t : ℝ) (ht : t ∈ J) : StrictMono (mapRadius (w t)) := by
    have hρs : ContDiff ℝ ∞ (mapRadius (w t)) := contDiff_id.mul (hs t ht).exp
    apply strictMono_of_hasDerivAt_pos
      (fun r => (hρs.differentiable (by simp) r).hasDerivAt)
    intro r
    have h := mapRadius_deriv_sub_one_bound (hs t ht) r (hv t ht r) (hd t ht r)
    linarith only [(abs_le.mp h).1]
  have hρ : ContinuousOn (fun p : ℝ × ℝ => mapRadius (w p.1) p.2) (J ×ˢ univ) :=
    continuousOn_snd.mul hc.rexp
  have hfixed (a : ℝ) : ContinuousOn (fun p : ℝ × ℝ => mapRadius (w p.1) a)
      (J ×ˢ univ) :=
    hρ.comp (continuousOn_fst.prodMk continuousOn_const)
      (fun _ hp => ⟨hp.1, mem_univ _⟩)
  have hinv (t : ℝ) (ht : t ∈ J) (r : ℝ) :
      mapRadius (w t) (mapRadiusInverse w t r) = r :=
    (mapRadius_inverse_properties (hs t ht) (hv t ht) (hd t ht)).2.2.1 r
  intro p hp
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hpa : mapRadius (w p.1) a < p.2 := by
      simpa only [Function.uncurry_def, hinv p.1 hp.1] using hm p.1 hp.1 ha
    have he := ((hfixed a p hp).sub continuousWithinAt_snd).eventually
      (eventually_lt_nhds (sub_neg.mpr hpa))
    filter_upwards [he, self_mem_nhdsWithin] with q hq hqJ
    apply (hm q.1 hqJ.1).lt_iff_lt.mp
    simp only [Function.uncurry_def, hinv q.1 hqJ.1]
    exact sub_neg.mp hq
  · intro a ha
    have hpa : p.2 < mapRadius (w p.1) a := by
      simpa only [Function.uncurry_def, hinv p.1 hp.1] using hm p.1 hp.1 ha
    have he := ((hfixed a p hp).sub continuousWithinAt_snd).eventually
      (eventually_gt_nhds (sub_pos.mpr hpa))
    filter_upwards [he, self_mem_nhdsWithin] with q hq hqJ
    apply (hm q.1 hqJ.1).lt_iff_lt.mp
    simp only [Function.uncurry_def, hinv q.1 hqJ.1]
    exact sub_pos.mp hq

end PoincareMT.M35.RadialGauge
