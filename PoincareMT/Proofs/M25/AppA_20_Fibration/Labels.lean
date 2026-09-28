import PoincareMT.Definitions.Ch09.NeckCapTopology
import PoincareMT.Proofs.M25.Mathlib.CircleArcs
import PoincareMT.Proofs.M25.Mathlib.FiberwiseGraphComplement
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Nonseparating labels from actual fiberwise graphs

The frozen sphere-bundle local trivializations give a coinducing
projection with connected fibers. An actual graph in a full product
chart then has connected complement, and the certificate homeomorphism
transports this to the component-relative neck label in Morgan--Tian
A.20, p. 508. The graph producer for every cover neck remains explicit;
see `tasks/M25/case-fibration/plan-cyclic-labels.md`, sections 3 and 6.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

attribute [local instance] SphereBundleCircleModel.carrier_topology
  SphereBundleCircleModel.carrier_charted SphereBundleCircleModel.carrier_manifold

namespace SphereBundleCircleModel

/-- The frozen local trivialization data defines an actual open partial
homeomorphism on the full preimage of a base neighborhood. Inverse-domain
membership is derived from the exact image and inverse identities.
This is the local bundle input for MT A.20, p. 508. -/
theorem exists_bundle_chart (B : SphereBundleCircleModel.{u}) (c : UnitCircle) :
    ∃ U : Set UnitCircle, IsOpen U ∧ c ∈ U ∧
      ∃ e : OpenPartialHomeomorph B.carrier (UnitTwoSphere × UnitCircle),
        e.source = B.projection ⁻¹' U ∧ e.target = univ ×ˢ U ∧
        ∀ x ∈ e.source, (e x).2 = B.projection x := by
  obtain ⟨U, hU, hc, f, g, himage, hleft, hright, hf, hg, hbase⟩ :=
    B.local_trivialization c
  have hfMap : MapsTo f (B.projection ⁻¹' U) (univ ×ˢ U) := by
    intro x hx
    rw [← himage]
    exact ⟨x, hx, rfl⟩
  have hgMap : MapsTo g (univ ×ˢ U) (B.projection ⁻¹' U) := by
    intro z hz
    rw [← himage] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [hleft hx]
    exact hx
  let e : OpenPartialHomeomorph B.carrier (UnitTwoSphere × UnitCircle) :=
    { toFun := f
      invFun := g
      source := B.projection ⁻¹' U
      target := univ ×ˢ U
      map_source' := hfMap
      map_target' := hgMap
      left_inv' := hleft
      right_inv' := hright
      open_source := hU.preimage B.projection_continuous
      open_target := isOpen_univ.prod hU
      continuousOn_toFun := hf.continuousOn
      continuousOn_invFun := hg.continuousOn }
  exact ⟨U, hU, hc, e, rfl, rfl, hbase⟩

/-- The actual sphere-bundle projection is open, using only local
trivializations over their stated neighborhoods. MT A.20, p. 508. -/
theorem m25_isOpenMap_projection (B : SphereBundleCircleModel.{u}) :
    IsOpenMap B.projection := by
  intro O hO
  apply isOpen_iff_mem_nhds.mpr
  rintro c ⟨x, hx, rfl⟩
  obtain ⟨U, _, hc, e, hsource, _, hbase⟩ := B.exists_bundle_chart (B.projection x)
  have hxsource : x ∈ e.source := hsource.symm ▸ hc
  let W : Set UnitCircle := Prod.snd '' (e '' (O ∩ e.source))
  have hW : IsOpen W := isOpenMap_snd _
    (e.isOpen_image_of_subset_source (hO.inter e.open_source) inter_subset_right)
  have hxW : B.projection x ∈ W :=
    ⟨e x, ⟨x, ⟨hx, hxsource⟩, rfl⟩, hbase x hxsource⟩
  have hWsub : W ⊆ B.projection '' O := by
    rintro y ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw.1, (hbase w hw.2).symm⟩
  exact Filter.mem_of_superset (hW.mem_nhds hxW) hWsub

/-- Every actual sphere-bundle fiber is connected. The proof uses the
entire local fiber and retains the inverse chart's target condition.
This is the connected-fiber input for MT A.20, p. 508. -/
theorem isConnected_projection_fiber (B : SphereBundleCircleModel.{u}) (c : UnitCircle) :
    IsConnected (B.projection ⁻¹' {c}) := by
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num))
  obtain ⟨U, _, hc, e, hsource, htarget, hbase⟩ := B.exists_bundle_chart c
  have hpair (q : UnitTwoSphere) : (q, c) ∈ e.target := by
    rw [htarget]
    exact ⟨mem_univ _, hc⟩
  let G : UnitTwoSphere → B.carrier := fun q => e.symm (q, c)
  have hG : ContinuousOn G univ :=
    e.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun q _ => hpair q)
  have himage : G '' univ = B.projection ⁻¹' {c} := by
    apply Subset.antisymm
    · rintro _ ⟨q, _, rfl⟩
      change B.projection (e.symm (q, c)) = c
      rw [← hbase _ (e.map_target (hpair q)), e.right_inv (hpair q)]
    · intro x hx
      change B.projection x = c at hx
      have hxsource : x ∈ e.source := by rw [hsource, mem_preimage, hx]; exact hc
      refine ⟨(e x).1, mem_univ _, ?_⟩
      change e.symm ((e x).1, c) = x
      rw [← hx, ← hbase x hxsource, Prod.mk.eta, e.left_inv hxsource]
  rw [← himage]
  exact (isConnected_univ : IsConnected (univ : Set UnitTwoSphere)).image G hG

/-- The actual bundle projection is coinducing because it is a
continuous open surjection. This supplies connected closed-arc preimages
without asserting a global arc trivialization in MT A.20, p. 508. -/
theorem isCoinducing_projection (B : SphereBundleCircleModel.{u}) :
    Topology.IsCoinducing B.projection :=
  (B.m25_isOpenMap_projection.isQuotientMap B.projection_continuous
    B.projection_surjective).isCoinducing

/-- Any base chart retained in one local-trivialization neighborhood lifts
to an actual fiberwise product chart on the full inverse image of its
target. This does not trivialize an arbitrary larger arc. MT A.20, p. 508. -/
theorem exists_fiberwise_chart_neighborhood (B : SphereBundleCircleModel.{u})
    (c : UnitCircle) :
    ∃ U : Set UnitCircle, IsOpen U ∧ c ∈ U ∧
      ∀ j : OpenPartialHomeomorph ℝ UnitCircle, j.target ⊆ U →
        ∃ T : OpenPartialHomeomorph (UnitTwoSphere × ℝ) B.carrier,
          T.source = univ ×ˢ j.source ∧ T.target = B.projection ⁻¹' j.target ∧
          ∀ z ∈ T.source, B.projection (T z) = j z.2 := by
  obtain ⟨U, hU, hc, e, hsource, htarget, hbase⟩ := B.exists_bundle_chart c
  refine ⟨U, hU, hc, ?_⟩
  intro j hj
  let k := (OpenPartialHomeomorph.refl UnitTwoSphere).prod j
  let T := k.trans e.symm
  have hpair (z : UnitTwoSphere × ℝ) (hz : z.2 ∈ j.source) :
      (z.1, j z.2) ∈ e.target := by
    rw [htarget]
    exact ⟨mem_univ _, hj (j.map_source hz)⟩
  have hTsource : T.source = univ ×ˢ j.source := by
    rw [OpenPartialHomeomorph.trans_source]
    change (univ ×ˢ j.source) ∩ k ⁻¹' e.target = univ ×ˢ j.source
    apply inter_eq_left.mpr
    intro z hz
    exact hpair z hz.2
  have hTtarget : T.target = B.projection ⁻¹' j.target := by
    rw [OpenPartialHomeomorph.trans_target]
    change e.source ∩ e ⁻¹' (univ ×ˢ j.target) = B.projection ⁻¹' j.target
    ext x
    constructor
    · rintro ⟨hx, _, hjx⟩
      change B.projection x ∈ j.target
      rwa [hbase x hx] at hjx
    · intro hx
      have hxsource : x ∈ e.source := hsource.symm ▸ hj hx
      exact ⟨hxsource, mem_univ _, (hbase x hxsource).symm ▸ hx⟩
  refine ⟨T, hTsource, hTtarget, ?_⟩
  intro z hz
  have hzj : z.2 ∈ j.source := (hTsource ▸ hz).2
  change B.projection (e.symm (z.1, j z.2)) = j z.2
  rw [← hbase _ (e.map_target (hpair z hzj)), e.right_inv (hpair z hzj)]

end SphereBundleCircleModel

namespace SphereBundleCircleCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} {X : Set M}

/-- An exact fiberwise graph for the transported central sphere gives
the frozen component-relative nonseparating label. The certificate maps
are only used on their actual carrier. This is the deterministic label
consumer for MT A.20, p. 508. -/
theorem isNonseparating_of_fiberwise_graph (F : SphereBundleCircleCertificate g X)
    (N : EpsilonNeck g) (hsphere : N.central_sphere ⊆ F.carrier)
    (j : OpenPartialHomeomorph ℝ UnitCircle)
    (T : OpenPartialHomeomorph (UnitTwoSphere × ℝ) F.model.carrier)
    {a α β b : ℝ} (ha : a < α) (hαβ : α < β) (hb : β < b)
    (hj : j.source = Ioo a b) (hT : T.source = univ ×ˢ Ioo a b)
    (htarget : T.target = F.model.projection ⁻¹' j.target)
    (hfiber : ∀ z ∈ T.source, F.model.projection (T z) = j z.2)
    (hC : IsConnected ((j '' Ioo α β)ᶜ))
    (h : UnitTwoSphere → ℝ) (hh : Continuous h) (hrange : ∀ q, h q ∈ Ioo α β)
    (hgraph : range (fun q => T (q, h q)) = F.forward '' N.central_sphere) :
    N.IsNonseparating := by
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num))
  have hcompl : IsConnected ((F.forward '' N.central_sphere)ᶜ) := by
    rw [← hgraph]
    exact j.isConnected_compl_range_graph_of_fiberwise T F.model.projection
      ha hαβ hb hj hT htarget hfiber F.model.isCoinducing_projection
      F.model.isConnected_projection_fiber hC h hh hrange
  have hinverse : Continuous F.inverse := by
    have heq : F.inverse = fun y => (F.homeomorph.symm y).1 :=
      funext F.inverse_eq
    rw [heq]
    exact continuous_subtype_val.comp F.homeomorph.symm.continuous
  have himage : F.inverse '' ((F.forward '' N.central_sphere)ᶜ) =
      F.carrier \ N.central_sphere := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      have hycarrier : F.inverse y ∈ F.carrier := by
        rw [F.inverse_eq]
        exact (F.homeomorph.symm y).2
      refine ⟨hycarrier, ?_⟩
      intro hysphere
      apply hy
      refine ⟨F.inverse y, hysphere, ?_⟩
      rw [F.inverse_eq, F.forward_eq (F.homeomorph.symm y),
        F.homeomorph.apply_symm_apply]
    · intro x hx
      refine ⟨F.forward x, ?_, ?_⟩
      · rintro ⟨z, hz, heq⟩
        have hsubtype : (⟨z, hsphere hz⟩ : F.carrier) = ⟨x, hx.1⟩ :=
          F.homeomorph.injective
            ((F.forward_eq ⟨z, hsphere hz⟩).symm.trans
              (heq.trans (F.forward_eq ⟨x, hx.1⟩)))
        have hzx : z = x := congrArg Subtype.val hsubtype
        exact hx.2 (hzx ▸ hz)
      · rw [F.forward_eq ⟨x, hx.1⟩, F.inverse_eq, F.homeomorph.symm_apply_apply]
  obtain ⟨c, hcomponent⟩ := F.component
  have hcenter : N.center ∈ connectedComponent c :=
    hcomponent ▸ hsphere N.center_on_central_sphere
  have hcomponent' : connectedComponent N.center = F.carrier :=
    (connectedComponent_eq hcenter).symm.trans hcomponent.symm
  change IsConnected (connectedComponent N.center \ N.central_sphere)
  rw [hcomponent', ← himage]
  exact hcompl.image F.inverse hinverse.continuousOn

/-- Every cover neck is nonseparating when the whole-manifold bundle
certificate supplies an exact fiberwise graph for each one. The family
is the original cover family, not merely the certificate's chosen necks.
This is the explicit uniform-label consumer for corrected MT A.20, p. 508. -/
theorem nonseparating_necks_of_fiberwise_graphs (H : NeckOnlyCover g)
    (F : SphereBundleCircleCertificate g H.X) (hwhole : F.carrier = univ)
    (hgraphs : ∀ N ∈ H.necks,
      ∃ (j : OpenPartialHomeomorph ℝ UnitCircle)
        (T : OpenPartialHomeomorph (UnitTwoSphere × ℝ) F.model.carrier)
        (a α β b : ℝ) (h : UnitTwoSphere → ℝ),
        a < α ∧ α < β ∧ β < b ∧ j.source = Ioo a b ∧
        T.source = univ ×ˢ Ioo a b ∧ T.target = F.model.projection ⁻¹' j.target ∧
        (∀ z ∈ T.source, F.model.projection (T z) = j z.2) ∧
        IsConnected ((j '' Ioo α β)ᶜ) ∧ Continuous h ∧
        (∀ q, h q ∈ Ioo α β) ∧
        range (fun q => T (q, h q)) = F.forward '' N.central_sphere) :
    ∀ N ∈ H.necks, N.IsNonseparating := by
  intro N hN
  obtain ⟨j, T, a, α, β, b, h, ha, hαβ, hb, hj, hT, htarget,
    hfiber, hC, hh, hrange, hgraph⟩ := hgraphs N hN
  apply F.isNonseparating_of_fiberwise_graph N (hwhole.symm ▸ subset_univ _)
    j T ha hαβ hb hj hT htarget hfiber hC h hh hrange hgraph

end SphereBundleCircleCertificate

end PoincareMT
