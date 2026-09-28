import PoincareMT.Proofs.M07.Geometry.Manifold.InverseFunction.SmoothInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The actual terminal exhaustion map as a partial diffeomorphism

The whole forward function is retained, including its derivative slots.
The inverse is smooth on the actual image by the local inverse theorem.
Source: terminal-common-interval-identification.md, C6b.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareMT.M47

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [Nonempty M]

/-- The restricted open embedding gives a partial homeomorphism with the
literal original forward map on the entire carrier. -/
noncomputable def terminalCommonInterval_exhaustionMap
    {E : Set M} (hE : IsOpen E) (f : M → N)
    (hf : Topology.IsOpenEmbedding (fun x : E => f x)) : OpenPartialHomeomorph M N :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((show InjOn f E from fun x hx y hy heq =>
      congrArg Subtype.val (hf.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) heq)).toPartialEquiv f E)
    (continuousOn_iff_continuous_domRestrict.mpr hf.continuous) hf.isOpenMap hE

/-- Both source and image are the actual exhaustion sets, and equality of
the total forward functions retains every manifold derivative slot. -/
theorem terminalCommonInterval_exhaustion_map_readouts
    {E : Set M} (hE : IsOpen E) (f : M → N)
    (hf : Topology.IsOpenEmbedding (fun x : E => f x)) :
    let e := terminalCommonInterval_exhaustionMap hE f hf
    e.source = E ∧ e.target = f '' E ∧ (e : M → N) = f := by
  exact ⟨rfl, rfl, rfl⟩

/-- The actual inverse is smooth by the existing local inverse theorem;
no regularity or metric bound on that inverse is assumed. -/
theorem terminalCommonInterval_exhaustion_map_smooth
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    {E : Set M} (hE : IsOpen E) (f : M → N)
    (hf : Topology.IsOpenEmbedding (fun x : E => f x))
    (hs : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f E) :
    let e := terminalCommonInterval_exhaustionMap hE f hf
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := by
  let e := terminalCommonInterval_exhaustionMap hE f hf
  refine ⟨hs.contMDiffOn, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ : y ∈ f '' E := hy
  apply ContMDiffAt.contMDiffWithinAt
  apply Poincare.contMDiffAt_of_local_left_inverse (hs ⟨x, hx⟩).contMDiffAt
    ((hs ⟨x, hx⟩).mfderivToContinuousLinearEquiv (by simp)).bijective
  filter_upwards [hE.mem_nhds hx] with z hz
  exact e.left_inv hz

end PoincareMT.M47
