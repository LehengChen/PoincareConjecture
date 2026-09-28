import PoincareMT.Proofs.M25.Topology3D.Space3.SphereRegionChart
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Smooth sphere restriction of a norm-preserving ambient map

An ambient diffeomorphism preserving norms restricts smoothly in both
directions to the unit sphere. This retains the smooth normalization
needed by the reviewed source-sphere-disc-split derivation of 2026-09-22,
for Hatcher, Notes on Basic 3-Manifold Topology, Lemma 1.3, p. 3.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareMT.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

/-- The norm-preserving ambient diffeomorphism restricts to the native
unit sphere, with its existing smooth manifold structure in both directions. -/
noncomputable def normPreservingSphereDiffeomorph
    (F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (hF : ∀ y, ‖F y‖ = ‖y‖) :
    Diffeomorph (𝓡 n) (𝓡 n) (sphere (0 : E) 1) (sphere (0 : E) 1) ∞ where
  toEquiv := (normPreservingSphereHomeomorph F.toHomeomorph hF).toEquiv
  contMDiff_toFun := (F.contMDiff_toFun.comp
    (contMDiff_coe_sphere (E := E) (n := n))).codRestrict_sphere _
  contMDiff_invFun := (F.contMDiff_invFun.comp
    (contMDiff_coe_sphere (E := E) (n := n))).codRestrict_sphere _

omit [FiniteDimensional ℝ E] in
/-- The smooth restriction agrees pointwise with the given ambient map. -/
@[simp] theorem normPreservingSphereDiffeomorph_apply
    (F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (hF : ∀ y, ‖F y‖ = ‖y‖)
    (q : sphere (0 : E) 1) :
    (normPreservingSphereDiffeomorph (n := n) F hF q : E) = F q := rfl

omit [FiniteDimensional ℝ E] in
/-- The inverse smooth restriction agrees with the ambient inverse. -/
@[simp] theorem normPreservingSphereDiffeomorph_symm_apply
    (F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (hF : ∀ y, ‖F y‖ = ‖y‖)
    (q : sphere (0 : E) 1) :
    ((normPreservingSphereDiffeomorph (n := n) F hF).symm q : E) = F.symm q := rfl

end PoincareMT.M25.Topology3D
