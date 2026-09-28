import PoincareMT.Proofs.M25.Topology3D.Space3.NorthSphereChart
import PoincareMT.Proofs.M25.Topology3D.Space3.SurgeryMatchingProfile
import PoincareMT.Proofs.M25.Topology3D.Space3.CircleRadialChart

/-!+# The retained northern disc in a regular surgery

Compose the explicit northern sphere chart, the ambient matching
diffeomorphism, and the rectified source-disc chart. Its exact hemisphere
image and radial collar identity implement equation (6) in the reviewed
regular-disc-surgery derivation of 2026-09-22, following Hatcher, Notes on
Basic 3-Manifold Topology, Theorem 1.1 and Lemma 1.3, pp. 1-3.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareMT.M25.Topology3D

/-- The retained source-disc map is an actual smooth open chart between
patches of the standard source sphere. -/
noncomputable def surgeryNorthChart
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere) :
    OpenPartialHomeomorph UnitTwoSphere UnitTwoSphere :=
  (northSphereChart.transHomeomorph R.toHomeomorph).trans e

/-- The retained source parametrization has the exact composite formula. -/
@[simp] theorem surgeryNorthChart_apply
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere) (q : UnitTwoSphere) :
    surgeryNorthChart R e q = e (R (northSphereCoordinate q)) := rfl

/-- The northern surgery chart has precisely the domain where both
local charts are meaningful. -/
theorem surgeryNorthChart_source
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere) :
    (surgeryNorthChart R e).source =
      {q | q ∈ northSphereDomain ∧ R (northSphereCoordinate q) ∈ e.source} := rfl

/-- The composed northern map is smooth on its full actual source. -/
theorem surgeryNorthChart_contMDiffOn
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (surgeryNorthChart R e)
      (surgeryNorthChart R e).source :=
  he.comp (R.contMDiff_toFun.comp_contMDiffOn
    (northSphereChart_contMDiffOn.mono inter_subset_left)) (fun _ hq => hq.2)

/-- The inverse of the retained northern map is smooth on its actual
target, so this is a diffeomorphism of open source patches. -/
theorem surgeryNorthChart_symm_contMDiffOn
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (hi : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (surgeryNorthChart R e).symm
      (surgeryNorthChart R e).target :=
  northSphereChart_symm_contMDiff.comp_contMDiffOn
    (R.contMDiff_invFun.comp_contMDiffOn (hi.mono inter_subset_left))

/-- Exact ball preservation by R puts the entire closed northern
hemisphere inside the source-disc chart when the joining radius is at
most one. -/
theorem surgeryNorthChart_contains_hemisphere
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : closedBall 0 1 ⊆ e.source) {c : ℝ} (hc : c ≤ 1)
    (hR : R '' closedBall 0 1 = closedBall 0 c) :
    {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} ⊆
      (surgeryNorthChart R e).source := by
  intro q hq
  refine ⟨northern_hemisphere_subset_chart_source hq, he ?_⟩
  apply closedBall_subset_closedBall hc
  rw [← hR]
  refine ⟨northSphereCoordinate q, ?_, rfl⟩
  rw [← northSphereChart_image_northern_hemisphere]
  exact ⟨q, hq, rfl⟩

/-- The retained northern hemisphere parametrizes the exact smaller
closed source disc, with no assertion about the unrelated source disc. -/
theorem surgeryNorthChart_image_hemisphere
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere) {c : ℝ}
    (hR : R '' closedBall 0 1 = closedBall 0 c) :
    surgeryNorthChart R e '' {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} =
      e '' closedBall 0 c := by
  change (e ∘ R ∘ northSphereChart) '' _ = _
  rw [image_comp, image_comp, northSphereChart_image_northern_hemisphere, hR]

/-- The chart construction retains injective derivatives at every
point of its full open source. -/
theorem surgeryNorthChart_mfderiv_injective
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target)
    {q : UnitTwoSphere} (hq : q ∈ (surgeryNorthChart R e).source) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 2) (surgeryNorthChart R e) q) := by
  have hm : (surgeryNorthChart R e).MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨(surgeryNorthChart_contMDiffOn R e he).mdifferentiableOn (by simp),
      (surgeryNorthChart_symm_contMDiffOn R e hi).mdifferentiableOn (by simp)⟩
  exact hm.mfderiv_injective hq

/-- Height in the northern chart is the rational function used by the
radial matching map. The domain hypothesis excludes its junk pole value. -/
theorem northSphereCoordinate_height {q : UnitTwoSphere}
    (hq : q ∈ northSphereDomain) :
    (heightCoordinates (q : E3)).2 =
      (1 - ‖northSphereCoordinate q‖ ^ 2) / (1 + ‖northSphereCoordinate q‖ ^ 2) := by
  have h := congrArg (fun p : UnitTwoSphere => (heightCoordinates (p : E3)).2)
    (northSpherePoint_coordinate hq)
  rw [northSpherePoint_coordinates] at h
  exact h.symm

/-- The matching radius is c minus alpha times the standard sphere
height, which gives exact equality on the open cap overlap. -/
theorem surgeryMatchingRadius_north {q : UnitTwoSphere}
    (hq : q ∈ northSphereDomain) (c alpha : ℝ) :
    surgeryMatchingRadius c alpha ‖northSphereCoordinate q‖ =
      c - alpha * (heightCoordinates (q : E3)).2 := by
  rw [northSphereCoordinate_height hq, surgeryMatchingRadius]
  ring

/-- When both radial germs apply, the retained northern map equals the
prescribed source collar at the exact affine height parameter. -/
theorem surgeryNorthChart_collar_formula
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (Q : UnitCircle × ℝ → UnitTwoSphere) (c alpha k sigma : ℝ)
    {q : UnitTwoSphere} (hq : q ∈ northSphereDomain)
    (hw : northSphereCoordinate q ≠ 0)
    (hpos : 0 < surgeryMatchingRadius c alpha ‖northSphereCoordinate q‖)
    (hR : R (northSphereCoordinate q) =
      surgeryMatchingRadius c alpha ‖northSphereCoordinate q‖ •
        NormedSpace.normalize (northSphereCoordinate q))
    (he : e (R (northSphereCoordinate q)) =
      Q (circleDirection (R (northSphereCoordinate q)),
        sigma * (k * (1 - ‖R (northSphereCoordinate q)‖)))) :
    surgeryNorthChart R e q =
      Q (circleDirection (northSphereCoordinate q),
        sigma * (k * (1 - c) + k * alpha * (heightCoordinates (q : E3)).2)) := by
  rw [surgeryNorthChart_apply, he, hR, ← circleDirection_coe hw,
    circleDirection_smul _ hpos, norm_smul, Real.norm_eq_abs, abs_of_pos hpos,
    norm_eq_of_mem_sphere, mul_one, surgeryMatchingRadius_north hq]
  congr 2
  ring

end PoincareMT.M25.Topology3D
