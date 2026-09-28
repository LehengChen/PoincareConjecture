import PoincareMT.Proofs.M25.Topology3D.Space3.CollarCoordinates
import PoincareMT.Proofs.M25.Topology3D.Space3.HeightField
import PoincareMT.Proofs.M25.Topology3D.Space3.SphereSard

/-!
# A smooth unit normal for the central collar sphere

Normalize the gradient of the actual inverse collar parameter. Its
nonvanishing derivative makes the normal well-defined, and the chain rule
on the central slice proves normal orthogonality. Sphere Sard then supplies
simultaneously regular antipodal normal values. This is the normal-map
step in Hatcher, Notes on Basic 3-Manifold Topology, Theorem 1.1, p. 1;
see the generic-height and sphere-sard derivations in the task records.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareMT.M25.Topology3D

/-- The normalized gradient of the inverse collar coordinate is a
smooth unit normal to every tangent vector of the central sphere. -/
theorem exists_sphere_collar_unit_normal (ψ : UnitTwoSphere × ℝ → E3)
    (hψ : IsCollarEmbedding ψ) :
    ∃ N : UnitTwoSphere → UnitTwoSphere, ContMDiff (𝓡 2) (𝓡 2) ∞ N ∧
      ∀ (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q),
        ⟪(N q : E3),
          mfderiv (𝓡 2) 𝓘(ℝ, E3) (fun p : UnitTwoSphere => ψ (p, 0)) q v⟫_ℝ = 0 := by
  obtain ⟨ρ, hρ, hρψ, hρnz⟩ := exists_sphere_collar_defining_function ψ hψ
  let U : Set E3 := ψ '' (univ ×ˢ Ioo (-1) 1)
  let e : UnitTwoSphere → E3 := fun q => ψ (q, 0)
  have hU : IsOpen U := collar_image_open ψ hψ
  have heU (q : UnitTwoSphere) : e q ∈ U :=
    ⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have he : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ e := by
    apply contMDiffOn_univ.mp
    exact hψ.1.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      (fun _ _ => ⟨mem_univ _, by norm_num⟩)
  have hgrad := contDiffOn_gradient_of_isOpen hU ρ hρ
  have hn0 (q : UnitTwoSphere) : gradient ρ (e q) ≠ 0 := by
    intro hz
    apply hρnz _ (heU q)
    rw [← toDual_gradient, hz, map_zero]
  let N : UnitTwoSphere → UnitTwoSphere := fun q => sphereDirection (gradient ρ (e q))
  have hN : ContMDiff (𝓡 2) (𝓡 2) ∞ N := by
    apply contMDiffOn_univ.mp
    exact sphereDirection_contMDiffOn.comp
      (hgrad.contMDiffOn.comp he.contMDiffOn (fun q _ => heU q))
      (fun q _ => hn0 q)
  refine ⟨N, hN, ?_⟩
  intro q v
  have hzero : ρ ∘ e = fun _ => 0 :=
    funext fun p => hρψ (p, 0) ⟨mem_univ _, by norm_num⟩
  have hd := ((hρ.contDiffAt (hU.mem_nhds (heU q))).differentiableAt
    (by simp)).hasFDerivAt.hasMFDerivAt.comp q
      (he.mdifferentiable (by simp) q).hasMFDerivAt
  have hmap := hd.mfderiv
  rw [hzero, mfderiv_const] at hmap
  have hkernel : fderiv ℝ ρ (e q) (mfderiv (𝓡 2) 𝓘(ℝ, E3) e q v) = 0 :=
    congrArg (fun A => A v) hmap.symm
  let A : TangentSpace (𝓡 2) q →L[ℝ] E3 := mfderiv (𝓡 2) 𝓘(ℝ, E3) e q
  have hkernel' : fderiv ℝ ρ (e q) (A v) = 0 := hkernel
  change ⟪(sphereDirection (gradient ρ (e q)) : E3),
    A v⟫_ℝ = 0
  rw [sphereDirection_coe (hn0 q), NormedSpace.normalize, real_inner_smul_left,
    inner_gradient_left, hkernel', mul_zero]

/-- Every central collar sphere has a smooth unit normal and a unit
direction with regular normal derivatives over both antipodal values. -/
theorem exists_sphere_collar_regular_normal (ψ : UnitTwoSphere × ℝ → E3)
    (hψ : IsCollarEmbedding ψ) :
    ∃ (N : UnitTwoSphere → UnitTwoSphere) (u : UnitTwoSphere),
      ContMDiff (𝓡 2) (𝓡 2) ∞ N ∧
      (∀ (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q),
        ⟪(N q : E3),
          mfderiv (𝓡 2) 𝓘(ℝ, E3) (fun p : UnitTwoSphere => ψ (p, 0)) q v⟫_ℝ = 0) ∧
      ∀ q : UnitTwoSphere, ((N q : E3) = (u : E3) ∨ (N q : E3) = -(u : E3)) →
        Function.Injective (mfderiv (𝓡 2) (𝓡 2) N q) := by
  obtain ⟨N, hN, hnormal⟩ := exists_sphere_collar_unit_normal ψ hψ
  obtain ⟨u, hu⟩ := exists_opposite_sphere_regularValues N hN
  exact ⟨N, u, hN, hnormal, hu⟩

end PoincareMT.M25.Topology3D
