import PoincareMT.Definitions.Ch01.RiemannianMetric
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.CompactOpen

/-!
# C¹ free loops and filling widths

This file keeps the loop-space model explicit.  A loop is a circle map that
admits a C¹ extension to a neighbourhood of the unit circle. Its topology is
induced by compact-open control of values and intrinsic tangential derivatives,
while families additionally carry joint C¹ extension data. No declaration
here uses Mathlib's abstract `LoopSpace`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval

universe u

namespace PoincareMT

abbrev LoopPlane := EuclideanSpace ℝ (Fin 2)
abbrev LoopAmbient := EuclideanSpace ℝ (Fin 3)

/-- The closed unit disk used as a parametrized filling domain. -/
def loopDiskSet : Set LoopPlane := Metric.closedBall 0 1

/-- The unit circle, represented as a subtype of the parameter plane. -/
abbrev LoopCircle := {z : LoopPlane // ‖z‖ = 1}

/-- The disk with its subspace topology. -/
abbrev LoopDisk := {z : LoopPlane // z ∈ loopDiskSet}

/-- The parameter two-sphere for free families. -/
abbrev LoopTwoSphere := {z : LoopAmbient // ‖z‖ = 1}

/-- A fixed annular neighborhood, with no filling-disk condition. -/
def loopAnnulus : Set LoopPlane := {z | 1 / 2 < ‖z‖ ∧ ‖z‖ < 2}

/-- The counterclockwise unit tangent at a point of the unit circle. -/
noncomputable def loopCircleTangent (z : LoopCircle) : LoopPlane :=
  !₂[-z.1 1, z.1 0]

instance : Coe LoopCircle LoopPlane := ⟨Subtype.val⟩
instance : Coe LoopDisk LoopPlane := ⟨Subtype.val⟩
instance : Coe LoopTwoSphere LoopAmbient := ⟨Subtype.val⟩

/-- A circle reparameterization is an explicit homeomorphism of the boundary. -/
structure CircleReparameterization where
  map : LoopCircle → LoopCircle
  inverse : LoopCircle → LoopCircle
  left_inverse : Function.LeftInverse inverse map
  right_inverse : Function.RightInverse inverse map
  continuous_map : Continuous map
  continuous_inverse : Continuous inverse

/-- A compact connected smooth three-manifold carrier. -/
structure CompactConnectedThreeManifold (M : Type u) [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] where
  hausdorff : T2Space M
  second_countable : SecondCountableTopology M
  compact : IsCompact (Set.univ : Set M)
  connected : IsConnected (Set.univ : Set M)
  nonempty : (Set.univ : Set M).Nonempty

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- C¹ regularity of a circle map, expressed by an ambient neighbourhood extension. -/
def IsC1Loop (γ : LoopCircle → M) : Prop :=
  ∃ extension : LoopPlane → M,
    (∀ z : LoopCircle, extension z = γ z) ∧
      ContMDiffOn (𝓡 2) (𝓡 3) 1 extension loopAnnulus

/-- The project-owned C¹ free-loop space.  The extension and its regularity are
part of each loop. The topology ignores its off-circle values and normal
derivatives, retaining only the intrinsic first jet of the circle map. -/
structure C1FreeLoopSpace where
  toFun : LoopCircle → M
  extension : LoopPlane → M
  boundary : ∀ z : LoopCircle, extension z = toFun z
  regularity : ContMDiffOn (𝓡 2) (𝓡 3) 1 extension loopAnnulus
  continuous : Continuous toFun
  tangent_continuous : Continuous (fun z : LoopCircle =>
    (⟨toFun z, mfderiv (𝓡 2) (𝓡 3) extension z.1 (loopCircleTangent z)⟩ :
      TangentBundle (𝓡 3) M))

instance : CoeFun (C1FreeLoopSpace (M := M)) (fun _ => LoopCircle → M) :=
  ⟨fun γ => γ.toFun⟩

/-- The canonical C¹ extension carried by the loop object. -/
def c1LoopExtension (γ : C1FreeLoopSpace (M := M)) : LoopPlane → M :=
  γ.extension

/-- The first derivative field, packaged in the tangent bundle so that its base
point and its vector vary together. -/
noncomputable def c1LoopDerivative (γ : C1FreeLoopSpace (M := M))
    (z : LoopCircle) (i : Fin 2) : TangentBundle (𝓡 3) M :=
  ⟨γ z, (mfderiv (𝓡 2) (𝓡 3) (c1LoopExtension γ) z)
    (EuclideanSpace.basisFun (Fin 2) ℝ i)⟩

/-- The intrinsic derivative; normal derivatives of an extension do not enter
the loop topology. -/
noncomputable def c1LoopTangent (γ : C1FreeLoopSpace (M := M)) :
    ContinuousMap LoopCircle (TangentBundle (𝓡 3) M) :=
  ⟨fun z => ⟨γ z, mfderiv (𝓡 2) (𝓡 3) γ.extension z.1 (loopCircleTangent z)⟩,
    γ.tangent_continuous⟩

/-- The C¹ topology is the induced topology of two compact-open function
spaces. In particular, convergence controls the whole compact circle. -/
noncomputable instance : TopologicalSpace (C1FreeLoopSpace (M := M)) :=
  TopologicalSpace.induced
    (fun γ => ((⟨γ.toFun, γ.continuous⟩ : ContinuousMap LoopCircle M),
      c1LoopTangent γ)) inferInstance

/-- The constant C¹ loop at a point. -/
noncomputable def constantC1Loop (x : M) : C1FreeLoopSpace (M := M) :=
  { toFun := fun _ => x
    extension := fun _ => x
    boundary := fun _ => rfl
    regularity := by
      simpa using (contMDiff_const.contMDiffOn :
        ContMDiffOn (𝓡 2) (𝓡 3) 1 (fun _ : LoopPlane => x) loopAnnulus)
    continuous := continuous_const
    tangent_continuous := by
      convert (continuous_const : Continuous (fun _ : LoopCircle =>
        (⟨x, 0⟩ : TangentBundle (𝓡 3) M))) using 1
      funext z
      simp only [mfderiv_const]
      rfl }

/-- A path in the free-loop space from a loop to a constant loop. -/
def InIdentityComponent (x₀ : M) (γ : C1FreeLoopSpace (M := M)) : Prop :=
  ∃ H : Set.Icc (0 : ℝ) 1 → C1FreeLoopSpace,
    Continuous H ∧ H ⟨0, by simp⟩ = γ ∧
      H ⟨1, by simp⟩ = constantC1Loop x₀

/-- A continuous disk extension witnesses that a loop is null-homotopic. -/
def IsNullHomotopicLoop (γ : C1FreeLoopSpace (M := M)) : Prop :=
  ∃ extension : LoopPlane → M,
    Continuous extension ∧
      ∀ z : LoopCircle, extension z = γ z

/-- The circle is the boundary of the chosen disk. -/
def loopBoundary : Set LoopPlane := {z | ‖z‖ = 1}

/-- The metric Jacobian density of a parametrized two-dimensional map. -/
noncomputable def parametrizedAreaDensity (g : RiemannianMetric 3 M)
    (f : LoopPlane → M) (z : LoopPlane) : ℝ :=
  let d := mfderiv (𝓡 2) (𝓡 3) f z
  let e : Fin 2 → TangentSpace (𝓡 3) (f z) :=
    fun i => d (EuclideanSpace.basisFun (Fin 2) ℝ i)
  Real.sqrt (max 0 (Matrix.det (fun i j => g.inner (f z) (e i) (e j))))

/-- Parametrized Riemannian area, integrated over the unit disk. -/
noncomputable def parametrizedRiemannianArea (g : RiemannianMetric 3 M)
    (f : LoopPlane → M) : ℝ :=
  ∫ z in loopDiskSet, parametrizedAreaDensity g f z ∂MeasureTheory.volume

/-- A Lipschitz spanning disk for a C¹ loop.  Boundary equality is allowed up
to the explicit circle homeomorphism carried by `reparameterization`. -/
structure LipschitzSpanningDisk (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) where
  map : LoopPlane → M
  continuous_on_disk : ContinuousOn map loopDiskSet
  /-- The metric Jacobian is evaluated at the a.e. differentiability locus of
  the Lipschitz parametrization. -/
  ae_manifold_differentiable : ∀ᵐ z ∂MeasureTheory.volume,
    z ∈ loopDiskSet → MDifferentiableAt (𝓡 2) (𝓡 3) map z
  reparameterization : CircleReparameterization
  boundary_eq : ∀ z : LoopCircle,
    map z = γ (reparameterization.map z)
  lipschitz_constant : ℝ
  lipschitz_nonnegative : 0 ≤ lipschitz_constant
  lipschitz_on_disk : ∀ x y : LoopDisk,
    g.edist (map x) (map y) ≤
      ENNReal.ofReal lipschitz_constant * ENNReal.ofReal ‖(x : LoopPlane) - y‖
  area_integrable : MeasureTheory.IntegrableOn
    (parametrizedAreaDensity g map) loopDiskSet MeasureTheory.volume
  area_nonnegative : 0 ≤ parametrizedRiemannianArea g map

namespace LipschitzSpanningDisk

noncomputable def area {g : RiemannianMetric 3 M}
    {γ : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g γ) : ℝ :=
  parametrizedRiemannianArea g D.map

end LipschitzSpanningDisk

/-- The nonempty admissible filling class and its finite-area witness. -/
structure FillingAreaData (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) where
  nonempty : Nonempty (LipschitzSpanningDisk g γ)
  finite_witness : ∃ D : LipschitzSpanningDisk g γ, ∃ C : ℝ, D.area ≤ C
  bounded_below : BddBelow (Set.range (fun D : LipschitzSpanningDisk g γ => D.area))

/-- Infimum of the areas of all admissible Lipschitz spanning disks. -/
noncomputable def fillingArea (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) : ℝ :=
  sInf (Set.range (fun D : LipschitzSpanningDisk g γ => D.area))

/-- A concrete realization of a free sphere family's based `π₂` class.  The
cube representative is a genuine `GenLoop`, and the sphere parameterization
ties it to the displayed family. The selected parameterization, including its
orientation, is part of the data; a raw sphere map alone does not specify the
decorated family's based class. -/
structure FreeTwoSphereClassCertificate
    (basepoint : M)
    (family : LoopTwoSphere → C1FreeLoopSpace (M := M))
    (α : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
      (constantC1Loop basepoint)) where
  cube_representative : ContinuousMap (Fin 2 → I) (C1FreeLoopSpace (M := M))
  boundary_const : ∀ y ∈ Cube.boundary (Fin 2),
    cube_representative y = constantC1Loop basepoint
  sphere_parameter : ContinuousMap (Fin 2 → I) LoopTwoSphere
  sphere_parameter_surjective : Function.Surjective sphere_parameter
  sphere_parameter_boundary_collapsed : ∃ c : LoopTwoSphere, ∀ y,
    y ∈ Cube.boundary (Fin 2) → sphere_parameter y = c
  /-- Exact fibers identify all boundary points and no distinct interior points. -/
  sphere_parameter_quotient_fiber : ∀ y z,
    sphere_parameter y = sphere_parameter z ↔
      y = z ∨ (y ∈ Cube.boundary (Fin 2) ∧ z ∈ Cube.boundary (Fin 2))
  family_agreement : ∀ y,
    cube_representative y = family (sphere_parameter y)
  class_eq : α = Quotient.mk'
    (⟨cube_representative, boundary_const⟩ :
      GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop basepoint))

/-- A free two-sphere family of null-homotopic C¹ loops. -/
structure FreeTwoSphereFamily where
  /-- Basepoint used for the based loop-space class of the family. -/
  basepoint : M
  family : LoopTwoSphere → C1FreeLoopSpace (M := M)
  /-- The typed based `π₂(ΛM, *)` class represented by this family. -/
  homotopy_class : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
    (constantC1Loop basepoint)
  class_certificate : FreeTwoSphereClassCertificate basepoint family homotopy_class
  continuous : Continuous family
  derivative_continuous : ∀ i : Fin 2,
    Continuous (fun p : LoopTwoSphere × LoopCircle =>
      c1LoopDerivative (family p.1) p.2 i)
  null_homotopic : ∀ c, IsNullHomotopicLoop (family c)
  joint_extension : ∃ extension : LoopTwoSphere × LoopPlane → M,
    ContinuousOn extension (Set.univ ×ˢ loopAnnulus) ∧
      (∀ c (z : LoopCircle), extension (c, z.1) = family c z) ∧
      ∀ c, ContMDiffOn (𝓡 2) (𝓡 3) 1 (fun z => extension (c, z)) loopAnnulus

/-- Width of a free family, as the supremum of its filling areas. -/
noncomputable def familyWidth (g : RiemannianMetric 3 M)
    (Γ : FreeTwoSphereFamily (M := M)) : ℝ :=
  sSup (Set.range (fun c => fillingArea g (Γ.family c)))

/-- The dependent sigma value of a family's based homotopy class. -/
def familySigmaClass (Γ : FreeTwoSphereFamily (M := M)) :
    Σ x : M, HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
      (constantC1Loop x) :=
  ⟨Γ.basepoint, Γ.homotopy_class⟩

/-- The maximum and finiteness facts needed to use the supremum as a maximum. -/
structure FamilyWidthData (g : RiemannianMetric 3 M)
    (Γ : FreeTwoSphereFamily (M := M)) where
  filling_data : ∀ c, FillingAreaData g (Γ.family c)
  bounded_above : BddAbove (Set.range (fun c => fillingArea g (Γ.family c)))
  attained : ∃ c : LoopTwoSphere,
    fillingArea g (Γ.family c) = familyWidth g Γ

/-- Free homotopy of sphere families, with a continuous family of families. -/
def FreeTwoSphereHomotopic (Γ₁ Γ₂ : FreeTwoSphereFamily (M := M)) : Prop :=
  ∃ H : Set.Icc (0 : ℝ) 1 → FreeTwoSphereFamily,
    Γ₁.basepoint = Γ₂.basepoint ∧
      familySigmaClass Γ₁ = familySigmaClass Γ₂ ∧
      (∀ s, (H s).basepoint = Γ₁.basepoint) ∧
      Continuous (fun p : Set.Icc (0 : ℝ) 1 × LoopTwoSphere => (H p.1).family p.2) ∧
      H ⟨0, by simp⟩ = Γ₁ ∧ H ⟨1, by simp⟩ = Γ₂

/-- The concrete set over which a free homotopy class width is minimized. -/
noncomputable def classWidthRange (g : RiemannianMetric 3 M)
    (ξ : FreeTwoSphereFamily (M := M)) : Set ℝ :=
  by classical
    exact {w | ∃ Γ : FreeTwoSphereFamily (M := M),
      familySigmaClass Γ = familySigmaClass ξ ∧
        Nonempty (FreeTwoSphereClassCertificate Γ.basepoint Γ.family
          Γ.homotopy_class) ∧
        FreeTwoSphereHomotopic ξ Γ ∧ familyWidth g Γ = w}

noncomputable def classWidth (g : RiemannianMetric 3 M)
    (ξ : FreeTwoSphereFamily (M := M)) : ℝ :=
  by classical
    exact sInf (classWidthRange g ξ)

/-- Boundedness and a finite witness for the class infimum. -/
structure ClassWidthData (g : RiemannianMetric 3 M)
    (ξ : FreeTwoSphereFamily (M := M)) where
  based_class : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
    (constantC1Loop ξ.basepoint)
  based_class_eq : based_class = ξ.homotopy_class
  representative : FreeTwoSphereFamily (M := M)
  representative_based : representative.basepoint = ξ.basepoint
  representative_class : familySigmaClass representative = familySigmaClass ξ
  representative_homotopic : FreeTwoSphereHomotopic ξ representative
  representative_width_finite : ∃ C : ℝ, familyWidth g representative ≤ C
  bounded_below : BddBelow (classWidthRange g ξ)

end PoincareMT
