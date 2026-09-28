import PoincareMT.Definitions.Ch18.LoopSpaceWidth
import PoincareMT.Definitions.Ch19.RampEstimates

/-!
# M58 short-loop triviality and small-area disks

This is the source-faithful `MT.18.lem.27` node.  It keeps the compact metric
manifold, the based pi2-triviality property, and the concrete C1 loop family
as primitive inputs.  Chapter 19 polygonal/C2 smoothing is a later ramp node;
it is not silently mixed into this topological short-loop lemma.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- The raw constant-loop family used by the free-loop reformulation of
Lemma 18.27. -/
noncomputable def constantLoopFamily {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] (x : M) :
    ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)) :=
  ⟨fun _ => constantC1Loop x, continuous_const⟩

/-!
The two conclusions used from Lemma 18.27 and Corollary 18.28.  The first
returns the identity in the actual based pi2 of the project C1 free-loop
space, so it does not assume the later pi2(loop-space)-pi3 identification.
The second supplies a concrete Lipschitz filling with the original allowed
circle reparameterization.
-/
structure RepairedShortLoopTrivialityData where
  short_loop_family_trivial : ∀ {M : Type u} [TopologicalSpace M]
      [T2Space M] [SecondCountableTopology M]
      [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      (g : RiemannianMetric 3 M)
      (_compact : IsCompact (Set.univ : Set M))
      (basepoint : M)
      (pi_two_trivial : Subsingleton
        (HomotopyGroup.Pi 2 M basepoint)),
      letI := pi_two_trivial
      ∃ ζ : ℝ, 0 < ζ ∧
        ∀ source : FreeTwoSphereFamily (M := M),
          source.basepoint = basepoint →
          (∀ c : LoopTwoSphere,
            freeLoopLength g (source.family c) < ζ) →
              source.homotopy_class = 1
  /-- Raw-family version used by M65's un-decorated output.  This is an
  explicit reformulation of the all-short argument, rather than an assumed
  arbitrary class predicate. -/
  raw_short_loop_family_trivial : ∀ {M : Type u} [TopologicalSpace M]
      [T2Space M] [SecondCountableTopology M]
      [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      (g : RiemannianMetric 3 M)
      (_compact : IsCompact (Set.univ : Set M))
      (_connected : IsConnected (Set.univ : Set M))
      (basepoint : M)
      (pi_two_trivial : Subsingleton
        (HomotopyGroup.Pi 2 M basepoint)),
      letI := pi_two_trivial
      ∃ ζ : ℝ, 0 < ζ ∧
        ∀ source : ContinuousMap LoopTwoSphere
            (C1FreeLoopSpace (M := M)),
          (∀ c, IsNullHomotopicLoop (source c)) →
          (∀ c, freeLoopLength g (source c) < ζ) →
            source.Homotopic (constantLoopFamily basepoint)
  small_loop_filling : ∀ {M : Type u} [TopologicalSpace M]
      [T2Space M] [SecondCountableTopology M]
      [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      (g : RiemannianMetric 3 M)
      (_compact : IsCompact (Set.univ : Set M)),
      ∀ η : ℝ, 0 < η →
        ∃ ζ : ℝ, 0 < ζ ∧ ζ < η / 2 ∧
          ∀ γ : C1FreeLoopSpace (M := M),
            freeLoopLength g γ < ζ →
              ∃ D : LipschitzSpanningDisk g γ, D.area < η

end PoincareMT
