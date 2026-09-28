import PoincareMT.Proofs.M25.Topology3D.Space3.Saddle.NonnestedEndComposition

/-!
# Image-chain assembly for the nonnested bridge

The reviewed B1 construction has four actual ambient maps: a reference end
exchange, a height-preserving middle comparison, a full-cap alignment, and a
target end exchange.  This file proves the final set-theoretic composition
once those maps expose their complete forward image laws.  It follows
Hatcher, Notes on Basic 3-Manifold Topology, Lemma 1.2, pp. 2-3, and the
image-chain derivation of 2026-09-23.
-/

set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareMT.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

/-- Assemble the reviewed B1 image chain into a bridge to a known ball.
`Gref` first replaces the reference sphere by its retained middle and cap
pieces, `Kband` carries the retained middle to the target, and `Fcaps`
aligns the complete cap pieces.  `Gtarget` decomposes the target sphere by
the same target middle and cap union.  The resulting map carries the target
sphere exactly onto the known reference boundary. -/
theorem exists_nonnested_bridge_of_image_chain
    (S Sref Rref Cref Rtarget Ctarget : Set E3)
    (Gref Kband Fcaps Gtarget : D3)
    (Bref : BallNeighborhoodChart E3 E3)
    (hRef : Gref '' Sref = Rref ∪ Cref)
    (hKband : Kband '' Rref = Rtarget)
    (hCaps : Fcaps '' (Rtarget ∪ Kband '' Cref) = Rtarget ∪ Ctarget)
    (hTarget : Gtarget '' S = Rtarget ∪ Ctarget)
    (hBref : Bref.boundary = Sref) :
    ∃ Kmid : D3, Kmid '' S = Bref.boundary := by
  let Fref : D3 := (Gref.trans Kband).trans Fcaps
  have hFref : Fref '' Sref = Rtarget ∪ Ctarget := by
    calc
      Fref '' Sref = Fcaps '' ((Gref.trans Kband) '' Sref) := by
        change ((Gref.trans Kband).trans Fcaps) '' Sref = _
        rw [Diffeomorph.coe_trans, Set.image_comp]
      _ = Fcaps '' (Kband '' (Gref '' Sref)) := by
        rw [Diffeomorph.coe_trans, Set.image_comp]
      _ = Fcaps '' (Kband '' (Rref ∪ Cref)) := by rw [hRef]
      _ = Fcaps '' (Kband '' Rref ∪ Kband '' Cref) := by
        simp only [image_union]
      _ = Fcaps '' (Rtarget ∪ Kband '' Cref) := by rw [hKband]
      _ = Rtarget ∪ Ctarget := hCaps
  have hFrefInv : Fref.symm '' (Rtarget ∪ Ctarget) = Sref := by
    rw [← hFref, image_image]
    simp only [Fref.symm_apply_apply, image_id']
  refine ⟨Gtarget.trans Fref.symm, ?_⟩
  calc
    (Gtarget.trans Fref.symm) '' S = Fref.symm '' (Gtarget '' S) := by
      rw [Diffeomorph.coe_trans, Set.image_comp]
    _ = Fref.symm '' (Rtarget ∪ Ctarget) := by rw [hTarget]
    _ = Sref := hFrefInv
    _ = Bref.boundary := hBref.symm

end PoincareMT.M25.Topology3D
