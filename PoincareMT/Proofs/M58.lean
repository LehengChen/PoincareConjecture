import PoincareMT.Statements.M58LoopSmoothing
import PoincareMT.Proofs.M58.Lemma18_27_Triviality
import PoincareMT.Proofs.M58.Cor18_28_SmallDisks

/-!
# M58 short-loop triviality and small-area disk proof entry

Natural-language theorem: construct the positive short-loop threshold and
identity-class conclusion of Morgan--Tian Lemma 18.27, together with the
small-area Lipschitz disk threshold of Corollary 18.28.  The loop-space to pi3
identification is owned by M59, and C2 ramp smoothing is owned by later Chapter
19 milestones.

Source: Morgan--Tian Lemma 18.27 and Corollary 18.28 (printed p. 434;
`references/derived/MT2007.txt:21255-21282`), with Definition 18.17
(`21070-21079`) for the admissible disk.  The C1-loop model qualification is
tracked in `reviews/errata/2026-09-10-surgery-extinction-audit.md:68-75`.

The proof uses a finite composition of local chart contractions and a
radial cutoff disk. Uniform metric derivative bounds and polar integration
give the small-area estimate for the contract's actual Lipschitz fillings.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Short-loop triviality and the corrected small-area disk threshold of
MT Lemma 18.27 and Corollary 18.28, printed pp. 434-435. -/
theorem repairedShortLoopTriviality : RepairedShortLoopTrivialityTheory.{u} := by
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · intro M _ _ _ _ _ g hcompact basepoint hpi
    exact Proofs.M58.short_loop_family_trivial g hcompact basepoint hpi
  · intro M _ _ _ _ _ g hcompact hconnected basepoint hpi
    obtain ⟨ζ, hζ, hfamily⟩ :=
      Proofs.M58.raw_short_loop_family_trivial g hcompact hconnected basepoint hpi
    exact ⟨ζ, hζ, fun source _ hlength => hfamily source hlength⟩
  · intro M _ _ _ _ _ g hcompact η hη
    exact Proofs.M58.small_loop_filling g hcompact η hη

end PoincareMT
