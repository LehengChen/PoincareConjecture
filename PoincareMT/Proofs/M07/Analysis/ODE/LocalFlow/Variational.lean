/-
Copyright (c) 2026 The DifferentialGeometry contributors.
Released under Apache 2.0 license.

Adapted from DifferentialGeometry/Analysis/ODE/Flow/Variational.lean
at revision 1b535dd102b94cc42b107cca27059687888f08b3.
Original SHA-256: 857a4e900bc707d0697f82ea293a20c59cf0ca16edf6bd820ebadca02a38a2c9
Changes: library paths and namespaces.
-/
import PoincareMT.Proofs.M05.Analysis.ODE.LocalFlow.Variational
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! This entry reuses the identical declaration block from the existing local
M05 provider above. Lean rejects duplicate data declarations even when their
types and bodies agree. Original imports and attribution are retained;
the provider retains its existing semantic and provenance review status. -/
