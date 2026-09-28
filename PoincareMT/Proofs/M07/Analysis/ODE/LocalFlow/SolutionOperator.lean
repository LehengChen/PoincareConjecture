/-
Copyright (c) 2026 The DifferentialGeometry contributors.
Released under Apache 2.0 license.

Adapted from DifferentialGeometry/Analysis/ODE/Flow/SolutionOperator.lean
at revision 1b535dd102b94cc42b107cca27059687888f08b3.
Original SHA-256: 4d1b20df8e09eded3971b1d00e860015385288c4665faed8910ce90590c8f362
Changes: library paths and namespaces.
-/
import PoincareMT.Proofs.M05.Analysis.ODE.LocalFlow.SolutionOperator
import PoincareMT.Proofs.M07.Analysis.ODE.LocalFlow.HigherRegularity.VariationalLinearMapSmoothness
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension


/-! This entry reuses the identical declaration block from the existing local
M05 provider above. Lean rejects duplicate data declarations even when their
types and bodies agree. Original imports and attribution are retained;
the provider retains its existing semantic and provenance review status. -/
