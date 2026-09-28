import PoincareMT.Proofs.M05.Analysis.ODE.LocalFlow.Variational
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Deduplicated bridge for the Horizon snapshot module
`Analysis.ODE.LocalFlow.Variational`.
Its constants already exist on main in
`PoincareMT.Proofs.M05.Analysis.ODE.LocalFlow.Variational`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/
