import PoincareMT.Proofs.M05.Analysis.ODE.LocalFlow.ParametricLinearODE
import PoincareMT.Proofs.M05.Analysis.ODE.LocalFlow.ParametricLinearODE.ParameterDerivative
import PoincareMT.Proofs.M05.Analysis.ODE.LocalFlow.ParametricLinearODE.Variational
import PoincareMT.Proofs.Horizon.Analysis.ODE.LocalFlow.Inhomogeneous

/-! Deduplicated bridge for the Horizon snapshot module
`Analysis.ODE.LocalFlow.ParametricLinearODE`.
Its constants already exist on main in
`PoincareMT.Proofs.M05.Analysis.ODE.LocalFlow.ParametricLinearODE`
`PoincareMT.Proofs.M05.Analysis.ODE.LocalFlow.ParametricLinearODE.ParameterDerivative`
`PoincareMT.Proofs.M05.Analysis.ODE.LocalFlow.ParametricLinearODE.Variational`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/
