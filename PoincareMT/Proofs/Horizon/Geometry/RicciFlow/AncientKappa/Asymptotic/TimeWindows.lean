import PoincareMT.Definitions.M18AsymptoticSoliton
import PoincareMT.Proofs.Horizon.Compat.M18AsymptoticSoliton
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.AncientKappa.Asymptotic.TimeWindows`.
Its constants already exist on main in
`PoincareMT.Definitions.M18AsymptoticSoliton`
`PoincareMT.Proofs.Horizon.Compat.M18AsymptoticSoliton`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/


/-!
# Compact time windows for an ancient limit

The definition is unchanged from Mapher's M18 definition file at revision
49331b7d7ecad38f53e4300c3b35d6a84b2cc648. These windows exhaust the open
ancient interval while retaining the based time -1.
-/

set_option autoImplicit false

namespace PoincareMT

theorem isCompact_ancientM18TimeWindow (j : ℕ) : IsCompact (ancientM18TimeWindow j) :=
  isCompact_Icc

end PoincareMT
