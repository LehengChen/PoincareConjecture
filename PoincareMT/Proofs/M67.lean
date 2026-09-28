import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Main
import PoincareMT.Statements.M67

/-!
# M67 surgery-time width transport proof entry

The sole M67 theorem-owned placeholder is the finite-piece assembly of the
M66 ordinary comparison with the M57/M59 surgery transport.  Earlier files are
read-only support; future proof helpers belong under `Proofs/M67/`.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- On a zero-time component path with trivial initial pi2, fix the induced
initial metric and a nonzero loop-space class under a coherent M59 system.
Assume the strict delta and height comparison bounds at every surgery in [0,T].
The actual flow satisfies the absolute scalar bound, and the supplied full
M61, M58, M65 and M66 services have the same width and deformation indices.
Construct the actual-flow width with the Proposition 18.18 estimates,
preserving that initial metric/class, constructing its regular and surgery
transport, and using the same M59 identifications at every slice.
Source: Morgan--Tian Proposition 15.12, p. 365, Claim 18.16 and Proposition
18.18, pp. 430--433. Metric restriction, class propagation and filling transport
are constructed, not assumed as width or jump estimates. -/
theorem m67SurgeryWidthTheory : M67SurgeryWidthTheory.{u} :=
  horizon_m67_surgery_width_theory


end PoincareMT
