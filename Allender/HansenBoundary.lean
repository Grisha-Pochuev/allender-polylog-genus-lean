import Allender.CircuitFamily
import Allender.CircuitGraph
import Allender.OrientableGenus
import Allender.ACC0Circuit

/-!
# Exact external boundary for Hansen's planar characterization

Hansen's published theorem states that polynomial-size constant-width planar
Boolean circuit families characterize `ACC⁰`.  The source model in this project
uses the same bounded-fan-in basis: binary AND/OR gates, unary COPY gates,
input literals, negated input literals, and constants.

This file records only the upper-bound direction needed by the candidate proof.
It is intentionally an external theorem declaration. No macroblock simulation,
padding argument, common-modulus theorem, or Allender conclusion is assumed.

A specialist should still confirm that the minor conventions of the published
model (initial layer, output location, padding, and size counting) agree exactly
or are connected by constant-overhead conversions. Until then the declaration
below is a named and auditable trust boundary rather than an internally proved
theorem.
-/

namespace Allender
namespace CircuitFamily

/-- Every concrete circuit in the family has planar underlying dependency graph. -/
def Planar (F : CircuitFamily) : Prop :=
  ∀ n, OrientableGenus.IsPlanar
    ((F.circuit n).layeredGraph.toSimpleGraph)

end CircuitFamily

namespace Hansen

/--
External theorem boundary: Hansen's upper-bound direction in the concrete
source and target models used by this repository.
-/
axiom planar_constant_width_to_acc0
    (F : CircuitFamily)
    (hsize : F.PolynomialSize)
    (hplanar : F.Planar) :
    InACC0 F.language

end Hansen
end Allender
