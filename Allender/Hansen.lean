import Allender.ACC0Circuit
import Allender.CircuitFamily
import Allender.CircuitGraph
import Allender.OrientableGenus

/-!
# Exact external boundary for Hansen's planar-circuit theorem

Kristoffer Arnsfelt Hansen's Theorem 1 states that constant-width,
polynomial-size planar circuits compute exactly `ACC⁰`.  The source model in
this repository uses the gate basis specified in that paper: fan-in two
`AND`/`OR`, fan-in one `COPY`, literals, and Boolean constants.  A
`CircuitFamily` already fixes one width for every input length, so the forward
direction needed by the Allender reduction has the family-level statement
below.

This module deliberately does not postulate a simulator for an arbitrary
relation or for independently chosen blocks.  It exposes one named published
theorem whose conclusion is the concrete `InACC0` definition from
`ACC0Circuit.lean`.  Later padding code must construct one actual planar
family before applying it.
-/

namespace Allender

namespace CircuitFamily

/-- Every concrete dependency graph in the family is planar. -/
def Planar (F : CircuitFamily) : Prop :=
  ∀ n, OrientableGenus.IsPlanar (F.circuit n).layeredGraph.toSimpleGraph

end CircuitFamily

namespace Hansen

/-- External theorem (Hansen, Theorem 1, forward direction): a nonuniform
constant-width family of polynomial-size planar circuits computes a language
in `ACC⁰`.

Constant width is structural in `CircuitFamily`; planarity and polynomial size
are explicit hypotheses.  The theorem returns one fixed modulus through the
definition of `InACC0`.
-/
axiom planar_constantWidth_polySize_to_ACC0
    (F : CircuitFamily)
    (hplanar : F.Planar)
    (hsize : F.PolynomialSize) :
    InACC0 F.language

end Hansen
end Allender
