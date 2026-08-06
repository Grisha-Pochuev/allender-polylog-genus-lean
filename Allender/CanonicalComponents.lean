import Allender.ComponentSupport
import Allender.OrientableGenus

/-!
# Canonical active components of a graph remainder

This module makes the active set used by the separator recursion concrete.  An
active identifier is the finite support of an actual nonplanar connected
component.  Support injectivity ensures that no components are merged, and
genus additivity bounds the number of active identifiers.

The decoding function is total (as required by the existing process structure)
but is proved to recover exactly the intended component whenever its identifier
is active.
-/

namespace Allender
namespace LayeredDigraph

open OrientableGenus

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {G : LayeredDigraph V}

/-- Finite supports of the actual nonplanar connected components of `H`. -/
noncomputable def activeComponentVerts (H : SimpleGraph V)
    [DecidableRel H.Adj] : Finset (Finset V) := by
  classical
  exact (OrientableGenus.nonplanarComponents H).image componentVerts

theorem mem_activeComponentVerts_iff (H : SimpleGraph V)
    [DecidableRel H.Adj] (s : Finset V) :
    s ∈ activeComponentVerts H ↔
      ∃ c ∈ OrientableGenus.nonplanarComponents H,
        componentVerts c = s := by
  classical
  simp [activeComponentVerts]

/-- The concrete active set has at most `genus H` members. -/
theorem activeComponentVerts_card_le_genus (H : SimpleGraph V)
    [DecidableRel H.Adj] :
    (activeComponentVerts H).card ≤ OrientableGenus.genus H := by
  classical
  calc
    (activeComponentVerts H).card ≤
        (OrientableGenus.nonplanarComponents H).card := by
      exact Finset.card_image_le
    _ ≤ OrientableGenus.genus H :=
      OrientableGenus.nonplanarComponents_card_le_genus H

/-- Decode a support identifier to its unique nonplanar component when possible.
Outside the active set an arbitrary component is returned; no theorem uses that
fallback as an active component. -/
noncomputable def componentForSupport (H : SimpleGraph V)
    [DecidableRel H.Adj] (s : Finset V) : H.ConnectedComponent := by
  classical
  if h : ∃ c ∈ OrientableGenus.nonplanarComponents H,
      componentVerts c = s then
    exact Classical.choose h
  else
    exact H.connectedComponentMk default

/-- Active identifiers decode back to their exact support. -/
theorem componentForSupport_verts (H : SimpleGraph V)
    [DecidableRel H.Adj] {s : Finset V}
    (hs : s ∈ activeComponentVerts H) :
    componentVerts (componentForSupport H s) = s := by
  classical
  have hex : ∃ c ∈ OrientableGenus.nonplanarComponents H,
      componentVerts c = s :=
    (mem_activeComponentVerts_iff H s).1 hs
  unfold componentForSupport
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).2

/-- An active identifier decodes to a genuinely nonplanar component. -/
theorem componentForSupport_mem_nonplanar (H : SimpleGraph V)
    [DecidableRel H.Adj] {s : Finset V}
    (hs : s ∈ activeComponentVerts H) :
    componentForSupport H s ∈
      OrientableGenus.nonplanarComponents H := by
  classical
  have hex : ∃ c ∈ OrientableGenus.nonplanarComponents H,
      componentVerts c = s :=
    (mem_activeComponentVerts_iff H s).1 hs
  unfold componentForSupport
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).1

/-- The concrete finite connected set attached to one active remainder
component. -/
noncomputable def activeFiniteConnectedSet (cuts : Finset Nat)
    (s : Finset V) : G.FiniteConnectedSet :=
  componentFiniteConnectedSet (G.deleteLayers_toSimpleGraph_le cuts)
    (componentForSupport (G.deleteLayers cuts).toSimpleGraph s)

/-- On an active identifier the concrete connected set has exactly that
identifier as its vertex finset. -/
theorem activeFiniteConnectedSet_verts (cuts : Finset Nat)
    {s : Finset V}
    (hs : s ∈ activeComponentVerts
      ((G.deleteLayers cuts).toSimpleGraph)) :
    (activeFiniteConnectedSet (G := G) cuts s).verts = s := by
  classical
  rw [activeFiniteConnectedSet, componentFiniteConnectedSet_verts]
  exact componentForSupport_verts _ hs

/-- Every active connected set is bounded by the ambient vertex count. -/
theorem activeFiniteConnectedSet_card_le (cuts : Finset Nat)
    (s : Finset V) :
    (activeFiniteConnectedSet (G := G) cuts s).verts.card ≤
      Fintype.card V := by
  classical
  exact componentFiniteConnectedSet_card_le
    (G.deleteLayers_toSimpleGraph_le cuts)
    (componentForSupport (G.deleteLayers cuts).toSimpleGraph s)

end LayeredDigraph
end Allender
