import Allender.LayeredGraph
import Mathlib.Tactic

/-!
# Undirected walks in a layered directed graph

Circuit genus is measured on the underlying undirected graph.  This file defines
walks in that graph and proves the discrete separator fact used in the candidate
proof: a walk avoiding a deleted whole layer cannot travel from below the layer
to above it.
-/

namespace Allender
namespace LayeredDigraph

variable {V : Type*}

/-- Adjacency in the underlying undirected graph. -/
def UAdj (G : LayeredDigraph V) (u v : V) : Prop := G.edge u v ∨ G.edge v u

/-- A finite walk in the underlying undirected graph. -/
inductive UWalk (G : LayeredDigraph V) : V → V → Type _
  | nil (v : V) : UWalk G v v
  | cons {u v z : V} (adj : G.UAdj u v) (tail : UWalk G v z) : UWalk G u z

namespace UWalk

variable {G : LayeredDigraph V}

/-- Every vertex occurring in a walk satisfies `P`. -/
def All {u v : V} (walk : G.UWalk u v) (P : V → Prop) : Prop :=
  match walk with
  | .nil x => P x
  | .cons (u := x) _ tail => P x ∧ tail.All P

/-- The first vertex of a walk satisfying `All P` satisfies `P`. -/
theorem all_start {u v : V} {walk : G.UWalk u v} {P : V → Prop}
    (h : walk.All P) : P u := by
  cases walk with
  | nil => exact h
  | cons => exact h.1

/-- The final vertex of a walk satisfying `All P` satisfies `P`. -/
theorem all_end {u v : V} {walk : G.UWalk u v} {P : V → Prop}
    (h : walk.All P) : P v := by
  induction walk with
  | nil => exact h
  | cons _ tail ih => exact ih h.2

/-- Pointwise implication transports an `All` proof along a walk. -/
theorem all_mono {u v : V} {walk : G.UWalk u v} {P Q : V → Prop}
    (h : walk.All P) (hpq : ∀ x, P x → Q x) : walk.All Q := by
  induction walk with
  | nil x => exact hpq x h
  | @cons x y z hadj tail ih =>
      exact ⟨hpq x h.1, ih h.2⟩

/--
All vertices of a surviving walk lie in one interval block determined by the
cut layers; in particular its endpoints have the same block index.
-/
theorem endpoint_same_block (cuts : Finset Nat) {u v : V}
    (walk : G.UWalk u v)
    (hall : walk.All (G.Survives cuts)) :
    G.blockIndex cuts u = G.blockIndex cuts v := by
  induction walk with
  | nil => rfl
  | @cons u v z hadj tail ih =>
      rcases hall with ⟨hu, htail⟩
      have hv : G.Survives cuts v := all_start htail
      have huv : G.blockIndex cuts u = G.blockIndex cuts v := by
        rcases hadj with huv | hvu
        · exact G.edge_same_block_of_source_survives cuts huv hu
        · exact (G.edge_same_block_of_source_survives cuts hvu hv).symm
      exact huv.trans (ih htail)

end UWalk

variable (G : LayeredDigraph V)

/-- A vertex below a singleton cut layer is in block zero. -/
theorem blockIndex_singleton_of_below {m : Nat} {v : V}
    (hv : G.layer v < m) :
    G.blockIndex {m} v = 0 := by
  unfold blockIndex cutCountBelow
  have hfilter : ({m} : Finset Nat).filter (fun k => k < G.layer v) = ∅ := by
    ext k
    constructor
    · intro hk
      have hkf := Finset.mem_filter.mp hk
      have hkm := Finset.mem_singleton.mp hkf.1
      subst k
      omega
    · intro hk
      simpa using hk
  rw [hfilter]
  simp

/-- A vertex above a singleton cut layer is in block one. -/
theorem blockIndex_singleton_of_above {m : Nat} {v : V}
    (hv : m < G.layer v) :
    G.blockIndex {m} v = 1 := by
  unfold blockIndex cutCountBelow
  have hfilter : ({m} : Finset Nat).filter (fun k => k < G.layer v) = {m} := by
    ext k
    constructor
    · intro hk
      exact (Finset.mem_filter.mp hk).1
    · intro hk
      have hkm := Finset.mem_singleton.mp hk
      subst k
      exact Finset.mem_filter.mpr ⟨by simp, hv⟩
  rw [hfilter]
  simp

/--
There is no undirected walk whose vertices all avoid layer `m` and whose
endpoints lie strictly on opposite sides of that layer.
-/
theorem no_surviving_walk_across_layer {m : Nat} {u v : V}
    (hu : G.layer u < m)
    (hv : m < G.layer v)
    (walk : G.UWalk u v)
    (hall : walk.All (G.Survives {m})) : False := by
  have hsame := UWalk.endpoint_same_block (G := G) {m} walk hall
  rw [G.blockIndex_singleton_of_below hu,
    G.blockIndex_singleton_of_above hv] at hsame
  omega

end LayeredDigraph
end Allender
