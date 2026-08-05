import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Layered directed graphs

The circuit graph is treated as a directed graph equipped with a natural-number
layer function.  Edges advance by exactly one layer.  Cutting whole layers assigns
all surviving endpoints of an edge to the same interval block.
-/

namespace Allender

/-- A directed graph whose edges go from layer `i` to layer `i + 1`. -/
structure LayeredDigraph (V : Type*) where
  edge : V → V → Prop
  layer : V → Nat
  edge_next : ∀ {u v}, edge u v → layer v = layer u + 1

namespace LayeredDigraph

variable {V : Type*} (G : LayeredDigraph V)

/-- A vertex survives deletion of the listed whole layers. -/
def Survives (cuts : Finset Nat) (v : V) : Prop := G.layer v ∉ cuts

/-- Number of cuts strictly below layer `ℓ`; this names the interval block of `ℓ`. -/
def blockIndex (cuts : Finset Nat) (ℓ : Nat) : Nat :=
  (cuts.filter fun k => k < ℓ).card

/-- If layer `n` is not cut, crossing from `n` to `n+1` does not change the block. -/
theorem blockIndex_succ_of_not_mem (cuts : Finset Nat) {n : Nat} (hn : n ∉ cuts) :
    blockIndex cuts (n + 1) = blockIndex cuts n := by
  unfold blockIndex
  have hsets :
      cuts.filter (fun k => k < n + 1) = cuts.filter (fun k => k < n) := by
    ext k
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hkcuts, hlt⟩
      refine ⟨hkcuts, ?_⟩
      by_contra hnot
      have hge : n ≤ k := Nat.le_of_not_gt hnot
      have hle : k ≤ n := Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hlt)
      have hkn : k = n := Nat.le_antisymm hle hge
      subst k
      exact hn hkcuts
    · rintro ⟨hkcuts, hlt⟩
      exact ⟨hkcuts, Nat.lt_trans hlt (by omega)⟩
  exact congrArg Finset.card hsets

/-- Every surviving source edge stays inside one cut-layer interval block. -/
theorem edge_same_block_of_source_survives (cuts : Finset Nat) {u v : V}
    (hEdge : G.edge u v) (hSurvive : G.Survives cuts u) :
    G.blockIndex cuts (G.layer u) = G.blockIndex cuts (G.layer v) := by
  rw [G.edge_next hEdge]
  exact (blockIndex_succ_of_not_mem cuts hSurvive).symm

/-- Edges strictly increase the layer number. -/
theorem layer_lt_of_edge {u v : V} (hEdge : G.edge u v) : G.layer u < G.layer v := by
  rw [G.edge_next hEdge]
  omega

end LayeredDigraph
end Allender
