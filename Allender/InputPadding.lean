import Allender.ACC0Circuit
import Allender.CircuitGraph
import Allender.OrientableGenus

/-!
# Adding and fixing unused input variables

The simultaneous use of Hansen's theorem pads many source circuits into one
family indexed by larger input lengths.  After Hansen supplies one `AC⁰[m]`
family, the added variables are fixed back to zero.  This file implements both
operations on the concrete source and target circuit models.

Padding source inputs changes only input-gate indices, never dependency edges.
Restricting a target circuit replaces an input outside the retained prefix by
the constant `false`.  The semantic theorems below make the two operations
exact rather than leaving “ignored inputs” as an informal convention.
Both transformations retain the existing layer width and layer count.
-/

namespace Allender

namespace BitState

/-- Extend an `n`-bit input to `N` bits by filling the unused suffix with zero. -/
def zeroExtend {n N : Nat} (h : n ≤ N) (x : BitState n) : BitState N :=
  fun j => if hj : j.val < n then x ⟨j.val, hj⟩ else false

@[simp] theorem zeroExtend_castLE {n N : Nat} (h : n ≤ N)
    (x : BitState n) (i : Fin n) :
    zeroExtend h x (Fin.castLE h i) = x i := by
  simp [zeroExtend]

/-- Every coordinate outside the retained prefix is zero. -/
theorem zeroExtend_eq_false_of_ge {n N : Nat} (h : n ≤ N)
    (x : BitState n) (j : Fin N) (hj : n ≤ j.val) :
    zeroExtend h x j = false := by
  simp [zeroExtend, Nat.not_lt.mpr hj]

end BitState

namespace Gate

/-- Rename the external input variables of a source gate. -/
def mapInput {n N w : Nat} (f : Fin n → Fin N) : Gate n w → Gate N w
  | .input i negated => .input (f i) negated
  | .constant value => .constant value
  | .copyGate source => .copyGate source
  | .andGate left right => .andGate left right
  | .orGate left right => .orGate left right

@[simp] theorem mapInput_parents {n N w : Nat} (f : Fin n → Fin N)
    (g : Gate n w) : (g.mapInput f).parents = g.parents := by
  cases g <;> rfl

@[simp] theorem mapInput_eval {n N w : Nat} (f : Fin n → Fin N)
    (g : Gate n w) (y : BitState N) (previous : BitState w) :
    (g.mapInput f).eval y previous = g.eval (fun i => y (f i)) previous := by
  cases g with
  | input i negated => cases negated <;> rfl
  | constant value => rfl
  | copyGate source => rfl
  | andGate left right => rfl
  | orGate left right => rfl

end Gate

namespace CircuitLayer

/-- Rename the external input variables used throughout one source layer. -/
def mapInput {n N w : Nat} (layer : CircuitLayer n w)
    (f : Fin n → Fin N) : CircuitLayer N w :=
  fun j => (layer j).mapInput f

@[simp] theorem mapInput_eval {n N w : Nat} (layer : CircuitLayer n w)
    (f : Fin n → Fin N) (y : BitState N) (previous : BitState w) :
    (layer.mapInput f).eval y previous =
      layer.eval (fun i => y (f i)) previous := by
  funext j
  exact Gate.mapInput_eval f (layer j) y previous

end CircuitLayer

namespace Circuit

/-- Rename every external input of a source circuit. -/
def mapInput {n N w : Nat} (C : Circuit n w)
    (f : Fin n → Fin N) : Circuit N w where
  layers := C.layers.map fun layer => layer.mapInput f
  output := C.output

@[simp] theorem mapInput_layers_length {n N w : Nat} (C : Circuit n w)
    (f : Fin n → Fin N) : (C.mapInput f).layers.length = C.layers.length := by
  simp [mapInput]

@[simp] theorem mapInput_size {n N w : Nat} (C : Circuit n w)
    (f : Fin n → Fin N) : (C.mapInput f).size = C.size := by
  simp [Circuit.size]

/-- Input renaming preserves the exact Boolean function after precomposition. -/
theorem mapInput_eval {n N w : Nat} (C : Circuit n w)
    (f : Fin n → Fin N) (y : BitState N) :
    (C.mapInput f).eval y = C.eval (fun i => y (f i)) := by
  unfold Circuit.eval Circuit.finalState
  simp only [mapInput, List.foldl_map]
  generalize BitState.zero w = initial
  induction C.layers generalizing initial with
  | nil => rfl
  | cons layer layers ih =>
      simp only [List.foldl_cons]
      rw [CircuitLayer.mapInput_eval]
      exact ih (layer.eval (fun i => y (f i)) initial)

/-- Pad a source circuit to a larger input length; the new suffix is ignored. -/
def padInput {n N w : Nat} (C : Circuit n w) (h : n ≤ N) : Circuit N w :=
  C.mapInput (Fin.castLE h)

/-- Padding followed by zero extension computes the original function. -/
@[simp] theorem padInput_eval_zeroExtend {n N w : Nat} (C : Circuit n w)
    (h : n ≤ N) (x : BitState n) :
    (C.padInput h).eval (BitState.zeroExtend h x) = C.eval x := by
  rw [padInput, mapInput_eval]
  congr 2
  funext i
  exact BitState.zeroExtend_castLE h x i

/-- Relabel vertices of an input-renamed circuit by their unchanged layer and
position in the original circuit. -/
def mapInputVertexEmbedding {n N w : Nat} (C : Circuit n w)
    (f : Fin n → Fin N) : (C.mapInput f).Vertex ↪ C.Vertex where
  toFun := fun v =>
    (⟨v.1.val, by simpa [mapInput] using v.1.isLt⟩, v.2)
  inj' := by
    intro u v huv
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun z => z.1.val) huv
    · simpa using congrArg (fun z => z.2) huv

/-- A dependency edge is unchanged by external-input renaming. -/
theorem mapInput_edge_embedding {n N w : Nat} (C : Circuit n w)
    (f : Fin n → Fin N) {u v : (C.mapInput f).Vertex}
    (hedge : (C.mapInput f).layeredGraph.edge u v) :
    C.layeredGraph.edge (C.mapInputVertexEmbedding f u)
      (C.mapInputVertexEmbedding f v) := by
  rcases hedge with ⟨hlayer, hparent⟩
  constructor
  · exact hlayer
  · let targetLayer : Fin C.layers.length :=
      ⟨v.1.val, by simpa [mapInput] using v.1.isLt⟩
    have huPosition : (C.mapInputVertexEmbedding f u).2 = u.2 := rfl
    have hvPosition : (C.mapInputVertexEmbedding f v).2 = v.2 := rfl
    have hvLayer : (C.mapInputVertexEmbedding f v).1 = targetLayer := by
      apply Fin.ext
      rfl
    rw [huPosition, hvPosition, hvLayer]
    simpa [mapInput, CircuitLayer.mapInput, targetLayer] using hparent

/-- After the explicit vertex relabelling, an input-renamed dependency graph
is a spanning subgraph of the original dependency graph. -/
theorem mapInput_graph_map_le {n N w : Nat} (C : Circuit n w)
    (f : Fin n → Fin N) :
    (C.mapInput f).layeredGraph.toSimpleGraph.map
        (C.mapInputVertexEmbedding f) ≤ C.layeredGraph.toSimpleGraph := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨u, v, huv, rfl, rfl⟩
  rcases huv with huv | hvu
  · exact Or.inl (C.mapInput_edge_embedding f huv)
  · exact Or.inr (C.mapInput_edge_embedding f hvu)

/-- Adding ignored source inputs preserves planarity. -/
theorem mapInput_isPlanar {n N w : Nat} (C : Circuit n w)
    (f : Fin n → Fin N)
    (hplanar : OrientableGenus.IsPlanar C.layeredGraph.toSimpleGraph) :
    OrientableGenus.IsPlanar (C.mapInput f).layeredGraph.toSimpleGraph := by
  exact OrientableGenus.isPlanar_of_map_le
    (C.mapInputVertexEmbedding f) (C.mapInput_graph_map_le f) hplanar

/-- In particular, padding a planar source circuit keeps it planar. -/
theorem padInput_isPlanar {n N w : Nat} (C : Circuit n w) (h : n ≤ N)
    (hplanar : OrientableGenus.IsPlanar C.layeredGraph.toSimpleGraph) :
    OrientableGenus.IsPlanar (C.padInput h).layeredGraph.toSimpleGraph :=
  C.mapInput_isPlanar (Fin.castLE h) hplanar

end Circuit

namespace ACCGate

/-- Fix every external input outside the first `n` variables to zero. -/
def restrictInput {m n N s : Nat} (h : n ≤ N) :
    ACCGate m N s → ACCGate m n s
  | .input i =>
      if hi : i.val < n then .input ⟨i.val, hi⟩ else .constant false
  | .constant value => .constant value
  | .notGate source => .notGate source
  | .andGate inputs => .andGate inputs
  | .orGate inputs => .orGate inputs
  | .modGate inputs => .modGate inputs

/-- Restriction agrees with evaluation on the zero-extended input. -/
@[simp] theorem restrictInput_eval {m n N s : Nat} (h : n ≤ N)
    (g : ACCGate m N s) (x : BitState n) (previous : BitState s) :
    (g.restrictInput h).eval x previous =
      g.eval (BitState.zeroExtend h x) previous := by
  cases g with
  | input i =>
      by_cases hi : i.val < n
      · simp [restrictInput, ACCGate.eval, hi, BitState.zeroExtend]
      · simp [restrictInput, ACCGate.eval, hi, BitState.zeroExtend]
  | constant value => simp [restrictInput, ACCGate.eval]
  | notGate source => simp [restrictInput, ACCGate.eval]
  | andGate inputs => simp [restrictInput, ACCGate.eval]
  | orGate inputs => simp [restrictInput, ACCGate.eval]
  | modGate inputs => simp [restrictInput, ACCGate.eval]

end ACCGate

namespace ACmLayer

/-- Restrict all external inputs of one target-circuit layer. -/
def restrictInput {m n N s : Nat} (layer : ACmLayer m N s)
    (h : n ≤ N) : ACmLayer m n s :=
  fun j => (layer j).restrictInput h

@[simp] theorem restrictInput_eval {m n N s : Nat} (layer : ACmLayer m N s)
    (h : n ≤ N) (x : BitState n) (previous : BitState s) :
    (layer.restrictInput h).eval x previous =
      layer.eval (BitState.zeroExtend h x) previous := by
  funext j
  exact ACCGate.restrictInput_eval h (layer j) x previous

end ACmLayer

namespace ACmCircuit

/-- Fix the unused suffix inputs of a target circuit to zero. -/
def restrictInput {m n N s : Nat} (C : ACmCircuit m N s)
    (h : n ≤ N) : ACmCircuit m n s where
  layers := C.layers.map fun layer => layer.restrictInput h
  output := C.output

@[simp] theorem restrictInput_depth {m n N s : Nat} (C : ACmCircuit m N s)
    (h : n ≤ N) : (C.restrictInput h).depth = C.depth := by
  simp [restrictInput, depth]

@[simp] theorem restrictInput_size {m n N s : Nat} (C : ACmCircuit m N s)
    (h : n ≤ N) : (C.restrictInput h).size = C.size := by
  simp [restrictInput, size]

/-- Restriction preserves the exact value on zero-extended inputs. -/
@[simp] theorem restrictInput_eval {m n N s : Nat} (C : ACmCircuit m N s)
    (h : n ≤ N) (x : BitState n) :
    (C.restrictInput h).eval x = C.eval (BitState.zeroExtend h x) := by
  unfold eval finalState restrictInput
  simp only [List.foldl_map]
  generalize BitState.zero s = initial
  induction C.layers generalizing initial with
  | nil => rfl
  | cons layer layers ih =>
      simp only [List.foldl_cons]
      rw [ACmLayer.restrictInput_eval]
      exact ih (layer.eval (BitState.zeroExtend h x) initial)

end ACmCircuit

end Allender
