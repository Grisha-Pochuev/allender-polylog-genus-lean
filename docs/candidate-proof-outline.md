# Candidate proof outline

This file records the structure of the current prose proof candidate available in the project materials. It is an outline for formalization, not a substitute for the full paper and not an independent validation.

## Proposed route

1. **Delete few whole layers.**  
   For a layered graph with `N` vertices and orientable genus `g`, recursively select median layers of positive-genus connected components. The claimed bound is that deleting at most

   ```text
   g · (⌈log₂ N⌉ + 1)
   ```

   whole layers leaves a planar graph.

2. **Split the circuit into planar pieces.**  
   The surviving intervals between deleted layers form planar macroblocks. Deleted layers act as small boundary gadgets because the circuit width is constant.

3. **Describe each planar block in `ACC⁰`.**  
   Apply Hansen's planar constant-width characterization to the transition relation of each macroblock. The proof must produce one common fixed modulus for all blocks and all input lengths.

4. **Compose the block transitions.**  
   A width-`w` boundary has only `2^w` states. Each macroblock therefore induces a relation on a fixed finite set. The full circuit is the sequential composition of polylogarithmically many such relations.

5. **Control depth and size.**  
   The relation-composition construction must be implemented in constant depth and polynomial size, with all constants independent of input length.

6. **Handle circuit details.**  
   The prose proof separately accounts for input literals on intermediate layers, macroblock boundaries, output negations, and the final size estimate.

## Claimed distinction from the invalid 2005 argument

The candidate route does not attempt to linearly arrange surface handles or assign east/west neighbours to handle connections. Instead, it seeks a recursive layer separator whose count is controlled through component size and genus additivity.

## Formalization map

| Prose step | Lean target |
|---|---|
| fixed-width boundary states | `Allender/FiniteState.lean` |
| transition composition | `Allender/Relation.lean` |
| cut-layer interval invariant | `Allender/LayeredGraph.lean` |
| `O(g log N)` planarization | Stage 3–4, pending |
| Hansen block simulation | Stage 6, pending |
| common modulus | Stage 6, pending |
| polylog relation composition in `ACC⁰` | Stage 7, pending |
| final theorem | Stage 8, pending |

## Central verification risk

The most important unresolved point is not the elementary relation algebra. It is whether the stated median-layer recursion really implies planarity after the claimed number of cuts for the exact graph-genus model, and whether the resulting block simulations compose inside a single `ACC⁰` family. Those claims must be formalized before the proof candidate can be treated as a solution.
