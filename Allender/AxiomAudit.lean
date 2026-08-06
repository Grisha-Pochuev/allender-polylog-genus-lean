import Allender

/-!
# Axiom audit

These commands print the trusted dependencies of the central checked lemmas during
compilation.  No theorem below is allowed to depend on `sorryAx`.
-/

#print axioms Allender.BitState.card
#print axioms Allender.Rel.comp_assoc
#print axioms Allender.Rel.composeList_append
#print axioms Allender.Rel.Functional.comp
#print axioms Allender.cutCountBelow_succ_of_not_mem
#print axioms Allender.LayeredDigraph.edge_same_block_of_source_survives
#print axioms Allender.HalvingChain.pow_mul_terminal_le
#print axioms Allender.HalvingChain.terminal_eq_zero_of_start_le
#print axioms Allender.exists_weightedMedianCut
#print axioms Allender.LayeredDigraph.UWalk.endpoint_same_block
#print axioms Allender.LayeredDigraph.no_surviving_walk_across_layer
#print axioms Allender.LayeredDigraph.FiniteConnectedSet.DescendantAfterCut.card_halves
#print axioms Allender.LayeredDigraph.FiniteConnectedSet.exists_medianLayer
