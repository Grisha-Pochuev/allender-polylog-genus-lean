import Allender

/-!
# Axiom audit

These commands print the trusted dependencies of the central checked lemmas during
compilation. No theorem below may depend on `sorryAx`.
-/

#print axioms Allender.BitState.card
#print axioms Allender.Rel.comp_assoc
#print axioms Allender.Rel.composeList_append
#print axioms Allender.Rel.chain_iff_composeList
#print axioms Allender.CircuitLayer.transition_functional
#print axioms Allender.Circuit.chain_from_zero_to_final
#print axioms Allender.Circuit.composeList_zero_final
#print axioms Allender.Circuit.card_vertex
#print axioms Allender.cutCountBelow_succ_of_not_mem
#print axioms Allender.LayeredDigraph.edge_same_block_of_source_survives
#print axioms Allender.LayeredDigraph.UWalk.endpoint_same_block
#print axioms Allender.LayeredDigraph.no_surviving_walk_across_layer
#print axioms Allender.exists_weightedMedianCut
#print axioms Allender.LayeredDigraph.FiniteConnectedSet.DescendantAfterCut.card_halves
#print axioms Allender.LayeredDigraph.FiniteConnectedSet.exists_medianLayer
#print axioms Allender.HalvingChain.pow_mul_terminal_le
#print axioms Allender.HalvingChain.terminal_eq_zero_of_start_le
#print axioms Allender.card_le_of_positive_cost_sum_le
#print axioms Allender.separator_round_count_bound
#print axioms Allender.card_badTransitions_le
#print axioms Allender.macroblock_count_le_of_cuts
#print axioms Allender.card_stateAssignments
#print axioms Allender.card_stateAssignments_log_le
#print axioms Allender.padding_gap
#print axioms Allender.paddedLength_injective_on_ranges
