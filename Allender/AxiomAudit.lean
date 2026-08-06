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
#print axioms Allender.chain_from_initial
#print axioms Allender.segmentRelation_iff_eval
#print axioms Allender.segmentRelation_functional
#print axioms Allender.segmentRelation_append
#print axioms Allender.initialState_iff_transition
#print axioms Allender.accept_cons_iff_exists_boundary_states
#print axioms Allender.Circuit.chain_from_zero_to_final
#print axioms Allender.Circuit.composeList_zero_final
#print axioms Allender.Circuit.card_vertex
#print axioms Allender.Circuit.size_eq_card_vertex
#print axioms Allender.ACCGate.eval_input
#print axioms Allender.ACCGate.eval_constant
#print axioms Allender.ACCGate.eval_not
#print axioms Allender.cutCountBelow_succ_of_not_mem
#print axioms Allender.LayeredDigraph.edge_same_block_of_source_survives
#print axioms Allender.LayeredDigraph.toSimpleGraph_adj
#print axioms Allender.LayeredDigraph.deleteLayers_empty_edge_iff
#print axioms Allender.LayeredDigraph.deleteLayers_toSimpleGraph_le
#print axioms Allender.LayeredDigraph.deleteLayers_mono
#print axioms Allender.LayeredDigraph.deleteLayers_union_edge_iff
#print axioms Allender.LayeredDigraph.no_edge_from_cut_vertex
#print axioms Allender.LayeredDigraph.no_edge_to_cut_vertex
#print axioms Allender.OrientableGenus.genus
#print axioms Allender.OrientableGenus.genus_mono
#print axioms Allender.OrientableGenus.genus_eq_sum_components
#print axioms Allender.OrientableGenus.nonplanarComponents_card_le_genus
#print axioms Allender.OrientableGenus.isPlanar_iff_nonplanarComponents_eq_empty
#print axioms Allender.OrientableGenus.genus_deleteLayers_le
#print axioms Allender.LayeredDigraph.UWalk.endpoint_same_block
#print axioms Allender.LayeredDigraph.no_surviving_walk_across_layer
#print axioms Allender.exists_weightedMedianCut
#print axioms Allender.LayeredDigraph.FiniteConnectedSet.DescendantAfterCut.card_halves
#print axioms Allender.LayeredDigraph.FiniteConnectedSet.exists_medianLayer
#print axioms Allender.HalvingChain.pow_mul_terminal_le
#print axioms Allender.HalvingChain.terminal_eq_zero_of_start_le
#print axioms Allender.LayeredDigraph.FiniteConnectedSet.DescendantChain.toHalvingChain
#print axioms Allender.LayeredDigraph.FiniteConnectedSet.DescendantChain.impossible_after_log
#print axioms Allender.ComponentRoundSystem.pow_mul_size_le
#print axioms Allender.ComponentRoundSystem.active_empty_after_log
#print axioms Allender.LayeredDigraph.LayerSeparationProcess.toComponentRoundSystem
#print axioms Allender.LayeredDigraph.LayerSeparationProcess.active_empty_after_log
#print axioms Allender.LayeredDigraph.LayerSeparationProcess.roundCuts_card_le
#print axioms Allender.LayeredDigraph.LayerSeparationProcess.selectedCounts_sum_le_log
#print axioms Allender.LayeredDigraph.LayerSeparationProcess.cumulativeCuts_card_le_mul
#print axioms Allender.LayeredDigraph.LayerSeparationProcess.RoundCoverage.nonplanar_card_le_active_card
#print axioms Allender.LayeredDigraph.LayerSeparationProcess.PlanarizationCoverage.final_isPlanar
#print axioms Allender.LayeredDigraph.LayerSeparationProcess.PlanarizationCoverage.final_cuts_card_le
#print axioms Allender.card_le_of_positive_cost_sum_le
#print axioms Allender.separator_round_count_bound
#print axioms Allender.card_badTransitions_le
#print axioms Allender.macroblock_count_le_of_cuts
#print axioms Allender.flatten_macroblockTags
#print axioms Allender.nil_not_mem_macroblockTags
#print axioms Allender.macroblock_isChain
#print axioms Allender.macroblocks_separated
#print axioms Allender.card_stateAssignments
#print axioms Allender.card_stateAssignments_log_le
#print axioms Allender.padding_gap
#print axioms Allender.paddedLength_injective_on_ranges
