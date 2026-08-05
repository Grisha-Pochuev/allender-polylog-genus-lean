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
#print axioms Allender.LayeredDigraph.blockIndex_succ_of_not_mem
#print axioms Allender.LayeredDigraph.edge_same_block_of_source_survives
