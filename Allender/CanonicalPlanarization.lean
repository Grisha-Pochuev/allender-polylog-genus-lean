import Allender.CanonicalComponents
import Allender.LayerSeparationProcess

/-!
# Canonical median-layer separation process

This module constructs the round-by-round process that was previously supplied
abstractly to `LayerSeparationProcess`.

At round `t` the active identifiers are exactly the supports of the actual
nonplanar connected components after the accumulated cuts.  The process deletes
one chosen median layer from each such component.  Every nonplanar component in
the next remainder has a canonical nonplanar parent in the previous remainder,
is contained in that parent, and avoids the parent's newly deleted median
layer.

Together these facts discharge the structural fields of
`LayerSeparationProcess`; no coverage map is assumed.
-/

namespace Allender
namespace LayeredDigraph

open OrientableGenus

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : LayeredDigraph V) [DecidableRel G.edge]

/-- A fixed chosen median of one concrete remainder component. -/
noncomputable def canonicalMedian (cuts : Finset Nat) (s : Finset V) :
    (activeFiniteConnectedSet (G := G) cuts s).MedianLayer :=
  Classical.choice
    (activeFiniteConnectedSet (G := G) cuts s).exists_medianLayer

/-- Median layers selected from all actual nonplanar components of one
remainder. -/
noncomputable def canonicalRoundCuts (cuts : Finset Nat) : Finset Nat := by
  classical
  exact (activeComponentVerts ((G.deleteLayers cuts).toSimpleGraph)).image
    fun s => (canonicalMedian G cuts s).index

/-- Accumulated cuts of the canonical recursion. -/
noncomputable def canonicalCuts : Nat → Finset Nat
  | 0 => ∅
  | t + 1 => canonicalCuts t ∪ canonicalRoundCuts G (canonicalCuts t)

@[simp] theorem canonicalCuts_zero :
    canonicalCuts G 0 = ∅ := rfl

@[simp] theorem canonicalCuts_succ (t : Nat) :
    canonicalCuts G (t + 1) =
      canonicalCuts G t ∪ canonicalRoundCuts G (canonicalCuts G t) := rfl

theorem canonicalCuts_subset_succ (t : Nat) :
    canonicalCuts G t ⊆ canonicalCuts G (t + 1) := by
  intro m hm
  rw [canonicalCuts_succ]
  exact Finset.mem_union_left _ hm

/-- The actual graph remainder after `t` canonical rounds. -/
noncomputable def canonicalRemainder (t : Nat) : SimpleGraph V :=
  (G.deleteLayers (canonicalCuts G t)).toSimpleGraph

/-- Later canonical remainders are spanning subgraphs of earlier ones. -/
theorem canonicalRemainder_mono (t : Nat) :
    canonicalRemainder G (t + 1) ≤ canonicalRemainder G t := by
  exact G.deleteLayers_mono (canonicalCuts_subset_succ G t)

/-- Actual nonplanar-component supports at round `t`. -/
noncomputable def canonicalActive (t : Nat) : Finset (Finset V) :=
  activeComponentVerts (canonicalRemainder G t)

/-- Concrete connected set represented by an identifier at round `t`. -/
noncomputable def canonicalComponent (t : Nat) (s : Finset V) :
    G.FiniteConnectedSet :=
  activeFiniteConnectedSet (G := G) (canonicalCuts G t) s

/-- Chosen median attached to a round component. -/
noncomputable def canonicalMedianAt (t : Nat) (s : Finset V) :
    (canonicalComponent G t s).MedianLayer :=
  canonicalMedian G (canonicalCuts G t) s

/-- The canonical parent identifier of a next-round component. -/
noncomputable def canonicalParent (t : Nat) (s : Finset V) : Finset V :=
  componentVerts
    (parentComponent (canonicalRemainder_mono G t)
      (componentForSupport (canonicalRemainder G (t + 1)) s))

theorem canonicalComponent_verts_of_active {t : Nat} {s : Finset V}
    (hs : s ∈ canonicalActive G t) :
    (canonicalComponent G t s).verts = s := by
  exact activeFiniteConnectedSet_verts (G := G)
    (canonicalCuts G t) hs

/-- The canonical parent of every active child is itself active. -/
theorem canonicalParent_active {t : Nat} {s : Finset V}
    (hs : s ∈ canonicalActive G (t + 1)) :
    canonicalParent G t s ∈ canonicalActive G t := by
  classical
  let Hchild := canonicalRemainder G (t + 1)
  let Hparent := canonicalRemainder G t
  let child : Hchild.ConnectedComponent :=
    componentForSupport Hchild s
  have hchild : child ∈ nonplanarComponents Hchild := by
    exact componentForSupport_mem_nonplanar Hchild hs
  have hparent :
      parentComponent (canonicalRemainder_mono G t) child ∈
        nonplanarComponents Hparent := by
    exact parentComponent_mem_nonplanar
      (canonicalRemainder_mono G t) hchild
  apply (mem_activeComponentVerts_iff Hparent
    (canonicalParent G t s)).2
  exact ⟨parentComponent (canonicalRemainder_mono G t) child,
    hparent, rfl⟩

/-- Every active child support is contained in its canonical parent support. -/
theorem canonicalChild_subset {t : Nat} {s : Finset V}
    (hs : s ∈ canonicalActive G (t + 1)) :
    (canonicalComponent G (t + 1) s).verts ⊆
      (canonicalComponent G t (canonicalParent G t s)).verts := by
  classical
  have hp : canonicalParent G t s ∈ canonicalActive G t :=
    canonicalParent_active G hs
  rw [canonicalComponent_verts_of_active G hs,
    canonicalComponent_verts_of_active G hp]
  intro v hv
  let Hchild := canonicalRemainder G (t + 1)
  let child : Hchild.ConnectedComponent :=
    componentForSupport Hchild s
  have hchildVerts : componentVerts child = s :=
    componentForSupport_verts Hchild hs
  have hvChild : v ∈ child.supp := by
    apply (mem_componentVerts child v).1
    rw [hchildVerts]
    exact hv
  have hvParent :
      v ∈ (parentComponent (canonicalRemainder_mono G t) child).supp :=
    component_supp_subset_parent (canonicalRemainder_mono G t)
      child hvChild
  exact (mem_componentVerts
    (parentComponent (canonicalRemainder_mono G t) child) v).2 hvParent

/-- Every active child avoids the median layer newly selected from its
canonical parent. -/
theorem canonicalChild_avoids {t : Nat} {s : Finset V}
    (hs : s ∈ canonicalActive G (t + 1)) :
    ∀ v ∈ (canonicalComponent G (t + 1) s).verts,
      G.layer v ≠ (canonicalMedianAt G t
        (canonicalParent G t s)).index := by
  classical
  intro v hv hveq
  have hp : canonicalParent G t s ∈ canonicalActive G t :=
    canonicalParent_active G hs
  have hvS : v ∈ s := by
    rw [canonicalComponent_verts_of_active G hs] at hv
    exact hv
  let Hchild := canonicalRemainder G (t + 1)
  let child : Hchild.ConnectedComponent :=
    componentForSupport Hchild s
  have hchildNonplanar : child ∈ nonplanarComponents Hchild :=
    componentForSupport_mem_nonplanar Hchild hs
  have hchildVerts : componentVerts child = s :=
    componentForSupport_verts Hchild hs
  have hvChild : v ∈ child.supp := by
    apply (mem_componentVerts child v).1
    rw [hchildVerts]
    exact hvS
  have hvSurvives : G.layer v ∉ canonicalCuts G (t + 1) :=
    G.nonplanarComponent_survives (canonicalCuts G (t + 1))
      hchildNonplanar hvChild
  apply hvSurvives
  rw [canonicalCuts_succ]
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨canonicalParent G t s, hp, ?_⟩
  simpa [canonicalMedianAt] using hveq.symm

/-- The fully concrete median-layer process for a prescribed number of rounds.
The only numerical hypotheses are the ambient vertex bound and the original
genus budget. -/
noncomputable def canonicalLayerSeparationProcess
    (steps N g : Nat)
    (hN : Fintype.card V ≤ N)
    (hgenus : OrientableGenus.genus G.toSimpleGraph ≤ g) :
    G.LayerSeparationProcess (Finset V) steps N g where
  active := canonicalActive G
  component := canonicalComponent G
  median := canonicalMedianAt G
  parent := canonicalParent G
  initial_size_le := by
    intro s hs
    exact (activeFiniteConnectedSet_card_le
      (G := G) (canonicalCuts G 0) s).trans hN
  active_card_le := by
    intro t ht
    calc
      (canonicalActive G t).card ≤
          OrientableGenus.genus (canonicalRemainder G t) :=
        activeComponentVerts_card_le_genus _
      _ ≤ OrientableGenus.genus G.toSimpleGraph := by
        exact G.genus_deleteLayers_le (canonicalCuts G t)
      _ ≤ g := hgenus
  parent_active := by
    intro t ht s hs
    exact canonicalParent_active G hs
  child_subset := by
    intro t ht s hs
    exact canonicalChild_subset G hs
  child_avoids := by
    intro t ht s hs
    exact canonicalChild_avoids G hs

end LayeredDigraph
end Allender
