module

public import Utilities.Subdivision.CensusSpanningForest
public import DraismaVargas.Infrastructure.GraphContraction
public import Utilities.Subdivision.UnitSubdivisionPresentation

@[expose] public section

/-!
# Connectedness, in the census's own language

`Utilities.Subdivision.CensusSpanningForest` produces a spanning
tree once connectedness is presented as "the full union-find fold has one
class".  A `CFGraph` states connectedness instead as
`graph_connected`: no proper nonempty vertex subset is closed under adjacency.
This file is the translation, and nothing else.  `MemberSeedExists` uses it to
show that every full-dimensional member has a target occurrence whose source
fibre is a forest.

## What is proved

* `adjInList_univ_of_num_edges_pos` -- an occurrence between two vertices is a
  census adjacency between their indices.
* `reachIn_univ_of_graph_connected` -- hence every pair of indices is reachable
  through all slots.
* `card_image_compFold_univ_eq_one` -- hence the full fold has exactly one
  class, which is the hypothesis `exists_spanning_tree_card` asks for.
* `exists_spanning_tree_of_graph_connected` -- the two composed: a connected
  `CFGraph` has a census spanning tree, `F.card + 1 = Fintype.card G.V`.

## Scope

Nothing here is about gluing data, target trees or fibres; it is graph theory
about one `CFGraph` and its `UnitSubdivisionPresentation.core`.
-/

namespace DraismaVargas.Infrastructure.CensusConnected

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral

/-- An occurrence joining two vertices is a census adjacency between their
canonical indices. -/
theorem adjInList_univ_of_num_edges_pos (G : CFGraph) {v w : G.V}
    (h : 0 < num_edges G v w) :
    AdjInList (UnitSubdivisionPresentation.core G)
      (edgeList (Finset.univ : Finset (Fin G.edges.card)))
      (UnitSubdivisionPresentation.vertexEquiv G v)
      (UnitSubdivisionPresentation.vertexEquiv G w) := by
  classical
  obtain ⟨pair, hmem, hends⟩ :=
    GraphContraction.exists_mem_edges_of_num_edges_pos G v w h
  let occurrence : G.edges := ⟨pair, ⟨0, Multiset.count_pos.mpr hmem⟩⟩
  have hocc : (occurrence : G.V × G.V) = pair := rfl
  refine ⟨UnitSubdivisionPresentation.edgeEquiv G occurrence,
    (mem_edgeList _ _).mpr (Finset.mem_univ _), ?_⟩
  rw [UnitSubdivisionPresentation.core_tail_edgeEquiv,
    UnitSubdivisionPresentation.core_head_edgeEquiv, hocc]
  rcases hends with hpair | hpair
  · exact Or.inl ⟨by rw [hpair], by rw [hpair]⟩
  · exact Or.inr ⟨by rw [hpair], by rw [hpair]⟩

/-- A connected `CFGraph` has all of its vertex indices mutually reachable
through the full slot set. -/
theorem reachIn_univ_of_graph_connected (G : CFGraph) (hConnected : graph_connected G)
    (x y : Fin (Fintype.card G.V)) :
    ReachIn (UnitSubdivisionPresentation.core G) Finset.univ x y := by
  classical
  by_contra hnot
  set S : Finset G.V := Finset.univ.filter fun w ↦
    ReachIn (UnitSubdivisionPresentation.core G) Finset.univ x
      (UnitSubdivisionPresentation.vertexEquiv G w) with hS
  have hxS : (UnitSubdivisionPresentation.vertexEquiv G).symm x ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [Equiv.apply_symm_apply]
    exact (reachIn_equivalence (UnitSubdivisionPresentation.core G) Finset.univ).refl x
  have hyS : (UnitSubdivisionPresentation.vertexEquiv G).symm y ∉ S := by
    intro hmem
    apply hnot
    have h := (Finset.mem_filter.mp hmem).2
    rwa [Equiv.apply_symm_apply] at h
  obtain ⟨v, hv, w, hw, hpos⟩ := hConnected S
    ⟨(UnitSubdivisionPresentation.vertexEquiv G).symm x,
      (UnitSubdivisionPresentation.vertexEquiv G).symm y, hxS, hyS⟩
  exact hw (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    ((Finset.mem_filter.mp hv).2).tail (adjInList_univ_of_num_edges_pos G hpos)⟩)

/-- Connectedness in the census's own language: the full union-find fold has
exactly one class. -/
theorem card_image_compFold_univ_eq_one (G : CFGraph) (hConnected : graph_connected G) :
    (Finset.image (compFold (UnitSubdivisionPresentation.core G) Finset.univ)
      Finset.univ).card = 1 := by
  classical
  have hpos : 0 < Fintype.card G.V := Fintype.card_pos
  let base : Fin (Fintype.card G.V) := ⟨0, hpos⟩
  refine Finset.card_eq_one.mpr
    ⟨compFold (UnitSubdivisionPresentation.core G) Finset.univ base, ?_⟩
  refine Finset.eq_singleton_iff_unique_mem.mpr
    ⟨Finset.mem_image_of_mem _ (Finset.mem_univ base), ?_⟩
  intro z hz
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hz
  exact (compFold_iff (UnitSubdivisionPresentation.core G) Finset.univ u base).mpr
    (reachIn_univ_of_graph_connected G hConnected u base)

/-- **A connected `CFGraph` has a census spanning tree.** -/
theorem exists_spanning_tree_of_graph_connected (G : CFGraph)
    (hConnected : graph_connected G) :
    ∃ F : Finset (Fin G.edges.card),
      IsForest (UnitSubdivisionPresentation.core G) F ∧
        F.card + 1 = Fintype.card G.V :=
  CensusSpanningForest.exists_spanning_tree_card (UnitSubdivisionPresentation.core G)
    (card_image_compFold_univ_eq_one G hConnected)

end DraismaVargas.Infrastructure.CensusConnected
