module

public import Utilities.Foundations.InducedSubgraph
public import Utilities.Subdivision.LeafPruning
public import Utilities.Subdivision.LeafReduction
public import Utilities.Subdivision.SubdivisionGraph

@[expose] public section

/-!
# Deleting pendant trees: from a graph to an induced subgraph

This module proves the **pendant-deletion pushforward**

> `BNExists G r d → BNExists (inducedSubgraph G S hS) r d`

for a connected `G` and a vertex set `S` whose induced subgraph has the genus
of `G`.  It is needed when a construction produces a Brill--Noether pencil on a
graph *with* pendant trees attached, while the graph of interest is the one
with those trees removed.  This happens in the Draisma--Vargas construction
(Draisma--Vargas Part I, arXiv:1909.12924), whose tropical morphisms are
defined on tropical modifications of a metric graph, that is, on the graph
with dangling trees attached.  This module moves the pencil across the
deletion.

## What is here

* `vertex_degree_eq_card_filter_incident` — degree as the number of incident
  occurrences, for a loopless multigraph.  A local copy: the corresponding
  lemma of `ChipFiringWithLean.Basic` is `private`.
* `exists_leaf_outside` — **the counting lemma**.  `G` connected, `S`
  nonempty, `genus (inducedSubgraph G S) = genus G`, some vertex outside `S`:
  then some vertex outside `S` has degree one.  Edges touching
  `T = univ \ S` number exactly `|T|`, so the degree sum over `T` is
  `|T| + |E(T,T)| < 2|T|` as soon as one edge crosses, which connectivity
  supplies; degree zero is impossible for the same reason.
* `laplacianEquiv_inducedSubgraph_deleteLeaf` — the reindexing
  `LaplacianEquiv (inducedSubgraph (deleteLeaf G leaf h) S' hS')
    (inducedSubgraph G S hS)` for a leaf outside `S`.  Nothing is deleted
  twice: `S'` is the same vertex set read in the pruned graph.
* `bnExists_deleteLeaf_iff` — the one-leaf step **in both directions**, for
  every rank and degree, composed from
  `LeafPruning.laplacianEquiv_deleteLeaf_addLeaf` and
  `LeafExtension.bnExists_addLeaf_iff`.  `LeafPruning` itself records only the
  lifting direction, in rank one (`bnExists_rank_one_of_deleteLeaf`).
* `bnExists_induce_iff_of_genus_eq` and `bnExists_induce_of_genus_eq` — the
  strong induction on `Fintype.card G.V`.  **The induced subgraph's own
  connectivity is not a hypothesis**: the induction carries only
  connectivity of `G` and the genus equality, and both are preserved by
  `deleteLeaf` (`LeafReduction.graph_connected_deleteLeaf`, `genus_deleteLeaf`).
* `Spec.restrict` and `laplacianEquiv_restrict` — a `SubdivisionGraph.Spec`
  restricted to a set `K` of core vertices and a set `L` of slots, together
  with its identification with the induced subgraph of `spec.graph` on the
  kept core vertices and the interiors of the kept slots.  The identification
  needs exactly one separation hypothesis beyond "a kept slot has kept
  endpoints": a *dropped* slot must not survive in the induced subgraph, and
  the only way it could is by having length one and two kept endpoints.

## Scope

Nothing here mentions a gluing datum, a dangling occurrence or a contraction
class: the statements are about graphs, induced subgraphs and subdivision
specifications only.
-/

namespace DraismaVargas.Infrastructure.PendantDeletion

open Utilities
open Utilities.Certificate

universe u v

/-! ## 1.  Degree as a count of incident occurrences -/

section Degree

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Summing the pair multiplicities `num_edges G v u` over `u` counts each
occurrence at `v` exactly once, provided no occurrence is a loop.  A local
copy of the `private` `degree_eq_total_flow` of `ChipFiringWithLean.Basic`. -/
private theorem sum_card_filter_pair (v : V) (s : Multiset (V × V))
    (hLoopless : ∀ e ∈ s, e.1 ≠ e.2) :
    (∑ u : V, Multiset.card (s.filter fun e ↦ e = (v, u) ∨ e = (u, v)))
      = Multiset.card (s.filter fun e ↦ e.1 = v ∨ e.2 = v) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons head tail ih =>
    have hTail : ∀ e ∈ tail, e.1 ≠ e.2 := fun e he ↦
      hLoopless e (Multiset.mem_cons_of_mem he)
    have hHead : head.1 ≠ head.2 := hLoopless head (Multiset.mem_cons_self head tail)
    simp only [Multiset.filter_cons, Multiset.card_add, Finset.sum_add_distrib]
    rw [ih hTail]
    have hSingle :
        (∑ u : V, Multiset.card
            (if head = (v, u) ∨ head = (u, v) then ({head} : Multiset (V × V)) else 0))
          = Multiset.card
            (if head.1 = v ∨ head.2 = v then ({head} : Multiset (V × V)) else 0) := by
      obtain ⟨x, y⟩ := head
      simp only at hHead
      by_cases hx : x = v
      · subst hx
        have hyx : y ≠ x := fun h ↦ hHead h.symm
        rw [ite_eq_left (Or.inl rfl)]
        rw [Finset.sum_eq_single y]
        · simp
        · intro u _ hu
          have : y ≠ u := fun h ↦ hu h.symm
          simp [Prod.mk.injEq, this, hyx]
        · simp
      · by_cases hy : y = v
        · subst hy
          rw [ite_eq_left (Or.inr rfl)]
          rw [Finset.sum_eq_single x]
          · simp
          · intro u _ hu
            have : x ≠ u := fun h ↦ hu h.symm
            simp [Prod.mk.injEq, this, hx]
          · simp
        · simp [Prod.mk.injEq, hx, hy]
    omega

/-- **Degree is the number of incident occurrences.**  For any loopless
multigraph, `vertex_degree G v` is the number of entries of `G.edges` one of
whose two slots is `v`. -/
theorem vertex_degree_eq_card_filter_incident (G : CFGraph.{u}) (v : G.V) :
    vertex_degree G v
      = (Multiset.card (G.edges.filter fun e ↦ e.1 = v ∨ e.2 = v) : ℤ) := by
  classical
  have hLoopless : ∀ e ∈ G.edges, e.1 ≠ e.2 := by
    intro e he hEq
    refine G.loopless e.1 ?_
    rwa [show (e.1, e.1) = e from Prod.ext rfl hEq]
  calc vertex_degree G v
      = ((∑ u : G.V, num_edges G v u : ℕ) : ℤ) := by
        rw [Nat.cast_sum]
        rfl
    _ = (Multiset.card (G.edges.filter fun e ↦ e.1 = v ∨ e.2 = v) : ℤ) := by
        rw [show (∑ u : G.V, num_edges G v u)
            = Multiset.card (G.edges.filter fun e ↦ e.1 = v ∨ e.2 = v) from
          sum_card_filter_pair v G.edges hLoopless]

/-- Looplessness of a `CFGraph` in the occurrence form the counts below
use. -/
theorem edges_fst_ne_snd (G : CFGraph.{u}) : ∀ e ∈ G.edges, e.1 ≠ e.2 := by
  intro e he hEq
  exact G.loopless e.1 (by rw [show e = (e.1, e.1) from Prod.ext rfl hEq.symm] at he; exact he)

end Degree

/-! ## 2.  The counting lemma -/

section Counting

variable {V : Type u} [DecidableEq V]

/-- Double counting: summing, over `v ∈ T`, the occurrences incident to `v`
counts the first endpoints in `T` plus the second endpoints in `T`, provided
no occurrence is a loop. -/
theorem sum_card_filter_incident (E : Multiset (V × V))
    (hLoopless : ∀ e ∈ E, e.1 ≠ e.2) (T : Finset V) :
    ∑ v ∈ T, Multiset.card (E.filter fun e ↦ e.1 = v ∨ e.2 = v) =
      Multiset.card (E.filter fun e ↦ e.1 ∈ T) +
        Multiset.card (E.filter fun e ↦ e.2 ∈ T) := by
  classical
  induction E using Multiset.induction_on with
  | empty => simp
  | cons e E ih =>
      have hE : ∀ f ∈ E, f.1 ≠ f.2 := fun f hf ↦ hLoopless f (Multiset.mem_cons_of_mem hf)
      have he : e.1 ≠ e.2 := hLoopless e (Multiset.mem_cons_self _ _)
      simp only [Multiset.filter_cons, Multiset.card_add, Finset.sum_add_distrib, ih hE]
      have hsingle :
          ∑ v ∈ T, Multiset.card
              (if e.1 = v ∨ e.2 = v then ({e} : Multiset (V × V)) else 0) =
            Multiset.card (if e.1 ∈ T then ({e} : Multiset (V × V)) else 0) +
              Multiset.card (if e.2 ∈ T then ({e} : Multiset (V × V)) else 0) := by
        have h1 : ∀ v ∈ T, Multiset.card
            (if e.1 = v ∨ e.2 = v then ({e} : Multiset (V × V)) else 0) =
            (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0) := by
          intro v _
          by_cases h1 : e.1 = v <;> by_cases h2 : e.2 = v <;> simp [h1, h2]
          exact he (h1.trans h2.symm)
        rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
        have hA : ∀ w : V, ∑ v ∈ T, (if w = v then 1 else 0) =
            Multiset.card (if w ∈ T then ({e} : Multiset (V × V)) else 0) := by
          intro w
          by_cases hw : w ∈ T
          · rw [Finset.sum_eq_single w (fun v _ hv ↦ by simp [Ne.symm hv]) (fun h ↦ absurd hw h)]
            simp [hw]
          · rw [Finset.sum_eq_zero (fun v hv ↦ by
                have : w ≠ v := fun h ↦ hw (h ▸ hv)
                simp [this])]
            simp [hw]
        rw [hA e.1, hA e.2]
      omega

omit [DecidableEq V] in
/-- Inclusion--exclusion on multiset filters, with the two one-sided terms. -/
theorem card_filter_or_eq (E : Multiset (V × V)) (p q : V × V → Prop)
    [DecidablePred p] [DecidablePred q] :
    Multiset.card (E.filter fun e ↦ p e ∨ q e) +
        Multiset.card (E.filter fun e ↦ p e ∧ q e) =
      Multiset.card (E.filter p) + Multiset.card (E.filter q) := by
  classical
  induction E using Multiset.induction_on with
  | empty => simp
  | cons e E ih =>
      simp only [Multiset.filter_cons, Multiset.card_add]
      by_cases hp : p e <;> by_cases hq : q e <;> simp [hp, hq] <;> omega

/-- A crossing occurrence makes the "or" filter strictly larger than the
"and" filter. -/
theorem card_filter_and_lt_card_filter_or (E : Multiset (V × V)) (p q : V × V → Prop)
    [DecidablePred p] [DecidablePred q] {e : V × V} (he : e ∈ E)
    (hcross : (p e ∧ ¬ q e) ∨ (¬ p e ∧ q e)) :
    Multiset.card (E.filter fun e ↦ p e ∧ q e) <
      Multiset.card (E.filter fun e ↦ p e ∨ q e) := by
  classical
  induction E using Multiset.induction_on with
  | empty => simp at he
  | cons f E ih =>
      simp only [Multiset.filter_cons, Multiset.card_add]
      rcases Multiset.mem_cons.mp he with rfl | hmem
      · have hOr : p e ∨ q e := by tauto
        have hAnd : ¬ (p e ∧ q e) := by tauto
        have hle : Multiset.card (E.filter fun e ↦ p e ∧ q e) ≤
            Multiset.card (E.filter fun e ↦ p e ∨ q e) :=
          Multiset.card_le_card (Multiset.monotone_filter_right _ (fun _ h ↦ Or.inl h.1))
        simp [hOr, hAnd]
        omega
      · have := ih hmem
        by_cases hp : p f <;> by_cases hq : q f <;> simp [hp, hq] <;> omega

end Counting

/-- **The counting lemma.**  A connected graph whose induced subgraph on a
nonempty proper vertex subset has the same genus has a degree-one vertex
outside that subset.

The induced subgraph's own connectivity is *not* used. -/
theorem exists_leaf_outside (G : CFGraph.{u}) (S : Finset G.V) (hS : S.Nonempty)
    (hG : graph_connected G)
    (hGenus : genus (inducedSubgraph G S hS) = genus G)
    (hT : ∃ v, v ∉ S) :
    ∃ v, v ∉ S ∧ vertex_degree G v = 1 := by
  classical
  obtain ⟨t, ht⟩ := hT
  obtain ⟨s, hs⟩ := id hS
  set T : Finset G.V := Finset.univ \ S with hTdef
  have hLoopless := edges_fst_ne_snd G
  have hEdges := inducedSubgraph_edge_card_eq_filter G S hS
  have hVertices := inducedSubgraph_vertex_card G S hS
  have hTcard : T.card = Fintype.card G.V - S.card := Finset.card_univ_sdiff S
  have hScard : S.card ≤ Fintype.card G.V := Finset.card_le_univ S
  have hSplit := congrArg Multiset.card
    (Multiset.filter_add_not (fun e : G.V × G.V ↦ e.1 ∈ S ∧ e.2 ∈ S) G.edges)
  rw [Multiset.card_add] at hSplit
  have hGenusNat : Multiset.card (G.edges.filter fun e ↦ ¬ (e.1 ∈ S ∧ e.2 ∈ S)) = T.card := by
    unfold genus at hGenus
    rw [hEdges, hVertices] at hGenus
    have h1 : Multiset.card G.edges ≥ Multiset.card (G.edges.filter fun e ↦ e.1 ∈ S ∧ e.2 ∈ S) :=
      Multiset.card_le_card (Multiset.filter_le _ _)
    omega
  have hDeg : ∑ v ∈ T, vertex_degree G v =
      ((Multiset.card (G.edges.filter fun e ↦ e.1 ∈ T) +
        Multiset.card (G.edges.filter fun e ↦ e.2 ∈ T) : ℕ) : ℤ) := by
    rw [Finset.sum_congr rfl fun v _ ↦ vertex_degree_eq_card_filter_incident G v,
      ← Nat.cast_sum, sum_card_filter_incident G.edges hLoopless T]
  have hMemT : ∀ v, v ∈ T ↔ v ∉ S := by intro v; simp [hTdef]
  have hIE := card_filter_or_eq G.edges (fun e ↦ e.1 ∈ T) (fun e ↦ e.2 ∈ T)
  have hOrEq : (G.edges.filter fun e ↦ e.1 ∈ T ∨ e.2 ∈ T) =
      G.edges.filter fun e ↦ ¬ (e.1 ∈ S ∧ e.2 ∈ S) := by
    apply Multiset.filter_congr
    intro e _
    rw [hMemT, hMemT, not_and_or]
  obtain ⟨v, hv, w, hw, hvw⟩ := hG S ⟨s, t, hs, ht⟩
  have hPos : 0 < Multiset.card (G.edges.filter fun e ↦ e = (v, w) ∨ e = (w, v)) := hvw
  obtain ⟨e, he⟩ := Multiset.card_pos_iff_exists_mem.mp hPos
  rw [Multiset.mem_filter] at he
  have hCross : ((e.1 ∈ T) ∧ ¬ (e.2 ∈ T)) ∨ (¬ (e.1 ∈ T) ∧ (e.2 ∈ T)) := by
    rw [hMemT, hMemT]
    rcases he.2 with rfl | rfl
    · exact Or.inr ⟨not_not.mpr hv, hw⟩
    · exact Or.inl ⟨hw, not_not.mpr hv⟩
  have hLt := card_filter_and_lt_card_filter_or G.edges (fun e ↦ e.1 ∈ T) (fun e ↦ e.2 ∈ T)
    he.1 hCross
  have hSum : ∑ v ∈ T, vertex_degree G v < ∑ _v ∈ T, (2 : ℤ) := by
    rw [hDeg, Finset.sum_const, nsmul_eq_mul]
    rw [hOrEq, hGenusNat] at hIE hLt
    have : Multiset.card (G.edges.filter fun e ↦ e.1 ∈ T) +
        Multiset.card (G.edges.filter fun e ↦ e.2 ∈ T) < T.card * 2 := by omega
    exact_mod_cast this
  obtain ⟨u, huT, hu⟩ := Finset.exists_lt_of_sum_lt hSum
  refine ⟨u, (hMemT u).mp huT, ?_⟩
  have huS : u ∉ S := (hMemT u).mp huT
  obtain ⟨x, hx, y, hy, hxy⟩ := hG {u} ⟨u, s, Finset.mem_singleton_self u,
    fun h ↦ huS (Finset.mem_singleton.mp h ▸ hs)⟩
  have hxu : x = u := Finset.mem_singleton.mp hx
  subst hxu
  have hge : (1 : ℤ) ≤ vertex_degree G x := by
    unfold vertex_degree
    have h1 : (1 : ℤ) ≤ (num_edges G x y : ℤ) := by exact_mod_cast hxy
    exact h1.trans (Finset.single_le_sum (f := fun u ↦ (num_edges G x u : ℤ))
      (fun i _ ↦ Nat.cast_nonneg _) (Finset.mem_univ y))
  omega

/-! ## 2b.  Induced subgraphs, with their vertices named

`(inducedSubgraph G S hS).V` and `{v : G.V // v ∈ S}` are definitionally the
same type, but they are not syntactically the same, and `rw` will not cross
the gap.  The two names below fix a spelling once and for all. -/

section Induced

variable (G : CFGraph.{u}) (S : Finset G.V) (hS : S.Nonempty)

/-- The ambient vertex underlying a vertex of an induced subgraph. -/
def induceVal (x : (inducedSubgraph G S hS).V) : G.V :=
  (x : {v : G.V // v ∈ S}).val

theorem induceVal_mem (x : (inducedSubgraph G S hS).V) :
    induceVal G S hS x ∈ S :=
  (x : {v : G.V // v ∈ S}).property

theorem induceVal_injective : Function.Injective (induceVal G S hS) := by
  intro x y hxy
  exact Subtype.ext hxy

/-- The vertex of the induced subgraph carried by a member of `S`. -/
def induceMk {v : G.V} (hv : v ∈ S) : (inducedSubgraph G S hS).V :=
  (⟨v, hv⟩ : {v : G.V // v ∈ S})

@[simp] theorem induceVal_induceMk {v : G.V} (hv : v ∈ S) :
    induceVal G S hS (induceMk G S hS hv) = v := rfl

/-- Multiplicities in an induced subgraph, in the naming just fixed. -/
@[simp] theorem num_edges_induced (x y : (inducedSubgraph G S hS).V) :
    num_edges (inducedSubgraph G S hS) x y =
      num_edges G (induceVal G S hS x) (induceVal G S hS y) :=
  num_edges_inducedSubgraph G S hS _ _

end Induced

/-! ## 3.  An induced subgraph, read after one leaf deletion -/

section Deletion

variable (G : CFGraph.{u}) (leaf : G.V) (hDegree : vertex_degree G leaf = 1)

/-- The underlying vertex of `G` of a vertex of the pruned graph.  The two
types are definitionally the same subtype; this names the coercion so that the
statements below do not depend on which of the two spellings Lean happens to
display. -/
def unprune (x : (LeafPruning.deleteLeaf G leaf hDegree).V) : G.V :=
  (x : LeafPruning.Remaining G leaf).val

theorem unprune_ne (x : (LeafPruning.deleteLeaf G leaf hDegree).V) :
    unprune G leaf hDegree x ≠ leaf :=
  (x : LeafPruning.Remaining G leaf).property

theorem unprune_injective :
    Function.Injective (unprune G leaf hDegree) := by
  intro x y hxy
  exact Subtype.ext hxy

/-- The vertex of the pruned graph carried by a vertex of `G` other than the
leaf. -/
def prune {v : G.V} (hv : v ≠ leaf) : (LeafPruning.deleteLeaf G leaf hDegree).V :=
  (⟨v, hv⟩ : LeafPruning.Remaining G leaf)

@[simp] theorem unprune_prune {v : G.V} (hv : v ≠ leaf) :
    unprune G leaf hDegree (prune G leaf hDegree hv) = v := rfl

/-- A vertex set of `G` avoiding `leaf`, read as a vertex set of the graph
with `leaf` deleted. -/
noncomputable def restrictSet (S : Finset G.V) :
    Finset (LeafPruning.deleteLeaf G leaf hDegree).V := by
  classical
  exact Finset.univ.filter fun x ↦ unprune G leaf hDegree x ∈ S

@[simp] theorem mem_restrictSet (S : Finset G.V)
    (x : (LeafPruning.deleteLeaf G leaf hDegree).V) :
    x ∈ restrictSet G leaf hDegree S ↔ unprune G leaf hDegree x ∈ S := by
  classical
  rw [restrictSet, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ x)

theorem restrictSet_nonempty {S : Finset G.V} (hS : S.Nonempty)
    (hLeaf : leaf ∉ S) : (restrictSet G leaf hDegree S).Nonempty := by
  obtain ⟨s, hs⟩ := hS
  have hNe : s ≠ leaf := fun hEq ↦ hLeaf (hEq ▸ hs)
  exact ⟨prune G leaf hDegree hNe, by rw [mem_restrictSet, unprune_prune]; exact hs⟩

/-- The two readings of the same vertex set agree as types. -/
noncomputable def restrictVertexEquiv {S : Finset G.V} (hS : S.Nonempty)
    (hLeaf : leaf ∉ S) :
    (inducedSubgraph (LeafPruning.deleteLeaf G leaf hDegree)
        (restrictSet G leaf hDegree S)
        (restrictSet_nonempty G leaf hDegree hS hLeaf)).V ≃
      (inducedSubgraph G S hS).V where
  toFun x := induceMk G S hS
    ((mem_restrictSet G leaf hDegree S _).mp
      (induceVal_mem (LeafPruning.deleteLeaf G leaf hDegree)
        (restrictSet G leaf hDegree S)
        (restrictSet_nonempty G leaf hDegree hS hLeaf) x))
  invFun y := induceMk (LeafPruning.deleteLeaf G leaf hDegree)
    (restrictSet G leaf hDegree S)
    (restrictSet_nonempty G leaf hDegree hS hLeaf)
    (show prune G leaf hDegree
        (fun hEq ↦ hLeaf (hEq ▸ induceVal_mem G S hS y)) ∈
      restrictSet G leaf hDegree S by
      rw [mem_restrictSet, unprune_prune]
      exact induceVal_mem G S hS y)
  left_inv x := induceVal_injective _ _ _ (unprune_injective G leaf hDegree rfl)
  right_inv y := induceVal_injective G S hS rfl

@[simp] theorem induceVal_restrictVertexEquiv {S : Finset G.V} (hS : S.Nonempty)
    (hLeaf : leaf ∉ S)
    (x : (inducedSubgraph (LeafPruning.deleteLeaf G leaf hDegree)
      (restrictSet G leaf hDegree S)
      (restrictSet_nonempty G leaf hDegree hS hLeaf)).V) :
    induceVal G S hS (restrictVertexEquiv G leaf hDegree hS hLeaf x) =
      unprune G leaf hDegree
        (induceVal (LeafPruning.deleteLeaf G leaf hDegree)
          (restrictSet G leaf hDegree S)
          (restrictSet_nonempty G leaf hDegree hS hLeaf) x) := rfl

/-- **The reindexing.**  Deleting a leaf outside `S` does not change the
subgraph induced on `S`. -/
noncomputable def laplacianEquiv_inducedSubgraph_deleteLeaf
    {S : Finset G.V} (hS : S.Nonempty) (hLeaf : leaf ∉ S) :
    LaplacianEquiv
      (inducedSubgraph (LeafPruning.deleteLeaf G leaf hDegree)
        (restrictSet G leaf hDegree S)
        (restrictSet_nonempty G leaf hDegree hS hLeaf))
      (inducedSubgraph G S hS) where
  toEquiv := restrictVertexEquiv G leaf hDegree hS hLeaf
  num_edges_eq := by
    intro x y
    rw [num_edges_induced, num_edges_induced, induceVal_restrictVertexEquiv,
      induceVal_restrictVertexEquiv]
    exact (LeafPruning.num_edges_deleteLeaf G leaf hDegree
      (induceVal (LeafPruning.deleteLeaf G leaf hDegree)
        (restrictSet G leaf hDegree S)
        (restrictSet_nonempty G leaf hDegree hS hLeaf) x)
      (induceVal (LeafPruning.deleteLeaf G leaf hDegree)
        (restrictSet G leaf hDegree S)
        (restrictSet_nonempty G leaf hDegree hS hLeaf) y)).symm

end Deletion

/-! ## 4.  The subgraph induced on everything -/

/-- Inducing on a set that contains every vertex changes nothing. -/
noncomputable def laplacianEquiv_inducedSubgraph_univ (G : CFGraph.{u})
    (S : Finset G.V) (hS : S.Nonempty) (hAll : ∀ v : G.V, v ∈ S) :
    LaplacianEquiv G (inducedSubgraph G S hS) where
  toEquiv :=
    { toFun := fun v ↦ induceMk G S hS (hAll v)
      invFun := fun x ↦ induceVal G S hS x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ induceVal_injective G S hS rfl }
  num_edges_eq := fun _ _ ↦ num_edges_induced G S hS _ _

/-! ## 5.  The one-leaf step, in both directions -/

/-- Brill--Noether existence in every rank and degree is invariant under
deleting a degree-one vertex.  `LeafPruning` records only the lifting direction
(`LeafPruning.bnExists_rank_one_of_deleteLeaf`, rank one); the equivalence is
the composition of `LeafPruning.laplacianEquiv_deleteLeaf_addLeaf` with
`LeafExtension.bnExists_addLeaf_iff`. -/
theorem bnExists_deleteLeaf_iff (G : CFGraph.{u}) (leaf : G.V)
    (hDegree : vertex_degree G leaf = 1) (r d : ℤ) :
    BNExists (LeafPruning.deleteLeaf G leaf hDegree) r d ↔ BNExists G r d :=
  (LeafExtension.bnExists_addLeaf_iff (LeafPruning.deleteLeaf G leaf hDegree)
      (LeafPruning.rootInDeleteLeaf G leaf hDegree) r d).symm.trans
    ((LeafPruning.laplacianEquiv_deleteLeaf_addLeaf G leaf hDegree).bnExists_iff
      r d).symm

/-! ## 6.  The pendant-deletion pushforward -/

private theorem bnExists_induce_aux :
    ∀ bound : ℕ, ∀ (G : CFGraph.{u}) (S : Finset G.V) (hS : S.Nonempty),
      Fintype.card G.V = bound → graph_connected G →
      genus (inducedSubgraph G S hS) = genus G →
      ∀ r d : ℤ, (BNExists G r d ↔ BNExists (inducedSubgraph G S hS) r d) := by
  intro bound
  induction bound using Nat.strong_induction_on with
  | _ bound ih =>
    intro G S hS hCard hConnected hGenus r d
    by_cases hAll : ∀ v : G.V, v ∈ S
    · exact (laplacianEquiv_inducedSubgraph_univ G S hS hAll).bnExists_iff r d
    · obtain ⟨outside, hOutside⟩ := not_forall.mp hAll
      obtain ⟨leaf, hLeaf, hDegree⟩ :=
        exists_leaf_outside G S hS hConnected hGenus ⟨outside, hOutside⟩
      set G' := LeafPruning.deleteLeaf G leaf hDegree with hG'
      have hS' : (restrictSet G leaf hDegree S).Nonempty :=
        restrictSet_nonempty G leaf hDegree hS hLeaf
      have hEquiv := laplacianEquiv_inducedSubgraph_deleteLeaf G leaf hDegree hS hLeaf
      have hSmaller : Fintype.card G'.V < bound := by
        rw [← hCard]
        exact LeafReduction.card_vertices_deleteLeaf_lt G leaf hDegree
      have hConnected' : graph_connected G' :=
        LeafReduction.graph_connected_deleteLeaf G leaf hConnected hDegree
      have hGenusDelete : genus G' = genus G :=
        LeafReduction.genus_deleteLeaf G leaf hDegree
      have hGenus' : genus (inducedSubgraph G' (restrictSet G leaf hDegree S) hS')
          = genus G' := by
        rw [hEquiv.genus_eq.symm.trans hGenus, hGenusDelete]
      have hInner := ih (Fintype.card G'.V) hSmaller G'
        (restrictSet G leaf hDegree S) hS' rfl hConnected' hGenus' r d
      calc BNExists G r d
          ↔ BNExists G' r d := (bnExists_deleteLeaf_iff G leaf hDegree r d).symm
        _ ↔ BNExists (inducedSubgraph G' (restrictSet G leaf hDegree S) hS') r d :=
            hInner
        _ ↔ BNExists (inducedSubgraph G S hS) r d := hEquiv.bnExists_iff r d

/-- **The pendant-deletion pushforward, as an equivalence.**  On a connected
graph, Brill--Noether existence in every rank and degree is carried by the
subgraph induced on any nonempty vertex set of the same genus.

The hypotheses are exactly the ones the induction consumes: `G` connected and
the genus equality.  The induced subgraph is *not* assumed connected — the
recursion only ever needs a leaf of the ambient graph lying outside `S`, and
both hypotheses are preserved by `deleteLeaf`. -/
theorem bnExists_induce_iff_of_genus_eq (G : CFGraph.{u}) (S : Finset G.V)
    (hS : S.Nonempty) (hConnected : graph_connected G)
    (hGenus : genus (inducedSubgraph G S hS) = genus G) (r d : ℤ) :
    BNExists G r d ↔ BNExists (inducedSubgraph G S hS) r d :=
  bnExists_induce_aux (Fintype.card G.V) G S hS rfl hConnected hGenus r d

/-- **The pendant-deletion pushforward.**  The direction used in applications:
a pencil on the whole graph, pendant trees included, is transported to the
graph with the pendant trees deleted. -/
theorem bnExists_induce_of_genus_eq (G : CFGraph.{u}) (S : Finset G.V)
    (hS : S.Nonempty) (hConnected : graph_connected G)
    (hGenus : genus (inducedSubgraph G S hS) = genus G) {r d : ℤ}
    (hBN : BNExists G r d) :
    BNExists (inducedSubgraph G S hS) r d :=
  (bnExists_induce_iff_of_genus_eq G S hS hConnected hGenus r d).mp hBN

/-! ## 7.  A subdivision spec restricted to kept vertices and kept slots -/

namespace Spec

open SubdivisionGraph

/-- Sigma-equality on a family indexed by `Fin m`, in the shape the slot
reindexing below produces it. -/
theorem sigma_fin_ext {m : ℕ} {f : Fin m → ℕ} {a b : Fin m} (hab : a = b)
    {x : Fin (f a)} {y : Fin (f b)} (hxy : (x : ℕ) = (y : ℕ)) :
    (⟨a, x⟩ : Σ i : Fin m, Fin (f i)) = ⟨b, y⟩ := by
  subst hab
  exact congrArg _ (Fin.ext hxy)

variable {n p : ℕ} (spec : Spec n p) (K : Finset (Fin n)) (L : Finset (Fin p))

/-- The core vertex named by a kept-vertex index. -/
noncomputable def keptVertexAt (v' : Fin K.card) : Fin n := (K.equivFin.symm v').val

/-- The slot named by a kept-slot index. -/
noncomputable def keptSlotAt (e' : Fin L.card) : Fin p := (L.equivFin.symm e').val

theorem keptVertexAt_mem (v' : Fin K.card) : keptVertexAt K v' ∈ K :=
  (K.equivFin.symm v').property

theorem keptSlotAt_mem (e' : Fin L.card) : keptSlotAt L e' ∈ L :=
  (L.equivFin.symm e').property

theorem keptVertexAt_injective : Function.Injective (keptVertexAt K) := by
  intro a b hab
  exact K.equivFin.symm.injective (Subtype.ext hab)

theorem keptSlotAt_injective : Function.Injective (keptSlotAt L) := by
  intro a b hab
  exact L.equivFin.symm.injective (Subtype.ext hab)

@[simp] theorem keptVertexAt_equivFin {v : Fin n} (hv : v ∈ K) :
    keptVertexAt K (K.equivFin ⟨v, hv⟩) = v := by
  rw [keptVertexAt, Equiv.symm_apply_apply]

@[simp] theorem keptSlotAt_equivFin {e : Fin p} (he : e ∈ L) :
    keptSlotAt L (L.equivFin ⟨e, he⟩) = e := by
  rw [keptSlotAt, Equiv.symm_apply_apply]

/-- **The restricted spec.**  Its core vertices are the members of `K`, its
slots the members of `L`, both reindexed by `Finset.equivFin` exactly as
`DegSpec.contractedSpec` reindexes its classes and surviving slots, and its
lengths are inherited. -/
noncomputable def restrict (hK : K.Nonempty)
    (hTail : ∀ e ∈ L, spec.core.tail e ∈ K)
    (hHead : ∀ e ∈ L, spec.core.head e ∈ K) :
    SubdivisionGraph.Spec K.card L.card where
  core :=
    { tail := fun e' ↦ K.equivFin
        ⟨spec.core.tail (keptSlotAt L e'), hTail _ (keptSlotAt_mem L e')⟩
      head := fun e' ↦ K.equivFin
        ⟨spec.core.head (keptSlotAt L e'), hHead _ (keptSlotAt_mem L e')⟩ }
  length := fun e' ↦ spec.length (keptSlotAt L e')
  core_nonempty := Finset.card_pos.mpr hK
  core_loopless := by
    intro e' hEq
    exact spec.core_loopless (keptSlotAt L e')
      (congrArg Subtype.val (K.equivFin.injective hEq))
  length_pos := fun e' ↦ spec.length_pos _

variable {spec K L}

@[simp] theorem restrict_length (hK : K.Nonempty)
    (hTail : ∀ e ∈ L, spec.core.tail e ∈ K)
    (hHead : ∀ e ∈ L, spec.core.head e ∈ K) (e' : Fin L.card) :
    (restrict spec K L hK hTail hHead).length e' = spec.length (keptSlotAt L e') := rfl

theorem restrict_core_tail (hK : K.Nonempty)
    (hTail : ∀ e ∈ L, spec.core.tail e ∈ K)
    (hHead : ∀ e ∈ L, spec.core.head e ∈ K) (e' : Fin L.card) :
    keptVertexAt K ((restrict spec K L hK hTail hHead).core.tail e') =
      spec.core.tail (keptSlotAt L e') :=
  keptVertexAt_equivFin K _

theorem restrict_core_head (hK : K.Nonempty)
    (hTail : ∀ e ∈ L, spec.core.tail e ∈ K)
    (hHead : ∀ e ∈ L, spec.core.head e ∈ K) (e' : Fin L.card) :
    keptVertexAt K ((restrict spec K L hK hTail hHead).core.head e') =
      spec.core.head (keptSlotAt L e') :=
  keptVertexAt_equivFin K _

/-! ### The kept vertices of `spec.graph` -/

variable (spec K L)

/-- The vertices of `spec.graph` that the restriction keeps: the core vertices
in `K` and the interior vertices of the slots in `L`. -/
noncomputable def keptVertices : Finset spec.Vertex := by
  classical
  exact Finset.univ.filter
    (fun v ↦ Sum.elim (fun a : Fin n ↦ a ∈ K) (fun x : spec.Interior ↦ x.1 ∈ L) v)

variable {spec K L}

@[simp] theorem mem_keptVertices_inl (a : Fin n) :
    (Sum.inl a : spec.Vertex) ∈ keptVertices spec K L ↔ a ∈ K := by
  classical
  simp only [keptVertices, Finset.mem_filter, Finset.mem_univ, true_and, Sum.elim_inl]

@[simp] theorem mem_keptVertices_inr (x : spec.Interior) :
    (Sum.inr x : spec.Vertex) ∈ keptVertices spec K L ↔ x.1 ∈ L := by
  classical
  simp only [keptVertices, Finset.mem_filter, Finset.mem_univ, true_and, Sum.elim_inr]

theorem keptVertices_nonempty (hK : K.Nonempty) :
    (keptVertices spec K L).Nonempty := by
  obtain ⟨a, ha⟩ := hK
  exact ⟨Sum.inl a, (mem_keptVertices_inl a).mpr ha⟩

/-! ### The inclusion of the restricted spec -/

variable (hK : K.Nonempty) (hTail : ∀ e ∈ L, spec.core.tail e ∈ K)
  (hHead : ∀ e ∈ L, spec.core.head e ∈ K)

/-- The vertex of `spec.graph` underlying a vertex of the restricted spec. -/
noncomputable def inclusion :
    (restrict spec K L hK hTail hHead).Vertex → spec.Vertex
  | Sum.inl v' => Sum.inl (keptVertexAt K v')
  | Sum.inr x => Sum.inr ⟨keptSlotAt L x.1, x.2⟩

/-- The unit step of `spec` underlying a unit step of the restricted spec. -/
noncomputable def stepInclusion :
    (restrict spec K L hK hTail hHead).Step → spec.Step :=
  fun s ↦ ⟨keptSlotAt L s.1, s.2⟩

theorem inclusion_injective :
    Function.Injective (inclusion hK hTail hHead) := by
  rintro (a | ⟨e₁, o₁⟩) (b | ⟨e₂, o₂⟩) h
  · exact congrArg Sum.inl (keptVertexAt_injective K (Sum.inl.inj h))
  · exact absurd h (by simp [inclusion])
  · exact absurd h (by simp [inclusion])
  · have hs : (⟨keptSlotAt L e₁, o₁⟩ : spec.Interior) = ⟨keptSlotAt L e₂, o₂⟩ :=
      Sum.inr.inj h
    have he : e₁ = e₂ := keptSlotAt_injective L (congrArg Sigma.fst hs)
    subst he
    have ho : (o₁ : ℕ) = (o₂ : ℕ) := congrArg (fun z : spec.Interior ↦ (z.2 : ℕ)) hs
    exact congrArg Sum.inr
      (sigma_fin_ext (f := fun e' ↦ (restrict spec K L hK hTail hHead).length e' - 1) rfl ho)

theorem stepInclusion_injective :
    Function.Injective (stepInclusion hK hTail hHead) := by
  rintro ⟨e₁, o₁⟩ ⟨e₂, o₂⟩ h
  have he : e₁ = e₂ := keptSlotAt_injective L (congrArg Sigma.fst h)
  subst he
  have ho : (o₁ : ℕ) = (o₂ : ℕ) := congrArg (fun z : spec.Step ↦ (z.2 : ℕ)) h
  exact sigma_fin_ext (f := fun e' ↦ (restrict spec K L hK hTail hHead).length e') rfl ho

theorem inclusion_mem (x : (restrict spec K L hK hTail hHead).Vertex) :
    inclusion hK hTail hHead x ∈ keptVertices spec K L := by
  rcases x with v' | ⟨e', o⟩
  · exact (mem_keptVertices_inl _).mpr (keptVertexAt_mem K v')
  · exact (mem_keptVertices_inr _).mpr (keptSlotAt_mem L e')

theorem inclusion_surjective {v : spec.Vertex} (hv : v ∈ keptVertices spec K L) :
    ∃ x, inclusion hK hTail hHead x = v := by
  rcases v with a | ⟨e, o⟩
  · refine ⟨Sum.inl (K.equivFin ⟨a, (mem_keptVertices_inl a).mp hv⟩), ?_⟩
    exact congrArg Sum.inl (keptVertexAt_equivFin K _)
  · have he : e ∈ L := (mem_keptVertices_inr _).mp hv
    have hslot : keptSlotAt L (L.equivFin ⟨e, he⟩) = e := keptSlotAt_equivFin L he
    refine ⟨Sum.inr ⟨L.equivFin ⟨e, he⟩,
      ⟨o.val, by rw [restrict_length, hslot]; exact o.isLt⟩⟩, ?_⟩
    exact congrArg Sum.inr
      (sigma_fin_ext (f := fun e ↦ spec.length e - 1) hslot rfl)

/-- The inclusion of the restricted spec, landing in the induced subgraph. -/
noncomputable def inducedInclusion
    (x : (restrict spec K L hK hTail hHead).Vertex) :
    (inducedSubgraph spec.graph (keptVertices spec K L)
      (keptVertices_nonempty hK)).V :=
  induceMk spec.graph (keptVertices spec K L) (keptVertices_nonempty hK)
    (inclusion_mem hK hTail hHead x)

@[simp] theorem induceVal_inducedInclusion
    (x : (restrict spec K L hK hTail hHead).Vertex) :
    induceVal spec.graph (keptVertices spec K L) (keptVertices_nonempty hK)
      (inducedInclusion hK hTail hHead x) = inclusion hK hTail hHead x := rfl

theorem inducedInclusion_bijective :
    Function.Bijective (inducedInclusion hK hTail hHead) := by
  constructor
  · intro a b hab
    exact inclusion_injective hK hTail hHead (congrArg
      (induceVal spec.graph (keptVertices spec K L) (keptVertices_nonempty hK)) hab)
  · intro y
    obtain ⟨x, hx⟩ := inclusion_surjective hK hTail hHead
      (induceVal_mem spec.graph (keptVertices spec K L) (keptVertices_nonempty hK) y)
    exact ⟨x, induceVal_injective _ _ _ (by rw [induceVal_inducedInclusion, hx])⟩

/-! ### The unit steps match -/

theorem inclusion_stepLeft (e' : Fin L.card)
    (o : Fin ((restrict spec K L hK hTail hHead).length e')) :
    inclusion hK hTail hHead ((restrict spec K L hK hTail hHead).stepLeft e' o) =
      spec.stepLeft (keptSlotAt L e') o := by
  have hlen : (restrict spec K L hK hTail hHead).length e' =
    spec.length (keptSlotAt L e') := rfl
  have hbound : (o : ℕ) < spec.length (keptSlotAt L e') := by
    have := o.isLt; omega
  by_cases h0 : (o : ℕ) = 0
  · rw [show (restrict spec K L hK hTail hHead).stepLeft e' o =
        (restrict spec K L hK hTail hHead).coreVertex
          ((restrict spec K L hK hTail hHead).core.tail e') from dite_eq_left h0,
      show spec.stepLeft (keptSlotAt L e') o =
        spec.coreVertex (spec.core.tail (keptSlotAt L e')) from dite_eq_left h0]
    exact congrArg Sum.inl (restrict_core_tail hK hTail hHead e')
  · rw [show (restrict spec K L hK hTail hHead).stepLeft e' o =
        (restrict spec K L hK hTail hHead).interiorVertex e'
          ⟨(o : ℕ) - 1, by omega⟩ from dite_eq_right h0,
      show spec.stepLeft (keptSlotAt L e') o =
        spec.interiorVertex (keptSlotAt L e')
          ⟨(o : ℕ) - 1, by omega⟩ from dite_eq_right h0]
    rfl

theorem inclusion_stepRight (e' : Fin L.card)
    (o : Fin ((restrict spec K L hK hTail hHead).length e')) :
    inclusion hK hTail hHead ((restrict spec K L hK hTail hHead).stepRight e' o) =
      spec.stepRight (keptSlotAt L e') o := by
  have hlen : (restrict spec K L hK hTail hHead).length e' =
    spec.length (keptSlotAt L e') := rfl
  have hbound : (o : ℕ) < spec.length (keptSlotAt L e') := by
    have := o.isLt; omega
  by_cases h1 : (o : ℕ) + 1 = spec.length (keptSlotAt L e')
  · rw [show (restrict spec K L hK hTail hHead).stepRight e' o =
        (restrict spec K L hK hTail hHead).coreVertex
          ((restrict spec K L hK hTail hHead).core.head e') from dite_eq_left h1,
      show spec.stepRight (keptSlotAt L e') o =
        spec.coreVertex (spec.core.head (keptSlotAt L e')) from dite_eq_left h1]
    exact congrArg Sum.inl (restrict_core_head hK hTail hHead e')
  · rw [show (restrict spec K L hK hTail hHead).stepRight e' o =
        (restrict spec K L hK hTail hHead).interiorVertex e'
          ⟨(o : ℕ), by omega⟩ from dite_eq_right h1,
      show spec.stepRight (keptSlotAt L e') o =
        spec.interiorVertex (keptSlotAt L e')
          ⟨(o : ℕ), by omega⟩ from dite_eq_right h1]
    rfl

theorem unitEdge_stepInclusion (s : (restrict spec K L hK hTail hHead).Step) :
    spec.unitEdge (stepInclusion hK hTail hHead s) =
      (inclusion hK hTail hHead
          ((restrict spec K L hK hTail hHead).unitEdge s).1,
        inclusion hK hTail hHead
          ((restrict spec K L hK hTail hHead).unitEdge s).2) := by
  obtain ⟨e', o⟩ := s
  exact Prod.ext (inclusion_stepLeft hK hTail hHead e' o).symm
    (inclusion_stepRight hK hTail hHead e' o).symm

/-! ### The dropped slots really are dropped -/

/-- A vertex of `spec.graph` is kept only in the two ways it can be. -/
theorem mem_keptVertices_stepLeft {e : Fin p} {o : Fin (spec.length e)}
    (h : spec.stepLeft e o ∈ keptVertices spec K L) (heL : e ∉ L) :
    (o : ℕ) = 0 ∧ spec.core.tail e ∈ K := by
  by_cases h0 : (o : ℕ) = 0
  · refine ⟨h0, ?_⟩
    rw [show spec.stepLeft e o = spec.coreVertex (spec.core.tail e) from dite_eq_left h0] at h
    exact (mem_keptVertices_inl _).mp h
  · rw [show spec.stepLeft e o =
      spec.interiorVertex e ⟨(o : ℕ) - 1, by have := o.isLt; omega⟩ from dite_eq_right h0] at h
    exact absurd ((mem_keptVertices_inr _).mp h) heL

theorem mem_keptVertices_stepRight {e : Fin p} {o : Fin (spec.length e)}
    (h : spec.stepRight e o ∈ keptVertices spec K L) (heL : e ∉ L) :
    (o : ℕ) + 1 = spec.length e ∧ spec.core.head e ∈ K := by
  by_cases h1 : (o : ℕ) + 1 = spec.length e
  · refine ⟨h1, ?_⟩
    rw [show spec.stepRight e o = spec.coreVertex (spec.core.head e) from dite_eq_left h1] at h
    exact (mem_keptVertices_inl _).mp h
  · rw [show spec.stepRight e o =
      spec.interiorVertex e ⟨(o : ℕ), by have := o.isLt; omega⟩ from dite_eq_right h1] at h
    exact absurd ((mem_keptVertices_inr _).mp h) heL

/-- **The separation hypothesis, in force.**  If a step of `spec` has both
endpoints kept, its slot is kept — provided a dropped slot of length one has a
dropped endpoint. -/
theorem mem_of_unitEdge_kept
    (hDrop : ∀ e ∉ L, spec.length e = 1 →
      spec.core.tail e ∉ K ∨ spec.core.head e ∉ K)
    {t : spec.Step}
    (hLeft : (spec.unitEdge t).1 ∈ keptVertices spec K L)
    (hRight : (spec.unitEdge t).2 ∈ keptVertices spec K L) :
    t.1 ∈ L := by
  by_contra heL
  obtain ⟨hzero, hTailK⟩ := mem_keptVertices_stepLeft hLeft heL
  obtain ⟨hlast, hHeadK⟩ := mem_keptVertices_stepRight hRight heL
  have hlen : spec.length t.1 = 1 := by omega
  rcases hDrop t.1 heL hlen with h | h
  · exact h hTailK
  · exact h hHeadK

theorem exists_stepInclusion
    (hDrop : ∀ e ∉ L, spec.length e = 1 →
      spec.core.tail e ∉ K ∨ spec.core.head e ∉ K)
    {t : spec.Step}
    (hLeft : (spec.unitEdge t).1 ∈ keptVertices spec K L)
    (hRight : (spec.unitEdge t).2 ∈ keptVertices spec K L) :
    ∃ s, stepInclusion hK hTail hHead s = t := by
  have heL : t.1 ∈ L := mem_of_unitEdge_kept hDrop hLeft hRight
  have hslot : keptSlotAt L (L.equivFin ⟨t.1, heL⟩) = t.1 := keptSlotAt_equivFin L heL
  refine ⟨⟨L.equivFin ⟨t.1, heL⟩, ⟨t.2.val, by rw [restrict_length, hslot]; exact t.2.isLt⟩⟩, ?_⟩
  exact sigma_fin_ext (f := fun e ↦ spec.length e) hslot rfl

/-! ### The restriction is the induced subgraph -/

/-- **`Spec.restrict` is `inducedSubgraph`.**  The separation hypothesis
`hDrop` is exactly what is needed and no more: a slot outside `L` survives the
induction only if it has length one and two kept endpoints. -/
noncomputable def laplacianEquiv_restrict
    (hDrop : ∀ e ∉ L, spec.length e = 1 →
      spec.core.tail e ∉ K ∨ spec.core.head e ∉ K) :
    LaplacianEquiv (restrict spec K L hK hTail hHead).graph
      (inducedSubgraph spec.graph (keptVertices spec K L)
        (keptVertices_nonempty hK)) where
  toEquiv := Equiv.ofBijective _ (inducedInclusion_bijective hK hTail hHead)
  num_edges_eq := by
    classical
    intro x y
    rw [num_edges_induced]
    show num_edges spec.graph (inclusion hK hTail hHead x)
        (inclusion hK hTail hHead y) = _
    rw [spec.num_edges_eq_card_filter_steps,
      (restrict spec K L hK hTail hHead).num_edges_eq_card_filter_steps]
    symm
    refine Finset.card_bij (fun s _ ↦ stepInclusion hK hTail hHead s) ?_ ?_ ?_
    · intro s hs
      rw [Finset.mem_filter] at hs ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [unitEdge_stepInclusion]
      rcases hs.2 with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
    · intro a _ b _ hab
      exact stepInclusion_injective hK hTail hHead hab
    · intro t ht
      rw [Finset.mem_filter] at ht
      have hLeft : (spec.unitEdge t).1 ∈ keptVertices spec K L := by
        rcases ht.2 with h | h
        · rw [h]; exact inclusion_mem hK hTail hHead x
        · rw [h]; exact inclusion_mem hK hTail hHead y
      have hRight : (spec.unitEdge t).2 ∈ keptVertices spec K L := by
        rcases ht.2 with h | h
        · rw [h]; exact inclusion_mem hK hTail hHead y
        · rw [h]; exact inclusion_mem hK hTail hHead x
      obtain ⟨s, hs⟩ := exists_stepInclusion hK hTail hHead hDrop hLeft hRight
      refine ⟨s, ?_, hs⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hEdge := unitEdge_stepInclusion hK hTail hHead s
      rw [hs] at hEdge
      rcases ht.2 with h | h
      · left
        rw [h] at hEdge
        exact Prod.ext (inclusion_injective hK hTail hHead (congrArg Prod.fst hEdge).symm)
          (inclusion_injective hK hTail hHead (congrArg Prod.snd hEdge).symm)
      · right
        rw [h] at hEdge
        exact Prod.ext (inclusion_injective hK hTail hHead (congrArg Prod.fst hEdge).symm)
          (inclusion_injective hK hTail hHead (congrArg Prod.snd hEdge).symm)

/-- The genus of a restricted spec, read off its two cardinalities. -/
theorem genus_restrict :
    genus (restrict spec K L hK hTail hHead).graph =
      (L.card : ℤ) - (K.card : ℤ) + 1 :=
  SubdivisionGraph.Spec.genus_graph _

end Spec

end DraismaVargas.Infrastructure.PendantDeletion
