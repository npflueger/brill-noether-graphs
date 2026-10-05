module

public import DraismaVargas.LocalCases.StableLocalProperties
public import Utilities.Iso.GraphContractionFibreTree

@[expose] public section

/-!
# The dangling-side descent

This module proves the one graph-theoretic hypothesis on which
`DraismaVargas.LocalCases.StableLocalProperties` leaves its conclusions
conditional: the property `DanglingSideDescent`, which makes the dangling walk
well founded and turns `sourceEdgeIndex_eq_one_of_danglingSide` and
`danglingEdgeNoGlue_of_changeMinimal_of_det_ne_zero` into unconditional
statements.

A dangling side is a connected set `S` of genus zero, crossed by exactly one
edge occurrence, from its inner endpoint to the outside.  Genus zero and
connectivity say that `S` is a tree, so every occurrence inside it is a
bridge: deleting an interior occurrence at the inner endpoint splits `S` into
two connected pieces, and the piece not containing the inner endpoint is a
strictly smaller dangling side.

The argument here is carried out entirely with chip-firing multigraphs, with
no passage to simple graphs.  Reachability is the reflexive transitive closure
`Reach` of positive edge multiplicity; `graph_connected` is equivalent to it
(`reach_of_graph_connected`, `graph_connected_of_reach`), and reachability
transfers into induced subgraphs (`reach_induced_transfer`).  The bridge
property itself is a counting statement: if the two endpoints of an occurrence
of a connected graph with `|E| + 1 = |V|` were still joined after deleting
every occurrence between them, the remaining graph would be connected with
fewer than `|V| - 1` occurrences, which
`Utilities.graph_connected_card_vertices_le_card_edges_add_one` forbids
(`bridge_split`).  The same counting, applied to the partition of `S` into the
two reachability classes, forces the new side to have genus zero and exactly
one crossing occurrence (`exists_smaller_cut`); no separate "no parallel
occurrences inside the side" lemma is needed.
-/

namespace DraismaVargas.LocalCases.DanglingDescent

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableLocalProperties

universe u

/-! ## Walk reachability -/

/-- Walk reachability in a chip-firing multigraph: the reflexive transitive
closure of "joined by at least one edge occurrence". -/
def Reach (H : CFGraph.{u}) : H.V → H.V → Prop :=
  Relation.ReflTransGen fun a b ↦ 0 < num_edges H a b

/-- Reachability is reflexive. -/
theorem reach_refl (H : CFGraph.{u}) (a : H.V) : Reach H a a :=
  Relation.ReflTransGen.refl

/-- One occurrence is a walk. -/
theorem reach_single {H : CFGraph.{u}} {a b : H.V} (h : 0 < num_edges H a b) :
    Reach H a b :=
  Relation.ReflTransGen.single h

/-- Reachability is transitive. -/
theorem reach_trans {H : CFGraph.{u}} {a b c : H.V} (hab : Reach H a b)
    (hbc : Reach H b c) : Reach H a c :=
  Relation.ReflTransGen.trans hab hbc

/-- Reachability is symmetric, because edge multiplicity is. -/
theorem reach_symm {H : CFGraph.{u}} {a b : H.V} (h : Reach H a b) : Reach H b a := by
  induction h with
  | refl => exact reach_refl H a
  | tail _ hbc ih =>
      exact Relation.ReflTransGen.head (by rwa [num_edges_symmetric]) ih

/-- A property that holds at a base vertex and passes along occurrences holds
at every vertex reachable from that base. -/
theorem reach_propagate {H : CFGraph.{u}} {motive : H.V → Prop} {base : H.V}
    (hBase : motive base)
    (hStep : ∀ a b : H.V, 0 < num_edges H a b → motive a → motive b)
    {v : H.V} (h : Reach H base v) : motive v := by
  induction h with
  | refl => exact hBase
  | tail _ hbc ih => exact hStep _ _ hbc ih

/-- A walk leaving a vertex set crosses it somewhere. -/
theorem exists_cross_of_reach {H : CFGraph.{u}} (S : Finset H.V) {x y : H.V}
    (h : Reach H x y) (hx : x ∈ S) :
    y ∉ S → ∃ v ∈ S, ∃ z ∉ S, 0 < num_edges H v z := by
  induction h with
  | refl => intro hy; exact absurd hx hy
  | @tail b c _ hbc ih =>
      intro hc
      by_cases hb : b ∈ S
      · exact ⟨b, hb, c, hc, hbc⟩
      · exact ih hb

/-- The cut definition of connectivity gives walks: in a connected graph every
vertex is reachable from every other. -/
theorem reach_of_graph_connected {H : CFGraph.{u}} (hConnected : graph_connected H)
    (a b : H.V) : Reach H a b := by
  classical
  by_contra hNot
  obtain ⟨v, hv, z, hz, hEdge⟩ :=
    hConnected (Finset.univ.filter fun x ↦ Reach H a x)
      ⟨a, b, by simp [reach_refl], by simp [hNot]⟩
  exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ z,
    reach_trans (Finset.mem_filter.mp hv).2 (reach_single hEdge)⟩)

/-- Walks give the cut definition of connectivity: a graph all of whose
vertices are reachable from one base vertex is connected. -/
theorem graph_connected_of_reach {H : CFGraph.{u}} (base : H.V)
    (hReach : ∀ v : H.V, Reach H base v) : graph_connected H := by
  intro S hS
  obtain ⟨x, y, hx, hy⟩ := hS
  exact exists_cross_of_reach S
    (reach_trans (reach_symm (hReach x)) (hReach y)) hx hy

/-- Transferring a walk into an induced subgraph of another graph along a map
that preserves occurrences and lands in the inducing set. -/
theorem reach_induced_transfer {G H : CFGraph.{u}} (f : H.V → G.V)
    (Y : Finset G.V) (hY : Y.Nonempty)
    (hAdj : ∀ a b : H.V, 0 < num_edges H a b → 0 < num_edges G (f a) (f b))
    (base : H.V) (root : G.V) (hRoot : f base = root) (hBase : root ∈ Y)
    (hMem : ∀ v : H.V, Reach H base v → f v ∈ Y) :
    ∀ (v : H.V), Reach H base v → ∀ (hv : f v ∈ Y),
      Reach (Utilities.inducedSubgraph G Y hY) ⟨root, hBase⟩ ⟨f v, hv⟩ := by
  subst hRoot
  intro v hv
  induction hv with
  | refl => intro _; exact reach_refl _ _
  | @tail b c hab hbc ih =>
      intro hcY
      refine reach_trans (ih (hMem b hab)) (reach_single ?_)
      rw [Utilities.num_edges_inducedSubgraph]
      exact hAdj b c hbc

/-! ## Deleting all occurrences between two vertices -/

/-- The multigraph obtained from `H` by deleting every edge occurrence joining
the two given vertices. -/
def deletePair (H : CFGraph.{u}) (p q : H.V) : CFGraph.{u} where
  V := H.V
  edges := H.edges.filter fun edge ↦ ¬ (edge = (p, q) ∨ edge = (q, p))
  loopless := fun v hv ↦ H.loopless v (Multiset.mem_of_mem_filter hv)

/-- Deleting occurrences does not change the vertex set. -/
theorem deletePair_vertex_card (H : CFGraph.{u}) (p q : H.V) :
    Fintype.card (deletePair H p q).V = Fintype.card H.V := rfl

/-- Edge multiplicities of `deletePair`, written with the instances of `H`.
This is the bridge past the vertex-type projection of the new graph. -/
theorem num_edges_deletePair_eq (H : CFGraph.{u}) (p q a b : H.V) :
    num_edges (deletePair H p q) a b =
      ((H.edges.filter fun edge ↦ ¬ (edge = (p, q) ∨ edge = (q, p))).filter
        fun edge ↦ edge = (a, b) ∨ edge = (b, a)).card := rfl

/-- Deleting occurrences cannot raise a multiplicity. -/
theorem num_edges_deletePair_le (H : CFGraph.{u}) (p q a b : H.V) :
    num_edges (deletePair H p q) a b ≤ num_edges H a b := by
  rw [num_edges_deletePair_eq]
  exact Multiset.card_le_card (Multiset.filter_le_filter _ (Multiset.filter_le _ _))

/-- Away from the deleted pair the multiplicities are unchanged. -/
theorem num_edges_deletePair_of_ne (H : CFGraph.{u}) (p q a b : H.V)
    (hNe : ¬ ((a = p ∧ b = q) ∨ (a = q ∧ b = p))) :
    num_edges (deletePair H p q) a b = num_edges H a b := by
  rw [num_edges_deletePair_eq, Multiset.filter_filter]
  refine congrArg Multiset.card (Multiset.filter_congr ?_)
  intro edge _
  constructor
  · exact fun h ↦ h.1
  · intro h
    refine ⟨h, ?_⟩
    rintro (hEdge | hEdge) <;> rw [hEdge] at h <;>
      simp only [Prod.mk.injEq] at h <;> exact hNe (by tauto)

/-- Exactly the occurrences joining the deleted pair are lost. -/
theorem card_edges_deletePair (H : CFGraph.{u}) (p q : H.V) :
    (deletePair H p q).edges.card + num_edges H p q = H.edges.card := by
  have h := congrArg Multiset.card (Multiset.filter_add_not
    (fun edge : H.V × H.V ↦ (edge = (p, q) ∨ edge = (q, p))) H.edges)
  simp only [Multiset.card_add] at h
  show (H.edges.filter fun edge ↦ ¬ (edge = (p, q) ∨ edge = (q, p))).card +
    num_edges H p q = H.edges.card
  simp only [num_edges]
  omega

/-! ## Splitting occurrences along a partition -/

/-- The occurrences satisfying one of two exclusive conditions are counted
once each. -/
theorem card_filter_or {α : Type*} (A : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] (hDisjoint : ∀ x, ¬ (p x ∧ q x)) :
    (A.filter fun x ↦ p x ∨ q x).card = (A.filter p).card + (A.filter q).card := by
  have h := Multiset.filter_add_filter p q A
  rw [Multiset.filter_eq_nil.mpr (fun x _ ↦ hDisjoint x), Multiset.add_zero] at h
  have hCard := congrArg Multiset.card h
  simp only [Multiset.card_add] at hCard
  omega

/-- `card_filter_or` with the disjunction presented through an equivalent
condition, so that no syntactic rewriting of the predicate is needed. -/
theorem card_filter_or' {α : Type*} (A : Multiset α) (r p q : α → Prop)
    [DecidablePred r] [DecidablePred p] [DecidablePred q]
    (hIff : ∀ x, r x ↔ (p x ∨ q x)) (hDisjoint : ∀ x, ¬ (p x ∧ q x)) :
    (A.filter r).card = (A.filter p).card + (A.filter q).card := by
  have hEq : A.filter r = A.filter fun x ↦ p x ∨ q x :=
    Multiset.filter_congr fun x _ ↦ hIff x
  rw [hEq]
  exact card_filter_or A p q hDisjoint

/-- Weakening the condition can only increase the count. -/
theorem card_filter_le_of_imp {α : Type*} (A : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] (hImp : ∀ x, p x → q x) :
    (A.filter p).card ≤ (A.filter q).card :=
  Multiset.card_le_card (Multiset.monotone_filter_right _ hImp)

/-- The number of edge occurrences with one endpoint in each of two vertex
sets. -/
def crossCount (G : CFGraph.{u}) (T R : Finset G.V) : ℕ :=
  (G.edges.filter fun edge ↦
    (edge.1 ∈ T ∧ edge.2 ∈ R) ∨ (edge.1 ∈ R ∧ edge.2 ∈ T)).card

/-- One pair of vertices, one on each side, contributes to the crossing
count. -/
theorem num_edges_le_crossCount (G : CFGraph.{u}) (T R : Finset G.V) {a b : G.V}
    (ha : a ∈ T) (hb : b ∈ R) : num_edges G a b ≤ crossCount G T R := by
  unfold crossCount num_edges
  refine card_filter_le_of_imp _ _ _ ?_
  rintro ⟨x, y⟩ h
  rcases h with h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨hb, ha⟩

/-- Two distinct crossing pairs contribute disjointly to the crossing count. -/
theorem num_edges_add_le_crossCount (G : CFGraph.{u}) (T R : Finset G.V)
    {a b c d : G.V} (ha : a ∈ T) (hb : b ∈ R) (hc : c ∈ T) (hd : d ∈ R)
    (hDisjoint : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    num_edges G a b + num_edges G c d ≤ crossCount G T R := by
  have hOr := card_filter_or G.edges (fun e : G.V × G.V ↦ e = (a, b) ∨ e = (b, a))
      (fun e : G.V × G.V ↦ e = (c, d) ∨ e = (d, c)) ?_
  · have hLe := card_filter_le_of_imp G.edges
      (fun e : G.V × G.V ↦ (e = (a, b) ∨ e = (b, a)) ∨ (e = (c, d) ∨ e = (d, c)))
      (fun edge : G.V × G.V ↦
        (edge.1 ∈ T ∧ edge.2 ∈ R) ∨ (edge.1 ∈ R ∧ edge.2 ∈ T)) ?_
    · unfold crossCount num_edges
      omega
    · rintro ⟨x, y⟩ h
      rcases h with (h | h) | (h | h) <;> simp only [Prod.mk.injEq] at h <;>
        obtain ⟨rfl, rfl⟩ := h
      · exact Or.inl ⟨ha, hb⟩
      · exact Or.inr ⟨hb, ha⟩
      · exact Or.inl ⟨hc, hd⟩
      · exact Or.inr ⟨hd, hc⟩
  · rintro ⟨x, y⟩ ⟨h1, h2⟩
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      rw [h1] at h2 <;> simp only [Prod.mk.injEq] at h2 <;> exact hDisjoint (by tauto)

/-- Splitting the occurrences of an induced subgraph along a partition of the
inducing set into two parts. -/
theorem inducedSubgraph_edge_card_split (G : CFGraph.{u}) (S T R : Finset G.V)
    (hS : S.Nonempty) (hT : T.Nonempty) (hR : R.Nonempty)
    (hUnion : ∀ x : G.V, x ∈ S ↔ (x ∈ T ∨ x ∈ R))
    (hDisjoint : ∀ x : G.V, x ∈ T → x ∉ R) :
    (Utilities.inducedSubgraph G S hS).edges.card =
      (Utilities.inducedSubgraph G T hT).edges.card +
        (Utilities.inducedSubgraph G R hR).edges.card + crossCount G T R := by
  rw [Utilities.inducedSubgraph_edge_card_eq_filter,
    Utilities.inducedSubgraph_edge_card_eq_filter,
    Utilities.inducedSubgraph_edge_card_eq_filter]
  have h1 := card_filter_or' G.edges
      (fun edge : G.V × G.V ↦ edge.1 ∈ S ∧ edge.2 ∈ S)
      (fun edge : G.V × G.V ↦ edge.1 ∈ T ∧ edge.2 ∈ T)
      (fun edge : G.V × G.V ↦ (edge.1 ∈ R ∧ edge.2 ∈ R) ∨
        ((edge.1 ∈ T ∧ edge.2 ∈ R) ∨ (edge.1 ∈ R ∧ edge.2 ∈ T)))
      (by intro x; simp only [hUnion]; tauto)
      (by
        rintro x ⟨⟨hx1, hx2⟩, hx3⟩
        rcases hx3 with ⟨h4, h5⟩ | ⟨h4, h5⟩ | ⟨h4, h5⟩
        · exact hDisjoint _ hx1 h4
        · exact hDisjoint _ hx2 h5
        · exact hDisjoint _ hx1 h4)
  have h2 := card_filter_or' G.edges
      (fun edge : G.V × G.V ↦ (edge.1 ∈ R ∧ edge.2 ∈ R) ∨
        ((edge.1 ∈ T ∧ edge.2 ∈ R) ∨ (edge.1 ∈ R ∧ edge.2 ∈ T)))
      (fun edge : G.V × G.V ↦ edge.1 ∈ R ∧ edge.2 ∈ R)
      (fun edge : G.V × G.V ↦
        (edge.1 ∈ T ∧ edge.2 ∈ R) ∨ (edge.1 ∈ R ∧ edge.2 ∈ T))
      (fun x ↦ Iff.rfl)
      (by
        rintro x ⟨⟨hx1, hx2⟩, hx3⟩
        rcases hx3 with ⟨h4, h5⟩ | ⟨h4, h5⟩
        · exact hDisjoint _ h4 hx1
        · exact hDisjoint _ h5 hx2)
  unfold crossCount
  omega

/-! ## The bridge split -/

/-- Every occurrence of a connected multigraph with `|E| + 1 = |V|` is a
bridge: after deleting all occurrences joining its endpoints they are no longer
reachable from one another, and every vertex is reachable from exactly one of
them.  Were both still reachable, the deleted graph would be connected with at
most `|V| - 2` occurrences. -/
theorem bridge_split (H : CFGraph.{u}) (hConn : graph_connected H)
    (hCard : H.edges.card + 1 = Fintype.card H.V) (p q : H.V)
    (hAdj : 0 < num_edges H p q) :
    ¬ Reach (deletePair H p q) q p ∧
      ∀ v : H.V, Reach (deletePair H p q) q v ∨ Reach (deletePair H p q) p v := by
  have hDich : ∀ v : H.V,
      Reach (deletePair H p q) q v ∨ Reach (deletePair H p q) p v := by
    intro v
    refine reach_propagate (H := H) (motive := fun x ↦
      Reach (deletePair H p q) q x ∨ Reach (deletePair H p q) p x)
      (Or.inl (reach_refl _ _)) ?_ (reach_of_graph_connected hConn q v)
    intro a b hab hA
    by_cases hPair : (a = p ∧ b = q) ∨ (a = q ∧ b = p)
    · rcases hPair with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inl (reach_refl _ _)
      · exact Or.inr (reach_refl _ _)
    · have hStep : 0 < num_edges (deletePair H p q) a b := by
        rw [num_edges_deletePair_of_ne H p q a b hPair]; exact hab
      exact hA.imp (fun h ↦ reach_trans h (reach_single hStep))
        (fun h ↦ reach_trans h (reach_single hStep))
  refine ⟨?_, hDich⟩
  intro hqp
  have hAll : ∀ v : H.V, Reach (deletePair H p q) q v := fun v ↦
    (hDich v).elim id fun h ↦ reach_trans hqp h
  have hConnD : graph_connected (deletePair H p q) := graph_connected_of_reach q hAll
  have hBound :=
    Utilities.graph_connected_card_vertices_le_card_edges_add_one _ hConnD
  rw [deletePair_vertex_card] at hBound
  have hSplit := card_edges_deletePair H p q
  omega

open Classical in
/-- The vertices of the side that remain reachable from `q` after every
occurrence joining `p` and `q` inside the side is deleted. -/
noncomputable def sideComponent (G : CFGraph.{u}) (S : Finset G.V)
    (hSne : S.Nonempty) (p q : (Utilities.inducedSubgraph G S hSne).V) :
    Finset G.V :=
  Finset.univ.filter fun x ↦ ∃ hx : x ∈ S,
    Reach (deletePair (Utilities.inducedSubgraph G S hSne) p q) q ⟨x, hx⟩

/-- Membership in `sideComponent` is reachability in the deleted graph. -/
theorem mem_sideComponent {G : CFGraph.{u}} {S : Finset G.V} {hSne : S.Nonempty}
    {p q : (Utilities.inducedSubgraph G S hSne).V} {x : G.V} (hx : x ∈ S) :
    x ∈ sideComponent G S hSne p q ↔
      Reach (deletePair (Utilities.inducedSubgraph G S hSne) p q) q ⟨x, hx⟩ := by
  classical
  unfold sideComponent
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h ↦ h.elim fun _ hr ↦ hr, fun h ↦ ⟨hx, h⟩⟩

/-- The component of `q` is part of the side. -/
theorem sideComponent_subset (G : CFGraph.{u}) (S : Finset G.V) (hSne : S.Nonempty)
    (p q : (Utilities.inducedSubgraph G S hSne).V) :
    sideComponent G S hSne p q ⊆ S := by
  classical
  intro x hx
  unfold sideComponent at hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact hx.elim fun h _ ↦ h

/-- The descent step for a genus-zero connected side with a single crossing
occurrence: an interior occurrence at the inner endpoint cuts off a strictly
smaller side with the same properties. -/
theorem exists_smaller_cut (G : CFGraph.{u}) (S : Finset G.V) (hSne : S.Nonempty)
    (inner outer w : G.V) (hInner : inner ∈ S) (hOuter : outer ∉ S) (hwMem : w ∈ S)
    (hCross : ∀ a b : G.V, a ∈ S → b ∉ S →
      num_edges G a b = if a = inner ∧ b = outer then 1 else 0)
    (hConn : graph_connected (Utilities.inducedSubgraph G S hSne))
    (hGenus : genus (Utilities.inducedSubgraph G S hSne) = 0)
    (hCompl : graph_connected (Utilities.inducedSubgraph G (Finset.univ \ S)
      ⟨outer, Finset.mem_sdiff.mpr ⟨Finset.mem_univ outer, hOuter⟩⟩))
    (hEdge : 0 < num_edges G inner w) :
    ∃ (T : Finset G.V) (hwT : w ∈ T) (hInnerT : inner ∉ T),
      T.card < S.card ∧
      (∀ a b : G.V, a ∈ T → b ∉ T →
        num_edges G a b = if a = w ∧ b = inner then 1 else 0) ∧
      graph_connected (Utilities.inducedSubgraph G T ⟨w, hwT⟩) ∧
      graph_connected (Utilities.inducedSubgraph G (Finset.univ \ T)
        ⟨inner, Finset.mem_sdiff.mpr ⟨Finset.mem_univ inner, hInnerT⟩⟩) ∧
      genus (Utilities.inducedSubgraph G T ⟨w, hwT⟩) = 0 := by
  classical
  have hnum : ∀ a b : (Utilities.inducedSubgraph G S hSne).V,
      num_edges (Utilities.inducedSubgraph G S hSne) a b = num_edges G a.1 b.1 :=
    fun a b ↦ Utilities.num_edges_inducedSubgraph G S hSne a b
  have hVcard : Fintype.card (Utilities.inducedSubgraph G S hSne).V = S.card :=
    Utilities.inducedSubgraph_vertex_card G S hSne
  have hEcard : (Utilities.inducedSubgraph G S hSne).edges.card + 1 = S.card := by
    unfold genus at hGenus
    rw [hVcard] at hGenus
    omega
  obtain ⟨pv, hpv⟩ : ∃ z : (Utilities.inducedSubgraph G S hSne).V, z.1 = inner :=
    ⟨⟨inner, hInner⟩, rfl⟩
  obtain ⟨qv, hqv⟩ : ∃ z : (Utilities.inducedSubgraph G S hSne).V, z.1 = w :=
    ⟨⟨w, hwMem⟩, rfl⟩
  have hAdjGS : 0 < num_edges (Utilities.inducedSubgraph G S hSne) pv qv := by
    rw [hnum, hpv, hqv]; exact hEdge
  obtain ⟨hNoReach, hDich⟩ :=
    bridge_split (Utilities.inducedSubgraph G S hSne) hConn (by omega) pv qv hAdjGS
  have hAdjD : ∀ a b : (Utilities.inducedSubgraph G S hSne).V,
      0 < num_edges (deletePair (Utilities.inducedSubgraph G S hSne) pv qv) a b →
        0 < num_edges G a.1 b.1 := by
    intro a b hab
    have h1 := num_edges_deletePair_le (Utilities.inducedSubgraph G S hSne) pv qv a b
    rw [hnum] at h1
    omega
  have hMemT : ∀ (x : G.V) (hx : x ∈ S),
      (x ∈ sideComponent G S hSne pv qv ↔
        Reach (deletePair (Utilities.inducedSubgraph G S hSne) pv qv) qv ⟨x, hx⟩) :=
    fun x hx ↦ mem_sideComponent hx
  have hTsub : sideComponent G S hSne pv qv ⊆ S := sideComponent_subset G S hSne pv qv
  have hwT : w ∈ sideComponent G S hSne pv qv := by
    refine (hMemT w hwMem).mpr ?_
    have hEq : (⟨w, hwMem⟩ : (Utilities.inducedSubgraph G S hSne).V) = qv :=
      Subtype.ext hqv.symm
    rw [hEq]
    exact reach_refl _ _
  have hInnerT : inner ∉ sideComponent G S hSne pv qv := by
    intro hmem
    have h := (hMemT inner hInner).mp hmem
    have hEq : (⟨inner, hInner⟩ : (Utilities.inducedSubgraph G S hSne).V) = pv :=
      Subtype.ext hpv.symm
    rw [hEq] at h
    exact hNoReach h
  have hInnerR : inner ∈ S \ sideComponent G S hSne pv qv :=
    Finset.mem_sdiff.mpr ⟨hInner, hInnerT⟩
  have hMemR : ∀ (x : G.V) (hx : x ∈ S),
      (x ∈ S \ sideComponent G S hSne pv qv ↔
        Reach (deletePair (Utilities.inducedSubgraph G S hSne) pv qv) pv ⟨x, hx⟩) := by
    intro x hx
    constructor
    · intro hxR
      rcases hDich ⟨x, hx⟩ with h | h
      · exact absurd ((hMemT x hx).mpr h) (Finset.mem_sdiff.mp hxR).2
      · exact h
    · intro hReach
      exact Finset.mem_sdiff.mpr ⟨hx, fun hxT ↦
        hNoReach (reach_trans ((hMemT x hx).mp hxT) (reach_symm hReach))⟩
  -- connectivity of the two pieces of the side
  have hTconn : graph_connected
      (Utilities.inducedSubgraph G (sideComponent G S hSne pv qv) ⟨w, hwT⟩) := by
    refine graph_connected_of_reach ⟨w, hwT⟩ ?_
    intro v
    have hvS : v.1 ∈ S := hTsub v.2
    exact reach_induced_transfer
      (H := deletePair (Utilities.inducedSubgraph G S hSne) pv qv)
      (fun z ↦ z.1) _ ⟨w, hwT⟩ hAdjD qv w hqv hwT
      (fun z hz ↦ (hMemT z.1 z.2).mpr hz) ⟨v.1, hvS⟩ ((hMemT v.1 hvS).mp v.2) v.2
  have hRconn : graph_connected (Utilities.inducedSubgraph G
      (S \ sideComponent G S hSne pv qv) ⟨inner, hInnerR⟩) := by
    refine graph_connected_of_reach ⟨inner, hInnerR⟩ ?_
    intro v
    have hvS : v.1 ∈ S := (Finset.mem_sdiff.mp v.2).1
    exact reach_induced_transfer
      (H := deletePair (Utilities.inducedSubgraph G S hSne) pv qv)
      (fun z ↦ z.1) _ ⟨inner, hInnerR⟩ hAdjD pv inner hpv
      hInnerR (fun z hz ↦ (hMemR z.1 z.2).mpr hz) ⟨v.1, hvS⟩
      ((hMemR v.1 hvS).mp v.2) v.2
  -- connectivity of the complement of the new side
  have hOuterT : outer ∈ Finset.univ \ sideComponent G S hSne pv qv :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h ↦ hOuter (hTsub h)⟩
  have hInnerComp : inner ∈ Finset.univ \ sideComponent G S hSne pv qv :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hInnerT⟩
  have hOuterC : outer ∈ Finset.univ \ S :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hOuter⟩
  have hComplT : graph_connected (Utilities.inducedSubgraph G
      (Finset.univ \ sideComponent G S hSne pv qv) ⟨inner, hInnerComp⟩) := by
    refine graph_connected_of_reach ⟨inner, hInnerComp⟩ ?_
    intro v
    by_cases hvS : v.1 ∈ S
    · refine reach_induced_transfer
        (H := deletePair (Utilities.inducedSubgraph G S hSne) pv qv)
        (fun z ↦ z.1) _ ⟨inner, hInnerComp⟩ hAdjD pv inner
        hpv hInnerComp (fun z hz ↦ Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
          (Finset.mem_sdiff.mp ((hMemR z.1 z.2).mpr hz)).2⟩) ⟨v.1, hvS⟩ ?_ v.2
      exact (hMemR v.1 hvS).mp
        (Finset.mem_sdiff.mpr ⟨hvS, (Finset.mem_sdiff.mp v.2).2⟩)
    · have hvC : v.1 ∈ Finset.univ \ S :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvS⟩
      have hStep : 0 < num_edges
          (Utilities.inducedSubgraph G (Finset.univ \ sideComponent G S hSne pv qv)
            ⟨inner, hInnerComp⟩) ⟨inner, hInnerComp⟩ ⟨outer, hOuterT⟩ := by
        have hValue : num_edges
            (Utilities.inducedSubgraph G (Finset.univ \ sideComponent G S hSne pv qv)
              ⟨inner, hInnerComp⟩) ⟨inner, hInnerComp⟩ ⟨outer, hOuterT⟩ =
            num_edges G inner outer :=
          Utilities.num_edges_inducedSubgraph G _ _ _ _
        rw [hCross inner outer hInner hOuter, ite_eq_left ⟨rfl, rfl⟩] at hValue
        omega
      refine reach_trans (reach_single hStep) ?_
      refine reach_induced_transfer
        (H := Utilities.inducedSubgraph G (Finset.univ \ S) ⟨outer, hOuterC⟩)
        (fun z ↦ z.1) _ ⟨inner, hInnerComp⟩ ?_
        (⟨outer, hOuterC⟩ : (Utilities.inducedSubgraph G (Finset.univ \ S)
          ⟨outer, hOuterC⟩).V) outer rfl hOuterT ?_ ⟨v.1, hvC⟩
        (reach_of_graph_connected hCompl _ _) v.2
      · intro a b hab
        have hValue : num_edges (Utilities.inducedSubgraph G (Finset.univ \ S)
            ⟨outer, hOuterC⟩) a b = num_edges G a.1 b.1 :=
          Utilities.num_edges_inducedSubgraph G _ _ _ _
        omega
      · intro z _
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
          fun h ↦ (Finset.mem_sdiff.mp z.2).2 (hTsub h)⟩
  -- the edge count forces the new side to be a tree with one crossing occurrence
  have hSplit := inducedSubgraph_edge_card_split G S (sideComponent G S hSne pv qv)
    (S \ sideComponent G S hSne pv qv) hSne ⟨w, hwT⟩ ⟨inner, hInnerR⟩
    (by
      intro x
      constructor
      · intro hx
        by_cases h : x ∈ sideComponent G S hSne pv qv
        · exact Or.inl h
        · exact Or.inr (Finset.mem_sdiff.mpr ⟨hx, h⟩)
      · rintro (h | h)
        · exact hTsub h
        · exact (Finset.mem_sdiff.mp h).1)
    (fun x hx h ↦ (Finset.mem_sdiff.mp h).2 hx)
  have hTcardV : Fintype.card (Utilities.inducedSubgraph G
      (sideComponent G S hSne pv qv) ⟨w, hwT⟩).V =
      (sideComponent G S hSne pv qv).card :=
    Utilities.inducedSubgraph_vertex_card G _ _
  have hRcardV : Fintype.card (Utilities.inducedSubgraph G
      (S \ sideComponent G S hSne pv qv) ⟨inner, hInnerR⟩).V =
      (S \ sideComponent G S hSne pv qv).card :=
    Utilities.inducedSubgraph_vertex_card G _ _
  have hTbound := Utilities.graph_connected_card_vertices_le_card_edges_add_one _ hTconn
  have hRbound := Utilities.graph_connected_card_vertices_le_card_edges_add_one _ hRconn
  have hCardSum : (sideComponent G S hSne pv qv).card +
      (S \ sideComponent G S hSne pv qv).card = S.card := by
    rw [add_comm]
    exact Finset.card_sdiff_add_card_eq_card hTsub
  have hRpos : 0 < (S \ sideComponent G S hSne pv qv).card :=
    Finset.card_pos.mpr ⟨inner, hInnerR⟩
  have hInnerEdge : 0 < num_edges G w inner := by
    rw [num_edges_symmetric]; exact hEdge
  have hCrossPos : 0 < crossCount G (sideComponent G S hSne pv qv)
      (S \ sideComponent G S hSne pv qv) := by
    have h1 := num_edges_le_crossCount G (sideComponent G S hSne pv qv)
      (S \ sideComponent G S hSne pv qv) hwT hInnerR
    omega
  have hTedge : (Utilities.inducedSubgraph G (sideComponent G S hSne pv qv)
      ⟨w, hwT⟩).edges.card + 1 = (sideComponent G S hSne pv qv).card := by omega
  have hCrossOne : crossCount G (sideComponent G S hSne pv qv)
      (S \ sideComponent G S hSne pv qv) = 1 := by omega
  refine ⟨sideComponent G S hSne pv qv, hwT, hInnerT, by omega, ?_, hTconn, hComplT, ?_⟩
  · intro a b haT hbT
    have haS : a ∈ S := hTsub haT
    have haNeInner : a ≠ inner := fun h ↦ hInnerT (h ▸ haT)
    by_cases hbS : b ∈ S
    · have hbR : b ∈ S \ sideComponent G S hSne pv qv :=
        Finset.mem_sdiff.mpr ⟨hbS, hbT⟩
      by_cases hPair : a = w ∧ b = inner
      · rw [ite_eq_left hPair]
        have h1 := num_edges_le_crossCount G (sideComponent G S hSne pv qv)
          (S \ sideComponent G S hSne pv qv) haT hbR
        have h2 : 0 < num_edges G a b := by rw [hPair.1, hPair.2]; exact hInnerEdge
        omega
      · rw [ite_eq_right hPair]
        have h1 := num_edges_add_le_crossCount G (sideComponent G S hSne pv qv)
          (S \ sideComponent G S hSne pv qv) haT hbR hwT hInnerR
          (by
            rintro (h | h)
            · exact hPair h
            · exact haNeInner h.1)
        omega
    · have h1 : ¬ (a = inner ∧ b = outer) := fun h ↦ haNeInner h.1
      have h2 : ¬ (a = w ∧ b = inner) := fun h ↦ hbS (h.2 ▸ hInner)
      rw [hCross a b haS hbS, ite_eq_right h1, ite_eq_right h2]
  · unfold genus
    rw [hTcardV]
    omega


/-! ## The descent property of dangling cuts -/

/-- The descent step, in terms of the dangling certificate: an occurrence from
the inner endpoint of a dangling cut to another vertex of its side carries a
dangling cut with a strictly smaller side. -/
theorem exists_danglingSide_of_mem_side {G : CFGraph.{u}} {inner outer w : G.V}
    (cut : DanglingSide G inner outer) (hwMem : w ∈ cut.side)
    (hEdge : 0 < num_edges G inner w) :
    ∃ smaller : DanglingSide G w inner, smaller.side.card < cut.side.card := by
  obtain ⟨T, hwT, hInnerT, hCard, hCrossNew, hConnNew, hComplNew, hGenusNew⟩ :=
    exists_smaller_cut G cut.side ⟨inner, cut.left_mem⟩ inner outer w cut.left_mem
      cut.right_not_mem hwMem cut.cross_num_edges cut.side_connected
      cut.side_genus_zero cut.complement_connected hEdge
  exact ⟨{ side := T
           left_mem := hwT
           right_not_mem := hInnerT
           cross_num_edges := hCrossNew
           side_connected := hConnNew
           complement_connected := hComplNew
           side_genus_zero := hGenusNew }, hCard⟩

variable {target : CFGraph} {degree : ℕ}

/-- The graph-theoretic input of the dangling walk, for every gluing datum:
every source occurrence at the inner endpoint of a dangling cut, other than
the cut occurrence itself, is again dangling along a strictly smaller cut. -/
theorem danglingSideDescent (data : GluingDatum target degree) :
    DanglingSideDescent data := by
  intro inner outer cut crossing other hCrossEnds hIncident hNe
  obtain ⟨w, hEnds⟩ := exists_other_sourceEnd data hIncident
  have hEdgePos : 0 < num_edges data.sourceGraph inner w :=
    num_edges_pos_of_sourceEnds data hEnds
  have hEndpointsOne : num_edges data.sourceGraph inner outer = 1 :=
    cut.num_edges_endpoints
  have hwNeOuter : w ≠ outer := by
    rintro rfl
    have hTwo := two_le_num_edges_of_ne data hNe hEnds hCrossEnds
    omega
  have hwMem : w ∈ cut.side := by
    by_contra hNotMem
    have hZero := cut.cross_num_edges inner w cut.left_mem hNotMem
    rw [ite_eq_right fun hPair ↦ hwNeOuter hPair.2] at hZero
    omega
  obtain ⟨smaller, hLess⟩ := exists_danglingSide_of_mem_side cut hwMem hEdgePos
  exact ⟨w, inner, smaller, hEnds.symm, hLess⟩

/-- Draisma--Vargas Part I, `lemma-dangling-no-glue`, edge form, with no descent
hypothesis: a change-minimal gluing datum whose honest stable length matrix is
nonsingular satisfies dangling-no-glue. -/
theorem danglingEdgeNoGlue_of_det_ne_zero
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (labelling : StableLengthMatrixLabelling data coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix
      labelling.presentation).det ≠ 0) :
    DanglingEdgeNoGlue data :=
  danglingEdgeNoGlue_of_changeMinimal_of_det_ne_zero data hValid hMinimal
    labelling hDet (danglingSideDescent data)

/-- The dangling walk, with no descent hypothesis: every occurrence carrying a
dangling cut is unramified. -/
theorem sourceEdgeIndex_eq_one_of_isDangling
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (labelling : StableLengthMatrixLabelling data coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix
      labelling.presentation).det ≠ 0)
    (edge : data.SourceEdge) (hDangling : IsDangling data edge) :
    data.sourceEdgeIndex edge = 1 :=
  danglingEdgeNoGlue_of_det_ne_zero data hValid hMinimal labelling hDet edge
    hDangling

end DraismaVargas.LocalCases.DanglingDescent
