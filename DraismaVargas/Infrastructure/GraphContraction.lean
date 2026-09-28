import DraismaVargas.Infrastructure.GluingDatum

/-!
# Contracting a single edge of a loopless multigraph

The Draisma--Vargas terminal-face argument needs to contract the target edges
whose length has become zero.  The chip-firing dependency provides no
contraction of a `CFGraph`, and `DraismaVargas.Infrastructure.TargetExpansion`
is the inverse operation.  This file supplies the graph-level half of the
contraction for a **single** edge; the gluing-datum half is
`DraismaVargas.Infrastructure.GluingContraction`.

The edge to be contracted is presented by its endpoints `a b : G.V` together
with

* `hab : a ≠ b` (the graph is loopless, so this is no restriction), and
* `hOne : num_edges G a b = 1`, which says that exactly one occurrence joins
  them.  In Part I the target is a tree, so this always holds, and it is what
  makes the contraction drop exactly one edge.

Rather than forming a quotient, the contraction *renames*: the new vertex type
is `{v : G.V // v ≠ b}` and the vertex `b` is folded onto `a`.  This keeps the
vertex type definitionally finite and decidable.  The new edge multiset is the
image of the old one under that renaming, after deleting *every* occurrence
joining `a` and `b`; under `hOne` there is exactly one such occurrence, so this
is honest edge contraction.  Deleting them is what keeps the image loopless,
and this is why the construction itself does not consume `hOne`: the hypothesis
is carried in the signature of `contract` so that the counting theorems apply
to every graph the definition is used on.

Main results:

* `contract` — the contracted graph;
* `card_edges_contract`, `card_vertices_contract`, `genus_contract` — one
  fewer edge, one fewer vertex, same genus (these are where `hOne` is used);
* `num_edges_contract_of_ne`, `num_edges_contract_merge` — the adjacency
  bookkeeping: multiplicities away from the merged vertex are unchanged, and
  at the merged vertex they add;
* `graph_connected_contract` — contraction preserves connectedness;
* `vertex_degree_contract_of_ne`, `vertex_degree_contract_merge` — the degree
  bookkeeping used by the gluing-datum contraction built on this file.
-/

namespace DraismaVargas.Infrastructure

namespace GraphContraction

/-- The vertices of the contracted graph: `b` is deleted, and the edge is
contracted by renaming `b` to `a`. -/
abbrev Vertex (G : CFGraph) (b : G.V) : Type _ := {v : G.V // v ≠ b}

/-- Splitting a filter along a disjunction of mutually exclusive predicates. -/
theorem card_filter_or_of_disjoint {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] (h : ∀ e ∈ s, ¬ (p e ∧ q e)) :
    Multiset.card (s.filter (fun e => p e ∨ q e))
      = Multiset.card (s.filter p) + Multiset.card (s.filter q) := by
  have h0 : s.filter (fun e => p e ∧ q e) = 0 := Multiset.filter_eq_nil.mpr h
  have hsum := Multiset.filter_add_filter (p := p) q s
  rw [h0, add_zero] at hsum
  rw [← hsum, Multiset.card_add]

variable (G : CFGraph) {a b : G.V}

/-- Rename `b` to `a`, and fix every other vertex.  This is the map on
vertices induced by the contraction. -/
def fold (hab : a ≠ b) (v : G.V) : Vertex G b :=
  if h : v = b then ⟨a, hab⟩ else ⟨v, h⟩

theorem fold_of_ne (hab : a ≠ b) {v : G.V} (h : v ≠ b) :
    fold G hab v = ⟨v, h⟩ := dif_neg h

@[simp] theorem fold_self (hab : a ≠ b) : fold G hab b = ⟨a, hab⟩ := dif_pos rfl

@[simp] theorem fold_coe (hab : a ≠ b) (x : Vertex G b) :
    fold G hab (x : G.V) = x := dif_neg x.2

@[simp] theorem fold_a (hab : a ≠ b) : fold G hab a = ⟨a, hab⟩ := dif_neg hab

/-- `fold` is injective except that it identifies `a` with `b`. -/
theorem fold_eq_fold_iff (hab : a ≠ b) (u v : G.V) :
    fold G hab u = fold G hab v ↔
      u = v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  by_cases hu : u = b <;> by_cases hv : v = b
  · subst hu; subst hv; simp
  · subst hu
    rw [fold_self, fold_of_ne G hab hv, Subtype.mk.injEq]
    constructor
    · intro h; exact Or.inr (Or.inr ⟨rfl, h.symm⟩)
    · rintro (h | ⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h.symm hv
      · exact absurd h.symm hab
      · exact h.symm
  · subst hv
    rw [fold_self, fold_of_ne G hab hu, Subtype.mk.injEq]
    constructor
    · intro h; exact Or.inr (Or.inl ⟨h, rfl⟩)
    · rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
      · exact absurd h hu
      · exact h
      · exact absurd h hu
  · rw [fold_of_ne G hab hu, fold_of_ne G hab hv, Subtype.mk.injEq]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd h hv
      · exact absurd h hu

/-- Characterisation of the value of `fold`. -/
theorem fold_eq_iff (hab : a ≠ b) (u : G.V) (y : Vertex G b) :
    fold G hab u = y ↔ (u = (y : G.V) ∨ ((y : G.V) = a ∧ u = b)) := by
  by_cases hu : u = b
  · subst hu
    rw [fold_self, Subtype.ext_iff]
    constructor
    · intro h; exact Or.inr ⟨h.symm, rfl⟩
    · rintro (h | ⟨h, -⟩)
      · exact absurd h.symm y.2
      · exact h.symm
  · rw [fold_of_ne G hab hu, Subtype.ext_iff]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨-, h⟩)
      · exact h
      · exact absurd h hu

/-- The occurrences of `G` that do not join `a` and `b`.  Under `hOne` exactly
one occurrence is discarded. -/
def keptEdges (G : CFGraph) (a b : G.V) : Multiset (G.V × G.V) :=
  G.edges.filter (fun e => ¬ (e = (a, b) ∨ e = (b, a)))

theorem mem_keptEdges {e : G.V × G.V} :
    e ∈ keptEdges G a b ↔ e ∈ G.edges ∧ ¬ (e = (a, b) ∨ e = (b, a)) :=
  Multiset.mem_filter

/-- The edge multiset of the contracted graph. -/
def contractEdges (hab : a ≠ b) : Multiset (Vertex G b × Vertex G b) :=
  (keptEdges G a b).map (fun e => (fold G hab e.1, fold G hab e.2))

theorem loopless_contractEdges (hab : a ≠ b) (x : Vertex G b) :
    (x, x) ∉ contractEdges G hab := by
  intro hx
  rw [contractEdges, Multiset.mem_map] at hx
  obtain ⟨e, he, heq⟩ := hx
  obtain ⟨p, q⟩ := e
  rw [mem_keptEdges] at he
  obtain ⟨heG, hkeep⟩ := he
  rw [Prod.ext_iff] at heq
  have hfold : fold G hab p = fold G hab q := heq.1.trans heq.2.symm
  rcases (fold_eq_fold_iff G hab p q).mp hfold with h | ⟨h, h'⟩ | ⟨h, h'⟩
  · exact G.loopless p (by rw [h] at heG ⊢; exact heG)
  · exact hkeep (Or.inl (by rw [h, h']))
  · exact hkeep (Or.inr (by rw [h, h']))

/-- Contract the unique edge occurrence joining `a` and `b`.

The hypothesis `hOne` is what makes this the contraction of a *single* edge:
the construction deletes every occurrence joining `a` and `b`, and `hOne` says
there is exactly one.  It is recorded in the signature so that the counting
theorems below apply to every graph this definition is used on. -/
def contract (G : CFGraph) {a b : G.V} (hab : a ≠ b)
    (_hOne : num_edges G a b = 1) : CFGraph where
  V := Vertex G b
  instNonempty := ⟨⟨a, hab⟩⟩
  edges := contractEdges G hab
  loopless := loopless_contractEdges G hab

theorem contract_edges (hab : a ≠ b) (hOne : num_edges G a b = 1) :
    (contract G hab hOne).edges = contractEdges G hab := rfl

/-! ### The two counts -/

/-- Deleting the occurrences joining `a` and `b` removes exactly
`num_edges G a b` of them. -/
theorem card_keptEdges_add (G : CFGraph) (a b : G.V) :
    Multiset.card (keptEdges G a b) + num_edges G a b = Multiset.card G.edges := by
  rw [keptEdges, num_edges, add_comm, ← Multiset.card_add, Multiset.filter_add_not]

/-- Contraction removes exactly one edge occurrence. -/
theorem card_edges_contract (hab : a ≠ b) (hOne : num_edges G a b = 1) :
    Multiset.card (contract G hab hOne).edges = Multiset.card G.edges - 1 := by
  have h := card_keptEdges_add G a b
  rw [hOne] at h
  have hmap : Multiset.card (contract G hab hOne).edges
      = Multiset.card (keptEdges G a b) := Multiset.card_map _ _
  omega

/-- Removing one vertex from a finite vertex type. -/
theorem card_vertex (G : CFGraph) (b : G.V) :
    Fintype.card (Vertex G b) = Fintype.card G.V - 1 := by
  rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ b),
    Finset.card_univ]

/-- Contraction removes exactly one vertex. -/
theorem card_vertices_contract (hab : a ≠ b) (hOne : num_edges G a b = 1) :
    Fintype.card (contract G hab hOne).V = Fintype.card G.V - 1 := by
  have hcongr : Fintype.card (contract G hab hOne).V = Fintype.card (Vertex G b) :=
    Fintype.card_congr (Equiv.refl _)
  rw [hcongr, card_vertex]

/-- A graph with an edge has at least one edge occurrence. -/
theorem one_le_card_edges (hOne : num_edges G a b = 1) :
    1 ≤ Multiset.card G.edges := by
  refine le_trans (le_of_eq hOne.symm) ?_
  exact Multiset.card_le_card (Multiset.filter_le _ G.edges)

/-- Contraction preserves the genus: it removes one edge and one vertex. -/
theorem genus_contract (hab : a ≠ b) (hOne : num_edges G a b = 1) :
    genus (contract G hab hOne) = genus G := by
  have hE : 1 ≤ Multiset.card G.edges := one_le_card_edges G hOne
  have hV : 1 ≤ Fintype.card G.V := Fintype.card_pos
  unfold genus
  rw [card_edges_contract, card_vertices_contract]
  omega

/-! ### Occurrences and connectivity -/

/-- An occurrence witnesses positive multiplicity. -/
theorem num_edges_pos_of_mem_edges (H : CFGraph) (x y : H.V) (h : (x, y) ∈ H.edges) :
    0 < num_edges H x y :=
  Multiset.card_pos_iff_exists_mem.mpr
    ⟨(x, y), Multiset.mem_filter.mpr ⟨h, Or.inl rfl⟩⟩

/-- The reversed occurrence also witnesses positive multiplicity. -/
theorem num_edges_pos_of_mem_edges' (H : CFGraph) (x y : H.V) (h : (y, x) ∈ H.edges) :
    0 < num_edges H x y :=
  Multiset.card_pos_iff_exists_mem.mpr
    ⟨(y, x), Multiset.mem_filter.mpr ⟨h, Or.inr rfl⟩⟩

/-- Positive multiplicity produces an occurrence. -/
theorem exists_mem_edges_of_num_edges_pos (H : CFGraph) (x y : H.V)
    (h : 0 < num_edges H x y) : ∃ e ∈ H.edges, e = (x, y) ∨ e = (y, x) := by
  unfold num_edges at h
  obtain ⟨e, he⟩ := Multiset.card_pos_iff_exists_mem.mp h
  rw [Multiset.mem_filter] at he
  exact ⟨e, he.1, he.2⟩

/-- Contraction preserves connectedness.  A separating set upstairs is pulled
back along `fold`; the `b`-fibre of the merged vertex is what keeps the merged
vertex from being split, and the unique `a`--`b` occurrence can never be the
crossing occurrence produced downstairs because its two endpoints have the same
image. -/
theorem graph_connected_contract (hab : a ≠ b) (hOne : num_edges G a b = 1)
    (hConn : graph_connected G) : graph_connected (contract G hab hOne) := by
  classical
  have key : ∀ T : Finset (Vertex G b), (∃ x y : Vertex G b, x ∈ T ∧ y ∉ T) →
      ∃ x ∈ T, ∃ y ∉ T, 0 < num_edges (contract G hab hOne) x y := by
    rintro T ⟨x, y, hxT, hyT⟩
    set S : Finset G.V := Finset.univ.filter (fun v => fold G hab v ∈ T) with hSdef
    have hmemS : ∀ v : G.V, v ∈ S ↔ fold G hab v ∈ T := by
      intro v
      rw [hSdef, Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ v, h⟩⟩
    have hxS : (x : G.V) ∈ S := (hmemS _).mpr (by rw [fold_coe]; exact hxT)
    have hyS : (y : G.V) ∉ S := by
      intro h
      have h' := (hmemS _).mp h
      rw [fold_coe] at h'
      exact hyT h'
    obtain ⟨v, hvS, w, hwS, hpos⟩ := hConn S ⟨_, _, hxS, hyS⟩
    have hfoldne : fold G hab v ≠ fold G hab w := by
      intro h
      exact hwS ((hmemS w).mpr (h ▸ (hmemS v).mp hvS))
    have hfold_ab : fold G hab a = fold G hab b := by rw [fold_a, fold_self]
    obtain ⟨e, heG, hends⟩ := exists_mem_edges_of_num_edges_pos G v w hpos
    have hkeep : e ∈ keptEdges G a b := by
      rw [mem_keptEdges]
      refine ⟨heG, ?_⟩
      rintro (rfl | rfl) <;> simp only [Prod.mk.injEq] at hends <;>
        rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hfoldne hfold_ab
      · exact hfoldne hfold_ab.symm
      · exact hfoldne hfold_ab.symm
      · exact hfoldne hfold_ab
    refine ⟨fold G hab v, (hmemS v).mp hvS, fold G hab w,
      fun hc => hwS ((hmemS w).mpr hc), ?_⟩
    rcases hends with rfl | rfl
    · exact num_edges_pos_of_mem_edges (contract G hab hOne) _ _
        (Multiset.mem_map_of_mem _ hkeep)
    · exact num_edges_pos_of_mem_edges' (contract G hab hOne) _ _
        (Multiset.mem_map_of_mem _ hkeep)
  exact key

/-! ### Adjacency in the contracted graph -/

/-- Multiplicity in the contracted graph, computed on the occurrences of `G`
that survive the contraction. -/
theorem num_edges_contract_eq (hab : a ≠ b) (hOne : num_edges G a b = 1)
    (x y : Vertex G b) :
    num_edges (contract G hab hOne) x y
      = Multiset.card (G.edges.filter (fun e =>
          ((fold G hab e.1, fold G hab e.2) = (x, y) ∨
            (fold G hab e.1, fold G hab e.2) = (y, x)) ∧
          ¬ (e = (a, b) ∨ e = (b, a)))) := by
  have h : Multiset.card ((contractEdges G hab).filter (fun p => p = (x, y) ∨ p = (y, x)))
      = Multiset.card ((keptEdges G a b).filter (fun e =>
          (fold G hab e.1, fold G hab e.2) = (x, y) ∨
            (fold G hab e.1, fold G hab e.2) = (y, x))) := by
    rw [contractEdges, Multiset.filter_map, Multiset.card_map]
    rfl
  rw [keptEdges, Multiset.filter_filter] at h
  exact h

/-- Away from the merged vertex, contraction does not change multiplicities. -/
theorem num_edges_contract_of_ne (hab : a ≠ b) (hOne : num_edges G a b = 1)
    {u v : G.V} (hu : u ≠ b) (hv : v ≠ b) (hua : u ≠ a) (hva : v ≠ a) :
    num_edges (contract G hab hOne) ⟨u, hu⟩ ⟨v, hv⟩ = num_edges G u v := by
  have hfu : ∀ p : G.V, fold G hab p = (⟨u, hu⟩ : Vertex G b) ↔ p = u := by
    intro p
    rw [fold_eq_iff]
    exact ⟨fun h => h.elim (fun h' => h') (fun h' => absurd h'.1 hua), fun h => Or.inl h⟩
  have hfv : ∀ p : G.V, fold G hab p = (⟨v, hv⟩ : Vertex G b) ↔ p = v := by
    intro p
    rw [fold_eq_iff]
    exact ⟨fun h => h.elim (fun h' => h') (fun h' => absurd h'.1 hva), fun h => Or.inl h⟩
  rw [num_edges_contract_eq]
  unfold num_edges
  refine congrArg Multiset.card (Multiset.filter_congr (fun e _ => ?_))
  obtain ⟨p, q⟩ := e
  simp only [Prod.mk.injEq, hfu, hfv]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact hua h1
    · exact hu h1
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact hva h1
    · exact hv h1

/-- At the merged vertex the occurrences are those at `a` together with those
at `b`.  The erased occurrence joining `a` and `b` does not contribute,
because the other endpoint `v` is neither `a` nor `b`. -/
theorem num_edges_contract_merge (hab : a ≠ b) (hOne : num_edges G a b = 1)
    {v : G.V} (hv : v ≠ b) (hva : v ≠ a) :
    num_edges (contract G hab hOne) ⟨a, hab⟩ ⟨v, hv⟩
      = num_edges G a v + num_edges G b v := by
  have hfa : ∀ p : G.V, fold G hab p = (⟨a, hab⟩ : Vertex G b) ↔ (p = a ∨ p = b) := by
    intro p
    rw [fold_eq_iff]
    exact ⟨fun h => h.elim (fun h' => Or.inl h') (fun h' => Or.inr h'.2),
      fun h => h.elim (fun h' => Or.inl h') (fun h' => Or.inr ⟨rfl, h'⟩)⟩
  have hfv : ∀ p : G.V, fold G hab p = (⟨v, hv⟩ : Vertex G b) ↔ p = v := by
    intro p
    rw [fold_eq_iff]
    exact ⟨fun h => h.elim (fun h' => h') (fun h' => absurd h'.1 hva), fun h => Or.inl h⟩
  have hdisj : ∀ e ∈ G.edges,
      ¬ ((e = (a, v) ∨ e = (v, a)) ∧ (e = (b, v) ∨ e = (v, b))) := by
    rintro ⟨p, q⟩ - ⟨h1, h2⟩
    simp only [Prod.mk.injEq] at h1 h2
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact hab h3
    · exact hv h4
    · exact hv h3
    · exact hab h4
  have hPQ : G.edges.filter (fun e =>
        ((fold G hab e.1, fold G hab e.2) = ((⟨a, hab⟩ : Vertex G b), (⟨v, hv⟩ : Vertex G b)) ∨
          (fold G hab e.1, fold G hab e.2) = ((⟨v, hv⟩ : Vertex G b), (⟨a, hab⟩ : Vertex G b))) ∧
        ¬ (e = (a, b) ∨ e = (b, a)))
      = G.edges.filter (fun e => (e = (a, v) ∨ e = (v, a)) ∨ (e = (b, v) ∨ e = (v, b))) := by
    refine Multiset.filter_congr (fun e _ => ?_)
    obtain ⟨p, q⟩ := e
    simp only [Prod.mk.injEq, hfa, hfv]
    constructor
    · rintro ⟨h, -⟩
      rcases h with ⟨hp | hp, rfl⟩ | ⟨rfl, hq | hq⟩
      · exact Or.inl (Or.inl ⟨hp, rfl⟩)
      · exact Or.inr (Or.inl ⟨hp, rfl⟩)
      · exact Or.inl (Or.inr ⟨rfl, hq⟩)
      · exact Or.inr (Or.inr ⟨rfl, hq⟩)
    · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩))
      · exact ⟨Or.inl ⟨Or.inl rfl, rfl⟩, by
          rintro (⟨-, h⟩ | ⟨h, -⟩)
          exacts [hv h, hab h]⟩
      · exact ⟨Or.inr ⟨rfl, Or.inl rfl⟩, by
          rintro (⟨-, h⟩ | ⟨h, -⟩)
          exacts [hab h, hv h]⟩
      · exact ⟨Or.inl ⟨Or.inr rfl, rfl⟩, by
          rintro (⟨h, -⟩ | ⟨-, h⟩)
          exacts [hab h.symm, hva h]⟩
      · exact ⟨Or.inr ⟨rfl, Or.inr rfl⟩, by
          rintro (⟨h, -⟩ | ⟨h, -⟩)
          exacts [hva h, hv h]⟩
  rw [num_edges_contract_eq, hPQ, card_filter_or_of_disjoint _ _ _ hdisj]
  rfl

/-! ### Degrees -/

/-- Split a sum over all vertices off the two contracted endpoints. -/
theorem sum_split (hab : a ≠ b) (g : G.V → ℤ) :
    ∑ w : G.V, g w = (∑ w ∈ (Finset.univ.erase b).erase a, g w) + g a + g b := by
  rw [← Finset.sum_erase_add Finset.univ g (Finset.mem_univ b),
    ← Finset.sum_erase_add (Finset.univ.erase b) g
      (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩)]

/-- A sum over the contracted vertex type is a sum over `G.V` with `b`
removed. -/
theorem sum_vertex (f : G.V → ℤ) :
    ∑ x : Vertex G b, f (x : G.V) = ∑ w ∈ Finset.univ.erase b, f w :=
  (Finset.sum_subtype (Finset.univ.erase b)
    (fun x => by simp [Finset.mem_erase]) f).symm

/-- Away from the merged vertex the degree is unchanged. -/
theorem vertex_degree_contract_of_ne (hab : a ≠ b) (hOne : num_edges G a b = 1)
    {u : G.V} (hu : u ≠ b) (hua : u ≠ a) :
    vertex_degree (contract G hab hOne) ⟨u, hu⟩ = vertex_degree G u := by
  classical
  have hpt : ∀ x : Vertex G b,
      (num_edges (contract G hab hOne) ⟨u, hu⟩ x : ℤ)
        = if (x : G.V) = a then (num_edges G u a : ℤ) + (num_edges G u b : ℤ)
          else (num_edges G u (x : G.V) : ℤ) := by
    intro x
    by_cases hx : (x : G.V) = a
    · rw [if_pos hx, show x = (⟨a, hab⟩ : Vertex G b) from Subtype.ext hx,
        num_edges_symmetric (contract G hab hOne) ⟨u, hu⟩ ⟨a, hab⟩,
        num_edges_contract_merge G hab hOne hu hua,
        num_edges_symmetric G a u, num_edges_symmetric G b u]
      exact Nat.cast_add _ _
    · rw [if_neg hx]
      exact_mod_cast num_edges_contract_of_ne G hab hOne hu x.2 hua hx
  calc vertex_degree (contract G hab hOne) ⟨u, hu⟩
      = ∑ x : Vertex G b, (num_edges (contract G hab hOne) ⟨u, hu⟩ x : ℤ) := rfl
    _ = ∑ x : Vertex G b, (if (x : G.V) = a then (num_edges G u a : ℤ) + (num_edges G u b : ℤ)
          else (num_edges G u (x : G.V) : ℤ)) := Finset.sum_congr rfl (fun x _ => hpt x)
    _ = ∑ w ∈ Finset.univ.erase b, (if w = a then (num_edges G u a : ℤ) + (num_edges G u b : ℤ)
          else (num_edges G u w : ℤ)) :=
        sum_vertex G (fun w : G.V => if w = a then (num_edges G u a : ℤ) + (num_edges G u b : ℤ)
          else (num_edges G u w : ℤ))
    _ = (∑ w ∈ (Finset.univ.erase b).erase a,
            (if w = a then (num_edges G u a : ℤ) + (num_edges G u b : ℤ)
              else (num_edges G u w : ℤ)))
          + (if a = a then (num_edges G u a : ℤ) + (num_edges G u b : ℤ)
              else (num_edges G u a : ℤ)) :=
        (Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩)).symm
    _ = (∑ w ∈ (Finset.univ.erase b).erase a, (num_edges G u w : ℤ))
          + ((num_edges G u a : ℤ) + (num_edges G u b : ℤ)) := by
        rw [if_pos rfl]
        exact congrArg (· + ((num_edges G u a : ℤ) + (num_edges G u b : ℤ)))
          (Finset.sum_congr rfl (fun w hw => if_neg (Finset.mem_erase.mp hw).1))
    _ = vertex_degree G u := by
        unfold vertex_degree
        rw [sum_split G hab (fun w => (num_edges G u w : ℤ))]
        ring

/-- At the merged vertex the degree is the sum of the two old degrees, less the
two ends of the contracted edge. -/
theorem vertex_degree_contract_merge (hab : a ≠ b) (hOne : num_edges G a b = 1) :
    vertex_degree (contract G hab hOne) ⟨a, hab⟩
      = vertex_degree G a + vertex_degree G b - 2 := by
  classical
  have hba : num_edges G b a = 1 := by rw [num_edges_symmetric]; exact hOne
  have hpt : ∀ x : Vertex G b,
      (num_edges (contract G hab hOne) ⟨a, hab⟩ x : ℤ)
        = if (x : G.V) = a then (0 : ℤ)
          else (num_edges G a (x : G.V) : ℤ) + (num_edges G b (x : G.V) : ℤ) := by
    intro x
    by_cases hx : (x : G.V) = a
    · rw [if_pos hx, show x = (⟨a, hab⟩ : Vertex G b) from Subtype.ext hx]
      exact_mod_cast num_edges_self_zero (contract G hab hOne) ⟨a, hab⟩
    · rw [if_neg hx]
      exact_mod_cast num_edges_contract_merge G hab hOne x.2 hx
  calc vertex_degree (contract G hab hOne) ⟨a, hab⟩
      = ∑ x : Vertex G b, (num_edges (contract G hab hOne) ⟨a, hab⟩ x : ℤ) := rfl
    _ = ∑ x : Vertex G b, (if (x : G.V) = a then (0 : ℤ)
          else (num_edges G a (x : G.V) : ℤ) + (num_edges G b (x : G.V) : ℤ)) :=
        Finset.sum_congr rfl (fun x _ => hpt x)
    _ = ∑ w ∈ Finset.univ.erase b, (if w = a then (0 : ℤ)
          else (num_edges G a w : ℤ) + (num_edges G b w : ℤ)) :=
        sum_vertex G (fun w : G.V => if w = a then (0 : ℤ)
          else (num_edges G a w : ℤ) + (num_edges G b w : ℤ))
    _ = (∑ w ∈ (Finset.univ.erase b).erase a, (if w = a then (0 : ℤ)
            else (num_edges G a w : ℤ) + (num_edges G b w : ℤ)))
          + (if a = a then (0 : ℤ) else (num_edges G a a : ℤ) + (num_edges G b a : ℤ)) :=
        (Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩)).symm
    _ = (∑ w ∈ (Finset.univ.erase b).erase a, (num_edges G a w : ℤ))
          + (∑ w ∈ (Finset.univ.erase b).erase a, (num_edges G b w : ℤ)) := by
        rw [if_pos rfl, add_zero, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun w hw => if_neg (Finset.mem_erase.mp hw).1)
    _ = vertex_degree G a + vertex_degree G b - 2 := by
        unfold vertex_degree
        rw [sum_split G hab (fun w => (num_edges G a w : ℤ)),
          sum_split G hab (fun w => (num_edges G b w : ℤ)),
          num_edges_self_zero, num_edges_self_zero, hOne, hba]
        push_cast
        ring

end GraphContraction

end DraismaVargas.Infrastructure
