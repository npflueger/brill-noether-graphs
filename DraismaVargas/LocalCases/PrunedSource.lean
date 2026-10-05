module

public import DraismaVargas.LocalCases.DanglingDescent

@[expose] public section

/-!
# The pruned source as an actual graph

`DraismaVargas.LocalCases.W4StableSource` deletes the dangling edge
occurrences of the literal quotient source `GluingDatum.sourceGraph`, but it
only ever records the *finset* `W4StableSource.nonDanglingEdges data` of the
occurrences that survive.  That is enough to define
`W4StableSource.nonDanglingValency`, and it is what every W4 wall argument
uses; it is **not** enough for an Euler count, because the pruned object `Γ`
never becomes a graph, so neither `genus Γ` nor its number of connected
components is expressible.

This module builds `Γ`.  `prunedSource data` is the `CFGraph` on the very same
vertex type `data.SourceVertex` as `data.sourceGraph`, whose edge multiset is
the image of the surviving occurrences under the same endpoint map
`GluingDatum.sourceEnds`.  Looplessness is inherited from the target, exactly
as for `sourceGraph`.  Isolated vertices are expected and harmless: a source
vertex all of whose incident occurrences are dangling simply has degree zero.

## The counting API

* `card_prunedSource_edges` — the occurrences of `Γ` are the surviving ones,
  `Multiset.card (prunedSource data).edges = (nonDanglingEdges data).card`.
* `vertex_degree_prunedSource` — **the degree bridge**,
  `vertex_degree (prunedSource data) v = nonDanglingValency data v`.  Both
  sides count edge occurrences incident to `v` with multiplicity and with the
  same orientation convention (an occurrence counts when its *first* or its
  *second* endpoint is `v`), so no factor of two and no double count of a
  parallel class intervenes.  This is the identity the Euler argument
  `∑ nd(v) = 2m` turns on.
* `sum_nonDanglingValency_eq_twice_card_nonDanglingEdges` — the handshake
  `∑ v, nd(v) = 2 m`, obtained from the ambient handshaking theorem
  `sum_vertex_degree_eq_twice_card_edges` through the bridge.
* `genus_prunedSource` — `g(Γ) = m - n + 1` with `m` the surviving occurrence
  count and `n = Fintype.card data.SourceVertex`, and
  `card_nonDanglingEdges_eq` for the `m = g(Γ) + n - 1` direction.
* `componentCount` and `euler_prunedSource` — the connected-component count of
  an arbitrary `CFGraph`, and `n = m - g(Γ) + c` in the shape the Euler
  argument consumes.  Components are counted as the classes of
  `DanglingDescent.Reach`, which is already an equivalence relation.
* `subEdges` and `componentCount_le_componentCount_cons_add_one` — the graph on
  a submultiset of the occurrences of a `CFGraph`, and the fact that adding one
  occurrence merges at most two components.  This is the machinery a deletion
  argument counts components with; it lives here because it is generic and
  because every module that needs it imports this one.

Nothing here proves trivalence; this module only makes the object and its
counts exist.

## Local copies

`ChipFiringWithLean.Basic` keeps `degree_eq_total_flow` and
`sum_num_edges_eq_filter_count` `private`, so the incidence form of
`vertex_degree` is reproved here as
`vertex_degree_eq_card_filter_incident_local`.
-/

namespace DraismaVargas.LocalCases.PrunedSource

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.DanglingDescent

universe u

variable {target : CFGraph} {degree : ℕ}

/-! ## Vertex degree as a count of incident occurrences

`vertex_degree G v` is defined as `∑ u, num_edges G v u`, i.e. by summing the
two-vertex multiplicities.  What the Euler count needs instead is the plain
number of edge *occurrences* at `v`.  For a loopless multigraph the two agree,
because a recorded occurrence `(a, b)` has `a ≠ b` and therefore meets `v` in
at most one of its two slots. -/

section Generic

/-- Summing the pair multiplicities `num_edges G v u` over `u` counts each
occurrence at `v` exactly once, provided no occurrence is a loop.  This is a
local copy of the `private` `degree_eq_total_flow` of
`ChipFiringWithLean.Basic`. -/
private theorem sum_card_filter_pair_local {T : Type u} [DecidableEq T] [Fintype T]
    (v : T) (s : Multiset (T × T)) (hLoopless : ∀ e ∈ s, e.1 ≠ e.2) :
    (∑ u : T, Multiset.card (s.filter fun e ↦ e = (v, u) ∨ e = (u, v)))
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
        (∑ u : T, Multiset.card
            (if head = (v, u) ∨ head = (u, v) then ({head} : Multiset (T × T)) else 0))
          = Multiset.card
            (if head.1 = v ∨ head.2 = v then ({head} : Multiset (T × T)) else 0) := by
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
theorem vertex_degree_eq_card_filter_incident_local (G : CFGraph.{u}) (v : G.V) :
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
          sum_card_filter_pair_local v G.edges hLoopless]

end Generic

/-! ## The pruned source `Γ`

`GluingDatum.sourceGraph` is the literal quotient source: its vertices are the
blocks above target vertices, and it carries **one** edge occurrence for every
element of `data.SourceEdge`, with endpoints `GluingDatum.sourceEnds`.  The
pruned source keeps the same vertices and exactly the occurrences that survive
the dangling deletion. -/

/-- **The pruned source `Γ`.**  Same vertices as `data.sourceGraph`, and one
edge occurrence for each element of `W4StableSource.nonDanglingEdges data`,
with the same endpoints `GluingDatum.sourceEnds`.  Vertices all of whose
incident occurrences are dangling survive as isolated vertices.

Marked `@[reducible]` on purpose: `(prunedSource data).V` has to reduce to
`data.SourceVertex` at instance transparency, or `vertex_degree`, `genus` and
every `Fintype`/`DecidableEq` lookup on the carrier stop matching the
`GluingDatum` API. -/
@[reducible] noncomputable def prunedSource (data : GluingDatum target degree) :
    CFGraph where
  V := data.SourceVertex
  instNonempty :=
    ⟨data.sourceEndpoint (Classical.choice inferInstance) ⟨0, data.degree_pos⟩⟩
  edges := (nonDanglingEdges data).val.map data.sourceEnds
  loopless := by
    intro vertex hmem
    simp only [Multiset.mem_map, Finset.mem_val] at hmem
    obtain ⟨edge, -, hedge⟩ := hmem
    exact data.sourceEnds_ne edge (by rw [hedge])

/-- The pruned source has the very same vertices as the literal quotient
source `GluingDatum.sourceGraph`. -/
theorem prunedSource_V (data : GluingDatum target degree) :
    (prunedSource data).V = data.SourceVertex := rfl

/-- The occurrences of the pruned source are the surviving occurrences, sent
to their endpoints by the same map that `GluingDatum.sourceGraph` uses. -/
theorem prunedSource_edges (data : GluingDatum target degree) :
    (prunedSource data).edges = (nonDanglingEdges data).val.map data.sourceEnds :=
  rfl

/-- Occurrence-level incidence is decidable: the source vertices carry a
`DecidableEq`.  `W4StableSource.Incident` is a plain `def`, so instance search
cannot see this without help. -/
instance decidableIncident (data : GluingDatum target degree)
    (edge : data.SourceEdge) (vertex : data.SourceVertex) :
    Decidable (Incident data edge vertex) := by
  unfold Incident
  infer_instance

/-! ## The counts an Euler argument needs -/

/-- **The occurrences of `Γ` are exactly the surviving ones.** -/
theorem card_prunedSource_edges (data : GluingDatum target degree) :
    Multiset.card (prunedSource data).edges = (nonDanglingEdges data).card := by
  rw [prunedSource_edges, Multiset.card_map]
  rfl

/-- Non-dangling valency is the cardinality of the surviving incident
occurrences, packaged as a `Finset.filter` over all occurrences. -/
theorem nonDanglingValency_eq_card_filter (data : GluingDatum target degree)
    (vertex : data.SourceVertex) :
    nonDanglingValency data vertex
      = (Finset.univ.filter fun edge : data.SourceEdge ↦
          ¬ IsDangling data edge ∧ Incident data edge vertex).card := by
  classical
  unfold nonDanglingValency
  exact congrArg Finset.card (Finset.ext fun edge ↦ by simp)

/-- **The degree bridge.**  The degree of a source vertex in the pruned source
is its non-dangling valency.

Both sides count *occurrences* incident to `vertex`, with multiplicity, under
the same orientation convention: `Incident data edge vertex` is
`(data.sourceEnds edge).1 = vertex ∨ (data.sourceEnds edge).2 = vertex`, and
`vertex_degree` of a loopless multigraph is, by
`vertex_degree_eq_card_filter_incident_local`, the number of entries of the
edge multiset whose first or second slot is `vertex`.  Since the endpoint map
`GluingDatum.sourceEnds` is applied to each surviving occurrence exactly once,
the two counts agree occurrence by occurrence; no factor of two and no
collapsing of a parallel class occurs. -/
theorem vertex_degree_prunedSource (data : GluingDatum target degree)
    (vertex : data.SourceVertex) :
    vertex_degree (prunedSource data) vertex
      = (nonDanglingValency data vertex : ℤ) := by
  classical
  rw [vertex_degree_eq_card_filter_incident_local, nonDanglingValency_eq_card_filter]
  congr 1
  rw [prunedSource_edges, Multiset.filter_map, Multiset.card_map]
  have hCongr :
      Multiset.filter
          ((fun e : data.SourceVertex × data.SourceVertex ↦
              e.1 = vertex ∨ e.2 = vertex) ∘ data.sourceEnds)
          (nonDanglingEdges data).val
        = Multiset.filter (fun edge ↦ Incident data edge vertex)
            (nonDanglingEdges data).val :=
    Multiset.filter_congr fun _ _ ↦ Iff.rfl
  rw [hCongr, ← Finset.filter_val]
  exact congrArg Finset.card (Finset.ext fun edge ↦ by simp)

/-- **The handshake for the pruned source**, `∑ nd(v) = 2 m`.  This is the
ambient handshaking theorem `sum_vertex_degree_eq_twice_card_edges` read
through the degree bridge. -/
theorem sum_nonDanglingValency_eq_twice_card_nonDanglingEdges
    (data : GluingDatum target degree) :
    (∑ vertex : data.SourceVertex, (nonDanglingValency data vertex : ℤ))
      = 2 * ((nonDanglingEdges data).card : ℤ) := by
  have hHandshake := sum_vertex_degree_eq_twice_card_edges (prunedSource data)
  rw [card_prunedSource_edges] at hHandshake
  rw [← hHandshake]
  exact Finset.sum_congr rfl fun vertex _ ↦
    (vertex_degree_prunedSource data vertex).symm

/-- The genus of the pruned source, unfolded to the counts it is made of:
`g(Γ) = m - n + 1` with `m` the surviving occurrence count and `n` the number
of source vertices. -/
theorem genus_prunedSource (data : GluingDatum target degree) :
    genus (prunedSource data)
      = ((nonDanglingEdges data).card : ℤ)
          - (Fintype.card data.SourceVertex : ℤ) + 1 := by
  unfold genus
  rw [card_prunedSource_edges]

/-- The surviving occurrence count read off the genus. -/
theorem card_nonDanglingEdges_eq_genus_add (data : GluingDatum target degree) :
    ((nonDanglingEdges data).card : ℤ)
      = genus (prunedSource data) + (Fintype.card data.SourceVertex : ℤ) - 1 := by
  rw [genus_prunedSource]
  ring

/-! ## Connected components

The pruned source need not be connected, so an Euler count on it needs `c`,
the number of connected components.  The repository's `genus` is the
connected-graph cyclomatic number `m - n + 1`; the invariant that survives
disconnection is `m - n + c`, provided here as `cyclomatic` and related to
`genus` by `cyclomatic_eq_genus_add_componentCount_sub_one`.

Components are the classes of `DanglingDescent.Reach`, which is already
reflexive (`reach_refl`), symmetric (`reach_symm`) and transitive
(`reach_trans`).  A class is recorded as the finset of vertices reachable from
a representative, and `componentCount` counts the distinct classes.  Nothing
below is specific to the pruned source. -/

section Components

/-- The vertex set of the walk-component of `v`.  `Reach` is not decidable, so
the classical instance is supplied explicitly rather than through a `classical`
block, which keeps the instance in the statement the same one that later
proofs elaborate. -/
noncomputable def component (G : CFGraph.{u}) (v : G.V) : Finset G.V :=
  @Finset.filter _ (fun w ↦ Reach G v w) (fun _ ↦ Classical.propDecidable _)
    Finset.univ

@[simp] theorem mem_component {G : CFGraph.{u}} (v w : G.V) :
    w ∈ component G v ↔ Reach G v w := by
  unfold component
  simp

theorem self_mem_component {G : CFGraph.{u}} (v : G.V) : v ∈ component G v :=
  (mem_component v v).2 (reach_refl G v)

theorem component_eq_of_reach {G : CFGraph.{u}} {v w : G.V} (h : Reach G v w) :
    component G v = component G w := by
  ext x
  simp only [mem_component]
  exact ⟨fun hx ↦ reach_trans (reach_symm h) hx, fun hx ↦ reach_trans h hx⟩

/-- **The number of connected components of a `CFGraph`**, counted as the
number of distinct walk-components. -/
noncomputable def componentCount (G : CFGraph.{u}) : ℕ :=
  (Finset.univ.image (component G)).card

theorem componentCount_pos (G : CFGraph.{u}) : 0 < componentCount G := by
  refine Finset.card_pos.mpr ⟨component G (Classical.arbitrary G.V), ?_⟩
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-- A graph is connected exactly when it has one component. -/
theorem componentCount_eq_one_iff (G : CFGraph.{u}) :
    componentCount G = 1 ↔ graph_connected G := by
  constructor
  · intro hCount
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hCount
    refine graph_connected_of_reach (Classical.arbitrary G.V) ?_
    intro v
    have hBase : component G (Classical.arbitrary G.V) = c := by
      have hMem := Finset.mem_image_of_mem (component G)
        (Finset.mem_univ (Classical.arbitrary G.V))
      rw [hc] at hMem
      exact Finset.mem_singleton.mp hMem
    have hHere : component G v = c := by
      have hMem := Finset.mem_image_of_mem (component G) (Finset.mem_univ v)
      rw [hc] at hMem
      exact Finset.mem_singleton.mp hMem
    have hIn : v ∈ component G (Classical.arbitrary G.V) := by
      rw [hBase, ← hHere]
      exact self_mem_component v
    exact (mem_component _ _).1 hIn
  · intro hConn
    have hAll : ∀ v : G.V, component G v = Finset.univ := by
      intro v
      ext w
      simp [reach_of_graph_connected hConn v w]
    have hImage :
        Finset.univ.image (component G) = {(Finset.univ : Finset G.V)} := by
      ext s
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨v, rfl⟩
        exact hAll v
      · intro hs
        exact ⟨Classical.arbitrary G.V, by rw [hAll]; exact hs.symm⟩
    unfold componentCount
    rw [hImage, Finset.card_singleton]

/-- The first Betti number `m - n + c` of a `CFGraph`.  This, not `genus`, is
what an Euler count on a possibly disconnected graph controls. -/
noncomputable def cyclomatic (G : CFGraph.{u}) : ℤ :=
  (Multiset.card G.edges : ℤ) - (Fintype.card G.V : ℤ) + (componentCount G : ℤ)

/-- **Euler's relation**, `n = m - b₁ + c`. -/
theorem card_V_eq_sub_cyclomatic_add_componentCount (G : CFGraph.{u}) :
    (Fintype.card G.V : ℤ)
      = (Multiset.card G.edges : ℤ) - cyclomatic G + (componentCount G : ℤ) := by
  unfold cyclomatic
  ring

theorem cyclomatic_eq_genus_add_componentCount_sub_one (G : CFGraph.{u}) :
    cyclomatic G = genus G + ((componentCount G : ℤ) - 1) := by
  unfold cyclomatic genus
  ring

theorem cyclomatic_eq_genus_of_connected {G : CFGraph.{u}}
    (hConn : graph_connected G) : cyclomatic G = genus G := by
  rw [cyclomatic_eq_genus_add_componentCount_sub_one,
    (componentCount_eq_one_iff G).2 hConn]
  norm_num

end Components

/-! ## The graph on a submultiset of the occurrences

`subEdges G s hs` keeps the vertices of `G` and carries only the
occurrences of `s`.  Deleting occurrences one at a time and tracking the
effect on `componentCount` is what an Euler count on a disconnected graph
needs, and it is what both the trivalence bound and the dangling-deletion
identity run on.  Nothing below is specific to the pruned source. -/

section SubEdges

/-- The graph on the vertices of `G` carrying only the occurrences of `s`.
Marked `@[reducible]` for the same reason `prunedSource` is, namely that
`(subEdges G s hs).V` has to reduce to `G.V` at instance transparency. -/
@[reducible] def subEdges (G : CFGraph.{u}) (s : Multiset (G.V × G.V))
    (hLoopless : ∀ v : G.V, (v, v) ∉ s) : CFGraph.{u} where
  V := G.V
  edges := s
  loopless := hLoopless

theorem num_edges_subEdges (G : CFGraph.{u}) (s : Multiset (G.V × G.V))
    (hs : ∀ v : G.V, (v, v) ∉ s) (a b : G.V) :
    num_edges (subEdges G s hs) a b
      = Multiset.card (s.filter fun e ↦ e = (a, b) ∨ e = (b, a)) := rfl

/-- An occurrence of the enlarged graph is either the new one or an old one. -/
private theorem num_edges_cons_cases (G : CFGraph.{u}) (e : G.V × G.V)
    (t : Multiset (G.V × G.V)) (hs : ∀ v : G.V, (v, v) ∉ e ::ₘ t)
    (ht : ∀ v : G.V, (v, v) ∉ t) (a b : G.V)
    (hpos : 0 < num_edges (subEdges G (e ::ₘ t) hs) a b) :
    (e = (a, b) ∨ e = (b, a)) ∨ 0 < num_edges (subEdges G t ht) a b := by
  classical
  by_cases hNew : e = (a, b) ∨ e = (b, a)
  · exact Or.inl hNew
  · refine Or.inr ?_
    rw [num_edges_subEdges, Multiset.filter_cons, ite_eq_right hNew, Multiset.zero_add]
      at hpos
    rw [num_edges_subEdges]
    exact hpos

/-- **Adding one occurrence breaks walks at that occurrence.** -/
theorem reach_cons_cases (G : CFGraph.{u}) (e : G.V × G.V)
    (t : Multiset (G.V × G.V)) (hs : ∀ v : G.V, (v, v) ∉ e ::ₘ t)
    (ht : ∀ v : G.V, (v, v) ∉ t) {x y : G.V}
    (hxy : Reach (subEdges G (e ::ₘ t) hs) x y) :
    Reach (subEdges G t ht) x y ∨
      (Reach (subEdges G t ht) x e.1 ∧ Reach (subEdges G t ht) e.2 y) ∨
      (Reach (subEdges G t ht) x e.2 ∧ Reach (subEdges G t ht) e.1 y) := by
  induction hxy with
  | refl => exact Or.inl (reach_refl _ _)
  | @tail b c _ hbc ih =>
      rcases num_edges_cons_cases G e t hs ht b c hbc with hNew | hOld
      · rcases hNew with hNew | hNew
        · subst hNew
          rcases ih with h | ⟨h1, h2⟩ | ⟨h1, _⟩
          · exact Or.inr (Or.inl ⟨h, reach_refl _ _⟩)
          · exact Or.inl (reach_trans h1 (reach_symm h2))
          · exact Or.inl h1
        · subst hNew
          rcases ih with h | ⟨h1, _⟩ | ⟨h1, h2⟩
          · exact Or.inr (Or.inr ⟨h, reach_refl _ _⟩)
          · exact Or.inl h1
          · exact Or.inl (reach_trans h1 (reach_symm h2))
      · have hStep : Reach (subEdges G t ht) b c := reach_single hOld
        exact ih.imp (fun h ↦ reach_trans h hStep)
          (Or.imp (fun h ↦ ⟨h.1, reach_trans h.2 hStep⟩)
            (fun h ↦ ⟨h.1, reach_trans h.2 hStep⟩))

/-- A representative vertex of a finset of vertices. -/
noncomputable def repOf {V : Type u} [Nonempty V] (c : Finset V) : V :=
  if h : c.Nonempty then h.choose else Classical.arbitrary V

private theorem repOf_mem {V : Type u} [Nonempty V] {c : Finset V}
    (h : c.Nonempty) : repOf c ∈ c := by
  rw [repOf, dite_eq_left h]
  exact h.choose_spec

/-- The chosen representative of a genuine walk-component represents it. -/
theorem component_repOf {G : CFGraph.{u}}
    {c : Finset G.V} (hc : c ∈ Finset.univ.image (component G)) :
    component G (repOf c) = c := by
  classical
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hc
  have hne : (component G v).Nonempty := ⟨v, self_mem_component v⟩
  exact (component_eq_of_reach
    ((mem_component v (repOf (component G v))).1 (repOf_mem hne))).symm

/-- **Adding one edge occurrence merges at most two components.** -/
theorem componentCount_le_componentCount_cons_add_one (G : CFGraph.{u})
    (e : G.V × G.V) (t : Multiset (G.V × G.V))
    (hs : ∀ v : G.V, (v, v) ∉ e ::ₘ t) (ht : ∀ v : G.V, (v, v) ∉ t) :
    componentCount (subEdges G t ht)
      ≤ componentCount (subEdges G (e ::ₘ t) hs) + 1 := by
  classical
  set H := subEdges G t ht with hH
  set K := subEdges G (e ::ₘ t) hs with hK
  set A := (Finset.univ.image (component H)).erase (component H e.2) with hA
  have hCardA : A.card + 1 = (Finset.univ.image (component H)).card :=
    Finset.card_erase_add_one
      (Finset.mem_image_of_mem _ (Finset.mem_univ (e.2 : G.V)))
  have hInj : A.card ≤ (Finset.univ.image (component K)).card := by
    refine Finset.card_le_card_of_injOn (fun c ↦ component K (repOf c))
      (fun c _ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_
    intro c hc c' hc' hEq
    have hcA : c ∈ A := hc
    have hc'A : c' ∈ A := hc'
    have hcRep : component H (repOf c) = c :=
      component_repOf (Finset.mem_of_mem_erase hcA)
    have hc'Rep : component H (repOf c') = c' :=
      component_repOf (Finset.mem_of_mem_erase hc'A)
    have hReachK : Reach K (repOf c) (repOf c') := by
      have hEq' : component K (repOf c) = component K (repOf c') := hEq
      have hmem : repOf c' ∈ component K (repOf c) := by
        rw [hEq']
        exact self_mem_component _
      exact (mem_component _ _).1 hmem
    rcases reach_cons_cases G e t hs ht hReachK with h | ⟨_, h2⟩ | ⟨h1, _⟩
    · rw [← hcRep, ← hc'Rep]
      exact component_eq_of_reach h
    · exact absurd (hc'Rep.symm.trans (component_eq_of_reach h2).symm)
        (Finset.ne_of_mem_erase hc'A)
    · exact absurd (hcRep.symm.trans (component_eq_of_reach h1))
        (Finset.ne_of_mem_erase hcA)
  unfold componentCount
  omega

end SubEdges

/-! ## The Euler relation on the pruned source -/

/-- The first Betti number of the pruned source, unfolded to the counts it is
made of. -/
theorem cyclomatic_prunedSource (data : GluingDatum target degree) :
    cyclomatic (prunedSource data)
      = ((nonDanglingEdges data).card : ℤ)
          - (Fintype.card data.SourceVertex : ℤ)
          + (componentCount (prunedSource data) : ℤ) := by
  unfold cyclomatic
  rw [card_prunedSource_edges]

/-- **`n = m - b₁(Γ) + c` for the pruned source.**  `n` is the number of source
vertices, `m = (nonDanglingEdges data).card` the number of surviving
occurrences, and `c` the number of connected components of `Γ`.  Together with
`sum_nonDanglingValency_eq_twice_card_nonDanglingEdges` (`∑ nd(v) = 2m`) this
is exactly the input the Draisma--Vargas trivalence count consumes. -/
theorem euler_prunedSource (data : GluingDatum target degree) :
    (Fintype.card data.SourceVertex : ℤ)
      = ((nonDanglingEdges data).card : ℤ)
          - cyclomatic (prunedSource data)
          + (componentCount (prunedSource data) : ℤ) := by
  rw [cyclomatic_prunedSource]
  ring

end DraismaVargas.LocalCases.PrunedSource
