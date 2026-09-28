import DraismaVargas.LocalCases.PrunedSource
import DraismaVargas.LocalCases.NonDanglingValency

/-!
# The spanning-forest bound and the trivalence count

`DraismaVargas.LocalCases.PrunedSource` builds the pruned source `Γ` as an
actual `CFGraph` and records the two identities an Euler argument consumes: the
handshake `∑ nd(v) = 2 m` and the Euler *identity*
`n = m - b₁(Γ) + c` (`euler_prunedSource`), with `b₁ = cyclomatic` — **not**
`genus`, since this development's `genus` is `|E| - |V| + 1` unconditionally,
which is the first Betti number only for a connected graph, and `Γ` is
generally disconnected.

An identity on its own bounds nothing.  The prerequisite is that the first
Betti number is **nonnegative** for an arbitrary — in particular disconnected —
finite multigraph.  The connected case is
`Utilities.graph_connected_card_vertices_le_card_edges_add_one`, which is
`0 ≤ genus` for a connected graph; the general case is proved here.

## The spanning-forest bound

`card_V_le_card_edges_add_componentCount` — `|V| ≤ |E| + c` for every
`CFGraph`, equivalently `cyclomatic_nonneg`, `0 ≤ cyclomatic G`.  The proof is
an induction on the edge multiset that needs no spanning forest: with no
occurrences at all every vertex is its own component
(`componentCount_edges_zero`), and adding one occurrence merges at most two
components (`componentCount_le_componentCount_cons_add_one`).  The latter is
the only real step.  It rests on `reach_cons_cases`: a walk in the enlarged
graph either avoids the new occurrence entirely, or breaks at it, so the
component map of the smaller graph is injective off the single class of the new
occurrence's second endpoint.  `subEdges G s hs` is the graph on the vertices
of `G` carrying only the occurrences of `s`; it is `@[reducible]` for the same
reason `prunedSource` is.

## The trivalence count

For the pruned source, write `V₀` for the isolated vertices (`nd = 0`) and
`V₃` for the vertices of the stable graph (`nd ≥ 3`).  Over a *connected*
quotient source `nd ≠ 1` (`NonDanglingValency.nonDanglingValency_ne_one`), so
every remaining vertex has `nd = 2`, and the handshake plus Euler collapse to
one identity (`sum_stableValency_add_two_mul_card_sourceVertex`),

```
∑_{v ∈ V₃} nd(v) + 2 n  =  2 m + 2 |V₀| + 2 |V₃|.
```

Read through `euler_prunedSource` this is exactly the Euler relation of the
*stable* graph `H(M)`, whose edges are the stable paths and whose vertices are
`V₃`: the valency-two vertices, which subdivide the stable paths, cancel out of
it.  Since every stable vertex contributes at least three to the left,

* `card_stableVertices_add_two_mul_componentCount_le` — `|V₃| + 2c ≤ 2 b₁ + 2|V₀|`,
  which is the Draisma--Vargas bound `m(H) ≤ 3 (b₁ - c(H))` once the stable-path
  count is identified with `m(H)`;
* `card_stableVertices_le_two_mul_cyclomatic` — `|V₃| ≤ 2 b₁(Γ)`, using
  `card_isolatedVertices_le_componentCount` (an isolated vertex is a component
  of its own).

and trivalence is precisely the statement that this bound is **saturated**:

* `trivalent_of_euler_saturated` — if `2 b₁ + 2|V₀| ≤ |V₃| + 2c`, the reverse
  of the displayed inequality, then `nd(v) ≤ 3` at every source vertex.

## What this does *not* close

`FullDimensionalSource.FullDimensionalSourcePresentation.trivalent` stays a
field.  The hypothesis of `trivalent_of_euler_saturated` is the numerical
residue of the Draisma--Vargas argument, and discharging it from the
`saturated` field needs two further inputs, supplied by other modules:

* the number of *stable paths* — which `saturated` controls, through
  `stablePath_card`, as `|E(target)|` — must be identified with the edge count
  of the stable graph, i.e. `∑_{v ∈ V₃} nd(v)` must be shown to be twice that
  number, each stable path having two ends at vertices of `V₃`.  Counting the
  ends is the content of `Decomposes`, but only for a presentation
  whose rows are *maximal* paths; `Decomposes` alone allows two rows to meet at
  a valency-two vertex.  `StablePathCount` proves the identity under
  `HasPathEnds`;
* `b₁(Γ)` must be identified with `genus data.sourceGraph`, i.e. deleting the
  dangling occurrences must be shown not to change the first Betti number.
  Each deletion is a bridge deletion, and `DanglingBetti` carries out the
  induction over the whole dangling set.

`TrivalenceClosure` chains the two with the present bound and shows that
trivalence is then equivalent to the identity
`genus data.sourceGraph = 2 * degree - 5 + 3 * c(H)`
(`TrivalenceClosure.trivalent_iff_genus_eq`). Without those inputs, no amount of
counting on `Γ` alone forces `nd ≤ 3`: the counting content of the handshake and
Euler is entirely contained in the displayed identity, which is symmetric under
moving excess valency between vertices.
-/

namespace DraismaVargas.LocalCases.Trivalence

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.DanglingDescent
open DraismaVargas.LocalCases.NonDanglingValency
open DraismaVargas.LocalCases.PrunedSource

universe u

/-! ## The spanning-forest bound for an arbitrary multigraph -/

section Forest

/-- The graph on the vertices of `G` carrying only the occurrences of `s`.
Marked `@[reducible]` on purpose, exactly as `PrunedSource.prunedSource` is:
`(subEdges G s hs).V` has to reduce to `G.V` at instance transparency, or
`num_edges`, `Reach` and every `Fintype`/`DecidableEq` lookup on the carrier
stop matching. -/
@[reducible] def subEdges (G : CFGraph.{u}) (s : Multiset (G.V × G.V))
    (hLoopless : ∀ v : G.V, (v, v) ∉ s) : CFGraph.{u} where
  V := G.V
  edges := s
  loopless := hLoopless

/-- Keeping every occurrence gives the graph back. -/
theorem subEdges_self (G : CFGraph.{u}) : subEdges G G.edges G.loopless = G := rfl

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
    rw [num_edges_subEdges, Multiset.filter_cons, if_neg hNew, Multiset.zero_add]
      at hpos
    rw [num_edges_subEdges]
    exact hpos

/-- **Adding one occurrence breaks walks at that occurrence.**  A walk in the
enlarged graph either is already a walk without the new occurrence, or joins
its source to one end of the new occurrence and the other end to its
target. -/
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
private noncomputable def repOf {V : Type u} [Nonempty V] (c : Finset V) : V :=
  if h : c.Nonempty then h.choose else Classical.arbitrary V

private theorem repOf_mem {V : Type u} [Nonempty V] {c : Finset V} (h : c.Nonempty) :
    repOf c ∈ c := by
  rw [repOf, dif_pos h]
  exact h.choose_spec

/-- **Adding one edge occurrence merges at most two components.**  The
component map of the smaller graph is injective on every class except that of
the new occurrence's second endpoint: two vertices joined only through the new
occurrence both reach one of its ends, and `reach_cons_cases` says which. -/
theorem componentCount_le_componentCount_cons_add_one (G : CFGraph.{u})
    (e : G.V × G.V) (t : Multiset (G.V × G.V))
    (hs : ∀ v : G.V, (v, v) ∉ e ::ₘ t) (ht : ∀ v : G.V, (v, v) ∉ t) :
    componentCount (subEdges G t ht)
      ≤ componentCount (subEdges G (e ::ₘ t) hs) + 1 := by
  classical
  set H := subEdges G t ht with hH
  set K := subEdges G (e ::ₘ t) hs with hK
  have hRep : ∀ c ∈ Finset.univ.image (component H), component H (repOf c) = c := by
    intro c hc
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hc
    have hne : (component H v).Nonempty := ⟨v, self_mem_component v⟩
    exact (component_eq_of_reach
      ((mem_component v (repOf (component H v))).1 (repOf_mem hne))).symm
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
      hRep c (Finset.mem_of_mem_erase hcA)
    have hc'Rep : component H (repOf c') = c' :=
      hRep c' (Finset.mem_of_mem_erase hc'A)
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

/-- With no occurrences at all every vertex is its own component. -/
theorem componentCount_edges_zero (G : CFGraph.{u})
    (h0 : ∀ v : G.V, (v, v) ∉ (0 : Multiset (G.V × G.V))) :
    componentCount (subEdges G 0 h0) = Fintype.card G.V := by
  classical
  have hReach : ∀ x y : G.V, Reach (subEdges G 0 h0) x y → x = y := by
    intro x y hxy
    induction hxy with
    | refl => rfl
    | @tail b c _ hbc _ =>
        rw [num_edges_subEdges] at hbc
        simp at hbc
  have hComp : component (subEdges G 0 h0) = fun v : G.V ↦ ({v} : Finset G.V) := by
    funext v
    ext w
    simp only [mem_component, Finset.mem_singleton]
    exact ⟨fun h ↦ (hReach v w h).symm, fun h ↦ h ▸ reach_refl _ _⟩
  unfold componentCount
  rw [hComp, Finset.card_image_of_injective _ Finset.singleton_injective,
    Finset.card_univ]

/-- **The spanning-forest bound.**  Every finite multigraph has at least
`|V| - |E|` connected components; no connectivity hypothesis. -/
theorem card_V_le_card_edges_add_componentCount (G : CFGraph.{u}) :
    Fintype.card G.V ≤ Multiset.card G.edges + componentCount G := by
  suffices hAll : ∀ (s : Multiset (G.V × G.V)) (hs : ∀ v : G.V, (v, v) ∉ s),
      Fintype.card G.V ≤ Multiset.card s + componentCount (subEdges G s hs) from
    hAll G.edges G.loopless
  intro s
  induction s using Multiset.induction_on with
  | empty =>
      intro hs
      rw [componentCount_edges_zero G hs]
      simp
  | cons e t ih =>
      intro hs
      have ht : ∀ v : G.V, (v, v) ∉ t := fun v hv ↦ hs v (Multiset.mem_cons_of_mem hv)
      have h1 := ih ht
      have h2 := componentCount_le_componentCount_cons_add_one G e t hs ht
      rw [Multiset.card_cons]
      omega

/-- **The first Betti number of a finite multigraph is nonnegative**, whether
or not the graph is connected.  This is the bound an Euler *identity* cannot
supply, and the prerequisite the Euler identity of `PrunedSource` needs. -/
theorem cyclomatic_nonneg (G : CFGraph.{u}) : 0 ≤ cyclomatic G := by
  have h := card_V_le_card_edges_add_componentCount G
  unfold cyclomatic
  omega

end Forest

/-! ## The counting lemmas, for an abstract valency function -/

section Counting

variable {V : Type*} [Fintype V]

/-- **The handshake and the isolated vertices, combined.**  A valency function
with no value `1` splits the vertices into `nd = 0`, `nd = 2` and `nd ≥ 3`; the
valency-two vertices then cancel out of the handshake, leaving an identity in
which only the isolated vertices and the vertices of valency at least three
appear. -/
private theorem sum_stable_eq (nd : V → ℕ) (m : ℕ)
    (hSum : ∑ v : V, nd v = 2 * m) (hNe : ∀ v : V, nd v ≠ 1) :
    (∑ v ∈ Finset.univ.filter fun v : V ↦ 3 ≤ nd v, (nd v : ℤ))
        + 2 * (Fintype.card V : ℤ)
      = 2 * (m : ℤ)
        + 2 * ((Finset.univ.filter fun v : V ↦ nd v = 0).card : ℤ)
        + 2 * ((Finset.univ.filter fun v : V ↦ 3 ≤ nd v).card : ℤ) := by
  classical
  have hSplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset V)) (p := fun v : V ↦ nd v = 0)
  rw [Finset.card_univ] at hSplit
  have hSP : (Finset.univ.filter fun v : V ↦ 3 ≤ nd v)
      ⊆ Finset.univ.filter fun v : V ↦ ¬ nd v = 0 := by
    intro v hv
    rw [Finset.mem_filter] at hv ⊢
    exact ⟨Finset.mem_univ _, by omega⟩
  have hStep : (∑ v ∈ Finset.univ.filter fun v : V ↦ 3 ≤ nd v, ((nd v : ℤ) - 2))
      = ∑ v ∈ Finset.univ.filter fun v : V ↦ ¬ nd v = 0, ((nd v : ℤ) - 2) := by
    refine Finset.sum_subset hSP ?_
    intro v hvP hvS
    rw [Finset.mem_filter] at hvP
    have hv2 : nd v = 2 := by
      have h1 : ¬ (3 ≤ nd v) := fun h ↦ hvS (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      have h2 := hNe v
      have h3 := hvP.2
      omega
    rw [hv2]
    norm_num
  have hPsum : (∑ v ∈ Finset.univ.filter fun v : V ↦ ¬ nd v = 0, (nd v : ℤ))
      = ∑ v : V, (nd v : ℤ) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro v _ hvP
    have hv0 : nd v = 0 := by
      by_contra h
      exact hvP (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [hv0]
    norm_num
  have hCast : (∑ v : V, (nd v : ℤ)) = 2 * (m : ℤ) := by
    rw [← Nat.cast_sum, hSum]
    push_cast
    ring
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
    hPsum, hCast] at hStep
  simp only [nsmul_eq_mul] at hStep
  have hSplit' : ((Finset.univ.filter fun v : V ↦ nd v = 0).card : ℤ)
      + ((Finset.univ.filter fun v : V ↦ ¬ nd v = 0).card : ℤ)
        = (Fintype.card V : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ ↦ (k : ℤ)) hSplit
  linarith

/-- Each vertex of valency at least three contributes at least three. -/
private theorem three_mul_card_le (nd : V → ℕ) :
    3 * ((Finset.univ.filter fun v : V ↦ 3 ≤ nd v).card : ℤ)
      ≤ ∑ v ∈ Finset.univ.filter fun v : V ↦ 3 ≤ nd v, (nd v : ℤ) := by
  classical
  have h : ∀ v ∈ Finset.univ.filter fun v : V ↦ 3 ≤ nd v, (3 : ℤ) ≤ (nd v : ℤ) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    exact_mod_cast hv.2
  have hsum := Finset.sum_le_sum h
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  linarith

/-- The converse inequality forces every valency at least three to be exactly
three, hence every valency to be at most three. -/
private theorem le_three_of_sum_le (nd : V → ℕ)
    (hLe : (∑ v ∈ Finset.univ.filter fun v : V ↦ 3 ≤ nd v, (nd v : ℤ))
      ≤ 3 * ((Finset.univ.filter fun v : V ↦ 3 ≤ nd v).card : ℤ))
    (v : V) : nd v ≤ 3 := by
  classical
  by_contra hv
  have hvS : v ∈ Finset.univ.filter fun v : V ↦ 3 ≤ nd v :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩
  have hNonneg : ∀ w ∈ Finset.univ.filter fun w : V ↦ 3 ≤ nd w,
      (0 : ℤ) ≤ (nd w : ℤ) - 3 := by
    intro w hw
    rw [Finset.mem_filter] at hw
    have h3 : (3 : ℤ) ≤ (nd w : ℤ) := by exact_mod_cast hw.2
    linarith
  have hZero :
      (∑ w ∈ Finset.univ.filter fun w : V ↦ 3 ≤ nd w, ((nd w : ℤ) - 3)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have h3 := three_mul_card_le (V := V) nd
    linarith
  have hEq := (Finset.sum_eq_zero_iff_of_nonneg hNonneg).1 hZero v hvS
  omega

end Counting

/-! ## The Euler count on the pruned source -/

section PrunedSourceCount

variable {target : CFGraph} {degree : ℕ}

/-- The isolated vertices of the pruned source: the source vertices all of
whose incident occurrences are dangling. -/
noncomputable def isolatedVertices (data : GluingDatum target degree) :
    Finset data.SourceVertex :=
  Finset.univ.filter fun vertex ↦ nonDanglingValency data vertex = 0

@[simp] theorem mem_isolatedVertices (data : GluingDatum target degree)
    (vertex : data.SourceVertex) :
    vertex ∈ isolatedVertices data ↔ nonDanglingValency data vertex = 0 := by
  unfold isolatedVertices
  simp

/-- The vertices of the stable graph: surviving valency at least three. -/
noncomputable def stableVertices (data : GluingDatum target degree) :
    Finset data.SourceVertex :=
  Finset.univ.filter fun vertex ↦ 3 ≤ nonDanglingValency data vertex

@[simp] theorem mem_stableVertices (data : GluingDatum target degree)
    (vertex : data.SourceVertex) :
    vertex ∈ stableVertices data ↔ 3 ≤ nonDanglingValency data vertex := by
  unfold stableVertices
  simp

/-- The handshake `∑ nd(v) = 2 m`, in `ℕ`. -/
theorem sum_nonDanglingValency (data : GluingDatum target degree) :
    (∑ vertex : data.SourceVertex, nonDanglingValency data vertex)
      = 2 * (nonDanglingEdges data).card := by
  have h := sum_nonDanglingValency_eq_twice_card_nonDanglingEdges data
  exact_mod_cast h

/-- An isolated source vertex carries no occurrence of the pruned source. -/
theorem num_edges_prunedSource_eq_zero (data : GluingDatum target degree)
    {vertex : data.SourceVertex} (hZero : nonDanglingValency data vertex = 0)
    (other : data.SourceVertex) :
    num_edges (prunedSource data) vertex other = 0 := by
  have hDeg : vertex_degree (prunedSource data) vertex = 0 := by
    rw [vertex_degree_prunedSource, hZero]
    norm_num
  have hSum : (∑ u : data.SourceVertex,
      ((num_edges (prunedSource data) vertex u : ℤ))) = 0 := hDeg
  have hNonneg : ∀ u ∈ (Finset.univ : Finset data.SourceVertex),
      (0 : ℤ) ≤ (num_edges (prunedSource data) vertex u : ℤ) :=
    fun u _ ↦ Int.natCast_nonneg _
  have hZeroAt := (Finset.sum_eq_zero_iff_of_nonneg hNonneg).1 hSum other
    (Finset.mem_univ _)
  exact_mod_cast hZeroAt

/-- An isolated source vertex is a connected component of the pruned source on
its own. -/
theorem component_prunedSource_eq_singleton (data : GluingDatum target degree)
    {vertex : data.SourceVertex} (hZero : nonDanglingValency data vertex = 0) :
    component (prunedSource data) vertex = {vertex} := by
  have hReach : ∀ w : data.SourceVertex,
      Reach (prunedSource data) vertex w → w = vertex := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail b c _ hbc ih =>
        rw [ih, num_edges_prunedSource_eq_zero data hZero c] at hbc
        omega
  ext w
  constructor
  · intro hMem
    exact Finset.mem_singleton.2
      (hReach w ((mem_component (G := prunedSource data) vertex w).1 hMem))
  · intro hMem
    rw [Finset.mem_singleton] at hMem
    subst hMem
    exact self_mem_component _

/-- The isolated vertices are pairwise distinct components. -/
theorem card_isolatedVertices_le_componentCount (data : GluingDatum target degree) :
    (isolatedVertices data).card ≤ componentCount (prunedSource data) := by
  classical
  unfold componentCount
  refine Finset.card_le_card_of_injOn (component (prunedSource data))
    (fun v _ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_
  intro v hv w hw hEq
  have hv0 : nonDanglingValency data v = 0 :=
    (mem_isolatedVertices data v).1 (Finset.mem_coe.1 hv)
  have hw0 : nonDanglingValency data w = 0 :=
    (mem_isolatedVertices data w).1 (Finset.mem_coe.1 hw)
  rw [component_prunedSource_eq_singleton data hv0,
    component_prunedSource_eq_singleton data hw0] at hEq
  exact Finset.singleton_injective hEq

/-- **The first Betti number of the pruned source is nonnegative.** -/
theorem cyclomatic_prunedSource_nonneg (data : GluingDatum target degree) :
    0 ≤ cyclomatic (prunedSource data) :=
  cyclomatic_nonneg _

/-- The spanning-forest bound on the pruned source, in the counts it is made
of: `n ≤ m + c`. -/
theorem card_sourceVertex_le_card_nonDanglingEdges_add_componentCount
    (data : GluingDatum target degree) :
    Fintype.card data.SourceVertex
      ≤ (nonDanglingEdges data).card + componentCount (prunedSource data) := by
  have h := card_V_le_card_edges_add_componentCount (prunedSource data)
  rwa [card_prunedSource_edges] at h

/-- **The Euler relation of the stable graph.**  The handshake
`∑ nd(v) = 2 m` and the splitting of the source vertices into `nd = 0`,
`nd = 2` and `nd ≥ 3` — legitimate because `nd ≠ 1` over a connected quotient
source — combine into a single identity from which the valency-two vertices
have disappeared.  Together with `euler_prunedSource` it is the Euler relation
of the stable graph `H(M)`, whose vertices are `stableVertices data` and whose
edges are the stable paths. -/
theorem sum_stableValency_add_two_mul_card_sourceVertex
    (data : GluingDatum target degree) (hConnected : data.Connected) :
    (∑ vertex ∈ stableVertices data, (nonDanglingValency data vertex : ℤ))
        + 2 * (Fintype.card data.SourceVertex : ℤ)
      = 2 * ((nonDanglingEdges data).card : ℤ)
        + 2 * ((isolatedVertices data).card : ℤ)
        + 2 * ((stableVertices data).card : ℤ) :=
  sum_stable_eq (nonDanglingValency data) (nonDanglingEdges data).card
    (sum_nonDanglingValency data) (nonDanglingValency_ne_one data hConnected)

/-- Every stable vertex contributes at least three to the handshake. -/
theorem three_mul_card_stableVertices_le (data : GluingDatum target degree) :
    3 * ((stableVertices data).card : ℤ)
      ≤ ∑ vertex ∈ stableVertices data, (nonDanglingValency data vertex : ℤ) :=
  three_mul_card_le _

/-- **The Draisma--Vargas Euler bound.**  Writing `b₁` for
`cyclomatic (prunedSource data)` and `c` for its component count,
`|V₃| + 2c ≤ 2 b₁ + 2 |V₀|`; equivalently, the stable graph has at most
`2 (b₁ - c(H))` vertices and at most `3 (b₁ - c(H))` edges. -/
theorem card_stableVertices_add_two_mul_componentCount_le
    (data : GluingDatum target degree) (hConnected : data.Connected) :
    ((stableVertices data).card : ℤ)
        + 2 * (componentCount (prunedSource data) : ℤ)
      ≤ 2 * cyclomatic (prunedSource data)
        + 2 * ((isolatedVertices data).card : ℤ) := by
  have hId := sum_stableValency_add_two_mul_card_sourceVertex data hConnected
  have hGe := three_mul_card_stableVertices_le data
  have hEuler := cyclomatic_prunedSource data
  linarith

/-- The stable graph has at most `2 b₁(Γ)` vertices. -/
theorem card_stableVertices_le_two_mul_cyclomatic
    (data : GluingDatum target degree) (hConnected : data.Connected) :
    ((stableVertices data).card : ℤ) ≤ 2 * cyclomatic (prunedSource data) := by
  have h1 := card_stableVertices_add_two_mul_componentCount_le data hConnected
  have h2 : ((isolatedVertices data).card : ℤ)
      ≤ (componentCount (prunedSource data) : ℤ) := by
    exact_mod_cast card_isolatedVertices_le_componentCount data
  linarith

/-- Trivalence is exactly the statement that the stable handshake is as small
as it can be: if the total stable valency does not exceed three per stable
vertex, every stable valency is exactly three. -/
theorem nonDanglingValency_le_three_of_sum_le (data : GluingDatum target degree)
    (hSat : (∑ vertex ∈ stableVertices data, (nonDanglingValency data vertex : ℤ))
      ≤ 3 * ((stableVertices data).card : ℤ)) :
    ∀ vertex : data.SourceVertex, nonDanglingValency data vertex ≤ 3 :=
  fun vertex ↦ le_three_of_sum_le _ hSat vertex

/-- **Trivalence from a saturated Euler bound.**  The hypothesis is the exact
reverse of `card_stableVertices_add_two_mul_componentCount_le`, so the two
together say the Draisma--Vargas bound is an equality; the conclusion is the
`trivalent` field of
`FullDimensionalSource.FullDimensionalSourcePresentation`.

Hypotheses used, and nothing else: connectedness of the quotient source (for
`nd ≠ 1`), the handshake and Euler identity of `PrunedSource`, and this one
numerical saturation.  In particular `cyclomatic` appears, never `genus`: the
pruned source is generally disconnected. -/
theorem trivalent_of_euler_saturated (data : GluingDatum target degree)
    (hConnected : data.Connected)
    (hSaturated : 2 * cyclomatic (prunedSource data)
        + 2 * ((isolatedVertices data).card : ℤ)
      ≤ ((stableVertices data).card : ℤ)
        + 2 * (componentCount (prunedSource data) : ℤ)) :
    ∀ vertex : data.SourceVertex, nonDanglingValency data vertex ≤ 3 := by
  refine nonDanglingValency_le_three_of_sum_le data ?_
  have hId := sum_stableValency_add_two_mul_card_sourceVertex data hConnected
  have hEuler := cyclomatic_prunedSource data
  linarith

end PrunedSourceCount

end DraismaVargas.LocalCases.Trivalence
