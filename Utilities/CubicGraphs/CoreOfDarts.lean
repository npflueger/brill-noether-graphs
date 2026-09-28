import Utilities.CubicGraphs.CubicCoreDarts

/-!
# Coring a cubic dart graph, and the Whitehead chain restated on cores

The count of Vargas, Part II (arXiv:2609.09109) is carried from the caterpillar
of loops to an arbitrary trivalent type along a chain of trivalent types, each
step a Whitehead move; this is how the proof of the main theorem there uses
the connectivity of the tropical moduli space through codimension one.  The
connectivity theorem of `Utilities.CubicGraphs.WhiteheadConnectivity` lives on
cubic dart graphs `CubicDartGraph D V`, while a subdivision specification is
indexed by an ordered core `Core n p`, and `CubicCoreDarts.ofCore` only runs
`Core → CubicDartGraph`.  Either the chain is restated on cores, or a coring
adapter -- a choice of slot and vertex orderings for a cubic dart graph -- is
built.

## Why the coring adapter suffices

This file builds the **coring adapter**, and on the dart type the chain
actually uses it costs nothing: **the choice of orderings is already made.**

`CubicCoreDarts.ofCore` builds its graph on the dart type `Fin p × Bool` and
the vertex type `Fin n`, with the edge involution `opposite = (e, b) ↦ (e, !b)`
fixed once and for all.  A `Core n p` is nothing but a pair of maps
`tail, head : Fin p → Fin n`.  So a cubic dart graph *on those two types, whose
involution is `opposite`*, **is** a core, read off by `coreOf G = ⟨fun e ↦
G.vert (e, false), fun e ↦ G.vert (e, true)⟩`, with no choice anywhere.  The
two round trips `coreOf_ofCore` and `graph_ofGraph` are `rfl` and a two-line
`ext'`.

The reason this is enough for the chain, rather than only for its endpoints, is
that `CubicDartGraph.move` sets `op := G.op` and changes `vert` alone.  So a
Whitehead move **never leaves the class of graphs whose involution is
`opposite`**, and neither does a finite sequence of them.  The chain
`Reaches (ofCore core) H` therefore descends, graph by graph, to a chain of
honest cores (`exists_chain_of_reaches`): the chain restated on cores is a
corollary of the adapter, not a separate development.

## What is proved here

* `coreOf`, `vertex_coreOf`, `coreOf_cubic`, `coreOf_connected` -- the adapter
  and its two side conditions.  Cubicity is the dart fibre count read through
  `CubicCoreDarts.card_fibre`; connectedness is the cut certificate
  `ExplicitPotential.Core.Connected` derived from `CubicDartGraph.conn` by
  transporting membership in a cut along the dart relation.
* `coreOf_ofCore`, `CubicCore`, `CubicCore.graph`, `CubicCore.ofGraph`,
  `graph_ofGraph`, `ofGraph_graph`, `graph_injective` -- the adapter is an
  inverse pair between `CubicCore n p` and the cubic dart graphs on
  `(Fin p × Bool, Fin n)` whose involution is `opposite`.
* `Step`, `exists_step_of_move`, `exists_chain_of_reaches` -- one Whitehead move
  between cores, and the descent of a whole `Reaches` chain to a
  `Relation.ReflTransGen Step` chain of cores.
* `CoreIso`, `CoreIso.orientation`, `coreIsoOfIso`, `CoreIso.toIso` -- the
  residual relabelling, in core language: a slot permutation, a vertex
  permutation, and a per-slot orientation flip.  `coreIsoOfIso` extracts it from
  a `CubicDartGraph.Iso` and `toIso` puts it back, so `CoreIso c c'` and
  `Nonempty (Iso (ofCore c) (ofCore c'))` are interchangeable and the residual
  is stated at exactly the right strength.
* `exists_chain` -- **the chain on cores**: any two connected cubic cores with
  `2 ≤ p + 1 - n` are joined by a finite chain of core Whitehead steps, up to a
  `CoreIso` at the far end.

## What is NOT proved here -- every surviving hypothesis

* **`exists_chain` ends at a core `CoreIso`-related to the target, not at the
  target itself.**  This is not slack in the proof: a Whitehead move
  precomposes `vert` with a transposition of darts and never touches the vertex
  *labels*, whereas `CubicDarts.reachesIso_of_genus_eq` (in
  `Utilities.CubicGraphs.WhiteheadConnectivity`) concludes `ReachesIso`,
  i.e. reaching a graph *isomorphic* to the target.  The `CoreIso` is therefore
  a genuine residue, and `coreIsoOfIso`/`toIso` show it is exactly the residue
  and no more.  Removing it would need a strictly stronger connectivity theorem
  (moves transitive on *labelled* cubic cores), which is not proved here.  What
  a count needs instead is that its index is a relabelling invariant; that is a
  separate statement, not addressed here.
* Nothing here mentions counts, requests, fibres, multiplicities or weights.  No
  transport of a count is claimed, and no wall is assumed trivalent.
* `coreOf_connected` assumes `G.op = opposite`; without it `coreOf G` need not
  record `G`'s edges at all.  Every use in this file supplies that hypothesis by
  `rfl`.

Consumers: the Draisma--Vargas count.
-/

namespace DraismaVargas.LocalCases.CoreOfDarts

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.CubicDarts.CubicDartGraph
open DraismaVargas.LocalCases.CubicCoreDarts
open Utilities.Certificate.ExplicitPotential (Core)
open Finset

variable {n p : ℕ}

/-! ## 1.  The adapter -/

/-- **The coring adapter.**  A cubic dart graph on the standard slot-end dart
type reads off as a core: slot `e` runs from the vertex of its `false` dart to
the vertex of its `true` dart.  No ordering is chosen -- both orderings are
already part of the types `Fin p × Bool` and `Fin n`. -/
def coreOf (G : CubicDartGraph (Fin p × Bool) (Fin n)) : Core n p where
  tail := fun e ↦ G.vert (e, false)
  head := fun e ↦ G.vert (e, true)

/-- The core's dart-to-vertex map is the graph's, on the nose. -/
theorem vertex_coreOf (G : CubicDartGraph (Fin p × Bool) (Fin n)) :
    vertex (coreOf G) = G.vert := by
  funext d
  rcases d with ⟨e, b⟩
  cases b <;> rfl

/-- Trivalence transfers: the occurrence-sensitive incidence degree of `coreOf G`
at a vertex is the size of that vertex's dart fibre. -/
theorem coreOf_cubic (G : CubicDartGraph (Fin p × Bool) (Fin n)) : (coreOf G).Cubic := by
  intro v
  rw [← card_fibre (coreOf G) v, vertex_coreOf]
  exact G.card_fibre v

/-- Every vertex of a cubic dart graph carries a dart. -/
private theorem exists_dart_at (G : CubicDartGraph (Fin p × Bool) (Fin n)) (v : Fin n) :
    ∃ d : Fin p × Bool, G.vert d = v := by
  classical
  have hcard := G.card_fibre v
  have hne : (univ.filter (fun d ↦ G.vert d = v)).Nonempty := by
    rw [← Finset.card_pos, hcard]
    omega
  obtain ⟨d, hd⟩ := hne
  exact ⟨d, (mem_filter.mp hd).2⟩

/-- **Connectedness transfers.**  `ExplicitPotential.Core.Connected` is a cut
certificate: every proper vertex subset is crossed by a slot.  If no slot
crossed, membership in the cut would be constant along both generating
relations on darts -- across an edge because the two darts of slot `e` are
`(e, false)` and `(e, true)`, and within a vertex trivially -- hence constant on
all darts by `CubicDartGraph.conn`, contradicting properness. -/
theorem coreOf_connected (G : CubicDartGraph (Fin p × Bool) (Fin n))
    (hop : G.op = opposite) : (coreOf G).Connected := by
  classical
  intro S hS
  by_contra hNo
  have hcross : ∀ e : Fin p, ((coreOf G).tail e ∈ S ↔ (coreOf G).head e ∈ S) := by
    intro e
    have h := not_or.mp (not_exists.mp hNo e)
    constructor
    · intro ht
      by_contra hh
      exact h.1 ⟨ht, hh⟩
    · intro hh
      by_contra ht
      exact h.2 ⟨hh, ht⟩
  have hconst : ∀ d d' : Fin p × Bool, G.vert d ∈ S ↔ G.vert d' ∈ S := by
    intro d d'
    have h := G.conn d d'
    induction h with
    | rel x y hxy =>
        rcases hxy with hxy | hxy
        · subst hxy
          rcases x with ⟨e, b⟩
          have hflip : G.op ((e, b) : Fin p × Bool) = ((e, !b) : Fin p × Bool) := by
            rw [hop]
            rfl
          rw [hflip]
          cases b
          · exact hcross e
          · exact (hcross e).symm
        · rw [hxy]
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  obtain ⟨v, w, hv, hw⟩ := hS
  obtain ⟨dv, hdv⟩ := exists_dart_at G v
  obtain ⟨dw, hdw⟩ := exists_dart_at G w
  exact hw (hdw ▸ (hconst dv dw).mp (hdv ▸ hv))

/-- The adapter undoes `CubicCoreDarts.ofCore` definitionally. -/
@[simp] theorem coreOf_ofCore (core : Core n p) (hCubic : core.Cubic)
    (hConnected : core.Connected) : coreOf (ofCore core hCubic hConnected) = core := rfl

/-! ## 2.  Cores bundled with their two side conditions -/

/-- A connected cubic core, bundled.  Whitehead moves preserve both conditions,
so this is the object a chain of cores runs through. -/
structure CubicCore (n p : ℕ) where
  /-- the labelled core -/
  core : Core n p
  /-- trivalence -/
  cubic : core.Cubic
  /-- the cut certificate -/
  connected : core.Connected

namespace CubicCore

/-- The dart graph of a bundled core. -/
def graph (c : CubicCore n p) : CubicDartGraph (Fin p × Bool) (Fin n) :=
  ofCore c.core c.cubic c.connected

@[simp] theorem op_graph (c : CubicCore n p) : c.graph.op = opposite := rfl

@[simp] theorem coreOf_graph (c : CubicCore n p) : coreOf c.graph = c.core := rfl

/-- The inverse adapter on bundled cores. -/
def ofGraph (G : CubicDartGraph (Fin p × Bool) (Fin n)) (hop : G.op = opposite) :
    CubicCore n p :=
  ⟨coreOf G, coreOf_cubic G, coreOf_connected G hop⟩

@[simp] theorem core_ofGraph (G : CubicDartGraph (Fin p × Bool) (Fin n))
    (hop : G.op = opposite) : (ofGraph G hop).core = coreOf G := rfl

/-- One round trip: a cubic dart graph whose involution is `opposite` is the
graph of the core it cores to. -/
theorem graph_ofGraph (G : CubicDartGraph (Fin p × Bool) (Fin n)) (hop : G.op = opposite) :
    (ofGraph G hop).graph = G := by
  refine CubicDartGraph.ext' hop.symm ?_
  funext d
  rcases d with ⟨e, b⟩
  cases b <;> rfl

/-- The other round trip. -/
theorem ofGraph_graph (c : CubicCore n p) : ofGraph c.graph (op_graph c) = c := rfl

theorem graph_injective : Function.Injective (graph (n := n) (p := p)) := by
  intro c c' h
  have := congrArg coreOf h
  cases c
  cases c'
  simpa using this

end CubicCore

/-! ## 3.  The Whitehead chain, restated on cores -/

/-- **One Whitehead move between cores.**  Read on dart graphs, because that is
where the move is defined; `exists_step_of_move` shows the class of graphs this
quantifies over is exactly the graphs of cores. -/
def Step (c c' : CubicCore n p) : Prop := Move c.graph c'.graph

theorem step_symm {c c' : CubicCore n p} (h : Step c c') : Step c' c := Move.symm h

/-- **A move out of a core lands on a core.**  A Whitehead move keeps `op`, so
the moved graph is still `opposite`-involutive and cores back. -/
theorem exists_step_of_move (c : CubicCore n p) {H : CubicDartGraph (Fin p × Bool) (Fin n)}
    (h : Move c.graph H) : ∃ c' : CubicCore n p, c'.graph = H ∧ Step c c' := by
  obtain ⟨m, rfl⟩ := h
  have hop : (c.graph.move m).op = opposite := rfl
  refine ⟨CubicCore.ofGraph _ hop, CubicCore.graph_ofGraph _ hop, ?_⟩
  rw [Step, CubicCore.graph_ofGraph]
  exact ⟨m, rfl⟩

/-- **The chain descends.**  Every graph a `Reaches` chain out of a core visits
is itself the graph of a core, and the chain reads as a chain of core steps.
This restates the Whitehead chain on cores, as a consequence of the adapter. -/
theorem exists_chain_of_reaches (c : CubicCore n p)
    {H : CubicDartGraph (Fin p × Bool) (Fin n)} (h : Reaches c.graph H) :
    ∃ c' : CubicCore n p, c'.graph = H ∧ Relation.ReflTransGen Step c c' := by
  induction h with
  | refl => exact ⟨c, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      obtain ⟨d, hd, hchain⟩ := ih
      subst hd
      obtain ⟨d', hd', hstep'⟩ := exists_step_of_move d hstep
      exact ⟨d', hd', hchain.tail hstep'⟩

/-! ## 4.  The residual relabelling, in core language -/

/-- **A relabelling of cores**: a permutation of slots, a permutation of
vertices, and for each slot a flag saying whether its two ends are exchanged.
`vertex` is `CubicCoreDarts.vertex`, so `vertex c' (slot e, false)` is
`c'.tail (slot e)` and `vertex c' (slot e, true)` is `c'.head (slot e)`;
`CoreIso.orientation` spells the two cases out. -/
structure CoreIso {n p : ℕ} (c c' : Core n p) where
  /-- the slot permutation -/
  slot : Fin p ≃ Fin p
  /-- the vertex permutation -/
  vtx : Fin n ≃ Fin n
  /-- `true` when the slot's two ends are exchanged -/
  flip : Fin p → Bool
  tail_map : ∀ e, vertex c' (slot e, flip e) = vtx (c.tail e)
  head_map : ∀ e, vertex c' (slot e, !flip e) = vtx (c.head e)

namespace CoreIso

variable {c c' : Core n p}

/-- The human-readable form: each slot is carried to its image either keeping
or reversing its orientation. -/
theorem orientation (i : CoreIso c c') (e : Fin p) :
    (c'.tail (i.slot e) = i.vtx (c.tail e) ∧ c'.head (i.slot e) = i.vtx (c.head e)) ∨
      (c'.head (i.slot e) = i.vtx (c.tail e) ∧ c'.tail (i.slot e) = i.vtx (c.head e)) := by
  have ht := i.tail_map e
  have hh := i.head_map e
  cases hf : i.flip e
  · rw [hf] at ht hh
    exact Or.inl ⟨ht, hh⟩
  · rw [hf] at ht hh
    exact Or.inr ⟨ht, hh⟩

/-- A core is relabelled to itself by the identity. -/
def refl (core : Core n p) : CoreIso core core where
  slot := Equiv.refl _
  vtx := Equiv.refl _
  flip := fun _ ↦ false
  tail_map := fun _ ↦ rfl
  head_map := fun _ ↦ rfl

/-- The dart bijection a core relabelling induces. -/
def dartEquiv (i : CoreIso c c') : (Fin p × Bool) ≃ (Fin p × Bool) where
  toFun := fun d ↦ (i.slot d.1, xor d.2 (i.flip d.1))
  invFun := fun d ↦ (i.slot.symm d.1, xor d.2 (i.flip (i.slot.symm d.1)))
  left_inv := by
    rintro ⟨e, b⟩
    have h : i.slot.symm (i.slot e) = e := i.slot.symm_apply_apply e
    simp only [h, Prod.mk.injEq, true_and]
    cases b <;> cases i.flip e <;> rfl
  right_inv := by
    rintro ⟨e, b⟩
    have h : i.slot (i.slot.symm e) = e := i.slot.apply_symm_apply e
    simp only [h, Prod.mk.injEq, true_and]
    cases b <;> cases i.flip (i.slot.symm e) <;> rfl

theorem dartEquiv_apply (i : CoreIso c c') (d : Fin p × Bool) :
    i.dartEquiv d = (i.slot d.1, xor d.2 (i.flip d.1)) := rfl

@[simp] theorem dartEquiv_false (i : CoreIso c c') (e : Fin p) :
    i.dartEquiv (e, false) = (i.slot e, i.flip e) := by
  simp [dartEquiv_apply]

@[simp] theorem dartEquiv_true (i : CoreIso c c') (e : Fin p) :
    i.dartEquiv (e, true) = (i.slot e, !(i.flip e)) := by
  simp [dartEquiv_apply]

end CoreIso

/-- **A graph isomorphism is a core relabelling.**  Its dart bijection commutes
with `opposite`, so it is a slot permutation together with a per-slot flip; its
vertex bijection is the vertex permutation. -/
noncomputable def coreIsoOfIso {c c' : CubicCore n p} (i : Iso c.graph c'.graph) :
    CoreIso c.core c'.core := by
  classical
  let f : Fin p → Fin p := fun e ↦ (i.dart (e, false)).1
  let t : Fin p → Bool := fun e ↦ (i.dart (e, false)).2
  have hdart_false : ∀ e, i.dart (e, false) = (f e, t e) := fun _ ↦ rfl
  have hdart_true : ∀ e, i.dart (e, true) = (f e, !(t e)) := by
    intro e
    have hop := i.op_map ((e, false) : Fin p × Bool)
    have h₁ : c'.graph.op (i.dart (e, false)) = opposite (i.dart (e, false)) := rfl
    have h₂ : c.graph.op ((e, false) : Fin p × Bool) = ((e, true) : Fin p × Bool) := rfl
    rw [h₁, h₂] at hop
    rw [← hop, hdart_false e]
    rfl
  have hinj : Function.Injective f := by
    intro e e' hee
    by_cases hb : t e = t e'
    · have hd : i.dart (e, false) = i.dart (e', false) := by
        rw [hdart_false, hdart_false, hee, hb]
      exact congrArg Prod.fst (i.dart.injective hd)
    · have hne : t e' = !(t e) := by
        cases h₁ : t e <;> cases h₂ : t e' <;>
          first
            | rfl
            | exact absurd (h₁.trans h₂.symm) hb
      have hd : i.dart (e', false) = i.dart (e, true) := by
        rw [hdart_false, hdart_true, hee, hne]
      exact absurd (congrArg Prod.snd (i.dart.injective hd)) (by simp)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), i.vtx, t, ?_, ?_⟩
  · intro e
    have hv := i.vert_map ((e, false) : Fin p × Bool)
    rw [hdart_false e] at hv
    exact hv
  · intro e
    have hv := i.vert_map ((e, true) : Fin p × Bool)
    rw [hdart_true e] at hv
    exact hv

/-- **And conversely**, so nothing is lost in passing to `CoreIso`: the residue
of `exists_chain` is exactly a relabelling of cores, neither weaker nor
stronger than a dart-graph isomorphism. -/
def CoreIso.toIso {c c' : CubicCore n p} (i : CoreIso c.core c'.core) :
    Iso c.graph c'.graph where
  dart := i.dartEquiv
  vtx := i.vtx
  op_map := by
    rintro ⟨e, b⟩
    cases b
    · show opposite (i.dartEquiv (e, false)) = i.dartEquiv (e, true)
      rw [CoreIso.dartEquiv_false, CoreIso.dartEquiv_true]
      rfl
    · show opposite (i.dartEquiv (e, true)) = i.dartEquiv (e, false)
      rw [CoreIso.dartEquiv_true, CoreIso.dartEquiv_false]
      cases i.flip e <;> rfl
  vert_map := by
    rintro ⟨e, b⟩
    cases b
    · show vertex c'.core (i.dartEquiv (e, false)) = i.vtx (c.core.tail e)
      rw [CoreIso.dartEquiv_false]
      exact i.tail_map e
    · show vertex c'.core (i.dartEquiv (e, true)) = i.vtx (c.core.head e)
      rw [CoreIso.dartEquiv_true]
      exact i.head_map e

/-! ## 5.  The chain on cores -/

/-- **Whitehead connectivity of connected cubic cores.**  Any two of them of the
same genus at least two are joined by a finite chain of core Whitehead steps,
ending at a core that is a relabelling of the target.

The relabelling is the residue discussed in the module docstring:
`CubicDarts.reachesIso_of_genus_eq` reaches a graph isomorphic to the target,
and a Whitehead move cannot permute vertex labels. -/
theorem exists_chain (c c' : CubicCore n p) (hGenus : 2 ≤ p + 1 - n) :
    ∃ c'' : CubicCore n p, Relation.ReflTransGen Step c c'' ∧
      Nonempty (CoreIso c''.core c'.core) := by
  have hgenus : c.graph.genus = p + 1 - n := genus_ofCore c.core c.cubic c.connected
  obtain ⟨K, hReach, ⟨iso⟩⟩ := reachesIso_of_genus_eq c.graph c'.graph (by omega) rfl
  obtain ⟨c'', hK, hchain⟩ := exists_chain_of_reaches c hReach
  subst hK
  exact ⟨c'', hchain, ⟨coreIsoOfIso iso⟩⟩

end DraismaVargas.LocalCases.CoreOfDarts
