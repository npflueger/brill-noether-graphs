module

public import DraismaVargasCount.TargetNormalForm

@[expose] public section

/-!
# A walk and cycle calculus for the target graph

**Source.**  Draisma--Vargas Part I (arXiv:1909.12924), section *Notation*: the
target of the morphisms considered is a tree.  Vargas, Part II
(arXiv:2609.09109): the pass-once condition (`def-auxiliary-conditions`,
`lm:properties`), whose proof is the ordered walk of a stable row.  `RowWalk`
§5 ("No backtracking") reduces the row statements to the target-side theorem
this file supplies: a non-backtracking walk in a tree does not repeat an
occurrence.

For `CFGraph`, `graph_connected` is a cut condition, `genus` is
`|E| - |V| + 1`, and `Count.TargetNormalForm` gives a rooted-tree normal form but
no path structure.  This file builds a walk and cycle calculus from scratch, for
a `CFGraph` **alone**: nothing here mentions a gluing datum, a sheet, a degree or
a multiplicity.

## What is proved

### 1.  Darts

`CFGraph` stores an occurrence as an **ordered pair** with no symmetry
condition -- which is exactly why `TargetNormalForm.NormalForm` carries an
orientation bit (its `flip`, and `inPath` there shows the un-oriented statement
is false).  A walk therefore cannot be a list of occurrences: it must record
which stored endpoint it arrives by.  `Dart` is an occurrence together with
that bit, with `tail`, `head` and `reverse`; `Step` is "leaves where the
previous one arrives, by a *different* occurrence"; `IsWalk` is the resulting
`List.IsChain`.  `isWalk_reverse` reverses a walk.

### 2.  Tree ranks

`TreeRank G` is a vertex numbering `rank` for which the two ends of every
occurrence are separated and an occurrence is **determined by its end of larger
rank** (`high_injective`).  That last field is the unique-parent-occurrence
statement, and it is where genus zero enters.  `orientedTreeRank` exhibits it
for the whole normal-form family `TargetNormalForm.orientedTree`, `comapTreeRank`
transports it along the occurrence bijection that a `NormalForm` stores as data,
and `exists_treeRank` concludes: **every connected genus-zero `CFGraph` carries
a tree rank.**  `up` is the induced parent map on vertices.

### 3.  The theorem

* `TreeRank.ascending_of_step` -- the local step: a walk that has just climbed
  cannot descend, because the vertex it reached is the larger end of the
  occurrence it arrived by and that occurrence is the only one of which it is.
* `TreeRank.nodup_fork` -- the induction: a walk is an ascending run reversed
  followed by an ascending run, and two ascending runs leaving one vertex by
  different occurrences stay apart (`TreeRank.edge_ne_of_fork`).
* `TreeRank.nodup_edges`, `nodup_edges_of_genusZero` -- **a non-backtracking
  walk in a connected genus-zero graph never repeats an occurrence**, and
  `eq_of_edge_eq*` is the injectivity form.
* `TreeRank.no_closed_walk`, `no_closed_walk_of_genusZero` -- **there is no
  closed non-backtracking walk**; `tail_ne_head_of_*` is the vertex form (a walk
  does not return to the vertex it started from).
* `TreeRank.eq_of_incident`, `eq_of_incident_of_genusZero` -- **no two
  occurrences join the same two vertices**, the graph-only content of
  `Count.RowWalk.SimpleTarget`.

### 4.  The shapes a consumer applies

`nodup_map_of_isChain` takes a list over an arbitrary index type carrying an
occurrence and the two ends by which the walk enters and leaves it.
`IsWalkFrom`/`nodup_of_isWalkFrom` take instead a list of occurrences and a
single starting vertex, computing every later vertex: this is the shape a
source-side traversal produces, and it is what `Count.RowGeodesic` feeds.

## What is NOT proved here

* Nothing about gluing data, stable rows, indices or denominators: the
  datum-side application is `DraismaVargas.Count.RowGeodesic`, which is where
  `Count.RowWalk.RowTargetInjective` and `Count.RowWalk.SimpleTarget` are
  discharged.
* `exists_treeRank` assumes exactly `graph_connected G` and `genus G = 0`, both
  explicit.  The `TreeRank`-level theorems assume only the structure, so they
  hold for a forest as well; connectivity is used only to produce one.
* No transport along a `Count.Transport.DatumIso` is needed: `NormalForm`
  already carries the occurrence bijection, and `comapTreeRank` uses it
  directly.

## Non-vacuity

`catTreeRank` inhabits `TreeRank` on the caterpillar target `T^CL_g`
(it is `orientedTreeRank` on the nose, since `catTree` is
a `rootedTree`), and `isWalk_catTree` exhibits a genuine two-step
non-backtracking walk there, through the two occurrences at the root.

## Consumers

`DraismaVargas.Count.RowGeodesic`, and through it the row-denominator inputs of
the multiplicity balances at walls and at type changes.
-/

namespace DraismaVargas.Count.TargetGeodesic

open DraismaVargas.Infrastructure
open DraismaVargas.Count.TargetNormalForm

variable {G : CFGraph.{0}}

/-! ## 1. The two ends of an occurrence, ordered by a rank -/

/-- The end of the occurrence `edge` at which `rank` is the larger. -/
def highEnd (rank : G.V → ℕ) (edge : G.edges) : G.V :=
  if rank (edge : G.V × G.V).1 < rank (edge : G.V × G.V).2 then (edge : G.V × G.V).2
  else (edge : G.V × G.V).1

/-- The end of the occurrence `edge` at which `rank` is the smaller. -/
def lowEnd (rank : G.V → ℕ) (edge : G.edges) : G.V :=
  if rank (edge : G.V × G.V).1 < rank (edge : G.V × G.V).2 then (edge : G.V × G.V).1
  else (edge : G.V × G.V).2

theorem ends_eq (rank : G.V → ℕ) (edge : G.edges) :
    ((edge : G.V × G.V).1 = lowEnd rank edge ∧ (edge : G.V × G.V).2 = highEnd rank edge) ∨
      ((edge : G.V × G.V).1 = highEnd rank edge ∧ (edge : G.V × G.V).2 = lowEnd rank edge) := by
  unfold highEnd lowEnd
  split_ifs with h
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

theorem rank_lowEnd_lt_rank_highEnd {rank : G.V → ℕ} {edge : G.edges}
    (hNe : rank (edge : G.V × G.V).1 ≠ rank (edge : G.V × G.V).2) :
    rank (lowEnd rank edge) < rank (highEnd rank edge) := by
  unfold highEnd lowEnd
  split_ifs with h
  · exact h
  · omega

/-- **A rank exhibiting the graph as a forest.**  A vertex numbering for which
the two ends of every occurrence are separated, and for which an occurrence is
determined by its end of larger rank.  For a connected genus-zero graph this
is the depth-first numbering of `Count.TargetNormalForm`; the second field is
the statement that a non-root vertex has a *unique* incident occurrence of
lower rank, which is where genus zero enters. -/
structure TreeRank (G : CFGraph.{0}) where
  /-- The vertex numbering. -/
  rank : G.V → ℕ
  /-- The two ends of an occurrence have different ranks. -/
  rank_ne : ∀ edge : G.edges,
    rank (edge : G.V × G.V).1 ≠ rank (edge : G.V × G.V).2
  /-- An occurrence is determined by its end of larger rank. -/
  high_injective : Function.Injective (highEnd rank)

namespace TreeRank

variable (A : TreeRank G)

/-- The end of larger rank. -/
abbrev high (edge : G.edges) : G.V := highEnd A.rank edge

/-- The end of smaller rank. -/
abbrev low (edge : G.edges) : G.V := lowEnd A.rank edge

theorem rank_low_lt (edge : G.edges) : A.rank (A.low edge) < A.rank (A.high edge) :=
  rank_lowEnd_lt_rank_highEnd (A.rank_ne edge)

theorem ends (edge : G.edges) :
    ((edge : G.V × G.V).1 = A.low edge ∧ (edge : G.V × G.V).2 = A.high edge) ∨
      ((edge : G.V × G.V).1 = A.high edge ∧ (edge : G.V × G.V).2 = A.low edge) :=
  ends_eq A.rank edge

theorem low_ne_high (edge : G.edges) : A.low edge ≠ A.high edge := by
  intro h
  have := A.rank_low_lt edge
  rw [h] at this
  exact lt_irrefl _ this

/-- The two ends of an occurrence, as an unordered alternative. -/
theorem eq_low_or_eq_high {edge : G.edges} {vertex : G.V}
    (h : (edge : G.V × G.V).1 = vertex ∨ (edge : G.V × G.V).2 = vertex) :
    vertex = A.low edge ∨ vertex = A.high edge := by
  rcases A.ends edge with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h with h | h
  · exact Or.inl (h.symm.trans h1)
  · exact Or.inr (h.symm.trans h2)
  · exact Or.inr (h.symm.trans h1)
  · exact Or.inl (h.symm.trans h2)

end TreeRank


/-! ## 2. Pulling a tree rank back -/

theorem highEnd_comap {H : CFGraph.{0}} (rank : H.V → ℕ) (ve : G.V → H.V)
    (ee : G.edges → H.edges)
    (h1 : ∀ e : G.edges, ((ee e : H.edges) : H.V × H.V).1 = ve (e : G.V × G.V).1)
    (h2 : ∀ e : G.edges, ((ee e : H.edges) : H.V × H.V).2 = ve (e : G.V × G.V).2)
    (e : G.edges) :
    ve (highEnd (fun v => rank (ve v)) e) = highEnd rank (ee e) := by
  unfold highEnd
  rw [h1 e, h2 e]
  split_ifs <;> rfl

/-- **Pulling a tree rank back along an occurrence-respecting comparison.** -/
def comapTreeRank {H : CFGraph.{0}} (A : TreeRank H) (ve : G.V → H.V)
    (ee : G.edges → H.edges) (hee : Function.Injective ee)
    (h1 : ∀ e : G.edges, ((ee e : H.edges) : H.V × H.V).1 = ve (e : G.V × G.V).1)
    (h2 : ∀ e : G.edges, ((ee e : H.edges) : H.V × H.V).2 = ve (e : G.V × G.V).2) :
    TreeRank G where
  rank := fun v => A.rank (ve v)
  rank_ne := by
    intro e
    rw [← h1 e, ← h2 e]
    exact A.rank_ne (ee e)
  high_injective := by
    intro e f hEq
    refine hee (A.high_injective ?_)
    rw [← highEnd_comap A.rank ve ee h1 h2 e, ← highEnd_comap A.rank ve ee h1 h2 f]
    exact congrArg ve hEq

/-! ## 3. The normal-form family is a tree rank -/

section Oriented

variable (n : ℕ) (parent : Fin n → Fin (n + 1))
  (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) (flip : Fin n → Bool)

theorem highEnd_occ (i : Fin n) :
    highEnd (fun v : (orientedTree n parent hparent flip).V => v.val)
      (occ n parent hparent flip i) = i.succ := by
  have hcoe : ((occ n parent hparent flip i :
      (orientedTree n parent hparent flip).edges) :
        (orientedTree n parent hparent flip).V ×
          (orientedTree n parent hparent flip).V) = orientedEdge n parent flip i := rfl
  have hi := hparent i
  unfold highEnd
  rw [hcoe]
  unfold orientedEdge
  split_ifs with hflip hlt hlt
  · simp only [Fin.val_succ] at hlt
    omega
  · rfl
  · rfl
  · simp only [Fin.val_succ] at hlt
    omega

/-- **The oriented rooted tree carries its vertex numbering as a tree rank.**
The parent map points to strictly smaller numbers, so the end of larger number
of the occurrence of tree edge `i` is `i.succ`, and `i` is recovered from it. -/
def orientedTreeRank : TreeRank (orientedTree n parent hparent flip) where
  rank := fun v => v.val
  rank_ne := by
    intro e
    obtain ⟨i, hi⟩ := (occ_bijective n parent hparent flip).2 e
    subst hi
    have hcoe : ((occ n parent hparent flip i :
        (orientedTree n parent hparent flip).edges) :
          (orientedTree n parent hparent flip).V ×
            (orientedTree n parent hparent flip).V) = orientedEdge n parent flip i := rfl
    rw [hcoe]
    intro hEq
    exact orientedEdge_fst_ne_snd n parent hparent flip i (Fin.ext hEq)
  high_injective := by
    intro e f hEq
    obtain ⟨i, hi⟩ := (occ_bijective n parent hparent flip).2 e
    obtain ⟨j, hj⟩ := (occ_bijective n parent hparent flip).2 f
    subst hi
    subst hj
    rw [highEnd_occ n parent hparent flip i, highEnd_occ n parent hparent flip j] at hEq
    exact congrArg _ (Fin.succ_injective _ hEq)

end Oriented

/-! ## 4. Existence -/

/-- **Every connected genus-zero target carries a tree rank.**  The numbering is
`Count.TargetNormalForm.exists_normalForm`'s; the occurrence bijection it stores
as data is what transports the tree rank back. -/
theorem exists_treeRank (G : CFGraph.{0}) (hConn : graph_connected G)
    (hGenus : genus G = 0) : Nonempty (TreeRank G) := by
  obtain ⟨nf⟩ := exists_normalForm G hConn hGenus _ rfl
  exact ⟨comapTreeRank (orientedTreeRank _ nf.parent nf.parent_le nf.flip)
    nf.vertexEquiv nf.edgeEquiv nf.edgeEquiv.injective nf.ends_fst nf.ends_snd⟩


/-! ## 5. Darts and non-backtracking walks -/

/-- A **dart**: an occurrence of `G` together with the end it is traversed
towards.  `CFGraph` stores an occurrence as an *ordered* pair with no symmetry
condition, so a walk cannot be a list of occurrences: it must record which of
the two stored endpoints it arrives by.  `reversed = false` means the
occurrence is traversed from its first stored end to its second. -/
structure Dart (G : CFGraph.{0}) where
  /-- The occurrence traversed. -/
  edge : G.edges
  /-- `false`: from the first stored end to the second. -/
  reversed : Bool

namespace Dart

/-- The end the dart is traversed away from. -/
def tail (dart : Dart G) : G.V :=
  if dart.reversed then (dart.edge : G.V × G.V).2 else (dart.edge : G.V × G.V).1

/-- The end the dart is traversed towards. -/
def head (dart : Dart G) : G.V :=
  if dart.reversed then (dart.edge : G.V × G.V).1 else (dart.edge : G.V × G.V).2

/-- The same occurrence, traversed the other way. -/
def reverse (dart : Dart G) : Dart G := ⟨dart.edge, !dart.reversed⟩

@[simp] theorem reverse_edge (dart : Dart G) : dart.reverse.edge = dart.edge := rfl

@[simp] theorem reverse_tail (dart : Dart G) : dart.reverse.tail = dart.head := by
  unfold reverse tail head
  cases dart.reversed <;> simp

@[simp] theorem reverse_head (dart : Dart G) : dart.reverse.head = dart.tail := by
  unfold reverse tail head
  cases dart.reversed <;> simp

theorem coe_fst_ne_snd (edge : G.edges) :
    (edge : G.V × G.V).1 ≠ (edge : G.V × G.V).2 := by
  intro hEq
  have hMem : (edge : G.V × G.V) ∈ G.edges := Multiset.coe_mem
  have hPair : (edge : G.V × G.V) =
      ((edge : G.V × G.V).1, (edge : G.V × G.V).1) := by
    apply Prod.ext
    · rfl
    · exact hEq.symm
  rw [hPair] at hMem
  exact G.loopless _ hMem

theorem tail_ne_head (dart : Dart G) : dart.tail ≠ dart.head := by
  unfold tail head
  cases dart.reversed
  · simpa using coe_fst_ne_snd dart.edge
  · simpa using (coe_fst_ne_snd dart.edge).symm

end Dart

/-- The step relation of a walk: the next dart leaves where this one arrives,
and it does so by a **different** occurrence.  This is exactly the
no-backtracking condition; `Count.RowWalk.target_ne_of_row` is its source-side
witness. -/
def Step (first second : Dart G) : Prop :=
  first.head = second.tail ∧ first.edge ≠ second.edge

/-- A **non-backtracking walk** of `G`. -/
def IsWalk (walk : List (Dart G)) : Prop := walk.IsChain Step

theorem isWalk_nil : IsWalk ([] : List (Dart G)) := List.isChain_nil

theorem isWalk_singleton (dart : Dart G) : IsWalk [dart] := List.isChain_singleton _

theorem IsWalk.tail {dart : Dart G} {walk : List (Dart G)}
    (h : IsWalk (dart :: walk)) : IsWalk walk := List.IsChain.tail h

theorem IsWalk.step {first second : Dart G} {walk : List (Dart G)}
    (h : IsWalk (first :: second :: walk)) : Step first second :=
  (List.isChain_cons_cons.mp h).1

theorem IsWalk.cons {dart : Dart G} {walk : List (Dart G)} (h : IsWalk walk)
    (hStep : ∀ second ∈ walk.head?, Step dart second) : IsWalk (dart :: walk) :=
  List.isChain_cons.mpr ⟨hStep, h⟩

/-- **The reverse of a non-backtracking walk is one.** -/
theorem isWalk_reverse {walk : List (Dart G)} (h : IsWalk walk) :
    IsWalk ((walk.map Dart.reverse).reverse) := by
  rw [IsWalk, List.isChain_reverse, List.isChain_map]
  refine h.imp ?_
  intro first second hStep
  exact ⟨by simpa using hStep.1.symm, by simpa using (Ne.symm hStep.2)⟩

/-! ## 6. Ascending darts -/

namespace TreeRank

variable (A : TreeRank G)

/-- A dart is **ascending** when it is traversed towards its end of larger
rank. -/
def Ascending (dart : Dart G) : Prop := A.rank dart.tail < A.rank dart.head

theorem ends_dart (dart : Dart G) :
    (dart.tail = A.low dart.edge ∧ dart.head = A.high dart.edge) ∨
      (dart.tail = A.high dart.edge ∧ dart.head = A.low dart.edge) := by
  unfold Dart.tail Dart.head
  rcases A.ends dart.edge with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases dart.reversed
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact Or.inl ⟨h2, h1⟩

theorem not_ascending_of_ends (dart : Dart G) (h1 : dart.tail = A.high dart.edge)
    (h2 : dart.head = A.low dart.edge) : ¬ A.Ascending dart := by
  show ¬ (A.rank dart.tail < A.rank dart.head)
  rw [h1, h2]
  exact Nat.not_lt.mpr (A.rank_low_lt dart.edge).le

theorem ascending_of_ends (dart : Dart G) (h1 : dart.tail = A.low dart.edge)
    (h2 : dart.head = A.high dart.edge) : A.Ascending dart := by
  show A.rank dart.tail < A.rank dart.head
  rw [h1, h2]
  exact A.rank_low_lt dart.edge

theorem head_eq_high (dart : Dart G) (hAsc : A.Ascending dart) :
    dart.head = A.high dart.edge := by
  rcases A.ends_dart dart with ⟨-, h⟩ | ⟨h1, h2⟩
  · exact h
  · exact absurd hAsc (A.not_ascending_of_ends dart h1 h2)

theorem tail_eq_low (dart : Dart G) (hAsc : A.Ascending dart) :
    dart.tail = A.low dart.edge := by
  rcases A.ends_dart dart with ⟨h, -⟩ | ⟨h1, h2⟩
  · exact h
  · exact absurd hAsc (A.not_ascending_of_ends dart h1 h2)

theorem tail_eq_high (dart : Dart G) (hAsc : ¬ A.Ascending dart) :
    dart.tail = A.high dart.edge := by
  rcases A.ends_dart dart with ⟨h1, h2⟩ | ⟨h, -⟩
  · exact absurd (A.ascending_of_ends dart h1 h2) hAsc
  · exact h

theorem ascending_reverse (dart : Dart G) (hAsc : ¬ A.Ascending dart) :
    A.Ascending dart.reverse := by
  have h1 := A.tail_eq_high dart hAsc
  rcases A.ends_dart dart with ⟨hl, -⟩ | ⟨-, h2⟩
  · exact absurd (h1.symm.trans hl) (A.low_ne_high dart.edge).symm
  · refine A.ascending_of_ends dart.reverse ?_ ?_
    · rw [Dart.reverse_tail, h2, Dart.reverse_edge]
    · rw [Dart.reverse_head, h1, Dart.reverse_edge]

/-- **The local step of the walk calculus.**  A walk that has just gone up
cannot come back down: the vertex it reached is the larger end of the
occurrence it arrived by, that occurrence is the only one of which it is the
larger end, and the walk continues by a different one. -/
theorem ascending_of_step {first second : Dart G} (hStep : Step first second)
    (hAsc : A.Ascending first) :
    A.Ascending second ∧ A.rank first.head < A.rank second.head := by
  have hSecond : A.Ascending second := by
    by_contra hNot
    refine hStep.2 (A.high_injective ?_)
    show A.high first.edge = A.high second.edge
    rw [← A.head_eq_high first hAsc, ← A.tail_eq_high second hNot, hStep.1]
  refine ⟨hSecond, ?_⟩
  rw [hStep.1]
  exact hSecond

/-- Once a walk ascends it ascends for ever. -/
theorem ascending_of_mem : ∀ (dart : Dart G) (walk : List (Dart G)),
    IsWalk (dart :: walk) → A.Ascending dart → ∀ other ∈ dart :: walk, A.Ascending other := by
  intro dart walk
  induction walk generalizing dart with
  | nil =>
      intro _ hAsc other hOther
      rcases List.mem_singleton.mp hOther with h
      exact h ▸ hAsc
  | cons second rest ih =>
      intro hWalk hAsc other hOther
      have hSecond : A.Ascending second := (A.ascending_of_step hWalk.step hAsc).1
      rcases List.mem_cons.mp hOther with h | h
      · exact h ▸ hAsc
      · exact ih second hWalk.tail hSecond other h

end TreeRank

/-! ## 7. The parent map and the ascending runs -/

/-- A chain for a transitive relation is pairwise. -/
private theorem pairwise_of_isChain {α : Type*} {R : α → α → Prop}
    (htrans : ∀ a b c : α, R a b → R b c → R a c) {l : List α} (h : l.IsChain R) :
    l.Pairwise R := by
  induction h with
  | nil => exact List.Pairwise.nil
  | singleton a => exact List.pairwise_singleton _ _
  | cons_cons hr _ ih =>
      refine List.Pairwise.cons ?_ ih
      intro c hc
      rcases List.mem_cons.mp hc with hc | hc
      · exact hc ▸ hr
      · exact htrans _ _ _ hr ((List.pairwise_cons.mp ih).1 c hc)

namespace TreeRank

variable (A : TreeRank G)

open Classical in
/-- **The parent of a vertex**: the smaller end of the unique occurrence of
which it is the larger end, and the vertex itself when there is none (the root,
or an isolated vertex).  `high_injective` is exactly what makes this a
function. -/
noncomputable def up (vertex : G.V) : G.V :=
  if h : ∃ edge : G.edges, A.high edge = vertex then A.low h.choose else vertex

theorem up_high (edge : G.edges) : A.up (A.high edge) = A.low edge := by
  have hex : ∃ other : G.edges, A.high other = A.high edge := ⟨edge, rfl⟩
  unfold up
  rw [dite_eq_left hex]
  exact congrArg A.low (A.high_injective hex.choose_spec)

theorem rank_up_le (vertex : G.V) : A.rank (A.up vertex) ≤ A.rank vertex := by
  unfold up
  split_ifs with h
  · have hspec : A.high h.choose = vertex := h.choose_spec
    have hlt := A.rank_low_lt h.choose
    rw [hspec] at hlt
    exact hlt.le
  · exact le_refl _

theorem rank_iterate_up_le (k : ℕ) (vertex : G.V) :
    A.rank (A.up^[k] vertex) ≤ A.rank vertex := by
  induction k generalizing vertex with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      exact le_trans (ih (A.up vertex)) (A.rank_up_le vertex)

theorem up_head (dart : Dart G) (hAsc : A.Ascending dart) : A.up dart.head = dart.tail := by
  rw [A.head_eq_high dart hAsc, A.up_high, ← A.tail_eq_low dart hAsc]

/-- Along an ascending run the larger ends climb strictly. -/
theorem rank_high_pairwise {walk : List (Dart G)} (hWalk : IsWalk walk)
    (hAll : ∀ dart ∈ walk, A.Ascending dart) :
    walk.Pairwise (fun first second =>
      A.rank (A.high first.edge) < A.rank (A.high second.edge)) := by
  refine pairwise_of_isChain ?_ (hWalk.imp_of_mem_imp ?_)
  · intro a b c hab hbc
    exact lt_trans hab hbc
  · intro a b ha hb hStep
    have hAscA := hAll a ha
    have hAscB := hAll b hb
    rw [← A.head_eq_high a hAscA, ← A.head_eq_high b hAscB]
    exact (A.ascending_of_step hStep hAscA).2

/-- **An ascending run repeats no occurrence.** -/
theorem nodup_edges_of_ascending {walk : List (Dart G)} (hWalk : IsWalk walk)
    (hAll : ∀ dart ∈ walk, A.Ascending dart) : (walk.map Dart.edge).Nodup := by
  have hPair : (walk.map Dart.edge).Pairwise (· ≠ ·) :=
    List.pairwise_map.mpr ((A.rank_high_pairwise hWalk hAll).imp
      (fun {a b} hlt hEq => absurd (congrArg (fun e => A.rank (A.high e)) hEq)
        (Nat.ne_of_lt hlt)))
  exact hPair

/-- The larger ends of an ascending run are all reached from the first one by
iterated parents. -/
theorem exists_iterate_up : ∀ (first : Dart G) (walk : List (Dart G)),
    IsWalk (first :: walk) → (∀ dart ∈ first :: walk, A.Ascending dart) →
    ∀ dart ∈ first :: walk, ∃ k, A.up^[k] dart.head = first.head := by
  intro first walk
  induction walk generalizing first with
  | nil =>
      intro _ _ dart hdart
      exact ⟨0, by rw [Function.iterate_zero_apply, List.mem_singleton.mp hdart]⟩
  | cons second rest ih =>
      intro hWalk hAll dart hdart
      rcases List.mem_cons.mp hdart with h | h
      · exact ⟨0, by rw [Function.iterate_zero_apply, h]⟩
      · obtain ⟨k, hk⟩ := ih second hWalk.tail
          (fun x hx => hAll x (List.mem_cons_of_mem _ hx)) dart h
        refine ⟨k + 1, ?_⟩
        rw [Function.iterate_succ_apply', hk,
          A.up_head second (hAll second (by simp))]
        exact hWalk.step.1.symm

private theorem absurd_iterate {vertex : G.V} {a b : ℕ} (hab : a < b)
    {dartOne dartTwo : Dart G} (hAscOne : A.Ascending dartOne)
    (hAscTwo : A.Ascending dartTwo)
    (hTail : A.rank dartOne.tail = A.rank dartTwo.tail)
    (ha : A.up^[a] vertex = dartOne.head) (hb : A.up^[b] vertex = dartTwo.head) : False := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, b = c + (a + 1) := ⟨b - a - 1, by omega⟩
  have hsplit : A.up^[b] vertex = A.up^[c] (A.up (A.up^[a] vertex)) := by
    rw [hc, Function.iterate_add_apply, Function.iterate_succ_apply']
  rw [ha, A.up_head dartOne hAscOne, hb] at hsplit
  have hle := A.rank_iterate_up_le c dartOne.tail
  rw [← hsplit] at hle
  have hlt : A.rank dartTwo.tail < A.rank dartTwo.head := hAscTwo
  omega

/-- **Two ascending runs leaving one vertex by different occurrences stay
apart.**  This is the only place the tree structure is used twice over: the
larger ends of one run climb out of the first run's occurrence and those of the
other out of a different one, and the parent chain cannot reconcile them. -/
theorem edge_ne_of_fork {walkOne walkTwo : List (Dart G)} {firstOne firstTwo : Dart G}
    (hOne : IsWalk (firstOne :: walkOne)) (hTwo : IsWalk (firstTwo :: walkTwo))
    (hAllOne : ∀ dart ∈ firstOne :: walkOne, A.Ascending dart)
    (hAllTwo : ∀ dart ∈ firstTwo :: walkTwo, A.Ascending dart)
    (hTail : firstOne.tail = firstTwo.tail) (hEdge : firstOne.edge ≠ firstTwo.edge) :
    ∀ dart ∈ firstOne :: walkOne, ∀ other ∈ firstTwo :: walkTwo, dart.edge ≠ other.edge := by
  intro dart hdart other hother hEq
  obtain ⟨a, ha⟩ := A.exists_iterate_up firstOne walkOne hOne hAllOne dart hdart
  obtain ⟨b, hb⟩ := A.exists_iterate_up firstTwo walkTwo hTwo hAllTwo other hother
  have hHeads : dart.head = other.head := by
    rw [A.head_eq_high dart (hAllOne dart hdart),
      A.head_eq_high other (hAllTwo other hother), hEq]
  rw [hHeads] at ha
  have hAscOne : A.Ascending firstOne := hAllOne firstOne (by simp)
  have hAscTwo : A.Ascending firstTwo := hAllTwo firstTwo (by simp)
  rcases lt_trichotomy a b with h | h | h
  · exact A.absurd_iterate h hAscOne hAscTwo (congrArg A.rank hTail) ha hb
  · subst h
    refine hEdge (A.high_injective ?_)
    show A.high firstOne.edge = A.high firstTwo.edge
    rw [← A.head_eq_high firstOne hAscOne, ← A.head_eq_high firstTwo hAscTwo, ← ha, ← hb]
  · exact A.absurd_iterate h hAscTwo hAscOne (congrArg A.rank hTail.symm) hb ha


/-! ## 8. No closed non-backtracking walk, and occurrence-injectivity -/

/-- **The walk splits into a descending part and an ascending part.**  The
induction is on the second list: an ascending prefix already traversed (stored
reversed, so that it too ascends out of the fork) and the remainder of the walk.
Each descending step of the remainder is moved onto the ascending prefix; the
first ascending step of the remainder ends the recursion, because from there on
the two runs ascend out of the fork by different occurrences. -/
theorem nodup_fork : ∀ (walk asc : List (Dart G)), IsWalk asc →
    (∀ dart ∈ asc, A.Ascending dart) → IsWalk walk →
    (∀ x ∈ asc.head?, ∀ y ∈ walk.head?, x.tail = y.tail ∧ x.edge ≠ y.edge) →
    (asc.map Dart.edge).Nodup ∧ (walk.map Dart.edge).Nodup ∧
      ∀ x ∈ asc, ∀ y ∈ walk, x.edge ≠ y.edge := by
  intro walk
  induction walk with
  | nil =>
      intro asc hAscWalk hAll _ _
      exact ⟨A.nodup_edges_of_ascending hAscWalk hAll, by simp, by simp⟩
  | cons dart rest ih =>
      intro asc hAscWalk hAll hWalk hFork
      by_cases hAsc : A.Ascending dart
      · have hAllWalk := A.ascending_of_mem dart rest hWalk hAsc
        refine ⟨A.nodup_edges_of_ascending hAscWalk hAll,
          A.nodup_edges_of_ascending hWalk hAllWalk, ?_⟩
        cases asc with
        | nil =>
            intro x hx
            simp at hx
        | cons firstOne ascRest =>
            obtain ⟨hTail, hEdgeNe⟩ := hFork firstOne (by simp) dart (by simp)
            exact A.edge_ne_of_fork hAscWalk hWalk hAll hAllWalk hTail hEdgeNe
      · have hStepHead : ∀ second ∈ rest.head?, Step dart second :=
          (List.isChain_cons.mp hWalk).1
        have hAscCons : IsWalk (dart.reverse :: asc) := by
          refine hAscWalk.cons ?_
          intro second hsecond
          obtain ⟨hTail, hEdgeNe⟩ := hFork second hsecond dart (by simp)
          refine ⟨?_, ?_⟩
          · rw [Dart.reverse_head]
            exact hTail.symm
          · rw [Dart.reverse_edge]
            exact Ne.symm hEdgeNe
        have hAllCons : ∀ other ∈ dart.reverse :: asc, A.Ascending other := by
          intro other hother
          rcases List.mem_cons.mp hother with h | h
          · exact h ▸ A.ascending_reverse dart hAsc
          · exact hAll other h
        have hForkNext : ∀ x ∈ (dart.reverse :: asc).head?, ∀ y ∈ rest.head?,
            x.tail = y.tail ∧ x.edge ≠ y.edge := by
          intro x hx y hy
          have hxEq : x = dart.reverse := by
            have hx' := hx
            simp at hx'
            exact hx'.symm
          obtain ⟨hHead, hEdgeNe⟩ := hStepHead y hy
          subst hxEq
          refine ⟨?_, ?_⟩
          · rw [Dart.reverse_tail]
            exact hHead
          · rw [Dart.reverse_edge]
            exact hEdgeNe
        obtain ⟨hN1, hN2, hDisj⟩ :=
          ih (dart.reverse :: asc) hAscCons hAllCons hWalk.tail hForkNext
        have hN1' : (dart.edge :: asc.map Dart.edge).Nodup := by simpa using hN1
        refine ⟨(List.nodup_cons.mp hN1').2, ?_, ?_⟩
        · have hnot : dart.edge ∉ rest.map Dart.edge := by
            intro hmem
            obtain ⟨y, hy, hyEq⟩ := List.mem_map.mp hmem
            refine hDisj dart.reverse (by simp) y hy ?_
            rw [Dart.reverse_edge]
            exact hyEq.symm
          have hcons : (dart.edge :: rest.map Dart.edge).Nodup :=
            List.nodup_cons.mpr ⟨hnot, hN2⟩
          simpa using hcons
        · intro x hx y hy
          rcases List.mem_cons.mp hy with h | h
          · subst h
            intro hEq
            exact (List.nodup_cons.mp hN1').1 (List.mem_map.mpr ⟨x, hx, hEq⟩)
          · exact hDisj x (List.mem_cons_of_mem _ hx) y h

include A in
/-- **A non-backtracking walk never repeats an occurrence.**  The theorem the
target-side residues of `RowWalk` need. -/
theorem nodup_edges {walk : List (Dart G)} (hWalk : IsWalk walk) :
    (walk.map Dart.edge).Nodup :=
  (A.nodup_fork walk [] isWalk_nil (by simp) hWalk (by simp)).2.1

include A in
/-- Occurrence-injectivity in the form a consumer applies. -/
theorem eq_of_edge_eq {walk : List (Dart G)} (hWalk : IsWalk walk)
    {first second : Dart G} (hFirst : first ∈ walk) (hSecond : second ∈ walk)
    (hEdge : first.edge = second.edge) : first = second :=
  List.inj_on_of_nodup_map (A.nodup_edges hWalk) hFirst hSecond hEdge

include A in
/-- **There is no closed non-backtracking walk.**  A closed walk is a nonempty
walk whose last dart steps to its first; doubling it would be a walk repeating
every occurrence. -/
theorem no_closed_walk {walk : List (Dart G)} (hNe : walk ≠ []) (hWalk : IsWalk walk)
    (hSeam : ∀ x ∈ walk.getLast?, ∀ y ∈ walk.head?, Step x y) : False := by
  have hDouble : IsWalk (walk ++ walk) := List.IsChain.append hWalk hWalk hSeam
  have hNodup := A.nodup_edges hDouble
  rw [List.map_append, List.nodup_append] at hNodup
  obtain ⟨dart, hdart⟩ := List.exists_mem_of_ne_nil walk hNe
  exact hNodup.2.2 dart.edge (List.mem_map_of_mem hdart) dart.edge
    (List.mem_map_of_mem hdart) rfl

include A in
/-- **A non-backtracking walk does not return to its starting vertex.** -/
theorem tail_ne_head_of_isWalk {walk : List (Dart G)} (hWalk : IsWalk walk)
    {first last : Dart G} (hFirst : walk.head? = some first)
    (hLast : walk.getLast? = some last) : first.tail ≠ last.head := by
  intro hClosed
  have hNe : walk ≠ [] := by
    intro h
    rw [h] at hFirst
    exact absurd hFirst (by simp)
  by_cases hEdge : last.edge = first.edge
  · have hLastMem : last ∈ walk := List.mem_of_getLast? hLast
    have hFirstMem : first ∈ walk := List.mem_of_mem_head? hFirst
    have hEq : last = first := A.eq_of_edge_eq hWalk hLastMem hFirstMem hEdge
    cases walk with
    | nil => exact hNe rfl
    | cons head tail =>
        have hHead : head = first := by simpa using hFirst
        cases tail with
        | nil =>
            have hlh : last = head := by
              have h' := hLast
              simp at h'
              exact h'.symm
            rw [hlh, hHead] at hClosed
            exact Dart.tail_ne_head first hClosed
        | cons second rest =>
            have hMem : last ∈ second :: rest := by
              have hgl : (head :: second :: rest).getLast? = (second :: rest).getLast? := by
                simp [List.getLast?_cons_cons]
              rw [hgl] at hLast
              exact List.mem_of_getLast? hLast
            have hNodup : (head :: second :: rest).Nodup :=
              List.Nodup.of_map _ (A.nodup_edges hWalk)
            rw [hEq, ← hHead] at hMem
            exact (List.nodup_cons.mp hNodup).1 hMem
  · refine A.no_closed_walk hNe hWalk ?_
    intro x hx y hy
    have hxEq : x = last := by
      rw [hLast] at hx
      have hx' := hx
      simp at hx'
      exact hx'.symm
    have hyEq : y = first := by
      rw [hFirst] at hy
      have hy' := hy
      simp at hy'
      exact hy'.symm
    subst hxEq
    subst hyEq
    exact ⟨hClosed.symm, hEdge⟩

/-! ## 9. No parallel occurrences -/

include A in
/-- **A graph with a tree rank has no parallel occurrences.**  Two occurrences
joining the same two distinct vertices have the same end of larger rank. -/
theorem eq_of_incident {x y : G.V} (hxy : x ≠ y) {first second : G.edges}
    (hfx : (first : G.V × G.V).1 = x ∨ (first : G.V × G.V).2 = x)
    (hfy : (first : G.V × G.V).1 = y ∨ (first : G.V × G.V).2 = y)
    (hsx : (second : G.V × G.V).1 = x ∨ (second : G.V × G.V).2 = x)
    (hsy : (second : G.V × G.V).1 = y ∨ (second : G.V × G.V).2 = y) :
    first = second := by
  refine A.high_injective ?_
  show A.high first = A.high second
  have hHighFirst : A.high first = x ∨ A.high first = y := by
    rcases A.eq_low_or_eq_high hfx with h | h
    · rcases A.eq_low_or_eq_high hfy with h' | h'
      · exact absurd (h.trans h'.symm) hxy
      · exact Or.inr h'.symm
    · exact Or.inl h.symm
  have hHighSecond : A.high second = x ∨ A.high second = y := by
    rcases A.eq_low_or_eq_high hsx with h | h
    · rcases A.eq_low_or_eq_high hsy with h' | h'
      · exact absurd (h.trans h'.symm) hxy
      · exact Or.inr h'.symm
    · exact Or.inl h.symm
  have hLowFirst : A.low first = x ∨ A.low first = y := by
    rcases A.eq_low_or_eq_high hfx with h | h
    · exact Or.inl h.symm
    · rcases A.eq_low_or_eq_high hfy with h' | h'
      · exact Or.inr h'.symm
      · exact absurd (h.trans h'.symm) hxy
  have hLowSecond : A.low second = x ∨ A.low second = y := by
    rcases A.eq_low_or_eq_high hsx with h | h
    · exact Or.inl h.symm
    · rcases A.eq_low_or_eq_high hsy with h' | h'
      · exact Or.inr h'.symm
      · exact absurd (h.trans h'.symm) hxy
  have hFirst := A.rank_low_lt first
  have hSecond := A.rank_low_lt second
  rcases hHighFirst with h1 | h1 <;> rcases hHighSecond with h2 | h2
  · rw [h1, h2]
  · rcases hLowFirst with hl | hl
    · exact absurd (hl.trans h1.symm) (A.low_ne_high first)
    · rcases hLowSecond with hl' | hl'
      · rw [h1, hl] at hFirst
        rw [h2, hl'] at hSecond
        omega
      · exact absurd (hl'.trans h2.symm) (A.low_ne_high second)
  · rcases hLowFirst with hl | hl
    · rcases hLowSecond with hl' | hl'
      · exact absurd (hl'.trans h2.symm) (A.low_ne_high second)
      · rw [h1, hl] at hFirst
        rw [h2, hl'] at hSecond
        omega
    · exact absurd (hl.trans h1.symm) (A.low_ne_high first)
  · rw [h1, h2]

end TreeRank

/-! ## 10. The theorem for a connected genus-zero target -/

/-- **A non-backtracking walk in a connected genus-zero graph never repeats an
occurrence.**  The target-side theorem the count waits on. -/
theorem nodup_edges_of_genusZero {G : CFGraph.{0}} (hConn : graph_connected G)
    (hGenus : genus G = 0) {walk : List (Dart G)} (hWalk : IsWalk walk) :
    (walk.map Dart.edge).Nodup :=
  (exists_treeRank G hConn hGenus).some.nodup_edges hWalk

/-- Occurrence-injectivity along a walk of a connected genus-zero graph. -/
theorem eq_of_edge_eq_of_genusZero {G : CFGraph.{0}} (hConn : graph_connected G)
    (hGenus : genus G = 0) {walk : List (Dart G)} (hWalk : IsWalk walk)
    {first second : Dart G} (hFirst : first ∈ walk) (hSecond : second ∈ walk)
    (hEdge : first.edge = second.edge) : first = second :=
  (exists_treeRank G hConn hGenus).some.eq_of_edge_eq hWalk hFirst hSecond hEdge

/-- **A connected genus-zero graph carries no closed non-backtracking walk.** -/
theorem no_closed_walk_of_genusZero {G : CFGraph.{0}} (hConn : graph_connected G)
    (hGenus : genus G = 0) {walk : List (Dart G)} (hNe : walk ≠ []) (hWalk : IsWalk walk)
    (hSeam : ∀ x ∈ walk.getLast?, ∀ y ∈ walk.head?, Step x y) : False :=
  (exists_treeRank G hConn hGenus).some.no_closed_walk hNe hWalk hSeam

/-- **A non-backtracking walk in a connected genus-zero graph does not return to
its starting vertex.** -/
theorem tail_ne_head_of_genusZero {G : CFGraph.{0}} (hConn : graph_connected G)
    (hGenus : genus G = 0) {walk : List (Dart G)} (hWalk : IsWalk walk)
    {first last : Dart G} (hFirst : walk.head? = some first)
    (hLast : walk.getLast? = some last) : first.tail ≠ last.head :=
  (exists_treeRank G hConn hGenus).some.tail_ne_head_of_isWalk hWalk hFirst hLast

/-- **A connected genus-zero graph has no parallel occurrences.**  The
graph-only form of `Count.RowWalk.SimpleTarget`. -/
theorem eq_of_incident_of_genusZero {G : CFGraph.{0}} (hConn : graph_connected G)
    (hGenus : genus G = 0) {x y : G.V} (hxy : x ≠ y) {first second : G.edges}
    (hfx : (first : G.V × G.V).1 = x ∨ (first : G.V × G.V).2 = x)
    (hfy : (first : G.V × G.V).1 = y ∨ (first : G.V × G.V).2 = y)
    (hsx : (second : G.V × G.V).1 = x ∨ (second : G.V × G.V).2 = x)
    (hsy : (second : G.V × G.V).1 = y ∨ (second : G.V × G.V).2 = y) :
    first = second :=
  (exists_treeRank G hConn hGenus).some.eq_of_incident hxy hfx hfy hsx hsy

/-! ## 11. The shape a consumer applies -/

/-- The dart traversing `edge` towards `leave`. -/
def dartOf (edge : G.edges) (leave : G.V) : Dart G :=
  ⟨edge, decide ((edge : G.V × G.V).1 = leave)⟩

@[simp] theorem dartOf_edge (edge : G.edges) (leave : G.V) :
    (dartOf edge leave).edge = edge := rfl

theorem dartOf_head {edge : G.edges} {leave : G.V}
    (h : (edge : G.V × G.V).1 = leave ∨ (edge : G.V × G.V).2 = leave) :
    (dartOf edge leave).head = leave := by
  unfold dartOf Dart.head
  by_cases hfst : (edge : G.V × G.V).1 = leave
  · simp [hfst]
  · simp only [hfst, decide_false, Bool.false_eq_true, ite_false]
    rcases h with h | h
    · exact absurd h hfst
    · exact h

theorem dartOf_tail {edge : G.edges} {enter leave : G.V}
    (hEnds : (edge : G.V × G.V) = (enter, leave) ∨ (edge : G.V × G.V) = (leave, enter)) :
    (dartOf edge leave).tail = enter := by
  have hNe := Dart.coe_fst_ne_snd edge
  unfold dartOf Dart.tail
  rcases hEnds with h | h
  · rw [h] at hNe ⊢
    have hNeEnds : enter ≠ leave := hNe
    simp [hNeEnds]
  · rw [h] at hNe ⊢
    simp

/-- **The consumable form of the theorem.**  A list whose entries each carry a
target occurrence and the two ends by which the walk enters and leaves it, with
consecutive entries meeting at a vertex by *different* occurrences: then no
occurrence is carried twice.  This is stated over an arbitrary index type so
that a consumer can feed it its own ordered row. -/
theorem nodup_map_of_isChain {α : Type*} (A : TreeRank G) {l : List α}
    {edge : α → G.edges} {enter leave : α → G.V}
    (hEnds : ∀ a ∈ l, (edge a : G.V × G.V) = (enter a, leave a) ∨
      (edge a : G.V × G.V) = (leave a, enter a))
    (hChain : l.IsChain fun first second =>
      leave first = enter second ∧ edge first ≠ edge second) :
    (l.map edge).Nodup := by
  have hWalk : IsWalk (l.map fun a => dartOf (edge a) (leave a)) := by
    rw [IsWalk, List.isChain_map]
    refine hChain.imp_of_mem_imp ?_
    intro a b ha hb hab
    refine ⟨?_, ?_⟩
    · rw [dartOf_head (by
        rcases hEnds a ha with h | h
        · exact Or.inr (congrArg Prod.snd h)
        · exact Or.inl (congrArg Prod.fst h)),
        dartOf_tail (hEnds b hb)]
      exact hab.1
    · exact hab.2
  have hNodup := A.nodup_edges hWalk
  rw [List.map_map] at hNodup
  exact hNodup

/-- The same for a connected genus-zero target. -/
theorem nodup_map_of_isChain_of_genusZero {α : Type*} {G : CFGraph.{0}}
    (hConn : graph_connected G) (hGenus : genus G = 0) {l : List α}
    {edge : α → G.edges} {enter leave : α → G.V}
    (hEnds : ∀ a ∈ l, (edge a : G.V × G.V) = (enter a, leave a) ∨
      (edge a : G.V × G.V) = (leave a, enter a))
    (hChain : l.IsChain fun first second =>
      leave first = enter second ∧ edge first ≠ edge second) :
    (l.map edge).Nodup :=
  nodup_map_of_isChain (exists_treeRank G hConn hGenus).some hEnds hChain

/-! ## 12. A walk read off as a list of occurrences from a starting vertex -/

/-- `vertex` is one of the two stored ends of `edge`. -/
def IsEnd (edge : G.edges) (vertex : G.V) : Prop :=
  (edge : G.V × G.V).1 = vertex ∨ (edge : G.V × G.V).2 = vertex

/-- The end of `edge` other than `vertex`. -/
def otherEndOf (edge : G.edges) (vertex : G.V) : G.V :=
  if (edge : G.V × G.V).1 = vertex then (edge : G.V × G.V).2 else (edge : G.V × G.V).1

theorem isEnd_otherEndOf (edge : G.edges) (vertex : G.V) :
    IsEnd edge (otherEndOf edge vertex) := by
  unfold IsEnd otherEndOf
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem ends_pair_of_isEnd {edge : G.edges} {vertex : G.V} (h : IsEnd edge vertex) :
    (edge : G.V × G.V) = (vertex, otherEndOf edge vertex) ∨
      (edge : G.V × G.V) = (otherEndOf edge vertex, vertex) := by
  unfold otherEndOf
  split_ifs with hfst
  · exact Or.inl (Prod.ext hfst rfl)
  · rcases h with h | h
    · exact absurd h hfst
    · exact Or.inr (Prod.ext rfl h)

/-- **A non-backtracking walk presented as a list of occurrences read off from a
starting vertex.**  This is the shape a source-side consumer produces: it names
only the entry vertex, and every further vertex is computed. -/
def IsWalkFrom : G.V → List G.edges → Prop
  | _, [] => True
  | vertex, edge :: rest =>
      IsEnd edge vertex ∧ (∀ next ∈ rest.head?, next ≠ edge) ∧
        IsWalkFrom (otherEndOf edge vertex) rest

/-- The darts of such a walk. -/
def dartsFrom : G.V → List G.edges → List (Dart G)
  | _, [] => []
  | vertex, edge :: rest =>
      dartOf edge (otherEndOf edge vertex) :: dartsFrom (otherEndOf edge vertex) rest

theorem map_edge_dartsFrom : ∀ (vertex : G.V) (l : List G.edges),
    (dartsFrom vertex l).map Dart.edge = l
  | _, [] => rfl
  | vertex, edge :: rest => by
      show Dart.edge (dartOf edge (otherEndOf edge vertex)) ::
        (dartsFrom (otherEndOf edge vertex) rest).map Dart.edge = edge :: rest
      rw [map_edge_dartsFrom (otherEndOf edge vertex) rest, dartOf_edge]

theorem head?_dartsFrom (vertex : G.V) (edge : G.edges) (rest : List G.edges) :
    (dartsFrom vertex (edge :: rest)).head? = some (dartOf edge (otherEndOf edge vertex)) :=
  rfl

theorem isWalk_dartsFrom : ∀ (vertex : G.V) (l : List G.edges),
    IsWalkFrom vertex l → IsWalk (dartsFrom vertex l)
  | _, [], _ => isWalk_nil
  | vertex, edge :: rest, h => by
      refine IsWalk.cons (isWalk_dartsFrom (otherEndOf edge vertex) rest h.2.2) ?_
      intro second hsecond
      cases rest with
      | nil => exact absurd hsecond (by simp [dartsFrom])
      | cons next tail =>
          have hsecondEq : second = dartOf next (otherEndOf next (otherEndOf edge vertex)) := by
            have h' := hsecond
            rw [head?_dartsFrom] at h'
            simpa using h'.symm
          subst hsecondEq
          refine ⟨?_, ?_⟩
          · rw [dartOf_head (isEnd_otherEndOf edge vertex),
              dartOf_tail (ends_pair_of_isEnd h.2.2.1)]
          · rw [dartOf_edge, dartOf_edge]
            exact Ne.symm (h.2.1 next rfl)

/-- **The theorem in the shape a source-side consumer produces it.**  The list
of target occurrences read off a non-backtracking walk from a starting vertex
has no repetition. -/
theorem nodup_of_isWalkFrom (A : TreeRank G) {vertex : G.V} {l : List G.edges}
    (h : IsWalkFrom vertex l) : l.Nodup := by
  have hNodup := A.nodup_edges (isWalk_dartsFrom vertex l h)
  rw [map_edge_dartsFrom] at hNodup
  exact hNodup

/-- The same for a connected genus-zero target. -/
theorem nodup_of_isWalkFrom_of_genusZero {G : CFGraph.{0}} (hConn : graph_connected G)
    (hGenus : genus G = 0) {vertex : G.V} {l : List G.edges}
    (h : IsWalkFrom vertex l) : l.Nodup :=
  nodup_of_isWalkFrom (exists_treeRank G hConn hGenus).some h

/-! ## 13. A walk does not return to the vertex it starts from -/

/-- No dart of a walk arrives at the vertex the walk started from. -/
theorem tail_head_ne_of_mem (A : TreeRank G) {walk : List (Dart G)} (hWalk : IsWalk walk)
    {first dart : Dart G} (hFirst : walk.head? = some first) (hMem : dart ∈ walk) :
    first.tail ≠ dart.head := by
  obtain ⟨front, back, hsplit⟩ := List.append_of_mem hMem
  have hPrefix : IsWalk (front ++ [dart]) := by
    refine List.IsChain.prefix (l := walk) hWalk ⟨back, ?_⟩
    rw [hsplit]
    simp
  have hHead : (front ++ [dart]).head? = some first := by
    rw [hsplit] at hFirst
    cases front with
    | nil => simpa using hFirst
    | cons a t => simpa using hFirst
  exact A.tail_ne_head_of_isWalk hPrefix hHead (by simp)

/-- No dart of a walk leaves the vertex the walk started from, except the first. -/
theorem tail_ne_of_mem (A : TreeRank G) {walk : List (Dart G)} (hWalk : IsWalk walk)
    {first dart : Dart G} (hFirst : walk.head? = some first) (hMem : dart ∈ walk)
    (hNe : dart ≠ first) : first.tail ≠ dart.tail := by
  obtain ⟨front, back, hsplit⟩ := List.append_of_mem hMem
  have hFrontNe : front ≠ [] := by
    intro hEmpty
    rw [hEmpty] at hsplit
    rw [hsplit] at hFirst
    have hEq : dart = first := by simpa using hFirst
    exact hNe hEq
  have hChain : (front ++ dart :: back).IsChain Step := by rw [← hsplit]; exact hWalk
  have hStep : Step (front.getLast hFrontNe) dart := by
    have hrel := List.IsChain.rel_getLast_head_of_append hChain hFrontNe
      (List.cons_ne_nil dart back)
    simpa using hrel
  have hPrevMem : front.getLast hFrontNe ∈ walk := by
    rw [hsplit]
    exact List.mem_append_left _ (List.getLast_mem hFrontNe)
  rw [← hStep.1]
  exact tail_head_ne_of_mem A hWalk hFirst hPrevMem

theorem isEnd_dart_iff (dart : Dart G) (vertex : G.V) :
    IsEnd dart.edge vertex ↔ (vertex = dart.tail ∨ vertex = dart.head) := by
  unfold IsEnd Dart.tail Dart.head
  cases dart.reversed
  · simp only [Bool.false_eq_true, ite_false]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  · simp only [ite_true]
    constructor
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h.symm
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h.symm

/-- **A non-backtracking walk never touches its starting vertex again.**  Only
the first occurrence of the walk has the starting vertex as an end. -/
theorem not_isEnd_of_mem_tail (A : TreeRank G) {vertex : G.V} {l : List G.edges}
    (h : IsWalkFrom vertex l) {edge : G.edges} (hMem : edge ∈ l.tail) :
    ¬ IsEnd edge vertex := by
  cases l with
  | nil => exact absurd hMem (by simp)
  | cons head rest =>
      intro hIsEnd
      have hWalk : IsWalk (dartsFrom vertex (head :: rest)) :=
        isWalk_dartsFrom vertex (head :: rest) h
      have hTailMap : (dartsFrom (otherEndOf head vertex) rest).map Dart.edge = rest :=
        map_edge_dartsFrom (otherEndOf head vertex) rest
      have hMemRest : edge ∈ rest := hMem
      rw [← hTailMap] at hMemRest
      obtain ⟨dart, hdart, hdartEdge⟩ := List.mem_map.mp hMemRest
      have hFirstTail : (dartOf head (otherEndOf head vertex)).tail = vertex :=
        dartOf_tail (ends_pair_of_isEnd h.1)
      have hNodup : (dartsFrom vertex (head :: rest)).Nodup :=
        List.Nodup.of_map _ (A.nodup_edges hWalk)
      have hDartNe : dart ≠ dartOf head (otherEndOf head vertex) := by
        intro hEq
        exact (List.nodup_cons.mp hNodup).1 (hEq ▸ hdart)
      have hMemWalk : dart ∈ dartsFrom vertex (head :: rest) :=
        List.mem_cons_of_mem _ hdart
      have hHead : (dartsFrom vertex (head :: rest)).head?
          = some (dartOf head (otherEndOf head vertex)) := rfl
      rw [← hdartEdge] at hIsEnd
      rcases (isEnd_dart_iff dart vertex).mp hIsEnd with hCase | hCase
      · exact tail_ne_of_mem A hWalk hHead hMemWalk hDartNe (hFirstTail.trans hCase)
      · exact tail_head_ne_of_mem A hWalk hHead hMemWalk (hFirstTail.trans hCase)

/-- The same for a connected genus-zero target. -/
theorem not_isEnd_of_mem_tail_of_genusZero {G : CFGraph.{0}} (hConn : graph_connected G)
    (hGenus : genus G = 0) {vertex : G.V} {l : List G.edges} (h : IsWalkFrom vertex l)
    {edge : G.edges} (hMem : edge ∈ l.tail) : ¬ IsEnd edge vertex :=
  not_isEnd_of_mem_tail (exists_treeRank G hConn hGenus).some h hMem

/-! ## 14. Non-vacuity: the caterpillar of loops -/

open DraismaVargas.Infrastructure.CaterpillarTree

/-- **`TreeRank` is inhabited**: the caterpillar of loops `T^CL_g`, the target of
Part II's own family, is already in normal form, so its vertex numbering is its
tree rank. -/
def catTreeRank (m : ℕ) : TreeRank (catTree m) :=
  orientedTreeRank (6 * m + 3) (catParent m) (catParent_le m) (fun _ => false)

/-- The two occurrences at the root of `T^CL_g` give a genuine two-step
non-backtracking walk, so `IsWalk` is not inhabited only by the empty list. -/
theorem isWalk_catTree (m : ℕ) :
    IsWalk [(⟨occ m ⟨0, by omega⟩, true⟩ : Dart (catTree m)),
      ⟨occ m ⟨1, by omega⟩, false⟩] := by
  refine List.isChain_pair.mpr ⟨?_, ?_⟩
  · show ((⟨occ m ⟨0, by omega⟩, true⟩ : Dart (catTree m))).head
      = ((⟨occ m ⟨1, by omega⟩, false⟩ : Dart (catTree m))).tail
    show ((occ m ⟨0, by omega⟩ : (catTree m).edges) :
        (catTree m).V × (catTree m).V).1
      = ((occ m ⟨1, by omega⟩ : (catTree m).edges) :
        (catTree m).V × (catTree m).V).1
    simp only [occ_fst]
    exact Fin.ext (by simp [catParent, parentIndex])
  · show (occ m ⟨0, by omega⟩ : (catTree m).edges) ≠ occ m ⟨1, by omega⟩
    intro hEq
    exact absurd (congrArg Fin.val (occ_injective m hEq)) (by norm_num)

/-- The theorem on the caterpillar target. -/
example (m : ℕ) {walk : List (Dart (catTree m))} (hWalk : IsWalk walk) :
    (walk.map Dart.edge).Nodup := (catTreeRank m).nodup_edges hWalk

end DraismaVargas.Count.TargetGeodesic
