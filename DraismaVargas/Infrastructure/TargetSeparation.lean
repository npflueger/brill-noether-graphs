module

public import DraismaVargas.Infrastructure.IteratedContraction
public import DraismaVargas.Infrastructure.TargetBranchRegion

@[expose] public section

/-!
# A vertex of a connected genus-zero target separates its incident branches

`TargetBranchRegion` selects the connected component of a root vertex after
deleting a distinguished target vertex `wall`, and turns it into the Boolean
predicates that drive `GluingDatum.SheetRelabeling.ofRegion`.  Which occurrences
that region moves is decidable on a concrete target, but the *general* fact that
two different occurrences at `wall` reach two different components is carried
as a hypothesis by the modules that use it: `W2M1kSourceCandidates` calls it
`hSeparated` (divalent wall), `W3FourDisjointness` calls it `hGrowFixed` /
`hOtherMoved` (trivalent wall).  This file proves it.

## The statement

`not_reachable_farEndpoint`: in a connected target of genus zero, if `first` and
`second` are **distinct** edge occurrences both incident to `wall`, then the far
endpoint of `second` is not reachable from the far endpoint of `first` in the
target with `wall` deleted.

Everything else here is that theorem in the form a consumer wants it:

* `farEndpoint`, `farEndpoint_ne`, `farEndpoint_ends` — the far endpoint of an
  occurrence at `wall`, the same definition as
  `M11RemoteCandidates.branchRoot star label` without the `TwoStar` packaging;
* `vertexMoved_farEndpoint_eq_false`, `edgeMoved_eq_false` — the Boolean form:
  the branch selected by one occurrence moves neither the far endpoint of a
  different occurrence nor that occurrence itself;
* `edgeMoved_self_eq_true` — the complementary fact that the selected branch
  always moves its own occurrence (this one needs no genus hypothesis);
* `separated_of_genus_zero` — the two together, `⟨moved, fixed⟩`, which is what
  `W3FourDisjointness.exists_branchGauge_disjoint` asks for as its pair
  `hOtherMoved`, `hGrowFixed`.

## Why the hypotheses can hold at once

`graph_connected target` and `genus target = 0` are the two standing Part-I
hypotheses on the target, carried together by
`FullDimensionalSource.FullDimensionalSourcePresentation` (fields
`targetConnected`, `targetGenus`) and by `SemanticAtlasMarch.State.PresentedProgress`;
a path on three vertices satisfies both and has a divalent vertex, so the extra
demand of two distinct incident occurrences is satisfiable as well.  The
conclusion is not vacuous for the same reason: on such a target the deleted
graph really does have two components.

## Proof

Genus zero says `|V| = |E| + 1`, so *every* occurrence of a connected target is
a bridge: deleting one and staying connected contradicts
`Utilities.graph_connected_card_vertices_le_card_edges_add_one`
(`not_reachable_eraseOccurrence`).  If the two far endpoints were joined after
deleting `wall`, the occurrence `first` would not be a bridge -- its endpoints
`wall` and `farEndpoint wall first` are joined by going through `second` and
then along that deleted-graph walk.  The degenerate case, where the two
occurrences have the *same* far endpoint, is excluded separately by
`IteratedContraction.num_edges_le_one_of_genus_zero_of_connected`: a connected
genus-zero target has no parallel occurrences.

No result in this file mentions a gluing datum; the whole argument is about the
target graph alone.
-/

namespace DraismaVargas.Infrastructure

namespace TargetSeparation

open Utilities IteratedContraction

variable {target : CFGraph}

/-! ### Occurrences and their endpoints -/

/-- An occurrence with the prescribed (unordered) endpoints witnesses positive
multiplicity there. -/
theorem num_edges_pos_of_ends {x y : target.V} {edge : target.edges}
    (hEnds : (edge : target.V × target.V) = (x, y) ∨
      (edge : target.V × target.V) = (y, x)) :
    0 < num_edges target x y := by
  have hMem : (edge : target.V × target.V) ∈ target.edges := Multiset.coe_mem
  rcases hEnds with hEq | hEq <;> rw [hEq] at hMem
  · exact GraphContraction.num_edges_pos_of_mem_edges target x y hMem
  · exact GraphContraction.num_edges_pos_of_mem_edges' target x y hMem

/-- Two **distinct** occurrences with the same pair of endpoints are parallel:
the multiplicity there is at least two. -/
theorem two_le_num_edges_of_ne {x y : target.V} {first second : target.edges}
    (hFirst : (first : target.V × target.V) = (x, y) ∨
      (first : target.V × target.V) = (y, x))
    (hSecond : (second : target.V × target.V) = (x, y) ∨
      (second : target.V × target.V) = (y, x))
    (hNe : first ≠ second) : 2 ≤ num_edges target x y := by
  have hFirstMem : (first : target.V × target.V) ∈ target.edges := Multiset.coe_mem
  have hSecondMem : (second : target.V × target.V) ∈ target.edges := Multiset.coe_mem
  by_cases hSame : (first : target.V × target.V) = (second : target.V × target.V)
  · -- The same ordered pair twice: the two occurrences differ in their index.
    obtain ⟨pair, index⟩ := first
    obtain ⟨pair', index'⟩ := second
    have hPair : pair = pair' := hSame
    subst hPair
    have hIndex : index.1 ≠ index'.1 := by
      intro hVal
      have hIdx : index = index' := Fin.ext hVal
      subst hIdx
      exact hNe rfl
    have hCount : 2 ≤ Multiset.count pair target.edges := by
      have h₁ := index.2
      have h₂ := index'.2
      omega
    have hFilter : Multiset.count pair
        (target.edges.filter (fun e ↦ e = (x, y) ∨ e = (y, x))) =
        Multiset.count pair target.edges :=
      Multiset.count_filter_of_pos hFirst
    have hCard := Multiset.count_le_card pair
      (target.edges.filter (fun e ↦ e = (x, y) ∨ e = (y, x)))
    rw [hFilter] at hCard
    exact le_trans hCount hCard
  · -- Two different ordered pairs, both retained by the filter.
    classical
    have hSubset :
        ({(first : target.V × target.V), (second : target.V × target.V)} :
          Finset (target.V × target.V)) ⊆
        (target.edges.filter (fun e ↦ e = (x, y) ∨ e = (y, x))).toFinset := by
      intro pair hPair
      rw [Finset.mem_insert, Finset.mem_singleton] at hPair
      rw [Multiset.mem_toFinset, Multiset.mem_filter]
      rcases hPair with rfl | rfl
      · exact ⟨hFirstMem, hFirst⟩
      · exact ⟨hSecondMem, hSecond⟩
    calc (2 : ℕ)
        = ({(first : target.V × target.V), (second : target.V × target.V)} :
            Finset (target.V × target.V)).card := (Finset.card_pair hSame).symm
      _ ≤ (target.edges.filter (fun e ↦ e = (x, y) ∨ e = (y, x))).toFinset.card :=
            Finset.card_le_card hSubset
      _ ≤ num_edges target x y := Multiset.toFinset_card_le _

/-- The endpoint of an occurrence at `wall` other than `wall` itself.  This is
`M11RemoteCandidates.branchRoot` with the `TwoStar` packaging removed. -/
def farEndpoint (wall : target.V) (edge : target.edges) : target.V :=
  if (edge : target.V × target.V).1 = wall then (edge : target.V × target.V).2
  else (edge : target.V × target.V).1

/-- A loopless target has no occurrence both of whose endpoints are `wall`, so
the far endpoint of an incident occurrence really is different from `wall`. -/
theorem farEndpoint_ne {wall : target.V} {edge : target.edges}
    (hIncident : (edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) :
    farEndpoint wall edge ≠ wall := by
  unfold farEndpoint
  split_ifs with hLeft
  · intro hRight
    have hMem : (edge : target.V × target.V) ∈ target.edges := Multiset.coe_mem
    have hPair : (edge : target.V × target.V) = (wall, wall) := Prod.ext hLeft hRight
    rw [hPair] at hMem
    exact target.loopless wall hMem
  · rcases hIncident with hAbsurd | _
    · exact absurd hAbsurd hLeft
    · exact hLeft

/-- The endpoints of an incident occurrence, in the two possible orders. -/
theorem farEndpoint_ends {wall : target.V} {edge : target.edges}
    (hIncident : (edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) :
    (edge : target.V × target.V) = (wall, farEndpoint wall edge) ∨
      (edge : target.V × target.V) = (farEndpoint wall edge, wall) := by
  unfold farEndpoint
  split_ifs with hLeft
  · exact Or.inl (Prod.ext hLeft rfl)
  · rcases hIncident with hAbsurd | hRight
    · exact absurd hAbsurd hLeft
    · exact Or.inr (Prod.ext rfl hRight)

/-! ### Every occurrence of a connected genus-zero target is a bridge -/

/-- Adjacency in the underlying simple graph survives the deletion of one
occurrence that does not join the two vertices concerned. -/
theorem adj_eraseOccurrence {pair : target.V × target.V}
    (hPair : pair ∈ target.edges) {x y : target.V}
    (hAdj : (underlyingSimpleGraph target).Adj x y)
    (hAway : ¬ (pair = (x, y) ∨ pair = (y, x))) :
    (underlyingSimpleGraph (eraseOccurrence target pair)).Adj x y := by
  rw [underlyingSimpleGraph_adj] at hAdj ⊢
  rwa [num_edges_eraseOccurrence_of_not target hPair x y hAway]

/-- Reachability survives the deletion of one occurrence whose own endpoints
remain joined afterwards: reroute each use of the deleted pair. -/
theorem reachable_eraseOccurrence {pair : target.V × target.V}
    (hPair : pair ∈ target.edges)
    (hEnds :
      (underlyingSimpleGraph (eraseOccurrence target pair)).Reachable pair.1 pair.2)
    {x y : target.V}
    (hReachable : (underlyingSimpleGraph target).Reachable x y) :
    (underlyingSimpleGraph (eraseOccurrence target pair)).Reachable x y := by
  obtain ⟨walk⟩ := hReachable
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v w hAdj _ ih =>
      refine SimpleGraph.Reachable.trans ?_ ih
      by_cases hCase : pair = (u, v) ∨ pair = (v, u)
      · rcases hCase with hCase | hCase
        · subst hCase; exact hEnds
        · subst hCase; exact hEnds.symm
      · exact (adj_eraseOccurrence hPair hAdj hCase).reachable

/-- Deleting an occurrence whose endpoints remain joined leaves the target
connected. -/
theorem graph_connected_eraseOccurrence
    (hConnected : graph_connected target) {pair : target.V × target.V}
    (hPair : pair ∈ target.edges)
    (hEnds :
      (underlyingSimpleGraph (eraseOccurrence target pair)).Reachable pair.1 pair.2) :
    graph_connected (eraseOccurrence target pair) := by
  rw [graph_connected_iff_underlyingSimpleGraph_connected] at hConnected
  rw [graph_connected_iff_underlyingSimpleGraph_connected, SimpleGraph.connected_iff]
  exact ⟨fun x y ↦ reachable_eraseOccurrence hPair hEnds (hConnected.preconnected x y),
    inferInstance⟩

/-- **Every occurrence of a connected genus-zero target is a bridge.**  Genus
zero forces `|V| = |E| + 1`, and a connected graph needs at least `|V| - 1`
occurrences. -/
theorem not_reachable_eraseOccurrence (hConnected : graph_connected target)
    (hGenus : genus target = 0) {pair : target.V × target.V}
    (hPair : pair ∈ target.edges) :
    ¬ (underlyingSimpleGraph (eraseOccurrence target pair)).Reachable
      pair.1 pair.2 := by
  intro hEnds
  have hConnected' := graph_connected_eraseOccurrence hConnected hPair hEnds
  have hBound :=
    Utilities.graph_connected_card_vertices_le_card_edges_add_one _ hConnected'
  rw [card_vertices_eraseOccurrence, card_edges_eraseOccurrence target hPair] at hBound
  have hOneLe : 1 ≤ Multiset.card target.edges :=
    Multiset.card_pos.mpr (fun hEmpty => by simp [hEmpty] at hPair)
  have hVertices : (Fintype.card target.V : ℤ) = (Multiset.card target.edges : ℤ) + 1 := by
    unfold genus at hGenus
    omega
  have hVerticesNat : Fintype.card target.V = Multiset.card target.edges + 1 := by
    exact_mod_cast hVertices
  omega

/-! ### The separation theorem -/

/-- A walk of the deleted graph is a walk of the target after deleting any one
occurrence incident to the deleted vertex. -/
theorem reachable_eraseOccurrence_of_deleted {wall : target.V}
    {pair : target.V × target.V} (hPair : pair ∈ target.edges)
    (hWall : pair.1 = wall ∨ pair.2 = wall)
    {left right : {vertex : target.V // vertex ≠ wall}}
    (hReachable : (TargetBranchRegion.deletedGraph wall).Reachable left right) :
    (underlyingSimpleGraph (eraseOccurrence target pair)).Reachable left.1 right.1 := by
  refine hReachable.map ⟨Subtype.val, ?_⟩
  intro source destination hAdj
  refine adj_eraseOccurrence hPair hAdj ?_
  rintro (hEq | hEq)
  · rcases hWall with hw | hw
    · exact source.2 ((congrArg Prod.fst hEq).symm.trans hw)
    · exact destination.2 ((congrArg Prod.snd hEq).symm.trans hw)
  · rcases hWall with hw | hw
    · exact destination.2 ((congrArg Prod.fst hEq).symm.trans hw)
    · exact source.2 ((congrArg Prod.snd hEq).symm.trans hw)

/-- **Distinct occurrences at a vertex of a connected genus-zero target have far
endpoints in distinct components of the target with that vertex deleted.**

This is the lemma `W2M1kSourceCandidates` carries as `hSeparated` and
`W3FourDisjointness` as the pair `hGrowFixed`/`hOtherMoved`. -/
theorem not_reachable_farEndpoint (hConnected : graph_connected target)
    (hGenus : genus target = 0) {wall : target.V} {first second : target.edges}
    (hFirst : (first : target.V × target.V).1 = wall ∨
      (first : target.V × target.V).2 = wall)
    (hSecond : (second : target.V × target.V).1 = wall ∨
      (second : target.V × target.V).2 = wall)
    (hNe : first ≠ second) :
    ¬ (TargetBranchRegion.deletedGraph wall).Reachable
      ⟨farEndpoint wall first, farEndpoint_ne hFirst⟩
      ⟨farEndpoint wall second, farEndpoint_ne hSecond⟩ := by
  intro hReachable
  -- A connected genus-zero target has no parallel occurrences, so the two far
  -- endpoints are different to begin with.
  have hFar : farEndpoint wall first ≠ farEndpoint wall second := by
    intro hEq
    have hSecondEnds := farEndpoint_ends hSecond
    rw [← hEq] at hSecondEnds
    have hTwo := two_le_num_edges_of_ne (farEndpoint_ends hFirst) hSecondEnds hNe
    have hOne := num_edges_le_one_of_genus_zero_of_connected target hConnected hGenus
      wall (farEndpoint wall first)
    omega
  -- The occurrence `first` is then not a bridge: go through `second` instead.
  refine not_reachable_eraseOccurrence (pair := (first : target.V × target.V))
    hConnected hGenus Multiset.coe_mem ?_
  have hWall : (first : target.V × target.V).1 = wall ∨
      (first : target.V × target.V).2 = wall := hFirst
  have hAway : ¬ ((first : target.V × target.V) = (wall, farEndpoint wall second) ∨
      (first : target.V × target.V) = (farEndpoint wall second, wall)) := by
    rcases farEndpoint_ends hFirst with hEq | hEq <;> rw [hEq] <;> rintro (hc | hc)
    · exact hFar (congrArg Prod.snd hc)
    · exact farEndpoint_ne hSecond (congrArg Prod.fst hc).symm
    · exact farEndpoint_ne hFirst (congrArg Prod.fst hc)
    · exact hFar (congrArg Prod.fst hc)
  have hAdj : (underlyingSimpleGraph
      (eraseOccurrence target (first : target.V × target.V))).Adj
      wall (farEndpoint (target := target) wall second) := by
    refine adj_eraseOccurrence Multiset.coe_mem ?_ hAway
    rw [underlyingSimpleGraph_adj]
    exact num_edges_pos_of_ends (farEndpoint_ends hSecond)
  have hBranch := reachable_eraseOccurrence_of_deleted
    (pair := (first : target.V × target.V)) Multiset.coe_mem hWall hReachable.symm
  have hJoined : (underlyingSimpleGraph
      (eraseOccurrence target (first : target.V × target.V))).Reachable
      wall (farEndpoint (target := target) wall first) := hAdj.reachable.trans hBranch
  rcases farEndpoint_ends hFirst with hEq | hEq
  · rw [show (first : target.V × target.V).1 = wall from congrArg Prod.fst hEq,
      show (first : target.V × target.V).2 = farEndpoint wall first from
        congrArg Prod.snd hEq]
    exact hJoined
  · rw [show (first : target.V × target.V).1 = farEndpoint wall first from
        congrArg Prod.fst hEq,
      show (first : target.V × target.V).2 = wall from congrArg Prod.snd hEq]
    exact hJoined.symm

/-! ### The Boolean form consumed by the branch swap -/

/-- The far endpoint of a *different* occurrence at `wall` is not moved by the
branch swap across `first`. -/
theorem vertexMoved_farEndpoint_eq_false (hConnected : graph_connected target)
    (hGenus : genus target = 0) {wall : target.V} {first second : target.edges}
    (hFirst : (first : target.V × target.V).1 = wall ∨
      (first : target.V × target.V).2 = wall)
    (hSecond : (second : target.V × target.V).1 = wall ∨
      (second : target.V × target.V).2 = wall)
    (hNe : first ≠ second) :
    TargetBranchRegion.vertexMoved wall (farEndpoint wall first)
      (farEndpoint_ne hFirst) (farEndpoint wall second) = false := by
  rw [← Bool.not_eq_true, TargetBranchRegion.vertexMoved_eq_true_iff]
  rintro ⟨hMember, hReachable⟩
  exact not_reachable_farEndpoint hConnected hGenus hFirst hSecond hNe hReachable

/-- **The separation hypothesis, in exactly the Boolean shape the branch swap
consumes.**  The branch at `first` does not move a different occurrence at
`wall`. -/
theorem edgeMoved_eq_false (hConnected : graph_connected target)
    (hGenus : genus target = 0) {wall : target.V} {first second : target.edges}
    (hFirst : (first : target.V × target.V).1 = wall ∨
      (first : target.V × target.V).2 = wall)
    (hSecond : (second : target.V × target.V).1 = wall ∨
      (second : target.V × target.V).2 = wall)
    (hNe : first ≠ second) :
    TargetBranchRegion.edgeMoved wall (farEndpoint wall first)
      (farEndpoint_ne hFirst) second = false := by
  have hFar :=
    vertexMoved_farEndpoint_eq_false hConnected hGenus hFirst hSecond hNe
  unfold TargetBranchRegion.edgeMoved
  rcases farEndpoint_ends hSecond with hEq | hEq <;> rw [hEq] <;>
    simp [hFar]

/-- The branch swap always moves the occurrence it is taken across.  No genus or
connectivity hypothesis is needed: the far endpoint is the root of its own
component. -/
theorem edgeMoved_self_eq_true {wall : target.V} {first : target.edges}
    (hFirst : (first : target.V × target.V).1 = wall ∨
      (first : target.V × target.V).2 = wall) :
    TargetBranchRegion.edgeMoved wall (farEndpoint wall first)
      (farEndpoint_ne hFirst) first = true := by
  have hRoot : TargetBranchRegion.vertexMoved wall (farEndpoint wall first)
      (farEndpoint_ne hFirst) (farEndpoint wall first) = true := by
    rw [TargetBranchRegion.vertexMoved_eq_true_iff]
    exact ⟨farEndpoint_ne hFirst, SimpleGraph.Reachable.refl _⟩
  unfold TargetBranchRegion.edgeMoved
  rcases farEndpoint_ends hFirst with hEq | hEq <;> rw [hEq] <;> simp [hRoot]

/-- **Both halves at once.**  In a connected genus-zero target the branch swap
across one occurrence at `wall` moves that occurrence and fixes every other
occurrence at `wall`.  `W3FourDisjointness.exists_branchGauge_disjoint` and
`exists_branchGauge_not_disjoint` take these as `hOtherMoved` and `hGrowFixed`
(with `first := otherTarget`, `second := growTarget`), and
`W2M1kSourceCandidates.branchSwap_aligns` / `branchSwap_separates` take the
second as `hSeparated` (with `first := star.edge 1`, `second := star.edge 0`). -/
theorem separated_of_genus_zero (hConnected : graph_connected target)
    (hGenus : genus target = 0) {wall : target.V} {first second : target.edges}
    (hFirst : (first : target.V × target.V).1 = wall ∨
      (first : target.V × target.V).2 = wall)
    (hSecond : (second : target.V × target.V).1 = wall ∨
      (second : target.V × target.V).2 = wall)
    (hNe : first ≠ second) :
    TargetBranchRegion.edgeMoved wall (farEndpoint wall first)
        (farEndpoint_ne hFirst) first = true ∧
      TargetBranchRegion.edgeMoved wall (farEndpoint wall first)
        (farEndpoint_ne hFirst) second = false :=
  ⟨edgeMoved_self_eq_true hFirst,
    edgeMoved_eq_false hConnected hGenus hFirst hSecond hNe⟩

end TargetSeparation

end DraismaVargas.Infrastructure
