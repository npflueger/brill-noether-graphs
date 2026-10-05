module

public import DraismaVargas.LocalCases.DanglingDescent

@[expose] public section

/-!
# Non-dangling valency at a wall block

This module proves the dichotomy `nd(A) = 0` or `nd(A) ≥ 2` that
Draisma--Vargas Part I observes just before constructing the stable graph
`H(M)` of a gluing datum, and packages the arithmetic consequences of the
non-dangling formula for `r_φ` (Part I, `lem-rphi-nd`) at a block of vanishing
local ramification.

## The graph-theoretic core

`exists_danglingSide_of_forall_neighbour_dangling`: if every occurrence at a
source vertex `v` other than a single occurrence to `u` hangs in a genus-zero
branch, then `v` together with all those branches is a genus-zero side of a
cut whose unique crossing occurrence is the one to `u`.  Hence that last
occurrence is dangling too, so a vertex with exactly one surviving occurrence
cannot exist (`nonDanglingValency_ne_one`).

The side is built by absorbing the dangling branches one at a time
(`absorb_branch`).  The invariant carried through the absorption is: `T` is
connected, `|E(T)| + 1 = |T|` (a tree), `v ∈ T`, `u ∉ T`, and every occurrence
leaving `T` starts at `v`.  Connectivity of the complement is deliberately
*not* part of the invariant — it is false at the start (`T = {v}`, with `v` a
cut vertex) and is recovered at the very end from the single-crossing property
by `complement_connected_of_unique_cross`.

## What is, and is not, derived here

At a W4 wall, Equation (C) gives `ch(w₀) = 0`, hence `r(A) = 0` for every wall
block (`localRamification_wallBlock_eq_zero`).  With dangling-no-glue,
`lem-rphi-nd` then yields (`wallBlock_local_picture`)

* `nd(A) = 0`, and then `|A| = 1`; or
* `nd(A) ≥ 2`, and then `nd(A) ≤ 2|A| + 2`.

The bound `nd(A) ≤ 3` is **not** proved here and is not a consequence of
validity, dangling-no-glue and Equation (C): with `r(A) = 0` and `|A| = 1` a
four-valent wall block has exactly four incident occurrences, and all four may
survive without violating any of those hypotheses.  In Part I the bound is
the trivalence of `H(M₀)` (observed in the subsection on the cases for
constructing `P*(M₀)`), i.e. full-dimensionality of the incoming datum — the
`stablePath_card` field, not `equation_c`.  It is therefore taken as the
explicit hypothesis `nd(A) ≤ 3` of `nonDanglingValency_eq_zero_or_two_or_three`
and of `auxR0SourceInput_of_det_ne_zero`, and it is exactly what the
`nonDangling_valency` field of `W4StableSource.AuxR0SourceInput` needs beyond
this file.
-/

namespace DraismaVargas.LocalCases.NonDanglingValency

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.DanglingDescent

universe u

/-! ## Occurrence bookkeeping -/

section GraphLemma

variable {G : CFGraph.{u}}

/-- A recorded edge occurrence gives positive multiplicity between its
endpoints. -/
theorem num_edges_pos_of_mem_edges {x y : G.V} (hMem : (x, y) ∈ G.edges) :
    0 < num_edges G x y := by
  classical
  unfold num_edges
  rw [Multiset.card_pos_iff_exists_mem]
  exact ⟨(x, y), Multiset.mem_filter.mpr ⟨hMem, Or.inl rfl⟩⟩

/-- The complement of a vertex set whose only crossing occurrence is one
bridge is connected, as soon as the ambient graph is. -/
theorem complement_connected_of_unique_cross
    (hConnected : graph_connected G) (side : Finset G.V) {inner outer : G.V}
    (hOuter : outer ∉ side)
    (hCross : ∀ a b : G.V, a ∈ side → b ∉ side →
      num_edges G a b = if a = inner ∧ b = outer then 1 else 0) :
    graph_connected (Utilities.inducedSubgraph G (Finset.univ \ side)
      ⟨outer, Finset.mem_sdiff.mpr ⟨Finset.mem_univ outer, hOuter⟩⟩) := by
  classical
  have hOuterMem : outer ∈ Finset.univ \ side :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ outer, hOuter⟩
  have hMemIff : ∀ x : G.V, x ∈ Finset.univ \ side ↔ x ∉ side := by
    intro x
    simp
  refine graph_connected_of_reach ⟨outer, hOuterMem⟩ ?_
  intro z
  have hMotive : ∀ x : G.V, Reach G outer x → ∀ hx : x ∈ Finset.univ \ side,
      Reach (Utilities.inducedSubgraph G (Finset.univ \ side) ⟨outer, hOuterMem⟩)
        ⟨outer, hOuterMem⟩ ⟨x, hx⟩ := by
    intro x hReach
    refine reach_propagate (H := G)
      (motive := fun y ↦ ∀ hy : y ∈ Finset.univ \ side,
        Reach (Utilities.inducedSubgraph G (Finset.univ \ side) ⟨outer, hOuterMem⟩)
          ⟨outer, hOuterMem⟩ ⟨y, hy⟩) ?_ ?_ hReach
    · intro _
      exact reach_refl _ _
    · intro a b hab hA hb
      have hbSide : b ∉ side := (hMemIff b).1 hb
      by_cases haSide : a ∈ side
      · have hValue := hCross a b haSide hbSide
        have hPair : a = inner ∧ b = outer := by
          by_contra hNot
          rw [ite_eq_right hNot] at hValue
          omega
        have hEq : (⟨b, hb⟩ : (Utilities.inducedSubgraph G (Finset.univ \ side)
            ⟨outer, hOuterMem⟩).V) = ⟨outer, hOuterMem⟩ :=
          Subtype.ext hPair.2
        rw [hEq]
        exact reach_refl _ _
      · have haMem : a ∈ Finset.univ \ side := (hMemIff a).2 haSide
        refine reach_trans (hA haMem) (reach_single ?_)
        have hValue : num_edges
            (Utilities.inducedSubgraph G (Finset.univ \ side) ⟨outer, hOuterMem⟩)
            ⟨a, haMem⟩ ⟨b, hb⟩ = num_edges G a b :=
          Utilities.num_edges_inducedSubgraph G _ _ _ _
        omega
  exact hMotive z.1 (reach_of_graph_connected hConnected outer z.1) z.2

/-- **The absorption step.**  Let `side` be a tree containing `inner`, every
occurrence out of which starts at `inner`, and let `branch` be a vertex outside
`side` carrying a dangling cut towards `inner`.  Then the union of `side` with
that dangling side is again a tree containing `inner`, every occurrence out of
which starts at `inner`, and it is strictly larger. -/
theorem absorb_branch
    (side : Finset G.V) {inner branch : G.V}
    (hInner : inner ∈ side) (hBranchNot : branch ∉ side)
    (hCross : ∀ a : G.V, a ∈ side → ∀ c : G.V, c ∉ side →
      0 < num_edges G a c → a = inner)
    (hConn : graph_connected (Utilities.inducedSubgraph G side ⟨inner, hInner⟩))
    (hTree : (Utilities.inducedSubgraph G side ⟨inner, hInner⟩).edges.card + 1 =
      side.card)
    (cut : DanglingSide G branch inner) :
    ∃ hInnerBig : inner ∈ side ∪ cut.side,
      graph_connected (Utilities.inducedSubgraph G (side ∪ cut.side)
        ⟨inner, hInnerBig⟩) ∧
      (Utilities.inducedSubgraph G (side ∪ cut.side)
        ⟨inner, hInnerBig⟩).edges.card + 1 = (side ∪ cut.side).card ∧
      (∀ a : G.V, a ∈ side ∪ cut.side → ∀ c : G.V, c ∉ side ∪ cut.side →
        0 < num_edges G a c → a = inner) ∧
      side.card < (side ∪ cut.side).card := by
  classical
  have hBranchCut : branch ∈ cut.side := cut.left_mem
  have hInnerCut : inner ∉ cut.side := cut.right_not_mem
  have hCutCross := cut.cross_num_edges
  have hEdgeOne : num_edges G branch inner = 1 := cut.num_edges_endpoints
  -- the two sides are disjoint
  have hDisjoint : ∀ x : G.V, x ∈ side → x ∉ cut.side := by
    intro x hxSide hxCut
    have hBase : (⟨x, hxCut⟩ : (Utilities.inducedSubgraph G cut.side
        ⟨branch, hBranchCut⟩).V) ∈
        (Finset.univ.filter fun y : (Utilities.inducedSubgraph G cut.side
          ⟨branch, hBranchCut⟩).V ↦ y.1 ∈ side) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxSide⟩
    have hTargetNot : (⟨branch, hBranchCut⟩ : (Utilities.inducedSubgraph G
        cut.side ⟨branch, hBranchCut⟩).V) ∉
        (Finset.univ.filter fun y : (Utilities.inducedSubgraph G cut.side
          ⟨branch, hBranchCut⟩).V ↦ y.1 ∈ side) := by
      intro hMem
      exact hBranchNot (Finset.mem_filter.mp hMem).2
    obtain ⟨p, hp, q, hq, hEdge⟩ :=
      exists_cross_of_reach _
        (reach_of_graph_connected cut.side_connected ⟨x, hxCut⟩
          ⟨branch, hBranchCut⟩) hBase hTargetNot
    have hpSide : p.1 ∈ side := (Finset.mem_filter.mp hp).2
    have hqSide : q.1 ∉ side := fun h ↦ hq (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, h⟩)
    have hValue : num_edges (Utilities.inducedSubgraph G cut.side
        ⟨branch, hBranchCut⟩) p q = num_edges G p.1 q.1 :=
      Utilities.num_edges_inducedSubgraph G _ _ _ _
    have hInnerEq : p.1 = inner := hCross p.1 hpSide q.1 hqSide (by omega)
    have hpvCut : p.1 ∈ cut.side := p.2
    rw [hInnerEq] at hpvCut
    exact hInnerCut hpvCut
  have hInnerBig : inner ∈ side ∪ cut.side := Finset.mem_union_left _ hInner
  have hBranchBig : branch ∈ side ∪ cut.side := Finset.mem_union_right _ hBranchCut
  have hUnionIff : ∀ x : G.V, x ∈ side ∪ cut.side ↔ (x ∈ side ∨ x ∈ cut.side) := by
    intro x
    exact Finset.mem_union
  -- the only occurrence between the two sides is the cut occurrence
  have hCrossCount : crossCount G side cut.side = 1 := by
    have hFilter : (G.edges.filter fun e : G.V × G.V ↦
          (e.1 ∈ side ∧ e.2 ∈ cut.side) ∨ (e.1 ∈ cut.side ∧ e.2 ∈ side)) =
        G.edges.filter fun e : G.V × G.V ↦
          e = (inner, branch) ∨ e = (branch, inner) := by
      refine Multiset.filter_congr ?_
      intro e hMem
      have hPos : 0 < num_edges G e.1 e.2 := num_edges_pos_of_mem_edges hMem
      have hPos' : 0 < num_edges G e.2 e.1 := by
        rw [num_edges_symmetric]; exact hPos
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · have hFst : e.1 = inner := hCross e.1 h1 e.2 (fun h ↦ hDisjoint e.2 h h2) hPos
          have hValue := hCutCross e.2 e.1 h2 (hFst ▸ hInnerCut)
          have hPair : e.2 = branch ∧ e.1 = inner := by
            by_contra hNot
            rw [ite_eq_right hNot] at hValue
            omega
          exact Or.inl (Prod.ext hFst hPair.1)
        · have hSnd : e.2 = inner := hCross e.2 h2 e.1 (fun h ↦ hDisjoint e.1 h h1) hPos'
          have hValue := hCutCross e.1 e.2 h1 (hSnd ▸ hInnerCut)
          have hPair : e.1 = branch ∧ e.2 = inner := by
            by_contra hNot
            rw [ite_eq_right hNot] at hValue
            omega
          exact Or.inr (Prod.ext hPair.1 hSnd)
      · rintro (hEq | hEq) <;> rw [hEq]
        · exact Or.inl ⟨hInner, hBranchCut⟩
        · exact Or.inr ⟨hBranchCut, hInner⟩
    unfold crossCount
    rw [hFilter]
    change num_edges G inner branch = 1
    rw [num_edges_symmetric]
    exact hEdgeOne
  -- the branch is a tree as well
  have hBranchVertexCard : Fintype.card (Utilities.inducedSubgraph G cut.side
      ⟨branch, hBranchCut⟩).V = cut.side.card :=
    Utilities.inducedSubgraph_vertex_card G _ _
  have hBranchTree : (Utilities.inducedSubgraph G cut.side
      ⟨branch, hBranchCut⟩).edges.card + 1 = cut.side.card := by
    have hGenus := cut.side_genus_zero
    unfold genus at hGenus
    rw [hBranchVertexCard] at hGenus
    omega
  have hCardUnion : (side ∪ cut.side).card = side.card + cut.side.card :=
    Finset.card_union_of_disjoint (Finset.disjoint_left.mpr hDisjoint)
  have hSplit := inducedSubgraph_edge_card_split G (side ∪ cut.side) side
    cut.side ⟨inner, hInnerBig⟩ ⟨inner, hInner⟩ ⟨branch, hBranchCut⟩
    hUnionIff hDisjoint
  have hBranchPos : 0 < cut.side.card := Finset.card_pos.mpr ⟨branch, hBranchCut⟩
  refine ⟨hInnerBig, ?_, by omega, ?_, by omega⟩
  · -- connectivity of the union
    refine graph_connected_of_reach ⟨inner, hInnerBig⟩ ?_
    intro z
    rcases (hUnionIff z.1).1 z.2 with hzSide | hzCut
    · exact reach_induced_transfer
        (H := Utilities.inducedSubgraph G side ⟨inner, hInner⟩)
        (fun y ↦ y.1) _ ⟨inner, hInnerBig⟩
        (fun a b hab ↦ by
          have hValue : num_edges (Utilities.inducedSubgraph G side
              ⟨inner, hInner⟩) a b = num_edges G a.1 b.1 :=
            Utilities.num_edges_inducedSubgraph G _ _ _ _
          omega)
        ⟨inner, hInner⟩ inner rfl hInnerBig
        (fun y _ ↦ Finset.mem_union_left _ y.2) ⟨z.1, hzSide⟩
        (reach_of_graph_connected hConn _ _) z.2
    · have hStep : 0 < num_edges (Utilities.inducedSubgraph G (side ∪ cut.side)
          ⟨inner, hInnerBig⟩) ⟨inner, hInnerBig⟩ ⟨branch, hBranchBig⟩ := by
        have hValue : num_edges (Utilities.inducedSubgraph G (side ∪ cut.side)
            ⟨inner, hInnerBig⟩) ⟨inner, hInnerBig⟩ ⟨branch, hBranchBig⟩ =
            num_edges G inner branch :=
          Utilities.num_edges_inducedSubgraph G _ _ _ _
        rw [num_edges_symmetric] at hValue
        omega
      refine reach_trans (reach_single hStep) ?_
      exact reach_induced_transfer
        (H := Utilities.inducedSubgraph G cut.side ⟨branch, hBranchCut⟩)
        (fun y ↦ y.1) _ ⟨inner, hInnerBig⟩
        (fun a b hab ↦ by
          have hValue : num_edges (Utilities.inducedSubgraph G cut.side
              ⟨branch, hBranchCut⟩) a b = num_edges G a.1 b.1 :=
            Utilities.num_edges_inducedSubgraph G _ _ _ _
          omega)
        ⟨branch, hBranchCut⟩ branch rfl hBranchBig
        (fun y _ ↦ Finset.mem_union_right _ y.2) ⟨z.1, hzCut⟩
        (reach_of_graph_connected cut.side_connected _ _) z.2
  · -- every occurrence leaving the union still starts at `inner`
    intro a haBig c hcBig hPos
    rcases (hUnionIff a).1 haBig with haSide | haCut
    · exact hCross a haSide c (fun h ↦ hcBig (Finset.mem_union_left _ h)) hPos
    · have hcCut : c ∉ cut.side := fun h ↦ hcBig (Finset.mem_union_right _ h)
      have hValue := hCutCross a c haCut hcCut
      have hPair : a = branch ∧ c = inner := by
        by_contra hNot
        rw [ite_eq_right hNot] at hValue
        omega
      exact absurd (hPair.2 ▸ hInnerBig) hcBig

/-- The absorption recursion: from any partially built tree side around
`inner`, absorbing the remaining dangling branches produces the dangling cut
whose unique crossing occurrence goes to `outer`. -/
theorem exists_danglingSide_aux (hConnected : graph_connected G)
    {inner outer : G.V} (hEdgeOne : num_edges G inner outer = 1)
    (hBranches : ∀ b : G.V, b ≠ outer → 0 < num_edges G inner b →
      Nonempty (DanglingSide G b inner)) :
    ∀ (n : ℕ) (side : Finset G.V) (hInner : inner ∈ side),
      (Finset.univ \ side).card = n → outer ∉ side →
      graph_connected (Utilities.inducedSubgraph G side ⟨inner, hInner⟩) →
      (Utilities.inducedSubgraph G side ⟨inner, hInner⟩).edges.card + 1 =
        side.card →
      (∀ a : G.V, a ∈ side → ∀ c : G.V, c ∉ side →
        0 < num_edges G a c → a = inner) →
      Nonempty (DanglingSide G inner outer) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro side hInner hCard hOuter hConn hTree hCross
    by_cases hBranch :
        ∃ b : G.V, b ∉ side ∧ b ≠ outer ∧ 0 < num_edges G inner b
    · obtain ⟨b, hbNot, hbNe, hbPos⟩ := hBranch
      obtain ⟨cut⟩ := hBranches b hbNe hbPos
      obtain ⟨hInnerBig, hConnBig, hTreeBig, hCrossBig, hLess⟩ :=
        absorb_branch side hInner hbNot hCross hConn hTree cut
      have hOuterCut : outer ∉ cut.side := by
        intro hMem
        have hValue := cut.cross_num_edges outer inner hMem cut.right_not_mem
        rw [ite_eq_right (fun hPair ↦ hbNe hPair.1.symm)] at hValue
        rw [num_edges_symmetric] at hEdgeOne
        omega
      have hOuterBig : outer ∉ side ∪ cut.side := by
        intro hMem
        rcases Finset.mem_union.mp hMem with h | h
        · exact hOuter h
        · exact hOuterCut h
      have hCardSide : (Finset.univ \ side).card =
          Fintype.card G.V - side.card := Finset.card_univ_sdiff side
      have hCardBig : (Finset.univ \ (side ∪ cut.side)).card =
          Fintype.card G.V - (side ∪ cut.side).card :=
        Finset.card_univ_sdiff _
      have hLe : (side ∪ cut.side).card ≤ Fintype.card G.V := by
        simpa using Finset.card_le_univ (side ∪ cut.side)
      exact ih (Finset.univ \ (side ∪ cut.side)).card (by omega)
        (side ∪ cut.side) hInnerBig rfl hOuterBig hConnBig hTreeBig hCrossBig
    · have hBranchZero : ∀ b : G.V, b ∉ side → b ≠ outer →
          num_edges G inner b = 0 := by
        intro b hbNot hbNe
        by_contra hNonzero
        exact hBranch ⟨b, hbNot, hbNe, Nat.pos_of_ne_zero hNonzero⟩
      have hCrossExact : ∀ a b : G.V, a ∈ side → b ∉ side →
          num_edges G a b = if a = inner ∧ b = outer then 1 else 0 := by
        intro a b ha hb
        by_cases hPair : a = inner ∧ b = outer
        · rw [ite_eq_left hPair, hPair.1, hPair.2]
          exact hEdgeOne
        · rw [ite_eq_right hPair]
          by_contra hNonzero
          have hPos : 0 < num_edges G a b := Nat.pos_of_ne_zero hNonzero
          have haInner : a = inner := hCross a ha b hb hPos
          subst haInner
          have hbOuter : b ≠ outer := fun h ↦ hPair ⟨rfl, h⟩
          have hZero := hBranchZero b hb hbOuter
          omega
      have hVertexCard : Fintype.card (Utilities.inducedSubgraph G side
          ⟨inner, hInner⟩).V = side.card :=
        Utilities.inducedSubgraph_vertex_card G _ _
      exact ⟨{ side := side
               left_mem := hInner
               right_not_mem := hOuter
               cross_num_edges := hCrossExact
               side_connected := hConn
               complement_connected :=
                 complement_connected_of_unique_cross hConnected side hOuter
                   hCrossExact
               side_genus_zero := by
                 unfold genus
                 rw [hVertexCard]
                 omega }⟩

/-- **The non-dangling dichotomy, graph form.**  If every occurrence at
`inner` other than a single occurrence to `outer` hangs in a genus-zero
branch, then the occurrence to `outer` is itself the unique crossing
occurrence of a genus-zero cut around `inner`. -/
theorem exists_danglingSide_of_forall_neighbour_dangling
    (hConnected : graph_connected G) {inner outer : G.V}
    (hEdgeOne : num_edges G inner outer = 1)
    (hBranches : ∀ b : G.V, b ≠ outer → 0 < num_edges G inner b →
      Nonempty (DanglingSide G b inner)) :
    Nonempty (DanglingSide G inner outer) := by
  classical
  have hNe : outer ≠ inner := by
    intro hEq
    rw [hEq, num_edges_self_zero] at hEdgeOne
    omega
  have hMem : inner ∈ ({inner} : Finset G.V) := Finset.mem_singleton_self inner
  refine exists_danglingSide_aux hConnected hEdgeOne hBranches
    (Finset.univ \ ({inner} : Finset G.V)).card {inner} hMem rfl ?_ ?_ ?_ ?_
  · intro hOuter
    exact hNe (Finset.mem_singleton.mp hOuter)
  · refine graph_connected_of_reach ⟨inner, hMem⟩ ?_
    intro z
    have hz : z = ⟨inner, hMem⟩ :=
      Subtype.ext (Finset.mem_singleton.mp z.2)
    rw [hz]
    exact reach_refl _ _
  · have hZero : (Utilities.inducedSubgraph G ({inner} : Finset G.V)
        ⟨inner, hMem⟩).edges.card = 0 := by
      have hFilter := Utilities.inducedSubgraph_edge_card_eq_filter G
        ({inner} : Finset G.V) ⟨inner, hMem⟩
      rw [hFilter, Multiset.card_eq_zero]
      refine Multiset.filter_eq_nil.mpr ?_
      intro e hMemE hCond
      have hLoop : e = (inner, inner) :=
        Prod.ext (Finset.mem_singleton.mp hCond.1)
          (Finset.mem_singleton.mp hCond.2)
      rw [hLoop] at hMemE
      exact G.loopless inner hMemE
    rw [hZero, Finset.card_singleton]
  · intro a ha _ _ _
    exact Finset.mem_singleton.mp ha

end GraphLemma

/-! ## The dichotomy for a gluing datum -/

section Gluing

variable {target : CFGraph} {degree : ℕ}

/-- Reading a dangling certificate along a chosen orientation of the
occurrence. -/
theorem danglingSide_of_isDangling (data : GluingDatum target degree)
    {edge : data.SourceEdge} {first second : data.SourceVertex}
    (hEnds : data.sourceEnds edge = (first, second) ∨
      data.sourceEnds edge = (second, first))
    (hDangling : IsDangling data edge) :
    Nonempty (DanglingSide data.sourceGraph first second) ∨
      Nonempty (DanglingSide data.sourceGraph second first) := by
  rcases hDangling with hCut | hCut <;> rcases hEnds with hE | hE <;>
    rw [hE] at hCut
  · exact Or.inl hCut
  · exact Or.inr hCut
  · exact Or.inr hCut
  · exact Or.inl hCut

/-- The far endpoint of an occurrence is determined by the near one. -/
theorem other_end_unique (data : GluingDatum target degree)
    {edge : data.SourceEdge} {base first second : data.SourceVertex}
    (hFirst : data.sourceEnds edge = (base, first) ∨
      data.sourceEnds edge = (first, base))
    (hSecond : data.sourceEnds edge = (base, second) ∨
      data.sourceEnds edge = (second, base)) :
    first = second := by
  rcases hFirst with h1 | h1 <;> rcases hSecond with h2 | h2 <;> rw [h1] at h2
  · exact congrArg Prod.snd h2
  · have hOne : base = second := congrArg Prod.fst h2
    have hTwo : first = base := congrArg Prod.snd h2
    exact hTwo.trans hOne
  · have hOne : first = base := congrArg Prod.fst h2
    have hTwo : base = second := congrArg Prod.snd h2
    exact hOne.trans hTwo
  · exact congrArg Prod.fst h2

/-- **Draisma--Vargas Part I, the non-dangling valency dichotomy** (observed
before the construction of `H(M)`): a source vertex of a connected gluing datum
never has exactly one surviving incident occurrence. Otherwise every other
occurrence there would hang in a genus-zero branch, and then that last
occurrence would be dangling too. -/
theorem nonDanglingValency_ne_one
    (data : GluingDatum target degree) (hConnected : data.Connected)
    (vertex : data.SourceVertex) :
    nonDanglingValency data vertex ≠ 1 := by
  classical
  intro hOne
  have hCard : ((Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
      (fun edge ↦ ¬ IsDangling data edge.1)).card = 1 :=
    (card_filter_not_isDangling_eq_nonDanglingValency data vertex).trans hOne
  obtain ⟨survivor, hMemSurvivor⟩ :=
    Finset.card_pos.mp (by omega : 0 < ((Finset.univ :
      Finset (IncidentSourceEdge data vertex)).filter
        (fun edge ↦ ¬ IsDangling data edge.1)).card)
  have hUnique := Finset.card_le_one.mp (le_of_eq hCard)
  have hSurvives : ¬ IsDangling data survivor.1 :=
    (Finset.mem_filter.mp hMemSurvivor).2
  have hOtherDangling : ∀ other : data.SourceEdge, Incident data other vertex →
      other ≠ survivor.1 → IsDangling data other := by
    intro other hIncident hNe
    by_contra hNot
    have hMem : (⟨other, hIncident⟩ : IncidentSourceEdge data vertex) ∈
        (Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
          (fun edge ↦ ¬ IsDangling data edge.1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNot⟩
    exact hNe (congrArg Subtype.val (hUnique _ hMem survivor hMemSurvivor))
  obtain ⟨outer, hEnds⟩ := exists_other_sourceEnd data survivor.2
  -- a dangling cut whose inner endpoint is `vertex` would kill the survivor
  have hNoInnerCut : ∀ (far : data.SourceVertex) (other : data.SourceEdge),
      (data.sourceEnds other = (vertex, far) ∨
        data.sourceEnds other = (far, vertex)) →
      other ≠ survivor.1 →
      DanglingSide data.sourceGraph vertex far → False := by
    intro far other hOtherEnds hNe cut
    obtain ⟨first, second, smaller, hSurvivorEnds, _⟩ :=
      danglingSideDescent data vertex far cut other survivor.1 hOtherEnds
        survivor.2 (fun hEq ↦ hNe hEq.symm)
    exact hSurvives (isDangling_of_danglingSide data hSurvivorEnds smaller)
  -- the surviving occurrence is the only one joining its two endpoints
  have hPos : 0 < num_edges data.sourceGraph vertex outer :=
    num_edges_pos_of_sourceEnds data hEnds
  have hEdgeOne : num_edges data.sourceGraph vertex outer = 1 := by
    by_contra hNeOne
    have hTwo : 1 < ((Finset.univ : Finset data.SourceEdge).filter fun edge ↦
        data.sourceEnds edge = (vertex, outer) ∨
          data.sourceEnds edge = (outer, vertex)).card := by
      rw [← num_edges_sourceGraph_eq_card_filter]
      omega
    obtain ⟨first, hFirst, second, hSecond, hNeFirstSecond⟩ :=
      Finset.one_lt_card.mp hTwo
    obtain ⟨other, hOtherMem, hOtherNe⟩ :
        ∃ other ∈ (Finset.univ : Finset data.SourceEdge).filter (fun edge ↦
          data.sourceEnds edge = (vertex, outer) ∨
            data.sourceEnds edge = (outer, vertex)), other ≠ survivor.1 := by
      by_cases hCase : first = survivor.1
      · exact ⟨second, hSecond, fun hEq ↦ hNeFirstSecond (hCase.trans hEq.symm)⟩
      · exact ⟨first, hFirst, hCase⟩
    have hOtherEnds := (Finset.mem_filter.mp hOtherMem).2
    have hDangling : IsDangling data other :=
      hOtherDangling other (incident_of_sourceEnds data hOtherEnds) hOtherNe
    rcases danglingSide_of_isDangling data hOtherEnds hDangling with hCut | hCut
    · obtain ⟨cut⟩ := hCut
      exact hNoInnerCut outer other hOtherEnds hOtherNe cut
    · obtain ⟨cut⟩ := hCut
      have hCutOne : num_edges data.sourceGraph outer vertex = 1 :=
        cut.num_edges_endpoints
      have hSym : num_edges data.sourceGraph vertex outer =
          num_edges data.sourceGraph outer vertex :=
        num_edges_symmetric data.sourceGraph vertex outer
      exact hNeOne (hSym.trans hCutOne)
  -- every other neighbour hangs in a genus-zero branch
  have hBranches : ∀ b : data.SourceVertex, b ≠ outer →
      0 < num_edges data.sourceGraph vertex b →
      Nonempty (DanglingSide data.sourceGraph b vertex) := by
    intro b hbNe hbPos
    obtain ⟨other, hOtherEnds⟩ := exists_sourceEnds_of_num_edges_pos data hbPos
    have hOtherNe : other ≠ survivor.1 := by
      intro hEq
      rw [hEq] at hOtherEnds
      exact hbNe (other_end_unique data hOtherEnds hEnds)
    have hDangling : IsDangling data other :=
      hOtherDangling other (incident_of_sourceEnds data hOtherEnds) hOtherNe
    rcases danglingSide_of_isDangling data hOtherEnds hDangling with hCut | hCut
    · obtain ⟨cut⟩ := hCut
      exact (hNoInnerCut b other hOtherEnds hOtherNe cut).elim
    · exact hCut
  obtain ⟨cut⟩ := exists_danglingSide_of_forall_neighbour_dangling hConnected
    hEdgeOne hBranches
  exact hSurvives (isDangling_of_danglingSide data hEnds cut)

/-! ## The arithmetic of `lem-rphi-nd` at a block of vanishing ramification -/

/-- Each surviving occurrence has index at most the block size, so the total
surviving index is at most `nd(A) · |A|`. -/
theorem sum_sourceEdgeIndex_nonDangling_le
    (data : GluingDatum target degree) (vertex : data.SourceVertex) :
    (∑ edge ∈ (Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
        (fun edge ↦ ¬ IsDangling data edge.1),
      (data.sourceEdgeIndex edge.1 : ℤ)) ≤
      (nonDanglingValency data vertex : ℤ) *
        ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
  classical
  calc
    (∑ edge ∈ (Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
        (fun edge ↦ ¬ IsDangling data edge.1),
        (data.sourceEdgeIndex edge.1 : ℤ)) ≤
        ∑ _edge ∈ (Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
          (fun edge ↦ ¬ IsDangling data edge.1),
          ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
      refine Finset.sum_le_sum ?_
      intro edge _
      exact_mod_cast sourceEdgeIndex_le_blockCard data vertex edge
    _ = (nonDanglingValency data vertex : ℤ) *
        ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        card_filter_not_isDangling_eq_nonDanglingValency]

/-- Each surviving occurrence has index at least one. -/
theorem le_sum_sourceEdgeIndex_nonDangling
    (data : GluingDatum target degree) (vertex : data.SourceVertex) :
    (nonDanglingValency data vertex : ℤ) ≤
      ∑ edge ∈ (Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
        (fun edge ↦ ¬ IsDangling data edge.1),
        (data.sourceEdgeIndex edge.1 : ℤ) := by
  classical
  calc
    (nonDanglingValency data vertex : ℤ) =
        ∑ _edge ∈ (Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
          (fun edge ↦ ¬ IsDangling data edge.1), (1 : ℤ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one,
        card_filter_not_isDangling_eq_nonDanglingValency]
    _ ≤ ∑ edge ∈ (Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
          (fun edge ↦ ¬ IsDangling data edge.1),
          (data.sourceEdgeIndex edge.1 : ℤ) := by
      refine Finset.sum_le_sum ?_
      intro edge _
      exact_mod_cast sourceEdgeIndex_pos data edge.1

/-- The number of incident occurrences at a block, in terms of the local
ramification: `N(A) = r(A) + 2 + |A| · (val(v) - 2)`. -/
theorem card_incidentSourceEdge_eq_localRamification_form
    (data : GluingDatum target degree) (vertex : data.SourceVertex) :
    (Fintype.card (IncidentSourceEdge data vertex) : ℤ) =
      data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ + 2 +
        ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) *
          (((GluingDatum.incidentEdges vertex.1.1).card : ℤ) - 2) := by
  have hCard := card_incidentSourceEdge_eq_sum_blockCountWithin data vertex
  unfold GluingDatum.localRamification
  rw [hCard, Nat.cast_sum]
  ring

/-- The surviving valency never exceeds the number of incident occurrences. -/
theorem nonDanglingValency_le_card_incidentSourceEdge
    (data : GluingDatum target degree) (vertex : data.SourceVertex) :
    nonDanglingValency data vertex ≤
      Fintype.card (IncidentSourceEdge data vertex) := by
  classical
  calc
    nonDanglingValency data vertex =
        ((Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
          (fun edge ↦ ¬ IsDangling data edge.1)).card :=
      (card_filter_not_isDangling_eq_nonDanglingValency data vertex).symm
    _ ≤ (Finset.univ : Finset (IncidentSourceEdge data vertex)).card :=
      Finset.card_filter_le _ _
    _ = Fintype.card (IncidentSourceEdge data vertex) := Finset.card_univ

/-- **Observation I, vertex form.**  A block of vanishing local ramification
with no surviving incident occurrence is a single sheet. -/
theorem blockCard_eq_one_of_nonDanglingValency_eq_zero
    (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (vertex : data.SourceVertex)
    (hZero : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0)
    (hValency : nonDanglingValency data vertex = 0) :
    (data.vertexPartition vertex.1.1).blockCard vertex.1.2 = 1 := by
  classical
  have hEmpty : (Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
      (fun edge ↦ ¬ IsDangling data edge.1) = ∅ := by
    rw [← Finset.card_eq_zero,
      card_filter_not_isDangling_eq_nonDanglingValency]
    exact hValency
  have hForm := localRamification_eq_nonDangling_form data hNoGlue vertex
  rw [hZero, hEmpty, Finset.sum_empty, hValency] at hForm
  have hCast : ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) = 1 := by
    push_cast at hForm
    linarith
  exact_mod_cast hCast

/-- **`lem-rphi-nd` with the two index bounds.**  At a block of vanishing
local ramification, `(nd(A) - 2) · (|A| - 1) ≥ 0`: a block of size at least
two has surviving valency zero or at least two. -/
theorem localRamification_zero_index_inequality
    (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (vertex : data.SourceVertex)
    (hZero : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0) :
    0 ≤ ((nonDanglingValency data vertex : ℤ) - 2) *
      (((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) - 1) := by
  have hForm := localRamification_eq_nonDangling_form data hNoGlue vertex
  rw [hZero] at hForm
  have hUpper := sum_sourceEdgeIndex_nonDangling_le data vertex
  have hExpand : ((nonDanglingValency data vertex : ℤ) - 2) *
      (((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) - 1) =
      (nonDanglingValency data vertex : ℤ) *
          ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) -
        ((nonDanglingValency data vertex : ℤ) - 2 +
          2 * ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ)) := by
    ring
  rw [hExpand]
  linarith

/-- **The occurrence bound.**  At a block of vanishing local ramification the
surviving valency is at most `2 + |A| · (val(v) - 2)`. -/
theorem nonDanglingValency_le_of_localRamification_zero
    (data : GluingDatum target degree) (vertex : data.SourceVertex)
    (hZero : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0) :
    (nonDanglingValency data vertex : ℤ) ≤
      2 + ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) *
        (((GluingDatum.incidentEdges vertex.1.1).card : ℤ) - 2) := by
  have hCard := card_incidentSourceEdge_eq_localRamification_form data vertex
  rw [hZero] at hCard
  have hLe : (nonDanglingValency data vertex : ℤ) ≤
      (Fintype.card (IncidentSourceEdge data vertex) : ℤ) := by
    exact_mod_cast nonDanglingValency_le_card_incidentSourceEdge data vertex
  linarith

/-- The paper's dichotomy in the form used downstream: at any source vertex
the surviving valency is either zero or at least two. -/
theorem nonDanglingValency_eq_zero_or_two_le
    (data : GluingDatum target degree) (hConnected : data.Connected)
    (vertex : data.SourceVertex) :
    nonDanglingValency data vertex = 0 ∨ 2 ≤ nonDanglingValency data vertex := by
  have hNe := nonDanglingValency_ne_one data hConnected vertex
  omega

/-! ## Equation (C) at a W4 wall -/

/-- Vanishing change at a target vertex makes every block above it
unramified. -/
theorem localRamification_eq_zero_of_targetChange_eq_zero
    (data : GluingDatum target degree) (hValid : data.Valid)
    (vertex : target.V) (hChange : data.targetChange vertex = 0)
    (block : (data.vertexPartition vertex).Blocks) :
    data.localRamification vertex block = 0 := by
  have hNonneg :
      ∀ b ∈ (Finset.univ : Finset (data.vertexPartition vertex).Blocks),
        0 ≤ data.localRamification vertex b :=
    fun b _ ↦ data.localRamification_nonneg vertex (hValid.2 vertex) b
  have hSum : ∑ b : (data.vertexPartition vertex).Blocks,
      data.localRamification vertex b = 0 := hChange
  exact (Finset.sum_eq_zero_iff_of_nonneg hNonneg).mp hSum block
    (Finset.mem_univ block)

/-- Equation (C) at a four-valent wall: `ch(w₀) + val(w₀) - 3 = 1` with
`val(w₀) = 4` gives `ch(w₀) = 0`. -/
theorem targetChange_eq_zero_of_targetExcess_eq_one
    (data : GluingDatum target degree) (vertex : target.V)
    (hValency : (GluingDatum.incidentEdges vertex).card = 4)
    (hExcess : data.targetExcess vertex = 1) :
    data.targetChange vertex = 0 := by
  unfold GluingDatum.targetExcess at hExcess
  rw [hValency] at hExcess
  push_cast at hExcess
  linarith

/-- Equation (C) at a W4 wall makes every wall block unramified. -/
theorem localRamification_wallBlock_eq_zero
    {wall : target.V} (data : GluingDatum target degree) (hValid : data.Valid)
    (star : W4TargetPairings.FourStar target wall)
    (hExcess : data.targetExcess wall = 1)
    (sourceBlock : WallBlock data wall) :
    data.localRamification wall sourceBlock = 0 :=
  localRamification_eq_zero_of_targetChange_eq_zero data hValid wall
    (targetChange_eq_zero_of_targetExcess_eq_one data wall
      star.card_incidentEdges hExcess) sourceBlock

/-- The block of a wall block's quotient-source vertex is that wall block. -/
theorem sourceVertex_block_eq {wall : target.V}
    (data : GluingDatum target degree) (sourceBlock : WallBlock data wall) :
    (⟨(WallBlock.sourceVertex data wall sourceBlock).1.2,
      (WallBlock.sourceVertex data wall sourceBlock).2⟩ :
        (data.vertexPartition wall).Blocks) = sourceBlock :=
  Subtype.ext sourceBlock.2

/-- Reading the local ramification of a wall block at its quotient-source
vertex. -/
theorem localRamification_sourceVertex {wall : target.V}
    (data : GluingDatum target degree) (sourceBlock : WallBlock data wall) :
    data.localRamification
        (WallBlock.sourceVertex data wall sourceBlock).1.1
        ⟨(WallBlock.sourceVertex data wall sourceBlock).1.2,
          (WallBlock.sourceVertex data wall sourceBlock).2⟩ =
      data.localRamification wall sourceBlock :=
  congrArg (data.localRamification wall) (sourceVertex_block_eq data sourceBlock)

/-- Reading the block size of a wall block at its quotient-source vertex. -/
theorem blockCard_sourceVertex {wall : target.V}
    (data : GluingDatum target degree) (sourceBlock : WallBlock data wall) :
    (data.vertexPartition
          (WallBlock.sourceVertex data wall sourceBlock).1.1).blockCard
        (WallBlock.sourceVertex data wall sourceBlock).1.2 =
      (data.vertexPartition wall).blockCard sourceBlock.1 :=
  congrArg (data.vertexPartition wall).blockCard sourceBlock.2

/-- **What this file proves about a W4 wall block.**  The surviving valency is
either zero — and then the block is a single sheet — or at least two, and in
the latter case it is at most `2|A| + 2`.  The only further input needed is
the trivalence bound that would replace `2|A| + 2` by `3`. -/
theorem wallBlock_local_picture {wall : target.V}
    (data : GluingDatum target degree) (hValid : data.Valid)
    (hNoGlue : DanglingEdgeNoGlue data)
    (star : W4TargetPairings.FourStar target wall)
    (hExcess : data.targetExcess wall = 1)
    (sourceBlock : WallBlock data wall) :
    (nonDanglingValency data
          (WallBlock.sourceVertex data wall sourceBlock) = 0 ∧
        (data.vertexPartition wall).blockCard sourceBlock.1 = 1) ∨
      (2 ≤ nonDanglingValency data
            (WallBlock.sourceVertex data wall sourceBlock) ∧
        (nonDanglingValency data
            (WallBlock.sourceVertex data wall sourceBlock) : ℤ) ≤
          2 * ((data.vertexPartition wall).blockCard sourceBlock.1 : ℤ) + 2) := by
  have hZero : data.localRamification
      (WallBlock.sourceVertex data wall sourceBlock).1.1
      ⟨(WallBlock.sourceVertex data wall sourceBlock).1.2,
        (WallBlock.sourceVertex data wall sourceBlock).2⟩ = 0 := by
    rw [localRamification_sourceVertex]
    exact localRamification_wallBlock_eq_zero data hValid star hExcess sourceBlock
  rcases nonDanglingValency_eq_zero_or_two_le data hValid.1
    (WallBlock.sourceVertex data wall sourceBlock) with hZeroValency | hTwo
  · refine Or.inl ⟨hZeroValency, ?_⟩
    have hCard := blockCard_eq_one_of_nonDanglingValency_eq_zero data hNoGlue
      (WallBlock.sourceVertex data wall sourceBlock) hZero hZeroValency
    rwa [blockCard_sourceVertex] at hCard
  · refine Or.inr ⟨hTwo, ?_⟩
    have hBound := nonDanglingValency_le_of_localRamification_zero data
      (WallBlock.sourceVertex data wall sourceBlock) hZero
    rw [blockCard_sourceVertex] at hBound
    have hValency : (GluingDatum.incidentEdges wall).card = 4 :=
      star.card_incidentEdges
    have hSame : (GluingDatum.incidentEdges
        (WallBlock.sourceVertex data wall sourceBlock).1.1).card = 4 := hValency
    rw [hSame] at hBound
    push_cast at hBound ⊢
    linarith

/-! ## The trichotomy, and the wall interface -/

/-- **The local trichotomy.**  Beyond connectedness the only input is the
trivalence bound `nd(A) ≤ 3`; the exclusion of `nd(A) = 1` is
`nonDanglingValency_ne_one`. -/
theorem nonDanglingValency_eq_zero_or_two_or_three
    (data : GluingDatum target degree) (hConnected : data.Connected)
    (vertex : data.SourceVertex)
    (hLe : nonDanglingValency data vertex ≤ 3) :
    nonDanglingValency data vertex = 0 ∨ nonDanglingValency data vertex = 2 ∨
      nonDanglingValency data vertex = 3 := by
  have hNe := nonDanglingValency_ne_one data hConnected vertex
  omega

/-- Wall-block form, matching the `nonDangling_valency` field of
`W4StableSource.AuxR0SourceInput` verbatim. -/
theorem wallBlock_nonDanglingValency_eq_zero_or_two_or_three
    {wall : target.V} (data : GluingDatum target degree) (hValid : data.Valid)
    (hLe : ∀ sourceBlock : WallBlock data wall,
      nonDanglingValency data
        (WallBlock.sourceVertex data wall sourceBlock) ≤ 3) :
    ∀ sourceBlock : WallBlock data wall,
      nonDanglingValency data
          (WallBlock.sourceVertex data wall sourceBlock) = 0 ∨
        nonDanglingValency data
            (WallBlock.sourceVertex data wall sourceBlock) = 2 ∨
          nonDanglingValency data
            (WallBlock.sourceVertex data wall sourceBlock) = 3 :=
  fun sourceBlock ↦ nonDanglingValency_eq_zero_or_two_or_three data hValid.1 _
    (hLe sourceBlock)

/-- **WARNING: this theorem's hypotheses are contradictory, so it is vacuous and
must not be built on.**  Two independent inconsistencies, both proved in
`DraismaVargas.LocalCases.FullDimensionalSource`:

* `hMinimal : data.ChangeMinimal` says the target excess is `0` at *every*
  vertex, while `equation_c` says it is `1` at `wall`
  (`false_of_changeMinimal_auxR0SourceInput`);
* a `StableLengthMatrixLabelling data coordinate` carries
  `StablePath data ≃ coordinate ≃ target.edges`, forcing
  `Fintype.card (StablePath data) = target.edges.card`, while `stablePath_card`
  asserts `target.edges.card + 1` (`false_of_labelling_auxR0SourceInput`).

The cause is structural rather than a slip in this proof.  `AuxR0SourceInput`
describes the **codimension-one wall datum**: its target is one occurrence
short and it carries excess `1` at the wall.  A *square* honest stable
presentation describes the **full-dimensional datum**: change-minimal, with one
stable path per target occurrence.  Those are different data, so no adapter on a single `data` can
exist, and `FullDimensionalSourcePresentation.false_of_auxR0SourceInput` proves exactly that.

Everything above this declaration is unaffected; in particular
`nonDanglingValency_ne_one` and the trichotomy are genuine.  The sound approach
is to relate a full-dimensional datum to its wall degeneration -- see
`FullDimensionalSource.WallDegeneration` -- rather than to assume both
descriptions of one datum. -/
theorem auxR0SourceInput_of_det_ne_zero
    {wall : target.V} {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (valid : data.Valid)
    (stablePath_card : Fintype.card (StablePath data) = target.edges.card + 1)
    (hMinimal : data.ChangeMinimal)
    (labelling : StableLengthMatrixLabelling data coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix
      labelling.presentation).det ≠ 0)
    (hValency : ∀ sourceBlock : WallBlock data wall,
      nonDanglingValency data
        (WallBlock.sourceVertex data wall sourceBlock) ≤ 3)
    (equation_c : data.targetExcess wall = 1) :
    AuxR0SourceInput data star where
  valid := valid
  stablePath_card := stablePath_card
  dangling_no_glue :=
    danglingEdgeNoGlue_of_det_ne_zero data valid hMinimal labelling hDet
  nonDangling_valency :=
    wallBlock_nonDanglingValency_eq_zero_or_two_or_three data valid hValency
  equation_c := equation_c

end Gluing

end DraismaVargas.LocalCases.NonDanglingValency

