module

public import DraismaVargas.LocalCases.TraversalPresentation
public import DraismaVargas.LocalCases.ZeroForestPreservation

@[expose] public section

/-!
# Cycles of the quotient source are unions of displayed rows

`TraversalPresentation.isForest_of_cyclesAreRows` reduces the forest receipt
at a terminal face (the zero set of a cleared face is a census forest) to one
residual incidence condition, `TraversalPresentation.CyclesAreRows`:

```
∀ slots, ¬ IsForest (core sourceGraph) slots →
  ∃ row, ∀ edge ∈ presentation.path row, sourceSlotEquiv.symm edge ∈ slots
```

This file proves that condition from `TraversalPresentation.StrongPresentation`
together with two purely local source-side inputs.  The census lemma the
argument needs, which `Utilities.Certificate.ContractionForestCensusGeneral`
does not provide, is in `TerminalForestReceipt` §0.

## §1 The census converse, in `TerminalForestReceipt` §0

`ContractionForestCensusGeneral` proves the graphic-matroid rank *inequality*
`n ≤ #classes + F.card` for every slot set, defines `IsForest F` to be its
equality case, and derives the consequences of `IsForest`
(`forest_image_add_card_eq`, `forest_card_lt`, and — in
`ZeroForestBridge.isForest_of_subset` — heredity).  It never produces an
`IsForest` from acyclicity.  The converse — *acyclic ⟹ forest* — is
`isForest_of_acyclic`, and `exists_redundant_of_not_isForest` is
the contrapositive in the form the rest of this file consumes: **a slot set
that is not a census forest carries a redundant slot.**  With it come the
minimal-non-forest lemmas `exists_minimal_not_isForest`,
`exists_ne_slotAt_of_minimal` (every core vertex met by a slot of a minimal
non-forest `C` is met by a second one) and `notMem_of_separated` (a bridge is
never in `C`).

All of them live in `TerminalForestReceipt` §0, alongside
`not_isForest_of_redundant`, which is the other direction of the same
equivalence (`isForest_iff_acyclic`); the `open` at the top of the file brings
in the names §2--§4 consume.

## §2 The source-side dictionary

`ZeroForestPreservation` already matches census slots with source occurrences
(`slotOf`, `SlotStep`, `reachIn_iff_reflTransGen_slotStep`) and census vertex
labels with quotient-source vertices (`ZeroForestBridge.sourceVertexOf`).  §2
adds the incidence translation `slotAt_iff_incident` and the two facts §3 needs
about a dangling occurrence: it is the unique occurrence crossing its dangling
cut (`eq_of_crosses`), hence a bridge (`not_reachIn_of_isDangling`).

## §3 The row argument

A cycle consists of surviving occurrences, and a cycle cannot enter a stable
path partway, because the interior vertices of a stable path have surviving
valency exactly two.  Formally, let `C ⊆ slots` be a minimal non-forest.

* No slot of `C` is dangling (§1 `notMem_of_separated` + §2
  `not_reachIn_of_isDangling`).
* Take a slot of `C`; its occurrence survives, so `StrongPresentation.decomposes`
  puts it in a unique row.
* Walk along that row.  Consecutive occurrences meet at a vertex of surviving
  valency two (`StrongPresentation.chain`); at such a vertex there are exactly
  two surviving occurrences (`W4StableSource.nonDanglingIncident_eq_pair`), and
  `C` supplies a second one (§1), which is therefore the next occurrence of the
  row.  So membership in `C` propagates along the whole row, in both
  directions.

Hence the row lies in `C ⊆ slots`, which is `CyclesAreRows`.

## What the argument needs beyond `StrongPresentation`

Nothing about the rows, and nothing assumed about `data`:

* `Connected` is *not* needed.  What is needed is that no dangling occurrence
  lies on a cycle; the argument uses the occurrence's `DanglingSide`
  certificate, which is exactly `IsDangling`, and the fact is proved here
  (`not_reachIn_of_isDangling`), not assumed.
* Nothing else.  `cyclesAreRows` below takes a `StrongPresentation` and a
  `ClearedFace` and nothing more.

See §5 for the joint-satisfiability discussion.
-/

namespace DraismaVargas.LocalCases.CycleRows

open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open DraismaVargas.LocalCases.TerminalForestReceipt
  (SlotAt exists_minimal_not_isForest exists_ne_slotAt_of_minimal
    notMem_of_separated)
open DraismaVargas.LocalCases.ZeroFreeTerminalFace (isForest_empty)

/-! ## 1.  The census converse and minimal non-forests

The census converse and the minimal-non-forest lemmas live in
`TerminalForestReceipt` §0, next to `not_isForest_of_redundant`, which is
the other direction of the same equivalence:

  `isForest_of_acyclic`, `exists_redundant_of_not_isForest`,
  `isForest_iff_acyclic`, `isForest_of_not_reachIn_erase`,
  `exists_minimal_not_isForest`, `SlotAt`, `exists_ne_slotAt_of_minimal`,
  `notMem_of_separated`, `ZeroFreeTerminalFace.isForest_empty`

and their supporting lemmas `reachIn_mono`, `eq_of_reachIn_of_no_incidence`,
`card_image_compFold_lt_of_not_reachIn`, `Acyclic` and
`card_image_compFold_add_card_le_of_acyclic`.  This file reaches them through
`TraversalPresentation` and opens the ones it consumes, just above. -/


/-! ## 2.  The source-side dictionary, and dangling occurrences are bridges

`ZeroForestPreservation` supplies the translation of census reachability into
walks through source occurrences (`reachIn_iff_reflTransGen_slotStep`); what is
added here is the incidence translation and the fact that a dangling occurrence
lies on no cycle.  The latter is immediate from the `DanglingSide` certificate
once one knows that a dangling occurrence is the *only* occurrence crossing its
cut, which is what the multiplicity field `cross_num_edges` says. -/

section Source

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.ZeroForestBridge
open DraismaVargas.LocalCases.ZeroForestPreservation

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)
  (realization : data.NonnegativeIntegralRealization)

/-- Census incidence of a slot is incidence of the occurrence it carries. -/
theorem slotAt_iff_incident (slot : Fin data.sourceGraph.edges.card)
    (x : Fin (Fintype.card data.sourceGraph.V)) :
    SlotAt (UnitSubdivisionPresentation.core data.sourceGraph) slot x ↔
      Incident data (realization.sourceEdgeAt slot) (sourceVertexOf data x) := by
  have hTail := vertexEquiv_symm_core_tail data realization slot
  have hHead := vertexEquiv_symm_core_head data realization slot
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [← hTail, h])
    · exact Or.inr (by rw [← hHead, h])
  · rintro (h | h)
    · exact Or.inl (sourceVertexOf_injective data (by rw [hTail, h]))
    · exact Or.inr (sourceVertexOf_injective data (by rw [hHead, h]))

/-- The census core of a quotient source is loopless. -/
theorem core_loopless (slot : Fin data.sourceGraph.edges.card) :
    (UnitSubdivisionPresentation.core data.sourceGraph).tail slot
      ≠ (UnitSubdivisionPresentation.core data.sourceGraph).head slot :=
  (UnitSubdivisionPresentation.spec data.sourceGraph).core_loopless slot

/-- Two distinct occurrences joining the same pair of quotient-source vertices
make the multiplicity at least two. -/
theorem two_le_num_edges_of_ne {first second : data.SourceEdge} (hNe : first ≠ second)
    {a b : data.SourceVertex}
    (hFirst : data.sourceEnds first = (a, b) ∨ data.sourceEnds first = (b, a))
    (hSecond : data.sourceEnds second = (a, b) ∨ data.sourceEnds second = (b, a)) :
    2 ≤ num_edges data.sourceGraph a b := by
  classical
  rw [GluingDatum.SheetRelabeling.num_edges_sourceGraph_eq_sum]
  have hSubset : ({first, second} : Finset data.SourceEdge) ⊆
      Finset.univ.filter fun edge ↦ data.sourceEnds edge = (a, b) ∨
        data.sourceEnds edge = (b, a) := by
    intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFirst⟩
    · rw [Finset.mem_singleton] at hEdge
      exact hEdge ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSecond⟩
  have hPair : ({first, second} : Finset data.SourceEdge).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hNe), Finset.card_singleton]
  have hCard := Finset.card_le_card hSubset
  rw [hPair, Finset.card_filter] at hCard
  exact hCard

/-- **A separating occurrence is the only occurrence crossing its cut.** -/
theorem eq_of_crosses {x y : data.SourceVertex}
    (cut : Utilities.SeparatingEdgeCut data.sourceGraph x y)
    {edge : data.SourceEdge}
    (hEdge : data.sourceEnds edge = (x, y) ∨ data.sourceEnds edge = (y, x))
    {other : data.SourceEdge}
    (hCross :
      ((data.sourceEnds other).1 ∈ cut.side ∧ (data.sourceEnds other).2 ∉ cut.side) ∨
        ((data.sourceEnds other).2 ∈ cut.side ∧ (data.sourceEnds other).1 ∉ cut.side)) :
    other = edge := by
  have hPos := sourceEnds_num_edges_pos data other
  have hEnds : data.sourceEnds other = (x, y) ∨ data.sourceEnds other = (y, x) := by
    rcases hCross with ⟨hIn, hOut⟩ | ⟨hIn, hOut⟩
    · have hCount := cut.cross_num_edges _ _ hIn hOut
      split_ifs at hCount with hCase
      · exact Or.inl (Prod.ext hCase.1 hCase.2)
      · omega
    · have hCount := cut.cross_num_edges _ _ hIn hOut
      have hBack : 0 < num_edges data.sourceGraph
          (data.sourceEnds other).2 (data.sourceEnds other).1 := by
        unfold num_edges at hPos ⊢
        simpa only [Or.comm] using hPos
      split_ifs at hCount with hCase
      · exact Or.inr (Prod.ext hCase.2 hCase.1)
      · omega
  by_contra hNe
  have hTwo := two_le_num_edges_of_ne data hNe hEnds hEdge
  have hOne := cut.num_edges_endpoints
  omega

/-- **A separating occurrence lies on no cycle.**  Every walk avoiding its slot
stays on one side of the cut. -/
theorem not_reachIn_of_separatingEdgeCut {x y : data.SourceVertex}
    (cut : Utilities.SeparatingEdgeCut data.sourceGraph x y)
    {edge : data.SourceEdge}
    (hEdge : data.sourceEnds edge = (x, y) ∨ data.sourceEnds edge = (y, x))
    (F : Finset (Fin data.sourceGraph.edges.card))
    {slot : Fin data.sourceGraph.edges.card}
    (hSlot : realization.sourceEdgeAt slot = edge) :
    ¬ ReachIn (UnitSubdivisionPresentation.core data.sourceGraph) (F.erase slot)
      ((UnitSubdivisionPresentation.core data.sourceGraph).tail slot)
      ((UnitSubdivisionPresentation.core data.sourceGraph).head slot) := by
  intro hReach
  rw [reachIn_iff_reflTransGen_slotStep data realization] at hReach
  have hStep : ∀ u v : data.SourceVertex,
      SlotStep data realization (F.erase slot) u v → (u ∈ cut.side ↔ v ∈ cut.side) := by
    intro u v hUV
    obtain ⟨other, hOther, hOtherEnds⟩ := hUV
    have hNe : realization.sourceEdgeAt other ≠ edge := by
      intro hEq
      exact (Finset.mem_erase.mp hOther).1
        (by rw [← slotOf_sourceEdgeAt data realization other, hEq, ← hSlot,
          slotOf_sourceEdgeAt])
    by_contra hIff
    refine hNe (eq_of_crosses data cut hEdge ?_)
    rcases hOtherEnds with ⟨hFst, hSnd⟩ | ⟨hSnd, hFst⟩
    · rw [hFst, hSnd]
      by_cases hu : u ∈ cut.side
      · exact Or.inl ⟨hu, fun hv ↦ hIff ⟨fun _ ↦ hv, fun _ ↦ hu⟩⟩
      · exact Or.inr ⟨by
          by_contra hv
          exact hIff ⟨fun h ↦ absurd h hu, fun h ↦ absurd h hv⟩, hu⟩
    · rw [hFst, hSnd]
      by_cases hu : u ∈ cut.side
      · exact Or.inr ⟨hu, fun hv ↦ hIff ⟨fun _ ↦ hv, fun _ ↦ hu⟩⟩
      · exact Or.inl ⟨by
          by_contra hv
          exact hIff ⟨fun h ↦ absurd h hu, fun h ↦ absurd h hv⟩, hu⟩
  have hSide : ∀ u v : data.SourceVertex,
      Relation.ReflTransGen (SlotStep data realization (F.erase slot)) u v →
        (u ∈ cut.side ↔ v ∈ cut.side) := by
    intro u v hUV
    induction hUV with
    | refl => exact Iff.rfl
    | tail _ hLast ih => exact ih.trans (hStep _ _ hLast)
  have hTail : sourceVertexOf data
      ((UnitSubdivisionPresentation.core data.sourceGraph).tail slot)
      = (data.sourceEnds edge).1 := by
    rw [vertexEquiv_symm_core_tail data realization slot, hSlot]
  have hHead : sourceVertexOf data
      ((UnitSubdivisionPresentation.core data.sourceGraph).head slot)
      = (data.sourceEnds edge).2 := by
    rw [vertexEquiv_symm_core_head data realization slot, hSlot]
  rw [hTail, hHead] at hReach
  have hFinal := hSide _ _ hReach
  rcases hEdge with hEq | hEq <;> rw [hEq] at hFinal
  · exact cut.right_not_mem (hFinal.mp cut.left_mem)
  · exact cut.right_not_mem (hFinal.mpr cut.left_mem)

/-- **A dangling occurrence lies on no cycle.**  Both orientations of the
dangling certificate are separating edge cuts. -/
theorem not_reachIn_of_isDangling {edge : data.SourceEdge}
    (hDangling : IsDangling data edge)
    (F : Finset (Fin data.sourceGraph.edges.card))
    {slot : Fin data.sourceGraph.edges.card}
    (hSlot : realization.sourceEdgeAt slot = edge) :
    ¬ ReachIn (UnitSubdivisionPresentation.core data.sourceGraph) (F.erase slot)
      ((UnitSubdivisionPresentation.core data.sourceGraph).tail slot)
      ((UnitSubdivisionPresentation.core data.sourceGraph).head slot) := by
  rcases hDangling with hCut | hCut
  · obtain ⟨cut⟩ := hCut
    exact not_reachIn_of_separatingEdgeCut data realization cut.toSeparatingEdgeCut
      (Or.inl rfl) F hSlot
  · obtain ⟨cut⟩ := hCut
    exact not_reachIn_of_separatingEdgeCut data realization cut.toSeparatingEdgeCut
      (Or.inr rfl) F hSlot

end Source

/-! ## 3.  A cycle is a union of whole rows

The interior vertices of a stable path have surviving valency exactly two, so a
cycle cannot enter a row partway.  §1 gives the cycle its two incidences at
every vertex it meets, §2 keeps dangling occurrences off it, and
`StrongPresentation.chain` together with
`W4StableSource.nonDanglingIncident_eq_pair` turns the second incidence into the
next occurrence of the same row. -/

section Rows

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.PresentationDecomposition
open DraismaVargas.LocalCases.TraversalPresentation
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.ZeroForestBridge
open DraismaVargas.LocalCases.ZeroForestPreservation

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {wall : target.V} {candidate : Candidate target degree data wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ}

/-- A property constant along the steps of a chain is constant on the chain. -/
private theorem forall_mem_iff_of_isChain {α : Type*} {R : α → α → Prop}
    {P : α → Prop} :
    ∀ L : List α, L.IsChain R → (∀ a ∈ L, ∀ b ∈ L, R a b → (P a ↔ P b)) →
      ∀ a ∈ L, ∀ b ∈ L, (P a ↔ P b) := by
  intro L
  induction L with
  | nil => intro _ _ a ha; simp at ha
  | cons x xs ih =>
    intro hChain hStep
    have hKey : ∀ b ∈ x :: xs, (P x ↔ P b) := by
      intro b hb
      match xs, hChain with
      | [], _ =>
        rw [List.mem_singleton] at hb
        exact hb ▸ Iff.rfl
      | y :: ys, hChain =>
        rw [List.isChain_cons_cons] at hChain
        have hHead : P x ↔ P y :=
          hStep x (by simp) y (by simp) hChain.1
        have hTail := ih hChain.2
          (fun a ha b hb hab ↦ hStep a (List.mem_cons_of_mem _ ha)
            b (List.mem_cons_of_mem _ hb) hab)
        rcases List.mem_cons.mp hb with hb | hb
        · exact hb ▸ Iff.rfl
        · exact hHead.trans (hTail y (by simp) b hb)
    exact fun a ha b hb ↦ (hKey a ha).symm.trans (hKey b hb)

/-- The meeting predicate of a strong presentation is symmetric. -/
theorem meetsAt_symm {first second : data.SourceEdge}
    (hMeet : MeetsAt data first second) : MeetsAt data second first := by
  obtain ⟨vertex, hFirst, hSecond, hValency⟩ := hMeet
  exact ⟨vertex, hSecond, hFirst, hValency⟩

/-- **The propagation step.**  A minimal non-forest whose slots all survive
contains, with one occurrence of a row, the occurrence the row meets it at. -/
theorem mem_of_meetsAt
    (realization : data.NonnegativeIntegralRealization)
    {C : Finset (Fin data.sourceGraph.edges.card)}
    (hNot : ¬ IsForest
      (UnitSubdivisionPresentation.core data.sourceGraph) C)
    (hMin : ∀ drop ∈ C, IsForest
      (UnitSubdivisionPresentation.core data.sourceGraph) (C.erase drop))
    (hSurvive : ∀ slot ∈ C,
      ¬ IsDangling data (realization.sourceEdgeAt slot))
    {first second : data.SourceEdge}
    (hFirstSurvives : ¬ IsDangling data first)
    (hSecondSurvives : ¬ IsDangling data second)
    (hMeet : MeetsAt data first second)
    (hFirstMem : slotOf data realization first ∈ C) :
    slotOf data realization second ∈ C := by
  obtain ⟨vertex, hFirstIncident, hSecondIncident, hValency⟩ := hMeet
  set label := (sourceVertexEquiv data).symm vertex with hLabel
  have hVertex : sourceVertexOf data label = vertex := by
    rw [hLabel, ← sourceVertexEquiv_apply, Equiv.apply_symm_apply]
  have hSlotAt : SlotAt (UnitSubdivisionPresentation.core data.sourceGraph)
      (slotOf data realization first) label := by
    rw [slotAt_iff_incident data realization, sourceEdgeAt_slotOf, hVertex]
    exact hFirstIncident
  obtain ⟨other, hOtherMem, hOtherNe, hOtherAt⟩ :=
    exists_ne_slotAt_of_minimal _ hNot hMin (core_loopless data)
      hFirstMem hSlotAt
  rw [slotAt_iff_incident data realization, hVertex] at hOtherAt
  obtain ⟨companion, hCompanionNe, hPair⟩ :=
    nonDanglingIncident_eq_pair data hValency hFirstSurvives hFirstIncident
  have hSecondPair : second ∈ ({first, companion} : Finset data.SourceEdge) := by
    rw [← hPair]
    exact (mem_nonDanglingIncident data vertex second).mpr
      ⟨hSecondSurvives, hSecondIncident⟩
  have hOtherPair : realization.sourceEdgeAt other
      ∈ ({first, companion} : Finset data.SourceEdge) := by
    rw [← hPair]
    exact (mem_nonDanglingIncident data vertex _).mpr
      ⟨hSurvive other hOtherMem, hOtherAt⟩
  have hOtherCompanion : realization.sourceEdgeAt other = companion := by
    rcases Finset.mem_insert.mp hOtherPair with hCase | hCase
    · exact absurd (by rw [← slotOf_sourceEdgeAt data realization other,
        hCase]) hOtherNe
    · exact Finset.mem_singleton.mp hCase
  rcases Finset.mem_insert.mp hSecondPair with hCase | hCase
  · rw [hCase]
    exact hFirstMem
  · rw [Finset.mem_singleton] at hCase
    rw [hCase, ← hOtherCompanion, slotOf_sourceEdgeAt]
    exact hOtherMem

/-- **Every cycle of the quotient source is a union of complete displayed
rows.**  The residual incidence condition of
`TraversalPresentation.isForest_of_cyclesAreRows`.

Only two of the seven fields of `TraversalPresentation.StrongPresentation` are
used, and they are exactly the two `PresentationDecomposition` already names:
the rows partition the surviving occurrences, and consecutive occurrences of a
row meet at a surviving valency-two vertex.  The endpoint fields — the
strengthening `StrongPresentation` was built for — are not needed here; a row
that closed up into a cycle would still be swallowed whole. -/
theorem row_subset_of_not_isForest
    {presentation : data.LengthMatrixPresentation coordinate}
    (hDecomposes : Decomposes presentation)
    (hChain : ∀ row : coordinate,
      (presentation.path row).IsChain (MeetsAt data))
    (realization : data.NonnegativeIntegralRealization)
    (slots : Finset (Fin data.sourceGraph.edges.card))
    (hSlots : ¬ IsForest (UnitSubdivisionPresentation.core data.sourceGraph) slots) :
    ∃ row : coordinate, ∀ edge ∈ presentation.path row,
      realization.sourceSlotEquiv.symm edge ∈ slots := by
  classical
  obtain ⟨C, hSubset, hNot, hMin⟩ :=
    exists_minimal_not_isForest
      (UnitSubdivisionPresentation.core data.sourceGraph) slots hSlots
  have hSurvive : ∀ slot ∈ C,
      ¬ IsDangling data (realization.sourceEdgeAt slot) := by
    intro slot hSlot hDangling
    exact notMem_of_separated _ hNot hMin
      (fun F ↦ not_reachIn_of_isDangling data realization hDangling F rfl)
      hSlot
  obtain ⟨start, hStart⟩ : C.Nonempty := by
    rcases C.eq_empty_or_nonempty with rfl | hNonempty
    · exact absurd (isForest_empty _) hNot
    · exact hNonempty
  obtain ⟨row, hRow⟩ := hDecomposes.surviving_mem
    (realization.sourceEdgeAt start) (hSurvive start hStart)
  refine ⟨row, ?_⟩
  have hNonDangling : ∀ edge ∈ presentation.path row,
      ¬ IsDangling data edge := by
    intro edge hEdge hDangling
    exact hDecomposes.dangling_not_mem edge hDangling row hEdge
  have hConstant := forall_mem_iff_of_isChain
    (P := fun edge ↦ slotOf data realization edge ∈ C)
    (presentation.path row) (hChain row)
    (fun a ha b hb hab ↦
      ⟨fun hA ↦ mem_of_meetsAt realization hNot hMin hSurvive
          (hNonDangling a ha) (hNonDangling b hb) hab hA,
        fun hB ↦ mem_of_meetsAt realization hNot hMin hSurvive
          (hNonDangling b hb) (hNonDangling a ha) (meetsAt_symm hab) hB⟩)
  intro edge hEdge
  refine hSubset ?_
  refine (hConstant (realization.sourceEdgeAt start) hRow edge hEdge).mp ?_
  rw [slotOf_sourceEdgeAt]
  exact hStart

/-- The cleared-face form of the generic occurrence argument. -/
theorem cyclesAreRows_of_decomposes
    {presentation : candidate.datum.LengthMatrixPresentation coordinate}
    (hDecomposes : Decomposes presentation)
    (hChain : ∀ row : coordinate,
      (presentation.path row).IsChain (MeetsAt candidate.datum))
    (face : ClearedFace candidate presentation coordinates) :
    CyclesAreRows presentation face :=
  row_subset_of_not_isForest hDecomposes hChain face.realization

/-- **The residual incidence condition, from a strong presentation.** This is
the hypothesis of `TraversalPresentation.isForest_of_cyclesAreRows`,
discharged. -/
theorem cyclesAreRows (strong : StrongPresentation candidate.datum coordinate)
    (face : ClearedFace candidate strong.toPresentation coordinates) :
    CyclesAreRows strong.toPresentation face :=
  cyclesAreRows_of_decomposes strong.decomposes strong.chain face

end Rows

/-! ## 4.  The forest receipt at a terminal face

With §3 in hand `TraversalPresentation.isForest_of_cyclesAreRows` needs no
hypothesis beyond a strong presentation and the interface.  The other input
of a terminal face, `Candidate.ClearedFace.InputRefinement` — the
identification of the *pruned* contracted source with the scaled input — is
not a statement about the source alone and is not addressed here. -/

section Residue

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.SemanticAtlasMarch
open DraismaVargas.LocalCases.TraversalPresentation
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph

variable {coordinate chart : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}

/-- **The forest receipt, unconditionally.**  The zero set of a cleared face of
a strong presentation is a census forest: the arithmetic half is
`TraversalPresentation.exists_sourceLength_ne_zero_of_interface`, the incidence
half is §3. -/
theorem isForest_sourceZeroSet {target : CFGraph.{0}}
    {data : GluingDatum target degree} {wall : target.V}
    {candidate : Candidate target degree data wall}
    {coordinates : coordinate → ℚ} {n p : ℕ} {spec : Spec n p}
    (strong : StrongPresentation candidate.datum coordinate)
    (iface : InputInterface spec strong.toPresentation coordinates)
    (face : ClearedFace candidate strong.toPresentation coordinates) :
    ContractionForestCensusGeneral.IsForest
      (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      face.realization.sourceZeroSet :=
  isForest_of_cyclesAreRows iface face (cyclesAreRows strong face)

end Residue

/-! ## 5.  Joint satisfiability

Nothing in §3 or §4 adds a hypothesis to `TraversalPresentation`'s list, so the
joint-satisfiability check of `TraversalPresentation` §8 applies:
`TraversalPresentation.ofLabelling` realizes every field of `StrongPresentation`
simultaneously from `W4StableSource.HasPathEnds` and an honest
`W4StableSource.StableLengthMatrixLabelling`, and
`TraversalPresentation.ofFullDimensional` realizes them from the package
`FullDimensionalSource.FullDimensionalSourcePresentation` the local cases carry.
Since §4 asks for nothing beyond a strong presentation, an interface and a
cleared face, its hypotheses are realized by one object too.

The `ClearedFace` argument is likewise not a new constraint: it exists at every
nonnegative coordinate vector
(`BalancedGlobal.Candidate.clearedFace`), and at a terminal march state it is
supplied by `ZeroFreeTerminalFace.clearedFaceOfTerminal`.

The two conditions that could have conflicted are the two §3 imposes on the
*same* vertex of the quotient source: `MeetsAt` asks for surviving valency two
at the vertex where two consecutive occurrences of a row meet, while the
dangling-cut argument of §2 asks the crossing occurrence of a cut to be unique.
They never meet: §2 is applied only to occurrences carried by slots of the
minimal non-forest `C`, and `notMem_of_separated` removes exactly those, so no
occurrence is asked to be both dangling and a link of a chain.  This is the
same check `TraversalPresentation` §8 performs for `chain` against
`head_isPathEnd`.
-/

end DraismaVargas.LocalCases.CycleRows
