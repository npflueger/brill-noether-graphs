import DraismaVargas.LocalCases.W2M1kIncomingMatching
import DraismaVargas.LocalCases.W2MkkSelectedCensus

/-!
# The selected-class census at a `w2M1k` wall

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w2-r2-nd3-M-1k}`, Figure 33; the Base I/II
vocabulary is fixed once for the whole valency-two section (case `{w2-r2}`),
where the two trees contracting to `T_0` are listed.

This module determines what an **arbitrary** incoming `w2M1k` cover's two
restored endpoints and contracted occurrence carry on the distinguished block
`A₀`.  `W2M1kIncomingMatching.SelectedCensus` names the three facts; this module
produces them from the classifier's payload -- the profile and its M-1k `Shape`
(`IncomingSourceCases.W2.Classification.m1k` through
`W2M1kIncomingCensus.exists_shape_of_m1k`) -- together with the standing bundle,
one branch per Figure 33 member.

## The one fact that makes M-1k uniform: both directions look alike on `A₀`

At M-kk the doubled direction splits `A₀` as `e₁ ⊔ e₂` with both parts of
cardinality at least two, while the single direction splits it as
`e₃ ⊔ {x}`.  At M-1k **both** directions have an index-one pinned occurrence and
an index-`k` bulk one (`W2M1kStableGraph.edgePartition_blockCountWithin`), so
each direction's occurrence partition is `A₀` with *its own* pinned sheet
detached (§1, `direction_block_eq_detachSheet`).  Everything below is a
consequence of that one picture together with counting.

## Three branches, because Base I.a genuinely occurs

`W2MkkSelectedCensus.divalent_endpoints` precludes the leaf orientation at
M-kk; at M-1k Figure 33's `M⁽¹⁾` *is* the leaf member, so the incoming target is
`T_2` or `T_∅` and the dichotomy becomes a trichotomy
(`W2M1kIncomingCensus.member_trichotomy`).

**At a `T_2` wall** the counting is M-kk's, verbatim.  Write `p`, `q`, `c` for
the numbers of induced blocks above `A₀` of the `zeroEnd` endpoint, the `oneEnd`
endpoint and the contracted occurrence.  Each direction induces two blocks above
`A₀`, so `p, q ≤ 2` (`blockCountWithin_mono`); change-minimality puts one unit at
each divalent restored endpoint, so the two Riemann--Hurwitz sums are
`c + 2 - 2p = 1` and `c + 2 - 2q = 1`; and the contraction forest gives
`c + 1 = p + q`.  Exactly two solutions survive (`selected_counts`):

* `p = q = c = 1` -- **Base II.1** (in Part I's vocabulary), Figure 33's `M⁽³⁾`:
  all three wall positions carry the whole of `A₀`;
* `p = q = 2`, `c = 3` -- **Base II.2.2.M**, Figure 33's `M⁽²⁾`: each
  endpoint carries its own direction's detachment and the contracted occurrence
  carries both, i.e. `ResolutionM1k.secondNewEdge`.

Unlike M-kk, **no background census is needed** for the second branch: both
endpoints carry detachments of the wall partition itself, so
`SheetPartition.refines_detachSheet_of_block_singleton` applies twice and
M-kk's `contracted_refines_endpointPartition` has no analogue to prove.

**An aligned datum can only be `M⁽³⁾`** (`not_detaching_of_aligned`): detaching
the *same* sheet at both restored endpoints would isolate it in the join of the
two endpoint partitions -- that is, in `mergedPartition` -- while `A₀` has
`k + 1 ≥ 3` sheets.

**At a `T_∅` wall** the leaf's star is `{contracted}` and a change-minimal leaf
makes the contracted occurrence partition discrete
(`MonovalentWall.exists_leafFibre`, through
`W2MkkSelectedCensus.discrete_of_leaf`).  At the trivalent endpoint the change
vanishes, so every block has `r = 0`; with the contracted occurrence discrete
that reads `#t₂(B) + #t₃(B) = 2`, so each direction has exactly one block inside
each endpoint block and **both directions carry the trivalent endpoint's own
partition everywhere** (`branch_block_eq_flag`, `branch_block_eq_coflag`).  Each
direction isolates its own pinned sheet, so the two pinned sheets coincide:
**Base I.a's alignment is a theorem here** (`aligned_of_leaf`), and a `T_∅` wall
is never separated (`not_dividedData_of_leaf`).  At the leaf itself
`r(B) = 2|B| - 2` and `ch = 2`, so exactly one block has two sheets and every
other is a singleton; the two-sheet block contains the pinned sheet by the same
join argument.  That is `SheetPartition.pairBlock`, and Figure 33's retained
pair is therefore **produced**, not assumed: `exists_selectedCensus_leaf`
returns the `LeafPair` its census is about.

## Main results

* `join_block_eq_singleton` -- a sheet isolated by both endpoint partitions is
  isolated by their join, hence by `mergedPartition`.  This is the connectivity
  of a merged block, in the only form the census needs;
* `direction_block_eq_detachSheet` -- each wall direction detaches its own
  pinned sheet on `A₀`;
* `selected_counts` -- the `T_2` count system, solved;
* `selectedCensus_dichotomy_of_dividedData` -- `M⁽²⁾` or `M⁽³⁾` at a separated
  `T_2` wall;
* `selectedCensus_of_aligned` -- `M⁽³⁾` outright at an aligned `T_2` wall;
* `exists_selectedCensus_leaf` -- `M⁽¹⁾`, with its leaf pair, at a `T_∅` wall;
* `exists_selectedCensus` -- the three branches in one statement, from the
  classifier's payload and the standing bundle alone.

`W2M1kIncomingMatching.LeafBackgroundCensus` -- the `(1,3)` background half of
the incoming census -- is **not** proved here; `W2M1kLeafBackground` proves it.
-/

namespace DraismaVargas.LocalCases.W2M1kSelectedCensus

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open TargetExpansion ResolutionM1k FullDimensionalSource WallDegeneration
open W4Assembly W4StableSource W2R1Target SecondEquation StableLocalProperties
open M11IncomingPartitions
open W2M1kSourceCandidates
open W2M1kIncomingCensus

/-! ## §0  Two partition facts

The first is the only form of *connectivity* this census needs: a merged block
is a single class of the join of the two endpoint partitions, so a sheet that
both endpoints isolate is isolated there too.  Neither statement mentions a
gluing datum. -/

section Generic

variable {d : ℕ}

private theorem eq_anchor_of_step {left right : SheetPartition d} {anchor : Fin d}
    (hLeft : ∀ sheet, left.Rel anchor sheet → sheet = anchor)
    (hRight : ∀ sheet, right.Rel anchor sheet → sheet = anchor)
    {x y : Fin d} (hxy : left.Rel x y ∨ right.Rel x y) (hx : x = anchor) : y = anchor := by
  subst hx
  rcases hxy with h | h
  · exact hLeft y h
  · exact hRight y h

private theorem eq_anchor_iff_of_joinRel {left right : SheetPartition d} {anchor : Fin d}
    (hLeft : ∀ sheet, left.Rel anchor sheet → sheet = anchor)
    (hRight : ∀ sheet, right.Rel anchor sheet → sheet = anchor)
    {i j : Fin d} (h : SheetPartition.JoinRel left right i j) :
    (i = anchor ↔ j = anchor) := by
  induction h with
  | rel u v huv =>
      exact ⟨fun hu ↦ eq_anchor_of_step hLeft hRight huv hu,
        fun hv ↦ eq_anchor_of_step hLeft hRight (huv.imp Eq.symm Eq.symm) hv⟩
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- **A sheet isolated by both partitions is isolated by their join.** -/
theorem join_block_eq_singleton (left right : SheetPartition d) (anchor : Fin d)
    (hLeft : left.block anchor = {anchor}) (hRight : right.block anchor = {anchor}) :
    (SheetPartition.join left right).block anchor = {anchor} := by
  have hLeftRel : ∀ sheet, left.Rel anchor sheet → sheet = anchor := by
    intro sheet hSheet
    have hMem : sheet ∈ left.block anchor := (left.mem_block_iff anchor sheet).mpr hSheet
    rw [hLeft] at hMem
    simpa using hMem
  have hRightRel : ∀ sheet, right.Rel anchor sheet → sheet = anchor := by
    intro sheet hSheet
    have hMem : sheet ∈ right.block anchor := (right.mem_block_iff anchor sheet).mpr hSheet
    rw [hRight] at hMem
    simpa using hMem
  ext sheet
  rw [SheetPartition.mem_block_iff, Finset.mem_singleton]
  constructor
  · intro hRel
    exact (eq_anchor_iff_of_joinRel hLeftRel hRightRel
      ((SheetPartition.join_rel_iff left right anchor sheet).mp hRel)).mp rfl
  · intro hSheet
    subst hSheet
    exact ((SheetPartition.join left right).rel_iff sheet sheet).mpr rfl

/-- Outside the retained pair, `pairBlock` is discrete on the block. -/
theorem pairBlock_block_of_rel_of_ne (partition : SheetPartition d)
    (first second sheet : Fin d) (hne : first ≠ second)
    (hSheet : partition.Rel first sheet) (hFirst : sheet ≠ first) (hSecond : sheet ≠ second) :
    (partition.pairBlock first second hne).block sheet = {sheet} := by
  classical
  have hRepr : (partition.pairBlock first second hne).repr sheet = sheet :=
    partition.pairBlock_repr_of_rel_of_ne_second first second sheet hne hSheet hSecond
  ext value
  rw [SheetPartition.mem_block_iff, Finset.mem_singleton, SheetPartition.rel_iff, hRepr]
  constructor
  · intro hValue
    by_cases hValueBlock : partition.Rel first value
    · by_cases hValueSecond : value = second
      · exfalso
        have hTog : partition.Rel first second := by rw [← hValueSecond]; exact hValueBlock
        rw [hValueSecond, partition.pairBlock_repr_second first second hne hTog] at hValue
        exact hFirst hValue
      · rw [partition.pairBlock_repr_of_rel_of_ne_second first second value hne
          hValueBlock hValueSecond] at hValue
        exact hValue.symm
    · exfalso
      rw [partition.pairBlock_repr_of_not_rel first second value hne hValueBlock] at hValue
      refine hValueBlock ?_
      have hRelSV : partition.Rel sheet value := by
        show partition.repr sheet = partition.repr value
        rw [hValue, partition.repr_idem]
      exact hSheet.trans hRelSV
  · intro hValue
    rw [hValue, hRepr]

end Generic

/-! ## §1  One wall direction, on the distinguished block

`W2M1kStableGraph` already says that a direction's pinned and bulk occurrences
tile `A₀` and that the direction induces exactly two blocks there.  What is
added here is the literal identification: above `A₀` the direction's occurrence
partition **is** the detachment of its pinned sheet.  Nothing about an incoming
cover enters; `data` is the wall datum. -/

section Directions

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- The bulk occurrence of a direction has index `k`. -/
theorem bulkSheet_blockCard (shape : Shape profile) (label : Fin 2) :
    (data.edgePartition (star.edge label)).blockCard
      (W2M1kStableGraph.bulkSheet profile label) = shape.k := by
  have h : data.sourceEdgeIndex (W2M1kStableGraph.bulkOccurrence profile label).1 =
      (data.edgePartition (star.edge label)).blockCard
        (W2M1kStableGraph.bulkSheet profile label) := by
    show (data.edgePartition (W2M1kStableGraph.bulkOccurrence profile label).1.1.1).blockCard
      (W2M1kStableGraph.bulkSheet profile label) = _
    rw [W2M1kStableGraph.bulkOccurrence_target label]
  rw [W2M1kStableGraph.bulkOccurrence_index shape label] at h
  exact h.symm

/-- **Each wall direction detaches its own pinned sheet on `A₀`.** -/
theorem direction_block_eq_detachSheet (shape : Shape profile) (label : Fin 2)
    (remainder : Fin degree) (hne : pinSheet profile label ≠ remainder)
    (hTogether : (data.vertexPartition wall).Rel (pinSheet profile label) remainder)
    (sheet : Fin degree) (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (data.edgePartition (star.edge label)).block sheet =
      ((data.vertexPartition wall).detachSheet (pinSheet profile label) remainder hne
        hTogether).block sheet := by
  classical
  have hWallPin : (data.vertexPartition wall).Rel (pinSheet profile label) sheet :=
    (pinSheet_rel label).symm.trans hSheet
  by_cases hPin : sheet = pinSheet profile label
  · subst hPin
    rw [pinSheet_block shape label,
      (data.vertexPartition wall).detachSheet_block_single (pinSheet profile label)
        remainder hne hTogether]
  · have hBulkRel : (data.edgePartition (star.edge label)).Rel
        (W2M1kStableGraph.bulkSheet profile label) sheet :=
      W2M1kStableGraph.edgePartition_rel_bulk shape label sheet hSheet hPin
    have hLHS : (data.edgePartition (star.edge label)).block sheet =
        (data.edgePartition (star.edge label)).block
          (W2M1kStableGraph.bulkSheet profile label) :=
      ((data.edgePartition (star.edge label)).block_eq_of_rel hBulkRel).symm
    have hReprSheet := (data.vertexPartition wall).detachSheet_repr_of_rel_of_ne
      (pinSheet profile label) remainder sheet hne hTogether hPin hWallPin
    have hReprRem := (data.vertexPartition wall).detachSheet_repr_of_rel_of_ne
      (pinSheet profile label) remainder remainder hne hTogether hne.symm hTogether
    have hRelRem : ((data.vertexPartition wall).detachSheet (pinSheet profile label)
        remainder hne hTogether).Rel sheet remainder := by
      rw [SheetPartition.rel_iff, hReprSheet, hReprRem]
    have hRHS : ((data.vertexPartition wall).detachSheet (pinSheet profile label)
          remainder hne hTogether).block sheet =
        ((data.vertexPartition wall).block (pinSheet profile label)).erase
          (pinSheet profile label) := by
      rw [((data.vertexPartition wall).detachSheet (pinSheet profile label) remainder hne
          hTogether).block_eq_of_rel hRelRem,
        (data.vertexPartition wall).detachSheet_block_remainder (pinSheet profile label)
          remainder hne hTogether]
    rw [hLHS, hRHS]
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro value hValue
      have hRel := ((data.edgePartition (star.edge label)).mem_block_iff _ value).mp hValue
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · intro hEq
        subst hEq
        exact W2M1kStableGraph.edgePartition_separate shape label hRel
      · refine ((data.vertexPartition wall).mem_block_iff _ value).mpr ?_
        exact ((pinSheet_rel label).symm.trans
          (W2M1kStableGraph.bulkSheet_rel label)).trans
          ((star.edgePartition_refines_wall data label).rel hRel)
    · have hCardErase : (((data.vertexPartition wall).block (pinSheet profile label)).erase
          (pinSheet profile label)).card = shape.k := by
        rw [Finset.card_erase_of_mem
          ((data.vertexPartition wall).self_mem_block (pinSheet profile label))]
        have := pinSheet_blockCard_wall shape label
        unfold SheetPartition.blockCard at this
        omega
      have hCardBulk : ((data.edgePartition (star.edge label)).block
          (W2M1kStableGraph.bulkSheet profile label)).card = shape.k :=
        bulkSheet_blockCard shape label
      omega

theorem pin_ne_bulk (shape : Shape profile) (label : Fin 2) :
    pinSheet profile label ≠ W2M1kStableGraph.bulkSheet profile label :=
  (W2M1kStableGraph.bulkSheet_ne_pinSheet shape label).symm

theorem pin_rel_bulk (label : Fin 2) :
    (data.vertexPartition wall).Rel (pinSheet profile label)
      (W2M1kStableGraph.bulkSheet profile label) :=
  (pinSheet_rel label).symm.trans (W2M1kStableGraph.bulkSheet_rel label)

end Directions

/-! ## §2  The incoming datum: the second flag, and the three counts

`W2M1kIncomingCensus.flagEdge` is the incoming occurrence above `star.edge 0`,
which meets `zeroEnd`; `coflagEdge` is its companion above `star.edge 1`, which
meets `oneEnd` at a `T_2` wall and, together with the flag, meets `branchEnd` at
a `T_∅` one. -/

section Coflag

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)

/-- The incoming occurrence above `star.edge 1`, the companion of
`W2M1kIncomingCensus.flagEdge`. -/
noncomputable def coflagEdge : target.edges := unfoldEdge hc hab hOne (star.edge 1)

theorem flagEdge_ne_coflagEdge :
    flagEdge hc hab hOne star ≠ coflagEdge hc hab hOne star := by
  intro h
  have hSub : (foldEdgeEquiv hc hab hOne).symm (star.edge 0) =
      (foldEdgeEquiv hc hab hOne).symm (star.edge 1) := Subtype.ext h
  exact (by decide : (0 : Fin 2) ≠ 1)
    (star.edge_injective ((foldEdgeEquiv hc hab hOne).symm.injective hSub))

/-- The `star.edge 1` occurrence meets the fresh restored endpoint. -/
theorem coflagEdge_mem_oneEnd
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    coflagEdge hc hab hOne star ∈
      GluingDatum.incidentEdges (oneEnd hc hab hOne star) := by
  have hNe := IncomingW2TargetPlacement.right_star_ne_of_divalent hc hab hOne star hLeft hRight
  rcases Bool.eq_false_or_eq_true
    (IncomingTargetExpansion.right hc hab hOne (star.edge 0)) with hTrue | hFalse
  · rw [oneEnd_of_true hc hab hOne star hTrue]
    have hOneFalse : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = false := by
      rcases Bool.eq_false_or_eq_true
        (IncomingTargetExpansion.right hc hab hOne (star.edge 1)) with h | h
      · exact absurd (hTrue.trans h.symm) hNe
      · exact h
    exact (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
      (star.edge_mem_incidentEdges 1)).mp hOneFalse
  · rw [oneEnd_of_false hc hab hOne star hFalse]
    have hOneTrue : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = true := by
      rcases Bool.eq_false_or_eq_true
        (IncomingTargetExpansion.right hc hab hOne (star.edge 1)) with h | h
      · exact h
      · exact absurd (hFalse.trans h.symm) hNe
    exact (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp hOneTrue

/-- Both restored wall directions meet the trivalent endpoint of a `T_∅`
wall. -/
theorem unfoldEdge_mem_branchEnd (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1) (label : Fin 2) :
    unfoldEdge hc hab hOne (star.edge label) ∈
      GluingDatum.incidentEdges (branchEnd hc hab hOne star) := by
  rcases hLeaf with hLeafLeft | hLeafRight
  · rw [branchEnd_of_true hc hab hOne star
      (IncomingW2TargetPlacement.right_star_of_leaf_left hc hab hOne star hLeafLeft 0)]
    exact (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp
      (IncomingW2TargetPlacement.right_star_of_leaf_left hc hab hOne star hLeafLeft label)
  · rw [branchEnd_of_false hc hab hOne star
      (IncomingW2TargetPlacement.right_star_of_leaf_right hc hab hOne star hLeafRight 0)]
    exact (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
      (star.edge_mem_incidentEdges label)).mp
      (IncomingW2TargetPlacement.right_star_of_leaf_right hc hab hOne star hLeafRight label)

end Coflag

section Counts

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  {block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (profile : W2R2SourceProfile.SourceProfile (contractDatum data hc hab hOne) star block)

/-- **Each restored wall direction induces two blocks above `A₀`.** -/
theorem direction_count (shape : Shape profile) (label : Fin 2) :
    (data.edgePartition (unfoldEdge hc hab hOne (star.edge label))).blockCountWithin
      (mergedPartition data a b) block.1 = 2 := by
  rw [← contractDatum_vertexPartition_merge data hc hab hOne]
  exact W2M1kStableGraph.edgePartition_blockCountWithin shape label block.1
    ((((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).rel_iff _ _).mpr rfl)

theorem flag_count (shape : Shape profile) :
    (data.edgePartition (flagEdge hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 = 2 :=
  direction_count data hc hab hOne profile shape 0

theorem coflag_count (shape : Shape profile) :
    (data.edgePartition (coflagEdge hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 = 2 :=
  direction_count data hc hab hOne profile shape 1

theorem zeroEnd_divalent
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    (GluingDatum.incidentEdges (zeroEnd hc hab hOne star)).card = 2 := by
  rcases ends_cases hc hab hOne star with ⟨hZero, _⟩ | ⟨hZero, _⟩
  · rw [hZero]; exact hLeft
  · rw [hZero]; exact hRight

theorem oneEnd_divalent
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    (GluingDatum.incidentEdges (oneEnd hc hab hOne star)).card = 2 := by
  rcases ends_cases hc hab hOne star with ⟨_, hOneE⟩ | ⟨_, hOneE⟩
  · rw [hOneE]; exact hRight
  · rw [hOneE]; exact hLeft

include fullDim hForest in
/-- **The three induced counts above `A₀` at a `T_2` M-1k wall.**  Base II.1 is
the first alternative and Base II.2.2 the second; nothing else solves the
system. -/
theorem selected_counts (shape : Shape profile)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (hChangeLeft : data.targetChange a = 1) (hChangeRight : data.targetChange b = 1) :
    ((data.vertexPartition (zeroEnd hc hab hOne star)).blockCountWithin
          (mergedPartition data a b) block.1 = 1 ∧
        (data.vertexPartition (oneEnd hc hab hOne star)).blockCountWithin
          (mergedPartition data a b) block.1 = 1 ∧
        (data.edgePartition contracted).blockCountWithin
          (mergedPartition data a b) block.1 = 1) ∨
      ((data.vertexPartition (zeroEnd hc hab hOne star)).blockCountWithin
          (mergedPartition data a b) block.1 = 2 ∧
        (data.vertexPartition (oneEnd hc hab hOne star)).blockCountWithin
          (mergedPartition data a b) block.1 = 2 ∧
        (data.edgePartition contracted).blockCountWithin
          (mergedPartition data a b) block.1 = 3) := by
  classical
  have hZeroEnd : zeroEnd hc hab hOne star = a ∨ zeroEnd hc hab hOne star = b := by
    rcases ends_cases hc hab hOne star with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hOneEndCases : oneEnd hc hab hOne star = a ∨ oneEnd hc hab hOne star = b := by
    rcases ends_cases hc hab hOne star with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inr h
    · exact Or.inl h
  have hRefinesZero := W2MkkSelectedCensus.restoredEnd_refines data _ hZeroEnd
  have hRefinesOne := W2MkkSelectedCensus.restoredEnd_refines data _ hOneEndCases
  have hForestCount : ((data.edgePartition contracted).blockCountWithin
        (mergedPartition data a b) block.1 : ℤ) + 1 =
      ((data.vertexPartition a).blockCountWithin (mergedPartition data a b) block.1 : ℤ) +
        ((data.vertexPartition b).blockCountWithin (mergedPartition data a b) block.1 : ℤ) :=
    contractionForest_count data hc hForest
      (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block)
  have hPair : ((data.edgePartition contracted).blockCountWithin
        (mergedPartition data a b) block.1 : ℤ) + 1 =
      ((data.vertexPartition (zeroEnd hc hab hOne star)).blockCountWithin
          (mergedPartition data a b) block.1 : ℤ) +
        ((data.vertexPartition (oneEnd hc hab hOne star)).blockCountWithin
          (mergedPartition data a b) block.1 : ℤ) := by
    rcases ends_cases hc hab hOne star with ⟨hZero, hOneE⟩ | ⟨hZero, hOneE⟩
    · rw [hZero, hOneE]; exact hForestCount
    · rw [hZero, hOneE]; linarith [hForestCount]
  have hChangeZero : data.targetChange (zeroEnd hc hab hOne star) = 1 := by
    rcases hZeroEnd with h | h
    · rw [h]; exact hChangeLeft
    · rw [h]; exact hChangeRight
  have hChangeOne : data.targetChange (oneEnd hc hab hOne star) = 1 := by
    rcases hOneEndCases with h | h
    · rw [h]; exact hChangeLeft
    · rw [h]; exact hChangeRight
  have hZeroSum : (∑ sourceBlock ∈ SheetPartition.blocksWithin
        (data.vertexPartition (zeroEnd hc hab hOne star)) (mergedPartition data a b)
        (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block),
      data.localRamification (zeroEnd hc hab hOne star) sourceBlock) =
      ((data.edgePartition contracted).blockCountWithin
          (mergedPartition data a b) block.1 : ℤ)
        + ((data.edgePartition (flagEdge hc hab hOne star)).blockCountWithin
            (mergedPartition data a b) block.1 : ℤ)
        - 2 * ((data.vertexPartition (zeroEnd hc hab hOne star)).blockCountWithin
            (mergedPartition data a b) block.1 : ℤ) :=
    W2MkkSelectedCensus.sum_localRamification_of_divalent data
    (zeroEnd hc hab hOne star) (flagEdge hc hab hOne star)
    (fun h ↦ unfoldEdge_ne_contracted hc hab hOne _ h.symm)
    (zeroEnd_divalent hc hab hOne hLeftCard hRightCard)
    (contracted_mem_zeroEnd hc hab hOne star)
    (flagEdge_mem_zeroEnd hc hab hOne star) hRefinesZero
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block)
  have hOneSum : (∑ sourceBlock ∈ SheetPartition.blocksWithin
        (data.vertexPartition (oneEnd hc hab hOne star)) (mergedPartition data a b)
        (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block),
      data.localRamification (oneEnd hc hab hOne star) sourceBlock) =
      ((data.edgePartition contracted).blockCountWithin
          (mergedPartition data a b) block.1 : ℤ)
        + ((data.edgePartition (coflagEdge hc hab hOne star)).blockCountWithin
            (mergedPartition data a b) block.1 : ℤ)
        - 2 * ((data.vertexPartition (oneEnd hc hab hOne star)).blockCountWithin
            (mergedPartition data a b) block.1 : ℤ) :=
    W2MkkSelectedCensus.sum_localRamification_of_divalent data
    (oneEnd hc hab hOne star) (coflagEdge hc hab hOne star)
    (fun h ↦ unfoldEdge_ne_contracted hc hab hOne _ h.symm)
    (oneEnd_divalent hc hab hOne hLeftCard hRightCard)
    (contracted_mem_oneEnd hc hab hOne star)
    (coflagEdge_mem_oneEnd hc hab hOne star hLeftCard hRightCard) hRefinesOne
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block)
  rw [flag_count data hc hab hOne profile shape] at hZeroSum
  rw [coflag_count data hc hab hOne profile shape] at hOneSum
  have hZeroBounds := W2MkkSelectedCensus.sum_localRamification_le_targetChange data fullDim
    (zeroEnd hc hab hOne star)
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block)
  have hOneBounds := W2MkkSelectedCensus.sum_localRamification_le_targetChange data fullDim
    (oneEnd hc hab hOne star)
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block)
  rw [hZeroSum, hChangeZero] at hZeroBounds
  rw [hOneSum, hChangeOne] at hOneBounds
  have hZeroLe : (data.vertexPartition (zeroEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 ≤ 2 := by
    have hMono : (data.vertexPartition (zeroEnd hc hab hOne star)).blockCountWithin
          (mergedPartition data a b) block.1 ≤
        (data.edgePartition (flagEdge hc hab hOne star)).blockCountWithin
          (mergedPartition data a b) block.1 :=
      W2MkkSelectedCensus.blockCountWithin_mono
        (data.edgePartition (flagEdge hc hab hOne star))
        (data.vertexPartition (zeroEnd hc hab hOne star)) (mergedPartition data a b)
        (refines_of_mem_incidentEdges data (flagEdge_mem_zeroEnd hc hab hOne star))
        hRefinesZero (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block)
    rw [flag_count data hc hab hOne profile shape] at hMono
    exact hMono
  have hZeroPos := SheetPartition.blockCountWithin_pos
    (data.vertexPartition (zeroEnd hc hab hOne star)) (mergedPartition data a b) block.1
  have hOnePos := SheetPartition.blockCountWithin_pos
    (data.vertexPartition (oneEnd hc hab hOne star)) (mergedPartition data a b) block.1
  have hContractedPos := SheetPartition.blockCountWithin_pos
    (data.edgePartition contracted) (mergedPartition data a b) block.1
  obtain ⟨hZeroNonneg, hZeroLeOne⟩ := hZeroBounds
  obtain ⟨hOneNonneg, hOneLeOne⟩ := hOneBounds
  rcases Nat.lt_or_ge ((data.vertexPartition (zeroEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1) 2 with hLt | hGe
  · left
    refine ⟨by omega, by omega, by omega⟩
  · right
    refine ⟨by omega, by omega, by omega⟩

/-! ## §3  From the counts to the partitions, at a `T_2` wall

Each count now forces a literal identity of blocks above `A₀`: `1 = 1` against
the merged partition itself in the joined branch, and `2 = 2`, `2 = 2`, `3 = 3`
against the two direction partitions and the doubly detached one in the divided
branch. -/

/-- The wall datum's partition at the merged vertex, abbreviated. -/
theorem wall_eq_merged :
    (contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩ = mergedPartition data a b :=
  contractDatum_vertexPartition_merge data hc hab hOne

/-- **Base II.1 on `A₀`.**  All three wall positions carry the whole
distinguished block. -/
theorem joinedCensus_of_counts
    (hZero : (data.vertexPartition (zeroEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 = 1)
    (hOneE : (data.vertexPartition (oneEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 = 1)
    (hNew : (data.edgePartition contracted).blockCountWithin
      (mergedPartition data a b) block.1 = 1) :
    W2M1kIncomingMatching.SelectedCensus data hc hab hOne block
      (zeroEnd hc hab hOne star) (oneEnd hc hab hOne star)
      (mergedPartition data a b) (mergedPartition data a b) (mergedPartition data a b) := by
  have hZeroEnd : zeroEnd hc hab hOne star = a ∨ zeroEnd hc hab hOne star = b := by
    rcases ends_cases hc hab hOne star with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hOneEndCases : oneEnd hc hab hOne star = a ∨ oneEnd hc hab hOne star = b := by
    rcases ends_cases hc hab hOne star with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inr h
    · exact Or.inl h
  refine ⟨?_, ?_, ?_⟩
  · intro sheet hSheet
    refine SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ _
      (W2MkkSelectedCensus.restoredEnd_refines data _ hZeroEnd) sheet ?_
    rw [← blockCountWithin_congr _ (mergedPartition data a b) hSheet]
    exact hZero
  · intro sheet hSheet
    refine SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ _
      (W2MkkSelectedCensus.restoredEnd_refines data _ hOneEndCases) sheet ?_
    rw [← blockCountWithin_congr _ (mergedPartition data a b) hSheet]
    exact hOneE
  · intro sheet hSheet
    refine SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ _
      (edgePartition_refines_mergedPartition data hc) sheet ?_
    rw [← blockCountWithin_congr _ (mergedPartition data a b) hSheet]
    exact hNew

/-- **Base II.2.2, the retained endpoint.**  With two induced blocks above `A₀`
it carries the `star.edge 0` occurrence partition there. -/
theorem zeroEnd_block_eq_flag (shape : Shape profile)
    (hZero : (data.vertexPartition (zeroEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 = 2)
    (sheet : Fin degree) (hSheet : (mergedPartition data a b).Rel block.1 sheet) :
    (data.vertexPartition (zeroEnd hc hab hOne star)).block sheet =
      (data.edgePartition (flagEdge hc hab hOne star)).block sheet := by
  have hZeroEnd : zeroEnd hc hab hOne star = a ∨ zeroEnd hc hab hOne star = b := by
    rcases ends_cases hc hab hOne star with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  refine (W2MkkSelectedCensus.block_eq_of_blockCountWithin_eq
    (data.edgePartition (flagEdge hc hab hOne star))
    (data.vertexPartition (zeroEnd hc hab hOne star)) (mergedPartition data a b)
    (refines_of_mem_incidentEdges data (flagEdge_mem_zeroEnd hc hab hOne star))
    (W2MkkSelectedCensus.restoredEnd_refines data _ hZeroEnd)
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block) ?_ sheet hSheet).symm
  show (data.edgePartition (flagEdge hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 =
    (data.vertexPartition (zeroEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1
  rw [flag_count data hc hab hOne profile shape, hZero]

/-- The mirror at the fresh endpoint. -/
theorem oneEnd_block_eq_coflag (shape : Shape profile)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (hOneE : (data.vertexPartition (oneEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 = 2)
    (sheet : Fin degree) (hSheet : (mergedPartition data a b).Rel block.1 sheet) :
    (data.vertexPartition (oneEnd hc hab hOne star)).block sheet =
      (data.edgePartition (coflagEdge hc hab hOne star)).block sheet := by
  have hOneEndCases : oneEnd hc hab hOne star = a ∨ oneEnd hc hab hOne star = b := by
    rcases ends_cases hc hab hOne star with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inr h
    · exact Or.inl h
  refine (W2MkkSelectedCensus.block_eq_of_blockCountWithin_eq
    (data.edgePartition (coflagEdge hc hab hOne star))
    (data.vertexPartition (oneEnd hc hab hOne star)) (mergedPartition data a b)
    (refines_of_mem_incidentEdges data
      (coflagEdge_mem_oneEnd hc hab hOne star hLeftCard hRightCard))
    (W2MkkSelectedCensus.restoredEnd_refines data _ hOneEndCases)
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne block) ?_ sheet hSheet).symm
  show (data.edgePartition (coflagEdge hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 =
    (data.vertexPartition (oneEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1
  rw [coflag_count data hc hab hOne profile shape, hOneE]

/-- The distinguished block, read in the merged partition. -/
theorem pin_merged_rel (label : Fin 2) :
    (mergedPartition data a b).Rel block.1 (pinSheet profile label) :=
  cast (merged_rel_eq data hc hab hOne block.1 (pinSheet profile label)) (pinSheet_rel label)

/-- **The retained endpoint isolates `star.edge 0`'s pinned sheet** in the
detaching branch. -/
theorem zeroEnd_block_pin (shape : Shape profile)
    (hZero : (data.vertexPartition (zeroEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 = 2) :
    (data.vertexPartition (zeroEnd hc hab hOne star)).block (pinSheet profile 0) =
      {pinSheet profile 0} := by
  rw [zeroEnd_block_eq_flag data hc hab hOne profile shape hZero (pinSheet profile 0)
    (pin_merged_rel data hc hab hOne profile 0)]
  exact pinSheet_block shape 0

/-- The mirror at the fresh endpoint. -/
theorem oneEnd_block_pin (shape : Shape profile)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (hOneE : (data.vertexPartition (oneEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 = 2) :
    (data.vertexPartition (oneEnd hc hab hOne star)).block (pinSheet profile 1) =
      {pinSheet profile 1} := by
  rw [oneEnd_block_eq_coflag data hc hab hOne profile shape hLeftCard hRightCard hOneE
    (pinSheet profile 1) (pin_merged_rel data hc hab hOne profile 1)]
  exact pinSheet_block shape 1

/-- **Aligned pins preclude Base II.2.2.**  If both restored endpoints detached
the *same* sheet, that sheet would already be a block of the merged partition,
while `A₀` has `k + 1 ≥ 3` sheets. -/
theorem not_detaching_of_aligned (shape : Shape profile)
    (hAligned : pinSheet profile 0 = pinSheet profile 1)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (hZero : (data.vertexPartition (zeroEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 = 2)
    (hOneE : (data.vertexPartition (oneEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 = 2) : False := by
  have hPinZero := zeroEnd_block_pin data hc hab hOne profile shape hZero
  have hPinOne := oneEnd_block_pin data hc hab hOne profile shape hLeftCard hRightCard hOneE
  rw [← hAligned] at hPinOne
  have hSing : (mergedPartition data a b).block (pinSheet profile 0) =
      {pinSheet profile 0} := by
    rcases ends_cases hc hab hOne star with ⟨hZ, hO⟩ | ⟨hZ, hO⟩
    · rw [hZ] at hPinZero
      rw [hO] at hPinOne
      exact join_block_eq_singleton _ _ _ hPinZero hPinOne
    · rw [hZ] at hPinZero
      rw [hO] at hPinOne
      exact join_block_eq_singleton _ _ _ hPinOne hPinZero
  have hCard : (mergedPartition data a b).blockCard (pinSheet profile 0) = shape.k + 1 := by
    rw [← wall_eq_merged data hc hab hOne]
    exact pinSheet_blockCard_wall shape 0
  unfold SheetPartition.blockCard at hCard
  rw [hSing, Finset.card_singleton] at hCard
  have := shape.one_lt_k
  omega

/-- The contracted occurrence isolates each pinned sheet in the detaching
branch. -/
theorem contracted_block_pin_zero (shape : Shape profile)
    (hZero : (data.vertexPartition (zeroEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 = 2) :
    (data.edgePartition contracted).block (pinSheet profile 0) = {pinSheet profile 0} := by
  classical
  have hSub : (data.edgePartition contracted).block (pinSheet profile 0) ⊆
      (data.vertexPartition (zeroEnd hc hab hOne star)).block (pinSheet profile 0) := by
    intro value hValue
    exact ((data.vertexPartition (zeroEnd hc hab hOne star)).mem_block_iff _ value).mpr
      ((refines_of_mem_incidentEdges data (contracted_mem_zeroEnd hc hab hOne star)).rel
        (((data.edgePartition contracted).mem_block_iff _ value).mp hValue))
  rw [zeroEnd_block_pin data hc hab hOne profile shape hZero] at hSub
  refine Finset.Subset.antisymm hSub ?_
  intro value hValue
  rw [Finset.mem_singleton] at hValue
  subst hValue
  exact (data.edgePartition contracted).self_mem_block _

theorem contracted_block_pin_one (shape : Shape profile)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (hOneE : (data.vertexPartition (oneEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 = 2) :
    (data.edgePartition contracted).block (pinSheet profile 1) = {pinSheet profile 1} := by
  classical
  have hSub : (data.edgePartition contracted).block (pinSheet profile 1) ⊆
      (data.vertexPartition (oneEnd hc hab hOne star)).block (pinSheet profile 1) := by
    intro value hValue
    exact ((data.vertexPartition (oneEnd hc hab hOne star)).mem_block_iff _ value).mpr
      ((refines_of_mem_incidentEdges data (contracted_mem_oneEnd hc hab hOne star)).rel
        (((data.edgePartition contracted).mem_block_iff _ value).mp hValue))
  rw [oneEnd_block_pin data hc hab hOne profile shape hLeftCard hRightCard hOneE] at hSub
  refine Finset.Subset.antisymm hSub ?_
  intro value hValue
  rw [Finset.mem_singleton] at hValue
  subst hValue
  exact (data.edgePartition contracted).self_mem_block _

/-- **Base II.2.2, the contracted occurrence.**  It detaches both pinned sheets
from `A₀`: Figure 33's `secondNewEdge`. -/
theorem contracted_block_eq_secondNewEdge (shape : Shape profile)
    (divided : DividedData profile)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (hZero : (data.vertexPartition (zeroEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 = 2)
    (hOneE : (data.vertexPartition (oneEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 = 2)
    (hNew : (data.edgePartition contracted).blockCountWithin
      (mergedPartition data a b) block.1 = 3)
    (sheet : Fin degree) (hSheet : (mergedPartition data a b).Rel block.1 sheet) :
    (data.edgePartition contracted).block sheet =
      (secondNewEdge ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
        (pinSheet profile 0) (pinSheet profile 1) divided.third
        (W2M1kStableGraph.pin_rel_pin profile 0 1) divided.rel_third divided.pins_ne
        divided.ne_first divided.ne_second).block sheet := by
  classical
  have hRefWall : (data.edgePartition contracted).Refines
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) := by
    rw [wall_eq_merged data hc hab hOne]
    exact edgePartition_refines_mergedPartition data hc
  have hRefOne : (data.edgePartition contracted).Refines
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet
        (pinSheet profile 0) (pinSheet profile 1) divided.pins_ne
        (W2M1kStableGraph.pin_rel_pin profile 0 1)) :=
    SheetPartition.refines_detachSheet_of_block_singleton _ _ _ _ _ _ hRefWall
      (contracted_block_pin_zero data hc hab hOne profile shape hZero)
  have hRefTwo : (data.edgePartition contracted).Refines
      (secondNewEdge ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
        (pinSheet profile 0) (pinSheet profile 1) divided.third
        (W2M1kStableGraph.pin_rel_pin profile 0 1) divided.rel_third divided.pins_ne
        divided.ne_first divided.ne_second) :=
    SheetPartition.refines_detachSheet_of_block_singleton _ _ _ _ _ _ hRefOne
      (contracted_block_pin_one data hc hab hOne profile shape hLeftCard hRightCard hOneE)
  have hSheetWall : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
      block.1 sheet := W2M1kIncomingMatching.on_wall_of_on_merged data hc hab hOne hSheet
  refine W2MkkSelectedCensus.block_eq_of_blockCountWithin_eq (data.edgePartition contracted)
    (secondNewEdge ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
      (pinSheet profile 0) (pinSheet profile 1) divided.third
      (W2M1kStableGraph.pin_rel_pin profile 0 1) divided.rel_third divided.pins_ne
      divided.ne_first divided.ne_second)
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) hRefTwo
    (secondNewEdge_refines_wall _ _ _ _ _ _ _ _ _) block ?_ sheet hSheetWall
  have hConv : (data.edgePartition contracted).blockCountWithin
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) block.1 =
      (data.edgePartition contracted).blockCountWithin (mergedPartition data a b) block.1 :=
    congrArg (fun partition : SheetPartition degree ↦
      (data.edgePartition contracted).blockCountWithin partition block.1)
      (wall_eq_merged data hc hab hOne)
  rw [hConv, hNew, secondNewEdge_blockCountWithin
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) (pinSheet profile 0)
    (pinSheet profile 1) divided.third block.1 (W2M1kStableGraph.pin_rel_pin profile 0 1)
    divided.rel_third divided.pins_ne divided.ne_first divided.ne_second
    (pinSheet_rel 0).symm]

/-- **Base II.2.2 on `A₀` (in Part I's vocabulary), assembled.**  Each restored endpoint
detaches its own direction's pinned sheet and the contracted occurrence detaches
both. -/
theorem dividedCensus_of_counts (shape : Shape profile) (divided : DividedData profile)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    (hZero : (data.vertexPartition (zeroEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 = 2)
    (hOneE : (data.vertexPartition (oneEnd hc hab hOne star)).blockCountWithin
      (mergedPartition data a b) block.1 = 2)
    (hNew : (data.edgePartition contracted).blockCountWithin
      (mergedPartition data a b) block.1 = 3) :
    W2M1kIncomingMatching.SelectedCensus data hc hab hOne block
      (zeroEnd hc hab hOne star) (oneEnd hc hab hOne star)
      (W2M1kIncomingMatching.dividedSelected divided).left
      (W2M1kIncomingMatching.dividedSelected divided).right
      (W2M1kIncomingMatching.dividedSelected divided).newEdge := by
  refine ⟨?_, ?_, ?_⟩
  · intro sheet hSheet
    exact (zeroEnd_block_eq_flag data hc hab hOne profile shape hZero sheet hSheet).trans
      (direction_block_eq_detachSheet shape 0 (pinSheet profile 1) divided.pins_ne
        (W2M1kStableGraph.pin_rel_pin profile 0 1) sheet
        (W2M1kIncomingMatching.on_wall_of_on_merged data hc hab hOne hSheet))
  · intro sheet hSheet
    exact (oneEnd_block_eq_coflag data hc hab hOne profile shape hLeftCard hRightCard hOneE
      sheet hSheet).trans
      (direction_block_eq_detachSheet shape 1 (pinSheet profile 0) divided.pins_ne.symm
        (W2M1kStableGraph.pin_rel_pin profile 1 0) sheet
        (W2M1kIncomingMatching.on_wall_of_on_merged data hc hab hOne hSheet))
  · intro sheet hSheet
    exact contracted_block_eq_secondNewEdge data hc hab hOne profile shape divided
      hLeftCard hRightCard hZero hOneE hNew sheet hSheet

include fullDim hc in
/-- At two divalent restored endpoints the change is one at each. -/
theorem divalent_changes (twoStar : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2) :
    data.targetChange a = 1 ∧ data.targetChange b = 1 := by
  rcases valencySplit_of_twoStar data hc hab hOne fullDim.valid fullDim.changeMinimal
    twoStar with
    ⟨_, _, hChangeLeft, hChangeRight⟩ | ⟨hLeafLeft, _, _, _⟩ | ⟨_, hLeafRight, _, _⟩
  · exact ⟨hChangeLeft, hChangeRight⟩
  · exact absurd (hLeafLeft.symm.trans hLeftCard) (by decide)
  · exact absurd (hLeafRight.symm.trans hRightCard) (by decide)

/-! ## §4  The `T_∅` wall: Figure 33's `M⁽¹⁾`

Base I.a.  The leaf carries the whole two units of change and the trivalent
endpoint none, and the contracted occurrence is discrete; the census follows
without any count above `A₀` at all, block by block. -/

/-- The leaf endpoint's star is the contracted occurrence alone. -/
theorem leaf_incidentEdges (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
    (GluingDatum.incidentEdges b).card = 1) :
    GluingDatum.incidentEdges (leafEnd hc hab hOne star) = {contracted} :=
  W2MkkSelectedCensus.incidentEdges_eq_singleton (leafEnd hc hab hOne star)
    (contracted_mem_leafEnd hc hab hOne star) (leafEnd_card_one hc hab hOne star hLeaf)

include fullDim hc in
/-- A change-minimal leaf makes the contracted occurrence partition discrete. -/
theorem contracted_discrete (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
    (GluingDatum.incidentEdges b).card = 1) (sheet : Fin degree) :
    (data.edgePartition contracted).repr sheet = sheet := by
  rcases hLeaf with hLeafLeft | hLeafRight
  · exact W2MkkSelectedCensus.discrete_of_leaf data fullDim a
      (contracted_mem_incidentEdges_left hc) hLeafLeft sheet
  · exact W2MkkSelectedCensus.discrete_of_leaf data fullDim b
      (contracted_mem_incidentEdges_right hc) hLeafRight sheet

include fullDim in
/-- The `T_∅` valencies and changes, read at `leafEnd` and `branchEnd`. -/
theorem leaf_valencies (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
    (GluingDatum.incidentEdges b).card = 1) :
    (GluingDatum.incidentEdges (branchEnd hc hab hOne star)).card = 3 ∧
      data.targetChange (branchEnd hc hab hOne star) = 0 ∧
      data.targetChange (leafEnd hc hab hOne star) = 2 := by
  have hCardLeaf := leafEnd_card_one hc hab hOne star hLeaf
  rcases leaf_ends_cases hc hab hOne star with ⟨hL, hB⟩ | ⟨hL, hB⟩
  · rw [hL] at hCardLeaf
    rw [hB, hL]
    rcases valencySplit_of_twoStar data hc hab hOne fullDim.valid fullDim.changeMinimal star with
      ⟨h1, _, _, _⟩ | ⟨_, h2, h3, h4⟩ | ⟨h1, _, _, _⟩
    · omega
    · exact ⟨h2, h4, h3⟩
    · omega
  · rw [hL] at hCardLeaf
    rw [hB, hL]
    rcases valencySplit_of_twoStar data hc hab hOne fullDim.valid fullDim.changeMinimal star with
      ⟨_, h1, _, _⟩ | ⟨_, h1, _, _⟩ | ⟨h2, _, h3, h4⟩
    · omega
    · omega
    · exact ⟨h2, h3, h4⟩

include fullDim in
/-- The trivalent endpoint's star is the contracted occurrence and the two
restored wall directions. -/
theorem branch_incidentEdges (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
    (GluingDatum.incidentEdges b).card = 1) :
    GluingDatum.incidentEdges (branchEnd hc hab hOne star) =
      {contracted, flagEdge hc hab hOne star, coflagEdge hc hab hOne star} := by
  classical
  have hContractedFlag : contracted ≠ flagEdge hc hab hOne star :=
    fun h ↦ unfoldEdge_ne_contracted hc hab hOne _ h.symm
  have hContractedCoflag : contracted ≠ coflagEdge hc hab hOne star :=
    fun h ↦ unfoldEdge_ne_contracted hc hab hOne _ h.symm
  have hNotMemFirst : contracted ∉
      ({flagEdge hc hab hOne star, coflagEdge hc hab hOne star} : Finset target.edges) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hContractedFlag h
    · exact hContractedCoflag h
  have hNotMemSecond : flagEdge hc hab hOne star ∉
      ({coflagEdge hc hab hOne star} : Finset target.edges) := by
    simp only [Finset.mem_singleton]
    exact flagEdge_ne_coflagEdge hc hab hOne star
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · exact contracted_mem_branchEnd hc hab hOne star
    · rcases Finset.mem_insert.mp hEdge with rfl | hEdge
      · exact unfoldEdge_mem_branchEnd hc hab hOne star hLeaf 0
      · rw [Finset.mem_singleton.mp hEdge]
        exact unfoldEdge_mem_branchEnd hc hab hOne star hLeaf 1
  · rw [(leaf_valencies data hc hab hOne fullDim hLeaf).1,
      Finset.card_insert_of_notMem hNotMemFirst,
      Finset.card_insert_of_notMem hNotMemSecond, Finset.card_singleton]

include fullDim in
/-- At the trivalent endpoint of a `T_∅` wall every local ramification
vanishes. -/
theorem branch_localRamification_zero (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1)
    (endpointBlock : (data.vertexPartition (branchEnd hc hab hOne star)).Blocks) :
    data.localRamification (branchEnd hc hab hOne star) endpointBlock = 0 := by
  classical
  have hSum : ∑ other : (data.vertexPartition (branchEnd hc hab hOne star)).Blocks,
      data.localRamification (branchEnd hc hab hOne star) other = 0 :=
    (leaf_valencies data hc hab hOne fullDim hLeaf).2.1
  have hNonneg : ∀ other ∈ (Finset.univ :
      Finset (data.vertexPartition (branchEnd hc hab hOne star)).Blocks),
      0 ≤ data.localRamification (branchEnd hc hab hOne star) other :=
    fun other _ ↦ data.localRamification_nonneg _ (fullDim.valid.2 _) other
  exact (Finset.sum_eq_zero_iff_of_nonneg hNonneg).mp hSum endpointBlock (Finset.mem_univ _)

include fullDim in
/-- **Both restored directions agree with the trivalent endpoint everywhere.**
The contracted occurrence is discrete there, so Riemann--Hurwitz leaves exactly
one block of each direction inside each endpoint block. -/
theorem branch_direction_counts (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1) (sheet : Fin degree) :
    (data.edgePartition (flagEdge hc hab hOne star)).blockCountWithin
        (data.vertexPartition (branchEnd hc hab hOne star)) sheet = 1 ∧
      (data.edgePartition (coflagEdge hc hab hOne star)).blockCountWithin
        (data.vertexPartition (branchEnd hc hab hOne star)) sheet = 1 := by
  classical
  have hContractedFlag : contracted ≠ flagEdge hc hab hOne star :=
    fun h ↦ unfoldEdge_ne_contracted hc hab hOne _ h.symm
  have hContractedCoflag : contracted ≠ coflagEdge hc hab hOne star :=
    fun h ↦ unfoldEdge_ne_contracted hc hab hOne _ h.symm
  have hNotMemFirst : contracted ∉
      ({flagEdge hc hab hOne star, coflagEdge hc hab hOne star} : Finset target.edges) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hContractedFlag h
    · exact hContractedCoflag h
  have hNotMemSecond : flagEdge hc hab hOne star ∉
      ({coflagEdge hc hab hOne star} : Finset target.edges) := by
    simp only [Finset.mem_singleton]
    exact flagEdge_ne_coflagEdge hc hab hOne star
  have hRam := branch_localRamification_zero data hc hab hOne fullDim hLeaf
    ((data.vertexPartition (branchEnd hc hab hOne star)).toBlock sheet)
  unfold GluingDatum.localRamification at hRam
  rw [branch_incidentEdges data hc hab hOne fullDim hLeaf, Finset.sum_insert hNotMemFirst,
    Finset.sum_insert hNotMemSecond, Finset.sum_singleton,
    Finset.card_insert_of_notMem hNotMemFirst, Finset.card_insert_of_notMem hNotMemSecond,
    Finset.card_singleton, SheetPartition.toBlock_val] at hRam
  have hReprRel : (data.vertexPartition (branchEnd hc hab hOne star)).Rel
      ((data.vertexPartition (branchEnd hc hab hOne star)).repr sheet) sheet :=
    (data.vertexPartition (branchEnd hc hab hOne star)).rel_repr_left sheet
  rw [blockCountWithin_congr (data.edgePartition contracted)
      (data.vertexPartition (branchEnd hc hab hOne star)) hReprRel,
    blockCountWithin_congr (data.edgePartition (flagEdge hc hab hOne star))
      (data.vertexPartition (branchEnd hc hab hOne star)) hReprRel,
    blockCountWithin_congr (data.edgePartition (coflagEdge hc hab hOne star))
      (data.vertexPartition (branchEnd hc hab hOne star)) hReprRel,
    blockCard_congr (data.vertexPartition (branchEnd hc hab hOne star)) hReprRel,
    W2MkkSelectedCensus.blockCountWithin_of_discrete
      (contracted_discrete data hc fullDim hLeaf)] at hRam
  have hFlagPos := SheetPartition.blockCountWithin_pos
    (data.edgePartition (flagEdge hc hab hOne star))
    (data.vertexPartition (branchEnd hc hab hOne star)) sheet
  have hCoflagPos := SheetPartition.blockCountWithin_pos
    (data.edgePartition (coflagEdge hc hab hOne star))
    (data.vertexPartition (branchEnd hc hab hOne star)) sheet
  push_cast at hRam
  constructor <;> omega

include fullDim in
/-- The `star.edge 0` occurrence and the trivalent endpoint agree everywhere. -/
theorem branch_block_eq_flag (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1) (sheet : Fin degree) :
    (data.vertexPartition (branchEnd hc hab hOne star)).block sheet =
      (data.edgePartition (flagEdge hc hab hOne star)).block sheet :=
  (SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one
    (data.edgePartition (flagEdge hc hab hOne star))
    (data.vertexPartition (branchEnd hc hab hOne star))
    (refines_of_mem_incidentEdges data (unfoldEdge_mem_branchEnd hc hab hOne star hLeaf 0))
    sheet (branch_direction_counts data hc hab hOne fullDim hLeaf sheet).1).symm

include fullDim in
/-- The mirror for `star.edge 1`. -/
theorem branch_block_eq_coflag (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1) (sheet : Fin degree) :
    (data.vertexPartition (branchEnd hc hab hOne star)).block sheet =
      (data.edgePartition (coflagEdge hc hab hOne star)).block sheet :=
  (SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one
    (data.edgePartition (coflagEdge hc hab hOne star))
    (data.vertexPartition (branchEnd hc hab hOne star))
    (refines_of_mem_incidentEdges data (unfoldEdge_mem_branchEnd hc hab hOne star hLeaf 1))
    sheet (branch_direction_counts data hc hab hOne fullDim hLeaf sheet).2).symm

include fullDim in
/-- **Base I.a is aligned, derived.**  At a `T_∅` wall both wall directions
carry the trivalent endpoint's own partition, so each isolates the other's
pinned sheet; only the aligned datum can do that. -/
theorem aligned_of_leaf (shape : Shape profile)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1) :
    pinSheet profile 0 = pinSheet profile 1 := by
  by_contra hNe
  have hBranchPin : (data.vertexPartition (branchEnd hc hab hOne star)).block
      (pinSheet profile 1) = {pinSheet profile 1} :=
    (branch_block_eq_coflag data hc hab hOne fullDim hLeaf (pinSheet profile 1)).trans
      (pinSheet_block shape 1)
  have hFlagPin : ((contractDatum data hc hab hOne).edgePartition (star.edge 0)).block
      (pinSheet profile 1) = {pinSheet profile 1} :=
    (branch_block_eq_flag data hc hab hOne fullDim hLeaf (pinSheet profile 1)).symm.trans
      hBranchPin
  have hRelBulk := W2M1kStableGraph.edgePartition_rel_bulk shape 0 (pinSheet profile 1)
    (pinSheet_rel 1) (fun h ↦ hNe h.symm)
  have hCardEq : ((contractDatum data hc hab hOne).edgePartition (star.edge 0)).blockCard
      (W2M1kStableGraph.bulkSheet profile 0) =
      ((contractDatum data hc hab hOne).edgePartition (star.edge 0)).blockCard
        (pinSheet profile 1) := SheetPartition.blockCard_congr _ hRelBulk
  rw [bulkSheet_blockCard shape 0] at hCardEq
  unfold SheetPartition.blockCard at hCardEq
  rw [hFlagPin, Finset.card_singleton] at hCardEq
  have := shape.one_lt_k
  omega

include fullDim in
/-- **Riemann--Hurwitz at a change-minimal leaf.**  The contracted occurrence is
discrete there, so every block contributes `2|B| - 2`. -/
theorem leaf_localRamification (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1)
    (endpointBlock : (data.vertexPartition (leafEnd hc hab hOne star)).Blocks) :
    data.localRamification (leafEnd hc hab hOne star) endpointBlock =
      2 * ((data.vertexPartition (leafEnd hc hab hOne star)).blockCard
        endpointBlock.1 : ℤ) - 2 := by
  unfold GluingDatum.localRamification
  rw [leaf_incidentEdges hc hab hOne (star := star) hLeaf, Finset.sum_singleton,
    Finset.card_singleton,
    W2MkkSelectedCensus.blockCountWithin_of_discrete
      (contracted_discrete data hc fullDim hLeaf)]
  push_cast
  ring

include fullDim in
/-- A leaf block has at most two sheets: `2|B| - 2 ≤ ch(u) = 2`. -/
theorem leaf_blockCard_le_two (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1)
    (endpointBlock : (data.vertexPartition (leafEnd hc hab hOne star)).Blocks) :
    (data.vertexPartition (leafEnd hc hab hOne star)).blockCard endpointBlock.1 ≤ 2 := by
  classical
  have hNonneg : ∀ other ∈ (Finset.univ :
      Finset (data.vertexPartition (leafEnd hc hab hOne star)).Blocks),
      0 ≤ data.localRamification (leafEnd hc hab hOne star) other :=
    fun other _ ↦ data.localRamification_nonneg _ (fullDim.valid.2 _) other
  have hLe : data.localRamification (leafEnd hc hab hOne star) endpointBlock ≤
      data.targetChange (leafEnd hc hab hOne star) :=
    Finset.single_le_sum hNonneg (Finset.mem_univ _)
  rw [leaf_localRamification data hc hab hOne fullDim hLeaf endpointBlock,
    (leaf_valencies data hc hab hOne fullDim hLeaf).2.2] at hLe
  omega

include fullDim in
/-- Once one leaf block carries the whole change, every other is a singleton. -/
theorem leaf_blockCard_eq_one_of_ne (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1)
    (first second : (data.vertexPartition (leafEnd hc hab hOne star)).Blocks)
    (hFirst : (data.vertexPartition (leafEnd hc hab hOne star)).blockCard first.1 = 2)
    (hNe : second ≠ first) :
    (data.vertexPartition (leafEnd hc hab hOne star)).blockCard second.1 = 1 := by
  classical
  have hNonneg : ∀ other ∈ (Finset.univ :
      Finset (data.vertexPartition (leafEnd hc hab hOne star)).Blocks),
      0 ≤ data.localRamification (leafEnd hc hab hOne star) other :=
    fun other _ ↦ data.localRamification_nonneg _ (fullDim.valid.2 _) other
  have hSum : ∑ other ∈ ({first, second} :
        Finset (data.vertexPartition (leafEnd hc hab hOne star)).Blocks),
      data.localRamification (leafEnd hc hab hOne star) other ≤
      data.targetChange (leafEnd hc hab hOne star) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun other _ _ ↦ hNonneg other (Finset.mem_univ _))
  rw [Finset.sum_pair (Ne.symm hNe),
    leaf_localRamification data hc hab hOne fullDim hLeaf first,
    leaf_localRamification data hc hab hOne fullDim hLeaf second, hFirst,
    (leaf_valencies data hc hab hOne fullDim hLeaf).2.2] at hSum
  have hPos := (data.vertexPartition (leafEnd hc hab hOne star)).blockCard_pos second.1
  omega

include fullDim in
/-- **The leaf's retained pair contains the pinned sheet.**  Its block has at
most two sheets by Riemann--Hurwitz, and at least two because otherwise the
pinned sheet would be isolated at both restored endpoints, hence in the merged
partition, while `A₀` has `k + 1 ≥ 3` sheets. -/
theorem leaf_pin_blockCard (shape : Shape profile)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1) :
    (data.vertexPartition (leafEnd hc hab hOne star)).blockCard (pinSheet profile 0) = 2 := by
  classical
  have hUpper : (data.vertexPartition (leafEnd hc hab hOne star)).blockCard
      (pinSheet profile 0) ≤ 2 := by
    have h := leaf_blockCard_le_two data hc hab hOne fullDim hLeaf
      ((data.vertexPartition (leafEnd hc hab hOne star)).toBlock (pinSheet profile 0))
    rwa [SheetPartition.toBlock_val, SheetPartition.blockCard_congr _
      ((data.vertexPartition (leafEnd hc hab hOne star)).rel_repr_left
        (pinSheet profile 0))] at h
  have hLower : 2 ≤ (data.vertexPartition (leafEnd hc hab hOne star)).blockCard
      (pinSheet profile 0) := by
    by_contra hSmall
    have hPos := (data.vertexPartition (leafEnd hc hab hOne star)).blockCard_pos
      (pinSheet profile 0)
    have hOneCard : (data.vertexPartition (leafEnd hc hab hOne star)).blockCard
        (pinSheet profile 0) = 1 := by omega
    have hLeafSing : (data.vertexPartition (leafEnd hc hab hOne star)).block
        (pinSheet profile 0) = {pinSheet profile 0} :=
      SheetPartition.block_eq_singleton_of_blockCard_eq_one _ _ hOneCard
    have hBranchSing : (data.vertexPartition (branchEnd hc hab hOne star)).block
        (pinSheet profile 0) = {pinSheet profile 0} :=
      (branch_block_eq_flag data hc hab hOne fullDim hLeaf (pinSheet profile 0)).trans
        (pinSheet_block shape 0)
    have hSing : (mergedPartition data a b).block (pinSheet profile 0) =
        {pinSheet profile 0} := by
      rcases leaf_ends_cases hc hab hOne star with ⟨hL, hB⟩ | ⟨hL, hB⟩
      · rw [hL] at hLeafSing
        rw [hB] at hBranchSing
        exact join_block_eq_singleton _ _ _ hLeafSing hBranchSing
      · rw [hL] at hLeafSing
        rw [hB] at hBranchSing
        exact join_block_eq_singleton _ _ _ hBranchSing hLeafSing
    have hCard : (mergedPartition data a b).blockCard (pinSheet profile 0) = shape.k + 1 := by
      rw [← wall_eq_merged data hc hab hOne]
      exact pinSheet_blockCard_wall shape 0
    unfold SheetPartition.blockCard at hCard
    rw [hSing, Finset.card_singleton] at hCard
    have := shape.one_lt_k
    omega
  omega

include fullDim in
/-- **The selected-class census at a `T_∅` wall: Base I.a.**  An arbitrary
full-dimensional incoming cover whose contracted wall carries a `w2M1k` profile
and whose restored contracted edge has a leaf endpoint *is* Figure 33's `M⁽¹⁾`
on the distinguished block, for a leaf pair this theorem produces. -/
theorem exists_selectedCensus_leaf (shape : Shape profile)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1) :
    ∃ pair : LeafPair profile,
      W2M1kIncomingMatching.SelectedCensus data hc hab hOne block
        (leafEnd hc hab hOne star) (branchEnd hc hab hOne star)
        (W2M1kIncomingMatching.leafSelected pair).left
        (W2M1kIncomingMatching.leafSelected pair).right
        (W2M1kIncomingMatching.leafSelected pair).newEdge := by
  classical
  have hPinCard := leaf_pin_blockCard data hc hab hOne fullDim profile shape hLeaf
  obtain ⟨second, hRelSecond, hNeSecond⟩ :=
    (data.vertexPartition (leafEnd hc hab hOne star)).exists_other_of_one_lt_blockCard
      (pinSheet profile 0) (by omega)
  have hPairBlock : (data.vertexPartition (leafEnd hc hab hOne star)).block
      (pinSheet profile 0) = {pinSheet profile 0, second} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro value hValue
      rcases Finset.mem_insert.mp hValue with rfl | hValue
      · exact (data.vertexPartition (leafEnd hc hab hOne star)).self_mem_block _
      · rw [Finset.mem_singleton.mp hValue]
        exact ((data.vertexPartition (leafEnd hc hab hOne star)).mem_block_iff _ _).mpr hRelSecond
    · have hCard : ((data.vertexPartition (leafEnd hc hab hOne star)).block
          (pinSheet profile 0)).card = 2 := hPinCard
      rw [Finset.card_insert_of_notMem (by simpa using hNeSecond), Finset.card_singleton]
      omega
  have hLeafEnds : leafEnd hc hab hOne star = a ∨ leafEnd hc hab hOne star = b := by
    rcases leaf_ends_cases hc hab hOne star with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hWallSecond : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
      (pinSheet profile 0) second :=
    cast (merged_rel_eq data hc hab hOne (pinSheet profile 0) second).symm
      ((W2MkkSelectedCensus.restoredEnd_refines data _ hLeafEnds).rel hRelSecond)
  obtain ⟨third, hRelThird, hNeThird, hSecondThird⟩ :=
    SheetPartition.exists_third_of_blockCard_eq_add_one
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) (pinSheet profile 0) second
      hNeSecond hWallSecond shape.k shape.one_lt_k (pinSheet_blockCard_wall shape 0)
  refine ⟨⟨aligned_of_leaf data hc hab hOne fullDim profile shape hLeaf, second, third,
    hWallSecond, hRelThird, hNeSecond, hNeThird, hSecondThird⟩, ?_, ?_, ?_⟩
  · intro sheet hSheet
    have hWallSheet : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
        block.1 sheet := W2M1kIncomingMatching.on_wall_of_on_merged data hc hab hOne hSheet
    have hPinSheet : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
        (pinSheet profile 0) sheet := (pinSheet_rel 0).symm.trans hWallSheet
    by_cases hIsPin : sheet = pinSheet profile 0
    · subst hIsPin
      rw [hPairBlock]
      exact (SheetPartition.pairBlock_block_first _ _ _ hNeSecond hWallSecond).symm
    · by_cases hIsSecond : sheet = second
      · have hRelPair : (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).pairBlock
            (pinSheet profile 0) second hNeSecond).Rel (pinSheet profile 0) second :=
          (SheetPartition.pairBlock_rel_first_iff _ _ _ _ hNeSecond hWallSecond).mpr
            (Or.inr rfl)
        have hLeft : (data.vertexPartition (leafEnd hc hab hOne star)).block second =
            {pinSheet profile 0, second} :=
          (((data.vertexPartition (leafEnd hc hab hOne star)).block_eq_of_rel
            hRelSecond).symm).trans hPairBlock
        have hRight : (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).pairBlock
            (pinSheet profile 0) second hNeSecond).block second =
            {pinSheet profile 0, second} :=
          (SheetPartition.block_eq_of_rel _ hRelPair).symm.trans
            (SheetPartition.pairBlock_block_first _ _ _ hNeSecond hWallSecond)
        rw [hIsSecond, hLeft]
        exact hRight.symm
      · have hNotRel : ¬ (data.vertexPartition (leafEnd hc hab hOne star)).Rel
            (pinSheet profile 0) sheet := by
          intro hRel
          have hMem := ((data.vertexPartition (leafEnd hc hab hOne star)).mem_block_iff
            (pinSheet profile 0) sheet).mpr hRel
          rw [hPairBlock] at hMem
          rcases Finset.mem_insert.mp hMem with h | h
          · exact hIsPin h
          · exact hIsSecond (Finset.mem_singleton.mp h)
        have hBlockNe : (data.vertexPartition (leafEnd hc hab hOne star)).toBlock sheet ≠
            (data.vertexPartition (leafEnd hc hab hOne star)).toBlock (pinSheet profile 0) :=
          fun hEq ↦ hNotRel (congrArg Subtype.val hEq).symm
        have hPinBlockCard : (data.vertexPartition (leafEnd hc hab hOne star)).blockCard
            ((data.vertexPartition (leafEnd hc hab hOne star)).toBlock
              (pinSheet profile 0)).1 = 2 := by
          rw [SheetPartition.toBlock_val, SheetPartition.blockCard_congr _
            ((data.vertexPartition (leafEnd hc hab hOne star)).rel_repr_left
              (pinSheet profile 0))]
          exact hPinCard
        have hSingle := leaf_blockCard_eq_one_of_ne data hc hab hOne fullDim hLeaf _ _
          hPinBlockCard hBlockNe
        rw [SheetPartition.toBlock_val, SheetPartition.blockCard_congr _
          ((data.vertexPartition (leafEnd hc hab hOne star)).rel_repr_left sheet)] at hSingle
        rw [SheetPartition.block_eq_singleton_of_blockCard_eq_one _ _ hSingle]
        exact (pairBlock_block_of_rel_of_ne _ _ _ _ hNeSecond hPinSheet hIsPin hIsSecond).symm
  · intro sheet hSheet
    exact (branch_block_eq_flag data hc hab hOne fullDim hLeaf sheet).trans
      (direction_block_eq_detachSheet shape 0 second hNeSecond hWallSecond sheet
        (W2M1kIncomingMatching.on_wall_of_on_merged data hc hab hOne hSheet))
  · intro sheet hSheet
    have hWallSheet : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
        block.1 sheet := W2M1kIncomingMatching.on_wall_of_on_merged data hc hab hOne hSheet
    have hPinSheet : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
        (pinSheet profile 0) sheet := (pinSheet_rel 0).symm.trans hWallSheet
    have hDiscBlock : (data.edgePartition contracted).block sheet = {sheet} := by
      ext value
      rw [SheetPartition.mem_block_iff, Finset.mem_singleton, SheetPartition.rel_iff,
        contracted_discrete data hc fullDim hLeaf sheet,
        contracted_discrete data hc fullDim hLeaf value]
      exact eq_comm
    rw [hDiscBlock]
    exact (SheetPartition.splitBlock_block_of_rel _ _ _ hPinSheet).symm

include fullDim in
/-- **A `T_∅` wall is never separated.**  `DividedData` asks the two pinned
sheets to differ; `aligned_of_leaf` says they do not. -/
theorem not_dividedData_of_leaf (shape : Shape profile)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1)
    (divided : DividedData profile) : False :=
  divided.pins_ne (aligned_of_leaf data hc hab hOne fullDim profile shape hLeaf)

include fullDim hForest in
/-- **The selected-class census at a separated `T_2` wall: Part I's Base II
dichotomy.**  An
arbitrary full-dimensional incoming cover whose contracted wall carries a
`w2M1k` profile with *distinct* pinned sheets satisfies Base II.2.2 -- Figure
33's `M⁽²⁾` -- or Base II.1 -- Figure 33's `M⁽³⁾` -- on the distinguished
block. -/
theorem selectedCensus_dichotomy_of_dividedData (shape : Shape profile)
    (divided : DividedData profile)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2) :
    W2M1kIncomingMatching.SelectedCensus data hc hab hOne block
        (zeroEnd hc hab hOne star) (oneEnd hc hab hOne star)
        (W2M1kIncomingMatching.dividedSelected divided).left
        (W2M1kIncomingMatching.dividedSelected divided).right
        (W2M1kIncomingMatching.dividedSelected divided).newEdge ∨
      W2M1kIncomingMatching.SelectedCensus data hc hab hOne block
        (zeroEnd hc hab hOne star) (oneEnd hc hab hOne star)
        (mergedPartition data a b) (mergedPartition data a b) (mergedPartition data a b) := by
  obtain ⟨hChangeLeft, hChangeRight⟩ :=
    divalent_changes data hc hab hOne fullDim star hLeftCard hRightCard
  rcases selected_counts data hc hab hOne fullDim hForest profile shape hLeftCard hRightCard
    hChangeLeft hChangeRight with ⟨hZero, hOneE, hNew⟩ | ⟨hZero, hOneE, hNew⟩
  · exact Or.inr (joinedCensus_of_counts data hc hab hOne hZero hOneE hNew)
  · exact Or.inl (dividedCensus_of_counts data hc hab hOne profile shape divided
      hLeftCard hRightCard hZero hOneE hNew)

include fullDim hForest in
/-- **The selected-class census at an aligned `T_2` wall.**  When the two pinned sheets
agree, Base II.2.2 is impossible -- it would isolate that sheet at both restored
endpoints, hence in the merged partition -- so the cover is Figure 33's `M⁽³⁾`
outright. -/
theorem selectedCensus_of_aligned (shape : Shape profile)
    (hAligned : pinSheet profile 0 = pinSheet profile 1)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2) :
    W2M1kIncomingMatching.SelectedCensus data hc hab hOne block
      (zeroEnd hc hab hOne star) (oneEnd hc hab hOne star)
      (mergedPartition data a b) (mergedPartition data a b) (mergedPartition data a b) := by
  obtain ⟨hChangeLeft, hChangeRight⟩ :=
    divalent_changes data hc hab hOne fullDim star hLeftCard hRightCard
  rcases selected_counts data hc hab hOne fullDim hForest profile shape hLeftCard hRightCard
    hChangeLeft hChangeRight with ⟨hZero, hOneE, hNew⟩ | ⟨hZero, hOneE, hNew⟩
  · exact joinedCensus_of_counts data hc hab hOne hZero hOneE hNew
  · exact absurd (not_detaching_of_aligned data hc hab hOne profile shape hAligned
      hLeftCard hRightCard hZero hOneE) not_false

/-! ## §5  The three branches in one statement -/

include fullDim hForest in
/-- **The selected-class census of an arbitrary
incoming `w2M1k` cover.**  Exactly the classifier's payload -- the profile, its
M-1k `Shape` -- and the standing bundle enter.  The three branches are Figure
33's three members: Base I.a at a `T_∅` wall, Base II.1 and Base II.2.2 at a
`T_2` one.  The divided branch is stated for *every* `DividedData` witness,
because the two detached classes do not depend on which residual sheet names
them. -/
theorem exists_selectedCensus (shape : Shape profile) :
    (∃ pair : LeafPair profile,
        ((GluingDatum.incidentEdges a).card = 1 ∨
            (GluingDatum.incidentEdges b).card = 1) ∧
          W2M1kIncomingMatching.SelectedCensus data hc hab hOne block
            (leafEnd hc hab hOne star) (branchEnd hc hab hOne star)
            (W2M1kIncomingMatching.leafSelected pair).left
            (W2M1kIncomingMatching.leafSelected pair).right
            (W2M1kIncomingMatching.leafSelected pair).newEdge) ∨
      ((GluingDatum.incidentEdges a).card = 2 ∧ (GluingDatum.incidentEdges b).card = 2 ∧
        (W2M1kIncomingMatching.SelectedCensus data hc hab hOne block
            (zeroEnd hc hab hOne star) (oneEnd hc hab hOne star)
            (mergedPartition data a b) (mergedPartition data a b)
            (mergedPartition data a b) ∨
          ∀ divided : DividedData profile,
            W2M1kIncomingMatching.SelectedCensus data hc hab hOne block
              (zeroEnd hc hab hOne star) (oneEnd hc hab hOne star)
              (W2M1kIncomingMatching.dividedSelected divided).left
              (W2M1kIncomingMatching.dividedSelected divided).right
              (W2M1kIncomingMatching.dividedSelected divided).newEdge)) := by
  rcases valencySplit_of_twoStar data hc hab hOne fullDim.valid fullDim.changeMinimal star with
    ⟨hLeftCard, hRightCard, hChangeLeft, hChangeRight⟩ | ⟨hLeafLeft, _, _, _⟩ |
      ⟨_, hLeafRight, _, _⟩
  · refine Or.inr ⟨hLeftCard, hRightCard, ?_⟩
    rcases selected_counts data hc hab hOne fullDim hForest profile shape hLeftCard hRightCard
      hChangeLeft hChangeRight with ⟨hZero, hOneE, hNew⟩ | ⟨hZero, hOneE, hNew⟩
    · exact Or.inl (joinedCensus_of_counts data hc hab hOne hZero hOneE hNew)
    · exact Or.inr (fun divided ↦ dividedCensus_of_counts data hc hab hOne profile shape
        divided hLeftCard hRightCard hZero hOneE hNew)
  · obtain ⟨pair, hCensus⟩ :=
      exists_selectedCensus_leaf data hc hab hOne fullDim profile shape (Or.inl hLeafLeft)
    exact Or.inl ⟨pair, Or.inl hLeafLeft, hCensus⟩
  · obtain ⟨pair, hCensus⟩ :=
      exists_selectedCensus_leaf data hc hab hOne fullDim profile shape (Or.inr hLeafRight)
    exact Or.inl ⟨pair, Or.inr hLeafRight, hCensus⟩

end Counts

end DraismaVargas.LocalCases.W2M1kSelectedCensus
