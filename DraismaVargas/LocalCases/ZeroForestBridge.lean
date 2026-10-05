module

public import DraismaVargas.Infrastructure.ContractionRamification
public import DraismaVargas.Infrastructure.NonnegativeRationalRealization
public import Utilities.Subdivision.ContractionForestCensusGeneral
public import Utilities.Subdivision.UnitSubdivisionPresentation

@[expose] public section

/-!
# Where the contraction forest receipt comes from

`DraismaVargas.Infrastructure.ContractionRamification` defines
`ContractionForest data a b contracted`, the source-topology receipt consumed by
`valid_contractDatum`, but nothing in the infrastructure layer *produces* it.
This file produces it, from the source-topology receipt a terminal face already
carries: `Utilities.Certificate.ContractionForestCensusGeneral.IsForest` for the
canonical zero set of a nonnegative integral realization.

Above one target occurrence `contracted` with endpoints `a`, `b` there is a
bipartite graph: its vertices are the blocks of `data.vertexPartition a`
together with the blocks of `data.vertexPartition b`, its edges are the blocks
of `data.edgePartition contracted`, and an edge block sits inside exactly one
block at each end (`refines_left`/`refines_right`).  The blocks of
`mergedPartition data a b = SheetPartition.join (vertexPartition a)
(vertexPartition b)` are exactly the connected components of that bipartite
graph, because the join relation is the equivalence relation *generated* by the
two endpoint relations.  So `ContractionForest` reads `Eᵢ = pᵢ + qᵢ - 1` in
every component: every component is a tree.

Main results:

* `card_blocksWithin_edge_add_one_ge` — the per-component inequality
  `pᵢ + qᵢ ≤ Eᵢ + 1`.  Every component is connected, so `ContractionForest` is
  exactly the equality case and is never a strengthening in the wrong
  direction.
* `contractionForest_iff_global_count` — `ContractionForest` is equivalent to
  the single global equation `E + C = p + q`, where `C` is the number of merged
  blocks.  This is `#edges = #vertices - #components`, the same shape as the
  census's `IsForest`.
* `isForest_of_subset` — a subset of a census forest is a census forest.  The
  census proves the graphic-matroid rank inequality and records `IsForest` as
  its equality case, but never this hereditary property, and it is the only
  property of the face's receipt the bridge needs.
* `contractionForest_of_isForest` and
  `contractionForest_of_isForest_of_targetLength_eq_zero` — the bridge:
  a nonnegative integral realization whose zero source occurrences form a
  census forest supplies `ContractionForest` at every zero-length target
  occurrence.

The bridge runs as follows.  Restrict the receipt to the slots `F` lying above
the contracted occurrence; those slots are the blocks of
`data.edgePartition contracted`, so `IsForest` for them reads
`#classes(F) + E = #sourceVertices`.  Label every source vertex above `a` or `b`
by its merged block and fix every other source vertex (`mergeLabel`).  That
label is constant along the fibre graph, hence factors through the census fold,
so `C + (#sourceVertices - p - q) ≤ #classes(F)`, which is `E + C ≤ p + q`.
The reverse inequality is the sum of the per-component inequality, so the two
sides agree and `contractionForest_iff_global_count` closes the argument.

The proof of the inequality is a growth induction.  Write `countOn P S` for the
number of blocks of `P` met by a finite set `S` of sheets.  Starting from a
single sheet, where all three counts are `1`, enlarge `S` one sheet at a time,
always adding a sheet related to one already present by the left or the right
endpoint relation.  Adding such a sheet `s` either
* leaves the edge count unchanged, and then, since the edge partition refines
  both endpoint partitions, it leaves both endpoint counts unchanged; or
* raises the edge count by one, and then it leaves *one* endpoint count
  unchanged (the one whose relation attached `s`) and raises the other by at
  most one.

Either way `countOn left + countOn right - countOn edge` does not increase, so
it stays at its initial value `1`.  The growth exhausts the whole join class,
because a set closed under the generating relation is a union of join classes.
-/

namespace DraismaVargas.LocalCases.ZeroForestBridge

open DraismaVargas.Infrastructure

/-! ## Counting blocks met by a finite set of sheets -/

section Abstract

variable {d : ℕ}

open SheetPartition

/-- The number of blocks of `partition` met by a finite set of sheets. -/
def countOn (partition : SheetPartition d) (sheets : Finset (Fin d)) : ℕ :=
  (sheets.image partition.repr).card

theorem mem_image_repr_iff (partition : SheetPartition d)
    (sheets : Finset (Fin d)) (s : Fin d) :
    partition.repr s ∈ sheets.image partition.repr ↔
      ∃ t ∈ sheets, partition.Rel t s := by
  constructor
  · intro hMember
    obtain ⟨t, hMem, hValue⟩ := Finset.mem_image.mp hMember
    exact ⟨t, hMem, hValue⟩
  · rintro ⟨t, hMem, hValue⟩
    exact Finset.mem_image.mpr ⟨t, hMem, hValue⟩

/-- Adding a sheet already related to a present one does not change the count. -/
theorem countOn_insert_of_rel (partition : SheetPartition d)
    (sheets : Finset (Fin d)) {s t : Fin d} (hMem : t ∈ sheets)
    (hRel : partition.Rel t s) :
    countOn partition (insert s sheets) = countOn partition sheets := by
  unfold countOn
  rw [Finset.image_insert,
    Finset.insert_eq_self.mpr
      ((mem_image_repr_iff partition sheets s).mpr ⟨t, hMem, hRel⟩)]

/-- Adding one sheet raises the count by at most one. -/
theorem countOn_insert_le (partition : SheetPartition d)
    (sheets : Finset (Fin d)) (s : Fin d) :
    countOn partition (insert s sheets) ≤ countOn partition sheets + 1 := by
  unfold countOn
  rw [Finset.image_insert]
  exact Finset.card_insert_le _ _

theorem countOn_singleton (partition : SheetPartition d) (s : Fin d) :
    countOn partition {s} = 1 := by
  unfold countOn
  rw [Finset.image_singleton, Finset.card_singleton]

/-- The growth step.  `edge` refines both endpoint partitions, and the new
sheet is attached to the old set by one of the two endpoint relations; then the
slack `countOn left + countOn right - countOn edge` does not increase. -/
theorem le_insert_step {left right edge : SheetPartition d}
    (hLeft : edge.Refines left) (hRight : edge.Refines right)
    {sheets : Finset (Fin d)} {s t : Fin d} (hMem : t ∈ sheets)
    (hAttach : left.Rel t s ∨ right.Rel t s)
    (hPrevious : countOn left sheets + countOn right sheets
      ≤ countOn edge sheets + 1) :
    countOn left (insert s sheets) + countOn right (insert s sheets)
      ≤ countOn edge (insert s sheets) + 1 := by
  classical
  by_cases hEdge : edge.repr s ∈ sheets.image edge.repr
  · obtain ⟨u, hMemU, hValue⟩ := (mem_image_repr_iff edge sheets s).mp hEdge
    rw [countOn_insert_of_rel left sheets hMemU (hLeft.rel hValue),
      countOn_insert_of_rel right sheets hMemU (hRight.rel hValue),
      countOn_insert_of_rel edge sheets hMemU hValue]
    exact hPrevious
  · have hEdgeCount :
        countOn edge (insert s sheets) = countOn edge sheets + 1 := by
      unfold countOn
      rw [Finset.image_insert, Finset.card_insert_of_notMem hEdge]
    rcases hAttach with hAttach | hAttach
    · rw [countOn_insert_of_rel left sheets hMem hAttach, hEdgeCount]
      have hOther := countOn_insert_le right sheets s
      omega
    · rw [countOn_insert_of_rel right sheets hMem hAttach, hEdgeCount]
      have hOther := countOn_insert_le left sheets s
      omega

/-! ## A proper subset of a join class has an exit -/

/-- The generating relation of the join is symmetric. -/
theorem attach_symm {left right : SheetPartition d} {i j : Fin d}
    (h : left.Rel i j ∨ right.Rel i j) : left.Rel j i ∨ right.Rel j i :=
  h.elim (fun hLeft ↦ Or.inl (Eq.symm hLeft)) fun hRight ↦ Or.inr (Eq.symm hRight)

/-- A subset of a join class that is a *proper* subset has an exit: a sheet of
the class outside the subset, attached to a sheet of the subset by one of the
two endpoint relations.  Otherwise the subset would be closed under the
generating relation, hence a union of join classes. -/
theorem exists_exit {left right : SheetPartition d} {sheets : Finset (Fin d)}
    {root : Fin d} (hRoot : root ∈ sheets)
    (hSubset : sheets ⊆ joinClass left right root)
    (hNe : sheets ≠ joinClass left right root) :
    ∃ s t, s ∈ joinClass left right root ∧ s ∉ sheets ∧ t ∈ sheets ∧
      (left.Rel t s ∨ right.Rel t s) := by
  by_contra hNone
  push Not at hNone
  have hStep : ∀ i j : Fin d,
      (left.Rel i j ∨ right.Rel i j) → i ∈ sheets → j ∈ sheets := by
    intro i j hAttach hMemI
    by_contra hMemJ
    have hClassI : JoinRel left right root i :=
      (mem_joinClass left right root i).mp (hSubset hMemI)
    have hClassJ : JoinRel left right root j :=
      hClassI.trans (hAttach.elim joinRel_of_left joinRel_of_right)
    have hBoth := hNone j i ((mem_joinClass left right root j).mpr hClassJ)
      hMemJ hMemI
    exact hAttach.elim hBoth.1 hBoth.2
  have hIff : ∀ i j : Fin d, JoinRel left right i j → (i ∈ sheets ↔ j ∈ sheets) := by
    intro i j hJoin
    induction hJoin with
    | rel x y hxy => exact ⟨hStep x y hxy, hStep y x (attach_symm hxy)⟩
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond
  refine hNe (Finset.Subset.antisymm hSubset ?_)
  intro u hMemU
  exact (hIff root u ((mem_joinClass left right root u).mp hMemU)).mp hRoot

/-! ## The per-component inequality -/

/-- The growth induction: a subset of the join class carrying the inequality
propagates it to the whole class.  `budget` bounds the number of sheets still
to be added. -/
theorem countOn_joinClass_le_of_subset {left right edge : SheetPartition d}
    (hLeft : edge.Refines left) (hRight : edge.Refines right) (root : Fin d) :
    ∀ (budget : ℕ) (sheets : Finset (Fin d)),
      (joinClass left right root).card ≤ sheets.card + budget →
      root ∈ sheets → sheets ⊆ joinClass left right root →
      countOn left sheets + countOn right sheets ≤ countOn edge sheets + 1 →
      countOn left (joinClass left right root)
          + countOn right (joinClass left right root)
        ≤ countOn edge (joinClass left right root) + 1 := by
  intro budget
  induction budget with
  | zero =>
    intro sheets hBudget hRoot hSubset hPrevious
    have hEq : sheets = joinClass left right root :=
      Finset.eq_of_subset_of_card_le hSubset (by omega)
    rw [← hEq]
    exact hPrevious
  | succ budget ih =>
    intro sheets hBudget hRoot hSubset hPrevious
    by_cases hEq : sheets = joinClass left right root
    · rw [← hEq]
      exact hPrevious
    obtain ⟨s, t, hClassS, hNotMemS, hMemT, hAttach⟩ :=
      exists_exit hRoot hSubset hEq
    refine ih (insert s sheets) ?_ (Finset.mem_insert_of_mem hRoot) ?_ ?_
    · rw [Finset.card_insert_of_notMem hNotMemS]
      omega
    · intro x hMemX
      rcases Finset.mem_insert.mp hMemX with hx | hx
      · exact hx ▸ hClassS
      · exact hSubset hx
    · exact le_insert_step hLeft hRight hMemT hAttach hPrevious

/-- The per-component inequality, in the `countOn` form. -/
theorem countOn_joinClass_le {left right edge : SheetPartition d}
    (hLeft : edge.Refines left) (hRight : edge.Refines right) (root : Fin d) :
    countOn left (joinClass left right root)
        + countOn right (joinClass left right root)
      ≤ countOn edge (joinClass left right root) + 1 := by
  refine countOn_joinClass_le_of_subset hLeft hRight root
    (joinClass left right root).card {root} ?_
    (Finset.mem_singleton_self root) ?_ ?_
  · simp
  · exact Finset.singleton_subset_iff.mpr
      ((mem_joinClass left right root root).mpr (joinRel_refl left right root))
  · rw [countOn_singleton, countOn_singleton, countOn_singleton]

/-- The join class of a sheet is its block in the constructed join. -/
theorem joinClass_eq_block (left right : SheetPartition d) (root : Fin d) :
    joinClass left right root = (join left right).block root := by
  ext j
  rw [mem_joinClass, SheetPartition.mem_block_iff, join_rel_iff]

/-- The per-component inequality, in the induced-block-count form: inside one
block of the join, the numbers of blocks of the two endpoint partitions add up
to at most one more than the number of blocks of any common refinement. -/
theorem blockCountWithin_join_add_le {left right edge : SheetPartition d}
    (hLeft : edge.Refines left) (hRight : edge.Refines right) (root : Fin d) :
    left.blockCountWithin (join left right) root
        + right.blockCountWithin (join left right) root
      ≤ edge.blockCountWithin (join left right) root + 1 := by
  have hCount := countOn_joinClass_le hLeft hRight (left := left) (right := right)
    (edge := edge) root
  rw [joinClass_eq_block] at hCount
  exact hCount

end Abstract

/-! ## The inequality above a contracted target occurrence -/

section Datum

open SheetPartition ContractionRamification

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
variable {contracted : target.edges}

/-- Inside every block of the merged partition, the numbers of blocks of the
two endpoint partitions add up to at most one more than the number of blocks of
the contracted occurrence's partition.  This is the connectivity half of
`ContractionForest`: a merged block is a single join class, so its fibre graph
is connected, and `ContractionForest` is exactly the equality case. -/
theorem card_blocksWithin_edge_add_one_ge (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (mergedBlock : (mergedPartition data a b).Blocks) :
    (blocksWithin (data.vertexPartition a) (mergedPartition data a b)
          mergedBlock).card
        + (blocksWithin (data.vertexPartition b) (mergedPartition data a b)
          mergedBlock).card
      ≤ (blocksWithin (data.edgePartition contracted) (mergedPartition data a b)
          mergedBlock).card + 1 := by
  rw [card_blocksWithin_eq_blockCountWithin _ _
      (vertexPartition_refines_mergedPartition data a b),
    card_blocksWithin_eq_blockCountWithin _ _
      (vertexPartition_refines_mergedPartition_right data a b),
    card_blocksWithin_eq_blockCountWithin _ _
      (edgePartition_refines_mergedPartition data hc)]
  exact blockCountWithin_join_add_le
    (refines_of_mem_incidentEdges_local data (contracted_mem_incidentEdges_left hc))
    (refines_of_mem_incidentEdges_local data (contracted_mem_incidentEdges_right hc))
    mergedBlock.1

/-! ## The global form -/

/-- Summing the numbers of fine blocks inside all coarse blocks recovers the
total number of fine blocks, in the `blocksWithin` form. -/
theorem sum_card_blocksWithin_eq_card_blocks (fine coarse : SheetPartition degree)
    (hRefines : fine.Refines coarse) :
    (∑ coarseBlock : coarse.Blocks,
        (blocksWithin fine coarse coarseBlock).card)
      = Fintype.card fine.Blocks := by
  rw [← sum_blockCountWithin_eq_card_blocks fine coarse hRefines]
  exact Finset.sum_congr rfl fun coarseBlock _ ↦
    card_blocksWithin_eq_blockCountWithin fine coarse hRefines coarseBlock

/-- The two endpoint families, summed over the merged blocks. -/
theorem sum_card_blocksWithin_endpoints (data : GluingDatum target degree)
    (a b : target.V) :
    (∑ mergedBlock : (mergedPartition data a b).Blocks,
        ((blocksWithin (data.vertexPartition a) (mergedPartition data a b)
            mergedBlock).card
          + (blocksWithin (data.vertexPartition b) (mergedPartition data a b)
            mergedBlock).card))
      = Fintype.card (data.vertexPartition a).Blocks
        + Fintype.card (data.vertexPartition b).Blocks := by
  rw [Finset.sum_add_distrib,
    sum_card_blocksWithin_eq_card_blocks _ _
      (vertexPartition_refines_mergedPartition data a b),
    sum_card_blocksWithin_eq_card_blocks _ _
      (vertexPartition_refines_mergedPartition_right data a b)]

/-- The edge family plus one per merged block, summed over the merged blocks. -/
theorem sum_card_blocksWithin_edge_add_one (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) :
    (∑ mergedBlock : (mergedPartition data a b).Blocks,
        ((blocksWithin (data.edgePartition contracted) (mergedPartition data a b)
            mergedBlock).card + 1))
      = Fintype.card (data.edgePartition contracted).Blocks
        + Fintype.card (mergedPartition data a b).Blocks := by
  rw [Finset.sum_add_distrib,
    sum_card_blocksWithin_eq_card_blocks _ _
      (edgePartition_refines_mergedPartition data hc)]
  simp

/-- The forest receipt is equivalent to the single global equation
`E + C = p + q`, where `E`, `p`, `q` count the blocks of the contracted
occurrence's partition and of the two endpoint partitions, and `C` counts the
merged blocks.  This is `#edges = #vertices - #components`, the additive shape
of a forest census.

Forward is summing the per-block equalities.  Backward is the per-component
inequality `card_blocksWithin_edge_add_one_ge` together with the fact that a
sum of nonnegative slacks vanishing forces each slack to vanish. -/
theorem contractionForest_iff_global_count (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) :
    ContractionForest data a b contracted ↔
      Fintype.card (data.edgePartition contracted).Blocks
          + Fintype.card (mergedPartition data a b).Blocks
        = Fintype.card (data.vertexPartition a).Blocks
          + Fintype.card (data.vertexPartition b).Blocks := by
  have hLe : ∀ mergedBlock ∈
      (Finset.univ : Finset (mergedPartition data a b).Blocks),
      (blocksWithin (data.vertexPartition a) (mergedPartition data a b)
          mergedBlock).card
        + (blocksWithin (data.vertexPartition b) (mergedPartition data a b)
          mergedBlock).card
      ≤ (blocksWithin (data.edgePartition contracted) (mergedPartition data a b)
          mergedBlock).card + 1 :=
    fun mergedBlock _ ↦ card_blocksWithin_edge_add_one_ge data hc mergedBlock
  constructor
  · intro hForest
    rw [← sum_card_blocksWithin_edge_add_one data hc,
      ← sum_card_blocksWithin_endpoints data a b]
    exact Finset.sum_congr rfl fun mergedBlock _ ↦ hForest mergedBlock
  · intro hCount mergedBlock
    have hSums :
        (∑ block : (mergedPartition data a b).Blocks,
            ((blocksWithin (data.vertexPartition a) (mergedPartition data a b)
                block).card
              + (blocksWithin (data.vertexPartition b) (mergedPartition data a b)
                block).card))
          = ∑ block : (mergedPartition data a b).Blocks,
              ((blocksWithin (data.edgePartition contracted)
                (mergedPartition data a b) block).card + 1) := by
      rw [sum_card_blocksWithin_endpoints data a b,
        sum_card_blocksWithin_edge_add_one data hc, hCount]
    exact ((Finset.sum_eq_sum_iff_of_le hLe).mp hSums mergedBlock
      (Finset.mem_univ mergedBlock)).symm

end Datum

/-! ## A subset of a census forest is a census forest

`Utilities/Subdivision/ContractionForestCensusGeneral.lean` proves the
graphic-matroid rank inequality `n ≤ #classes + F.card` for every slot set, and
records `IsForest` as its equality case, but never the hereditary property.
The receipt carried by a terminal face is `IsForest` for the *whole* zero set;
producing `ContractionForest` at one target occurrence needs it only for the
zero slots above that occurrence, so the restriction lemma is the bridge's
first step.

The proof is the relative form of the rank inequality: folding the extra slots
`F \ F'` after the slots of `F'` cuts the class count by at most `(F \ F').card`,
and the fold only sees the *set* of slots in its list, not their order or
multiplicity. -/

section Census

open Utilities.Certificate.ContractionForestCensusGeneral

variable {n p : ℕ}
  (core : Utilities.Certificate.ExplicitPotential.Core n p)

/-- Folding a further list of slots cuts the number of classes by at most the
length of that list.  The relative form of
`card_le_card_image_foldRep_add_length`. -/
theorem card_image_foldRep_le_append (first second : List (Fin p)) :
    (Finset.image (foldRep core first) Finset.univ).card
      ≤ (Finset.image (foldRep core (first ++ second)) Finset.univ).card
        + second.length := by
  induction second using List.reverseRecOn with
  | nil => simp
  | append_singleton rest slot ih =>
    have hStep := card_image_le_card_image_unionStep_succ
      (foldRep core (first ++ rest)) (core.tail slot) (core.head slot)
    rw [← List.append_assoc, foldRep_snoc]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- The fold sees only the set of slots in its list: two lists with the same
members induce the same number of classes. -/
theorem card_image_foldRep_congr (first second : List (Fin p))
    (hMembers : ∀ slot, slot ∈ first ↔ slot ∈ second) :
    (Finset.image (foldRep core first) Finset.univ).card
      = (Finset.image (foldRep core second) Finset.univ).card := by
  have hAdj : ∀ x y : Fin n,
      AdjInList core first x y ↔ AdjInList core second x y := by
    intro x y
    constructor
    · rintro ⟨slot, hSlot, hEnds⟩
      exact ⟨slot, (hMembers slot).mp hSlot, hEnds⟩
    · rintro ⟨slot, hSlot, hEnds⟩
      exact ⟨slot, (hMembers slot).mpr hSlot, hEnds⟩
  have hMono : ∀ relation relation' : Fin n → Fin n → Prop,
      (∀ u v, relation u v → relation' u v) →
      ∀ x y, Relation.ReflTransGen relation x y →
        Relation.ReflTransGen relation' x y := by
    intro relation relation' hStep x y hReach
    induction hReach with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hLast ih => exact ih.tail (hStep _ _ hLast)
  have hReach : ∀ x y : Fin n,
      ReachInList core first x y ↔ ReachInList core second x y := by
    intro x y
    exact ⟨hMono _ _ (fun u v h ↦ (hAdj u v).mp h) x y,
      hMono _ _ (fun u v h ↦ (hAdj u v).mpr h) x y⟩
  have hFibres : ∀ x y : Fin n,
      foldRep core first x = foldRep core first y ↔
        foldRep core second x = foldRep core second y := by
    intro x y
    rw [foldRep_iff, foldRep_iff]
    exact hReach x y
  exact le_antisymm
    (card_image_le_of_rep_iff (foldRep_idem core first) hFibres)
    (card_image_le_of_rep_iff (foldRep_idem core second)
      fun x y ↦ (hFibres x y).symm)

/-- Contracting a subset of a slot set cuts the class count by at most the
number of slots left out. -/
theorem card_image_compFold_le_of_subset {larger smaller : Finset (Fin p)}
    (hSubset : smaller ⊆ larger) :
    (Finset.image (compFold core smaller) Finset.univ).card
      ≤ (Finset.image (compFold core larger) Finset.univ).card
        + (larger \ smaller).card := by
  classical
  have hMembers : ∀ slot : Fin p,
      slot ∈ edgeList smaller ++ edgeList (larger \ smaller) ↔
        slot ∈ edgeList larger := by
    intro slot
    rw [List.mem_append, mem_edgeList, mem_edgeList, mem_edgeList,
      Finset.mem_sdiff]
    constructor
    · rintro (hSlot | ⟨hSlot, -⟩)
      · exact hSubset hSlot
      · exact hSlot
    · intro hSlot
      by_cases hSmall : slot ∈ smaller
      · exact Or.inl hSmall
      · exact Or.inr ⟨hSlot, hSmall⟩
  have hCongr := card_image_foldRep_congr core
    (edgeList smaller ++ edgeList (larger \ smaller)) (edgeList larger) hMembers
  have hAppend := card_image_foldRep_le_append core (edgeList smaller)
    (edgeList (larger \ smaller))
  rw [length_edgeList] at hAppend
  unfold compFold
  omega

/-- **A subset of a census forest is a census forest.**  This is the only
property of the terminal face's `IsForest` receipt that the contraction
bridge needs: the receipt holds for the whole zero set, and the fibre above one
target occurrence uses it only for the zero slots lying over that
occurrence. -/
theorem isForest_of_subset {larger smaller : Finset (Fin p)}
    (hSubset : smaller ⊆ larger) (hForest : IsForest core larger) :
    IsForest core smaller := by
  classical
  have hAdd := forest_image_add_card_eq core hForest
  have hLower := card_le_card_image_compFold_add_card core smaller
  have hUpper := card_image_compFold_le_of_subset core hSubset
  have hDiff := Finset.card_sdiff_add_card_eq_card hSubset
  have hLe : smaller.card ≤ larger.card := Finset.card_le_card hSubset
  unfold IsForest
  omega

end Census

/-! ## Counting the source objects above one target object -/

section Fibres

open SheetPartition

-- `target.edges` is the multiset-as-type and carries no `DecidableEq`
-- instance, so the fibre filters below are taken classically.  The attribute is
-- file-local and has priority `0`, so genuine instances still win.
attribute [local instance 0] Classical.propDecidable

variable {target : CFGraph} {degree : ℕ}

/-- The quotient-source vertices above a target vertex are its vertex-partition
blocks. -/
theorem card_filter_sourceVertex (data : GluingDatum target degree)
    (vertex : target.V) :
    (Finset.univ.filter fun source : data.SourceVertex ↦
        source.1.1 = vertex).card
      = Fintype.card (data.vertexPartition vertex).Blocks := by
  rw [← Finset.card_univ]
  refine Finset.card_bij'
    (fun source _ ↦ (data.vertexPartition vertex).toBlock source.1.2)
    (fun block _ ↦ (⟨(vertex, block.1), block.2⟩ : data.SourceVertex))
    (fun _ _ ↦ Finset.mem_univ _)
    (fun block _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
    (fun source hSource ↦ ?_) (fun block _ ↦ ?_)
  · have hVertex : source.1.1 = vertex := (Finset.mem_filter.mp hSource).2
    apply Subtype.ext
    apply Prod.ext
    · exact hVertex.symm
    · show (data.vertexPartition vertex).repr source.1.2 = source.1.2
      rw [← hVertex]
      exact source.2
  · exact Subtype.ext block.2

/-- The quotient-source edge blocks above a target occurrence are its
edge-partition blocks. -/
theorem card_filter_sourceEdge (data : GluingDatum target degree)
    (edge : target.edges) :
    (Finset.univ.filter fun source : data.SourceEdge ↦ source.1.1 = edge).card
      = Fintype.card (data.edgePartition edge).Blocks := by
  rw [← Finset.card_univ]
  refine Finset.card_bij'
    (fun source _ ↦ (data.edgePartition edge).toBlock source.1.2)
    (fun block _ ↦ (⟨(edge, block.1), block.2⟩ : data.SourceEdge))
    (fun _ _ ↦ Finset.mem_univ _)
    (fun block _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
    (fun source hSource ↦ ?_) (fun block _ ↦ ?_)
  · have hEdge : source.1.1 = edge := (Finset.mem_filter.mp hSource).2
    apply Subtype.ext
    apply Prod.ext
    · exact hEdge.symm
    · show (data.edgePartition edge).repr source.1.2 = source.1.2
      rw [← hEdge]
      exact source.2
  · exact Subtype.ext block.2

end Fibres

/-! ## The merged-block label on quotient-source vertices -/

section MergeLabel

open SheetPartition ContractionRamification

attribute [local instance 0] Classical.propDecidable

variable {target : CFGraph} {degree : ℕ}

/-- Collapse every quotient-source vertex above `a` or `b` to its merged block,
and fix every other quotient-source vertex.  A source vertex above `a` or `b`
is labelled only by its merged block, so the label is constant along the fibre
graph above the contracted occurrence. -/
noncomputable def mergeLabel (data : GluingDatum target degree) (a b : target.V)
    (source : data.SourceVertex) : target.V × Fin degree :=
  if source.1.1 = a ∨ source.1.1 = b then
    (a, (mergedPartition data a b).repr source.1.2)
  else source.1

theorem mergeLabel_of_above (data : GluingDatum target degree) (a b : target.V)
    {source : data.SourceVertex} (h : source.1.1 = a ∨ source.1.1 = b) :
    mergeLabel data a b source
      = (a, (mergedPartition data a b).repr source.1.2) :=
  ite_eq_left h

theorem mergeLabel_of_not_above (data : GluingDatum target degree)
    (a b : target.V) {source : data.SourceVertex}
    (h : ¬(source.1.1 = a ∨ source.1.1 = b)) :
    mergeLabel data a b source = source.1 :=
  ite_eq_right h

/-- The label's image splits into one point per merged block and one point per
source vertex above neither endpoint. -/
theorem image_mergeLabel (data : GluingDatum target degree) (a b : target.V) :
    Finset.image (mergeLabel data a b) Finset.univ
      = (Finset.univ.image fun block : (mergedPartition data a b).Blocks ↦
            (a, block.1))
        ∪ ((Finset.univ.filter fun source : data.SourceVertex ↦
              ¬(source.1.1 = a ∨ source.1.1 = b)).image fun source ↦ source.1) := by
  ext item
  simp only [Finset.mem_image, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨source, rfl⟩
    by_cases hAbove : source.1.1 = a ∨ source.1.1 = b
    · exact Or.inl ⟨(mergedPartition data a b).toBlock source.1.2,
        (mergeLabel_of_above data a b hAbove).symm⟩
    · exact Or.inr ⟨source, hAbove, (mergeLabel_of_not_above data a b hAbove).symm⟩
  · rintro (⟨block, rfl⟩ | ⟨source, hAbove, rfl⟩)
    · refine ⟨data.sourceEndpoint a block.1, ?_⟩
      have hVertex : (data.sourceEndpoint a block.1).1.1 = a := rfl
      rw [mergeLabel_of_above data a b (Or.inl hVertex)]
      have hRel : (mergedPartition data a b).Rel
          ((data.vertexPartition a).repr block.1) block.1 :=
        (vertexPartition_refines_mergedPartition data a b).rel
          ((data.vertexPartition a).rel_repr_left block.1)
      have hRepr : (mergedPartition data a b).repr
          ((data.vertexPartition a).repr block.1) = block.1 := hRel.trans block.2
      exact congrArg (fun sheet ↦ (a, sheet)) hRepr
    · exact ⟨source, mergeLabel_of_not_above data a b hAbove⟩

/-- Counting the label's image: one point per merged block, plus one point per
source vertex above neither endpoint. -/
theorem card_image_mergeLabel (data : GluingDatum target degree) {a b : target.V}
    (hab : a ≠ b) :
    (Finset.image (mergeLabel data a b) Finset.univ).card
        + Fintype.card (data.vertexPartition a).Blocks
        + Fintype.card (data.vertexPartition b).Blocks
      = Fintype.card (mergedPartition data a b).Blocks
        + Fintype.card data.SourceVertex := by
  have hDisjoint :
      Disjoint
        (Finset.univ.image fun block : (mergedPartition data a b).Blocks ↦
          (a, block.1))
        ((Finset.univ.filter fun source : data.SourceVertex ↦
            ¬(source.1.1 = a ∨ source.1.1 = b)).image fun source ↦ source.1) := by
    refine Finset.disjoint_left.mpr ?_
    rintro item hFirst hSecond
    obtain ⟨block, -, rfl⟩ := Finset.mem_image.mp hFirst
    obtain ⟨source, hSource, hValue⟩ := Finset.mem_image.mp hSecond
    exact (Finset.mem_filter.mp hSource).2
      (Or.inl (congrArg Prod.fst hValue))
  have hFirstCard :
      (Finset.univ.image fun block : (mergedPartition data a b).Blocks ↦
          (a, block.1)).card
        = Fintype.card (mergedPartition data a b).Blocks := by
    rw [Finset.card_image_of_injective _ ?_, Finset.card_univ]
    intro first second hEq
    exact Subtype.ext (congrArg Prod.snd hEq)
  have hSecondCard :
      ((Finset.univ.filter fun source : data.SourceVertex ↦
          ¬(source.1.1 = a ∨ source.1.1 = b)).image fun source ↦ source.1).card
        = (Finset.univ.filter fun source : data.SourceVertex ↦
            ¬(source.1.1 = a ∨ source.1.1 = b)).card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have hAboveCard :
      (Finset.univ.filter fun source : data.SourceVertex ↦
          source.1.1 = a ∨ source.1.1 = b).card
        = Fintype.card (data.vertexPartition a).Blocks
          + Fintype.card (data.vertexPartition b).Blocks := by
    rw [Finset.filter_or, Finset.card_union_of_disjoint, card_filter_sourceVertex,
      card_filter_sourceVertex]
    refine Finset.disjoint_left.mpr ?_
    intro source hLeft hRight
    exact hab (((Finset.mem_filter.mp hLeft).2).symm.trans
      (Finset.mem_filter.mp hRight).2)
  have hSplit :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset data.SourceVertex))
      (p := fun source : data.SourceVertex ↦ source.1.1 = a ∨ source.1.1 = b)
  rw [Finset.card_univ] at hSplit
  rw [image_mergeLabel, Finset.card_union_of_disjoint hDisjoint, hFirstCard,
    hSecondCard]
  omega

end MergeLabel

/-! ## The census bridge -/

section Bridge

open SheetPartition ContractionRamification
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral

attribute [local instance 0] Classical.propDecidable

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
variable {contracted : target.edges}

/-- The canonical quotient-source core slots lying above one target
occurrence. -/
noncomputable def fibreSlots (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (contracted : target.edges) : Finset (Fin data.sourceGraph.edges.card) :=
  Finset.univ.filter fun slot ↦ (realization.sourceEdgeAt slot).1.1 = contracted

@[simp] theorem mem_fibreSlots (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (contracted : target.edges) (slot : Fin data.sourceGraph.edges.card) :
    slot ∈ fibreSlots data realization contracted ↔
      (realization.sourceEdgeAt slot).1.1 = contracted := by
  unfold fibreSlots
  exact ⟨fun h ↦ (Finset.mem_filter.mp h).2,
    fun h ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

/-- The slots above a target occurrence are its edge-partition blocks. -/
theorem card_fibreSlots (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (contracted : target.edges) :
    (fibreSlots data realization contracted).card
      = Fintype.card (data.edgePartition contracted).Blocks := by
  rw [← card_filter_sourceEdge data contracted]
  refine Finset.card_bij'
    (fun slot _ ↦ realization.sourceEdgeAt slot)
    (fun edge _ ↦ realization.sourceSlotEquiv.symm edge)
    (fun slot hSlot ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (mem_fibreSlots data realization contracted slot).mp hSlot⟩)
    (fun edge hEdge ↦ ?_) (fun slot _ ↦ ?_) (fun edge _ ↦ ?_)
  · refine (mem_fibreSlots data realization contracted _).mpr ?_
    rw [← GluingDatum.NonnegativeIntegralRealization.sourceSlotEquiv_apply,
      Equiv.apply_symm_apply]
    exact (Finset.mem_filter.mp hEdge).2
  · rw [← GluingDatum.NonnegativeIntegralRealization.sourceSlotEquiv_apply,
      Equiv.symm_apply_apply]
  · rw [← GluingDatum.NonnegativeIntegralRealization.sourceSlotEquiv_apply,
      Equiv.apply_symm_apply]

/-- If every source occurrence above the target occurrence has vanished, its
slots all lie in the canonical zero set. -/
theorem fibreSlots_subset_sourceZeroSet (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hZero : ∀ edge : data.SourceEdge, edge.1.1 = contracted →
      realization.sourceLength edge = 0) :
    fibreSlots data realization contracted ⊆ realization.sourceZeroSet := by
  intro slot hSlot
  rw [GluingDatum.NonnegativeIntegralRealization.mem_sourceZeroSet]
  exact hZero _ ((mem_fibreSlots data realization contracted slot).mp hSlot)

/-- The quotient-source vertex carrying a canonical finite core label.  The
ascription forces the `data.sourceGraph.V` label type down to
`data.SourceVertex`, which it unfolds to. -/
noncomputable def sourceVertexOf (data : GluingDatum target degree)
    (label : Fin (Fintype.card data.sourceGraph.V)) : data.SourceVertex :=
  (UnitSubdivisionPresentation.vertexEquiv data.sourceGraph).symm label

theorem sourceVertexOf_surjective (data : GluingDatum target degree) :
    Function.Surjective (sourceVertexOf data) :=
  (UnitSubdivisionPresentation.vertexEquiv data.sourceGraph).symm.surjective

/-! ### The two ends of a core slot -/

theorem vertexEquiv_symm_core_tail (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (slot : Fin data.sourceGraph.edges.card) :
    sourceVertexOf data
        ((UnitSubdivisionPresentation.core data.sourceGraph).tail slot)
      = (data.sourceEnds (realization.sourceEdgeAt slot)).1 := by
  unfold sourceVertexOf
  rw [UnitSubdivisionPresentation.core_tail]
  simp only [Equiv.symm_apply_apply]
  rw [GluingDatum.NonnegativeIntegralRealization.sourceEdgeAt,
    data.sourceEnds_sourceEdgeOfOccurrence]
  rfl

theorem vertexEquiv_symm_core_head (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (slot : Fin data.sourceGraph.edges.card) :
    sourceVertexOf data
        ((UnitSubdivisionPresentation.core data.sourceGraph).head slot)
      = (data.sourceEnds (realization.sourceEdgeAt slot)).2 := by
  unfold sourceVertexOf
  rw [UnitSubdivisionPresentation.core_head]
  simp only [Equiv.symm_apply_apply]
  rw [GluingDatum.NonnegativeIntegralRealization.sourceEdgeAt,
    data.sourceEnds_sourceEdgeOfOccurrence]
  rfl

/-! ### The label is constant on the fibre -/

theorem mergeLabel_sourceEndpoint_left (data : GluingDatum target degree)
    (a b : target.V) (sheet : Fin degree) :
    mergeLabel data a b (data.sourceEndpoint a sheet)
      = (a, (mergedPartition data a b).repr sheet) := by
  rw [mergeLabel_of_above data a b (Or.inl (rfl : (data.sourceEndpoint a sheet).1.1 = a))]
  exact congrArg (fun sheet' ↦ (a, sheet'))
    ((vertexPartition_refines_mergedPartition data a b).rel
      ((data.vertexPartition a).rel_repr_left sheet))

theorem mergeLabel_sourceEndpoint_right (data : GluingDatum target degree)
    (a b : target.V) (sheet : Fin degree) :
    mergeLabel data a b (data.sourceEndpoint b sheet)
      = (a, (mergedPartition data a b).repr sheet) := by
  rw [mergeLabel_of_above data a b (Or.inr (rfl : (data.sourceEndpoint b sheet).1.1 = b))]
  exact congrArg (fun sheet' ↦ (a, sheet'))
    ((vertexPartition_refines_mergedPartition_right data a b).rel
      ((data.vertexPartition b).rel_repr_left sheet))

/-- The two ends of a slot above the contracted occurrence carry the same
merged-block label. -/
theorem mergeLabel_core_tail_eq_head (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b))
    {slot : Fin data.sourceGraph.edges.card}
    (hSlot : slot ∈ fibreSlots data realization contracted) :
    mergeLabel data a b
        (sourceVertexOf data
          ((UnitSubdivisionPresentation.core data.sourceGraph).tail slot))
      = mergeLabel data a b
        (sourceVertexOf data
          ((UnitSubdivisionPresentation.core data.sourceGraph).head slot)) := by
  have hAbove : (realization.sourceEdgeAt slot).1.1 = contracted :=
    (mem_fibreSlots data realization contracted slot).mp hSlot
  have hPair : ((realization.sourceEdgeAt slot).1.1 : target.V × target.V) = (a, b) := by
    rw [hAbove]; exact hc
  rw [vertexEquiv_symm_core_tail, vertexEquiv_symm_core_head]
  show mergeLabel data a b
      (data.sourceEndpoint ((realization.sourceEdgeAt slot).1.1 : target.V × target.V).1
        (realization.sourceEdgeAt slot).1.2)
    = mergeLabel data a b
      (data.sourceEndpoint ((realization.sourceEdgeAt slot).1.1 : target.V × target.V).2
        (realization.sourceEdgeAt slot).1.2)
  rw [hPair]
  rw [mergeLabel_sourceEndpoint_left, mergeLabel_sourceEndpoint_right]

/-- The label is constant along reachability through the fibre slots. -/
theorem mergeLabel_of_reachIn (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b))
    {x y : Fin (Fintype.card data.sourceGraph.V)}
    (hReach : Relation.ReflTransGen
      (AdjInList (UnitSubdivisionPresentation.core data.sourceGraph)
        (edgeList (fibreSlots data realization contracted))) x y) :
    mergeLabel data a b (sourceVertexOf data x)
      = mergeLabel data a b (sourceVertexOf data y) := by
  induction hReach with
  | refl => rfl
  | tail _ hStep ih =>
    refine ih.trans ?_
    obtain ⟨slot, hMember, hEnds⟩ := hStep
    have hSlot : slot ∈ fibreSlots data realization contracted :=
      (mem_edgeList _ slot).mp hMember
    rcases hEnds with ⟨hTail, hHead⟩ | ⟨hHead, hTail⟩
    · rw [← hTail, ← hHead]
      exact mergeLabel_core_tail_eq_head data realization hc hSlot
    · rw [← hTail, ← hHead]
      exact (mergeLabel_core_tail_eq_head data realization hc hSlot).symm

/-- The label factors through the union-find fold of the fibre slots. -/
theorem mergeLabel_compFold (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b))
    (x : Fin (Fintype.card data.sourceGraph.V)) :
    mergeLabel data a b
        (sourceVertexOf data
          (compFold (UnitSubdivisionPresentation.core data.sourceGraph)
            (fibreSlots data realization contracted) x))
      = mergeLabel data a b (sourceVertexOf data x) :=
  mergeLabel_of_reachIn data realization hc
    ((compFold_iff (UnitSubdivisionPresentation.core data.sourceGraph)
      (fibreSlots data realization contracted) _ x).mp
      (compFold_idem (UnitSubdivisionPresentation.core data.sourceGraph)
        (fibreSlots data realization contracted) x))

/-- Hence the label has at most as many values as the fold has classes. -/
theorem card_image_mergeLabel_le (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b)) :
    (Finset.image (mergeLabel data a b) Finset.univ).card
      ≤ (Finset.image
          (compFold (UnitSubdivisionPresentation.core data.sourceGraph)
            (fibreSlots data realization contracted)) Finset.univ).card := by
  have hTransfer :
      Finset.image (mergeLabel data a b) (Finset.univ : Finset data.SourceVertex)
        = Finset.image (fun x ↦ mergeLabel data a b (sourceVertexOf data x))
          (Finset.univ : Finset (Fin (Fintype.card data.sourceGraph.V))) := by
    rw [← Finset.image_univ_of_surjective (sourceVertexOf_surjective data),
      Finset.image_image]
    rfl
  have hFactor :
      Finset.image (fun x ↦ mergeLabel data a b (sourceVertexOf data x))
        (Finset.univ : Finset (Fin (Fintype.card data.sourceGraph.V)))
      = Finset.image (fun x ↦ mergeLabel data a b (sourceVertexOf data x))
        (Finset.image
          (compFold (UnitSubdivisionPresentation.core data.sourceGraph)
            (fibreSlots data realization contracted)) Finset.univ) := by
    rw [Finset.image_image]
    exact Finset.image_congr fun x _ ↦
      (mergeLabel_compFold data realization hc x).symm
  rw [hTransfer, hFactor]
  exact Finset.card_image_le

/-! ### The bridge -/

/-- Summing the per-component inequality: the global count is always at least
the endpoint count. -/
theorem global_count_ge (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) :
    Fintype.card (data.vertexPartition a).Blocks
        + Fintype.card (data.vertexPartition b).Blocks
      ≤ Fintype.card (data.edgePartition contracted).Blocks
        + Fintype.card (mergedPartition data a b).Blocks := by
  rw [← sum_card_blocksWithin_endpoints data a b,
    ← sum_card_blocksWithin_edge_add_one data hc]
  exact Finset.sum_le_sum fun mergedBlock _ ↦
    card_blocksWithin_edge_add_one_ge data hc mergedBlock

/-- **The census bridge.**  A terminal face whose zero source occurrences form
a census forest supplies the Draisma--Vargas contraction receipt at every
zero-length target occurrence. -/
theorem contractionForest_of_isForest (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hZero : ∀ edge : data.SourceEdge, edge.1.1 = contracted →
      realization.sourceLength edge = 0)
    (hForest : IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet) :
    ContractionForest data a b contracted := by
  have hab : a ≠ b := by
    have hMember : (contracted : target.V × target.V) ∈ target.edges :=
      Multiset.coe_mem
    rw [hc] at hMember
    intro hEq
    rw [hEq] at hMember
    exact target.loopless b hMember
  have hFibreForest :
      IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
        (fibreSlots data realization contracted) :=
    isForest_of_subset _
      (fibreSlots_subset_sourceZeroSet data realization hZero) hForest
  have hAdd := forest_image_add_card_eq
    (UnitSubdivisionPresentation.core data.sourceGraph) hFibreForest
  rw [card_fibreSlots data realization contracted] at hAdd
  have hLe := card_image_mergeLabel_le data realization hc
  have hLabel := card_image_mergeLabel data hab
  have hVertices : Fintype.card data.sourceGraph.V
      = Fintype.card data.SourceVertex := rfl
  rw [← hVertices] at hLabel
  have hGe := global_count_ge data hc
  rw [contractionForest_iff_global_count data hc]
  omega

/-- A source occurrence above a vanishing target occurrence vanishes: the
dilation equation has a strictly positive index. -/
theorem sourceLength_eq_zero_of_targetLength_eq_zero
    (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hTarget : realization.targetLength contracted = 0)
    (edge : data.SourceEdge) (hEdge : edge.1.1 = contracted) :
    realization.sourceLength edge = 0 := by
  have hDilation := realization.dilation_length edge
  rw [hEdge, hTarget] at hDilation
  exact (Nat.mul_eq_zero.mp hDilation).resolve_left
    (Nat.ne_of_gt (data.sourceEdgeIndex_pos edge))

/-- **The census bridge at a zero-length target occurrence.**  This is the form
the terminal face supplies: its receipt is `IsForest` for the whole zero set,
and the occurrence being contracted has vanishing target length. -/
theorem contractionForest_of_isForest_of_targetLength_eq_zero
    (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hTarget : realization.targetLength contracted = 0)
    (hForest : IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet) :
    ContractionForest data a b contracted :=
  contractionForest_of_isForest data realization hc
    (fun edge hEdge ↦ sourceLength_eq_zero_of_targetLength_eq_zero data
      realization hTarget edge hEdge) hForest

end Bridge

end DraismaVargas.LocalCases.ZeroForestBridge
