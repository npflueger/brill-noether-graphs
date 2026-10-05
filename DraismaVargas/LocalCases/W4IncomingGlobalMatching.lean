module

public import DraismaVargas.LocalCases.W4IncomingBlockPictures
public import DraismaVargas.LocalCases.W4RetainedBlockRelations
public import DraismaVargas.LocalCases.W4StableGraph

@[expose] public section

/-!
# Complete incoming W4 partition identification

Source: Draisma--Vargas Part I, Case {aux-r0} (sub-cases nd2 and nd3), the
non-dangling union lemma (`lemma-class-union`), and Case {w4} (abbreviated W4):
Figures 26--27 and Equation (1).

This module completes the incoming side of the actual W4 wall comparison, on
top of the target normalization, pruned-fibre census, retained flags, sheet
classes and restricted relations.

## The canonical nd3 ordering is derived, not assumed

`W4IncomingBlockPictures.nd3_ordered_classes` *takes* an ordering of the three
active nd3 branches in which the first is alone on its pairing side.
`canonical_ordering` derives that ordering: `Nd3Block.singletonLabel` -- the very
label the outgoing candidate's own nd3 resolution uses -- is proved to be the
singleton, and `pairFirst`/`pairSecond` name the other two.  The input is only
the finite `2+2` classification of `W4TargetPairings`, so the derivation needs
no geometric hypothesis at all.  `nd3_canonical_classes` is the resulting
ordering-free sheet-class identification.

## The dangling picture

For an entirely dangling wall block the surviving wall valency is zero, and
then there is no surviving internal occurrence either
(`dangling_internalEdges_eq_empty`: one would force a source vertex of
surviving valency one, which a connected quotient source does not have), the
pruned fibre is empty, the merged class is a single sheet
(`dangling_mergedBlock_eq_singleton`), and both endpoint relations and the
contracted-edge relation are discrete on it.

## Exhaustive matching

`nd2_same_partition_table`, `nd2_opposite_partition_table`,
`nd3_canonical_partition_table` and `dangling_partition_table` give the literal
block of `vertexPartition a`, `vertexPartition b` and `edgePartition contracted`
at *every* sheet of the merged block -- inactive sheets included.
`pairingSide` names the original target end carrying a prescribed side of the
normalized pairing; `endpoint_fst_eq_pairingSide` proves that this is the
canonical incoming endpoint of every retained wall occurrence on that side, so
the possible global endpoint exchange is handled once for the whole wall rather
than per flag.  `partition_block_matching` and `partition_sameBlocks` then
compare all three partitions with the canonical candidate's pasted resolution
`W4Assembly.wholeResolution` for the normalized pairing.

The consumed hypotheses are exactly those of the other incoming W4 modules:
one full-dimensional source presentation, occurrencewise
dangling compatibility across the contraction, the four-star at the contracted
wall, and the actual `AuxR0BlockPicture` of every wall block.  Those coexist:
they are the same bundle under which `W4IncomingRetainedFlags`,
`W4IncomingSheetClasses` and `W4IncomingBlockPictures` are proved, and
the picture assignment is the source-side classification `W4SourceClassification`
constructs from an active-branch census.

Stored-representative normalization -- turning these pointwise `SameBlocks` into
exact datum equality by `PartitionNormalization.sheetRelabeling`, as is done
in the M11 case -- needs the outgoing candidate datum as well, and is not
claimed here.
-/

namespace DraismaVargas.LocalCases.W4IncomingGlobalMatching

open DraismaVargas.Infrastructure GraphContraction GluingContraction ContractionRamification
open W4StableSource W4Assembly W4TargetPairings
open W4IncomingRetainedFlags W4IncomingSheetClasses W4IncomingBlockPictures
open ResolutionM11 ResolutionW4
open FullDimensionalSource FullContractionFibre PrunedFibreValency PrunedFibreTree WallDegeneration

section Ordering

variable {target : CFGraph} {wall : target.V}

/-- The first of the two nd3 branches sharing the side opposite the canonical
singleton branch. -/
def pairFirst (block : Nd3Block) (pairing : Fin 3) : Fin 4 :=
  if block.singletonLabel pairing = block.first then block.second else block.first

/-- The second of the two nd3 branches sharing the side opposite the canonical
singleton branch. -/
def pairSecond (block : Nd3Block) (pairing : Fin 3) : Fin 4 :=
  if block.singletonLabel pairing = block.third then block.second else block.third

/-- **The canonical nd3 singleton/pair ordering.**  For the actual three
distinct active branches of an nd3 wall block and any of the three `2+2`
target pairings, `Nd3Block.singletonLabel` and the two labels
`pairFirst`/`pairSecond` are a genuine reordering of the block's active
labels in which the first is alone on its side and the other two share the
opposite side.  Nothing is assumed: the split is forced by the finite
classification of `2+2` pairings. -/
theorem canonical_ordering (block : Nd3Block)
    (star : FourStar target wall) (pairing : Fin 3) :
    block.singletonLabel pairing ∈ block.activeLabels ∧
      pairFirst block pairing ∈ block.activeLabels ∧
      pairSecond block pairing ∈ block.activeLabels ∧
      pairFirst block pairing ≠ pairSecond block pairing ∧
      star.right pairing (star.edge (block.singletonLabel pairing)) ≠
        star.right pairing (star.edge (pairFirst block pairing)) ∧
      star.right pairing (star.edge (pairFirst block pairing)) =
        star.right pairing (star.edge (pairSecond block pairing)) := by
  refine ⟨block.singletonLabel_mem_activeLabels pairing, ?_⟩
  rcases block.singletonLabel_isSingleton_actual star pairing with
    ⟨hLabel, hNe, hSame⟩ | ⟨hLabel, hNe, hSame⟩ | ⟨hLabel, hNe, hSame⟩
  · have hFirst : pairFirst block pairing = block.second := by
      simp only [pairFirst, ite_eq_left hLabel]
    have hSecond : pairSecond block pairing = block.third := by
      refine ite_eq_right ?_
      rw [hLabel]
      exact block.first_ne_third
    rw [hFirst, hSecond, hLabel]
    exact ⟨by simp, by simp, block.second_ne_third, hNe, hSame⟩
  · have hFirst : pairFirst block pairing = block.first := by
      refine ite_eq_right ?_
      rw [hLabel]
      exact fun h ↦ block.first_ne_second h.symm
    have hSecond : pairSecond block pairing = block.third := by
      refine ite_eq_right ?_
      rw [hLabel]
      exact block.second_ne_third
    rw [hFirst, hSecond, hLabel]
    exact ⟨by simp, by simp, block.first_ne_third, hNe, hSame⟩
  · have hFirst : pairFirst block pairing = block.first := by
      refine ite_eq_right ?_
      rw [hLabel]
      exact fun h ↦ block.first_ne_third h.symm
    have hSecond : pairSecond block pairing = block.second := by
      simp only [pairSecond, ite_eq_left hLabel]
    rw [hFirst, hSecond, hLabel]
    exact ⟨by simp, by simp, block.first_ne_second, hNe, hSame⟩

/-- Every W4 nd2 local resolution keeps each of its three partitions equal to
the wall partition or to the wall partition with the selected block split. -/
theorem nd2Resolution_sides {degree : ℕ} (P : SheetPartition degree) (anchor : Fin degree)
    (firstRight secondRight : Bool) :
    ((nd2Resolution P anchor firstRight secondRight).left = P ∨
        (nd2Resolution P anchor firstRight secondRight).left = P.splitBlock anchor) ∧
      ((nd2Resolution P anchor firstRight secondRight).right = P ∨
        (nd2Resolution P anchor firstRight secondRight).right = P.splitBlock anchor) ∧
      ((nd2Resolution P anchor firstRight secondRight).newEdge = P ∨
        (nd2Resolution P anchor firstRight secondRight).newEdge = P.splitBlock anchor) := by
  unfold nd2Resolution
  split_ifs <;>
    simp [splitResolutionAt, joinedResolutionAt, LocalResolution.reverse]

/-- Equality of every block is exactly `SameBlocks`. -/
theorem sameBlocks_of_block_eq {degree : ℕ} {first second : SheetPartition degree}
    (h : ∀ sheet : Fin degree, first.block sheet = second.block sheet) :
    first.SameBlocks second := by
  intro i j
  rw [← SheetPartition.mem_block_iff, ← SheetPartition.mem_block_iff, h i]

end Ordering

section Incoming

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*}
  [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : FourStar (contract target hab hOne) ⟨a, hab⟩)
  (hCompat : DanglingCompatible data hc hab hOne)
  (block : (mergedPartition data a b).Blocks)

local notation "M₀" => contractDatum data hc hab hOne
local notation "q" => W4IncomingTargetNormalization.pairing data fd hc hab hOne star
local notation "B₀" => W4IncomingBlockPictures.wallBlock data hc hab hOne block

/-! ### Reading a restricted relation as a literal block table -/

omit [Fintype coordinate] [DecidableEq coordinate] fd star hCompat in
/-- A partition whose relation, restricted to the merged block, is one
distinguished sheet set plus singletons, has that literal block table on every
sheet of the merged block -- inactive sheets included. -/
theorem block_eq_ite_of_restricted_rel (P : SheetPartition degree)
    (S : Finset (Fin degree))
    (hRel : ∀ first second : Fin degree,
      first ∈ (mergedPartition data a b).block block.1 →
      (P.Rel first second ↔ first = second ∨ (first ∈ S ∧ second ∈ S)))
    (sheet : Fin degree) (hSheet : sheet ∈ (mergedPartition data a b).block block.1) :
    P.block sheet = if sheet ∈ S then S else {sheet} := by
  classical
  by_cases hMem : sheet ∈ S
  · rw [ite_eq_left hMem]
    ext other
    rw [SheetPartition.mem_block_iff, hRel sheet other hSheet]
    constructor
    · rintro (rfl | ⟨_, hOther⟩)
      · exact hMem
      · exact hOther
    · intro hOther
      exact Or.inr ⟨hMem, hOther⟩
  · rw [ite_eq_right hMem]
    ext other
    rw [SheetPartition.mem_block_iff, hRel sheet other hSheet, Finset.mem_singleton]
    constructor
    · rintro (rfl | ⟨hBad, _⟩)
      · rfl
      · exact absurd hBad hMem
    · rintro rfl
      exact Or.inl rfl

include fd star hCompat

/-- **The canonical nd3 incoming class identification.**  No ordering of the
three active branches is supplied: the canonical `Nd3Block.singletonLabel`
used by the outgoing candidate's own nd3 resolution is proved to be the
singleton side, and the other two labels are named by `pairFirst`/`pairSecond`.
The unique surviving internal occurrence and the singleton-side endpoint carry
exactly the retained singleton-branch class; the pair-side endpoint carries the
whole merged class. -/
theorem nd3_canonical_classes {model : Nd3Block}
    (picture : AuxR0Nd3Picture M₀ star B₀ model) :
    ∃ edge : data.SourceEdge,
      internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = {edge} ∧
      (data.edgePartition edge.1.1).block edge.1.2 =
        ((M₀).edgePartition (star.edge (model.singletonLabel q))).block
          (picture.activeSheet (model.singletonLabel q)) ∧
      (data.vertexPartition (endpoint data hc hab hOne
          ((M₀).sourceEdge (star.edge (model.singletonLabel q))
            (picture.activeSheet (model.singletonLabel q)))).1.1).block
        (endpoint data hc hab hOne ((M₀).sourceEdge (star.edge (model.singletonLabel q))
          (picture.activeSheet (model.singletonLabel q)))).1.2 =
          ((M₀).edgePartition (star.edge (model.singletonLabel q))).block
            (picture.activeSheet (model.singletonLabel q)) ∧
      (data.vertexPartition (endpoint data hc hab hOne
          ((M₀).sourceEdge (star.edge (pairFirst model q))
            (picture.activeSheet (pairFirst model q)))).1.1).block
        (endpoint data hc hab hOne ((M₀).sourceEdge (star.edge (pairFirst model q))
          (picture.activeSheet (pairFirst model q)))).1.2 =
          (mergedPartition data a b).block block.1 := by
  obtain ⟨hSingleton, hPairFirst, hPairSecond, hPairNe, hOpposite, hSame⟩ :=
    canonical_ordering model star q
  exact W4IncomingBlockPictures.nd3_ordered_classes data fd hc hab hOne star hCompat block
    picture (model.singletonLabel q) (pairFirst model q) (pairSecond model q)
    hSingleton hPairFirst hPairSecond hPairNe hOpposite hSame

/-! ### The entirely dangling incoming wall block -/

omit [Fintype coordinate] [DecidableEq coordinate] fd star in
/-- A merged block whose surviving wall valency vanishes has no surviving
retained boundary occurrence at all. -/
theorem dangling_boundaryEdges_eq_empty
    (hZero : nonDanglingValency M₀ (mergedVertex data hc hab hOne block) = 0) :
    boundaryEdges data hc hab hOne (mergedVertex data hc hab hOne block) = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [card_boundaryEdges data hc hab hOne hCompat _]
  exact hZero

omit fd star hCompat in
/-- Every surviving occurrence at a source vertex of an entirely dangling
merged block is one of the block's surviving internal occurrences. -/
theorem nonDanglingIncident_subset_internalEdges
    (hBoundary : boundaryEdges data hc hab hOne (mergedVertex data hc hab hOne block) = ∅)
    (point : data.SourceVertex)
    (hPoint : sourceVertexMap data hc hab hOne point = mergedVertex data hc hab hOne block)
    (edge : data.SourceEdge) (hEdge : edge ∈ nonDanglingIncident data point) :
    edge ∈ internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) := by
  classical
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident data point edge).mp hEdge
  have hEnds : sourceVertexMap data hc hab hOne (data.sourceEnds edge).1 =
      mergedVertex data hc hab hOne block ∨
      sourceVertexMap data hc hab hOne (data.sourceEnds edge).2 =
        mergedVertex data hc hab hOne block :=
    hIncident.imp (fun h ↦ by rw [h]; exact hPoint) (fun h ↦ by rw [h]; exact hPoint)
  by_cases hTarget : edge.1.1 = contracted
  · have hSame := sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne edge hTarget
    refine (mem_internalEdges data hc hab hOne _ edge).mpr ⟨hSurvives, hTarget, ?_⟩
    rcases hEnds with h | h
    · exact h
    · exact hSame.trans h
  · exfalso
    have hMem : edge ∈ boundaryEdges data hc hab hOne (mergedVertex data hc hab hOne block) :=
      (mem_boundaryEdges data hc hab hOne _ edge).mpr ⟨hSurvives, hTarget, hEnds⟩
    rw [hBoundary] at hMem
    exact Finset.notMem_empty _ hMem

/-- **No surviving internal occurrence survives under an entirely dangling
wall block.**  If one did, the pruned-fibre uniqueness would make it the only
surviving occurrence at each of its two ends, and a source vertex of surviving
valency one does not exist in a connected quotient source. -/
theorem dangling_internalEdges_eq_empty
    (hZero : nonDanglingValency M₀ (mergedVertex data hc hab hOne block) = 0) :
    internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = ∅ := by
  classical
  by_contra hNonempty
  obtain ⟨edge, hEdge⟩ := Finset.nonempty_iff_ne_empty.mpr hNonempty
  have hBoundary := dangling_boundaryEdges_eq_empty data hc hab hOne hCompat block hZero
  obtain ⟨hSurvives, hTarget, hMap⟩ := (mem_internalEdges data hc hab hOne _ edge).mp hEdge
  have hSingle : nonDanglingIncident data (data.sourceEnds edge).1 = {edge} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨(mem_nonDanglingIncident data _ edge).mpr ⟨hSurvives, Or.inl rfl⟩, ?_⟩
    intro other hOther
    exact W4IncomingPrunedFibre.internalEdges_subsingleton data fd hc hab hOne star _ other
      (nonDanglingIncident_subset_internalEdges data hc hab hOne block hBoundary _ hMap
        other hOther) edge hEdge
  have hOneValency : nonDanglingValency data (data.sourceEnds edge).1 = 1 := by
    rw [← card_nonDanglingIncident, hSingle, Finset.card_singleton]
  exact NonDanglingValency.nonDanglingValency_ne_one data fd.connected _ hOneValency

/-- With neither boundary nor internal survivors, the whole pruned fibre of an
entirely dangling merged block is empty. -/
theorem dangling_activeFibreVertices_eq_empty
    (hZero : nonDanglingValency M₀ (mergedVertex data hc hab hOne block) = 0) :
    activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) = ∅ := by
  classical
  have hInternal := dangling_internalEdges_eq_empty data fd hc hab hOne star hCompat block hZero
  have hSum := sum_nonDanglingValency_activeFibre data hc hab hOne hCompat
    (mergedVertex data hc hab hOne block)
  rw [hZero, hInternal, Finset.card_empty] at hSum
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro point hPoint
  have hActive := ((mem_activeFibreVertices data hc hab hOne _ point).mp hPoint).2
  have hTerm : nonDanglingValency data point = 0 :=
    (Finset.sum_eq_zero_iff.mp (by simpa using hSum)) point hPoint
  exact hActive hTerm

/-- Every source endpoint above an entirely dangling merged block is inactive. -/
theorem dangling_endpoint_inactive
    (hZero : nonDanglingValency M₀ (mergedVertex data hc hab hOne block) = 0)
    (place : target.V) (hPlace : place = a ∨ place = b) (sheet : Fin degree)
    (hSheet : sheet ∈ (mergedPartition data a b).block block.1) :
    nonDanglingValency data (data.sourceEndpoint place sheet) = 0 := by
  classical
  by_contra hActive
  have hMem := (mem_activeFibreVertices data hc hab hOne _ _).mpr
    ⟨(mem_fibreVertices data hc hab hOne _ _).mp
      (W4IncomingClassUnion.endpoint_mem_fibre data hc hab hOne block place hPlace sheet hSheet),
      hActive⟩
  rw [dangling_activeFibreVertices_eq_empty data fd hc hab hOne star hCompat block hZero] at hMem
  exact Finset.notMem_empty _ hMem

/-- **An entirely dangling incoming wall block is a single sheet.**  Both
endpoint classes of every one of its sheets are singletons by dangling-no-glue,
and the merged class is their join. -/
theorem dangling_mergedBlock_eq_singleton
    (hZero : nonDanglingValency M₀ (mergedVertex data hc hab hOne block) = 0) :
    (mergedPartition data a b).block block.1 = {block.1} := by
  classical
  have hSelf : block.1 ∈ (mergedPartition data a b).block block.1 :=
    (SheetPartition.mem_block_iff _ _ _).mpr rfl
  have hLeft := W4IncomingClassUnion.inactive_endpoint_block data fd hc hab hOne star a
    (Or.inl rfl) block.1
    (dangling_endpoint_inactive data fd hc hab hOne star hCompat block hZero a (Or.inl rfl)
      block.1 hSelf)
  have hRight := W4IncomingClassUnion.inactive_endpoint_block data fd hc hab hOne star b
    (Or.inr rfl) block.1
    (dangling_endpoint_inactive data fd hc hab hOne star hCompat block hZero b (Or.inr rfl)
      block.1 hSelf)
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hSelf, fun other hOther ↦ ?_⟩
  exact (W4IncomingClassUnion.eq_of_join_rel_of_singletons (data.vertexPartition a)
    (data.vertexPartition b) block.1 other hLeft hRight
    ((SheetPartition.mem_block_iff _ _ _).mp hOther)).symm

/-- **The dangling picture's incoming endpoint relation is discrete.**  This
covers every sheet of the merged block, not only the (nonexistent) surviving
flags. -/
theorem dangling_endpoint_rel_iff
    (hZero : nonDanglingValency M₀ (mergedVertex data hc hab hOne block) = 0)
    (place : target.V) (hPlace : place = a ∨ place = b)
    (first second : Fin degree)
    (hFirst : first ∈ (mergedPartition data a b).block block.1) :
    (data.vertexPartition place).Rel first second ↔ first = second := by
  apply W4IncomingBlockRelations.endpoint_rel_iff_eq_of_no_active data fd hc hab hOne star
    block place hPlace ?_ first second hFirst
  intro point hPoint
  rw [dangling_activeFibreVertices_eq_empty data fd hc hab hOne star hCompat block hZero] at hPoint
  exact absurd hPoint (Finset.notMem_empty _)

/-- **The dangling picture's incoming contracted-edge relation is discrete.** -/
theorem dangling_edge_rel_iff
    (hZero : nonDanglingValency M₀ (mergedVertex data hc hab hOne block) = 0)
    (first second : Fin degree)
    (hFirst : first ∈ (mergedPartition data a b).block block.1) :
    (data.edgePartition contracted).Rel first second ↔ first = second :=
  W4IncomingInternalRelations.edge_rel_iff_eq_of_empty data hc hab hOne fd block
    (dangling_internalEdges_eq_empty data fd hc hab hOne star hCompat block hZero) first second
    hFirst

/-! ### Complete blockwise incoming partition tables -/

omit [Fintype coordinate] [DecidableEq coordinate] fd star hCompat in
/-- A partition agreeing with the merged class at one anchor sheet agrees with
it at every sheet of the merged block. -/
theorem block_eq_merged_of_anchor (P : SheetPartition degree) (anchor : Fin degree)
    (hAnchor : P.block anchor = (mergedPartition data a b).block block.1)
    (sheet : Fin degree) (hSheet : sheet ∈ (mergedPartition data a b).block block.1) :
    P.block sheet = (mergedPartition data a b).block block.1 := by
  have hMem : sheet ∈ P.block anchor := by rw [hAnchor]; exact hSheet
  rw [← hAnchor]
  exact (P.block_eq_of_rel ((P.mem_block_iff anchor sheet).mp hMem)).symm

omit [Fintype coordinate] [DecidableEq coordinate] data fd star hCompat block in
/-- The contracted occurrence has exactly two original ends. -/
theorem eq_of_ends {first second place : target.V}
    (hFirst : first = a ∨ first = b) (hSecond : second = a ∨ second = b)
    (hPlace : place = a ∨ place = b) (hNe : first ≠ second) :
    place = first ∨ place = second := by
  rcases hFirst with rfl | rfl <;> rcases hSecond with rfl | rfl <;>
    rcases hPlace with rfl | rfl <;> simp_all

omit hCompat in
/-- Singleton block table at an inactive original endpoint of the merged block. -/
theorem inactive_side_block (place : target.V) (hPlace : place = a ∨ place = b)
    (hNone : ∀ point ∈ activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block), point.1.1 ≠ place)
    (sheet : Fin degree) (hSheet : sheet ∈ (mergedPartition data a b).block block.1) :
    (data.vertexPartition place).block sheet = {sheet} := by
  apply W4IncomingClassUnion.inactive_endpoint_block data fd hc hab hOne star place hPlace sheet
  by_contra hActive
  exact hNone (data.sourceEndpoint place sheet)
    ((mem_activeFibreVertices data hc hab hOne _ _).mpr
      ⟨(mem_fibreVertices data hc hab hOne _ _).mp
        (W4IncomingClassUnion.endpoint_mem_fibre data hc hab hOne block place hPlace sheet hSheet),
        hActive⟩) rfl

/-- **Complete nd2 same-side incoming table.**  The flag-side endpoint carries
the whole merged class on every sheet of the block; the opposite endpoint and
the contracted occurrence are singletons on every sheet, inactive ones
included. -/
theorem nd2_same_partition_table {model : Nd2Block}
    (picture : AuxR0Nd2Picture M₀ star B₀ model)
    (hSide : star.right q (star.edge model.first) = star.right q (star.edge model.second)) :
    (∀ sheet ∈ (mergedPartition data a b).block block.1,
        (data.vertexPartition (endpoint data hc hab hOne picture.first.1).1.1).block sheet =
          (mergedPartition data a b).block block.1) ∧
      (∀ place, (place = a ∨ place = b) →
        place ≠ (endpoint data hc hab hOne picture.first.1).1.1 →
        ∀ sheet ∈ (mergedPartition data a b).block block.1,
          (data.vertexPartition place).block sheet = {sheet}) ∧
      (∀ sheet ∈ (mergedPartition data a b).block block.1,
        (data.edgePartition contracted).block sheet = {sheet}) := by
  classical
  have hNd := nd2_valency M₀ star B₀ picture
  rw [sourceVertex_eq_merged data hc hab hOne block] at hNd
  have hFirst := flag_incident M₀ star B₀ model.first block.1 rfl
  have hSecond := flag_incident M₀ star B₀ model.second block.1 rfl
  rw [sourceVertex_eq_merged data hc hab hOne block] at hFirst hSecond
  have hNe := nd2_flags_ne M₀ star B₀ picture
  obtain ⟨_, hActive, hEmpty, _⟩ := nd2_same_pairing_side data fd hc hab hOne star hCompat block
    hNd picture.first picture.second hNe hFirst hSecond hSide
  obtain ⟨hEndClass, _, _⟩ := nd2_same_side_classes data fd hc hab hOne star hCompat block hNd
    picture.first picture.second hNe hFirst hSecond hSide
  refine ⟨fun sheet hSheet ↦ block_eq_merged_of_anchor data block _ _ hEndClass
      sheet hSheet, fun place hPlace hNePlace sheet hSheet ↦ ?_,
    fun sheet hSheet ↦ W4IncomingInternalRelations.edge_block_eq_singleton_of_empty
      data hc hab hOne fd block hEmpty sheet hSheet⟩
  refine inactive_side_block data fd hc hab hOne star block place hPlace ?_ sheet hSheet
  intro point hPoint
  rw [hActive, Finset.mem_singleton] at hPoint
  rw [hPoint]
  exact fun h ↦ hNePlace h.symm

/-- **Complete nd2 opposite-side incoming table.**  Both original endpoint
partitions and the contracted-edge partition restrict to the whole merged
class on every sheet of the block. -/
theorem nd2_opposite_partition_table {model : Nd2Block}
    (picture : AuxR0Nd2Picture M₀ star B₀ model)
    (hSide : star.right q (star.edge model.first) ≠ star.right q (star.edge model.second)) :
    (∀ place, (place = a ∨ place = b) → ∀ sheet ∈ (mergedPartition data a b).block block.1,
        (data.vertexPartition place).block sheet = (mergedPartition data a b).block block.1) ∧
      (∀ sheet ∈ (mergedPartition data a b).block block.1,
        (data.edgePartition contracted).block sheet =
          (mergedPartition data a b).block block.1) := by
  classical
  have hNd := nd2_valency M₀ star B₀ picture
  rw [sourceVertex_eq_merged data hc hab hOne block] at hNd
  have hFirst := flag_incident M₀ star B₀ model.first block.1 rfl
  have hSecond := flag_incident M₀ star B₀ model.second block.1 rfl
  rw [sourceVertex_eq_merged data hc hab hOne block] at hFirst hSecond
  obtain ⟨edge, hSingle, hEdgeClass, hFirstClass, hSecondClass⟩ :=
    nd2_opposite_side_classes data fd hc hab hOne star hCompat block hNd
      picture.first picture.second hFirst hSecond hSide
  have hSides : (endpoint data hc hab hOne picture.first.1).1.1 ≠
      (endpoint data hc hab hOne picture.second.1).1.1 :=
    (endpoint_side_ne_iff_pairing data fd hc hab hOne star block picture.first.1 picture.second.1
      hFirst hSecond).mpr hSide
  have hEdgeTarget : edge.1.1 = contracted := by
    have hMem : edge ∈ internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) := by
      rw [hSingle]; exact Finset.mem_singleton_self _
    exact ((mem_internalEdges data hc hab hOne _ edge).mp hMem).2.1
  refine ⟨fun place hPlace sheet hSheet ↦ ?_, fun sheet hSheet ↦ ?_⟩
  · rcases eq_of_ends (W4IncomingSheetClasses.endpoint_above data hc hab hOne picture.first.1)
      (W4IncomingSheetClasses.endpoint_above data hc hab hOne picture.second.1)
      hPlace hSides with rfl | rfl
    · exact block_eq_merged_of_anchor data block _ _ hFirstClass sheet hSheet
    · exact block_eq_merged_of_anchor data block _ _ hSecondClass sheet hSheet
  · rw [← hEdgeTarget]
    exact block_eq_merged_of_anchor data block _ _ hEdgeClass sheet hSheet

/-- **Complete dangling incoming table.**  Both endpoint partitions and the
contracted-edge partition are discrete on an entirely dangling merged block --
which is itself a single sheet. -/
theorem dangling_partition_table
    (hZero : nonDanglingValency M₀ (mergedVertex data hc hab hOne block) = 0) :
    (∀ place, (place = a ∨ place = b) → ∀ sheet ∈ (mergedPartition data a b).block block.1,
        (data.vertexPartition place).block sheet = {sheet}) ∧
      (∀ sheet ∈ (mergedPartition data a b).block block.1,
        (data.edgePartition contracted).block sheet = {sheet}) := by
  refine ⟨fun place hPlace sheet hSheet ↦ ?_, fun sheet hSheet ↦
    W4IncomingInternalRelations.edge_block_eq_singleton_of_empty data hc hab hOne fd block
      (dangling_internalEdges_eq_empty data fd hc hab hOne star hCompat block hZero) sheet hSheet⟩
  refine inactive_side_block data fd hc hab hOne star block place hPlace ?_ sheet hSheet
  intro point hPoint
  rw [dangling_activeFibreVertices_eq_empty data fd hc hab hOne star hCompat block hZero] at hPoint
  exact absurd hPoint (Finset.notMem_empty _)

/-- **Complete canonical nd3 incoming table.**  With the singleton/pair
ordering derived rather than assumed, the singleton-side endpoint partition and
the contracted-edge partition both restrict to the literal retained
singleton-branch partition on every sheet of the merged block, while the
pair-side endpoint carries the whole merged class. -/
theorem nd3_canonical_partition_table {model : Nd3Block}
    (picture : AuxR0Nd3Picture M₀ star B₀ model) :
    (∀ sheet ∈ (mergedPartition data a b).block block.1,
        (data.vertexPartition (endpoint data hc hab hOne
            ((M₀).sourceEdge (star.edge (model.singletonLabel q))
              (picture.activeSheet (model.singletonLabel q)))).1.1).block sheet =
          ((M₀).edgePartition (star.edge (model.singletonLabel q))).block sheet) ∧
      (∀ place, (place = a ∨ place = b) →
        place ≠ (endpoint data hc hab hOne
            ((M₀).sourceEdge (star.edge (model.singletonLabel q))
              (picture.activeSheet (model.singletonLabel q)))).1.1 →
        ∀ sheet ∈ (mergedPartition data a b).block block.1,
          (data.vertexPartition place).block sheet = (mergedPartition data a b).block block.1) ∧
      (∀ sheet ∈ (mergedPartition data a b).block block.1,
        (data.edgePartition contracted).block sheet =
          ((M₀).edgePartition (star.edge (model.singletonLabel q))).block sheet) := by
  classical
  obtain ⟨hMem₀, hMem₁, hMem₂, hNeLabels, hOpp, hSame⟩ := canonical_ordering model star q
  have hNd := nd3_valency M₀ star B₀ picture
  rw [sourceVertex_eq_merged data hc hab hOne block] at hNd
  have hInc₀ := nd3_flag_incident M₀ star B₀ picture (model.singletonLabel q) hMem₀
  have hInc₁ := nd3_flag_incident M₀ star B₀ picture (pairFirst model q) hMem₁
  have hInc₂ := nd3_flag_incident M₀ star B₀ picture (pairSecond model q) hMem₂
  rw [sourceVertex_eq_merged data hc hab hOne block] at hInc₀ hInc₁ hInc₂
  obtain ⟨_, _, _, hActive, _, _, _, _⟩ := nd3_singleton_pairing_side data fd hc hab hOne star
    hCompat block hNd (nd3Flag M₀ star B₀ picture (model.singletonLabel q) hMem₀)
    (nd3Flag M₀ star B₀ picture (pairFirst model q) hMem₁)
    (nd3Flag M₀ star B₀ picture (pairSecond model q) hMem₂)
    (nd3_flags_ne M₀ star B₀ picture (pairFirst model q) (pairSecond model q) hMem₁ hMem₂ hNeLabels)
    hInc₀ hInc₁ hInc₂ hOpp hSame
  obtain ⟨edge, hSingle, hEdgeClass, hSmallClass, hLargeClass⟩ :=
    nd3_canonical_classes data fd hc hab hOne star hCompat block picture
  have hActivePair : activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) =
      {endpoint data hc hab hOne ((M₀).sourceEdge (star.edge (model.singletonLabel q))
          (picture.activeSheet (model.singletonLabel q))),
        endpoint data hc hab hOne ((M₀).sourceEdge (star.edge (pairFirst model q))
          (picture.activeSheet (pairFirst model q)))} := hActive
  have hSmallActive : endpoint data hc hab hOne ((M₀).sourceEdge
        (star.edge (model.singletonLabel q)) (picture.activeSheet (model.singletonLabel q))) ∈
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) := by
    rw [hActivePair]
    exact Finset.mem_insert_self _ _
  have hSidesNe : (endpoint data hc hab hOne ((M₀).sourceEdge (star.edge (model.singletonLabel q))
        (picture.activeSheet (model.singletonLabel q)))).1.1 ≠
      (endpoint data hc hab hOne ((M₀).sourceEdge (star.edge (pairFirst model q))
        (picture.activeSheet (pairFirst model q)))).1.1 :=
    (endpoint_side_ne_iff_pairing data fd hc hab hOne star block _ _ hInc₀ hInc₁).mpr hOpp
  have hWallRel : ∀ first : Fin degree, first ∈ (mergedPartition data a b).block block.1 →
      ((M₀).vertexPartition ⟨a, hab⟩).Rel (W4IncomingBlockPictures.wallBlock data hc hab hOne
        block).1 first := by
    intro first hFirst
    have hRel : (mergedPartition data a b).Rel block.1 first :=
      (SheetPartition.mem_block_iff _ _ _).mp hFirst
    have hEq : ((M₀).vertexPartition ⟨a, hab⟩) = mergedPartition data a b :=
      contractDatum_vertexPartition_merge data hc hab hOne
    show ((M₀).vertexPartition ⟨a, hab⟩).repr block.1 =
      ((M₀).vertexPartition ⟨a, hab⟩).repr first
    rw [hEq]
    exact hRel
  have hNoGlueWall : DanglingEdgeNoGlue (M₀) :=
    danglingEdgeNoGlue_contractDatum data hCompat.2 fd.danglingEdgeNoGlue
  -- the literal retained singleton-branch table
  have hFineTable : ∀ sheet ∈ (mergedPartition data a b).block block.1,
      ((M₀).edgePartition (star.edge (model.singletonLabel q))).block sheet =
        if sheet ∈ ((M₀).edgePartition (star.edge (model.singletonLabel q))).block
            (picture.activeSheet (model.singletonLabel q)) then
          ((M₀).edgePartition (star.edge (model.singletonLabel q))).block
            (picture.activeSheet (model.singletonLabel q))
        else {sheet} := by
    intro sheet hSheet
    exact block_eq_ite_of_restricted_rel data block _ _
      (fun first second hFirst ↦ W4RetainedBlockRelations.nd3_rel_iff hNoGlueWall picture
        (model.singletonLabel q) first second (hWallRel first hFirst)) sheet hSheet
  refine ⟨fun sheet hSheet ↦ ?_, fun place hPlace hNePlace sheet hSheet ↦ ?_,
    fun sheet hSheet ↦ ?_⟩
  · rw [hFineTable sheet hSheet]
    refine block_eq_ite_of_restricted_rel data block _ _
      (fun first second hFirst ↦ ?_) sheet hSheet
    rw [W4IncomingBlockRelations.endpoint_rel_iff_of_active data fd hc hab hOne star block _
      (W4IncomingSheetClasses.endpoint_above data hc hab hOne _) _ hSmallActive rfl first second
      hFirst]
    simp only [← SheetPartition.mem_block_iff, hSmallClass]
  · rcases eq_of_ends (W4IncomingSheetClasses.endpoint_above data hc hab hOne _)
      (W4IncomingSheetClasses.endpoint_above data hc hab hOne _) hPlace hSidesNe with rfl | rfl
    · exact absurd rfl hNePlace
    · exact block_eq_merged_of_anchor data block _ _ hLargeClass sheet hSheet
  · rw [hFineTable sheet hSheet]
    refine block_eq_ite_of_restricted_rel data block _ _
      (fun first second hFirst ↦ ?_) sheet hSheet
    rw [← hEdgeClass]
    exact W4IncomingInternalRelations.edge_rel_iff_mem_survivor_block_of_singleton data hc hab hOne
      fd block edge hSingle first second hFirst

/-! ### Cancelling the global endpoint exchange once, for the whole wall -/

omit hCompat block in
/-- The original target end carrying a prescribed side of the canonical W4
pairing.  The possible global endpoint exchange performed by the incoming
target normalization is cancelled here, once, uniformly over the wall. -/
noncomputable def pairingSide (side : Bool) : target.V :=
  if ∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne e = star.right q e then
    (if side then b else a)
  else (if side then a else b)

omit hCompat block in
theorem pairingSide_cases (side : Bool) :
    pairingSide data fd hc hab hOne star side = a ∨
      pairingSide data fd hc hab hOne star side = b := by
  unfold pairingSide
  split <;> cases side <;> simp

omit hCompat block in
theorem pairingSide_ne :
    pairingSide data fd hc hab hOne star false ≠ pairingSide data fd hc hab hOne star true := by
  unfold pairingSide
  split <;> simp [hab, Ne.symm hab]

omit hCompat block in
/-- At every retained wall occurrence the canonical incoming endpoint is the
original end named by that occurrence's pairing side. -/
theorem endpoint_fst_eq_pairingSide (edge : (M₀).SourceEdge)
    (hAt : edge.1.1 ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩) :
    (endpoint data hc hab hOne edge).1.1 =
      pairingSide data fd hc hab hOne star (star.right q edge.1.1) := by
  rw [endpoint_target]
  unfold pairingSide
  by_cases hSupport : ∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne e = star.right q e
  · rw [ite_eq_left hSupport, hSupport _ hAt]
  · rw [ite_eq_right hSupport,
      (W4IncomingTargetNormalization.pairing_placement data fd hc hab hOne star).resolve_left
        hSupport _ hAt]
    cases star.right q edge.1.1 <;> simp

/-! ### Blockwise matching with the candidate's own local resolution -/

omit [Fintype coordinate] [DecidableEq coordinate] fd star hCompat in
theorem wall_block_eq (sheet : Fin degree)
    (hSheet : sheet ∈ (mergedPartition data a b).block block.1) :
    ((M₀).vertexPartition ⟨a, hab⟩).block sheet = (mergedPartition data a b).block block.1 := by
  rw [contractDatum_vertexPartition_merge data hc hab hOne]
  exact ((mergedPartition data a b).block_eq_of_rel
    ((SheetPartition.mem_block_iff _ _ _).mp hSheet)).symm

omit [Fintype coordinate] [DecidableEq coordinate] fd star hCompat in
theorem wall_rel_anchor (sheet : Fin degree)
    (hSheet : sheet ∈ (mergedPartition data a b).block block.1) :
    ((M₀).vertexPartition ⟨a, hab⟩).Rel block.1 sheet := by
  rw [contractDatum_vertexPartition_merge data hc hab hOne]
  exact (SheetPartition.mem_block_iff _ _ _).mp hSheet

/-- **Blockwise nd2 matching.**  On every sheet of the merged block, the two
original endpoint partitions and the contracted-edge partition agree with the
candidate's own local nd2 resolution for the canonical pairing. -/
theorem nd2_local_match {model : Nd2Block}
    (picture : AuxR0Nd2Picture M₀ star B₀ model)
    (sheet : Fin degree) (hSheet : sheet ∈ (mergedPartition data a b).block block.1) :
    (data.vertexPartition (pairingSide data fd hc hab hOne star false)).block sheet =
        (resolutionAt (M₀) star q block.1 (.nd2 model)).left.block sheet ∧
      (data.vertexPartition (pairingSide data fd hc hab hOne star true)).block sheet =
        (resolutionAt (M₀) star q block.1 (.nd2 model)).right.block sheet ∧
      (data.edgePartition contracted).block sheet =
        (resolutionAt (M₀) star q block.1 (.nd2 model)).newEdge.block sheet := by
  classical
  have hWallSheet := wall_block_eq data hc hab hOne block sheet hSheet
  have hSplitSheet := SheetPartition.splitBlock_block_of_rel ((M₀).vertexPartition ⟨a, hab⟩)
    block.1 sheet (wall_rel_anchor data hc hab hOne block sheet hSheet)
  have hFirstSide : (endpoint data hc hab hOne picture.first.1).1.1 =
      pairingSide data fd hc hab hOne star (star.right q (star.edge model.first)) :=
    endpoint_fst_eq_pairingSide data fd hc hab hOne star picture.first.1
      (star.edge_mem_incidentEdges model.first)
  have hSideNe := pairingSide_ne data fd hc hab hOne star
  have hResolution : resolutionAt (M₀) star q block.1 (.nd2 model)
      = nd2Resolution ((M₀).vertexPartition ⟨a, hab⟩) block.1
          (star.right q (star.edge model.first)) (star.right q (star.edge model.second)) := rfl
  rw [hResolution]
  by_cases hSame : star.right q (star.edge model.first) = star.right q (star.edge model.second)
  · obtain ⟨hFlag, hOther, hEdgeTable⟩ :=
      nd2_same_partition_table data fd hc hab hOne star hCompat block picture hSame
    have hFlagAt := hFlag sheet hSheet
    have hEdgeAt := hEdgeTable sheet hSheet
    rw [hFirstSide] at hFlagAt
    have hNew : (nd2Resolution ((M₀).vertexPartition ⟨a, hab⟩) block.1
        (star.right q (star.edge model.first)) (star.right q (star.edge model.second))).newEdge
        = ((M₀).vertexPartition ⟨a, hab⟩).splitBlock block.1 :=
      nd2Resolution_newEdge_of_same _ _ _ _ hSame
    have hActiveEnd := nd2Resolution_activeEndpoint_of_same ((M₀).vertexPartition ⟨a, hab⟩)
      block.1 (star.right q (star.edge model.first)) (star.right q (star.edge model.second)) hSame
    have hOtherEnd := nd2Resolution_otherEndpoint_of_same ((M₀).vertexPartition ⟨a, hab⟩)
      block.1 (star.right q (star.edge model.first)) (star.right q (star.edge model.second)) hSame
    cases hBit : star.right q (star.edge model.first) with
    | false =>
        rw [hBit] at hFlagAt hActiveEnd hOtherEnd hNew
        simp only [Bool.false_eq_true, ite_false] at hActiveEnd hOtherEnd
        refine ⟨?_, ?_, ?_⟩
        · rw [hActiveEnd, hWallSheet]
          exact hFlagAt
        · rw [hOtherEnd, hSplitSheet]
          refine hOther _ (pairingSide_cases data fd hc hab hOne star true) ?_ sheet hSheet
          rw [hFirstSide, hBit]
          exact fun h ↦ hSideNe h.symm
        · rw [hNew, hSplitSheet]
          exact hEdgeAt
    | true =>
        rw [hBit] at hFlagAt hActiveEnd hOtherEnd hNew
        simp only [ite_true] at hActiveEnd hOtherEnd
        refine ⟨?_, ?_, ?_⟩
        · rw [hOtherEnd, hSplitSheet]
          refine hOther _ (pairingSide_cases data fd hc hab hOne star false) ?_ sheet hSheet
          rw [hFirstSide, hBit]
          exact hSideNe
        · rw [hActiveEnd, hWallSheet]
          exact hFlagAt
        · rw [hNew, hSplitSheet]
          exact hEdgeAt
  · obtain ⟨hAll, hEdgeTable⟩ :=
      nd2_opposite_partition_table data fd hc hab hOne star hCompat block picture hSame
    obtain ⟨hLeft, hRight⟩ := nd2Resolution_endpoints_of_ne ((M₀).vertexPartition ⟨a, hab⟩)
      block.1 (star.right q (star.edge model.first)) (star.right q (star.edge model.second)) hSame
    have hNew := nd2Resolution_newEdge_of_ne ((M₀).vertexPartition ⟨a, hab⟩)
      block.1 (star.right q (star.edge model.first)) (star.right q (star.edge model.second)) hSame
    rw [hLeft, hRight, hNew, hWallSheet]
    exact ⟨hAll _ (pairingSide_cases data fd hc hab hOne star false) sheet hSheet,
      hAll _ (pairingSide_cases data fd hc hab hOne star true) sheet hSheet,
      hEdgeTable sheet hSheet⟩

/-- **Blockwise canonical nd3 matching.**  With the singleton/pair ordering
derived, the incoming endpoint and contracted-edge partitions agree on every
sheet of the merged block with the candidate's own local nd3 resolution. -/
theorem nd3_local_match {model : Nd3Block}
    (picture : AuxR0Nd3Picture M₀ star B₀ model)
    (sheet : Fin degree) (hSheet : sheet ∈ (mergedPartition data a b).block block.1) :
    (data.vertexPartition (pairingSide data fd hc hab hOne star false)).block sheet =
        (resolutionAt (M₀) star q block.1 (.nd3 model)).left.block sheet ∧
      (data.vertexPartition (pairingSide data fd hc hab hOne star true)).block sheet =
        (resolutionAt (M₀) star q block.1 (.nd3 model)).right.block sheet ∧
      (data.edgePartition contracted).block sheet =
        (resolutionAt (M₀) star q block.1 (.nd3 model)).newEdge.block sheet := by
  classical
  have hWallSheet := wall_block_eq data hc hab hOne block sheet hSheet
  obtain ⟨hSmall, hLarge, hEdgeTable⟩ :=
    nd3_canonical_partition_table data fd hc hab hOne star hCompat block picture
  have hSmallSide : (endpoint data hc hab hOne ((M₀).sourceEdge
        (star.edge (model.singletonLabel q))
        (picture.activeSheet (model.singletonLabel q)))).1.1 =
      pairingSide data fd hc hab hOne star (star.right q (star.edge (model.singletonLabel q))) :=
    endpoint_fst_eq_pairingSide data fd hc hab hOne star _
      (star.edge_mem_incidentEdges (model.singletonLabel q))
  have hSideNe := pairingSide_ne data fd hc hab hOne star
  have hResolution : resolutionAt (M₀) star q block.1 (.nd3 model)
      = nd3Resolution ((M₀).vertexPartition ⟨a, hab⟩)
          ((M₀).edgePartition (star.edge (model.singletonLabel q)))
          (star.edgePartition_refines_wall (M₀) (model.singletonLabel q))
          (star.right q (star.edge (model.singletonLabel q))) := rfl
  have hEndpoints := nd3Resolution_endpoint_partitions ((M₀).vertexPartition ⟨a, hab⟩)
    ((M₀).edgePartition (star.edge (model.singletonLabel q)))
    (star.edgePartition_refines_wall (M₀) (model.singletonLabel q))
    (star.right q (star.edge (model.singletonLabel q)))
  have hNew := nd3Resolution_newEdge ((M₀).vertexPartition ⟨a, hab⟩)
    ((M₀).edgePartition (star.edge (model.singletonLabel q)))
    (star.edgePartition_refines_wall (M₀) (model.singletonLabel q))
    (star.right q (star.edge (model.singletonLabel q)))
  have hSmallAt := hSmall sheet hSheet
  have hEdgeAt := hEdgeTable sheet hSheet
  rw [hSmallSide] at hSmallAt
  rw [hResolution]
  cases hBit : star.right q (star.edge (model.singletonLabel q)) with
  | false =>
      rw [hBit] at hSmallAt hEndpoints hNew
      simp only [Bool.false_eq_true, ite_false] at hEndpoints
      obtain ⟨hFine, hWall⟩ := hEndpoints
      refine ⟨?_, ?_, ?_⟩
      · rw [hFine]
        exact hSmallAt
      · rw [hWall, hWallSheet]
        refine hLarge _ (pairingSide_cases data fd hc hab hOne star true) ?_ sheet hSheet
        rw [hSmallSide, hBit]
        exact fun h ↦ hSideNe h.symm
      · rw [hNew]
        exact hEdgeAt
  | true =>
      rw [hBit] at hSmallAt hEndpoints hNew
      simp only [ite_true] at hEndpoints
      obtain ⟨hFine, hWall⟩ := hEndpoints
      refine ⟨?_, ?_, ?_⟩
      · rw [hWall, hWallSheet]
        refine hLarge _ (pairingSide_cases data fd hc hab hOne star false) ?_ sheet hSheet
        rw [hSmallSide, hBit]
        exact hSideNe
      · rw [hFine]
        exact hSmallAt
      · rw [hNew]
        exact hEdgeAt

/-- **Blockwise dangling matching.**  An entirely dangling merged block is a
single sheet, so every W4 nd2 pattern -- in particular the harmless one the
candidate construction assigns to a dangling block -- reproduces the discrete
incoming tables. -/
theorem dangling_local_match
    (hZero : nonDanglingValency M₀ (mergedVertex data hc hab hOne block) = 0)
    (model : Nd2Block)
    (sheet : Fin degree) (hSheet : sheet ∈ (mergedPartition data a b).block block.1) :
    (data.vertexPartition (pairingSide data fd hc hab hOne star false)).block sheet =
        (resolutionAt (M₀) star q block.1 (.nd2 model)).left.block sheet ∧
      (data.vertexPartition (pairingSide data fd hc hab hOne star true)).block sheet =
        (resolutionAt (M₀) star q block.1 (.nd2 model)).right.block sheet ∧
      (data.edgePartition contracted).block sheet =
        (resolutionAt (M₀) star q block.1 (.nd2 model)).newEdge.block sheet := by
  classical
  have hSingleton := dangling_mergedBlock_eq_singleton data fd hc hab hOne star hCompat block hZero
  have hEq : sheet = block.1 := by
    have hMem := hSheet
    rw [hSingleton, Finset.mem_singleton] at hMem
    exact hMem
  have hWallSheet : ((M₀).vertexPartition ⟨a, hab⟩).block sheet = {sheet} := by
    rw [wall_block_eq data hc hab hOne block sheet hSheet, hSingleton, hEq]
  have hSplitSheet := SheetPartition.splitBlock_block_of_rel ((M₀).vertexPartition ⟨a, hab⟩)
    block.1 sheet (wall_rel_anchor data hc hab hOne block sheet hSheet)
  obtain ⟨hAll, hEdgeTable⟩ :=
    dangling_partition_table data fd hc hab hOne star hCompat block hZero
  have hResolution : resolutionAt (M₀) star q block.1 (.nd2 model)
      = nd2Resolution ((M₀).vertexPartition ⟨a, hab⟩) block.1
          (star.right q (star.edge model.first)) (star.right q (star.edge model.second)) := rfl
  obtain ⟨hLeft, hRight, hNewSide⟩ := nd2Resolution_sides ((M₀).vertexPartition ⟨a, hab⟩) block.1
    (star.right q (star.edge model.first)) (star.right q (star.edge model.second))
  have hSide : ∀ P : SheetPartition degree,
      (P = (M₀).vertexPartition ⟨a, hab⟩ ∨
        P = ((M₀).vertexPartition ⟨a, hab⟩).splitBlock block.1) → P.block sheet = {sheet} := by
    rintro P (rfl | rfl)
    · exact hWallSheet
    · exact hSplitSheet
  rw [hResolution]
  exact ⟨(hAll _ (pairingSide_cases data fd hc hab hOne star false) sheet hSheet).trans
      (hSide _ hLeft).symm,
    (hAll _ (pairingSide_cases data fd hc hab hOne star true) sheet hSheet).trans
      (hSide _ hRight).symm,
    (hEdgeTable sheet hSheet).trans (hSide _ hNewSide).symm⟩

/-! ### Exhaustive matching over the whole incoming wall -/

omit [Fintype coordinate] [DecidableEq coordinate] fd hCompat block in
/-- The candidate's blockwise W4 pattern, read off the actual auxiliary
picture of every wall block. -/
noncomputable def blockPattern
    (pictures : ∀ sourceBlock : WallBlock (M₀) ⟨a, hab⟩,
      AuxR0BlockPicture (M₀) star sourceBlock) (sheet : Fin degree) : BlockPattern :=
  (pictures (WallBlock.ofSheet (M₀) ⟨a, hab⟩ sheet)).pattern

omit block in
/-- **Exhaustive incoming endpoint and contracted-edge identification.**  Given
the actual auxiliary picture of every wall block, both original endpoint
partitions and the contracted-edge partition have exactly the blocks of the
canonical candidate's pasted W4 resolution -- at every sheet, including the
inactive sheets of active blocks and the entirely dangling blocks. -/
theorem partition_block_matching
    (pictures : ∀ sourceBlock : WallBlock (M₀) ⟨a, hab⟩,
      AuxR0BlockPicture (M₀) star sourceBlock) (sheet : Fin degree) :
    (data.vertexPartition (pairingSide data fd hc hab hOne star false)).block sheet =
        (wholeResolution (M₀) star
          (blockPattern data hc hab hOne star pictures) q).left.block sheet ∧
      (data.vertexPartition (pairingSide data fd hc hab hOne star true)).block sheet =
        (wholeResolution (M₀) star
          (blockPattern data hc hab hOne star pictures) q).right.block sheet ∧
      (data.edgePartition contracted).block sheet =
        (wholeResolution (M₀) star
          (blockPattern data hc hab hOne star pictures) q).newEdge.block sheet := by
  classical
  have hSheet : sheet ∈ (mergedPartition data a b).block
      ((mergedPartition data a b).toBlock sheet).1 :=
    (SheetPartition.mem_block_iff _ _ _).mpr ((mergedPartition data a b).rel_repr_left sheet)
  have hAnchor : ((M₀).vertexPartition ⟨a, hab⟩).repr sheet =
      ((mergedPartition data a b).toBlock sheet).1 := by
    rw [contractDatum_vertexPartition_merge data hc hab hOne]
    rfl
  have hOfSheet : WallBlock.ofSheet (M₀) ⟨a, hab⟩ (((M₀).vertexPartition ⟨a, hab⟩).repr sheet)
      = W4IncomingBlockPictures.wallBlock data hc hab hOne
        ((mergedPartition data a b).toBlock sheet) := by
    apply Subtype.ext
    change ((M₀).vertexPartition ⟨a, hab⟩).repr (((M₀).vertexPartition ⟨a, hab⟩).repr sheet) =
      ((mergedPartition data a b).toBlock sheet).1
    rw [SheetPartition.repr_idem]
    exact hAnchor
  have hPatternAt : blockPattern data hc hab hOne star pictures
      (((M₀).vertexPartition ⟨a, hab⟩).repr sheet) =
      (pictures (W4IncomingBlockPictures.wallBlock data hc hab hOne
        ((mergedPartition data a b).toBlock sheet))).pattern := by
    unfold blockPattern
    rw [hOfSheet]
  rw [W4StableGraph.wholeResolution_left_block (M₀) star
      (blockPattern data hc hab hOne star pictures) q sheet,
    W4StableGraph.wholeResolution_right_block (M₀) star
      (blockPattern data hc hab hOne star pictures) q sheet,
    W4StableGraph.wholeResolution_newEdge_block (M₀) star
      (blockPattern data hc hab hOne star pictures) q sheet]
  unfold blockwiseResolution
  rw [hPatternAt, hAnchor]
  cases hPic : pictures (W4IncomingBlockPictures.wallBlock data hc hab hOne
      ((mergedPartition data a b).toBlock sheet)) with
  | dangling oldDangling =>
      have hZero := dangling_valency (M₀) star (W4IncomingBlockPictures.wallBlock data hc hab hOne
        ((mergedPartition data a b).toBlock sheet)) oldDangling
      rw [sourceVertex_eq_merged data hc hab hOne ((mergedPartition data a b).toBlock sheet)]
        at hZero
      exact dangling_local_match data fd hc hab hOne star hCompat
        ((mergedPartition data a b).toBlock sheet) hZero
        W4SourceClassification.ActiveBlockClassification.danglingBlock sheet hSheet
  | nd2 model picture =>
      exact nd2_local_match data fd hc hab hOne star hCompat
        ((mergedPartition data a b).toBlock sheet) picture sheet hSheet
  | nd3 model picture =>
      exact nd3_local_match data fd hc hab hOne star hCompat
        ((mergedPartition data a b).toBlock sheet) picture sheet hSheet

omit block in
/-- **Exhaustive global endpoint and internal `SameBlocks`.**  The two original
endpoint partitions and the contracted-edge partition of the incoming datum
have exactly the blocks of the canonical candidate's pasted W4 resolution for
the normalized pairing.  Only the actual auxiliary picture of each wall block
is consumed; no cover equality, no-return, or row-matching premise is added.
Stored-representative normalization is a further step and is not claimed here. -/
theorem partition_sameBlocks
    (pictures : ∀ sourceBlock : WallBlock (M₀) ⟨a, hab⟩,
      AuxR0BlockPicture (M₀) star sourceBlock) :
    (data.vertexPartition (pairingSide data fd hc hab hOne star false)).SameBlocks
        (wholeResolution (M₀) star (blockPattern data hc hab hOne star pictures) q).left ∧
      (data.vertexPartition (pairingSide data fd hc hab hOne star true)).SameBlocks
        (wholeResolution (M₀) star (blockPattern data hc hab hOne star pictures) q).right ∧
      (data.edgePartition contracted).SameBlocks
        (wholeResolution (M₀) star (blockPattern data hc hab hOne star pictures) q).newEdge :=
  ⟨sameBlocks_of_block_eq (fun sheet ↦
      (partition_block_matching data fd hc hab hOne star hCompat pictures sheet).1),
    sameBlocks_of_block_eq (fun sheet ↦
      (partition_block_matching data fd hc hab hOne star hCompat pictures sheet).2.1),
    sameBlocks_of_block_eq (fun sheet ↦
      (partition_block_matching data fd hc hab hOne star hCompat pictures sheet).2.2)⟩

end Incoming

end DraismaVargas.LocalCases.W4IncomingGlobalMatching
