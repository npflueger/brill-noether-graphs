module

public import DraismaVargas.LocalCases.W4IncomingPrunedFibre

@[expose] public section

/-!
# Incoming contracted-edge relations on each merged sheet block

Source: Draisma--Vargas Part I, the non-dangling union lemma
(`lemma-class-union`) and Case `{aux-r0}`. Every canonical contracted occurrence
in a merged block lies in its actual full fibre. If it is not among the
surviving internal occurrences, it dangles and dangling-no-glue makes its sheet
block singleton. Thus an empty survivor set gives the discrete relation; a
singleton survivor set gives its literal sheet block plus singleton classes
elsewhere.

The relation proofs do not need a new no-return, connectivity, compatibility,
or partition-matching assumption. Their internal-set receipts are the actual
finsets classified by `W4IncomingPrunedFibre`; the last corollary derives the
singleton receipt from membership in an incoming W4 fibre.
-/

namespace DraismaVargas.LocalCases.W4IncomingInternalRelations

open DraismaVargas.Infrastructure GraphContraction GluingContraction ContractionRamification
open W4StableSource FullDimensionalSource FullContractionFibre PrunedFibreValency PrunedFibreTree

variable {target : CFGraph} {degree : ℕ}

section Fibre

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

include hc in
/-- The actual same-sheet contracted occurrence belongs to the full fibre
specified by its merged sheet block. -/
theorem sourceEdge_mem_fullInternalEdges
    (block : (mergedPartition data a b).Blocks) (sheet : Fin degree)
    (hSheet : sheet ∈ (mergedPartition data a b).block block.1) :
    data.sourceEdge contracted sheet ∈ fullInternalEdges data contracted block := by
  apply (mem_fullInternalEdges_iff data contracted block _).mpr
  refine ⟨rfl, ?_⟩
  have hRel := ((mergedPartition data a b).mem_block_iff block.1 sheet).mp hSheet
  have hRefines := edgePartition_refines_mergedPartition data hc
  exact (hRefines.rel ((data.edgePartition contracted).rel_repr_left sheet)).trans
    (hRel.symm.trans block.2)

/-- Inside a specified merged block, belonging to the actual pruned
internal-edge set is exactly survival of the canonical occurrence. -/
theorem sourceEdge_mem_internalEdges_iff
    (block : (mergedPartition data a b).Blocks) (sheet : Fin degree)
    (hSheet : sheet ∈ (mergedPartition data a b).block block.1) :
    data.sourceEdge contracted sheet ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne block) ↔
      ¬ IsDangling data (data.sourceEdge contracted sheet) := by
  constructor
  · intro h
    exact ((mem_internalEdges data hc hab hOne _ _).mp h).1
  · intro hSurvives
    have hEnds := (sourceEnds_mem_fibre_mergedVertex_iff data hc hab hOne block _).mpr
      (sourceEdge_mem_fullInternalEdges data hc block sheet hSheet)
    exact (mem_internalEdges data hc hab hOne _ _).mpr
      ⟨hSurvives, rfl, (mem_fibreVertices data hc hab hOne _ _).mp hEnds.1⟩

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (fd : FullDimensionalSourcePresentation data coordinate)

include fd

/-- Any dangling canonical contracted occurrence is literally a singleton
sheet block, by the incoming dangling-no-glue theorem. -/
theorem block_eq_singleton_of_dangling (sheet : Fin degree)
    (hDangling : IsDangling data (data.sourceEdge contracted sheet)) :
    (data.edgePartition contracted).block sheet = {sheet} := by
  have hIndex := fd.danglingEdgeNoGlue (data.sourceEdge contracted sheet) hDangling
  rw [GluingDatum.sourceEdgeIndex_sourceEdge] at hIndex
  exact (data.edgePartition contracted).block_eq_singleton_of_blockCard_eq_one sheet hIndex

/-- With no surviving internal occurrence, every sheet class in the merged
block is singleton. No hypothesis on a second sheet is necessary. -/
theorem edge_block_eq_singleton_of_empty
    (block : (mergedPartition data a b).Blocks)
    (hEmpty : internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = ∅)
    (sheet : Fin degree) (hSheet : sheet ∈ (mergedPartition data a b).block block.1) :
    (data.edgePartition contracted).block sheet = {sheet} := by
  apply block_eq_singleton_of_dangling data fd sheet
  by_contra hSurvives
  have hMem := (sourceEdge_mem_internalEdges_iff data hc hab hOne block sheet hSheet).mpr hSurvives
  rw [hEmpty] at hMem
  exact Finset.notMem_empty _ hMem

theorem edge_rel_iff_eq_of_empty
    (block : (mergedPartition data a b).Blocks)
    (hEmpty : internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = ∅)
    (first second : Fin degree) (hFirst : first ∈ (mergedPartition data a b).block block.1) :
    (data.edgePartition contracted).Rel first second ↔ first = second := by
  rw [← SheetPartition.mem_block_iff,
    edge_block_eq_singleton_of_empty data hc hab hOne fd block hEmpty first hFirst,
    Finset.mem_singleton]
  exact eq_comm

omit [Fintype coordinate] [DecidableEq coordinate] fd in
/-- Every other canonical contracted occurrence in this merged block is
dangling; this is derived from actual internal-set membership. -/
theorem isDangling_of_sourceEdge_ne
    (block : (mergedPartition data a b).Blocks) (survivor : data.SourceEdge)
    (hSingle : internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = {survivor})
    (sheet : Fin degree) (hSheet : sheet ∈ (mergedPartition data a b).block block.1)
    (hNe : data.sourceEdge contracted sheet ≠ survivor) :
    IsDangling data (data.sourceEdge contracted sheet) := by
  by_contra hSurvives
  have hMem := (sourceEdge_mem_internalEdges_iff data hc hab hOne block sheet hSheet).mpr hSurvives
  rw [hSingle, Finset.mem_singleton] at hMem
  exact hNe hMem

theorem edge_block_eq_singleton_of_sourceEdge_ne
    (block : (mergedPartition data a b).Blocks) (survivor : data.SourceEdge)
    (hSingle : internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = {survivor})
    (sheet : Fin degree) (hSheet : sheet ∈ (mergedPartition data a b).block block.1)
    (hNe : data.sourceEdge contracted sheet ≠ survivor) :
    (data.edgePartition contracted).block sheet = {sheet} :=
  block_eq_singleton_of_dangling data fd sheet
    (isDangling_of_sourceEdge_ne data hc hab hOne block survivor hSingle sheet hSheet hNe)

/-- The full restricted relation consists of the one actual surviving
sheet block and singleton classes elsewhere in the merged block. -/
theorem edge_rel_iff_of_singleton
    (block : (mergedPartition data a b).Blocks) (survivor : data.SourceEdge)
    (hSingle : internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = {survivor})
    (first second : Fin degree) (hFirst : first ∈ (mergedPartition data a b).block block.1) :
    (data.edgePartition contracted).Rel first second ↔
      first = second ∨ ((data.edgePartition contracted).Rel survivor.1.2 first ∧
        (data.edgePartition contracted).Rel survivor.1.2 second) := by
  constructor
  · intro hRel
    by_cases hDangling : IsDangling data (data.sourceEdge contracted first)
    · have hMem := ((data.edgePartition contracted).mem_block_iff first second).mpr hRel
      rw [block_eq_singleton_of_dangling data fd first hDangling, Finset.mem_singleton] at hMem
      exact Or.inl hMem.symm
    · have hMem := (sourceEdge_mem_internalEdges_iff data hc hab hOne block first hFirst).mpr hDangling
      rw [hSingle, Finset.mem_singleton] at hMem
      have hRepr : (data.edgePartition contracted).repr first = survivor.1.2 :=
        congrArg (fun edge : data.SourceEdge ↦ edge.1.2) hMem
      have hFirstRel : (data.edgePartition contracted).Rel survivor.1.2 first := by
        rw [← hRepr]
        exact (data.edgePartition contracted).rel_repr_left first
      exact Or.inr ⟨hFirstRel, hFirstRel.trans hRel⟩
  · rintro (rfl | ⟨hFirstRel, hSecondRel⟩)
    · rfl
    · exact hFirstRel.symm.trans hSecondRel

/-- The sheet-set version selects the surviving block or a singleton.
This identifies the whole restricted edge partition, including inactive sheets. -/
theorem edge_block_eq_ite_of_singleton
    (block : (mergedPartition data a b).Blocks) (survivor : data.SourceEdge)
    (hSingle : internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = {survivor})
    (sheet : Fin degree) (hSheet : sheet ∈ (mergedPartition data a b).block block.1) :
    (data.edgePartition contracted).block sheet =
      if (data.edgePartition contracted).Rel survivor.1.2 sheet then
        (data.edgePartition contracted).block survivor.1.2 else {sheet} := by
  classical
  by_cases hRel : (data.edgePartition contracted).Rel survivor.1.2 sheet
  · rw [ite_eq_left hRel]
    exact (data.edgePartition contracted).block_eq_of_rel hRel.symm
  · rw [ite_eq_right hRel]
    ext other
    rw [SheetPartition.mem_block_iff, Finset.mem_singleton,
      edge_rel_iff_of_singleton data hc hab hOne fd block survivor hSingle sheet other hSheet]
    simp only [hRel, false_and, or_false]
    exact eq_comm

/-- Membership in the surviving block can be stated using the survivor's
own target occurrence and sheet representative. -/
theorem edge_rel_iff_mem_survivor_block_of_singleton
    (block : (mergedPartition data a b).Blocks) (survivor : data.SourceEdge)
    (hSingle : internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = {survivor})
    (first second : Fin degree) (hFirst : first ∈ (mergedPartition data a b).block block.1) :
    (data.edgePartition contracted).Rel first second ↔ first = second ∨
      (first ∈ (data.edgePartition survivor.1.1).block survivor.1.2 ∧
        second ∈ (data.edgePartition survivor.1.1).block survivor.1.2) := by
  have hMem : survivor ∈ internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) := by
    rw [hSingle]
    exact Finset.mem_singleton_self _
  have hTarget := ((mem_internalEdges data hc hab hOne _ _).mp hMem).2.1
  rw [hTarget]
  simpa only [SheetPartition.mem_block_iff] using
    edge_rel_iff_of_singleton data hc hab hOne fd block survivor hSingle first second hFirst

/-- The actual W4 fibre theorem supplies the singleton census from one
surviving member, so this consumer assumes no whole internal-edge picture. -/
theorem edge_rel_iff_of_internal
    (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)
    (block : (mergedPartition data a b).Blocks) (survivor : data.SourceEdge)
    (hMember : survivor ∈ internalEdges data hc hab hOne (mergedVertex data hc hab hOne block))
    (first second : Fin degree) (hFirst : first ∈ (mergedPartition data a b).block block.1) :
    (data.edgePartition contracted).Rel first second ↔ first = second ∨
      (first ∈ (data.edgePartition survivor.1.1).block survivor.1.2 ∧
        second ∈ (data.edgePartition survivor.1.1).block survivor.1.2) := by
  have hSingle : internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = {survivor} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hMember, fun other hOther ↦
      W4IncomingPrunedFibre.internalEdges_subsingleton data fd hc hab hOne star
        (mergedVertex data hc hab hOne block) other hOther survivor hMember⟩
  exact edge_rel_iff_mem_survivor_block_of_singleton data hc hab hOne fd block survivor hSingle first second hFirst

end Fibre

end DraismaVargas.LocalCases.W4IncomingInternalRelations
