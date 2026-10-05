module

public import DraismaVargas.LocalCases.W4StableSource

@[expose] public section

/-!
# Complete retained branch relations from the source survivor census

In Draisma--Vargas Part I's auxiliary Case {aux-r0-nd3} (used in Case {w4}),
the canonical fine partition is the singleton-side old
edge partition. Its one surviving class is accompanied by singleton dangling
classes. The actual picture's complete occurrence census and dangling-no-glue prove
this relation identity, including sheets not on the surviving occurrence.
-/

namespace DraismaVargas.LocalCases.W4RetainedBlockRelations

open DraismaVargas.Infrastructure W4Assembly W4StableSource

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

/-- A single surviving occurrence in the specified old wall block identifies
the whole restricted retained-edge relation, because all other classes dangle. -/
theorem rel_iff_of_unique_survivor
    (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (block : WallBlock data wall) (edge : target.edges) (survivor : data.SourceEdge)
    (hUnique : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel block.1 sheet →
      ¬ IsDangling data (data.sourceEdge edge sheet) → data.sourceEdge edge sheet = survivor)
    (first second : Fin degree) (hFirst : (data.vertexPartition wall).Rel block.1 first) :
    (data.edgePartition edge).Rel first second ↔ first = second ∨
      ((data.edgePartition edge).Rel survivor.1.2 first ∧
        (data.edgePartition edge).Rel survivor.1.2 second) := by
  constructor
  · intro hRel
    by_cases hDangling : IsDangling data (data.sourceEdge edge first)
    · have hIndex := hNoGlue (data.sourceEdge edge first) hDangling
      rw [GluingDatum.sourceEdgeIndex_sourceEdge] at hIndex
      have hBlock := (data.edgePartition edge).block_eq_singleton_of_blockCard_eq_one first hIndex
      have hMem := (SheetPartition.mem_block_iff _ _ _).mpr hRel
      rw [hBlock, Finset.mem_singleton] at hMem
      exact Or.inl hMem.symm
    · have hEq := hUnique first hFirst hDangling
      have hRepr : (data.edgePartition edge).repr first = survivor.1.2 :=
        congrArg (fun e : data.SourceEdge ↦ e.1.2) hEq
      have hRoot : (data.edgePartition edge).Rel survivor.1.2 first := by
        rw [← hRepr]
        exact SheetPartition.rel_repr_left _ _
      exact Or.inr ⟨hRoot, hRoot.trans hRel⟩
  · rintro (rfl | ⟨hFirst, hSecond⟩)
    · rfl
    · exact hFirst.symm.trans hSecond

/-- The actual nd3 picture has only its named surviving occurrence on each
active target branch. Canonical source representatives remain in the same
wall block by exterior refinement. -/
theorem nd3_unique_survivor
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {sourceBlock : WallBlock data wall} {block : Nd3Block}
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (label : Fin 4) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet)
    (hSurvives : ¬ IsDangling data (data.sourceEdge (star.edge label) sheet)) :
    data.sourceEdge (star.edge label) sheet =
      data.sourceEdge (star.edge label) (picture.activeSheet label) := by
  have hRefines := star.edgePartition_refines_wall data label
  have hRoot : (data.vertexPartition wall).Rel sourceBlock.1
      (data.sourceEdge (star.edge label) sheet).1.2 :=
    hSheet.trans (hRefines.rel (SheetPartition.rel_repr_right _ _))
  have hBlock := WallBlock.ofSheet_eq_of_rel data wall sourceBlock _ hRoot
  obtain ⟨other, _, hEq⟩ := picture.only_surviving _ hBlock ⟨label, rfl⟩ hSurvives
  have hLabel : label = other := star.edge_injective
    (congrArg (fun e : data.SourceEdge ↦ e.1.1) hEq)
  subst other
  exact hEq

/-- The fine partition used by the actual nd3 candidate is exactly its
surviving branch class plus singleton classes on all other wall sheets. -/
theorem nd3_rel_iff
    {data : GluingDatum target degree} (hNoGlue : DanglingEdgeNoGlue data)
    {star : W4TargetPairings.FourStar target wall}
    {sourceBlock : WallBlock data wall} {block : Nd3Block}
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (label : Fin 4) (first second : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel sourceBlock.1 first) :
    (data.edgePartition (star.edge label)).Rel first second ↔ first = second ∨
      (first ∈ (data.edgePartition (star.edge label)).block (picture.activeSheet label) ∧
        second ∈ (data.edgePartition (star.edge label)).block (picture.activeSheet label)) := by
  have h := rel_iff_of_unique_survivor data hNoGlue sourceBlock (star.edge label)
    (data.sourceEdge (star.edge label) (picture.activeSheet label))
    (nd3_unique_survivor picture label) first second hFirst
  simpa only [SheetPartition.mem_block_iff, GluingDatum.sourceEdge,
    SheetPartition.Rel, SheetPartition.repr_idem] using h

end DraismaVargas.LocalCases.W4RetainedBlockRelations
