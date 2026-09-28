import DraismaVargas.Infrastructure.GluingDatum

/-!
# Ramification change of a gluing datum

This file gives the source quantities used in the Draisma--Vargas dimension
formula names in the literal sheet-partition model.  The local ramification
at a source block is the Riemann--Hurwitz residual.  Summing over the blocks
above one target vertex gives its `targetChange`; adding the target valency
minus three gives the correction term in the dimension formula.

These definitions are deliberately independent of the wall case analysis.
In particular, Equation (C) of Draisma--Vargas Part I, for a codimension-one
limit, can be stated as `targetExcess = 1` before specializing to a four-valent
wall.
-/

namespace DraismaVargas.Infrastructure

namespace SheetPartition

variable {degree : ℕ}

/-- Send a fine partition block to the unique coarse block containing it. -/
def fineBlockToCoarseBlock (fine coarse : SheetPartition degree)
    (sourceBlock : fine.Blocks) : coarse.Blocks :=
  coarse.toBlock sourceBlock.1

/-- The block map is characterized by coarse equivalence of the two canonical
representatives. -/
theorem fineBlockToCoarseBlock_eq_iff_rel
    (fine coarse : SheetPartition degree)
    (fineBlock : fine.Blocks) (coarseBlock : coarse.Blocks) :
    fineBlockToCoarseBlock fine coarse fineBlock = coarseBlock ↔
      coarse.Rel coarseBlock.1 fineBlock.1 := by
  constructor
  · intro h
    have hValue := congrArg Subtype.val h
    exact coarseBlock.2.trans hValue.symm
  · intro hRel
    apply Subtype.ext
    exact hRel.symm.trans coarseBlock.2

/-- Fine blocks lying inside one specified coarse block. -/
noncomputable def blocksWithin (fine coarse : SheetPartition degree)
    (coarseBlock : coarse.Blocks) : Finset fine.Blocks := by
  classical
  exact Finset.univ.filter fun fineBlock ↦
    fineBlockToCoarseBlock fine coarse fineBlock = coarseBlock

@[simp] theorem mem_blocksWithin (fine coarse : SheetPartition degree)
    (coarseBlock : coarse.Blocks) (fineBlock : fine.Blocks) :
    fineBlock ∈ blocksWithin fine coarse coarseBlock ↔
      fineBlockToCoarseBlock fine coarse fineBlock = coarseBlock := by
  classical
  simp [blocksWithin]

/-- `blockCountWithin` is the cardinality of the literal finite fibre of the
map from fine blocks to coarse blocks. -/
theorem card_blocksWithin_eq_blockCountWithin
    (fine coarse : SheetPartition degree) (hRefines : fine.Refines coarse)
    (coarseBlock : coarse.Blocks) :
    (blocksWithin fine coarse coarseBlock).card =
      fine.blockCountWithin coarse coarseBlock.1 := by
  classical
  have hImage :
      (blocksWithin fine coarse coarseBlock).image Subtype.val =
        (coarse.block coarseBlock.1).image fine.repr := by
    ext representative
    constructor
    · intro hRepresentative
      obtain ⟨fineBlock, hFineBlock, hValue⟩ :=
        Finset.mem_image.mp hRepresentative
      have hMap :=
        (mem_blocksWithin fine coarse coarseBlock fineBlock).mp hFineBlock
      have hCoarse : coarse.Rel coarseBlock.1 fineBlock.1 :=
        (fineBlockToCoarseBlock_eq_iff_rel fine coarse fineBlock
          coarseBlock).mp hMap
      apply Finset.mem_image.mpr
      refine ⟨fineBlock.1,
        (coarse.mem_block_iff coarseBlock.1 fineBlock.1).mpr hCoarse, ?_⟩
      exact fineBlock.2.trans hValue
    · intro hRepresentative
      obtain ⟨sheet, hSheet, hValue⟩ :=
        Finset.mem_image.mp hRepresentative
      let fineBlock : fine.Blocks := fine.toBlock sheet
      have hCoarseSheet : coarse.Rel coarseBlock.1 sheet :=
        (coarse.mem_block_iff coarseBlock.1 sheet).mp hSheet
      have hFine : fine.Rel fineBlock.1 sheet := fine.rel_repr_left sheet
      have hCoarseFine : coarse.Rel fineBlock.1 sheet := hRefines.rel hFine
      have hCoarseBlock : coarse.Rel coarseBlock.1 fineBlock.1 :=
        hCoarseSheet.trans hCoarseFine.symm
      apply Finset.mem_image.mpr
      refine ⟨fineBlock,
        (mem_blocksWithin fine coarse coarseBlock fineBlock).mpr ?_, ?_⟩
      · exact (fineBlockToCoarseBlock_eq_iff_rel fine coarse fineBlock
          coarseBlock).mpr hCoarseBlock
      · exact hValue
  calc
    (blocksWithin fine coarse coarseBlock).card =
        ((blocksWithin fine coarse coarseBlock).image Subtype.val).card := by
      symm
      exact Finset.card_image_of_injective _ Subtype.val_injective
    _ = ((coarse.block coarseBlock.1).image fine.repr).card := by rw [hImage]
    _ = fine.blockCountWithin coarse coarseBlock.1 := rfl

/-- A refinement's blocks are counted wall block by wall block.

This is a general statement about `SheetPartition`; it is used by the non-star
local resolution of Position II.b in Part I's Case {w3}. -/
theorem card_blocks_eq_sum_blockCountWithin (fine coarse : SheetPartition degree)
    (hRefines : fine.Refines coarse) :
    Fintype.card fine.Blocks =
      ∑ block : coarse.Blocks, fine.blockCountWithin coarse block.1 := by
  classical
  rw [← Finset.card_univ]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := SheetPartition.fineBlockToCoarseBlock fine coarse)
    (t := (Finset.univ : Finset coarse.Blocks)) (fun x _ ↦ Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro block _
  rw [← SheetPartition.card_blocksWithin_eq_blockCountWithin fine coarse hRefines block]
  congr 1

/-- Summing the numbers of fine blocks inside all coarse blocks recovers the
total number of fine blocks. -/
theorem sum_blockCountWithin_eq_card_blocks
    (fine coarse : SheetPartition degree) (hRefines : fine.Refines coarse) :
    (∑ coarseBlock : coarse.Blocks,
      fine.blockCountWithin coarse coarseBlock.1) =
        Fintype.card fine.Blocks := by
  classical
  have hFibres := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset fine.Blocks))
    (t := (Finset.univ : Finset coarse.Blocks))
    (f := fineBlockToCoarseBlock fine coarse) (by simp)
  rw [Finset.card_univ] at hFibres
  calc
    (∑ coarseBlock : coarse.Blocks,
        fine.blockCountWithin coarse coarseBlock.1) =
        ∑ coarseBlock : coarse.Blocks,
          (blocksWithin fine coarse coarseBlock).card := by
      apply Finset.sum_congr rfl
      intro coarseBlock _
      rw [card_blocksWithin_eq_blockCountWithin fine coarse hRefines]
    _ = ∑ coarseBlock : coarse.Blocks,
        ((Finset.univ : Finset fine.Blocks).filter fun fineBlock ↦
          fineBlockToCoarseBlock fine coarse fineBlock = coarseBlock).card := by
      apply Finset.sum_congr rfl
      intro coarseBlock _
      apply congrArg Finset.card
      ext fineBlock
      simp only [mem_blocksWithin, Finset.mem_filter, Finset.mem_univ,
        true_and]
    _ = Fintype.card fine.Blocks := hFibres.symm

/-- The cardinalities of the canonical blocks sum to the sheet degree. -/
theorem sum_blockCard_blocks_eq_degree
    (partition : SheetPartition degree) (hDegree : 0 < degree) :
    (∑ sourceBlock : partition.Blocks,
      (partition.blockCard sourceBlock.1 : ℤ)) = degree := by
  calc
    (∑ sourceBlock : partition.Blocks,
        (partition.blockCard sourceBlock.1 : ℤ)) =
        ∑ sheet ∈ (Finset.univ : Finset (Fin degree)).filter
            (fun sheet ↦ partition.repr sheet = sheet),
          (partition.blockCard sheet : ℤ) := by
      symm
      exact Finset.sum_subtype _ (by simp)
        (fun sheet ↦ (partition.blockCard sheet : ℤ))
    _ =
        ∑ sheet : Fin degree,
          if partition.repr sheet = sheet then
            (partition.blockCard sheet : ℤ)
          else 0 := by
      rw [Finset.sum_filter]
    _ = degree := partition.sum_blockCard_representatives_eq_degree hDegree

/-- A fine partition has at most one block per sheet inside any fixed coarse
block.  In the gluing interpretation this is the local harmonic inequality
`val(A) ≤ m(A)`. -/
theorem blockCountWithin_le_blockCard
    (fine coarse : SheetPartition degree) (hRefines : fine.Refines coarse)
    (coarseBlock : coarse.Blocks) :
    fine.blockCountWithin coarse coarseBlock.1 ≤
      coarse.blockCard coarseBlock.1 := by
  classical
  have hSubset :
      (blocksWithin fine coarse coarseBlock).image Subtype.val ⊆
        coarse.block coarseBlock.1 := by
    intro sheet hSheet
    obtain ⟨fineBlock, hFineBlock, rfl⟩ := Finset.mem_image.mp hSheet
    have hMap :=
      (mem_blocksWithin fine coarse coarseBlock fineBlock).mp hFineBlock
    have hRel :=
      (fineBlockToCoarseBlock_eq_iff_rel fine coarse fineBlock
        coarseBlock).mp hMap
    exact (coarse.mem_block_iff coarseBlock.1 fineBlock.1).mpr hRel
  calc
    fine.blockCountWithin coarse coarseBlock.1 =
        (blocksWithin fine coarse coarseBlock).card :=
      (card_blocksWithin_eq_blockCountWithin fine coarse hRefines
        coarseBlock).symm
    _ = ((blocksWithin fine coarse coarseBlock).image Subtype.val).card := by
      symm
      exact Finset.card_image_of_injective _ Subtype.val_injective
    _ ≤ (coarse.block coarseBlock.1).card := Finset.card_le_card hSubset
    _ = coarse.blockCard coarseBlock.1 := rfl

end SheetPartition

namespace GluingDatum

variable {target : CFGraph} {degree : ℕ}

/-- Quotient-source vertices are exactly target vertices paired with a
canonical block of their vertex partition. -/
def sourceVertexEquivSigmaBlocks (data : GluingDatum target degree) :
    data.SourceVertex ≃
      Σ vertex : target.V, (data.vertexPartition vertex).Blocks where
  toFun sourceVertex :=
    ⟨sourceVertex.1.1, ⟨sourceVertex.1.2, sourceVertex.2⟩⟩
  invFun sourceBlock :=
    ⟨(sourceBlock.1, sourceBlock.2.1), sourceBlock.2.2⟩
  left_inv sourceVertex := by rfl
  right_inv sourceBlock := by rfl

/-- Quotient-source edge occurrences are exactly target occurrences paired
with a canonical block of their edge partition. -/
def sourceEdgeEquivSigmaBlocks (data : GluingDatum target degree) :
    data.SourceEdge ≃
      Σ edge : target.edges, (data.edgePartition edge).Blocks where
  toFun sourceEdge :=
    ⟨sourceEdge.1.1, ⟨sourceEdge.1.2, sourceEdge.2⟩⟩
  invFun sourceBlock :=
    ⟨(sourceBlock.1, sourceBlock.2.1), sourceBlock.2.2⟩
  left_inv sourceEdge := by rfl
  right_inv sourceBlock := by rfl

/-- Count quotient-source vertices fibrewise over the target. -/
theorem card_sourceVertex_eq_sum_card_blocks
    (data : GluingDatum target degree) :
    Fintype.card data.SourceVertex =
      ∑ vertex : target.V,
        Fintype.card (data.vertexPartition vertex).Blocks := by
  rw [Fintype.card_congr data.sourceVertexEquivSigmaBlocks,
    Fintype.card_sigma]

/-- Count quotient-source edge occurrences fibrewise over target
occurrences. -/
theorem card_sourceEdge_eq_sum_card_blocks
    (data : GluingDatum target degree) :
    Fintype.card data.SourceEdge =
      ∑ edge : target.edges,
        Fintype.card (data.edgePartition edge).Blocks := by
  rw [Fintype.card_congr data.sourceEdgeEquivSigmaBlocks,
    Fintype.card_sigma]

/-- The literal source graph has one occurrence for every source edge block. -/
@[simp] theorem sourceGraph_edges_card (data : GluingDatum target degree) :
    data.sourceGraph.edges.card = Fintype.card data.SourceEdge := by
  simp [sourceGraph]

/-- Each occurrence-labelled target edge contributes at both of its distinct
endpoints.  This weighted handshaking identity is convenient for the total
change formula. -/
theorem sum_incidentEdges (target : CFGraph)
    (value : target.edges → ℤ) :
    (∑ vertex : target.V, ∑ edge ∈ incidentEdges vertex, value edge) =
      2 * ∑ edge : target.edges, value edge := by
  classical
  simp only [incidentEdges, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    (∑ edge : target.edges, ∑ vertex : target.V,
        if (edge : target.V × target.V).1 = vertex ∨
            (edge : target.V × target.V).2 = vertex then value edge else 0) =
        ∑ edge : target.edges, (value edge + value edge) := by
      apply Finset.sum_congr rfl
      intro edge _
      have hne : (edge : target.V × target.V).1 ≠
          (edge : target.V × target.V).2 := by
        intro h
        have hPair : (edge : target.V × target.V) =
            ((edge : target.V × target.V).1,
              (edge : target.V × target.V).1) := by
          apply Prod.ext
          · rfl
          · exact h.symm
        have hMem : (edge : target.V × target.V) ∈ target.edges :=
          Multiset.coe_mem
        rw [hPair] at hMem
        exact target.loopless _ hMem
      calc
        (∑ vertex : target.V,
            if (edge : target.V × target.V).1 = vertex ∨
                (edge : target.V × target.V).2 = vertex then value edge else 0) =
            ∑ vertex : target.V,
              ((if (edge : target.V × target.V).1 = vertex then
                  value edge else 0) +
                (if (edge : target.V × target.V).2 = vertex then
                  value edge else 0)) := by
          apply Finset.sum_congr rfl
          intro vertex _
          by_cases hFirst : (edge : target.V × target.V).1 = vertex <;>
            by_cases hSecond : (edge : target.V × target.V).2 = vertex <;>
            simp [hFirst, hSecond]
          exact (hne (hFirst.trans hSecond.symm)).elim
        _ = value edge + value edge := by
          rw [Finset.sum_add_distrib]
          simp
    _ = 2 * ∑ edge : target.edges, value edge := by
      rw [mul_comm, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro edge _
      ring

/-- The sum of the induced edge-block counts over all source blocks above an
incident target vertex is the total number of blocks of that edge partition. -/
theorem sum_blockCountWithin_over_sourceBlocks
    (data : GluingDatum target degree) (vertex : target.V)
    (edge : target.edges) (hIncident : edge ∈ incidentEdges vertex) :
    (∑ sourceBlock : (data.vertexPartition vertex).Blocks,
      ((data.edgePartition edge).blockCountWithin
        (data.vertexPartition vertex) sourceBlock.1 : ℤ)) =
      Fintype.card (data.edgePartition edge).Blocks := by
  have hEnds := (Finset.mem_filter.mp hIncident).2
  have hRefines : (data.edgePartition edge).Refines
      (data.vertexPartition vertex) := by
    rcases hEnds with hLeft | hRight
    · simpa [hLeft] using data.refines_left edge
    · simpa [hRight] using data.refines_right edge
  exact_mod_cast SheetPartition.sum_blockCountWithin_eq_card_blocks
    (data.edgePartition edge) (data.vertexPartition vertex) hRefines

/-- The local ramification `r_φ(A)` at the source block represented by
`sourceBlock`, written directly in the sheet-partition coordinates of a
gluing datum. -/
def localRamification (data : GluingDatum target degree)
    (vertex : target.V) (sourceBlock : (data.vertexPartition vertex).Blocks) :
    ℤ :=
  (∑ edge ∈ incidentEdges vertex,
    ((data.edgePartition edge).blockCountWithin
      (data.vertexPartition vertex) sourceBlock.1 : ℤ)) - 2 -
    ((data.vertexPartition vertex).blockCard sourceBlock.1 : ℤ) *
      (((incidentEdges vertex).card : ℤ) - 2)

/-- The change `ch(v)` at a target vertex is the sum of local ramifications
over the distinct source blocks above it. -/
def targetChange (data : GluingDatum target degree) (vertex : target.V) : ℤ :=
  ∑ sourceBlock : (data.vertexPartition vertex).Blocks,
    data.localRamification vertex sourceBlock

/-- The contribution `ch(v) + val(v) - 3` of one target vertex to the
dimension-formula correction term. -/
def targetExcess (data : GluingDatum target degree) (vertex : target.V) : ℤ :=
  data.targetChange vertex + ((incidentEdges vertex).card : ℤ) - 3

/-- A target vertex is change-minimal when its correction term vanishes. -/
def ChangeMinimalAt (data : GluingDatum target degree)
    (vertex : target.V) : Prop :=
  data.targetExcess vertex = 0

/-- A gluing datum is change-minimal when every target vertex is. -/
def ChangeMinimal (data : GluingDatum target degree) : Prop :=
  ∀ vertex, data.ChangeMinimalAt vertex

/-- The nonnegative-correction property enjoyed by a combinatorial type in
the source: `ch(v) + val(v) - 3 ≥ 0` at every target vertex. -/
def CorrectionNonnegative (data : GluingDatum target degree) : Prop :=
  ∀ vertex, 0 ≤ data.targetExcess vertex

/-- Expand the change at one target vertex into the numbers of source blocks
above its incident edge occurrences and above the vertex itself. -/
theorem targetChange_eq_card_formula
    (data : GluingDatum target degree) (vertex : target.V) :
    data.targetChange vertex =
      (∑ edge ∈ incidentEdges vertex,
        (Fintype.card (data.edgePartition edge).Blocks : ℤ)) -
      2 * (Fintype.card (data.vertexPartition vertex).Blocks : ℤ) -
      (degree : ℤ) * (((incidentEdges vertex).card : ℤ) - 2) := by
  classical
  unfold targetChange localRamification
  simp_rw [Finset.sum_sub_distrib]
  have hIncidence :
      (∑ sourceBlock : (data.vertexPartition vertex).Blocks,
        ∑ edge ∈ incidentEdges vertex,
          ((data.edgePartition edge).blockCountWithin
            (data.vertexPartition vertex) sourceBlock.1 : ℤ)) =
        ∑ edge ∈ incidentEdges vertex,
          (Fintype.card (data.edgePartition edge).Blocks : ℤ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro edge hEdge
    exact sum_blockCountWithin_over_sourceBlocks data vertex edge hEdge
  rw [hIncidence]
  simp only [Finset.sum_const, Finset.card_univ, Int.nsmul_eq_mul]
  rw [← Finset.sum_mul]
  rw [SheetPartition.sum_blockCard_blocks_eq_degree
    (data.vertexPartition vertex) data.degree_pos]
  ring

/-- The total change, first in the fibre-counting form used to prove the
Draisma--Vargas formula. -/
theorem sum_targetChange_eq_card_formula
    (data : GluingDatum target degree) :
    (∑ vertex : target.V, data.targetChange vertex) =
      2 * (Fintype.card data.SourceEdge : ℤ) -
        2 * (Fintype.card data.SourceVertex : ℤ) -
        (degree : ℤ) *
          (2 * (target.edges.card : ℤ) -
            2 * (Fintype.card target.V : ℤ)) := by
  classical
  let incidenceTerm (vertex : target.V)
      (sourceBlock : (data.vertexPartition vertex).Blocks) : ℤ :=
    ∑ edge ∈ incidentEdges vertex,
      ((data.edgePartition edge).blockCountWithin
        (data.vertexPartition vertex) sourceBlock.1 : ℤ)
  let degreeTerm (vertex : target.V)
      (sourceBlock : (data.vertexPartition vertex).Blocks) : ℤ :=
    ((data.vertexPartition vertex).blockCard sourceBlock.1 : ℤ) *
      (((incidentEdges vertex).card : ℤ) - 2)
  have hIncidence :
      (∑ vertex : target.V,
        ∑ sourceBlock : (data.vertexPartition vertex).Blocks,
          incidenceTerm vertex sourceBlock) =
        2 * (Fintype.card data.SourceEdge : ℤ) := by
    calc
      (∑ vertex : target.V,
          ∑ sourceBlock : (data.vertexPartition vertex).Blocks,
            incidenceTerm vertex sourceBlock) =
          ∑ vertex : target.V,
            ∑ edge ∈ incidentEdges vertex,
              ∑ sourceBlock : (data.vertexPartition vertex).Blocks,
                ((data.edgePartition edge).blockCountWithin
                  (data.vertexPartition vertex) sourceBlock.1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro vertex _
        unfold incidenceTerm
        rw [Finset.sum_comm]
      _ = ∑ vertex : target.V,
          ∑ edge ∈ incidentEdges vertex,
            (Fintype.card (data.edgePartition edge).Blocks : ℤ) := by
        apply Finset.sum_congr rfl
        intro vertex _
        apply Finset.sum_congr rfl
        intro edge hEdge
        exact sum_blockCountWithin_over_sourceBlocks data vertex edge hEdge
      _ = 2 * ∑ edge : target.edges,
          (Fintype.card (data.edgePartition edge).Blocks : ℤ) :=
        sum_incidentEdges target _
      _ = 2 * (Fintype.card data.SourceEdge : ℤ) := by
        rw [data.card_sourceEdge_eq_sum_card_blocks]
        norm_cast
  have hConstant :
      (∑ vertex : target.V,
        ∑ _sourceBlock : (data.vertexPartition vertex).Blocks, (2 : ℤ)) =
        2 * (Fintype.card data.SourceVertex : ℤ) := by
    calc
      (∑ vertex : target.V,
          ∑ _sourceBlock : (data.vertexPartition vertex).Blocks, (2 : ℤ)) =
          2 * ∑ vertex : target.V,
            (Fintype.card (data.vertexPartition vertex).Blocks : ℤ) := by
        simp only [Finset.sum_const, Finset.card_univ, Int.nsmul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro vertex _
        ring
      _ = 2 * (Fintype.card data.SourceVertex : ℤ) := by
        rw [data.card_sourceVertex_eq_sum_card_blocks]
        norm_cast
  have hDegree :
      (∑ vertex : target.V,
        ∑ sourceBlock : (data.vertexPartition vertex).Blocks,
          degreeTerm vertex sourceBlock) =
        (degree : ℤ) *
          (2 * (target.edges.card : ℤ) -
            2 * (Fintype.card target.V : ℤ)) := by
    calc
      (∑ vertex : target.V,
          ∑ sourceBlock : (data.vertexPartition vertex).Blocks,
            degreeTerm vertex sourceBlock) =
          ∑ vertex : target.V,
            (degree : ℤ) * (((incidentEdges vertex).card : ℤ) - 2) := by
        apply Finset.sum_congr rfl
        intro vertex _
        unfold degreeTerm
        rw [← Finset.sum_mul]
        rw [SheetPartition.sum_blockCard_blocks_eq_degree
          (data.vertexPartition vertex) data.degree_pos]
      _ = (degree : ℤ) *
          (∑ vertex : target.V,
            (((incidentEdges vertex).card : ℤ) - 2)) := by
        symm
        rw [Finset.mul_sum]
      _ = (degree : ℤ) *
          (2 * (target.edges.card : ℤ) -
            2 * (Fintype.card target.V : ℤ)) := by
        congr 1
        rw [Finset.sum_sub_distrib]
        have hIncident := sum_incidentEdges target (fun _ ↦ (1 : ℤ))
        simp only [Finset.sum_const, Finset.card_univ, Int.nsmul_eq_mul,
          mul_one] at hIncident ⊢
        rw [hIncident]
        simp
        ring
  unfold targetChange localRamification
  change
    (∑ vertex : target.V,
      ∑ sourceBlock : (data.vertexPartition vertex).Blocks,
        (incidenceTerm vertex sourceBlock - 2 -
          degreeTerm vertex sourceBlock)) = _
  simp_rw [Finset.sum_sub_distrib]
  rw [hIncidence, hConstant, hDegree]

/-- The Draisma--Vargas total-change formula in the literal gluing-datum
model. -/
theorem totalChange (data : GluingDatum target degree) :
    (∑ vertex : target.V, data.targetChange vertex) =
      2 * genus data.sourceGraph - 2 * genus target * degree +
        2 * degree - 2 := by
  rw [data.sum_targetChange_eq_card_formula]
  unfold genus
  rw [data.sourceGraph_edges_card]
  change _ =
    2 * ((Fintype.card data.SourceEdge : ℤ) -
      (Fintype.card data.SourceVertex : ℤ) + 1) -
      2 * ((target.edges.card : ℤ) -
        (Fintype.card target.V : ℤ) + 1) * degree +
      2 * degree - 2
  ring

/-- The correction term in the Draisma--Vargas dimension formula, expressed
entirely through the source and target genera and the degree. -/
theorem dimensionCorrection (data : GluingDatum target degree) :
    (target.edges.card : ℤ) +
        ∑ vertex : target.V, data.targetExcess vertex =
      2 * genus data.sourceGraph - genus target * (2 * degree - 3) +
        2 * degree - 5 := by
  unfold targetExcess
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [data.totalChange]
  have hIncident := sum_incidentEdges target (fun _ ↦ (1 : ℤ))
  simp only [Finset.sum_const, Finset.card_univ, Int.nsmul_eq_mul,
    mul_one] at hIncident ⊢
  simp at hIncident
  rw [hIncident]
  unfold genus
  rw [data.sourceGraph_edges_card]
  ring

/-- For the genus-zero target used in Part I, the correction formula loses
its target-genus term. -/
theorem dimensionCorrection_of_target_genus_zero
    (data : GluingDatum target degree) (hTargetGenus : genus target = 0) :
    (target.edges.card : ℤ) +
        ∑ vertex : target.V, data.targetExcess vertex =
      2 * genus data.sourceGraph + 2 * degree - 5 := by
  rw [data.dimensionCorrection, hTargetGenus]
  norm_num

/-- Saturating the dimension bound forces every nonnegative correction term
to vanish, hence forces change-minimality. -/
theorem changeMinimal_of_dimension_saturated
    (data : GluingDatum target degree)
    (hCorrection : data.CorrectionNonnegative)
    (hSaturated :
      (target.edges.card : ℤ) =
        2 * genus data.sourceGraph - genus target * (2 * degree - 3) +
          2 * degree - 5) :
    data.ChangeMinimal := by
  have hDimension := data.dimensionCorrection
  have hSum : (∑ vertex : target.V, data.targetExcess vertex) = 0 := by
    linarith
  have hEach := (Finset.sum_eq_zero_iff_of_nonneg
    (fun vertex _ ↦ hCorrection vertex)).mp hSum
  intro vertex
  exact hEach vertex (Finset.mem_univ vertex)

/-- Genus-zero specialization used by the full-dimensional Part-I cones. -/
theorem changeMinimal_of_genus_zero_dimension_saturated
    (data : GluingDatum target degree)
    (hCorrection : data.CorrectionNonnegative)
    (hTargetGenus : genus target = 0)
    (hSaturated :
      (target.edges.card : ℤ) =
        2 * genus data.sourceGraph + 2 * degree - 5) :
    data.ChangeMinimal := by
  apply data.changeMinimal_of_dimension_saturated hCorrection
  simpa [hTargetGenus] using hSaturated

/-- Riemann--Hurwitz is exactly nonnegativity of every local ramification. -/
theorem localRamification_nonneg
    (data : GluingDatum target degree) (vertex : target.V)
    (hRiemannHurwitz : data.RiemannHurwitzAtTargetVertex vertex)
    (sourceBlock : (data.vertexPartition vertex).Blocks) :
    0 ≤ data.localRamification vertex sourceBlock := by
  have h := hRiemannHurwitz sourceBlock.1
  unfold localRamification
  omega

/-- Hence validity makes the change at every target vertex nonnegative. -/
theorem targetChange_nonneg
    (data : GluingDatum target degree) (hValid : data.Valid)
    (vertex : target.V) :
    0 ≤ data.targetChange vertex := by
  unfold targetChange
  exact Finset.sum_nonneg fun sourceBlock _ ↦
    data.localRamification_nonneg vertex (hValid.2 vertex) sourceBlock

/-- A change-minimal target vertex of a valid gluing datum has valency at
most three.  This is the numerical half of the source's local trivalence
constraint. -/
theorem incidentEdges_card_le_three_of_changeMinimalAt
    (data : GluingDatum target degree) (hValid : data.Valid)
    (vertex : target.V) (hMinimal : data.ChangeMinimalAt vertex) :
    (incidentEdges vertex).card ≤ 3 := by
  have hChange := data.targetChange_nonneg hValid vertex
  unfold ChangeMinimalAt targetExcess at hMinimal
  omega

end GluingDatum

end DraismaVargas.Infrastructure
