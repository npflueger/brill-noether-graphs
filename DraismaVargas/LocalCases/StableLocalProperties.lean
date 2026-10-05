module

public import DraismaVargas.LocalCases.W4StableSource

@[expose] public section

/-!
# Stable local properties of a gluing datum

This module records the balancing condition of Draisma--Vargas Part I
(arXiv:1909.12924) above one target vertex and the two index forms of the local
ramification it yields.  The LaTeX labels quoted below (`lemma-formula-rphi`,
`lemma-dangling-no-glue`, ...) are those of Part I, and "Observation I" is the
observation of that name in the proof of `lemma-dangling-no-glue`.

The balancing condition says that the dilation indices of the source edge
occurrences incident to one quotient-source vertex add up to the valency of
the target vertex times the local degree of the block.  Substituting it into
`GluingDatum.localRamification` turns that Riemann--Hurwitz residual into the
paper's index form `r(A) = 2(|A| - 1) - Σ (|f| - 1)`, and, after deleting the
dangling occurrences under `DanglingEdgeNoGlue`, into the non-dangling form
used by the dangling walk.

Observation I then says that a source block with vanishing local ramification
all of whose incident occurrences but one are unramified is a single sheet,
and so is its exceptional occurrence.

The later sections prove the two local halves of `lemma-dangling-no-glue`:

* `rem-leaves-min-change`: above a target leaf of a change-minimal datum
  without dangling target fibres there are only two kinds of blocks, and every
  source occurrence there is unramified (`leaf_block_dichotomy`,
  `sourceEdgeIndex_eq_one_of_target_leaf`).  In particular an occurrence at a
  source vertex of graph degree one is unramified.
* `lemma-dangling-rphi`: a block all of whose incident occurrences are
  dangling has vanishing local ramification
  (`localRamification_eq_zero_of_forall_isDangling`).  The divalent case is
  the dangling form of `lemma-equal-columns`: a block invisible to every
  surviving occurrence cannot carry the single unit of change of a
  change-minimal divalent target vertex, or the two columns of the honest
  stable length matrix there would agree.

The final section runs the dangling walk and deduces `DanglingEdgeNoGlue`
from these, given the purely graph-theoretic `DanglingSideDescent` property of
the occurrence-safe cut certificates.
-/

namespace DraismaVargas.LocalCases.StableLocalProperties

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource
open Finset

variable {target : CFGraph} {degree : ℕ}

/-! ## Fine blocks inside one coarse block -/

/-- A coarse block is the disjoint union of the fine blocks it contains, in
the `blocksWithin` presentation of that fibre. -/
theorem sum_blockCard_blocksWithin
    (fine coarse : SheetPartition degree) (hRefines : fine.Refines coarse)
    (coarseBlock : coarse.Blocks) :
    (∑ fineBlock ∈ SheetPartition.blocksWithin fine coarse coarseBlock,
        (fine.blockCard fineBlock.1 : ℤ)) =
      (coarse.blockCard coarseBlock.1 : ℤ) := by
  classical
  have hImage :
      (SheetPartition.blocksWithin fine coarse coarseBlock).image Subtype.val =
        (Finset.univ : Finset (Fin degree)).filter fun representative ↦
          fine.repr representative = representative ∧
            coarse.Rel coarseBlock.1 representative := by
    ext representative
    constructor
    · intro hMember
      obtain ⟨fineBlock, hFineBlock, hValue⟩ := Finset.mem_image.mp hMember
      have hRel : coarse.Rel coarseBlock.1 fineBlock.1 :=
        (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel fine coarse
          fineBlock coarseBlock).mp
          ((SheetPartition.mem_blocksWithin fine coarse coarseBlock
            fineBlock).mp hFineBlock)
      subst hValue
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fineBlock.2, hRel⟩
    · intro hMember
      obtain ⟨hIdempotent, hRel⟩ := (Finset.mem_filter.mp hMember).2
      refine Finset.mem_image.mpr ⟨⟨representative, hIdempotent⟩, ?_, rfl⟩
      exact (SheetPartition.mem_blocksWithin fine coarse coarseBlock _).mpr
        ((SheetPartition.fineBlockToCoarseBlock_eq_iff_rel fine coarse _
          coarseBlock).mpr hRel)
  calc
    (∑ fineBlock ∈ SheetPartition.blocksWithin fine coarse coarseBlock,
        (fine.blockCard fineBlock.1 : ℤ)) =
        ∑ representative ∈
            (SheetPartition.blocksWithin fine coarse coarseBlock).image
              Subtype.val,
          (fine.blockCard representative : ℤ) := by
      refine (Finset.sum_image
        (s := SheetPartition.blocksWithin fine coarse coarseBlock)
        (g := (Subtype.val : fine.Blocks → Fin degree))
        (f := fun representative ↦ (fine.blockCard representative : ℤ)) ?_).symm
      intro first _ second _ hValue
      exact Subtype.ext hValue
    _ = ∑ representative ∈ (Finset.univ : Finset (Fin degree)).filter
          (fun representative ↦ fine.repr representative = representative ∧
            coarse.Rel coarseBlock.1 representative),
        (fine.blockCard representative : ℤ) := by
      rw [hImage]
    _ = ∑ representative : Fin degree,
        if fine.repr representative = representative ∧
            coarse.Rel coarseBlock.1 representative then
          (fine.blockCard representative : ℤ)
        else 0 := by
      rw [Finset.sum_filter]
    _ = (coarse.blockCard coarseBlock.1 : ℤ) :=
      SheetPartition.sum_blockCard_representatives_eq_blockCard fine coarse
        hRefines coarseBlock.1

/-! ## The balancing condition -/

/-- The edge partition above a target occurrence incident to a vertex refines
the vertex partition there. -/
theorem refines_of_mem_incidentEdges (data : GluingDatum target degree)
    {vertex : target.V} {edge : target.edges}
    (hMember : edge ∈ GluingDatum.incidentEdges vertex) :
    (data.edgePartition edge).Refines (data.vertexPartition vertex) := by
  have hEnds := (Finset.mem_filter.mp hMember).2
  rcases hEnds with hLeft | hRight
  · simpa [hLeft] using data.refines_left edge
  · simpa [hRight] using data.refines_right edge

/-- Draisma--Vargas's balancing condition: the dilation indices of the source
edge occurrences incident to one quotient-source vertex add up to the target
valency times the local degree of the block. -/
theorem sum_sourceEdgeIndex_incident
    (data : GluingDatum target degree) (vertex : data.SourceVertex) :
    (∑ edge : IncidentSourceEdge data vertex,
        (data.sourceEdgeIndex edge.1 : ℤ)) =
      ((GluingDatum.incidentEdges vertex.1.1).card : ℤ) *
        ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
  calc
    (∑ edge : IncidentSourceEdge data vertex,
        (data.sourceEdgeIndex edge.1 : ℤ)) =
        ∑ item : Σ targetEdge : {edge : target.edges //
              edge ∈ GluingDatum.incidentEdges vertex.1.1},
            {fineBlock : (data.edgePartition targetEdge.1).Blocks //
              fineBlock ∈ SheetPartition.blocksWithin
                (data.edgePartition targetEdge.1)
                (data.vertexPartition vertex.1.1)
                ⟨vertex.1.2, vertex.2⟩},
          ((data.edgePartition item.1.1).blockCard item.2.1.1 : ℤ) :=
      Fintype.sum_equiv (incidentSourceEdgeEquiv data vertex) _ _ fun _ ↦ rfl
    _ = ∑ targetEdge : {edge : target.edges //
            edge ∈ GluingDatum.incidentEdges vertex.1.1},
          ∑ fineBlock ∈ SheetPartition.blocksWithin
              (data.edgePartition targetEdge.1)
              (data.vertexPartition vertex.1.1) ⟨vertex.1.2, vertex.2⟩,
            ((data.edgePartition targetEdge.1).blockCard fineBlock.1 : ℤ) := by
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun targetEdge _ ↦ ?_
      exact Finset.sum_coe_sort
        (SheetPartition.blocksWithin (data.edgePartition targetEdge.1)
          (data.vertexPartition vertex.1.1) ⟨vertex.1.2, vertex.2⟩)
        (fun fineBlock ↦
          ((data.edgePartition targetEdge.1).blockCard fineBlock.1 : ℤ))
    _ = ∑ _targetEdge : {edge : target.edges //
            edge ∈ GluingDatum.incidentEdges vertex.1.1},
          ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
      refine Finset.sum_congr rfl fun targetEdge _ ↦ ?_
      exact sum_blockCard_blocksWithin (data.edgePartition targetEdge.1)
        (data.vertexPartition vertex.1.1)
        (refines_of_mem_incidentEdges data targetEdge.2) ⟨vertex.1.2, vertex.2⟩
    _ = ((GluingDatum.incidentEdges vertex.1.1).card : ℤ) *
          ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

/-! ## The index form of the local ramification -/

/-- Draisma--Vargas `lemma-formula-rphi`: the local ramification of a source
block is `2(|A| - 1)` minus the total excess index of the incident source
edge occurrences. -/
theorem localRamification_eq_index_form
    (data : GluingDatum target degree) (vertex : data.SourceVertex) :
    data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ =
      2 * (((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) - 1) -
        ∑ edge : IncidentSourceEdge data vertex,
          ((data.sourceEdgeIndex edge.1 : ℤ) - 1) := by
  have hCard : (Fintype.card (IncidentSourceEdge data vertex) : ℤ) =
      ∑ targetEdge ∈ GluingDatum.incidentEdges vertex.1.1,
        ((data.edgePartition targetEdge).blockCountWithin
          (data.vertexPartition vertex.1.1) vertex.1.2 : ℤ) := by
    rw [card_incidentSourceEdge_eq_sum_blockCountWithin, Nat.cast_sum]
  have hOne : (∑ _edge : IncidentSourceEdge data vertex, (1 : ℤ)) =
      (Fintype.card (IncidentSourceEdge data vertex) : ℤ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Finset.sum_sub_distrib, sum_sourceEdgeIndex_incident, hOne, hCard]
  unfold GluingDatum.localRamification
  ring

/-! ## The non-dangling form -/

/-- Counting the surviving incident occurrences inside the incidence subtype
agrees with the non-dangling valency, which filters the whole occurrence
type. -/
theorem card_filter_not_isDangling_eq_nonDanglingValency
    (data : GluingDatum target degree) (vertex : data.SourceVertex) :
    ((Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
        (fun edge ↦ ¬ IsDangling data edge.1)).card =
      nonDanglingValency data vertex := by
  classical
  have hImage :
      ((Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
          (fun edge ↦ ¬ IsDangling data edge.1)).image Subtype.val =
        (Finset.univ : Finset data.SourceEdge).filter
          (fun edge ↦ ¬ IsDangling data edge ∧ Incident data edge vertex) := by
    ext edge
    constructor
    · intro hMember
      obtain ⟨incident, hIncident, hValue⟩ := Finset.mem_image.mp hMember
      have hSurvives := (Finset.mem_filter.mp hIncident).2
      subst hValue
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSurvives, incident.2⟩
    · intro hMember
      obtain ⟨hSurvives, hIncident⟩ := (Finset.mem_filter.mp hMember).2
      refine Finset.mem_image.mpr ⟨⟨edge, hIncident⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSurvives⟩
  calc
    ((Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
        (fun edge ↦ ¬ IsDangling data edge.1)).card =
        (((Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
          (fun edge ↦ ¬ IsDangling data edge.1)).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = ((Finset.univ : Finset data.SourceEdge).filter
          (fun edge ↦ ¬ IsDangling data edge ∧
            Incident data edge vertex)).card := by rw [hImage]
    _ = nonDanglingValency data vertex := rfl

/-- Draisma--Vargas `lem-rphi-nd`: under dangling-no-glue the dangling
occurrences contribute nothing to the index form, so the local ramification is
governed by the surviving valency alone. -/
theorem localRamification_eq_nonDangling_form
    (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (vertex : data.SourceVertex) :
    data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ =
      (nonDanglingValency data vertex : ℤ) - 2 +
        2 * ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) -
        ∑ edge ∈ (Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
            (fun edge ↦ ¬ IsDangling data edge.1),
          (data.sourceEdgeIndex edge.1 : ℤ) := by
  have hSplit :
      (∑ edge ∈ (Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
          (fun edge ↦ ¬ IsDangling data edge.1),
        ((data.sourceEdgeIndex edge.1 : ℤ) - 1)) =
        ∑ edge : IncidentSourceEdge data vertex,
          ((data.sourceEdgeIndex edge.1 : ℤ) - 1) := by
    refine Finset.sum_filter_of_ne ?_
    intro edge _ hNonzero hDangling
    apply hNonzero
    rw [hNoGlue edge.1 hDangling]
    norm_num
  have hCount :
      (∑ _edge ∈ (Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
          (fun edge ↦ ¬ IsDangling data edge.1), (1 : ℤ)) =
        (nonDanglingValency data vertex : ℤ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one,
      card_filter_not_isDangling_eq_nonDanglingValency]
  rw [localRamification_eq_index_form, ← hSplit, Finset.sum_sub_distrib,
    hCount]
  ring

/-! ## Observation I -/

/-- A fine block inside a coarse block has at most the coarse cardinality. -/
theorem blockCard_le_blockCard_of_refines {fine coarse : SheetPartition degree}
    (hRefines : fine.Refines coarse) {first second : Fin degree}
    (hRel : coarse.Rel first second) :
    fine.blockCard second ≤ coarse.blockCard first := by
  refine Finset.card_le_card ?_
  intro sheet hSheet
  exact (coarse.mem_block_iff first sheet).mpr
    (hRel.trans (hRefines.rel ((fine.mem_block_iff second sheet).mp hSheet)))

/-- The index of an incident source occurrence is at most the local degree of
the source vertex it meets. -/
theorem sourceEdgeIndex_le_blockCard (data : GluingDatum target degree)
    (vertex : data.SourceVertex) (edge : IncidentSourceEdge data vertex) :
    data.sourceEdgeIndex edge.1 ≤
      (data.vertexPartition vertex.1.1).blockCard vertex.1.2 := by
  obtain ⟨hMember, hRel⟩ :=
    (incident_iff_target_mem_and_rel data edge.1 vertex).mp edge.2
  exact blockCard_le_blockCard_of_refines
    (refines_of_mem_incidentEdges data hMember) hRel

/-- Draisma--Vargas Observation I: a source block of vanishing local
ramification whose incident occurrences are unramified except possibly one is
a single sheet, and the exceptional occurrence is unramified too. -/
theorem blockCard_eq_one_of_localRamification_zero
    (data : GluingDatum target degree) (vertex : data.SourceVertex)
    (special : IncidentSourceEdge data vertex)
    (hOthers : ∀ edge : IncidentSourceEdge data vertex, edge ≠ special →
      data.sourceEdgeIndex edge.1 = 1)
    (hZero : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0) :
    (data.vertexPartition vertex.1.1).blockCard vertex.1.2 = 1 ∧
      data.sourceEdgeIndex special.1 = 1 := by
  have hSum : (∑ edge : IncidentSourceEdge data vertex,
      ((data.sourceEdgeIndex edge.1 : ℤ) - 1)) =
      (data.sourceEdgeIndex special.1 : ℤ) - 1 := by
    refine Fintype.sum_eq_single special ?_
    intro edge hNe
    rw [hOthers edge hNe]
    norm_num
  rw [localRamification_eq_index_form, hSum] at hZero
  have hLe := sourceEdgeIndex_le_blockCard data vertex special
  have hPos := (data.vertexPartition vertex.1.1).blockCard_pos vertex.1.2
  omega

/-- The exception-free form of Observation I used by the dangling walk: if
every incident occurrence is unramified and the local ramification vanishes,
then the source block is a single sheet. -/
theorem blockCard_eq_one_of_forall_sourceEdgeIndex_eq_one
    (data : GluingDatum target degree) (vertex : data.SourceVertex)
    (hAll : ∀ edge : IncidentSourceEdge data vertex,
      data.sourceEdgeIndex edge.1 = 1)
    (hZero : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0) :
    (data.vertexPartition vertex.1.1).blockCard vertex.1.2 = 1 := by
  have hSum : (∑ edge : IncidentSourceEdge data vertex,
      ((data.sourceEdgeIndex edge.1 : ℤ) - 1)) = 0 := by
    refine Finset.sum_eq_zero fun edge _ ↦ ?_
    rw [hAll edge]
    norm_num
  rw [localRamification_eq_index_form, hSum] at hZero
  omega


/-! ## Occurrence counts at one quotient-source vertex

The next sections prove Draisma--Vargas `rem-leaves-min-change`: above a
target leaf a change-minimal datum has only two kinds of blocks, and every
source occurrence there is unramified.  The two numerical inputs are the
balancing identity above and the positivity of the induced block counts.
-/

/-- The quotient-source vertex carried by one block above a target vertex. -/
def blockVertex (data : GluingDatum target degree) (vertex : target.V)
    (block : (data.vertexPartition vertex).Blocks) : data.SourceVertex :=
  ⟨(vertex, block.1), block.2⟩

@[simp] theorem blockVertex_target (data : GluingDatum target degree)
    (vertex : target.V) (block : (data.vertexPartition vertex).Blocks) :
    (blockVertex data vertex block).1.1 = vertex := rfl

@[simp] theorem blockVertex_sheet (data : GluingDatum target degree)
    (vertex : target.V) (block : (data.vertexPartition vertex).Blocks) :
    (blockVertex data vertex block).1.2 = block.1 := rfl

@[simp] theorem blockVertex_self (data : GluingDatum target degree)
    (vertex : data.SourceVertex) :
    blockVertex data vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = vertex := rfl

/-- Dilation indices of quotient-source occurrences are positive. -/
theorem sourceEdgeIndex_pos (data : GluingDatum target degree)
    (edge : data.SourceEdge) : 0 < data.sourceEdgeIndex edge :=
  (data.edgePartition edge.1.1).blockCard_pos edge.1.2

/-- Every incident target occurrence induces at least one incident source
occurrence, so the source degree of a block is at least the target valency. -/
theorem incidentEdges_card_le_card_incidentSourceEdge
    (data : GluingDatum target degree) (vertex : data.SourceVertex) :
    (GluingDatum.incidentEdges vertex.1.1).card ≤
      Fintype.card (IncidentSourceEdge data vertex) := by
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  calc
    (GluingDatum.incidentEdges vertex.1.1).card =
        ∑ _targetEdge ∈ GluingDatum.incidentEdges vertex.1.1, 1 := by
      simp
    _ ≤ ∑ targetEdge ∈ GluingDatum.incidentEdges vertex.1.1,
          (data.edgePartition targetEdge).blockCountWithin
            (data.vertexPartition vertex.1.1) vertex.1.2 :=
      Finset.sum_le_sum fun targetEdge _ ↦
        SheetPartition.blockCountWithin_pos (data.edgePartition targetEdge)
          (data.vertexPartition vertex.1.1) vertex.1.2

/-- A source vertex of positive degree lies above a target vertex of positive
valency. -/
theorem incidentEdges_card_pos_of_card_incidentSourceEdge_pos
    (data : GluingDatum target degree) (vertex : data.SourceVertex)
    (hDegree : 0 < Fintype.card (IncidentSourceEdge data vertex)) :
    0 < (GluingDatum.incidentEdges vertex.1.1).card := by
  by_contra hZero
  have hEmpty : GluingDatum.incidentEdges vertex.1.1 = ∅ :=
    Finset.card_eq_zero.mp (by omega)
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin, hEmpty] at hDegree
  simp at hDegree

/-! ## Change-minimal leaves -/

/-- Above a target leaf the local ramification of a block is its source
degree plus its local degree, less two. -/
theorem localRamification_eq_leaf_form
    (data : GluingDatum target degree) (vertex : data.SourceVertex)
    (hLeaf : (GluingDatum.incidentEdges vertex.1.1).card = 1) :
    data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ =
      (Fintype.card (IncidentSourceEdge data vertex) : ℤ) +
        ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) - 2 := by
  have hFormula := localRamification_eq_vertex_degree data vertex
  rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge, hLeaf] at hFormula
  rw [hFormula]
  ring

/-- Above a target leaf all incident occurrences of a block lie above the
single incident target occurrence, so their number is at most the local
degree. -/
theorem card_incidentSourceEdge_le_blockCard_of_target_leaf
    (data : GluingDatum target degree) (vertex : data.SourceVertex)
    (hLeaf : (GluingDatum.incidentEdges vertex.1.1).card = 1) :
    (Fintype.card (IncidentSourceEdge data vertex) : ℤ) ≤
      ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
  have hBalance := sum_sourceEdgeIndex_incident data vertex
  rw [hLeaf] at hBalance
  calc
    (Fintype.card (IncidentSourceEdge data vertex) : ℤ) =
        ∑ _edge : IncidentSourceEdge data vertex, (1 : ℤ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    _ ≤ ∑ edge : IncidentSourceEdge data vertex,
          (data.sourceEdgeIndex edge.1 : ℤ) :=
      Finset.sum_le_sum fun edge _ ↦ by
        exact_mod_cast sourceEdgeIndex_pos data edge.1
    _ = ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
      rw [hBalance]
      ring


/-- Draisma--Vargas `rem-leaves-min-change`.  Above a target leaf of a valid,
change-minimal datum without dangling target fibres there are exactly two
kinds of blocks: single sheets with a single incident occurrence and vanishing
local ramification, and one block of local degree two with two incident
occurrences, local ramification two and a surviving incident occurrence. -/
theorem leaf_block_dichotomy
    (data : GluingDatum target degree) (hValid : data.Valid)
    (hNoDangling : NoDanglingTargetFibres data) (root : target.V)
    (hLeaf : (GluingDatum.incidentEdges root).card = 1)
    (hMinimal : data.ChangeMinimalAt root)
    (block : (data.vertexPartition root).Blocks) :
    (Fintype.card (IncidentSourceEdge data (blockVertex data root block)) = 1 ∧
        (data.vertexPartition root).blockCard block.1 = 1 ∧
        data.localRamification root block = 0) ∨
      (Fintype.card (IncidentSourceEdge data (blockVertex data root block)) = 2 ∧
        (data.vertexPartition root).blockCard block.1 = 2 ∧
        data.localRamification root block = 2 ∧
        ∃ edge : IncidentSourceEdge data (blockVertex data root block),
          ¬ IsDangling data edge.1) := by
  classical
  obtain ⟨targetEdge, hIncidentEdges⟩ := Finset.card_eq_one.mp hLeaf
  obtain ⟨survivor, hSurvivorTarget, hSurvives⟩ := hNoDangling targetEdge
  set witness : (data.vertexPartition root).Blocks :=
    (data.vertexPartition root).toBlock survivor.1.2 with hWitnessDef
  have hSurvivorMem : survivor.1.1 ∈ GluingDatum.incidentEdges root := by
    rw [hIncidentEdges, hSurvivorTarget]
    simp
  have hIncidentWitness :
      Incident data survivor (blockVertex data root witness) := by
    apply (incident_iff_target_mem_and_rel data survivor
      (blockVertex data root witness)).2
    exact ⟨hSurvivorMem, (data.vertexPartition root).rel_repr_left survivor.1.2⟩
  -- the witness block has at least two incident occurrences
  have hWitnessDegreeNeOne :
      Fintype.card (IncidentSourceEdge data (blockVertex data root witness))
        ≠ 1 := by
    intro hOne
    apply hSurvives
    have hDegree :
        vertex_degree data.sourceGraph (blockVertex data root witness) = 1 := by
      rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge, hOne]
      norm_num
    rcases hIncidentWitness with hLeft | hRight
    · exact isDangling_of_sourceEnds_fst_degree_eq_one data hValid.1 survivor
        (by rw [hLeft]; exact hDegree)
    · exact isDangling_of_sourceEnds_snd_degree_eq_one data hValid.1 survivor
        (by rw [hRight]; exact hDegree)
  have hWitnessDegreePos :
      1 ≤ Fintype.card (IncidentSourceEdge data (blockVertex data root witness)) := by
    have := incidentEdges_card_le_card_incidentSourceEdge data
      (blockVertex data root witness)
    rw [blockVertex_target, hLeaf] at this
    exact this
  have hWitnessTwo :
      2 ≤ Fintype.card (IncidentSourceEdge data (blockVertex data root witness)) := by
    omega
  -- the change at the leaf is two
  have hChange : data.targetChange root = 2 := by
    unfold GluingDatum.ChangeMinimalAt GluingDatum.targetExcess at hMinimal
    rw [hLeaf] at hMinimal
    omega
  have hNonneg : ∀ item : (data.vertexPartition root).Blocks,
      0 ≤ data.localRamification root item := fun item ↦
    data.localRamification_nonneg root (hValid.2 root) item
  have hSum : (∑ item : (data.vertexPartition root).Blocks,
      data.localRamification root item) = 2 := hChange
  -- the leaf form of the local ramification
  have hForm : ∀ item : (data.vertexPartition root).Blocks,
      data.localRamification root item =
        (Fintype.card (IncidentSourceEdge data (blockVertex data root item)) : ℤ) +
          ((data.vertexPartition root).blockCard item.1 : ℤ) - 2 := by
    intro item
    exact localRamification_eq_leaf_form data (blockVertex data root item) hLeaf
  have hBound : ∀ item : (data.vertexPartition root).Blocks,
      (Fintype.card (IncidentSourceEdge data (blockVertex data root item)) : ℤ) ≤
        ((data.vertexPartition root).blockCard item.1 : ℤ) := by
    intro item
    exact card_incidentSourceEdge_le_blockCard_of_target_leaf data
      (blockVertex data root item) hLeaf
  have hDegreeLower : ∀ item : (data.vertexPartition root).Blocks,
      1 ≤ Fintype.card (IncidentSourceEdge data (blockVertex data root item)) := by
    intro item
    have := incidentEdges_card_le_card_incidentSourceEdge data
      (blockVertex data root item)
    rw [blockVertex_target, hLeaf] at this
    exact this
  -- the witness block carries all of the change
  have hWitnessRamification : 2 ≤ data.localRamification root witness := by
    have hFormW := hForm witness
    have hBoundW := hBound witness
    omega
  have hWitnessLe : data.localRamification root witness ≤ 2 := by
    rw [← hSum]
    exact Finset.single_le_sum (fun item _ ↦ hNonneg item) (Finset.mem_univ _)
  have hWitnessEq : data.localRamification root witness = 2 := by omega
  have hOthers : ∀ item : (data.vertexPartition root).Blocks, item ≠ witness →
      data.localRamification root item = 0 := by
    intro item hNe
    have hSplit := Finset.sum_erase_add (Finset.univ : Finset (data.vertexPartition root).Blocks)
      (fun item ↦ data.localRamification root item) (Finset.mem_univ witness)
    have hEraseSum : (∑ other ∈ (Finset.univ : Finset (data.vertexPartition root).Blocks).erase witness,
        data.localRamification root other) = 0 := by
      rw [hWitnessEq] at hSplit
      omega
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun other _ ↦ hNonneg other)).mp hEraseSum item
      (Finset.mem_erase.mpr ⟨hNe, Finset.mem_univ _⟩)
  by_cases hCase : block = witness
  · right
    have hFormB := hForm witness
    have hBoundB := hBound witness
    rw [hCase]
    exact ⟨by omega, by omega, hWitnessEq, ⟨survivor, hIncidentWitness⟩,
      hSurvives⟩
  · left
    have hZero := hOthers block hCase
    have hFormB := hForm block
    have hBoundB := hBound block
    have hLowerB := hDegreeLower block
    refine ⟨by omega, by omega, hZero⟩


/-- The other incident occurrences force an upper bound on the index of any
one of them: each of them has index at least one and the total is pinned by
the balancing condition. -/
theorem sourceEdgeIndex_le_of_incident (data : GluingDatum target degree)
    (vertex : data.SourceVertex) (edge : IncidentSourceEdge data vertex) :
    (data.sourceEdgeIndex edge.1 : ℤ) ≤
      ((GluingDatum.incidentEdges vertex.1.1).card : ℤ) *
          ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) -
        (Fintype.card (IncidentSourceEdge data vertex) : ℤ) + 1 := by
  classical
  have hBalance := sum_sourceEdgeIndex_incident data vertex
  have hSplit := Finset.sum_erase_add
    (Finset.univ : Finset (IncidentSourceEdge data vertex))
    (fun item ↦ (data.sourceEdgeIndex item.1 : ℤ)) (Finset.mem_univ edge)
  have hPositive : 1 ≤ Fintype.card (IncidentSourceEdge data vertex) :=
    Fintype.card_pos_iff.mpr ⟨edge⟩
  have hCard :
      (((Finset.univ : Finset (IncidentSourceEdge data vertex)).erase edge).card : ℤ) =
        (Fintype.card (IncidentSourceEdge data vertex) : ℤ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ edge), Finset.card_univ]
    omega
  have hLower :
      (((Finset.univ : Finset (IncidentSourceEdge data vertex)).erase edge).card : ℤ) ≤
        ∑ item ∈ (Finset.univ : Finset (IncidentSourceEdge data vertex)).erase edge,
          (data.sourceEdgeIndex item.1 : ℤ) := by
    calc
      (((Finset.univ : Finset (IncidentSourceEdge data vertex)).erase edge).card : ℤ) =
          ∑ _item ∈ (Finset.univ : Finset (IncidentSourceEdge data vertex)).erase edge,
            (1 : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ _ :=
        Finset.sum_le_sum fun item _ ↦ by
          exact_mod_cast sourceEdgeIndex_pos data item.1
  linarith

/-- Above a target leaf of a valid, change-minimal datum without dangling
target fibres, the source degree of a block is its local degree. -/
theorem card_incidentSourceEdge_eq_blockCard_of_target_leaf
    (data : GluingDatum target degree) (hValid : data.Valid)
    (hNoDangling : NoDanglingTargetFibres data) (vertex : data.SourceVertex)
    (hLeaf : (GluingDatum.incidentEdges vertex.1.1).card = 1)
    (hMinimal : data.ChangeMinimalAt vertex.1.1) :
    Fintype.card (IncidentSourceEdge data vertex) =
      (data.vertexPartition vertex.1.1).blockCard vertex.1.2 := by
  rcases leaf_block_dichotomy data hValid hNoDangling vertex.1.1 hLeaf hMinimal
      ⟨vertex.1.2, vertex.2⟩ with ⟨hCard, hBlock, _⟩ | ⟨hCard, hBlock, _, _⟩
  · exact hCard.trans hBlock.symm
  · exact hCard.trans hBlock.symm

/-- Draisma--Vargas `rem-leaves-min-change`, index form: every source
occurrence incident to a block above a target leaf is unramified. -/
theorem sourceEdgeIndex_eq_one_of_target_leaf
    (data : GluingDatum target degree) (hValid : data.Valid)
    (hNoDangling : NoDanglingTargetFibres data) (vertex : data.SourceVertex)
    (hLeaf : (GluingDatum.incidentEdges vertex.1.1).card = 1)
    (hMinimal : data.ChangeMinimalAt vertex.1.1)
    (edge : IncidentSourceEdge data vertex) :
    data.sourceEdgeIndex edge.1 = 1 := by
  have hCard := card_incidentSourceEdge_eq_blockCard_of_target_leaf data hValid
    hNoDangling vertex hLeaf hMinimal
  have hLe := sourceEdgeIndex_le_of_incident data vertex edge
  rw [hLeaf, hCard] at hLe
  have hPos := sourceEdgeIndex_pos data edge.1
  push_cast at hLe
  omega

/-! ## Pendant occurrences -/

/-- A quotient-source vertex with a single incident occurrence lies above a
target leaf. -/
theorem incidentEdges_card_eq_one_of_card_incidentSourceEdge_eq_one
    (data : GluingDatum target degree) (vertex : data.SourceVertex)
    (hDegree : Fintype.card (IncidentSourceEdge data vertex) = 1) :
    (GluingDatum.incidentEdges vertex.1.1).card = 1 := by
  have hLe := incidentEdges_card_le_card_incidentSourceEdge data vertex
  have hPos := incidentEdges_card_pos_of_card_incidentSourceEdge_pos data vertex
    (by omega)
  omega

/-- The base case of the dangling walk: an occurrence at a quotient-source
vertex of degree one is unramified. -/
theorem sourceEdgeIndex_eq_one_of_card_incidentSourceEdge_eq_one
    (data : GluingDatum target degree) (hValid : data.Valid)
    (hNoDangling : NoDanglingTargetFibres data)
    (hMinimal : data.ChangeMinimal) (vertex : data.SourceVertex)
    (hDegree : Fintype.card (IncidentSourceEdge data vertex) = 1)
    (edge : IncidentSourceEdge data vertex) :
    data.sourceEdgeIndex edge.1 = 1 :=
  sourceEdgeIndex_eq_one_of_target_leaf data hValid hNoDangling vertex
    (incidentEdges_card_eq_one_of_card_incidentSourceEdge_eq_one data vertex
      hDegree)
    (hMinimal vertex.1.1) edge

/-- Graph-theoretic form of the base case: an occurrence with an endpoint of
source degree one is unramified. -/
theorem sourceEdgeIndex_eq_one_of_vertex_degree_eq_one
    (data : GluingDatum target degree) (hValid : data.Valid)
    (hNoDangling : NoDanglingTargetFibres data)
    (hMinimal : data.ChangeMinimal) (edge : data.SourceEdge)
    (hDegree : vertex_degree data.sourceGraph (data.sourceEnds edge).1 = 1 ∨
      vertex_degree data.sourceGraph (data.sourceEnds edge).2 = 1) :
    data.sourceEdgeIndex edge = 1 := by
  have hTransfer : ∀ vertex : data.SourceVertex,
      vertex_degree data.sourceGraph vertex = 1 →
      Fintype.card (IncidentSourceEdge data vertex) = 1 := by
    intro vertex hVertex
    have hCast := vertex_degree_sourceGraph_eq_card_incidentSourceEdge data vertex
    rw [hVertex] at hCast
    omega
  rcases hDegree with hDegree | hDegree
  · exact sourceEdgeIndex_eq_one_of_card_incidentSourceEdge_eq_one data hValid
      hNoDangling hMinimal (data.sourceEnds edge).1 (hTransfer _ hDegree)
      ⟨edge, incident_left data edge⟩
  · exact sourceEdgeIndex_eq_one_of_card_incidentSourceEdge_eq_one data hValid
      hNoDangling hMinimal (data.sourceEnds edge).2 (hTransfer _ hDegree)
      ⟨edge, incident_right data edge⟩

/-! ## The exceptional occurrence of a block -/

/-- If every incident occurrence but one is unramified, the index of the
exceptional occurrence is pinned by the local degree and the local
ramification. -/
theorem sourceEdgeIndex_eq_of_forall_other_eq_one
    (data : GluingDatum target degree) (vertex : data.SourceVertex)
    (special : IncidentSourceEdge data vertex)
    (hOthers : ∀ edge : IncidentSourceEdge data vertex, edge ≠ special →
      data.sourceEdgeIndex edge.1 = 1) :
    (data.sourceEdgeIndex special.1 : ℤ) =
      2 * ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) - 1 -
        data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ := by
  have hSum : (∑ edge : IncidentSourceEdge data vertex,
      ((data.sourceEdgeIndex edge.1 : ℤ) - 1)) =
      (data.sourceEdgeIndex special.1 : ℤ) - 1 := by
    refine Fintype.sum_eq_single special ?_
    intro edge hNe
    rw [hOthers edge hNe]
    norm_num
  have hForm := localRamification_eq_index_form data vertex
  rw [hSum] at hForm
  linarith

/-- Consequently the exceptional occurrence is ramified by at most the local
ramification of its block.  With vanishing local ramification this is
Observation I. -/
theorem sourceEdgeIndex_le_localRamification_add_one
    (data : GluingDatum target degree) (vertex : data.SourceVertex)
    (special : IncidentSourceEdge data vertex)
    (hOthers : ∀ edge : IncidentSourceEdge data vertex, edge ≠ special →
      data.sourceEdgeIndex edge.1 = 1) :
    (data.sourceEdgeIndex special.1 : ℤ) ≤
      data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ + 1 := by
  have hValue := sourceEdgeIndex_eq_of_forall_other_eq_one data vertex special
    hOthers
  have hLe : (data.sourceEdgeIndex special.1 : ℤ) ≤
      ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
    exact_mod_cast sourceEdgeIndex_le_blockCard data vertex special
  linarith


/-! ## Local structure at a divalent target vertex above one block of
vanishing ramification

Draisma--Vargas `lemma-change-zero` is stated for a divalent target vertex of
zero change.  The dangling case of `lemma-dangling-rphi` needs it one block at
a time: the two columns of the length matrix are still equal when only the
blocks carrying a surviving occurrence have vanishing ramification.  The
following lemmas are the per-block forms of the corresponding statements of
`W4StableSource`, proved here so that this module need not depend on that one.
-/

private theorem blockCountWithin_congr_local {d : ℕ}
    (fine coarse : SheetPartition d) {first second : Fin d}
    (hRel : coarse.Rel first second) :
    fine.blockCountWithin coarse first =
      fine.blockCountWithin coarse second := by
  unfold SheetPartition.blockCountWithin
  rw [coarse.block_eq_of_rel hRel]

/-- At a divalent target vertex, a block of vanishing local ramification
receives exactly one fine block from each incident target occurrence. -/
theorem blockCountWithin_eq_one_of_divalent_localRamification_zero
    (data : GluingDatum target degree) (vertex : target.V)
    (hDivalent : (GluingDatum.incidentEdges vertex).card = 2)
    (sheet : Fin degree)
    (hZero : data.localRamification vertex
      ((data.vertexPartition vertex).toBlock sheet) = 0)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges vertex) :
    (data.edgePartition edge).blockCountWithin
      (data.vertexPartition vertex) sheet = 1 := by
  classical
  obtain ⟨first, second, hNe, hPair⟩ := Finset.card_eq_two.mp hDivalent
  unfold GluingDatum.localRamification at hZero
  simp only [SheetPartition.toBlock_val] at hZero
  rw [hDivalent] at hZero
  have hTotal :
      ∑ item ∈ GluingDatum.incidentEdges vertex,
        ((data.edgePartition item).blockCountWithin
          (data.vertexPartition vertex)
          ((data.vertexPartition vertex).repr sheet) : ℤ) = 2 := by
    have hZeroFactor : ((2 : ℕ) : ℤ) - 2 = 0 := by norm_num
    rw [hZeroFactor, mul_zero] at hZero
    omega
  rw [hPair, Finset.sum_pair hNe] at hTotal
  have hFirstPos := SheetPartition.blockCountWithin_pos
    (data.edgePartition first) (data.vertexPartition vertex)
    ((data.vertexPartition vertex).repr sheet)
  have hSecondPos := SheetPartition.blockCountWithin_pos
    (data.edgePartition second) (data.vertexPartition vertex)
    ((data.vertexPartition vertex).repr sheet)
  have hBlockCount :
      (data.edgePartition edge).blockCountWithin
        (data.vertexPartition vertex)
        ((data.vertexPartition vertex).repr sheet) = 1 := by
    rw [hPair] at hEdge
    rcases Finset.mem_insert.mp hEdge with hCase | hCase
    · rw [hCase]; omega
    · rw [Finset.mem_singleton.mp hCase]; omega
  rw [← hBlockCount]
  exact blockCountWithin_congr_local (data.edgePartition edge)
    (data.vertexPartition vertex)
    ((data.vertexPartition vertex).rel_repr_right sheet)

/-- Hence that block is a block of each incident edge partition. -/
theorem edgePartition_block_eq_of_divalent_localRamification_zero
    (data : GluingDatum target degree) (vertex : target.V)
    (hDivalent : (GluingDatum.incidentEdges vertex).card = 2)
    (sheet : Fin degree)
    (hZero : data.localRamification vertex
      ((data.vertexPartition vertex).toBlock sheet) = 0)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges vertex) :
    (data.edgePartition edge).block sheet =
      (data.vertexPartition vertex).block sheet :=
  SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one
    (data.edgePartition edge) (data.vertexPartition vertex)
    (refines_of_mem_incidentEdges data hEdge) sheet
    (blockCountWithin_eq_one_of_divalent_localRamification_zero data vertex
      hDivalent sheet hZero edge hEdge)

/-- The two sheet relations agree there. -/
theorem edgePartition_rel_iff_of_divalent_localRamification_zero
    (data : GluingDatum target degree) (vertex : target.V)
    (hDivalent : (GluingDatum.incidentEdges vertex).card = 2)
    (sheet : Fin degree)
    (hZero : data.localRamification vertex
      ((data.vertexPartition vertex).toBlock sheet) = 0)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges vertex)
    (other : Fin degree) :
    (data.edgePartition edge).Rel sheet other ↔
      (data.vertexPartition vertex).Rel sheet other := by
  constructor
  · intro hRel
    have hMem : other ∈ (data.edgePartition edge).block sheet :=
      ((data.edgePartition edge).mem_block_iff sheet other).2 hRel
    rw [edgePartition_block_eq_of_divalent_localRamification_zero data vertex
      hDivalent sheet hZero edge hEdge] at hMem
    exact ((data.vertexPartition vertex).mem_block_iff sheet other).1 hMem
  · intro hRel
    have hMem : other ∈ (data.vertexPartition vertex).block sheet :=
      ((data.vertexPartition vertex).mem_block_iff sheet other).2 hRel
    rw [← edgePartition_block_eq_of_divalent_localRamification_zero data vertex
      hDivalent sheet hZero edge hEdge] at hMem
    exact ((data.edgePartition edge).mem_block_iff sheet other).1 hMem

/-- The dilation index of the canonical occurrence there is the local degree
of the block. -/
theorem sourceEdgeIndex_eq_of_divalent_localRamification_zero
    (data : GluingDatum target degree) (vertex : target.V)
    (hDivalent : (GluingDatum.incidentEdges vertex).card = 2)
    (sheet : Fin degree)
    (hZero : data.localRamification vertex
      ((data.vertexPartition vertex).toBlock sheet) = 0)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges vertex) :
    data.sourceEdgeIndex (data.sourceEdge edge sheet) =
      (data.vertexPartition vertex).blockCard sheet := by
  rw [GluingDatum.sourceEdgeIndex_sourceEdge]
  unfold SheetPartition.blockCard
  rw [edgePartition_block_eq_of_divalent_localRamification_zero data vertex
    hDivalent sheet hZero edge hEdge]

/-- A block of vanishing ramification above a divalent target vertex carries a
source vertex of graph degree two. -/
theorem vertex_degree_eq_two_of_divalent_localRamification_zero
    (data : GluingDatum target degree) (vertex : target.V)
    (hDivalent : (GluingDatum.incidentEdges vertex).card = 2)
    (sheet : Fin degree)
    (hZero : data.localRamification vertex
      ((data.vertexPartition vertex).toBlock sheet) = 0) :
    vertex_degree data.sourceGraph (data.sourceEndpoint vertex sheet) = 2 := by
  have hFormula :=
    localRamification_eq_vertex_degree data (data.sourceEndpoint vertex sheet)
  have hZero' : data.localRamification (data.sourceEndpoint vertex sheet).1.1
      ⟨(data.sourceEndpoint vertex sheet).1.2,
        (data.sourceEndpoint vertex sheet).2⟩ = 0 := hZero
  rw [hZero'] at hFormula
  have hDivalent' :
      (GluingDatum.incidentEdges
        (data.sourceEndpoint vertex sheet).1.1).card = 2 := hDivalent
  rw [hDivalent'] at hFormula
  have hZeroFactor : ((2 : ℕ) : ℤ) - 2 = 0 := by norm_num
  rw [hZeroFactor, mul_zero] at hFormula
  omega

/-- Danglingness of the two canonical occurrences through a sheet whose block
has vanishing ramification agrees. -/
theorem isDangling_sourceEdge_iff_of_divalent_localRamification_zero
    (data : GluingDatum target degree) (vertex : target.V)
    (hDivalent : (GluingDatum.incidentEdges vertex).card = 2)
    (sheet : Fin degree)
    (hZero : data.localRamification vertex
      ((data.vertexPartition vertex).toBlock sheet) = 0)
    {first second : target.edges} (hNe : first ≠ second)
    (hFirst : first ∈ GluingDatum.incidentEdges vertex)
    (hSecond : second ∈ GluingDatum.incidentEdges vertex) :
    IsDangling data (data.sourceEdge first sheet) ↔
      IsDangling data (data.sourceEdge second sheet) := by
  have hDegree := vertex_degree_eq_two_of_divalent_localRamification_zero data
    vertex hDivalent sheet hZero
  have hFirstIncident :=
    incident_sourceEdge_sourceEndpoint data vertex first hFirst sheet
  have hSecondIncident :=
    incident_sourceEdge_sourceEndpoint data vertex second hSecond sheet
  constructor
  · exact isDangling_of_incident_of_vertex_degree_eq_two data
      (sourceEdge_ne_of_target_ne data hNe sheet sheet) hFirstIncident
      hSecondIncident hDegree
  · exact isDangling_of_incident_of_vertex_degree_eq_two data
      (sourceEdge_ne_of_target_ne data (Ne.symm hNe) sheet sheet)
      hSecondIncident hFirstIncident hDegree

/-- When both survive they are consecutive, hence on the same stable path. -/
theorem stablePath_sourceEdge_eq_of_divalent_localRamification_zero
    (data : GluingDatum target degree) (vertex : target.V)
    (hDivalent : (GluingDatum.incidentEdges vertex).card = 2)
    (sheet : Fin degree)
    (hZero : data.localRamification vertex
      ((data.vertexPartition vertex).toBlock sheet) = 0)
    {first second : target.edges} (hNe : first ≠ second)
    (hFirst : first ∈ GluingDatum.incidentEdges vertex)
    (hSecond : second ∈ GluingDatum.incidentEdges vertex)
    (hFirstSurvives : ¬ IsDangling data (data.sourceEdge first sheet))
    (hSecondSurvives : ¬ IsDangling data (data.sourceEdge second sheet)) :
    NonDanglingEdge.stablePath
        (⟨data.sourceEdge first sheet, hFirstSurvives⟩ : NonDanglingEdge data) =
      NonDanglingEdge.stablePath
        (⟨data.sourceEdge second sheet, hSecondSurvives⟩ :
          NonDanglingEdge data) := by
  classical
  have hDegree := vertex_degree_eq_two_of_divalent_localRamification_zero data
    vertex hDivalent sheet hZero
  have hFirstIncident :=
    incident_sourceEdge_sourceEndpoint data vertex first hFirst sheet
  have hSecondIncident :=
    incident_sourceEdge_sourceEndpoint data vertex second hSecond sheet
  have hEdgeNe := sourceEdge_ne_of_target_ne data hNe sheet sheet
  refine stablePath_eq_of_consecutive
    ⟨fun hEqual ↦ hEdgeNe (congrArg Subtype.val hEqual),
      data.sourceEndpoint vertex sheet, hFirstIncident, hSecondIncident, ?_⟩
  have hFilter :
      ((Finset.univ : Finset data.SourceEdge).filter fun edge ↦
        ¬ IsDangling data edge ∧
          Incident data edge (data.sourceEndpoint vertex sheet)) =
        {data.sourceEdge first sheet, data.sourceEdge second sheet} := by
    apply Finset.Subset.antisymm
    · intro edge hEdge
      have hProperty := (Finset.mem_filter.mp hEdge).2
      rcases eq_of_incident_of_vertex_degree_eq_two data hEdgeNe hFirstIncident
        hSecondIncident hDegree hProperty.2 with hCase | hCase
      · simp [hCase]
      · simp [hCase]
    · intro edge hEdge
      rcases Finset.mem_insert.mp hEdge with hCase | hCase
      · rw [hCase]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          hFirstSurvives, hFirstIncident⟩
      · rw [Finset.mem_singleton.mp hCase]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          hSecondSurvives, hSecondIncident⟩
  unfold nonDanglingValency
  rw [hFilter, Finset.card_pair hEdgeNe]

/-- Transporting a source occurrence at such a block from one incident target
occurrence to the other, and back, is the identity. -/
theorem sourceEdge_transport_left_inverse_of_divalent_localRamification_zero
    (data : GluingDatum target degree) (vertex : target.V)
    (hDivalent : (GluingDatum.incidentEdges vertex).card = 2)
    (first second : target.edges)
    (hFirst : first ∈ GluingDatum.incidentEdges vertex)
    (hSecond : second ∈ GluingDatum.incidentEdges vertex)
    (edge : data.SourceEdge) (hTarget : edge.1.1 = first)
    (hZero : data.localRamification vertex
      ((data.vertexPartition vertex).toBlock edge.1.2) = 0) :
    data.sourceEdge first (data.sourceEdge second edge.1.2).1.2 = edge := by
  have hIdem : (data.edgePartition first).repr edge.1.2 = edge.1.2 := by
    rw [← hTarget]
    exact edge.2
  have hSecondRel : (data.edgePartition second).Rel
      edge.1.2 ((data.edgePartition second).repr edge.1.2) :=
    (data.edgePartition second).rel_repr_right edge.1.2
  have hVertexRel : (data.vertexPartition vertex).Rel
      edge.1.2 ((data.edgePartition second).repr edge.1.2) :=
    (edgePartition_rel_iff_of_divalent_localRamification_zero data vertex
      hDivalent edge.1.2 hZero second hSecond _).1 hSecondRel
  have hFirstRel : (data.edgePartition first).Rel
      edge.1.2 ((data.edgePartition second).repr edge.1.2) :=
    (edgePartition_rel_iff_of_divalent_localRamification_zero data vertex
      hDivalent edge.1.2 hZero first hFirst _).2 hVertexRel
  apply Subtype.ext
  apply Prod.ext
  · exact hTarget.symm
  · show (data.edgePartition first).repr
      ((data.edgePartition second).repr edge.1.2) = edge.1.2
    unfold SheetPartition.Rel at hFirstRel
    rw [← hFirstRel, hIdem]


/-- Draisma--Vargas `lemma-equal-columns`, dangling form: at a divalent target
vertex whose blocks all have vanishing local ramification *as far as the
surviving occurrences see*, the two columns of the honest stable-source length
matrix indexed by the incident target occurrences are equal.  A block all of
whose incident occurrences are dangling is invisible to both columns, so it is
allowed to carry ramification. -/
theorem matrix_column_eq_of_divalent_of_surviving_localRamification_zero
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    {data : GluingDatum target degree}
    (labelling : StableLengthMatrixLabelling data coordinate)
    (vertex : target.V)
    (hDivalent : (GluingDatum.incidentEdges vertex).card = 2)
    (hSurvivingBlocks : ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
      edge.1.1 ∈ GluingDatum.incidentEdges vertex →
      data.localRamification vertex
        ((data.vertexPartition vertex).toBlock edge.1.2) = 0)
    {first second : target.edges} (hNe : first ≠ second)
    (hFirst : first ∈ GluingDatum.incidentEdges vertex)
    (hSecond : second ∈ GluingDatum.incidentEdges vertex)
    (row : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix labelling.presentation row
        (labelling.targetEdge.symm first) =
      GluingDatum.LengthMatrixPresentation.matrix labelling.presentation row
        (labelling.targetEdge.symm second) := by
  classical
  have hConvert : ∀ item : target.edges,
      GluingDatum.LengthMatrixPresentation.matrix labelling.presentation row
          (labelling.targetEdge.symm item) =
        ∑ edge ∈ (Finset.univ : Finset data.SourceEdge).filter
            (fun edge ↦ (∃ hSurvives : ¬ IsDangling data edge,
                labelling.row (NonDanglingEdge.stablePath
                  (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = row) ∧
              edge.1.1 = item),
          (1 : ℚ) / data.sourceEdgeIndex edge := by
    intro item
    have hNodup : (labelling.path row).Nodup := by
      unfold StableLengthMatrixLabelling.path
      exact List.Nodup.filter _ (Finset.univ.nodup_toList)
    have hToFinset : (labelling.path row).toFinset =
        (Finset.univ : Finset data.SourceEdge).filter
          (fun edge ↦ ∃ hSurvives : ¬ IsDangling data edge,
            labelling.row (NonDanglingEdge.stablePath
              (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = row) := by
      ext edge
      simp [List.mem_toFinset, labelling.mem_path_iff]
    calc
      GluingDatum.LengthMatrixPresentation.matrix labelling.presentation row
            (labelling.targetEdge.symm item)
          = ((labelling.path row).map fun edge ↦
              GluingDatum.LengthMatrixPresentation.coefficient
                labelling.presentation edge
                (labelling.targetEdge.symm item)).sum := rfl
      _ = ∑ edge ∈ (labelling.path row).toFinset,
            GluingDatum.LengthMatrixPresentation.coefficient
              labelling.presentation edge
              (labelling.targetEdge.symm item) :=
          (List.sum_toFinset _ hNodup).symm
      _ = ∑ edge ∈ (Finset.univ : Finset data.SourceEdge).filter
              (fun edge ↦ ∃ hSurvives : ¬ IsDangling data edge,
                labelling.row (NonDanglingEdge.stablePath
                  (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = row),
            GluingDatum.LengthMatrixPresentation.coefficient
              labelling.presentation edge
              (labelling.targetEdge.symm item) := by
          rw [hToFinset]
      _ = ∑ edge ∈ ((Finset.univ : Finset data.SourceEdge).filter
              (fun edge ↦ ∃ hSurvives : ¬ IsDangling data edge,
                labelling.row (NonDanglingEdge.stablePath
                  (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = row)).filter
              (fun edge ↦ edge.1.1 = item),
            (1 : ℚ) / data.sourceEdgeIndex edge := by
          conv_rhs => rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro edge _
          by_cases hCase : edge.1.1 = item
          · rw [ite_eq_left hCase]
            simp [GluingDatum.LengthMatrixPresentation.coefficient,
              StableLengthMatrixLabelling.presentation, hCase]
          · rw [ite_eq_right hCase]
            apply GluingDatum.LengthMatrixPresentation.coefficient_eq_zero_of_target_ne
            simp only [StableLengthMatrixLabelling.presentation,
              Equiv.apply_symm_apply]
            exact fun hEqual ↦ hCase hEqual.symm
      _ = ∑ edge ∈ (Finset.univ : Finset data.SourceEdge).filter
              (fun edge ↦ (∃ hSurvives : ¬ IsDangling data edge,
                  labelling.row (NonDanglingEdge.stablePath
                    (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = row) ∧
                edge.1.1 = item),
            (1 : ℚ) / data.sourceEdgeIndex edge := by
          rw [Finset.filter_filter]
  have hTransfer : ∀ (one two : target.edges),
      one ∈ GluingDatum.incidentEdges vertex →
      two ∈ GluingDatum.incidentEdges vertex → one ≠ two →
      ∀ edge ∈ (Finset.univ : Finset data.SourceEdge).filter
        (fun edge ↦ (∃ hSurvives : ¬ IsDangling data edge,
            labelling.row (NonDanglingEdge.stablePath
              (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = row) ∧
          edge.1.1 = one),
      data.sourceEdge two edge.1.2 ∈
        (Finset.univ : Finset data.SourceEdge).filter
          (fun edge ↦ (∃ hSurvives : ¬ IsDangling data edge,
              labelling.row (NonDanglingEdge.stablePath
                (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = row) ∧
            edge.1.1 = two) := by
    intro one two hOne hTwo hOneTwo edge hEdge
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (Finset.mem_filter.mp hEdge).2
    have hSelf : data.sourceEdge one edge.1.2 = edge := by
      rw [← hTarget]
      exact GluingDatum.sourceEdge_self data edge
    have hZero : data.localRamification vertex
        ((data.vertexPartition vertex).toBlock edge.1.2) = 0 :=
      hSurvivingBlocks edge hSurvives (by rw [hTarget]; exact hOne)
    have hOneSurvives : ¬ IsDangling data (data.sourceEdge one edge.1.2) := by
      rw [hSelf]
      exact hSurvives
    have hTwoSurvives : ¬ IsDangling data (data.sourceEdge two edge.1.2) :=
      fun hDangling ↦ hOneSurvives
        ((isDangling_sourceEdge_iff_of_divalent_localRamification_zero data
          vertex hDivalent edge.1.2 hZero hOneTwo hOne hTwo).2 hDangling)
    have hPathEq := stablePath_sourceEdge_eq_of_divalent_localRamification_zero
      data vertex hDivalent edge.1.2 hZero hOneTwo hOne hTwo hOneSurvives
      hTwoSurvives
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hTwoSurvives, ?_⟩, rfl⟩
    rw [← hPathEq,
      show (⟨data.sourceEdge one edge.1.2, hOneSurvives⟩ :
        NonDanglingEdge data) = ⟨edge, hSurvives⟩ from Subtype.ext hSelf]
    exact hRow
  rw [hConvert first, hConvert second]
  refine Finset.sum_nbij' (fun edge ↦ data.sourceEdge second edge.1.2)
    (fun edge ↦ data.sourceEdge first edge.1.2)
    (hTransfer first second hFirst hSecond hNe)
    (hTransfer second first hSecond hFirst (Ne.symm hNe)) ?_ ?_ ?_
  · intro edge hEdge
    obtain ⟨⟨hSurvives, _⟩, hTarget⟩ := (Finset.mem_filter.mp hEdge).2
    exact sourceEdge_transport_left_inverse_of_divalent_localRamification_zero
      data vertex hDivalent first second hFirst hSecond edge hTarget
      (hSurvivingBlocks edge hSurvives (by rw [hTarget]; exact hFirst))
  · intro edge hEdge
    obtain ⟨⟨hSurvives, _⟩, hTarget⟩ := (Finset.mem_filter.mp hEdge).2
    exact sourceEdge_transport_left_inverse_of_divalent_localRamification_zero
      data vertex hDivalent second first hSecond hFirst edge hTarget
      (hSurvivingBlocks edge hSurvives (by rw [hTarget]; exact hSecond))
  · intro edge hEdge
    obtain ⟨⟨hSurvives, _⟩, hTarget⟩ := (Finset.mem_filter.mp hEdge).2
    have hZero : data.localRamification vertex
        ((data.vertexPartition vertex).toBlock edge.1.2) = 0 :=
      hSurvivingBlocks edge hSurvives (by rw [hTarget]; exact hFirst)
    have hSelf : data.sourceEdge first edge.1.2 = edge := by
      rw [← hTarget]
      exact GluingDatum.sourceEdge_self data edge
    have hFirstIndex := sourceEdgeIndex_eq_of_divalent_localRamification_zero
      data vertex hDivalent edge.1.2 hZero first hFirst
    rw [hSelf] at hFirstIndex
    have hSecondIndex :=
      sourceEdgeIndex_eq_of_divalent_localRamification_zero data vertex
        hDivalent edge.1.2 hZero second hSecond
    rw [hFirstIndex, hSecondIndex]


/-! ## Dangling blocks have vanishing ramification -/

/-- A change-minimal target vertex has at least one incident occurrence: a
target vertex with none would carry change three, while every block above it
would contribute an even local ramification. -/
theorem incidentEdges_card_pos_of_changeMinimalAt
    (data : GluingDatum target degree) (vertex : target.V)
    (hMinimal : data.ChangeMinimalAt vertex) :
    0 < (GluingDatum.incidentEdges vertex).card := by
  by_contra hZero
  have hEmpty : GluingDatum.incidentEdges vertex = ∅ :=
    Finset.card_eq_zero.mp (by omega)
  have hCard : (GluingDatum.incidentEdges vertex).card = 0 := by
    rw [hEmpty]
    simp
  have hForm : ∀ block : (data.vertexPartition vertex).Blocks,
      data.localRamification vertex block =
        2 * ((data.vertexPartition vertex).blockCard block.1 : ℤ) - 2 := by
    intro block
    unfold GluingDatum.localRamification
    rw [hEmpty]
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero]
    ring
  have hChange : data.targetChange vertex = 3 := by
    unfold GluingDatum.ChangeMinimalAt GluingDatum.targetExcess at hMinimal
    rw [hCard] at hMinimal
    omega
  have hSum : (∑ block : (data.vertexPartition vertex).Blocks,
      data.localRamification vertex block) = 3 := hChange
  rw [Finset.sum_congr rfl fun block _ ↦ hForm block, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hSum
  omega

/-- Draisma--Vargas `lemma-dangling-rphi`, divalent case: a block above a
divalent target vertex all of whose incident occurrences are dangling has
vanishing local ramification.  If it carried the single unit of change of a
change-minimal divalent vertex, the two columns of the length matrix at that
vertex would agree. -/
theorem localRamification_eq_zero_of_divalent_of_forall_isDangling
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree) (hValid : data.Valid)
    (labelling : StableLengthMatrixLabelling data coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix
      labelling.presentation).det ≠ 0)
    (vertex : data.SourceVertex)
    (hMinimal : data.ChangeMinimalAt vertex.1.1)
    (hDivalent : (GluingDatum.incidentEdges vertex.1.1).card = 2)
    (hDangling : ∀ edge : IncidentSourceEdge data vertex,
      IsDangling data edge.1) :
    data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0 := by
  classical
  by_contra hNonzero
  have hNonneg : ∀ block : (data.vertexPartition vertex.1.1).Blocks,
      0 ≤ data.localRamification vertex.1.1 block := fun block ↦
    data.localRamification_nonneg vertex.1.1 (hValid.2 vertex.1.1) block
  have hChange : data.targetChange vertex.1.1 = 1 := by
    unfold GluingDatum.ChangeMinimalAt GluingDatum.targetExcess at hMinimal
    rw [hDivalent] at hMinimal
    omega
  have hSum : (∑ block : (data.vertexPartition vertex.1.1).Blocks,
      data.localRamification vertex.1.1 block) = 1 := hChange
  have hLe : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ ≤ 1 := by
    rw [← hSum]
    exact Finset.single_le_sum (fun block _ ↦ hNonneg block) (Finset.mem_univ _)
  have hSelf : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 1 := by
    have := hNonneg ⟨vertex.1.2, vertex.2⟩
    omega
  have hOthers : ∀ block : (data.vertexPartition vertex.1.1).Blocks,
      block ≠ ⟨vertex.1.2, vertex.2⟩ →
      data.localRamification vertex.1.1 block = 0 := by
    intro block hNe
    have hSplit := Finset.sum_erase_add
      (Finset.univ : Finset (data.vertexPartition vertex.1.1).Blocks)
      (fun block ↦ data.localRamification vertex.1.1 block)
      (Finset.mem_univ (⟨vertex.1.2, vertex.2⟩ :
        (data.vertexPartition vertex.1.1).Blocks))
    have hEraseSum :
        (∑ other ∈ (Finset.univ :
            Finset (data.vertexPartition vertex.1.1).Blocks).erase
              ⟨vertex.1.2, vertex.2⟩,
          data.localRamification vertex.1.1 other) = 0 := by
      rw [hSelf] at hSplit
      omega
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun other _ ↦ hNonneg other)).mp hEraseSum block
      (Finset.mem_erase.mpr ⟨hNe, Finset.mem_univ _⟩)
  have hSurvivingBlocks : ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
      edge.1.1 ∈ GluingDatum.incidentEdges vertex.1.1 →
      data.localRamification vertex.1.1
        ((data.vertexPartition vertex.1.1).toBlock edge.1.2) = 0 := by
    intro edge hSurvives hMember
    refine hOthers _ ?_
    intro hEqual
    apply hSurvives
    have hRepr : (data.vertexPartition vertex.1.1).repr edge.1.2 = vertex.1.2 :=
      congrArg Subtype.val hEqual
    refine hDangling ⟨edge, ?_⟩
    apply (incident_iff_target_mem_and_rel data edge vertex).2
    refine ⟨hMember, ?_⟩
    show (data.vertexPartition vertex.1.1).repr vertex.1.2 =
      (data.vertexPartition vertex.1.1).repr edge.1.2
    rw [hRepr, vertex.2]
  obtain ⟨first, second, hNe, hPair⟩ := Finset.card_eq_two.mp hDivalent
  have hFirst : first ∈ GluingDatum.incidentEdges vertex.1.1 := by
    rw [hPair]; simp
  have hSecond : second ∈ GluingDatum.incidentEdges vertex.1.1 := by
    rw [hPair]; simp
  apply hDet
  refine Matrix.det_zero_of_column_eq
    (i := labelling.targetEdge.symm first)
    (j := labelling.targetEdge.symm second)
    (fun hEqual ↦ hNe (labelling.targetEdge.symm.injective hEqual)) ?_
  intro row
  exact matrix_column_eq_of_divalent_of_surviving_localRamification_zero
    labelling vertex.1.1 hDivalent hSurvivingBlocks hNe hFirst hSecond row

/-- Draisma--Vargas `lemma-dangling-rphi`: in a change-minimal datum with a
nonsingular stable length matrix, a block all of whose incident source
occurrences are dangling has vanishing local ramification. -/
theorem localRamification_eq_zero_of_forall_isDangling
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (labelling : StableLengthMatrixLabelling data coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix
      labelling.presentation).det ≠ 0)
    (vertex : data.SourceVertex)
    (hDangling : ∀ edge : IncidentSourceEdge data vertex,
      IsDangling data edge.1) :
    data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0 := by
  have hNoDangling := labelling.noDanglingTargetFibres_of_det_ne_zero hDet
  have hPos := incidentEdges_card_pos_of_changeMinimalAt data vertex.1.1
    (hMinimal vertex.1.1)
  have hLe := data.incidentEdges_card_le_three_of_changeMinimalAt hValid
    vertex.1.1 (hMinimal vertex.1.1)
  interval_cases hValency : (GluingDatum.incidentEdges vertex.1.1).card
  · rcases leaf_block_dichotomy data hValid hNoDangling vertex.1.1 hValency
        (hMinimal vertex.1.1) ⟨vertex.1.2, vertex.2⟩ with
      ⟨_, _, hZero⟩ | ⟨_, _, _, edge, hSurvives⟩
    · exact hZero
    · exact absurd (hDangling edge) hSurvives
  · exact localRamification_eq_zero_of_divalent_of_forall_isDangling data hValid
      labelling hDet vertex (hMinimal vertex.1.1) hValency hDangling
  · have hChange : data.targetChange vertex.1.1 = 0 := by
      have hMinimalAt := hMinimal vertex.1.1
      unfold GluingDatum.ChangeMinimalAt GluingDatum.targetExcess at hMinimalAt
      rw [hValency] at hMinimalAt
      omega
    exact localRamification_eq_zero_of_targetChange_zero data hValid vertex.1.1
      hChange ⟨vertex.1.2, vertex.2⟩


/-! ## The dangling walk

The numerical half of Draisma--Vargas `lemma-dangling-no-glue` is available
from the sections above: at the inner endpoint of a dangling cut all occurrences
are
dangling, so the block has vanishing ramification, and Observation I turns
"every other incident occurrence is unramified" into "the cut occurrence is
unramified".  The walk therefore only needs the graph-theoretic statement that
the recursion is well founded: deleting an interior occurrence of a dangling
side splits that side, which is a tree, into strictly smaller dangling sides.
That statement is isolated as `DanglingSideDescent`; it is a property of the
occurrence-safe cut certificate alone and involves no gluing numerics.
-/

/-- The graph-theoretic input of the dangling walk: every source occurrence at
the inner endpoint of a dangling cut, other than the cut occurrence itself, is
again dangling along a strictly smaller cut.

This holds because a dangling side is connected of genus zero, hence a tree
whose unique crossing occurrence sits at the inner endpoint: any other
occurrence there is interior, and deleting it splits the tree into a strictly
smaller genus-zero piece with connected complement.  It is stated here as a
hypothesis because it is a statement about `DanglingSide` alone, with no
gluing-datum numerics in it. -/
def DanglingSideDescent (data : GluingDatum target degree) : Prop :=
  ∀ (inner outer : data.SourceVertex)
    (cut : DanglingSide data.sourceGraph inner outer)
    (crossing other : data.SourceEdge),
    (data.sourceEnds crossing = (inner, outer) ∨
      data.sourceEnds crossing = (outer, inner)) →
    Incident data other inner → other ≠ crossing →
    ∃ (first second : data.SourceVertex)
      (smaller : DanglingSide data.sourceGraph first second),
      (data.sourceEnds other = (first, second) ∨
        data.sourceEnds other = (second, first)) ∧
      smaller.side.card < cut.side.card

/-- The dangling walk: under the descent property every occurrence carrying a
dangling cut is unramified.  The induction is on the cardinality of the side
of the cut. -/
theorem sourceEdgeIndex_eq_one_of_danglingSide
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (labelling : StableLengthMatrixLabelling data coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix
      labelling.presentation).det ≠ 0)
    (hDescent : DanglingSideDescent data) :
    ∀ (size : ℕ) (inner outer : data.SourceVertex)
      (cut : DanglingSide data.sourceGraph inner outer)
      (edge : data.SourceEdge), cut.side.card = size →
      (data.sourceEnds edge = (inner, outer) ∨
        data.sourceEnds edge = (outer, inner)) →
      data.sourceEdgeIndex edge = 1 := by
  intro size
  induction size using Nat.strong_induction_on with
  | _ size ih =>
    intro inner outer cut edge hCard hEnds
    have hIncident : Incident data edge inner :=
      incident_of_sourceEnds data hEnds
    have hSmaller : ∀ other : IncidentSourceEdge data inner,
        other ≠ ⟨edge, hIncident⟩ →
        IsDangling data other.1 ∧ data.sourceEdgeIndex other.1 = 1 := by
      intro other hNe
      obtain ⟨first, second, smaller, hOtherEnds, hLess⟩ :=
        hDescent inner outer cut edge other.1 hEnds other.2
          (fun hEqual ↦ hNe (Subtype.ext hEqual))
      refine ⟨isDangling_of_danglingSide data hOtherEnds smaller, ?_⟩
      exact ih smaller.side.card (hCard ▸ hLess) first second smaller other.1
        rfl hOtherEnds
    have hAllDangling : ∀ item : IncidentSourceEdge data inner,
        IsDangling data item.1 := by
      intro item
      by_cases hCase : item = ⟨edge, hIncident⟩
      · rw [hCase]
        exact isDangling_of_danglingSide data hEnds cut
      · exact (hSmaller item hCase).1
    have hZero := localRamification_eq_zero_of_forall_isDangling data hValid
      hMinimal labelling hDet inner hAllDangling
    have hBound : (data.sourceEdgeIndex edge : ℤ) ≤
        data.localRamification inner.1.1 ⟨inner.1.2, inner.2⟩ + 1 :=
      sourceEdgeIndex_le_localRamification_add_one data inner
        ⟨edge, hIncident⟩ fun item hItemNe ↦ (hSmaller item hItemNe).2
    rw [hZero] at hBound
    have hPos := sourceEdgeIndex_pos data edge
    omega

/-- Draisma--Vargas `lemma-dangling-no-glue`, edge form: a change-minimal
gluing datum whose honest stable length matrix is nonsingular satisfies
dangling-no-glue, provided the dangling cuts admit the tree descent. -/
theorem danglingEdgeNoGlue_of_changeMinimal_of_det_ne_zero
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (labelling : StableLengthMatrixLabelling data coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix
      labelling.presentation).det ≠ 0)
    (hDescent : DanglingSideDescent data) :
    DanglingEdgeNoGlue data := by
  intro edge hDangling
  rcases hDangling with hSide | hSide
  · exact hSide.elim fun cut ↦
      sourceEdgeIndex_eq_one_of_danglingSide data hValid hMinimal labelling
        hDet hDescent cut.side.card _ _ cut edge rfl (Or.inl rfl)
  · exact hSide.elim fun cut ↦
      sourceEdgeIndex_eq_one_of_danglingSide data hValid hMinimal labelling
        hDet hDescent cut.side.card _ _ cut edge rfl (Or.inr rfl)

/-- The pendant case of dangling-no-glue, with no descent hypothesis: if every
dangling occurrence has an endpoint of source degree one, a valid,
change-minimal datum without dangling target fibres satisfies
dangling-no-glue. -/
theorem danglingEdgeNoGlue_of_forall_pendant
    (data : GluingDatum target degree) (hValid : data.Valid)
    (hNoDangling : NoDanglingTargetFibres data)
    (hMinimal : data.ChangeMinimal)
    (hPendant : ∀ edge : data.SourceEdge, IsDangling data edge →
      vertex_degree data.sourceGraph (data.sourceEnds edge).1 = 1 ∨
        vertex_degree data.sourceGraph (data.sourceEnds edge).2 = 1) :
    DanglingEdgeNoGlue data := fun edge hDangling ↦
  sourceEdgeIndex_eq_one_of_vertex_degree_eq_one data hValid hNoDangling
    hMinimal edge (hPendant edge hDangling)

end DraismaVargas.LocalCases.StableLocalProperties
