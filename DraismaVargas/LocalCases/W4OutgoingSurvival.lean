module

public import DraismaVargas.LocalCases.W4StableGraph

@[expose] public section

/-!
# The outgoing W4 new-occurrence census

`W4StableGraph` records the actual source genus, the exact pruning of retained
old occurrences, and the exact *old* survivor census above every W4 wall block.
Of the *new* occurrences it treats only the nd2 block: all sheets dangle when
the two active branches share a side, and the single regrown occurrence
survives when they do not.

This module supplies the rest of the new-occurrence census:

* nd3 new survival together with its residual pruning;
* new pruning above an entirely dangling wall block;
* the complete surviving-occurrence census at both expanded endpoints, for
  each of the three source pictures, together with the literal surviving
  valencies `0`, `2` and `3` that census produces.

Everything below is a statement about literal quotient-source **occurrences**
of an actual W4 candidate.  In particular none of it reads the raw path lists
carried by `AuxR0SourceInput.presentedFamily`: those lists are not certified to
survive and are not certified to be the actual `StablePath` rows of the
outgoing datum.  The occurrence-induced stable-row and branch-incidence
equivalences, and the identification of the presented matrices with the
natural stable-length matrices, are built on top of this census and are not
proved here.
-/

namespace DraismaVargas.LocalCases.W4OutgoingSurvival

open DraismaVargas.Infrastructure TargetExpansion
open ResolutionM11 W4Assembly GlobalW4 W4StableSource W4StableGraph
open W4SourceClassification

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

/-! ## Naming the two expanded endpoints by a Boolean side

`false` is the retained copy of the wall and `true` is the fresh copy, the
same convention as `TargetExpansion.expandedEndpoint` and
`W4TargetPairings.Pairing.labelRight`.
-/

/-- The expanded target endpoint on one side of the regrown W4 edge. -/
def sideVertex (target : CFGraph) (wall : target.V) (side : Bool) :
    TargetExpansion.Vertex target :=
  if side then freshVertex target else oldVertex target wall

@[simp] theorem sideVertex_false (target : CFGraph) (wall : target.V) :
    sideVertex target wall false = oldVertex target wall := rfl

@[simp] theorem sideVertex_true (target : CFGraph) (wall : target.V) :
    sideVertex target wall true = freshVertex target := rfl

/-- The endpoint partition of a local resolution on one side. -/
def sidePartition {d : ℕ} (resolution : LocalResolution d) (side : Bool) :
    SheetPartition d :=
  if side then resolution.right else resolution.left

@[simp] theorem sidePartition_false {d : ℕ} (resolution : LocalResolution d) :
    sidePartition resolution false = resolution.left := rfl

@[simp] theorem sidePartition_true {d : ℕ} (resolution : LocalResolution d) :
    sidePartition resolution true = resolution.right := rfl

/-- The new edge refines both endpoint partitions. -/
theorem newEdge_refines_sidePartition {d : ℕ} (resolution : LocalResolution d)
    (side : Bool) :
    resolution.newEdge.Refines (sidePartition resolution side) := by
  cases side
  · exact resolution.edge_refines_left
  · exact resolution.edge_refines_right

theorem bool_eq_not_of_ne {first second : Bool} (h : first ≠ second) :
    first = ! second := by
  cases first <;> cases second <;> simp_all

/-- Passing to the canonical representative does not change the block
relation. -/
theorem rel_repr_left_iff {d : ℕ} (partition : SheetPartition d)
    (first second : Fin d) :
    partition.Rel (partition.repr first) second ↔
      partition.Rel first second := by
  simp [SheetPartition.Rel, partition.repr_idem]

/-! ## Reading the pasted W4 endpoints one wall block at a time -/

theorem wholeResolution_side_block
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (side : Bool) (sheet : Fin degree) :
    (sidePartition (wholeResolution data star pattern pairing) side).block
        sheet =
      (sidePartition (blockwiseResolution data star pattern pairing
        ((data.vertexPartition wall).repr sheet)) side).block sheet := by
  cases side
  · exact wholeResolution_left_block data star pattern pairing sheet
  · exact wholeResolution_right_block data star pattern pairing sheet

theorem wholeResolution_side_rel
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (side : Bool) (first second : Fin degree) :
    (sidePartition (wholeResolution data star pattern pairing) side).Rel
        first second ↔
      (sidePartition (blockwiseResolution data star pattern pairing
        ((data.vertexPartition wall).repr first)) side).Rel first second := by
  rw [← SheetPartition.mem_block_iff, ← SheetPartition.mem_block_iff,
    wholeResolution_side_block]

theorem wholeResolution_newEdge_rel
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (first second : Fin degree) :
    (wholeResolution data star pattern pairing).newEdge.Rel first second ↔
      (blockwiseResolution data star pattern pairing
        ((data.vertexPartition wall).repr first)).newEdge.Rel first second := by
  rw [← SheetPartition.mem_block_iff, ← SheetPartition.mem_block_iff,
    wholeResolution_newEdge_block]

/-- Both expanded endpoint partitions refine the old wall partition, so every
occurrence incident to an expanded endpoint lies above the wall block of its
sheet. -/
theorem sidePartition_refines_wall
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3) (side : Bool) :
    (sidePartition (wholeResolution data star pattern pairing) side).Refines
      (data.vertexPartition wall) := by
  cases side
  · exact SheetPartition.IsJoin.left_refines
      (wholeResolution_contracts data star pattern pairing)
  · exact SheetPartition.IsJoin.right_refines
      (wholeResolution_contracts data star pattern pairing)

/-- The assembled new edge refines the old wall partition. -/
theorem newEdge_refines_wall
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3) :
    (wholeResolution data star pattern pairing).newEdge.Refines
      (data.vertexPartition wall) :=
  (wholeResolution data star pattern pairing).edge_refines_left.trans
    (SheetPartition.IsJoin.left_refines
      (wholeResolution_contracts data star pattern pairing))

/-- A regrown occurrence met by an expanded endpoint of a wall block has its
sheet in that block. -/
theorem wall_rel_of_side_rel_newEdge_repr
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3) (side : Bool)
    (sourceBlock : WallBlock data wall) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet)
    (other : Fin degree)
    (hRel : (sidePartition (wholeResolution data star pattern pairing) side).Rel
      sheet ((wholeResolution data star pattern pairing).newEdge.repr other)) :
    (data.vertexPartition wall).Rel sourceBlock.1 other := by
  have hFirst : (data.vertexPartition wall).Rel sheet
      ((wholeResolution data star pattern pairing).newEdge.repr other) :=
    (sidePartition_refines_wall data star pattern pairing side).rel hRel
  have hSecond : (data.vertexPartition wall).Rel other
      ((wholeResolution data star pattern pairing).newEdge.repr other) :=
    (newEdge_refines_wall data star pattern pairing).rel
      ((wholeResolution data star pattern pairing).newEdge.rel_repr_right other)
  exact hSheet.trans (hFirst.trans hSecond.symm)

/-- A canonical branch occurrence through a wall block is met by an expanded
endpoint whose partition is still the whole wall partition. -/
theorem side_rel_sourceEdge_repr_of_wall
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3) (side : Bool)
    (sourceBlock : WallBlock data wall) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet)
    (hSide : sidePartition (blockwiseResolution data star pattern pairing
        sourceBlock.1) side = data.vertexPartition wall)
    (label : Fin 4) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel sourceBlock.1 other) :
    (sidePartition (wholeResolution data star pattern pairing) side).Rel sheet
      (data.sourceEdge (star.edge label) other).1.2 := by
  rw [wholeResolution_side_rel, hSheet.symm.trans sourceBlock.2, hSide]
  exact hSheet.symm.trans (hOther.trans
    ((star.edgePartition_refines_wall data label).rel
      ((data.edgePartition (star.edge label)).rel_repr_right other)))

/-- Everything an expanded endpoint sees lies above the wall block of its own
sheet. -/
theorem wallBlock_of_side_rel
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3) (side : Bool)
    (sourceBlock : WallBlock data wall) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet)
    (other : Fin degree)
    (hRel : (sidePartition (wholeResolution data star pattern pairing) side).Rel
      sheet other) :
    WallBlock.ofSheet data wall other = sourceBlock :=
  WallBlock.ofSheet_eq_of_rel data wall sourceBlock other
    (hSheet.trans ((sidePartition_refines_wall data star pattern pairing
      side).rel hRel))

/-! ## Occurrence distinctness in an assembled candidate

Surviving incidence *counts* — not merely the sets of adjacent occurrences —
are what a stable-graph comparison has to preserve, so the census below is
accompanied by literal valencies.  These two lemmas are what turns a list of
named survivors into a count.
-/

theorem oldSourceEdge_injective {data : GluingDatum target degree}
    (candidate : BalancedGlobal.Candidate target degree data wall) :
    Function.Injective candidate.oldSourceEdge := by
  intro first second hEq
  have hTarget :
      occurrenceEquiv target wall candidate.right (some first.1.1) =
        occurrenceEquiv target wall candidate.right (some second.1.1) :=
    congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.1) hEq
  have hSheet : first.1.2 = second.1.2 :=
    congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.2) hEq
  apply Subtype.ext
  apply Prod.ext
  · exact Option.some.inj
      ((occurrenceEquiv target wall candidate.right).injective hTarget)
  · exact hSheet

theorem oldSourceEdge_ne_newSourceEdge {data : GluingDatum target degree}
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (old : data.SourceEdge) (sheet : Fin degree) :
    candidate.oldSourceEdge old ≠ candidate.newSourceEdge sheet := by
  intro hEq
  have hTarget :
      occurrenceEquiv target wall candidate.right (some old.1.1) =
        occurrenceEquiv target wall candidate.right none :=
    congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.1) hEq
  exact Option.some_ne_none _
    ((occurrenceEquiv target wall candidate.right).injective hTarget)

/-! ## The occurrence dictionary at an expanded endpoint -/

section Receipts

variable {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall}
  {pattern : Fin degree → BlockPattern} {pairing : Fin 3}

/-- The pasted resolution of a pairing candidate is the assembled W4
resolution. -/
theorem candidate_paste
    (receipts : PairingReceipts data star pattern pairing) :
    LocalResolution.paste (data.vertexPartition wall)
        receipts.candidate.resolution receipts.candidate.contracts =
      wholeResolution data star pattern pairing := rfl

/-- The outgoing vertex partition at an expanded endpoint is the assembled
endpoint partition on that side. -/
theorem datum_vertexPartition_sideVertex
    (receipts : PairingReceipts data star pattern pairing) (side : Bool) :
    receipts.candidate.datum.vertexPartition (sideVertex target wall side) =
      sidePartition (wholeResolution data star pattern pairing) side := by
  cases side
  · exact GlobalResolution.datum_vertexPartition_old_wall data wall
      receipts.candidate.right (wholeResolution data star pattern pairing)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ receipts.candidate.exterior)
  · rfl

/-- A retained old occurrence reaches an expanded endpoint exactly when its
target occurrence met the wall and was assigned to that side. -/
theorem oldSourceEdge_mem_incidentEdges_side_iff
    (receipts : PairingReceipts data star pattern pairing)
    (side : Bool) (old : data.SourceEdge) :
    (receipts.candidate.oldSourceEdge old).1.1 ∈
        GluingDatum.incidentEdges (sideVertex target wall side) ↔
      old.1.1 ∈ GluingDatum.incidentEdges wall ∧
        star.right pairing old.1.1 = side := by
  simp only [BalancedGlobal.Candidate.oldSourceEdge_target,
    GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    occurrenceEquiv_some]
  cases side
  · exact oldEnds_incident_oldVertex_iff target wall (star.right pairing) old.1.1
  · exact oldEnds_incident_freshVertex_iff target wall (star.right pairing)
      old.1.1

/-- The regrown occurrence reaches both expanded endpoints. -/
theorem newSourceEdge_mem_incidentEdges_side
    (receipts : PairingReceipts data star pattern pairing)
    (side : Bool) (sheet : Fin degree) :
    (receipts.candidate.newSourceEdge sheet).1.1 ∈
      GluingDatum.incidentEdges (sideVertex target wall side) := by
  simp only [BalancedGlobal.Candidate.newSourceEdge_target,
    GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    occurrenceEquiv_none]
  cases side
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Complete incidence criterion for a retained old occurrence at an expanded
endpoint. -/
theorem old_incident_side_iff
    (receipts : PairingReceipts data star pattern pairing)
    (side : Bool) (anchor : Fin degree) (old : data.SourceEdge) :
    Incident receipts.candidate.datum (receipts.candidate.oldSourceEdge old)
        (receipts.candidate.datum.sourceEndpoint
          (sideVertex target wall side) anchor) ↔
      (old.1.1 ∈ GluingDatum.incidentEdges wall ∧
          star.right pairing old.1.1 = side) ∧
        (sidePartition (wholeResolution data star pattern pairing) side).Rel
          anchor old.1.2 := by
  rw [incident_iff_target_mem_and_rel]
  have hVertex :
      (receipts.candidate.datum.sourceEndpoint
        (sideVertex target wall side) anchor).1.1 =
        sideVertex target wall side := rfl
  rw [hVertex, oldSourceEdge_mem_incidentEdges_side_iff receipts side old]
  refine and_congr_right (fun _ ↦ ?_)
  have hSheet :
      (receipts.candidate.datum.sourceEndpoint
        (sideVertex target wall side) anchor).1.2 =
        (receipts.candidate.datum.vertexPartition
          (sideVertex target wall side)).repr anchor := rfl
  rw [hSheet, datum_vertexPartition_sideVertex receipts side]
  exact rel_repr_left_iff _ _ _

/-- Complete incidence criterion for the regrown occurrence at an expanded
endpoint. -/
theorem new_incident_side_iff
    (receipts : PairingReceipts data star pattern pairing)
    (side : Bool) (anchor sheet : Fin degree) :
    Incident receipts.candidate.datum (receipts.candidate.newSourceEdge sheet)
        (receipts.candidate.datum.sourceEndpoint
          (sideVertex target wall side) anchor) ↔
      (sidePartition (wholeResolution data star pattern pairing) side).Rel
        anchor ((wholeResolution data star pattern pairing).newEdge.repr
          sheet) := by
  rw [incident_iff_target_mem_and_rel]
  have hVertex :
      (receipts.candidate.datum.sourceEndpoint
        (sideVertex target wall side) anchor).1.1 =
        sideVertex target wall side := rfl
  rw [hVertex]
  simp only [newSourceEdge_mem_incidentEdges_side receipts side sheet, true_and]
  have hSheet :
      (receipts.candidate.datum.sourceEndpoint
        (sideVertex target wall side) anchor).1.2 =
        (receipts.candidate.datum.vertexPartition
          (sideVertex target wall side)).repr anchor := rfl
  have hEdge : (receipts.candidate.newSourceEdge sheet).1.2 =
      (wholeResolution data star pattern pairing).newEdge.repr sheet := rfl
  rw [hSheet, hEdge, datum_vertexPartition_sideVertex receipts side]
  exact rel_repr_left_iff _ _ _

/-- Two regrown occurrences agree exactly when their sheets lie in one block
of the assembled new edge. -/
theorem newSourceEdge_eq_iff
    (receipts : PairingReceipts data star pattern pairing)
    (first second : Fin degree) :
    receipts.candidate.newSourceEdge first =
        receipts.candidate.newSourceEdge second ↔
      (wholeResolution data star pattern pairing).newEdge.Rel first second := by
  constructor
  · intro hEq
    have hSheet := congrArg (fun edge : receipts.candidate.datum.SourceEdge ↦
      edge.1.2) hEq
    exact hSheet
  · intro hRel
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact hRel

/-- Every regrown occurrence meets the expanded endpoint above its own
sheet. -/
theorem new_incident_side
    (receipts : PairingReceipts data star pattern pairing)
    (side : Bool) (sheet : Fin degree) :
    Incident receipts.candidate.datum (receipts.candidate.newSourceEdge sheet)
      (receipts.candidate.datum.sourceEndpoint
        (sideVertex target wall side) sheet) := by
  apply (new_incident_side_iff receipts side sheet sheet).mpr
  exact (newEdge_refines_sidePartition
    (wholeResolution data star pattern pairing) side).rel
    ((wholeResolution data star pattern pairing).newEdge.rel_repr_right sheet)

/-! ## Generic survival and pruning at an expanded endpoint

Both criteria below are the local valency-one exclusion of `W4StableGraph`
read through the occurrence dictionary.  They are stated for an arbitrary
pairing receipt, so that each of the three W4 pictures only has to supply its
own endpoint partition and its own old survivor census.
-/

/-- Pruning of retained old occurrences for an arbitrary pairing receipt.
Source-genus preservation is supplied by `pairingCandidate_sourceGenus`. -/
theorem old_isDangling_receipts_iff
    (receipts : PairingReceipts data star pattern pairing) (hValid : data.Valid)
    (old : data.SourceEdge) :
    IsDangling receipts.candidate.datum
        (receipts.candidate.oldSourceEdge old) ↔
      IsDangling data old :=
  ResolutionPruning.isDangling_oldSourceEdge_iff _ hValid
    (pairingCandidate_sourceGenus receipts) old

/-- When the endpoint partition on one side agrees with the assembled new edge
through a sheet, every regrown occurrence meeting that endpoint is the one
above the sheet itself. -/
theorem new_eq_of_incident_side
    (receipts : PairingReceipts data star pattern pairing)
    (side : Bool) (anchor sheet : Fin degree)
    (hBlocks :
      (sidePartition (wholeResolution data star pattern pairing) side).block
          anchor =
        (wholeResolution data star pattern pairing).newEdge.block anchor)
    (hIncident : Incident receipts.candidate.datum
      (receipts.candidate.newSourceEdge sheet)
      (receipts.candidate.datum.sourceEndpoint
        (sideVertex target wall side) anchor)) :
    receipts.candidate.newSourceEdge sheet =
      receipts.candidate.newSourceEdge anchor := by
  have hRel := (new_incident_side_iff receipts side anchor sheet).mp hIncident
  have hMem :
      (wholeResolution data star pattern pairing).newEdge.repr sheet ∈
        (sidePartition (wholeResolution data star pattern pairing)
          side).block anchor :=
    (SheetPartition.mem_block_iff _ _ _).mpr hRel
  rw [hBlocks] at hMem
  have hNewRel := (SheetPartition.mem_block_iff _ _ _).mp hMem
  apply (newSourceEdge_eq_iff receipts sheet anchor).mpr
  exact (((wholeResolution data star pattern pairing).newEdge.rel_repr_right
    sheet).trans hNewRel.symm)

/-- **Residual pruning.**  If the endpoint partition on one side agrees with
the assembled new edge through a sheet, and every old occurrence reaching that
endpoint was already dangling, then the regrown occurrence there dangles:
otherwise the endpoint would have surviving valency exactly one. -/
theorem new_dangles_of_side
    (receipts : PairingReceipts data star pattern pairing) (hValid : data.Valid)
    (side : Bool) (sheet : Fin degree)
    (hBlocks :
      (sidePartition (wholeResolution data star pattern pairing) side).block
          sheet =
        (wholeResolution data star pattern pairing).newEdge.block sheet)
    (hOld : ∀ old : data.SourceEdge,
      old.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing old.1.1 = side →
      (sidePartition (wholeResolution data star pattern pairing) side).Rel
        sheet old.1.2 →
      IsDangling data old) :
    IsDangling receipts.candidate.datum
      (receipts.candidate.newSourceEdge sheet) := by
  apply dangles_of_exhausted_singleton
    (receipts.candidate.datum_valid hValid).1
    (receipts.candidate.datum.sourceEndpoint
      (sideVertex target wall side) sheet)
    (receipts.candidate.newSourceEdge sheet)
    (new_incident_side receipts side sheet)
  intro edge hIncident hSurvives
  rcases ResolutionPruning.sourceEdge_cases receipts.candidate edge with
    ⟨old, rfl⟩ | ⟨other, rfl⟩
  · obtain ⟨⟨hMem, hSide⟩, hRel⟩ :=
      (old_incident_side_iff receipts side sheet old).mp hIncident
    exact absurd ((old_isDangling_receipts_iff receipts hValid old).mpr
      (hOld old hMem hSide hRel)) hSurvives
  · exact new_eq_of_incident_side receipts side sheet other hBlocks hIncident

/-- **New survival.**  If the endpoint partition on one side agrees with the
assembled new edge through a sheet and exactly one old survivor reaches that
endpoint, the regrown occurrence survives: otherwise that old survivor would
have surviving valency exactly one there. -/
theorem new_survives_of_side
    (receipts : PairingReceipts data star pattern pairing) (hValid : data.Valid)
    (side : Bool) (sheet : Fin degree) (first : data.SourceEdge)
    (hBlocks :
      (sidePartition (wholeResolution data star pattern pairing) side).block
          sheet =
        (wholeResolution data star pattern pairing).newEdge.block sheet)
    (hFirstMem : first.1.1 ∈ GluingDatum.incidentEdges wall)
    (hFirstSide : star.right pairing first.1.1 = side)
    (hFirstRel :
      (sidePartition (wholeResolution data star pattern pairing) side).Rel
        sheet first.1.2)
    (hFirstSurvives : ¬ IsDangling data first)
    (hOnly : ∀ old : data.SourceEdge,
      old.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing old.1.1 = side →
      (sidePartition (wholeResolution data star pattern pairing) side).Rel
        sheet old.1.2 →
      ¬ IsDangling data old → old = first) :
    ¬ IsDangling receipts.candidate.datum
      (receipts.candidate.newSourceEdge sheet) := by
  apply second_survives_of_exhausted_pair
    (receipts.candidate.datum_valid hValid).1
    (receipts.candidate.datum.sourceEndpoint
      (sideVertex target wall side) sheet)
    (receipts.candidate.oldSourceEdge first)
    (receipts.candidate.newSourceEdge sheet)
    ((old_incident_side_iff receipts side sheet first).mpr
      ⟨⟨hFirstMem, hFirstSide⟩, hFirstRel⟩)
    (fun hDangling ↦ hFirstSurvives
      ((old_isDangling_receipts_iff receipts hValid first).mp hDangling))
  intro edge hIncident hSurvives
  rcases ResolutionPruning.sourceEdge_cases receipts.candidate edge with
    ⟨old, rfl⟩ | ⟨other, rfl⟩
  · obtain ⟨⟨hMem, hSide⟩, hRel⟩ :=
      (old_incident_side_iff receipts side sheet old).mp hIncident
    exact Or.inl (congrArg receipts.candidate.oldSourceEdge
      (hOnly old hMem hSide hRel (fun hDangling ↦ hSurvives
        ((old_isDangling_receipts_iff receipts hValid old).mpr hDangling))))
  · exact Or.inr
      (new_eq_of_incident_side receipts side sheet other hBlocks hIncident)

end Receipts

/-! ## The three local W4 block resolutions, read on both sides -/

/-- A same-side nd2 block keeps the whole old block at the endpoint carrying
its two active branches and splits it into singleton sheets at the other
endpoint and on the new edge. -/
theorem nd2_same_activeSide_partition
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (anchor : Fin degree) (block : Nd2Block)
    (hPattern : pattern anchor = .nd2 block)
    (hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
      W4TargetPairings.Pairing.labelRight pairing block.second) :
    sidePartition (blockwiseResolution data star pattern pairing anchor)
        (W4TargetPairings.Pairing.labelRight pairing block.first) =
      data.vertexPartition wall := by
  cases hFirst : W4TargetPairings.Pairing.labelRight pairing block.first <;>
    simp [blockwiseResolution, hPattern, resolutionAt,
      ResolutionW4.nd2ResolutionForPairing, ResolutionW4.nd2Resolution,
      splitResolutionAt, sidePartition, hFirst, hSame ▸ hFirst]

/-- The other endpoint of a same-side nd2 block, and its new edge, are the
split of the old block. -/
theorem nd2_same_otherSide_partition
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (anchor : Fin degree) (block : Nd2Block)
    (hPattern : pattern anchor = .nd2 block)
    (hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
      W4TargetPairings.Pairing.labelRight pairing block.second) :
    sidePartition (blockwiseResolution data star pattern pairing anchor)
        (! W4TargetPairings.Pairing.labelRight pairing block.first) =
      (data.vertexPartition wall).splitBlock anchor := by
  cases hFirst : W4TargetPairings.Pairing.labelRight pairing block.first <;>
    simp [blockwiseResolution, hPattern, resolutionAt,
      ResolutionW4.nd2ResolutionForPairing, ResolutionW4.nd2Resolution,
      splitResolutionAt, sidePartition, hFirst, hSame ▸ hFirst]

theorem nd2_same_newEdge
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (anchor : Fin degree) (block : Nd2Block)
    (hPattern : pattern anchor = .nd2 block)
    (hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
      W4TargetPairings.Pairing.labelRight pairing block.second) :
    (blockwiseResolution data star pattern pairing anchor).newEdge =
      (data.vertexPartition wall).splitBlock anchor := by
  cases hFirst : W4TargetPairings.Pairing.labelRight pairing block.first <;>
    simp [blockwiseResolution, hPattern, resolutionAt,
      ResolutionW4.nd2ResolutionForPairing, ResolutionW4.nd2Resolution,
      splitResolutionAt, hFirst, hSame ▸ hFirst]

/-- An opposite-side nd2 block stays joined: both endpoints and the new edge
retain the whole old block. -/
theorem nd2_ne_side_partition
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (anchor : Fin degree) (block : Nd2Block) (side : Bool)
    (hPattern : pattern anchor = .nd2 block)
    (hNe : W4TargetPairings.Pairing.labelRight pairing block.first ≠
      W4TargetPairings.Pairing.labelRight pairing block.second) :
    sidePartition (blockwiseResolution data star pattern pairing anchor) side =
      data.vertexPartition wall := by
  cases side <;>
    simp [blockwiseResolution, hPattern, resolutionAt,
      ResolutionW4.nd2ResolutionForPairing, ResolutionW4.nd2Resolution,
      joinedResolutionAt, sidePartition, hNe]

theorem nd2_ne_newEdge
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (anchor : Fin degree) (block : Nd2Block)
    (hPattern : pattern anchor = .nd2 block)
    (hNe : W4TargetPairings.Pairing.labelRight pairing block.first ≠
      W4TargetPairings.Pairing.labelRight pairing block.second) :
    (blockwiseResolution data star pattern pairing anchor).newEdge =
      data.vertexPartition wall := by
  simp [blockwiseResolution, hPattern, resolutionAt,
    ResolutionW4.nd2ResolutionForPairing, ResolutionW4.nd2Resolution,
    joinedResolutionAt, hNe]

/-- On an nd3 block the endpoint carrying the isolated branch, and the new
edge, are the isolated branch's own old edge partition. -/
theorem nd3_singletonSide_partition
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (anchor : Fin degree) (block : Nd3Block)
    (hPattern : pattern anchor = .nd3 block) :
    sidePartition (blockwiseResolution data star pattern pairing anchor)
        (W4TargetPairings.Pairing.labelRight pairing
          (block.singletonLabel pairing)) =
      data.edgePartition (star.edge (block.singletonLabel pairing)) := by
  cases hSide : W4TargetPairings.Pairing.labelRight pairing
      (block.singletonLabel pairing) <;>
    simp [blockwiseResolution, hPattern, resolutionAt,
      ResolutionW4.nd3ResolutionForPairing, ResolutionW4.nd3Resolution,
      ResolutionCoarseFine.fineResolution, sidePartition, hSide]

/-- The other nd3 endpoint, carrying the two remaining active branches,
retains the whole old block. -/
theorem nd3_otherSide_partition
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (anchor : Fin degree) (block : Nd3Block)
    (hPattern : pattern anchor = .nd3 block) :
    sidePartition (blockwiseResolution data star pattern pairing anchor)
        (! W4TargetPairings.Pairing.labelRight pairing
          (block.singletonLabel pairing)) =
      data.vertexPartition wall := by
  cases hSide : W4TargetPairings.Pairing.labelRight pairing
      (block.singletonLabel pairing) <;>
    simp [blockwiseResolution, hPattern, resolutionAt,
      ResolutionW4.nd3ResolutionForPairing, ResolutionW4.nd3Resolution,
      ResolutionCoarseFine.fineResolution, sidePartition, hSide]

theorem nd3_newEdge
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (anchor : Fin degree) (block : Nd3Block)
    (hPattern : pattern anchor = .nd3 block) :
    (blockwiseResolution data star pattern pairing anchor).newEdge =
      data.edgePartition (star.edge (block.singletonLabel pairing)) := by
  unfold blockwiseResolution
  rw [hPattern]
  exact resolutionAt_nd3_newEdge data star pairing anchor block

/-! ## The source-side old survivor on an isolated nd3 branch -/

/-- Above an nd3 wall block, the only old survivor whose target occurrence is
assigned to the isolated branch's side is that branch's own canonical
occurrence.  This is a statement about the incoming datum alone. -/
theorem nd3_old_survivor_on_singletonSide_eq
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {sourceBlock : WallBlock data wall} {block : Nd3Block}
    (picture : AuxR0Nd3Picture data star sourceBlock block) (pairing : Fin 3)
    (old : data.SourceEdge)
    (hBlock : WallBlock.ofSheet data wall old.1.2 = sourceBlock)
    (hMem : old.1.1 ∈ GluingDatum.incidentEdges wall)
    (hSide : star.right pairing old.1.1 =
      star.right pairing (star.edge (block.singletonLabel pairing)))
    (hSurvives : ¬ IsDangling data old) :
    old = data.sourceEdge (star.edge (block.singletonLabel pairing))
      (picture.activeSheet (block.singletonLabel pairing)) := by
  obtain ⟨label, hLabel⟩ := star.exists_edge_eq old.1.1 hMem
  obtain ⟨other, hOtherActive, hOld⟩ :=
    picture.only_surviving old hBlock ⟨label, hLabel⟩ hSurvives
  have hOtherEdge : old.1.1 = star.edge other := by
    simpa only [GluingDatum.sourceEdge_target] using
      congrArg (fun edge : data.SourceEdge ↦ edge.1.1) hOld
  rw [hOtherEdge] at hSide
  have hOtherSide :
      W4TargetPairings.Pairing.labelRight pairing other =
        W4TargetPairings.Pairing.labelRight pairing
          (block.singletonLabel pairing) := by
    simpa only [W4TargetPairings.FourStar.right_edge] using hSide
  have hEq : other = block.singletonLabel pairing :=
    block.eq_singletonLabel_of_active_of_same_side pairing other
      ((block.mem_activeLabels other).mp hOtherActive) hOtherSide
  rw [hOld, hEq]

/-! ## The semantic family of a W4 source input -/

section Input

variable {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall}

/-- The pairing receipt that the semantic W4 family is built from. -/
theorem inputReceipts (input : AuxR0SourceInput data star)
    (pairing : Fin 3) :
    PairingReceipts data star input.activeProfile.blockPattern pairing :=
  (input.auxProfile.pairingCounts pairing).toPairingReceipts

/-- Reading an entirely dangling source picture recovers the harmless nd2
resolution pattern used by every actual candidate above that block. -/
theorem blockPattern_eq_dangling_of_picture
    (input : AuxR0SourceInput data star) (sourceBlock : WallBlock data wall)
    (old_dangling : ∀ (edge : data.SourceEdge) (label : Fin 4),
      WallBlock.ofSheet data wall edge.1.2 = sourceBlock →
      star.edge label = edge.1.1 → IsDangling data edge)
    (hPicture : input.blockPicture sourceBlock = .dangling old_dangling) :
    input.activeProfile.blockPattern sourceBlock.1 =
      .nd2 ActiveBlockClassification.danglingBlock := by
  rw [input.activeProfile.blockPattern_anchor]
  change (input.activeProfile.classification sourceBlock).kind.pattern = _
  rw [← input.blockPicture_kind sourceBlock, hPicture]
  rfl

variable [DecidableEq target.edges]

/-- The three actual members of the semantic family are the three pairing
candidates. -/
theorem presentedFamily_candidate (input : AuxR0SourceInput data star)
    (pairing : Fin 3) :
    (input.presentedFamily data star).candidate pairing =
      (inputReceipts input pairing).candidate := rfl

/-! ### nd3 new survival and residual pruning -/

/-- In an nd3 wall block, the regrown occurrence above a sheet of the isolated
branch's own old edge block survives.  At the isolated endpoint it is paired
with that branch's canonical retained survivor. -/
theorem nd3_new_survives_of_rel
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture)
    (sheet : Fin degree)
    (hRel : (data.edgePartition
        (star.edge (block.singletonLabel pairing))).Rel sheet
      (picture.activeSheet (block.singletonLabel pairing))) :
    ¬ IsDangling ((input.presentedFamily data star).candidate pairing).datum
      (((input.presentedFamily data star).candidate pairing).newSourceEdge
        sheet) := by
  classical
  show ¬ IsDangling (inputReceipts input pairing).candidate.datum
    ((inputReceipts input pairing).candidate.newSourceEdge sheet)
  have hActive : block.singletonLabel pairing ∈ block.activeLabels :=
    block.singletonLabel_mem_activeLabels pairing
  have hPattern : input.activeProfile.blockPattern sourceBlock.1 = .nd3 block :=
    blockPattern_eq_nd3_of_picture input sourceBlock block picture hPicture
  have hWallSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet :=
    (picture.active_sheet _ hActive).trans
      ((star.edgePartition_refines_wall data
        (block.singletonLabel pairing)).rel hRel).symm
  have hRepr : (data.vertexPartition wall).repr sheet = sourceBlock.1 :=
    hWallSheet.symm.trans sourceBlock.2
  have hSidePart :
      sidePartition (blockwiseResolution data star
          input.activeProfile.blockPattern pairing sourceBlock.1)
        (W4TargetPairings.Pairing.labelRight pairing
          (block.singletonLabel pairing)) =
        data.edgePartition (star.edge (block.singletonLabel pairing)) :=
    nd3_singletonSide_partition data star input.activeProfile.blockPattern
      pairing sourceBlock.1 block hPattern
  have hBlocks :
      (sidePartition (wholeResolution data star
          input.activeProfile.blockPattern pairing)
        (W4TargetPairings.Pairing.labelRight pairing
          (block.singletonLabel pairing))).block sheet =
        (wholeResolution data star input.activeProfile.blockPattern
          pairing).newEdge.block sheet := by
    rw [wholeResolution_side_block, wholeResolution_newEdge_block, hRepr,
      hSidePart, nd3_newEdge data star input.activeProfile.blockPattern pairing
        sourceBlock.1 block hPattern]
  refine new_survives_of_side (inputReceipts input pairing) input.valid _ sheet
    (data.sourceEdge (star.edge (block.singletonLabel pairing))
      (picture.activeSheet (block.singletonLabel pairing)))
    hBlocks (star.edge_mem_incidentEdges _)
    (W4TargetPairings.FourStar.right_edge star pairing _) ?_
    (picture.active_survives _ hActive) ?_
  · rw [wholeResolution_side_rel, hRepr, hSidePart]
    exact hRel.trans
      ((data.edgePartition (star.edge (block.singletonLabel pairing))).rel_repr_right _)
  · intro old hMem hSide hRelOld hSurvives
    exact nd3_old_survivor_on_singletonSide_eq picture pairing old
      (wallBlock_of_side_rel data star input.activeProfile.blockPattern pairing
        _ sourceBlock sheet hWallSheet old.1.2 hRelOld)
      hMem (hSide.trans (W4TargetPairings.FourStar.right_edge star pairing _).symm)
      hSurvives

/-- **Residual nd3 pruning.**  Every other regrown occurrence above an nd3
wall block dangles: at the isolated endpoint it would be the only survivor. -/
theorem nd3_new_dangles_of_not_rel
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet)
    (hNotRel : ¬ (data.edgePartition
        (star.edge (block.singletonLabel pairing))).Rel sheet
      (picture.activeSheet (block.singletonLabel pairing))) :
    IsDangling ((input.presentedFamily data star).candidate pairing).datum
      (((input.presentedFamily data star).candidate pairing).newSourceEdge
        sheet) := by
  classical
  show IsDangling (inputReceipts input pairing).candidate.datum
    ((inputReceipts input pairing).candidate.newSourceEdge sheet)
  have hPattern : input.activeProfile.blockPattern sourceBlock.1 = .nd3 block :=
    blockPattern_eq_nd3_of_picture input sourceBlock block picture hPicture
  have hRepr : (data.vertexPartition wall).repr sheet = sourceBlock.1 :=
    hSheet.symm.trans sourceBlock.2
  have hSidePart :
      sidePartition (blockwiseResolution data star
          input.activeProfile.blockPattern pairing sourceBlock.1)
        (W4TargetPairings.Pairing.labelRight pairing
          (block.singletonLabel pairing)) =
        data.edgePartition (star.edge (block.singletonLabel pairing)) :=
    nd3_singletonSide_partition data star input.activeProfile.blockPattern
      pairing sourceBlock.1 block hPattern
  refine new_dangles_of_side (inputReceipts input pairing) input.valid
    (W4TargetPairings.Pairing.labelRight pairing
      (block.singletonLabel pairing)) sheet ?_ ?_
  · rw [wholeResolution_side_block, wholeResolution_newEdge_block, hRepr,
      hSidePart, nd3_newEdge data star input.activeProfile.blockPattern pairing
        sourceBlock.1 block hPattern]
  · intro old hMem hSide hRelOld
    by_contra hSurvives
    apply hNotRel
    have hEq := nd3_old_survivor_on_singletonSide_eq picture pairing old
      (wallBlock_of_side_rel data star input.activeProfile.blockPattern pairing
        _ sourceBlock sheet hSheet old.1.2 hRelOld)
      hMem (hSide.trans (W4TargetPairings.FourStar.right_edge star pairing _).symm)
      hSurvives
    rw [hEq] at hRelOld
    rw [wholeResolution_side_rel, hRepr, hSidePart] at hRelOld
    exact hRelOld.trans
      (((data.edgePartition
        (star.edge (block.singletonLabel pairing))).rel_repr_right _).symm)

/-- The complete nd3 new-occurrence census: exactly the regrown occurrences
above the isolated branch's own old edge block survive, and there is only one
such quotient occurrence. -/
theorem nd3_new_survives_iff
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet) :
    (¬ IsDangling ((input.presentedFamily data star).candidate pairing).datum
      (((input.presentedFamily data star).candidate pairing).newSourceEdge
        sheet)) ↔
      (data.edgePartition
        (star.edge (block.singletonLabel pairing))).Rel sheet
        (picture.activeSheet (block.singletonLabel pairing)) := by
  constructor
  · intro hSurvives
    by_contra hNotRel
    exact hSurvives (nd3_new_dangles_of_not_rel input pairing sourceBlock block
      picture hPicture sheet hSheet hNotRel)
  · exact nd3_new_survives_of_rel input pairing sourceBlock block picture
      hPicture sheet

/-- The canonical nd3 regrown sheet — the one chosen by `AuxR0Family.regrown` —
survives. -/
theorem nd3_new_survives_activeSheet
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture) :
    ¬ IsDangling ((input.presentedFamily data star).candidate pairing).datum
      (((input.presentedFamily data star).candidate pairing).newSourceEdge
        (picture.activeSheet (block.singletonLabel pairing))) :=
  nd3_new_survives_of_rel input pairing sourceBlock block picture hPicture _ rfl

/-! ### Dangling-block new pruning -/

/-- **Dangling-block new pruning.**  Above an entirely dangling wall block no
regrown occurrence survives, on either side of the target pairing.  The two
expanded endpoints above such a block therefore have surviving valency
zero. -/
theorem dangling_new_dangles
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall)
    (old_dangling : ∀ (edge : data.SourceEdge) (label : Fin 4),
      WallBlock.ofSheet data wall edge.1.2 = sourceBlock →
      star.edge label = edge.1.1 → IsDangling data edge)
    (hPicture : input.blockPicture sourceBlock = .dangling old_dangling)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet) :
    IsDangling ((input.presentedFamily data star).candidate pairing).datum
      (((input.presentedFamily data star).candidate pairing).newSourceEdge
        sheet) := by
  classical
  show IsDangling (inputReceipts input pairing).candidate.datum
    ((inputReceipts input pairing).candidate.newSourceEdge sheet)
  have hPattern : input.activeProfile.blockPattern sourceBlock.1 =
      .nd2 ActiveBlockClassification.danglingBlock :=
    blockPattern_eq_dangling_of_picture input sourceBlock old_dangling hPicture
  have hRepr : (data.vertexPartition wall).repr sheet = sourceBlock.1 :=
    hSheet.symm.trans sourceBlock.2
  have hOld : ∀ (side : Bool) (old : data.SourceEdge),
      old.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing old.1.1 = side →
      (sidePartition (wholeResolution data star
        input.activeProfile.blockPattern pairing) side).Rel sheet old.1.2 →
      IsDangling data old := by
    intro side old hMem _ hRelOld
    obtain ⟨label, hLabel⟩ := star.exists_edge_eq old.1.1 hMem
    exact old_dangling old label
      (wallBlock_of_side_rel data star input.activeProfile.blockPattern pairing
        side sourceBlock sheet hSheet old.1.2 hRelOld) hLabel
  by_cases hSame : W4TargetPairings.Pairing.labelRight pairing
      ActiveBlockClassification.danglingBlock.first =
    W4TargetPairings.Pairing.labelRight pairing
      ActiveBlockClassification.danglingBlock.second
  · refine new_dangles_of_side (inputReceipts input pairing) input.valid
      (! W4TargetPairings.Pairing.labelRight pairing
        ActiveBlockClassification.danglingBlock.first) sheet ?_ (hOld _)
    rw [wholeResolution_side_block, wholeResolution_newEdge_block, hRepr,
      nd2_same_otherSide_partition data star input.activeProfile.blockPattern
        pairing sourceBlock.1 _ hPattern hSame,
      nd2_same_newEdge data star input.activeProfile.blockPattern pairing
        sourceBlock.1 _ hPattern hSame]
  · refine new_dangles_of_side (inputReceipts input pairing) input.valid true
      sheet ?_ (hOld _)
    rw [wholeResolution_side_block, wholeResolution_newEdge_block, hRepr,
      nd2_ne_side_partition data star input.activeProfile.blockPattern pairing
        sourceBlock.1 _ true hPattern hSame,
      nd2_ne_newEdge data star input.activeProfile.blockPattern pairing
        sourceBlock.1 _ hPattern hSame]

/-! ## The complete surviving endpoint census

For each of the three source pictures and each of the two expanded endpoints
above the wall block, the theorems below list exactly the occurrences of the
actual candidate that survive there.  Multiplicity is occurrence multiplicity;
no statement is made about stable rows.
-/

/-- **Dangling block.**  Above an entirely dangling wall block both expanded
endpoints are isolated in the pruned outgoing source. -/
theorem dangling_nonDanglingIncident_eq_empty
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall)
    (old_dangling : ∀ (edge : data.SourceEdge) (label : Fin 4),
      WallBlock.ofSheet data wall edge.1.2 = sourceBlock →
      star.edge label = edge.1.1 → IsDangling data edge)
    (hPicture : input.blockPicture sourceBlock = .dangling old_dangling)
    (side : Bool) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet) :
    nonDanglingIncident
        ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate
          pairing).datum.sourceEndpoint (sideVertex target wall side) sheet) =
      ∅ := by
  classical
  show nonDanglingIncident (inputReceipts input pairing).candidate.datum
    ((inputReceipts input pairing).candidate.datum.sourceEndpoint
      (sideVertex target wall side) sheet) = ∅
  rw [Finset.eq_empty_iff_forall_notMem]
  intro edge hEdge
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hEdge
  rcases ResolutionPruning.sourceEdge_cases
    (inputReceipts input pairing).candidate edge with ⟨old, rfl⟩ | ⟨other, rfl⟩
  · obtain ⟨⟨hMem, _⟩, hRel⟩ :=
      (old_incident_side_iff _ side sheet old).mp hIncident
    obtain ⟨label, hLabel⟩ := star.exists_edge_eq old.1.1 hMem
    exact hSurvives ((old_isDangling_receipts_iff _ input.valid old).mpr
      (old_dangling old label
        (wallBlock_of_side_rel data star input.activeProfile.blockPattern
          pairing side sourceBlock sheet hSheet old.1.2 hRel) hLabel))
  · exact hSurvives (dangling_new_dangles input pairing sourceBlock old_dangling
      hPicture other (wall_rel_of_side_rel_newEdge_repr data star
        input.activeProfile.blockPattern pairing side sourceBlock sheet hSheet
        other ((new_incident_side_iff _ side sheet other).mp hIncident)))

/-- **Same-side nd2 block, joined endpoint.**  The endpoint carrying the two
active branches sees exactly their two canonical retained survivors; the
regrown occurrence is already pruned there. -/
theorem nd2_same_activeSide_census
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
      W4TargetPairings.Pairing.labelRight pairing block.second)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet)
    (edge :
      ((input.presentedFamily data star).candidate pairing).datum.SourceEdge) :
    edge ∈ nonDanglingIncident
        ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate
          pairing).datum.sourceEndpoint (sideVertex target wall
            (W4TargetPairings.Pairing.labelRight pairing block.first))
          sheet) ↔
      edge = ((input.presentedFamily data star).candidate
            pairing).oldSourceEdge
          (data.sourceEdge (star.edge block.first) sourceBlock.1) ∨
        edge = ((input.presentedFamily data star).candidate
            pairing).oldSourceEdge
          (data.sourceEdge (star.edge block.second) sourceBlock.1) := by
  classical
  have hPattern : input.activeProfile.blockPattern sourceBlock.1 = .nd2 block :=
    blockPattern_eq_nd2_of_picture input sourceBlock block picture hPicture
  have hSide := nd2_same_activeSide_partition data star
    input.activeProfile.blockPattern pairing sourceBlock.1 block hPattern hSame
  rw [mem_nonDanglingIncident]
  constructor
  · rintro ⟨hSurvives, hIncident⟩
    rcases ResolutionPruning.sourceEdge_cases
      (inputReceipts input pairing).candidate edge with ⟨old, rfl⟩ | ⟨other, rfl⟩
    · obtain ⟨⟨hMem, _⟩, hRel⟩ :=
        (old_incident_side_iff (inputReceipts input pairing)
          (W4TargetPairings.Pairing.labelRight pairing block.first) sheet
          old).mp hIncident
      obtain ⟨label, hLabel⟩ := star.exists_edge_eq old.1.1 hMem
      have hOldSurvives : ¬ IsDangling data old := fun hDangling ↦
        hSurvives ((old_isDangling_receipts_iff _ input.valid old).mpr hDangling)
      rcases picture.only_surviving old
          (wallBlock_of_side_rel data star input.activeProfile.blockPattern
            pairing _ sourceBlock sheet hSheet old.1.2 hRel)
          ⟨label, hLabel⟩ hOldSurvives with hOld | hOld
      · exact Or.inl (congrArg _ hOld)
      · exact Or.inr (congrArg _ hOld)
    · exact absurd (nd2_new_dangles_of_same input pairing sourceBlock block
        picture hPicture hSame other
        (wall_rel_of_side_rel_newEdge_repr data star
          input.activeProfile.blockPattern pairing _ sourceBlock sheet hSheet
          other ((new_incident_side_iff (inputReceipts input pairing)
            (W4TargetPairings.Pairing.labelRight pairing block.first) sheet
            other).mp hIncident))) hSurvives
  · rintro (rfl | rfl)
    · refine ⟨fun hDangling ↦ picture.first_survives
        ((old_isDangling_receipts_iff (inputReceipts input pairing) input.valid
          _).mp hDangling), ?_⟩
      exact (old_incident_side_iff (inputReceipts input pairing) _ sheet _).mpr
        ⟨⟨star.edge_mem_incidentEdges _,
          W4TargetPairings.FourStar.right_edge star pairing block.first⟩,
          side_rel_sourceEdge_repr_of_wall data star
            input.activeProfile.blockPattern pairing _ sourceBlock sheet hSheet
            hSide block.first sourceBlock.1 rfl⟩
    · refine ⟨fun hDangling ↦ picture.second_survives
        ((old_isDangling_receipts_iff (inputReceipts input pairing) input.valid
          _).mp hDangling), ?_⟩
      exact (old_incident_side_iff (inputReceipts input pairing) _ sheet _).mpr
        ⟨⟨star.edge_mem_incidentEdges _,
          (W4TargetPairings.FourStar.right_edge star pairing
            block.second).trans hSame.symm⟩,
          side_rel_sourceEdge_repr_of_wall data star
            input.activeProfile.blockPattern pairing _ sourceBlock sheet hSheet
            hSide block.second sourceBlock.1 rfl⟩

/-- **Same-side nd2 block, split endpoint.**  Every sheet of the split
endpoint is isolated in the pruned outgoing source. -/
theorem nd2_same_otherSide_census
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
      W4TargetPairings.Pairing.labelRight pairing block.second)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet) :
    nonDanglingIncident
        ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate
          pairing).datum.sourceEndpoint (sideVertex target wall
            (! W4TargetPairings.Pairing.labelRight pairing block.first))
          sheet) = ∅ := by
  classical
  show nonDanglingIncident (inputReceipts input pairing).candidate.datum
    ((inputReceipts input pairing).candidate.datum.sourceEndpoint
      (sideVertex target wall
        (! W4TargetPairings.Pairing.labelRight pairing block.first)) sheet) = ∅
  rw [Finset.eq_empty_iff_forall_notMem]
  intro edge hEdge
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hEdge
  rcases ResolutionPruning.sourceEdge_cases
    (inputReceipts input pairing).candidate edge with ⟨old, rfl⟩ | ⟨other, rfl⟩
  · obtain ⟨⟨hMem, hOldSide⟩, hRel⟩ :=
      (old_incident_side_iff (inputReceipts input pairing) _ sheet old).mp
        hIncident
    obtain ⟨label, hLabel⟩ := star.exists_edge_eq old.1.1 hMem
    have hOldSurvives : ¬ IsDangling data old := fun hDangling ↦
      hSurvives ((old_isDangling_receipts_iff _ input.valid old).mpr hDangling)
    rcases picture.only_surviving old
        (wallBlock_of_side_rel data star input.activeProfile.blockPattern
          pairing _ sourceBlock sheet hSheet old.1.2 hRel)
        ⟨label, hLabel⟩ hOldSurvives with hOld | hOld <;> rw [hOld] at hOldSide <;>
      simp only [GluingDatum.sourceEdge_target,
        W4TargetPairings.FourStar.right_edge] at hOldSide
    · exact absurd hOldSide (by simp)
    · rw [← hSame] at hOldSide
      exact absurd hOldSide (by simp)
  · exact hSurvives (nd2_new_dangles_of_same input pairing sourceBlock block
      picture hPicture hSame other
      (wall_rel_of_side_rel_newEdge_repr data star
        input.activeProfile.blockPattern pairing _ sourceBlock sheet hSheet
        other ((new_incident_side_iff (inputReceipts input pairing) _ sheet
          other).mp hIncident)))

/-- **Opposite-side nd2 block.**  Each expanded endpoint sees exactly the
canonical survivor of its own active branch together with the single surviving
regrown occurrence. -/
theorem nd2_ne_census
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (hNe : W4TargetPairings.Pairing.labelRight pairing block.first ≠
      W4TargetPairings.Pairing.labelRight pairing block.second)
    (label : Fin 4) (hLabel : label = block.first ∨ label = block.second)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet)
    (edge :
      ((input.presentedFamily data star).candidate pairing).datum.SourceEdge) :
    edge ∈ nonDanglingIncident
        ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate
          pairing).datum.sourceEndpoint (sideVertex target wall
            (W4TargetPairings.Pairing.labelRight pairing label)) sheet) ↔
      edge = ((input.presentedFamily data star).candidate
            pairing).oldSourceEdge
          (data.sourceEdge (star.edge label) sourceBlock.1) ∨
        edge = ((input.presentedFamily data star).candidate
          pairing).newSourceEdge sourceBlock.1 := by
  classical
  have hPattern : input.activeProfile.blockPattern sourceBlock.1 = .nd2 block :=
    blockPattern_eq_nd2_of_picture input sourceBlock block picture hPicture
  have hRepr : (data.vertexPartition wall).repr sheet = sourceBlock.1 :=
    hSheet.symm.trans sourceBlock.2
  have hSideWall := nd2_ne_side_partition data star
    input.activeProfile.blockPattern pairing sourceBlock.1 block
    (W4TargetPairings.Pairing.labelRight pairing label) hPattern hNe
  have hNewWall := nd2_ne_newEdge data star input.activeProfile.blockPattern
    pairing sourceBlock.1 block hPattern hNe
  have hSurvivesLabel : ¬ IsDangling data
      (data.sourceEdge (star.edge label) sourceBlock.1) := by
    rcases hLabel with rfl | rfl
    · exact picture.first_survives
    · exact picture.second_survives
  have hOnly : ∀ old : data.SourceEdge,
      WallBlock.ofSheet data wall old.1.2 = sourceBlock →
      (∃ other : Fin 4, star.edge other = old.1.1) →
      ¬ IsDangling data old →
      star.right pairing old.1.1 =
        W4TargetPairings.Pairing.labelRight pairing label →
      old = data.sourceEdge (star.edge label) sourceBlock.1 := by
    intro old hBlock hStar hSurv hSide
    rcases picture.only_surviving old hBlock hStar hSurv with hOld | hOld <;>
      rw [hOld] at hSide ⊢ <;>
      simp only [GluingDatum.sourceEdge_target,
        W4TargetPairings.FourStar.right_edge] at hSide
    · rcases hLabel with rfl | rfl
      · rfl
      · exact absurd hSide hNe
    · rcases hLabel with rfl | rfl
      · exact absurd hSide.symm hNe
      · rfl
  rw [mem_nonDanglingIncident]
  constructor
  · rintro ⟨hSurvives, hIncident⟩
    rcases ResolutionPruning.sourceEdge_cases
      (inputReceipts input pairing).candidate edge with ⟨old, rfl⟩ | ⟨other, rfl⟩
    · obtain ⟨⟨hMem, hOldSide⟩, hRel⟩ :=
        (old_incident_side_iff (inputReceipts input pairing)
          (W4TargetPairings.Pairing.labelRight pairing label) sheet old).mp
          hIncident
      exact Or.inl (congrArg _ (hOnly old
        (wallBlock_of_side_rel data star input.activeProfile.blockPattern
          pairing _ sourceBlock sheet hSheet old.1.2 hRel)
        (star.exists_edge_eq old.1.1 hMem)
        (fun hDangling ↦ hSurvives
          ((old_isDangling_receipts_iff (inputReceipts input pairing)
            input.valid old).mpr hDangling)) hOldSide))
    · refine Or.inr ((newSourceEdge_eq_iff (inputReceipts input pairing) other
        sourceBlock.1).mpr ?_)
      have hWall := wall_rel_of_side_rel_newEdge_repr data star
        input.activeProfile.blockPattern pairing _ sourceBlock sheet hSheet
        other ((new_incident_side_iff (inputReceipts input pairing)
          (W4TargetPairings.Pairing.labelRight pairing label) sheet other).mp
          hIncident)
      rw [wholeResolution_newEdge_rel, hWall.symm.trans sourceBlock.2, hNewWall]
      exact hWall.symm
  · rintro (rfl | rfl)
    · refine ⟨fun hDangling ↦ hSurvivesLabel
        ((old_isDangling_receipts_iff (inputReceipts input pairing) input.valid
          _).mp hDangling), ?_⟩
      exact (old_incident_side_iff (inputReceipts input pairing) _ sheet _).mpr
        ⟨⟨star.edge_mem_incidentEdges _,
          W4TargetPairings.FourStar.right_edge star pairing label⟩,
          side_rel_sourceEdge_repr_of_wall data star
            input.activeProfile.blockPattern pairing _ sourceBlock sheet hSheet
            hSideWall label sourceBlock.1 rfl⟩
    · refine ⟨nd2_new_survives_of_ne input pairing sourceBlock block picture
        hPicture hNe, ?_⟩
      refine (new_incident_side_iff (inputReceipts input pairing)
        (W4TargetPairings.Pairing.labelRight pairing label) sheet
        sourceBlock.1).mpr ?_
      rw [wholeResolution_side_rel, hRepr, hSideWall]
      exact hSheet.symm.trans ((newEdge_refines_wall data star
        input.activeProfile.blockPattern pairing).rel
          ((wholeResolution data star input.activeProfile.blockPattern
            pairing).newEdge.rel_repr_right sourceBlock.1))

/-- **nd3 block, isolated endpoint, surviving sheets.**  Above a sheet of the
isolated branch's own old edge block, the isolated endpoint sees exactly that
branch's canonical retained survivor and the surviving regrown occurrence. -/
theorem nd3_singletonSide_census
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture)
    (sheet : Fin degree)
    (hRel : (data.edgePartition
        (star.edge (block.singletonLabel pairing))).Rel sheet
      (picture.activeSheet (block.singletonLabel pairing)))
    (edge :
      ((input.presentedFamily data star).candidate pairing).datum.SourceEdge) :
    edge ∈ nonDanglingIncident
        ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate
          pairing).datum.sourceEndpoint (sideVertex target wall
            (W4TargetPairings.Pairing.labelRight pairing
              (block.singletonLabel pairing))) sheet) ↔
      edge = ((input.presentedFamily data star).candidate
            pairing).oldSourceEdge
          (data.sourceEdge (star.edge (block.singletonLabel pairing))
            (picture.activeSheet (block.singletonLabel pairing))) ∨
        edge = ((input.presentedFamily data star).candidate
          pairing).newSourceEdge sheet := by
  classical
  have hActive : block.singletonLabel pairing ∈ block.activeLabels :=
    block.singletonLabel_mem_activeLabels pairing
  have hPattern : input.activeProfile.blockPattern sourceBlock.1 = .nd3 block :=
    blockPattern_eq_nd3_of_picture input sourceBlock block picture hPicture
  have hWallSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet :=
    (picture.active_sheet _ hActive).trans
      ((star.edgePartition_refines_wall data
        (block.singletonLabel pairing)).rel hRel).symm
  have hRepr : (data.vertexPartition wall).repr sheet = sourceBlock.1 :=
    hWallSheet.symm.trans sourceBlock.2
  have hSidePart := nd3_singletonSide_partition data star
    input.activeProfile.blockPattern pairing sourceBlock.1 block hPattern
  have hBlocks :
      (sidePartition (wholeResolution data star
          input.activeProfile.blockPattern pairing)
        (W4TargetPairings.Pairing.labelRight pairing
          (block.singletonLabel pairing))).block sheet =
        (wholeResolution data star input.activeProfile.blockPattern
          pairing).newEdge.block sheet := by
    rw [wholeResolution_side_block, wholeResolution_newEdge_block, hRepr,
      hSidePart, nd3_newEdge data star input.activeProfile.blockPattern pairing
        sourceBlock.1 block hPattern]
  rw [mem_nonDanglingIncident]
  constructor
  · rintro ⟨hSurvives, hIncident⟩
    rcases ResolutionPruning.sourceEdge_cases
      (inputReceipts input pairing).candidate edge with ⟨old, rfl⟩ | ⟨other, rfl⟩
    · obtain ⟨⟨hMem, hOldSide⟩, hRelOld⟩ :=
        (old_incident_side_iff (inputReceipts input pairing) _ sheet old).mp
          hIncident
      exact Or.inl (congrArg _ (nd3_old_survivor_on_singletonSide_eq picture
        pairing old
        (wallBlock_of_side_rel data star input.activeProfile.blockPattern
          pairing _ sourceBlock sheet hWallSheet old.1.2 hRelOld) hMem
        (hOldSide.trans
          (W4TargetPairings.FourStar.right_edge star pairing _).symm)
        (fun hDangling ↦ hSurvives
          ((old_isDangling_receipts_iff (inputReceipts input pairing)
            input.valid old).mpr hDangling))))
    · exact Or.inr (new_eq_of_incident_side (inputReceipts input pairing) _
        sheet other hBlocks hIncident)
  · rintro (rfl | rfl)
    · refine ⟨fun hDangling ↦ (picture.active_survives _ hActive)
        ((old_isDangling_receipts_iff (inputReceipts input pairing) input.valid
          _).mp hDangling), ?_⟩
      refine (old_incident_side_iff (inputReceipts input pairing) _ sheet _).mpr
        ⟨⟨star.edge_mem_incidentEdges _,
          W4TargetPairings.FourStar.right_edge star pairing _⟩, ?_⟩
      rw [wholeResolution_side_rel, hRepr, hSidePart]
      exact hRel.trans ((data.edgePartition
        (star.edge (block.singletonLabel pairing))).rel_repr_right _)
    · exact ⟨nd3_new_survives_of_rel input pairing sourceBlock block picture
        hPicture sheet hRel,
        new_incident_side (inputReceipts input pairing) _ sheet⟩

/-- **nd3 block, isolated endpoint, pruned sheets.**  Every other sheet of the
isolated endpoint is isolated in the pruned outgoing source. -/
theorem nd3_singletonSide_residual_census
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet)
    (hNotRel : ¬ (data.edgePartition
        (star.edge (block.singletonLabel pairing))).Rel sheet
      (picture.activeSheet (block.singletonLabel pairing))) :
    nonDanglingIncident
        ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate
          pairing).datum.sourceEndpoint (sideVertex target wall
            (W4TargetPairings.Pairing.labelRight pairing
              (block.singletonLabel pairing))) sheet) = ∅ := by
  classical
  show nonDanglingIncident (inputReceipts input pairing).candidate.datum
    ((inputReceipts input pairing).candidate.datum.sourceEndpoint
      (sideVertex target wall (W4TargetPairings.Pairing.labelRight pairing
        (block.singletonLabel pairing))) sheet) = ∅
  have hPattern : input.activeProfile.blockPattern sourceBlock.1 = .nd3 block :=
    blockPattern_eq_nd3_of_picture input sourceBlock block picture hPicture
  have hRepr : (data.vertexPartition wall).repr sheet = sourceBlock.1 :=
    hSheet.symm.trans sourceBlock.2
  have hSidePart := nd3_singletonSide_partition data star
    input.activeProfile.blockPattern pairing sourceBlock.1 block hPattern
  have hBlocks :
      (sidePartition (wholeResolution data star
          input.activeProfile.blockPattern pairing)
        (W4TargetPairings.Pairing.labelRight pairing
          (block.singletonLabel pairing))).block sheet =
        (wholeResolution data star input.activeProfile.blockPattern
          pairing).newEdge.block sheet := by
    rw [wholeResolution_side_block, wholeResolution_newEdge_block, hRepr,
      hSidePart, nd3_newEdge data star input.activeProfile.blockPattern pairing
        sourceBlock.1 block hPattern]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro edge hEdge
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hEdge
  rcases ResolutionPruning.sourceEdge_cases
    (inputReceipts input pairing).candidate edge with ⟨old, rfl⟩ | ⟨other, rfl⟩
  · obtain ⟨⟨hMem, hOldSide⟩, hRelOld⟩ :=
      (old_incident_side_iff (inputReceipts input pairing) _ sheet old).mp
        hIncident
    have hEq := nd3_old_survivor_on_singletonSide_eq picture pairing old
      (wallBlock_of_side_rel data star input.activeProfile.blockPattern pairing
        _ sourceBlock sheet hSheet old.1.2 hRelOld) hMem
      (hOldSide.trans (W4TargetPairings.FourStar.right_edge star pairing _).symm)
      (fun hDangling ↦ hSurvives
        ((old_isDangling_receipts_iff (inputReceipts input pairing) input.valid
          old).mpr hDangling))
    rw [hEq] at hRelOld
    rw [wholeResolution_side_rel, hRepr, hSidePart] at hRelOld
    exact hNotRel (hRelOld.trans (((data.edgePartition
      (star.edge (block.singletonLabel pairing))).rel_repr_right _).symm))
  · rw [new_eq_of_incident_side (inputReceipts input pairing) _ sheet other
      hBlocks hIncident] at hSurvives
    exact hSurvives (nd3_new_dangles_of_not_rel input pairing sourceBlock block
      picture hPicture sheet hSheet hNotRel)

/-- **nd3 block, joined endpoint.**  The endpoint carrying the two remaining
active branches sees exactly their two canonical retained survivors together
with the single surviving regrown occurrence: a trivalent surviving star. -/
theorem nd3_otherSide_census
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet)
    (edge :
      ((input.presentedFamily data star).candidate pairing).datum.SourceEdge) :
    edge ∈ nonDanglingIncident
        ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate
          pairing).datum.sourceEndpoint (sideVertex target wall
            (! W4TargetPairings.Pairing.labelRight pairing
              (block.singletonLabel pairing))) sheet) ↔
      (∃ label : Fin 4, label ∈ block.activeLabels ∧
          W4TargetPairings.Pairing.labelRight pairing label ≠
            W4TargetPairings.Pairing.labelRight pairing
              (block.singletonLabel pairing) ∧
          edge = ((input.presentedFamily data star).candidate
              pairing).oldSourceEdge
            (data.sourceEdge (star.edge label)
              (picture.activeSheet label))) ∨
        edge = ((input.presentedFamily data star).candidate
            pairing).newSourceEdge
          (picture.activeSheet (block.singletonLabel pairing)) := by
  classical
  have hActive : block.singletonLabel pairing ∈ block.activeLabels :=
    block.singletonLabel_mem_activeLabels pairing
  have hPattern : input.activeProfile.blockPattern sourceBlock.1 = .nd3 block :=
    blockPattern_eq_nd3_of_picture input sourceBlock block picture hPicture
  have hRepr : (data.vertexPartition wall).repr sheet = sourceBlock.1 :=
    hSheet.symm.trans sourceBlock.2
  have hSideWall := nd3_otherSide_partition data star
    input.activeProfile.blockPattern pairing sourceBlock.1 block hPattern
  rw [mem_nonDanglingIncident]
  constructor
  · rintro ⟨hSurvives, hIncident⟩
    rcases ResolutionPruning.sourceEdge_cases
      (inputReceipts input pairing).candidate edge with ⟨old, rfl⟩ | ⟨other, rfl⟩
    · obtain ⟨⟨hMem, hOldSide⟩, hRelOld⟩ :=
        (old_incident_side_iff (inputReceipts input pairing) _ sheet old).mp
          hIncident
      obtain ⟨label, hLabel⟩ := star.exists_edge_eq old.1.1 hMem
      obtain ⟨other, hOtherActive, hOld⟩ := picture.only_surviving old
        (wallBlock_of_side_rel data star input.activeProfile.blockPattern
          pairing _ sourceBlock sheet hSheet old.1.2 hRelOld) ⟨label, hLabel⟩
        (fun hDangling ↦ hSurvives
          ((old_isDangling_receipts_iff (inputReceipts input pairing)
            input.valid old).mpr hDangling))
      rw [hOld] at hOldSide
      simp only [GluingDatum.sourceEdge_target,
        W4TargetPairings.FourStar.right_edge] at hOldSide
      exact Or.inl ⟨other, hOtherActive, by simp [hOldSide], congrArg _ hOld⟩
    · have hWall := wall_rel_of_side_rel_newEdge_repr data star
        input.activeProfile.blockPattern pairing _ sourceBlock sheet hSheet
        other ((new_incident_side_iff (inputReceipts input pairing) _ sheet
          other).mp hIncident)
      refine Or.inr ((newSourceEdge_eq_iff (inputReceipts input pairing) other
        (picture.activeSheet (block.singletonLabel pairing))).mpr ?_)
      rw [wholeResolution_newEdge_rel, hWall.symm.trans sourceBlock.2,
        nd3_newEdge data star input.activeProfile.blockPattern pairing
          sourceBlock.1 block hPattern]
      exact (nd3_new_survives_iff input pairing sourceBlock block picture
        hPicture other hWall).mp hSurvives
  · rintro (⟨label, hLabelActive, hLabelSide, rfl⟩ | rfl)
    · refine ⟨fun hDangling ↦ (picture.active_survives label hLabelActive)
        ((old_isDangling_receipts_iff (inputReceipts input pairing) input.valid
          _).mp hDangling), ?_⟩
      exact (old_incident_side_iff (inputReceipts input pairing) _ sheet _).mpr
        ⟨⟨star.edge_mem_incidentEdges _,
          (W4TargetPairings.FourStar.right_edge star pairing label).trans
            (bool_eq_not_of_ne hLabelSide)⟩,
          side_rel_sourceEdge_repr_of_wall data star
            input.activeProfile.blockPattern pairing _ sourceBlock sheet hSheet
            hSideWall label (picture.activeSheet label)
            (picture.active_sheet label hLabelActive)⟩
    · refine ⟨nd3_new_survives_activeSheet input pairing sourceBlock block
        picture hPicture, ?_⟩
      refine (new_incident_side_iff (inputReceipts input pairing) _ sheet
        (picture.activeSheet (block.singletonLabel pairing))).mpr ?_
      rw [wholeResolution_side_rel, hRepr, hSideWall]
      exact (hSheet.symm.trans (picture.active_sheet _ hActive)).trans
        ((newEdge_refines_wall data star input.activeProfile.blockPattern
          pairing).rel ((wholeResolution data star
            input.activeProfile.blockPattern pairing).newEdge.rel_repr_right _))

/-! ### Surviving valencies at the two expanded endpoints

The census above is turned into literal incidence counts here.  Reading the
four cases together: a dangling block contributes two isolated endpoints; a
same-side nd2 block one divalent and one isolated endpoint; an opposite-side
nd2 block two divalent endpoints; and an nd3 block one trivalent endpoint,
one divalent endpoint, and isolated residual sheets.
-/

theorem dangling_nonDanglingValency_eq_zero
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall)
    (old_dangling : ∀ (edge : data.SourceEdge) (label : Fin 4),
      WallBlock.ofSheet data wall edge.1.2 = sourceBlock →
      star.edge label = edge.1.1 → IsDangling data edge)
    (hPicture : input.blockPicture sourceBlock = .dangling old_dangling)
    (side : Bool) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet) :
    nonDanglingValency
        ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate
          pairing).datum.sourceEndpoint (sideVertex target wall side) sheet) =
      0 := by
  rw [← card_nonDanglingIncident, dangling_nonDanglingIncident_eq_empty input
    pairing sourceBlock old_dangling hPicture side sheet hSheet]
  simp

theorem nd2_same_otherSide_nonDanglingValency_eq_zero
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
      W4TargetPairings.Pairing.labelRight pairing block.second)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet) :
    nonDanglingValency
        ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate
          pairing).datum.sourceEndpoint (sideVertex target wall
            (! W4TargetPairings.Pairing.labelRight pairing block.first))
          sheet) = 0 := by
  rw [← card_nonDanglingIncident, nd2_same_otherSide_census input pairing
    sourceBlock block picture hPicture hSame sheet hSheet]
  simp

theorem nd3_singletonSide_residual_nonDanglingValency_eq_zero
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet)
    (hNotRel : ¬ (data.edgePartition
        (star.edge (block.singletonLabel pairing))).Rel sheet
      (picture.activeSheet (block.singletonLabel pairing))) :
    nonDanglingValency
        ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate
          pairing).datum.sourceEndpoint (sideVertex target wall
            (W4TargetPairings.Pairing.labelRight pairing
              (block.singletonLabel pairing))) sheet) = 0 := by
  rw [← card_nonDanglingIncident, nd3_singletonSide_residual_census input
    pairing sourceBlock block picture hPicture sheet hSheet hNotRel]
  simp

theorem nd2_same_activeSide_nonDanglingValency
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
      W4TargetPairings.Pairing.labelRight pairing block.second)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet) :
    nonDanglingValency
        ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate
          pairing).datum.sourceEndpoint (sideVertex target wall
            (W4TargetPairings.Pairing.labelRight pairing block.first))
          sheet) = 2 := by
  classical
  rw [← card_nonDanglingIncident]
  have hSet :
      nonDanglingIncident
          ((input.presentedFamily data star).candidate pairing).datum
          (((input.presentedFamily data star).candidate
            pairing).datum.sourceEndpoint (sideVertex target wall
              (W4TargetPairings.Pairing.labelRight pairing block.first))
            sheet) =
        {((input.presentedFamily data star).candidate pairing).oldSourceEdge
            (data.sourceEdge (star.edge block.first) sourceBlock.1),
          ((input.presentedFamily data star).candidate pairing).oldSourceEdge
            (data.sourceEdge (star.edge block.second) sourceBlock.1)} := by
    ext edge
    rw [nd2_same_activeSide_census input pairing sourceBlock block picture
      hPicture hSame sheet hSheet edge]
    simp
  rw [hSet]
  refine Finset.card_pair (fun hEq ↦ block.distinct (star.edge_injective ?_))
  simpa only [GluingDatum.sourceEdge_target] using
    congrArg (fun e : data.SourceEdge ↦ e.1.1) (oldSourceEdge_injective _ hEq)

theorem nd2_ne_nonDanglingValency
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (hNe : W4TargetPairings.Pairing.labelRight pairing block.first ≠
      W4TargetPairings.Pairing.labelRight pairing block.second)
    (label : Fin 4) (hLabel : label = block.first ∨ label = block.second)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet) :
    nonDanglingValency
        ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate
          pairing).datum.sourceEndpoint (sideVertex target wall
            (W4TargetPairings.Pairing.labelRight pairing label)) sheet) = 2 := by
  classical
  rw [← card_nonDanglingIncident]
  have hSet :
      nonDanglingIncident
          ((input.presentedFamily data star).candidate pairing).datum
          (((input.presentedFamily data star).candidate
            pairing).datum.sourceEndpoint (sideVertex target wall
              (W4TargetPairings.Pairing.labelRight pairing label)) sheet) =
        {((input.presentedFamily data star).candidate pairing).oldSourceEdge
            (data.sourceEdge (star.edge label) sourceBlock.1),
          ((input.presentedFamily data star).candidate
            pairing).newSourceEdge sourceBlock.1} := by
    ext edge
    rw [nd2_ne_census input pairing sourceBlock block picture hPicture hNe label
      hLabel sheet hSheet edge]
    simp
  rw [hSet]
  exact Finset.card_pair (oldSourceEdge_ne_newSourceEdge _ _ _)

theorem nd3_singletonSide_nonDanglingValency
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture)
    (sheet : Fin degree)
    (hRel : (data.edgePartition
        (star.edge (block.singletonLabel pairing))).Rel sheet
      (picture.activeSheet (block.singletonLabel pairing))) :
    nonDanglingValency
        ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate
          pairing).datum.sourceEndpoint (sideVertex target wall
            (W4TargetPairings.Pairing.labelRight pairing
              (block.singletonLabel pairing))) sheet) = 2 := by
  classical
  rw [← card_nonDanglingIncident]
  have hSet :
      nonDanglingIncident
          ((input.presentedFamily data star).candidate pairing).datum
          (((input.presentedFamily data star).candidate
            pairing).datum.sourceEndpoint (sideVertex target wall
              (W4TargetPairings.Pairing.labelRight pairing
                (block.singletonLabel pairing))) sheet) =
        {((input.presentedFamily data star).candidate pairing).oldSourceEdge
            (data.sourceEdge (star.edge (block.singletonLabel pairing))
              (picture.activeSheet (block.singletonLabel pairing))),
          ((input.presentedFamily data star).candidate pairing).newSourceEdge
            sheet} := by
    ext edge
    rw [nd3_singletonSide_census input pairing sourceBlock block picture
      hPicture sheet hRel edge]
    simp
  rw [hSet]
  exact Finset.card_pair (oldSourceEdge_ne_newSourceEdge _ _ _)

end Input

/-- Two of the three active nd3 branches are assigned to the endpoint opposite
the isolated one. -/
theorem nd3_card_activeLabels_off_singletonSide (block : Nd3Block)
    (pairing : Fin 3) :
    (block.activeLabels.filter fun label ↦
      W4TargetPairings.Pairing.labelRight pairing label ≠
        W4TargetPairings.Pairing.labelRight pairing
          (block.singletonLabel pairing)).card = 2 := by
  classical
  have hCard : block.activeLabels.card = 3 := by
    simp [Nd3Block.activeLabels, block.first_ne_second, block.first_ne_third,
      block.second_ne_third]
  have hSingleton :
      (block.activeLabels.filter fun label ↦
        W4TargetPairings.Pairing.labelRight pairing label =
          W4TargetPairings.Pairing.labelRight pairing
            (block.singletonLabel pairing)) =
        {block.singletonLabel pairing} := by
    ext label
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hActive, hSide⟩
      exact block.eq_singletonLabel_of_active_of_same_side pairing label
        ((block.mem_activeLabels label).mp hActive) hSide
    · rintro rfl
      exact ⟨block.singletonLabel_mem_activeLabels pairing, rfl⟩
  have hSplit := Finset.card_filter_add_card_filter_not
    (s := block.activeLabels)
    (fun label ↦ W4TargetPairings.Pairing.labelRight pairing label =
      W4TargetPairings.Pairing.labelRight pairing
        (block.singletonLabel pairing))
  rw [hSingleton, hCard, Finset.card_singleton] at hSplit
  simp only [ne_eq] at hSplit ⊢
  omega

section InputValency

variable {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall}
  [DecidableEq target.edges]

/-- **The trivalent nd3 endpoint.**  The endpoint carrying the two remaining
active branches has surviving valency three: two retained old survivors and
the single surviving regrown occurrence. -/
theorem nd3_otherSide_nonDanglingValency
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet) :
    nonDanglingValency
        ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate
          pairing).datum.sourceEndpoint (sideVertex target wall
            (! W4TargetPairings.Pairing.labelRight pairing
              (block.singletonLabel pairing))) sheet) = 3 := by
  classical
  rw [← card_nonDanglingIncident]
  have hSet :
      nonDanglingIncident
          ((input.presentedFamily data star).candidate pairing).datum
          (((input.presentedFamily data star).candidate
            pairing).datum.sourceEndpoint (sideVertex target wall
              (! W4TargetPairings.Pairing.labelRight pairing
                (block.singletonLabel pairing))) sheet) =
        insert (((input.presentedFamily data star).candidate
              pairing).newSourceEdge
            (picture.activeSheet (block.singletonLabel pairing)))
          ((block.activeLabels.filter fun label ↦
            W4TargetPairings.Pairing.labelRight pairing label ≠
              W4TargetPairings.Pairing.labelRight pairing
                (block.singletonLabel pairing)).image
            fun label ↦ ((input.presentedFamily data star).candidate
                pairing).oldSourceEdge
              (data.sourceEdge (star.edge label)
                (picture.activeSheet label))) := by
    ext edge
    rw [nd3_otherSide_census input pairing sourceBlock block picture hPicture
      sheet hSheet edge]
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro (⟨label, hActive, hNe, rfl⟩ | rfl)
      · exact Or.inr ⟨label, ⟨hActive, hNe⟩, rfl⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨label, ⟨hActive, hNe⟩, rfl⟩)
      · exact Or.inr rfl
      · exact Or.inl ⟨label, hActive, hNe, rfl⟩
  have hInj : Set.InjOn
      (fun label ↦ ((input.presentedFamily data star).candidate
          pairing).oldSourceEdge
        (data.sourceEdge (star.edge label) (picture.activeSheet label)))
      ↑(block.activeLabels.filter fun label ↦
        W4TargetPairings.Pairing.labelRight pairing label ≠
          W4TargetPairings.Pairing.labelRight pairing
            (block.singletonLabel pairing)) := by
    intro first _ second _ hEq
    apply star.edge_injective
    simpa only [GluingDatum.sourceEdge_target] using
      congrArg (fun e : data.SourceEdge ↦ e.1.1)
        (oldSourceEdge_injective _ hEq)
  have hNotMem : ((input.presentedFamily data star).candidate
        pairing).newSourceEdge
      (picture.activeSheet (block.singletonLabel pairing)) ∉
      (block.activeLabels.filter fun label ↦
        W4TargetPairings.Pairing.labelRight pairing label ≠
          W4TargetPairings.Pairing.labelRight pairing
            (block.singletonLabel pairing)).image
        fun label ↦ ((input.presentedFamily data star).candidate
            pairing).oldSourceEdge
          (data.sourceEdge (star.edge label) (picture.activeSheet label)) := by
    intro hMem
    obtain ⟨label, _, hEq⟩ := Finset.mem_image.mp hMem
    exact oldSourceEdge_ne_newSourceEdge _ _ _ hEq
  rw [hSet, Finset.card_insert_of_notMem hNotMem,
    Finset.card_image_of_injOn hInj,
    nd3_card_activeLabels_off_singletonSide block pairing]

end InputValency

end DraismaVargas.LocalCases.W4OutgoingSurvival
