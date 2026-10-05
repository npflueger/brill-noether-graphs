module

public import DraismaVargas.LocalCases.LimitChainCore

@[expose] public section

/-!
# The limit-matrix chain at a **finite set** of distinguished blocks

`LimitChainCore` states the five stages of an outgoing-member chain for a
member with **one** distinguished wall block: `BackgroundShape.selected :
Fin degree` names it, the three block clauses describe the member away from
it, and `LiftData`/`SelectedData`/`GraphData` describe the member above it.

`W2R1StableGraph` shows that the `{w2-r1}` case cannot use that: its two
members each have **two** branch vertices, above two ramification-one blocks
`A₀` and `B₀` and on opposite sides of the new edge, and
`W2R1StableGraph.not_backgroundClauses_both` shows no
`LimitChainCore.BackgroundShape` over such a member has both blocks outside
its distinguished one (`backgroundClauses_not_uniform`: nor is there a
family-wide choice).  This module is the variant that case needs: the same
five stages over a **`Finset` of anchors**.

## The four generalisations

1. `BackgroundShape data wall anchors` replaces `selected : Fin degree` by
   `anchors : Finset (Fin degree)` and quantifies the three block clauses
   over sheets related to **none** of them (`¬ IsSelected data wall anchors`).
   Every proof of `LimitChainCore.Background` goes through verbatim, because
   each one uses its `hSheet` only through `pasted_left_block`,
   `pasted_right_block` and `pasted_newEdge_block`.
2. `LiftData` drops `selected_valency_ne_two`.  That clause is **false** in
   `{w2-r1-nd2}` (`W2R1StableGraph.BlockMember.nd2_selected_valency_eq_two`),
   where both blocks contribute chains rather than trivalent vertices.  It is
   replaced by exactly what it was used for, and by exactly what the nd2 row
   identities supply: `selected_consecutive`, saying that a consecutive pair
   of the incoming stable quotient at a **selected** wall vertex still lands
   on one outgoing row.  `ofOneBlock` derives it from the old clause.
3. `SelectedData`'s five fields become `IsSelected`-quantified, and one of
   them is weakened for the same reason as `LiftData`'s.  The core asks a
   divalent selected endpoint to carry a new occurrence **and its own
   representative**; in `{w2-r1-nd2}` the retained member's two divalent
   endpoints above one block carry the *same* new occurrence with *different*
   old partners -- `e₃` on the single side, `e₂` on the doubled one -- so no
   single representative map can serve both.  The two `selected_*_pair` fields
   therefore ask only that the old partner lie in the representative's
   **incoming** row, which is exactly
   `W2R1SourceProfile.SourceProfile.nd2_stablePath_eq`.  `ofOneBlock` takes
   the partner to be the representative itself.
4. `GraphData` carries one `selectedSide` and one `selectedFlag` **per
   anchor**, and `branchImage` is built as a bijection onto the union of the
   branch stars.  Two extra fields pay for that union: `anchors_sep` (the
   anchors name distinct wall blocks) and `branch_ne` (distinct anchors have
   distinct branch vertices).  `branch_ne` is **not** an extra assumption when
   the anchors sit on opposite sides of the new edge: `branch_ne_of_side_ne`
   proves it, and that is the `{w2-r1}` configuration
   (`W2R1StableGraph.branch_side_ne`).

## Nothing is duplicated silently

Each of the four structures comes with `ofOneBlock`, sending the core's
structure to the singleton-anchor instance of this one, and with agreement
theorems for every construction the successor stages use:
`Background.replace`, `LiftData.stablePathLift`, `SelectedData.rowOfEdge`,
`SelectedData.stablePathEquiv`, `GraphData.branchImage`,
`GraphData.equivalence`.  `toOneBlock` goes back, and
`toOneBlock_ofOneBlock` is the identity.

## What is proved here

The whole of `LimitChainCore` §3--§5 at the anchor set: the background
replacement bijection (`Background.nonDanglingIncident_fresh_eq_image`,
`replace_injOn`, `nonDanglingValency_fresh_eq`,
`retained_stablePath_eq_replace`, `background_retained_eq_of_consecutive`),
the stable lift and its surjectivity, the reverse row assignment `rowOfEdge`
and the row equivalence `stablePathEquiv`, the retained columns
`matrix_retained`, the regrown column's split `matrix_new_split` with a
per-anchor `selected_set`, and `GraphData.equivalence`.

## Discipline

As in the core: every endpoint statement is an identity of **occurrence**
sets, never of stable-row labels, and no hypothesis beyond the structure
fields and `data.Valid` is added to any statement.
-/

namespace DraismaVargas.LocalCases.LimitChainTwoBlock

open DraismaVargas.Infrastructure
open TargetExpansion
open BalancedGlobal
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open ResolutionCoarseFine ResolutionM11
open ResolutionAwayFromWall StableSourceMatrix StablePathCount
open LimitChainCore (pasted wallSide wallSide_false wallSide_true
  sourceEdge_eq_iff_rel sourceVertex_ofSheet wall_rel_of_incident
  sourceEndpoint_eq_of_rel old_incident_fresh_selected_info
  old_incident_old_selected_info old_incident_fresh_sheet_rel
  new_incident_old_sheet_rel newSourceEdge_repr old_incident_old_sheet_rel
  oldSourceEdge_incident_old)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (datum : GluingDatum target degree)
    (vertex : datum.SourceVertex) : DecidableEq (IncidentSourceEdge datum vertex) :=
  Classical.decEq _

/-! ## §1  Selected sheets

A sheet is **selected** when it lies in the wall block of one of the
distinguished anchors, and **background** otherwise.  For a singleton anchor
set this is the core's `(data.vertexPartition wall).Rel selected sheet`. -/

/-- A sheet above one of the distinguished wall blocks. -/
def IsSelected (data : GluingDatum target degree) (wall : target.V)
    (anchors : Finset (Fin degree)) (sheet : Fin degree) : Prop :=
  ∃ anchor ∈ anchors, (data.vertexPartition wall).Rel anchor sheet

variable {anchors : Finset (Fin degree)}

theorem isSelected_of_rel {anchor sheet : Fin degree} (hMem : anchor ∈ anchors)
    (hRel : (data.vertexPartition wall).Rel anchor sheet) :
    IsSelected data wall anchors sheet := ⟨anchor, hMem, hRel⟩

theorem isSelected_trans {sheet other : Fin degree}
    (hSheet : IsSelected data wall anchors sheet)
    (hRel : (data.vertexPartition wall).Rel sheet other) :
    IsSelected data wall anchors other := by
  obtain ⟨anchor, hMem, hAnchor⟩ := hSheet
  exact ⟨anchor, hMem, hAnchor.trans hRel⟩

theorem not_isSelected_trans {sheet other : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    (hRel : (data.vertexPartition wall).Rel sheet other) :
    ¬ IsSelected data wall anchors other :=
  fun hOther ↦ hSheet (isSelected_trans hOther hRel.symm)

/-- **The singleton anchor set is the core's distinguished block.** -/
@[simp] theorem isSelected_singleton (anchor sheet : Fin degree) :
    IsSelected data wall {anchor} sheet ↔
      (data.vertexPartition wall).Rel anchor sheet := by
  constructor
  · rintro ⟨other, hOther, hRel⟩
    rwa [Finset.mem_singleton.mp hOther] at hRel
  · intro hRel
    exact ⟨anchor, Finset.mem_singleton_self _, hRel⟩

/-! ## §2  The background shape at a set of anchors -/

/-- What a member looks like away from **every** distinguished wall block. -/
structure BackgroundShape (data : GluingDatum target degree) (wall : target.V)
    (anchors : Finset (Fin degree)) extends LimitChainCore.WallCandidate data wall where
  /-- Off every distinguished block the retained endpoint carries the retained
  direction's class. -/
  left_block : ∀ {sheet : Fin degree}, ¬ IsSelected data wall anchors sheet →
    (pasted candidate).left.block sheet = (data.edgePartition retainedTarget).block sheet
  /-- the fresh endpoint the whole wall block. -/
  right_block : ∀ {sheet : Fin degree}, ¬ IsSelected data wall anchors sheet →
    (pasted candidate).right.block sheet = (data.vertexPartition wall).block sheet
  /-- and the new edge the retained direction's class. -/
  newEdge_block : ∀ {sheet : Fin degree}, ¬ IsSelected data wall anchors sheet →
    (pasted candidate).newEdge.block sheet = (data.edgePartition retainedTarget).block sheet
  genus_eq : genus candidate.datum.sourceGraph = genus data.sourceGraph

namespace BackgroundShape

variable (shape : BackgroundShape data wall anchors)

/-- The pasted local resolution of the member. -/
noncomputable def pasted : LocalResolution degree :=
  LimitChainCore.pasted shape.candidate

theorem pasted_left_block {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet) :
    shape.pasted.left.block sheet =
      (data.edgePartition shape.retainedTarget).block sheet :=
  shape.left_block hSheet

theorem pasted_right_block {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet) :
    shape.pasted.right.block sheet = (data.vertexPartition wall).block sheet :=
  shape.right_block hSheet

theorem pasted_newEdge_block {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet) :
    shape.pasted.newEdge.block sheet =
      (data.edgePartition shape.retainedTarget).block sheet :=
  shape.newEdge_block hSheet

/-! ### The one-block core as the singleton instance -/

/-- **The core's background shape is the singleton-anchor instance.** -/
def ofOneBlock (shape : LimitChainCore.BackgroundShape data wall) :
    BackgroundShape data wall {shape.selected} where
  toWallCandidate := shape.toWallCandidate
  left_block := fun hSheet ↦ shape.left_block
    (fun hRel ↦ hSheet ((isSelected_singleton _ _).mpr hRel))
  right_block := fun hSheet ↦ shape.right_block
    (fun hRel ↦ hSheet ((isSelected_singleton _ _).mpr hRel))
  newEdge_block := fun hSheet ↦ shape.newEdge_block
    (fun hRel ↦ hSheet ((isSelected_singleton _ _).mpr hRel))
  genus_eq := shape.genus_eq

/-- and back. -/
def toOneBlock (anchor : Fin degree) (shape : BackgroundShape data wall {anchor}) :
    LimitChainCore.BackgroundShape data wall where
  toWallCandidate := shape.toWallCandidate
  selected := anchor
  left_block := fun hSheet ↦ shape.left_block
    (fun hSel ↦ hSheet ((isSelected_singleton _ _).mp hSel))
  right_block := fun hSheet ↦ shape.right_block
    (fun hSel ↦ hSheet ((isSelected_singleton _ _).mp hSel))
  newEdge_block := fun hSheet ↦ shape.newEdge_block
    (fun hSel ↦ hSheet ((isSelected_singleton _ _).mp hSel))
  genus_eq := shape.genus_eq

@[simp] theorem ofOneBlock_candidate (shape : LimitChainCore.BackgroundShape data wall) :
    (ofOneBlock shape).candidate = shape.candidate := rfl

@[simp] theorem ofOneBlock_retainedTarget (shape : LimitChainCore.BackgroundShape data wall) :
    (ofOneBlock shape).retainedTarget = shape.retainedTarget := rfl

/-- **Round trip**: the singleton instance loses nothing. -/
theorem toOneBlock_ofOneBlock (shape : LimitChainCore.BackgroundShape data wall) :
    toOneBlock shape.selected (ofOneBlock shape) = shape := rfl

/-! ### The background census, verbatim from the core -/

theorem old_isDangling_iff (hValid : data.Valid) (edge : data.SourceEdge) :
    IsDangling shape.candidate.datum (shape.candidate.oldSourceEdge edge) ↔
      IsDangling data edge :=
  ResolutionPruning.isDangling_oldSourceEdge_iff shape.candidate hValid
    shape.genus_eq edge

theorem new_ne_old (sheet : Fin degree) (edge : data.SourceEdge) :
    shape.candidate.newSourceEdge sheet ≠
      shape.candidate.oldSourceEdge edge := by
  intro hEqual
  have hTargets := congrArg
    (fun item : shape.candidate.datum.SourceEdge ↦ item.1.1) hEqual
  have hLabels :=
    (occurrenceEquiv target wall shape.candidate.right).injective hTargets
  cases hLabels

theorem new_incident_old (sheet : Fin degree) :
    Incident shape.candidate.datum (shape.candidate.newSourceEdge sheet)
      (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) :=
  Or.inl (congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge data wall
    shape.candidate.right shape.pasted
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _ shape.candidate.exterior) sheet))

theorem background_incident_old (sheet : Fin degree) :
    Incident shape.candidate.datum
        (shape.candidate.oldSourceEdge
          (data.sourceEdge shape.retainedTarget sheet))
      (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) :=
  oldSourceEdge_incident_old shape.candidate shape.retainedTarget
    shape.target_mem shape.left sheet

/-- **The complete literal incidence at a background retained endpoint.** -/
theorem incident_old_cases {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    {edge : shape.candidate.datum.SourceEdge}
    (hIncident : Incident shape.candidate.datum edge
      (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) :
    edge = shape.candidate.newSourceEdge sheet ∨
      edge = shape.candidate.oldSourceEdge
        (data.sourceEdge shape.retainedTarget sheet) := by
  rcases ResolutionPruning.sourceEdge_cases shape.candidate edge with
    ⟨old, rfl⟩ | ⟨new, rfl⟩
  · right
    obtain ⟨hData, hRight⟩ :=
      old_incident_old_selected_info shape.candidate
        (WallBlock.ofSheet data wall sheet) sheet
        ((data.vertexPartition wall).rel_repr_left sheet) old hIncident
    have hTarget : old.1.1 = shape.retainedTarget := shape.unique _
      ((incident_iff_target_mem_and_rel data old _).mp hData).1 hRight
    have hSheetRel := old_incident_old_sheet_rel shape.candidate sheet old
      hIncident
    have hMem : old.1.2 ∈ shape.pasted.left.block sheet :=
      (shape.pasted.left.mem_block_iff _ _).mpr hSheetRel
    rw [shape.pasted_left_block hSheet] at hMem
    have hEdgeRel :=
      ((data.edgePartition shape.retainedTarget).mem_block_iff _ _).mp hMem
    refine congrArg shape.candidate.oldSourceEdge (Subtype.ext (Prod.ext ?_ ?_)).symm
    · exact hTarget.symm
    · change (data.edgePartition shape.retainedTarget).repr sheet = old.1.2
      have hRepr : (data.edgePartition shape.retainedTarget).repr old.1.2 =
          old.1.2 := by rw [← hTarget]; exact old.2
      exact hEdgeRel.trans hRepr
  · left
    have hSheetRel := new_incident_old_sheet_rel
      shape.candidate sheet new hIncident
    have hMem : shape.pasted.newEdge.repr new ∈ shape.pasted.left.block sheet :=
      (shape.pasted.left.mem_block_iff _ _).mpr hSheetRel
    rw [shape.pasted_left_block hSheet, ← shape.pasted_newEdge_block hSheet] at hMem
    have hNewRel := (shape.pasted.newEdge.mem_block_iff sheet _).mp hMem
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change shape.pasted.newEdge.repr new = shape.pasted.newEdge.repr sheet
      exact (shape.pasted.newEdge.repr_idem new).symm.trans hNewRel.symm

theorem nonDanglingIncident_old_subset {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet) :
    nonDanglingIncident shape.candidate.datum
        (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) ⊆
      {shape.candidate.newSourceEdge sheet,
        shape.candidate.oldSourceEdge
          (data.sourceEdge shape.retainedTarget sheet)} := by
  classical
  intro edge hMem
  obtain ⟨_, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  rcases shape.incident_old_cases hSheet hIncident with hNew | hOld
  · exact Finset.mem_insert.mpr (Or.inl hNew)
  · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hOld)

/-- **A background new occurrence has exactly the pruning status of its old
representative.** -/
theorem new_isDangling_iff (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet) :
    IsDangling shape.candidate.datum (shape.candidate.newSourceEdge sheet) ↔
      IsDangling data (data.sourceEdge shape.retainedTarget sheet) := by
  classical
  have hNe : (nonDanglingIncident shape.candidate.datum
      (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)).card
        ≠ 1 := by
    rw [card_nonDanglingIncident]
    exact NonDanglingValency.nonDanglingValency_ne_one shape.candidate.datum
      (shape.candidate.datum_valid hValid).1
      (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)
  constructor
  · intro hDangling
    by_contra hOldSurvives
    have hSingle : nonDanglingIncident shape.candidate.datum
        (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) =
        {shape.candidate.oldSourceEdge
          (data.sourceEdge shape.retainedTarget sheet)} := by
      apply Finset.Subset.antisymm
      · intro edge hMem
        obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
        rcases shape.incident_old_cases hSheet hIncident with hNew | hOld
        · exact absurd (hNew ▸ hSurvives) (by simpa using hDangling)
        · exact Finset.mem_singleton.mpr hOld
      · intro edge hMem
        rw [Finset.mem_singleton.mp hMem]
        exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨fun h ↦ hOldSurvives ((shape.old_isDangling_iff hValid _).mp h),
            shape.background_incident_old sheet⟩
    rw [hSingle, Finset.card_singleton] at hNe
    exact hNe rfl
  · intro hDangling
    by_contra hNewSurvives
    have hSingle : nonDanglingIncident shape.candidate.datum
        (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) =
        {shape.candidate.newSourceEdge sheet} := by
      apply Finset.Subset.antisymm
      · intro edge hMem
        obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
        rcases shape.incident_old_cases hSheet hIncident with hNew | hOld
        · exact Finset.mem_singleton.mpr hNew
        · exact absurd (hOld ▸ hSurvives)
            (by simpa using (shape.old_isDangling_iff hValid _).mpr hDangling)
      · intro edge hMem
        rw [Finset.mem_singleton.mp hMem]
        exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨hNewSurvives, shape.new_incident_old sheet⟩
    rw [hSingle, Finset.card_singleton] at hNe
    exact hNe rfl

/-- The complete surviving star at a background retained endpoint whose `t_α`
occurrence survives. -/
theorem nonDanglingIncident_old (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    (hSurvives : ¬ IsDangling data (data.sourceEdge shape.retainedTarget sheet)) :
    nonDanglingIncident shape.candidate.datum
        (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) =
      {shape.candidate.newSourceEdge sheet,
        shape.candidate.oldSourceEdge
          (data.sourceEdge shape.retainedTarget sheet)} := by
  classical
  apply Finset.Subset.antisymm (shape.nonDanglingIncident_old_subset hSheet)
  intro edge hMem
  rcases Finset.mem_insert.mp hMem with rfl | hOld
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨fun h ↦ hSurvives ((shape.new_isDangling_iff hValid hSheet).mp h),
        shape.new_incident_old sheet⟩
  · rw [Finset.mem_singleton.mp hOld]
    exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨fun h ↦ hSurvives ((shape.old_isDangling_iff hValid _).mp h),
        shape.background_incident_old sheet⟩

theorem old_nonDanglingValency_eq_two (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    (hSurvives : ¬ IsDangling data (data.sourceEdge shape.retainedTarget sheet)) :
    nonDanglingValency shape.candidate.datum
      (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) = 2 := by
  rw [← card_nonDanglingIncident,
    shape.nonDanglingIncident_old hValid hSheet hSurvives]
  exact Finset.card_pair (shape.new_ne_old _ _)

/-- **Every surviving background new occurrence lies in its old
representative's stable row.** -/
theorem new_stablePath_eq (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    (hSurvives : ¬ IsDangling data (data.sourceEdge shape.retainedTarget sheet)) :
    NonDanglingEdge.stablePath
        (⟨shape.candidate.newSourceEdge sheet,
          fun h ↦ hSurvives ((shape.new_isDangling_iff hValid hSheet).mp h)⟩ :
          NonDanglingEdge shape.candidate.datum) =
      NonDanglingEdge.stablePath
        (⟨shape.candidate.oldSourceEdge
            (data.sourceEdge shape.retainedTarget sheet),
          fun h ↦ hSurvives ((shape.old_isDangling_iff hValid _).mp h)⟩ :
          NonDanglingEdge shape.candidate.datum) := by
  refine stablePath_eq_of_consecutive ⟨?_, _, shape.new_incident_old sheet,
    shape.background_incident_old sheet,
    shape.old_nonDanglingValency_eq_two hValid hSheet hSurvives⟩
  intro hEq
  exact shape.new_ne_old sheet _ (congrArg Subtype.val hEq)

/-- **And carries its index.** -/
theorem newIndex_eq {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet) :
    shape.candidate.datum.sourceEdgeIndex
        (shape.candidate.newSourceEdge sheet) =
      data.sourceEdgeIndex (data.sourceEdge shape.retainedTarget sheet) := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    GluingDatum.sourceEdgeIndex_sourceEdge]
  change shape.pasted.newEdge.blockCard sheet =
    (data.edgePartition shape.retainedTarget).blockCard sheet
  unfold SheetPartition.blockCard
  rw [shape.pasted_newEdge_block hSheet]

end BackgroundShape

/-! ## §3  The background wall blocks: the replacement bijection

Away from **every** distinguished block the member installs the retained
direction's own star, so the whole of `LimitChainCore.Background` runs at the
anchor set.  Each proof is the core's, with `¬ Rel selected sheet` replaced by
`¬ IsSelected data wall anchors sheet`. -/

namespace Background

variable (shape : BackgroundShape data wall anchors)

/-- Sheets of one background wall block give one trivalent endpoint. -/
theorem fresh_endpoint_eq {first second : Fin degree}
    (hFirst : ¬ IsSelected data wall anchors first)
    (hRel : (data.vertexPartition wall).Rel first second) :
    shape.candidate.datum.sourceEndpoint (freshVertex target) first =
      shape.candidate.datum.sourceEndpoint (freshVertex target) second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change shape.pasted.right.repr first = shape.pasted.right.repr second
    have hMem : second ∈ (data.vertexPartition wall).block first :=
      ((data.vertexPartition wall).mem_block_iff first second).mpr hRel
    rw [← shape.pasted_right_block hFirst] at hMem
    exact (shape.pasted.right.mem_block_iff first second).mp hMem

/-- Background new occurrences are indexed by the background direction's own
classes. -/
theorem newSourceEdge_eq_of_edge_rel {first second : Fin degree}
    (hFirst : ¬ IsSelected data wall anchors first)
    (hRel : (data.edgePartition shape.retainedTarget).Rel first second) :
    shape.candidate.newSourceEdge second = shape.candidate.newSourceEdge first := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change shape.pasted.newEdge.repr second = shape.pasted.newEdge.repr first
    have hMem : second ∈ (data.edgePartition shape.retainedTarget).block first :=
      ((data.edgePartition shape.retainedTarget).mem_block_iff first second).mpr
        hRel
    rw [← shape.pasted_newEdge_block hFirst] at hMem
    exact ((shape.pasted.newEdge.mem_block_iff first second).mp hMem).symm

theorem newSourceEdge_eq_iff {first second : Fin degree}
    (hFirst : ¬ IsSelected data wall anchors first) :
    shape.candidate.newSourceEdge first = shape.candidate.newSourceEdge second ↔
      (data.edgePartition shape.retainedTarget).Rel first second := by
  constructor
  · intro hEqual
    have hRel : shape.pasted.newEdge.Rel first second :=
      congrArg (fun item : shape.candidate.datum.SourceEdge ↦ item.1.2) hEqual
    have hMem : second ∈ shape.pasted.newEdge.block first :=
      (shape.pasted.newEdge.mem_block_iff _ _).mpr hRel
    rw [shape.pasted_newEdge_block hFirst] at hMem
    exact ((data.edgePartition shape.retainedTarget).mem_block_iff _ _).mp hMem
  · intro hRel
    exact (newSourceEdge_eq_of_edge_rel shape hFirst hRel).symm

/-- A new occurrence meets the trivalent endpoint above every sheet of its own
wall block. -/
theorem new_incident_fresh {sheet other : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    (hRel : (data.vertexPartition wall).Rel sheet other) :
    Incident shape.candidate.datum (shape.candidate.newSourceEdge other)
      (shape.candidate.datum.sourceEndpoint (freshVertex target) sheet) := by
  have hBase : Incident shape.candidate.datum
      (shape.candidate.newSourceEdge other)
      (shape.candidate.datum.sourceEndpoint (freshVertex target) other) :=
    Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall
      shape.candidate.right shape.pasted
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ shape.candidate.exterior)
      other))
  rwa [fresh_endpoint_eq shape hSheet hRel]

/-- Conversely a new occurrence at a background trivalent endpoint is named by
a sheet of that endpoint's wall block. -/
theorem new_incident_fresh_rel {sheet new : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    (hIncident : Incident shape.candidate.datum
      (shape.candidate.newSourceEdge new)
      (shape.candidate.datum.sourceEndpoint (freshVertex target) sheet)) :
    (data.vertexPartition wall).Rel sheet (shape.pasted.newEdge.repr new) := by
  have hOutgoing := (incident_iff_target_mem_and_rel shape.candidate.datum
    (shape.candidate.newSourceEdge new)
    (shape.candidate.datum.sourceEndpoint (freshVertex target) sheet)).mp hIncident
  change occurrenceEquiv target wall shape.candidate.right none ∈
      GluingDatum.incidentEdges (freshVertex target) ∧
    shape.pasted.right.Rel (shape.pasted.right.repr sheet)
      (shape.pasted.newEdge.repr new) at hOutgoing
  have hRightRel : shape.pasted.right.Rel sheet
      (shape.pasted.newEdge.repr new) :=
    (shape.pasted.right.rel_repr_right sheet).trans hOutgoing.2
  have hMem : shape.pasted.newEdge.repr new ∈ shape.pasted.right.block sheet :=
    (shape.pasted.right.mem_block_iff _ _).mpr hRightRel
  rw [shape.pasted_right_block hSheet] at hMem
  exact ((data.vertexPartition wall).mem_block_iff _ _).mp hMem

/-- **The complete incidence dictionary at a background trivalent endpoint for
retained occurrences.** -/
theorem old_incident_fresh_iff {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    (old : data.SourceEdge) :
    Incident shape.candidate.datum (shape.candidate.oldSourceEdge old)
        (shape.candidate.datum.sourceEndpoint (freshVertex target) sheet) ↔
      Incident data old (data.sourceEndpoint wall sheet) ∧
        old.1.1 ≠ shape.retainedTarget := by
  constructor
  · intro hIncident
    obtain ⟨hData, hRight⟩ := old_incident_fresh_selected_info
      shape.candidate (WallBlock.ofSheet data wall sheet) sheet
      ((data.vertexPartition wall).rel_repr_left sheet) old hIncident
    rw [sourceVertex_ofSheet data wall sheet] at hData
    exact ⟨hData, (shape.right_eq_true_iff old.1.1
      ((incident_iff_target_mem_and_rel data old _).mp hData).1).mp hRight⟩
  · rintro ⟨hData, hNe⟩
    have hMem : old.1.1 ∈ GluingDatum.incidentEdges wall :=
      ((incident_iff_target_mem_and_rel data old _).mp hData).1
    have hBase : Incident shape.candidate.datum
        (shape.candidate.oldSourceEdge (data.sourceEdge old.1.1 old.1.2))
        (shape.candidate.datum.sourceEndpoint (freshVertex target) old.1.2) :=
      M11SplitSurvival.oldSourceEdge_incident_fresh shape.candidate old.1.1 hMem
        ((shape.right_eq_true_iff old.1.1 hMem).mpr hNe) old.1.2
    rw [GluingDatum.sourceEdge_self data old] at hBase
    rwa [← fresh_endpoint_eq shape hSheet
      (wall_rel_of_incident data wall sheet old hData)] at hBase

/-! ### The replacement bijection at a background trivalent endpoint -/

/-- An occurrence at a background wall vertex has a background sheet. -/
theorem background_of_incident {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    {edge : data.SourceEdge}
    (hIncident : Incident data edge (data.sourceEndpoint wall sheet)) :
    ¬ IsSelected data wall anchors edge.1.2 :=
  not_isSelected_trans hSheet
    (wall_rel_of_incident data wall sheet edge hIncident)

/-- **The member occurrence representing an incoming survivor at a background
wall vertex.** -/
noncomputable def replace (shape : BackgroundShape data wall anchors)
    (edge : data.SourceEdge) : shape.candidate.datum.SourceEdge :=
  if edge.1.1 = shape.retainedTarget then
    shape.candidate.newSourceEdge edge.1.2
  else shape.candidate.oldSourceEdge edge

theorem replace_of_target {edge : data.SourceEdge}
    (hTarget : edge.1.1 = shape.retainedTarget) :
    replace shape edge = shape.candidate.newSourceEdge edge.1.2 := ite_eq_left hTarget

theorem replace_of_target_ne {edge : data.SourceEdge}
    (hTarget : edge.1.1 ≠ shape.retainedTarget) :
    replace shape edge = shape.candidate.oldSourceEdge edge := ite_eq_right hTarget

/-- **The replacement agrees with the core's at a singleton anchor.** -/
theorem replace_ofOneBlock (shape : LimitChainCore.BackgroundShape data wall) :
    replace (BackgroundShape.ofOneBlock shape) =
      LimitChainCore.Background.replace shape := rfl

theorem replace_survives (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    {edge : data.SourceEdge} (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (data.sourceEndpoint wall sheet)) :
    ¬ IsDangling shape.candidate.datum (replace shape edge) := by
  by_cases hTarget : edge.1.1 = shape.retainedTarget
  · rw [replace_of_target shape hTarget]
    intro hDangling
    apply hSurvives
    rw [← shape.sourceEdge_retained_self hTarget]
    exact (shape.new_isDangling_iff hValid
      (background_of_incident hSheet hIncident)).mp hDangling
  · rw [replace_of_target_ne shape hTarget]
    exact ResolutionSurvival.not_isDangling_oldSourceEdge shape.candidate hValid.1
      edge hSurvives

theorem replace_incident {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    {edge : data.SourceEdge}
    (hIncident : Incident data edge (data.sourceEndpoint wall sheet)) :
    Incident shape.candidate.datum (replace shape edge)
      (shape.candidate.datum.sourceEndpoint (freshVertex target) sheet) := by
  by_cases hTarget : edge.1.1 = shape.retainedTarget
  · rw [replace_of_target shape hTarget]
    exact new_incident_fresh shape hSheet
      (wall_rel_of_incident data wall sheet edge hIncident)
  · rw [replace_of_target_ne shape hTarget]
    exact (old_incident_fresh_iff shape hSheet edge).mpr ⟨hIncident, hTarget⟩

/-- **The background trivalent endpoint's surviving star is the image of the
incoming one.** -/
theorem nonDanglingIncident_fresh_eq_image (hValid : data.Valid)
    {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet) :
    nonDanglingIncident shape.candidate.datum
        (shape.candidate.datum.sourceEndpoint (freshVertex target) sheet) =
      (nonDanglingIncident data (data.sourceEndpoint wall sheet)).image
        (replace shape) := by
  classical
  ext item
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases shape.candidate item with
      ⟨old, rfl⟩ | ⟨new, rfl⟩
    · obtain ⟨hData, hNe⟩ := (old_incident_fresh_iff shape hSheet old).mp hIncident
      refine Finset.mem_image.mpr ⟨old, (mem_nonDanglingIncident _ _ _).mpr
        ⟨fun hDangling ↦ hSurvives
          ((shape.old_isDangling_iff hValid old).mpr hDangling), hData⟩, ?_⟩
      exact replace_of_target_ne shape hNe
    · have hRel := new_incident_fresh_rel shape hSheet hIncident
      have hRepr : shape.candidate.newSourceEdge
          (shape.pasted.newEdge.repr new) =
            shape.candidate.newSourceEdge new :=
        newSourceEdge_repr shape.candidate new
      have hBackground : ¬ IsSelected data wall anchors
          (shape.pasted.newEdge.repr new) := not_isSelected_trans hSheet hRel
      have hNewSurvives : ¬ IsDangling shape.candidate.datum
          (shape.candidate.newSourceEdge (shape.pasted.newEdge.repr new)) := by
        rw [hRepr]; exact hSurvives
      have hOldSurvives : ¬ IsDangling data (data.sourceEdge
          shape.retainedTarget (shape.pasted.newEdge.repr new)) :=
        fun hDangling ↦ hNewSurvives
          ((shape.new_isDangling_iff hValid hBackground).mpr hDangling)
      refine Finset.mem_image.mpr ⟨data.sourceEdge shape.retainedTarget
        (shape.pasted.newEdge.repr new), (mem_nonDanglingIncident _ _ _).mpr
        ⟨hOldSurvives, ?_⟩, ?_⟩
      · rw [sourceEndpoint_eq_of_rel data wall hRel]
        exact incident_sourceEdge_sourceEndpoint data wall shape.retainedTarget
          shape.target_mem _
      · rw [replace_of_target shape (by rfl)]
        refine Eq.trans ?_ hRepr
        exact newSourceEdge_eq_of_edge_rel shape hBackground
          ((data.edgePartition shape.retainedTarget).rel_repr_right _)
  · intro hMem
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOld
    exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨replace_survives shape hValid hSheet hSurvives hIncident,
        replace_incident shape hSheet hIncident⟩

theorem replace_injOn {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet) :
    Set.InjOn (replace shape)
      ↑(nonDanglingIncident data (data.sourceEndpoint wall sheet)) := by
  intro first hFirst second hSecond hEqual
  have hFirstIncident : Incident data first (data.sourceEndpoint wall sheet) :=
    ((mem_nonDanglingIncident _ _ _).mp hFirst).2
  have hSecondIncident : Incident data second (data.sourceEndpoint wall sheet) :=
    ((mem_nonDanglingIncident _ _ _).mp hSecond).2
  by_cases hFirstTarget : first.1.1 = shape.retainedTarget
  · by_cases hSecondTarget : second.1.1 = shape.retainedTarget
    · rw [replace_of_target shape hFirstTarget,
        replace_of_target shape hSecondTarget] at hEqual
      have hRel := (newSourceEdge_eq_iff shape
        (background_of_incident hSheet hFirstIncident)).mp hEqual
      have hSource := (sourceEdge_eq_iff_rel data shape.retainedTarget
        first.1.2 second.1.2).mpr hRel
      rw [shape.sourceEdge_retained_self hFirstTarget,
        shape.sourceEdge_retained_self hSecondTarget] at hSource
      exact hSource
    · rw [replace_of_target shape hFirstTarget,
        replace_of_target_ne shape hSecondTarget] at hEqual
      exact absurd hEqual (shape.new_ne_old _ _)
  · by_cases hSecondTarget : second.1.1 = shape.retainedTarget
    · rw [replace_of_target_ne shape hFirstTarget,
        replace_of_target shape hSecondTarget] at hEqual
      exact absurd hEqual.symm (shape.new_ne_old _ _)
    · rw [replace_of_target_ne shape hFirstTarget,
        replace_of_target_ne shape hSecondTarget] at hEqual
      exact ResolutionCut.oldSourceEdge_injective shape.candidate hEqual

/-- **Background trivalent endpoints keep the incoming surviving valency.** -/
theorem nonDanglingValency_fresh_eq (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet) :
    nonDanglingValency shape.candidate.datum
        (shape.candidate.datum.sourceEndpoint (freshVertex target) sheet) =
      nonDanglingValency data (data.sourceEndpoint wall sheet) := by
  classical
  rw [← card_nonDanglingIncident, ← card_nonDanglingIncident,
    nonDanglingIncident_fresh_eq_image shape hValid hSheet,
    Finset.card_image_of_injOn (replace_injOn shape hSheet)]

/-- **Every retained background survivor keeps the row of its replacement.** -/
theorem retained_stablePath_eq_replace (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    {edge : data.SourceEdge} (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (data.sourceEndpoint wall sheet))
    (hReplace : ¬ IsDangling shape.candidate.datum (replace shape edge)) :
    (retainedEdge shape.candidate hValid.1 ⟨edge, hSurvives⟩).stablePath =
      NonDanglingEdge.stablePath
        (⟨replace shape edge, hReplace⟩ : NonDanglingEdge shape.candidate.datum) := by
  by_cases hTarget : edge.1.1 = shape.retainedTarget
  · have hBackground := background_of_incident hSheet hIncident
    have hSelf := shape.sourceEdge_retained_self hTarget
    have hOldSurvives : ¬ IsDangling data
        (data.sourceEdge shape.retainedTarget edge.1.2) := by
      rw [hSelf]; exact hSurvives
    have hPath := shape.new_stablePath_eq hValid hBackground hOldSurvives
    refine Eq.trans ?_ (hPath.symm.trans ?_)
    · exact congrArg NonDanglingEdge.stablePath
        (Subtype.ext (congrArg shape.candidate.oldSourceEdge hSelf.symm))
    · exact congrArg NonDanglingEdge.stablePath
        (Subtype.ext (replace_of_target shape hTarget).symm)
  · exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (replace_of_target_ne shape hTarget).symm)

/-- **The background half of the lift's well-definedness.** -/
theorem background_retained_eq_of_consecutive (hValid : data.Valid)
    {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    (first second : NonDanglingEdge data) (hNe : first ≠ second)
    (hFirst : Incident data first.1 (data.sourceEndpoint wall sheet))
    (hSecond : Incident data second.1 (data.sourceEndpoint wall sheet))
    (hValency : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2) :
    (retainedEdge shape.candidate hValid.1 first).stablePath =
      (retainedEdge shape.candidate hValid.1 second).stablePath := by
  classical
  have hFirstMem : first.1 ∈ nonDanglingIncident data
      (data.sourceEndpoint wall sheet) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨first.2, hFirst⟩
  have hSecondMem : second.1 ∈ nonDanglingIncident data
      (data.sourceEndpoint wall sheet) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨second.2, hSecond⟩
  have hFirstReplace := replace_survives shape hValid hSheet first.2 hFirst
  have hSecondReplace := replace_survives shape hValid hSheet second.2 hSecond
  have hNeReplace :
      (⟨replace shape first.1, hFirstReplace⟩ :
          NonDanglingEdge shape.candidate.datum) ≠
        ⟨replace shape second.1, hSecondReplace⟩ := by
    intro hEqual
    exact hNe (Subtype.ext (replace_injOn shape hSheet
      (Finset.mem_coe.mpr hFirstMem) (Finset.mem_coe.mpr hSecondMem)
      (congrArg Subtype.val hEqual)))
  have hConsecutive : Consecutive shape.candidate.datum
      ⟨replace shape first.1, hFirstReplace⟩
      ⟨replace shape second.1, hSecondReplace⟩ :=
    ⟨hNeReplace, shape.candidate.datum.sourceEndpoint (freshVertex target) sheet,
      replace_incident shape hSheet hFirst, replace_incident shape hSheet hSecond,
      (nonDanglingValency_fresh_eq shape hValid hSheet).trans hValency⟩
  calc (retainedEdge shape.candidate hValid.1 first).stablePath
      = NonDanglingEdge.stablePath
          (⟨replace shape first.1, hFirstReplace⟩ :
            NonDanglingEdge shape.candidate.datum) :=
        retained_stablePath_eq_replace shape hValid hSheet first.2 hFirst _
    _ = NonDanglingEdge.stablePath
          (⟨replace shape second.1, hSecondReplace⟩ :
            NonDanglingEdge shape.candidate.datum) :=
        stablePath_eq_of_consecutive hConsecutive
    _ = (retainedEdge shape.candidate hValid.1 second).stablePath :=
        (retained_stablePath_eq_replace shape hValid hSheet second.2 hSecond _).symm

/-- The complete surviving star at a divalent background endpoint of surviving
valency two. -/
theorem nonDanglingIncident_old_background {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    (hValency : nonDanglingValency shape.candidate.datum
      (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) = 2) :
    nonDanglingIncident shape.candidate.datum
        (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) =
      {shape.candidate.newSourceEdge sheet,
        shape.candidate.oldSourceEdge
          (data.sourceEdge shape.retainedTarget sheet)} := by
  classical
  refine Finset.eq_of_subset_of_card_le (shape.nonDanglingIncident_old_subset hSheet)
    (le_of_eq ?_)
  rw [Finset.card_pair (shape.new_ne_old _ _), card_nonDanglingIncident, hValency]

end Background

/-! ## §4  The stable lift at a set of anchors

`LimitChainCore.LiftData.selected_valency_ne_two` is **false** for a
`{w2-r1-nd2}` member: `W2R1StableGraph.BlockMember.nd2_selected_valency_eq_two`
says the distinguished vertex is divalent there, in both members and at both
blocks.  It is used in exactly one place -- the selected branch of
`retained_stablePath_eq_of_consecutive`, where it makes that branch vacuous --
so the variant records the conclusion of that branch instead, which is what
the nd2 row identities supply.  `ofOneBlock` derives it from the core's
clause; there is **no** converse, and that is the honest content of the
weakening. -/

/-- A member for which retention respects the incoming stable quotient at
every distinguished vertex as well as over the background. -/
structure LiftData (data : GluingDatum target degree) (wall : target.V)
    (anchors : Finset (Fin degree)) extends BackgroundShape data wall anchors where
  valid : data.Valid
  /-- A consecutive pair of the incoming stable quotient at a **selected** wall
  vertex still lands on one outgoing row. -/
  selected_consecutive : ∀ {sheet : Fin degree}, IsSelected data wall anchors sheet →
    ∀ (first second : NonDanglingEdge data), first ≠ second →
      Incident data first.1 (data.sourceEndpoint wall sheet) →
      Incident data second.1 (data.sourceEndpoint wall sheet) →
      nonDanglingValency data (data.sourceEndpoint wall sheet) = 2 →
      (retainedEdge candidate valid.1 first).stablePath =
        (retainedEdge candidate valid.1 second).stablePath

namespace LiftData

variable (rd : LiftData data wall anchors)

/-- **The core's lift data is the singleton-anchor instance**: trivalence of
the distinguished vertex makes the new clause vacuous. -/
def ofOneBlock (rd : LimitChainCore.LiftData data wall) :
    LiftData data wall {rd.selected} where
  toBackgroundShape := BackgroundShape.ofOneBlock rd.toBackgroundShape
  valid := rd.valid
  selected_consecutive := by
    intro sheet hSel first second _hNe _hFirst _hSecond hValency
    rw [← sourceEndpoint_eq_of_rel data wall
      ((isSelected_singleton _ _).mp hSel)] at hValency
    exact absurd hValency rd.selected_valency_ne_two

@[simp] theorem ofOneBlock_candidate (rd : LimitChainCore.LiftData data wall) :
    (ofOneBlock rd).candidate = rd.candidate := rfl

/-! ### The stable lift -/

/-- **The defining relation of the incoming stable quotient is respected by
retention.** -/
theorem retained_stablePath_eq_of_consecutive
    (first second : NonDanglingEdge data)
    (hConsecutive : Consecutive data first second) :
    (retainedEdge rd.candidate rd.valid.1 first).stablePath =
      (retainedEdge rd.candidate rd.valid.1 second).stablePath := by
  obtain ⟨hNe, vertex, hFirst, hSecond, hValency⟩ := hConsecutive
  by_cases hAt : vertex.1.1 = wall
  · have hVertex : data.sourceEndpoint wall vertex.1.2 = vertex :=
      (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr ⟨hAt.symm, rfl⟩
    have hValency' : nonDanglingValency data
        (data.sourceEndpoint wall vertex.1.2) = 2 := by
      rw [hVertex]; exact hValency
    have hFirst' : Incident data first.1
        (data.sourceEndpoint wall vertex.1.2) := by rw [hVertex]; exact hFirst
    have hSecond' : Incident data second.1
        (data.sourceEndpoint wall vertex.1.2) := by rw [hVertex]; exact hSecond
    by_cases hSelected : IsSelected data wall anchors vertex.1.2
    · exact rd.selected_consecutive hSelected first second hNe hFirst' hSecond'
        hValency'
    · exact Background.background_retained_eq_of_consecutive rd.toBackgroundShape
        rd.valid hSelected first second hNe hFirst' hSecond' hValency'
  · exact stablePath_eq_of_consecutive
      (consecutive_retained_of_away rd.candidate rd.valid rd.genus_eq
        first second hNe vertex hAt hFirst hSecond hValency)

/-- **The occurrence-induced stable-row map of a member.** -/
noncomputable def stablePathLift :
    StablePath data → StablePath rd.candidate.datum :=
  Quot.lift (fun edge ↦ (retainedEdge rd.candidate rd.valid.1 edge).stablePath)
    (fun _ _ hConsecutive ↦
      rd.retained_stablePath_eq_of_consecutive _ _ hConsecutive)

@[simp] theorem stablePathLift_mk (edge : NonDanglingEdge data) :
    rd.stablePathLift edge.stablePath =
      (retainedEdge rd.candidate rd.valid.1 edge).stablePath := rfl

/-- **The lift agrees with the core's at a singleton anchor.** -/
theorem stablePathLift_ofOneBlock (rd : LimitChainCore.LiftData data wall) :
    (ofOneBlock rd).stablePathLift = rd.stablePathLift := rfl

theorem replace_stablePath {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    {edge : data.SourceEdge} (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (data.sourceEndpoint wall sheet))
    (hReplace : ¬ IsDangling rd.candidate.datum
      (Background.replace rd.toBackgroundShape edge)) :
    NonDanglingEdge.stablePath
        (⟨Background.replace rd.toBackgroundShape edge, hReplace⟩ :
          NonDanglingEdge rd.candidate.datum) =
      rd.stablePathLift
        (NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data)) :=
  Eq.trans (Background.retained_stablePath_eq_replace rd.toBackgroundShape rd.valid
      hSheet hSurvives hIncident hReplace).symm
    (rd.stablePathLift_mk ⟨edge, hSurvives⟩).symm

end LiftData

/-! ## §5  The selected census, the row descent and the retained columns

`SelectedData`'s five fields are the core's, with `Rel selected sheet`
replaced by `IsSelected data wall anchors sheet`; nothing in them was
single-block by nature.  The representative map is a single
`Fin degree → data.SourceEdge`, as in the core: it is read at a selected
sheet, and which anchor's block that sheet lies in is not part of the data. -/

instance instDecidableIsSelected (data : GluingDatum target degree) (wall : target.V)
    (anchors : Finset (Fin degree)) (sheet : Fin degree) :
    Decidable (IsSelected data wall anchors sheet) :=
  inferInstanceAs
    (Decidable (∃ anchor ∈ anchors, (data.vertexPartition wall).Rel anchor sheet))

/-- A member together with the selected-block data the row descent and the
limit matrices need. -/
structure SelectedData (data : GluingDatum target degree) (wall : target.V)
    (anchors : Finset (Fin degree)) extends LiftData data wall anchors where
  /-- The old occurrence a selected new occurrence represents. -/
  selectedRep : Fin degree → data.SourceEdge
  selectedRep_survives : ∀ sheet : Fin degree, IsSelected data wall anchors sheet →
    ¬ IsDangling data (selectedRep sheet)
  /-- Selected sheets carrying the same new occurrence carry the same
  representative. -/
  selectedRep_congr : ∀ first second : Fin degree,
    IsSelected data wall anchors first → IsSelected data wall anchors second →
      candidate.newSourceEdge first = candidate.newSourceEdge second →
        selectedRep first = selectedRep second
  /-- A surviving selected new occurrence lies in its representative's row. -/
  selected_new_stablePath : ∀ (sheet : Fin degree), IsSelected data wall anchors sheet →
    ∀ (hSurvives : ¬ IsDangling candidate.datum (candidate.newSourceEdge sheet))
      (hRep : ¬ IsDangling candidate.datum (candidate.oldSourceEdge (selectedRep sheet))),
      NonDanglingEdge.stablePath
          (⟨candidate.newSourceEdge sheet, hSurvives⟩ : NonDanglingEdge candidate.datum) =
        NonDanglingEdge.stablePath
          (⟨candidate.oldSourceEdge (selectedRep sheet), hRep⟩ :
            NonDanglingEdge candidate.datum)
  /-- A selected retained endpoint of surviving valency two carries exactly
  one new occurrence and one incoming survivor, the latter in the
  representative's **incoming** row.  The core asks for the representative
  itself; `{w2-r1-nd2}` cannot supply that, only a partner sharing its row. -/
  selected_left_pair : ∀ sheet : Fin degree, IsSelected data wall anchors sheet →
    nonDanglingValency candidate.datum
        (candidate.datum.sourceEndpoint (oldVertex target wall) sheet) = 2 →
    ∃ (other : Fin degree) (old : data.SourceEdge)
      (hOther : IsSelected data wall anchors other) (hOld : ¬ IsDangling data old),
      nonDanglingIncident candidate.datum
          (candidate.datum.sourceEndpoint (oldVertex target wall) sheet) =
        {candidate.newSourceEdge other, candidate.oldSourceEdge old} ∧
      NonDanglingEdge.stablePath (⟨old, hOld⟩ : NonDanglingEdge data) =
        NonDanglingEdge.stablePath
          (⟨selectedRep other, selectedRep_survives other hOther⟩ : NonDanglingEdge data)
  /-- The same at a selected fresh endpoint. -/
  selected_right_pair : ∀ sheet : Fin degree, IsSelected data wall anchors sheet →
    nonDanglingValency candidate.datum
        (candidate.datum.sourceEndpoint (freshVertex target) sheet) = 2 →
    ∃ (other : Fin degree) (old : data.SourceEdge)
      (hOther : IsSelected data wall anchors other) (hOld : ¬ IsDangling data old),
      nonDanglingIncident candidate.datum
          (candidate.datum.sourceEndpoint (freshVertex target) sheet) =
        {candidate.newSourceEdge other, candidate.oldSourceEdge old} ∧
      NonDanglingEdge.stablePath (⟨old, hOld⟩ : NonDanglingEdge data) =
        NonDanglingEdge.stablePath
          (⟨selectedRep other, selectedRep_survives other hOther⟩ : NonDanglingEdge data)

namespace SelectedData

variable (rd : SelectedData data wall anchors)

/-- **The core's selected data is the singleton-anchor instance.** -/
def ofOneBlock (rd : LimitChainCore.SelectedData data wall) :
    SelectedData data wall {rd.selected} where
  toLiftData := LiftData.ofOneBlock rd.toLiftData
  selectedRep := rd.selectedRep
  selectedRep_survives := fun sheet hSheet ↦
    rd.selectedRep_survives sheet ((isSelected_singleton _ _).mp hSheet)
  selectedRep_congr := fun first second hFirst hSecond ↦
    rd.selectedRep_congr first second ((isSelected_singleton _ _).mp hFirst)
      ((isSelected_singleton _ _).mp hSecond)
  selected_new_stablePath := fun sheet hSheet ↦
    rd.selected_new_stablePath sheet ((isSelected_singleton _ _).mp hSheet)
  selected_left_pair := by
    intro sheet hSheet hValency
    obtain ⟨other, hOther, hStar⟩ :=
      rd.selected_left_pair sheet ((isSelected_singleton _ _).mp hSheet) hValency
    exact ⟨other, rd.selectedRep other, (isSelected_singleton _ _).mpr hOther,
      rd.selectedRep_survives other hOther, hStar, rfl⟩
  selected_right_pair := by
    intro sheet hSheet hValency
    obtain ⟨other, hOther, hStar⟩ :=
      rd.selected_right_pair sheet ((isSelected_singleton _ _).mp hSheet) hValency
    exact ⟨other, rd.selectedRep other, (isSelected_singleton _ _).mpr hOther,
      rd.selectedRep_survives other hOther, hStar, rfl⟩

@[simp] theorem ofOneBlock_candidate (rd : LimitChainCore.SelectedData data wall) :
    (ofOneBlock rd).candidate = rd.candidate := rfl

/-- The member's retained occurrences survive. -/
theorem retainedRep_survives {sheet : Fin degree}
    (hSheet : IsSelected data wall anchors sheet) :
    ¬ IsDangling rd.candidate.datum
      (rd.candidate.oldSourceEdge (rd.selectedRep sheet)) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge rd.candidate rd.valid.1 _
    (rd.selectedRep_survives sheet hSheet)

/-! ### The old occurrence represented by a surviving new occurrence -/

/-- Above a distinguished block the member's new occurrence represents
`selectedRep`; away from all of them, the background direction's own
occurrence through the same sheet. -/
noncomputable def newOldSourceEdge (sheet : Fin degree) : data.SourceEdge :=
  if IsSelected data wall anchors sheet then rd.selectedRep sheet
  else data.sourceEdge rd.retainedTarget sheet

theorem newOldSourceEdge_selected {sheet : Fin degree}
    (hSheet : IsSelected data wall anchors sheet) :
    rd.newOldSourceEdge sheet = rd.selectedRep sheet := ite_eq_left hSheet

theorem newOldSourceEdge_background {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet) :
    rd.newOldSourceEdge sheet = data.sourceEdge rd.retainedTarget sheet := ite_eq_right hSheet

/-- **The representative map agrees with the core's at a singleton anchor.** -/
theorem newOldSourceEdge_ofOneBlock (rd : LimitChainCore.SelectedData data wall)
    (sheet : Fin degree) :
    (ofOneBlock rd).newOldSourceEdge sheet = rd.newOldSourceEdge sheet := by
  by_cases hSel : (data.vertexPartition wall).Rel rd.selected sheet
  · rw [newOldSourceEdge_selected _ ((isSelected_singleton _ _).mpr hSel),
      rd.newOldSourceEdge_selected hSel]
    rfl
  · rw [newOldSourceEdge_background _
      (fun h ↦ hSel ((isSelected_singleton _ _).mp h)),
      rd.newOldSourceEdge_background hSel]
    rfl

theorem newOldSourceEdge_survives (sheet : Fin degree)
    (hSurvives : ¬ IsDangling rd.candidate.datum
      (rd.candidate.newSourceEdge sheet)) :
    ¬ IsDangling data (rd.newOldSourceEdge sheet) := by
  by_cases hSelected : IsSelected data wall anchors sheet
  · rw [rd.newOldSourceEdge_selected hSelected]
    exact rd.selectedRep_survives sheet hSelected
  · rw [rd.newOldSourceEdge_background hSelected]
    intro hDangling
    exact hSurvives ((rd.new_isDangling_iff rd.valid hSelected).mpr hDangling)

/-- The surviving incoming occurrence a surviving new occurrence represents. -/
noncomputable def newOldEdge (sheet : Fin degree)
    (hSurvives : ¬ IsDangling rd.candidate.datum
      (rd.candidate.newSourceEdge sheet)) : NonDanglingEdge data :=
  ⟨rd.newOldSourceEdge sheet, rd.newOldSourceEdge_survives sheet hSurvives⟩

/-- **Every surviving new occurrence lies in its representative's outgoing
row.** -/
theorem new_stablePath_eq_retained (sheet : Fin degree)
    (hSurvives : ¬ IsDangling rd.candidate.datum
      (rd.candidate.newSourceEdge sheet)) :
    NonDanglingEdge.stablePath
        (⟨rd.candidate.newSourceEdge sheet, hSurvives⟩ :
          NonDanglingEdge rd.candidate.datum) =
      (retainedEdge rd.candidate rd.valid.1
        (rd.newOldEdge sheet hSurvives)).stablePath := by
  by_cases hSelected : IsSelected data wall anchors sheet
  · refine Eq.trans (rd.selected_new_stablePath sheet hSelected hSurvives
      (rd.retainedRep_survives hSelected)) ?_
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext
      (congrArg rd.candidate.oldSourceEdge
        (rd.newOldSourceEdge_selected hSelected).symm))
  · have hOldSurvives : ¬ IsDangling data
        (data.sourceEdge rd.retainedTarget sheet) := by
      rw [← rd.newOldSourceEdge_background hSelected]
      exact rd.newOldSourceEdge_survives sheet hSurvives
    refine Eq.trans (rd.new_stablePath_eq rd.valid hSelected hOldSurvives) ?_
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext
      (congrArg rd.candidate.oldSourceEdge
        (rd.newOldSourceEdge_background hSelected).symm))

/-! ### Surjectivity of the induced row map -/

/-- Every surviving occurrence of a member lies on the outgoing row of an
actual retained incoming survivor. -/
theorem exists_retained_row (edge : NonDanglingEdge rd.candidate.datum) :
    ∃ old : NonDanglingEdge data,
      (retainedEdge rd.candidate rd.valid.1 old).stablePath = edge.stablePath := by
  rcases nonDanglingEdge_cases rd.candidate rd.valid rd.genus_eq edge
    with ⟨old, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · exact ⟨old, rfl⟩
  · exact ⟨rd.newOldEdge sheet hSurvives,
      (rd.new_stablePath_eq_retained sheet hSurvives).symm⟩

theorem stablePathLift_surjective : Function.Surjective rd.stablePathLift := by
  intro path
  induction path using Quot.inductionOn with
  | h edge =>
      obtain ⟨old, hPath⟩ := rd.exists_retained_row edge
      exact ⟨old.stablePath, hPath⟩

/-! ### The explicit reverse row assignment -/

/-- Two new occurrences that agree have the same representative. -/
theorem newOldSourceEdge_congr {first second : Fin degree}
    (hEq : rd.candidate.newSourceEdge first = rd.candidate.newSourceEdge second) :
    rd.newOldSourceEdge first = rd.newOldSourceEdge second := by
  have hRefines : (data.edgePartition rd.retainedTarget).Refines
      (data.vertexPartition wall) :=
    refines_of_mem_incidentEdges data rd.target_mem
  by_cases hFirst : IsSelected data wall anchors first
  · by_cases hSecond : IsSelected data wall anchors second
    · rw [rd.newOldSourceEdge_selected hFirst, rd.newOldSourceEdge_selected hSecond]
      exact rd.selectedRep_congr first second hFirst hSecond hEq
    · exfalso
      have hRel := (Background.newSourceEdge_eq_iff rd.toBackgroundShape hSecond).mp hEq.symm
      exact hSecond (isSelected_trans hFirst (hRefines.rel hRel).symm)
  · by_cases hSecond : IsSelected data wall anchors second
    · exfalso
      have hRel := (Background.newSourceEdge_eq_iff rd.toBackgroundShape hFirst).mp hEq
      exact hFirst (isSelected_trans hSecond (hRefines.rel hRel).symm)
    · rw [rd.newOldSourceEdge_background hFirst, rd.newOldSourceEdge_background hSecond]
      exact (sourceEdge_eq_iff_rel data rd.retainedTarget first second).mpr
        ((Background.newSourceEdge_eq_iff rd.toBackgroundShape hFirst).mp hEq)

/-- A surviving occurrence that is not retained is an actual surviving new
occurrence. -/
theorem new_representation (edge : NonDanglingEdge rd.candidate.datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge rd.candidate rd.valid.1 old = edge) :
    ∃ (sheet : Fin degree) (hSurvives : ¬ IsDangling rd.candidate.datum
        (rd.candidate.newSourceEdge sheet)),
      edge = ⟨rd.candidate.newSourceEdge sheet, hSurvives⟩ := by
  rcases nonDanglingEdge_cases rd.candidate rd.valid rd.genus_eq edge
    with ⟨old, hOld⟩ | ⟨sheet, hSurvives, hNew⟩
  · exact (hNotOld ⟨old, hOld.symm⟩).elim
  · exact ⟨sheet, hSurvives, hNew⟩

noncomputable def newSheet (edge : NonDanglingEdge rd.candidate.datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge rd.candidate rd.valid.1 old = edge) : Fin degree :=
  (rd.new_representation edge hNotOld).choose

theorem newSheet_survives (edge : NonDanglingEdge rd.candidate.datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge rd.candidate rd.valid.1 old = edge) :
    ¬ IsDangling rd.candidate.datum
      (rd.candidate.newSourceEdge (rd.newSheet edge hNotOld)) :=
  (rd.new_representation edge hNotOld).choose_spec.choose

theorem newSheet_spec (edge : NonDanglingEdge rd.candidate.datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge rd.candidate rd.valid.1 old = edge) :
    edge = ⟨rd.candidate.newSourceEdge (rd.newSheet edge hNotOld),
      rd.newSheet_survives edge hNotOld⟩ :=
  (rd.new_representation edge hNotOld).choose_spec.choose_spec

/-- **The reverse row assignment.** -/
noncomputable def rowOfEdge (edge : NonDanglingEdge rd.candidate.datum) :
    StablePath data := by
  classical
  exact if hOld : ∃ old : NonDanglingEdge data,
      retainedEdge rd.candidate rd.valid.1 old = edge then
    (Classical.choose hOld).stablePath
  else
    (rd.newOldEdge (rd.newSheet edge hOld) (rd.newSheet_survives edge hOld)).stablePath

@[simp] theorem rowOfEdge_retained (old : NonDanglingEdge data) :
    rd.rowOfEdge (retainedEdge rd.candidate rd.valid.1 old) = old.stablePath := by
  classical
  have hOld : ∃ other : NonDanglingEdge data,
      retainedEdge rd.candidate rd.valid.1 other =
        retainedEdge rd.candidate rd.valid.1 old := ⟨old, rfl⟩
  rw [rowOfEdge, dite_eq_left hOld]
  exact congrArg NonDanglingEdge.stablePath
    (retainedEdge_injective rd.candidate rd.valid.1 (Classical.choose_spec hOld))

theorem new_not_retained (sheet : Fin degree)
    (hSurvives : ¬ IsDangling rd.candidate.datum (rd.candidate.newSourceEdge sheet)) :
    ¬ ∃ old : NonDanglingEdge data,
      retainedEdge rd.candidate rd.valid.1 old =
        ⟨rd.candidate.newSourceEdge sheet, hSurvives⟩ := by
  rintro ⟨old, hOld⟩
  exact rd.new_ne_old sheet old.1 (congrArg Subtype.val hOld).symm

theorem rowOfEdge_not_retained (edge : NonDanglingEdge rd.candidate.datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge rd.candidate rd.valid.1 old = edge) :
    rd.rowOfEdge edge =
      (rd.newOldEdge (rd.newSheet edge hNotOld)
        (rd.newSheet_survives edge hNotOld)).stablePath := by
  classical
  exact dite_eq_right hNotOld

theorem rowOfEdge_new (sheet : Fin degree)
    (hSurvives : ¬ IsDangling rd.candidate.datum (rd.candidate.newSourceEdge sheet)) :
    rd.rowOfEdge ⟨rd.candidate.newSourceEdge sheet, hSurvives⟩ =
      (rd.newOldEdge sheet hSurvives).stablePath := by
  classical
  have hNotOld := rd.new_not_retained sheet hSurvives
  refine Eq.trans (rd.rowOfEdge_not_retained _ hNotOld) ?_
  refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
  exact rd.newOldSourceEdge_congr
    (congrArg Subtype.val (rd.newSheet_spec _ hNotOld)).symm

/-- **The reverse assignment agrees with the core's at a singleton anchor.** -/
theorem rowOfEdge_ofOneBlock (rd : LimitChainCore.SelectedData data wall)
    (edge : NonDanglingEdge rd.candidate.datum) :
    (ofOneBlock rd).rowOfEdge edge = rd.rowOfEdge edge := by
  rcases nonDanglingEdge_cases rd.candidate rd.valid rd.genus_eq edge
    with ⟨old, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · exact ((ofOneBlock rd).rowOfEdge_retained old).trans
      (rd.rowOfEdge_retained old).symm
  · refine ((ofOneBlock rd).rowOfEdge_new sheet hSurvives).trans
      (Eq.trans ?_ (rd.rowOfEdge_new sheet hSurvives).symm)
    exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (newOldSourceEdge_ofOneBlock rd sheet))

/-! #### The reverse assignment at the two expanded endpoints -/

/-- At a selected endpoint of surviving valency two the reverse assignment is
constant: the new occurrence returns to its representative's row and the old
partner to its own, and the two rows agree by hypothesis. -/
theorem rowOfEdge_eq_selected_pair {vertex : rd.candidate.datum.SourceVertex}
    {other : Fin degree} {old : data.SourceEdge}
    (hOther : IsSelected data wall anchors other) (hOld : ¬ IsDangling data old)
    (hStar : nonDanglingIncident rd.candidate.datum vertex =
      {rd.candidate.newSourceEdge other, rd.candidate.oldSourceEdge old})
    (hRow : NonDanglingEdge.stablePath (⟨old, hOld⟩ : NonDanglingEdge data) =
      NonDanglingEdge.stablePath
        (⟨rd.selectedRep other, rd.selectedRep_survives other hOther⟩ :
          NonDanglingEdge data))
    (first second : NonDanglingEdge rd.candidate.datum)
    (hFirst : Incident rd.candidate.datum first.1 vertex)
    (hSecond : Incident rd.candidate.datum second.1 vertex) :
    rd.rowOfEdge first = rd.rowOfEdge second := by
  classical
  have key : ∀ edge : NonDanglingEdge rd.candidate.datum,
      Incident rd.candidate.datum edge.1 vertex →
      rd.rowOfEdge edge = NonDanglingEdge.stablePath
        (⟨rd.selectedRep other, rd.selectedRep_survives other hOther⟩ :
          NonDanglingEdge data) := by
    intro edge hIncident
    have hMem : edge.1 ∈ nonDanglingIncident rd.candidate.datum vertex :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hIncident⟩
    rw [hStar] at hMem
    rcases Finset.mem_insert.mp hMem with hNew | hOldEq
    · have hSurvives : ¬ IsDangling rd.candidate.datum
          (rd.candidate.newSourceEdge other) := by
        rw [← hNew]; exact edge.2
      rw [show edge = ⟨rd.candidate.newSourceEdge other, hSurvives⟩ from
        Subtype.ext hNew, rd.rowOfEdge_new]
      exact congrArg NonDanglingEdge.stablePath
        (Subtype.ext (rd.newOldSourceEdge_selected hOther))
    · rw [Finset.mem_singleton] at hOldEq
      refine Eq.trans (congrArg rd.rowOfEdge
        (show edge = retainedEdge rd.candidate rd.valid.1 ⟨old, hOld⟩ from
          Subtype.ext hOldEq)) ?_
      exact (rd.rowOfEdge_retained ⟨old, hOld⟩).trans hRow
  rw [key first hFirst, key second hSecond]

/-- At a background divalent endpoint of surviving valency two both
occurrences return to the background direction's own row. -/
theorem rowOfEdge_eq_left_background {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    (hValency : nonDanglingValency rd.candidate.datum
      (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) = 2)
    (first second : NonDanglingEdge rd.candidate.datum)
    (hFirst : Incident rd.candidate.datum first.1
      (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet))
    (hSecond : Incident rd.candidate.datum second.1
      (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) :
    rd.rowOfEdge first = rd.rowOfEdge second := by
  classical
  have hStar := Background.nonDanglingIncident_old_background rd.toBackgroundShape
    hSheet hValency
  have hOldMem : rd.candidate.oldSourceEdge
      (data.sourceEdge rd.retainedTarget sheet) ∈
      nonDanglingIncident rd.candidate.datum
        (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) := by
    rw [hStar]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hOldSurvives : ¬ IsDangling data
      (data.sourceEdge rd.retainedTarget sheet) := fun hDangling ↦
    ((mem_nonDanglingIncident _ _ _).mp hOldMem).1
      ((rd.old_isDangling_iff rd.valid _).mpr hDangling)
  have key : ∀ edge : NonDanglingEdge rd.candidate.datum,
      Incident rd.candidate.datum edge.1
        (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) →
      rd.rowOfEdge edge = NonDanglingEdge.stablePath
        (⟨data.sourceEdge rd.retainedTarget sheet, hOldSurvives⟩ :
          NonDanglingEdge data) := by
    intro edge hIncident
    have hMem : edge.1 ∈ nonDanglingIncident rd.candidate.datum
        (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hIncident⟩
    rw [hStar] at hMem
    rcases Finset.mem_insert.mp hMem with hNew | hOld
    · have hSurvives : ¬ IsDangling rd.candidate.datum
          (rd.candidate.newSourceEdge sheet) := by
        rw [← hNew]; exact edge.2
      rw [show edge = ⟨rd.candidate.newSourceEdge sheet, hSurvives⟩ from
        Subtype.ext hNew, rd.rowOfEdge_new]
      exact congrArg NonDanglingEdge.stablePath
        (Subtype.ext (rd.newOldSourceEdge_background hSheet))
    · rw [Finset.mem_singleton] at hOld
      exact Eq.trans (congrArg rd.rowOfEdge
        (show edge = retainedEdge rd.candidate rd.valid.1
            ⟨data.sourceEdge rd.retainedTarget sheet, hOldSurvives⟩ from
          Subtype.ext hOld)) (rd.rowOfEdge_retained _)
  rw [key first hFirst, key second hSecond]

/-- At a background trivalent endpoint of surviving valency two both
occurrences return to rows of incoming survivors at the same wall vertex. -/
theorem rowOfEdge_eq_right_background {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet)
    (hValency : nonDanglingValency rd.candidate.datum
      (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet) = 2)
    (first second : NonDanglingEdge rd.candidate.datum)
    (hFirst : Incident rd.candidate.datum first.1
      (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet))
    (hSecond : Incident rd.candidate.datum second.1
      (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet)) :
    rd.rowOfEdge first = rd.rowOfEdge second := by
  classical
  have hStar := Background.nonDanglingIncident_fresh_eq_image rd.toBackgroundShape
    rd.valid hSheet
  have hIncoming : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2 :=
    (Background.nonDanglingValency_fresh_eq rd.toBackgroundShape rd.valid hSheet).symm.trans
      hValency
  have key : ∀ edge : NonDanglingEdge rd.candidate.datum,
      Incident rd.candidate.datum edge.1
        (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet) →
      ∃ old : NonDanglingEdge data,
        Incident data old.1 (data.sourceEndpoint wall sheet) ∧
          rd.rowOfEdge edge = old.stablePath := by
    intro edge hIncident
    have hMem : edge.1 ∈ nonDanglingIncident rd.candidate.datum
        (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hIncident⟩
    rw [hStar] at hMem
    obtain ⟨old, hOldMem, hReplace⟩ := Finset.mem_image.mp hMem
    obtain ⟨hOldSurvives, hOldIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOldMem
    refine ⟨⟨old, hOldSurvives⟩, hOldIncident, ?_⟩
    by_cases hTarget : old.1.1 = rd.retainedTarget
    · have hNew : edge.1 = rd.candidate.newSourceEdge old.1.2 :=
        hReplace.symm.trans (Background.replace_of_target rd.toBackgroundShape hTarget)
      have hSurvives : ¬ IsDangling rd.candidate.datum
          (rd.candidate.newSourceEdge old.1.2) := by
        rw [← hNew]; exact edge.2
      have hOldBackground : ¬ IsSelected data wall anchors old.1.2 :=
        Background.background_of_incident hSheet hOldIncident
      rw [show edge = ⟨rd.candidate.newSourceEdge old.1.2, hSurvives⟩ from
        Subtype.ext hNew, rd.rowOfEdge_new]
      exact congrArg NonDanglingEdge.stablePath (Subtype.ext
        ((rd.newOldSourceEdge_background hOldBackground).trans
          (rd.sourceEdge_retained_self hTarget)))
    · have hOldEq : edge.1 = rd.candidate.oldSourceEdge old :=
        hReplace.symm.trans (Background.replace_of_target_ne rd.toBackgroundShape hTarget)
      exact Eq.trans (congrArg rd.rowOfEdge
        (show edge = retainedEdge rd.candidate rd.valid.1 ⟨old, hOldSurvives⟩
          from Subtype.ext hOldEq)) (rd.rowOfEdge_retained _)
  obtain ⟨oldFirst, hOldFirst, hRowFirst⟩ := key first hFirst
  obtain ⟨oldSecond, hOldSecond, hRowSecond⟩ := key second hSecond
  rw [hRowFirst, hRowSecond]
  by_cases hEqual : oldFirst = oldSecond
  · rw [hEqual]
  · exact stablePath_eq_of_consecutive ⟨hEqual, data.sourceEndpoint wall sheet,
      hOldFirst, hOldSecond, hIncoming⟩

/-- The reverse assignment is constant at every divalent endpoint above the
wall. -/
theorem rowOfEdge_eq_left (sheet : Fin degree)
    (hValency : nonDanglingValency rd.candidate.datum
      (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) = 2)
    (first second : NonDanglingEdge rd.candidate.datum)
    (hFirst : Incident rd.candidate.datum first.1
      (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet))
    (hSecond : Incident rd.candidate.datum second.1
      (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) :
    rd.rowOfEdge first = rd.rowOfEdge second := by
  by_cases hSelected : IsSelected data wall anchors sheet
  · obtain ⟨other, old, hOther, hOld, hStar, hRow⟩ :=
      rd.selected_left_pair sheet hSelected hValency
    exact rd.rowOfEdge_eq_selected_pair hOther hOld hStar hRow first second hFirst hSecond
  · exact rd.rowOfEdge_eq_left_background hSelected hValency first second hFirst hSecond

/-- The same at every trivalent endpoint above the wall. -/
theorem rowOfEdge_eq_right (sheet : Fin degree)
    (hValency : nonDanglingValency rd.candidate.datum
      (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet) = 2)
    (first second : NonDanglingEdge rd.candidate.datum)
    (hFirst : Incident rd.candidate.datum first.1
      (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet))
    (hSecond : Incident rd.candidate.datum second.1
      (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet)) :
    rd.rowOfEdge first = rd.rowOfEdge second := by
  by_cases hSelected : IsSelected data wall anchors sheet
  · obtain ⟨other, old, hOther, hOld, hStar, hRow⟩ :=
      rd.selected_right_pair sheet hSelected hValency
    exact rd.rowOfEdge_eq_selected_pair hOther hOld hStar hRow first second hFirst hSecond
  · exact rd.rowOfEdge_eq_right_background hSelected hValency first second hFirst hSecond

/-- Away from the expanded wall both survivors at a divalent vertex are
retained. -/
theorem rowOfEdge_eq_away (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall)
    (first second : NonDanglingEdge rd.candidate.datum)
    (hFirst : Incident rd.candidate.datum first.1 (retainedVertex rd.candidate vertex))
    (hSecond : Incident rd.candidate.datum second.1 (retainedVertex rd.candidate vertex))
    (hValency : nonDanglingValency rd.candidate.datum
      (retainedVertex rd.candidate vertex) = 2) :
    rd.rowOfEdge first = rd.rowOfEdge second := by
  classical
  rcases nonDanglingEdge_cases rd.candidate rd.valid rd.genus_eq first
    with ⟨oldFirst, rfl⟩ | ⟨sheetFirst, hFirstSurvives, rfl⟩
  · rcases nonDanglingEdge_cases rd.candidate rd.valid rd.genus_eq
      second with ⟨oldSecond, rfl⟩ | ⟨sheetSecond, hSecondSurvives, rfl⟩
    · refine Eq.trans (rd.rowOfEdge_retained oldFirst)
        (Eq.trans ?_ (rd.rowOfEdge_retained oldSecond).symm)
      by_cases hEqual : oldFirst = oldSecond
      · exact congrArg NonDanglingEdge.stablePath hEqual
      · exact stablePath_eq_of_consecutive ⟨hEqual, vertex,
          (incident_oldSourceEdge_iff rd.candidate vertex hAway oldFirst.1).mp hFirst,
          (incident_oldSourceEdge_iff rd.candidate vertex hAway oldSecond.1).mp hSecond,
          (nonDanglingValency_retainedVertex rd.candidate rd.valid
            rd.genus_eq vertex hAway).symm.trans hValency⟩
    · exact (not_incident_newSourceEdge rd.candidate vertex hAway sheetSecond hSecond).elim
  · exact (not_incident_newSourceEdge rd.candidate vertex hAway sheetFirst hFirst).elim

/-- **The reverse assignment is constant on every actual consecutive pair of
the member.** -/
theorem rowOfEdge_eq_of_consecutive
    (first second : NonDanglingEdge rd.candidate.datum)
    (hConsecutive : Consecutive rd.candidate.datum first second) :
    rd.rowOfEdge first = rd.rowOfEdge second := by
  obtain ⟨_, vertex, hFirst, hSecond, hValency⟩ := hConsecutive
  have hSelf : rd.candidate.datum.sourceEndpoint vertex.1.1 vertex.1.2 = vertex :=
    (rd.candidate.datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, rfl⟩
  cases hTarget : vertex.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        have hEndpoint : rd.candidate.datum.sourceEndpoint
            (oldVertex target wall) vertex.1.2 = vertex :=
          (congrArg (fun item ↦ rd.candidate.datum.sourceEndpoint item
            vertex.1.2) hTarget.symm).trans hSelf
        rw [← hEndpoint] at hFirst hSecond hValency
        exact rd.rowOfEdge_eq_left vertex.1.2 hValency first second hFirst hSecond
      · obtain ⟨old, hOld, hVertex⟩ := exists_retainedVertex_of_target
          rd.candidate vertex place hAt hTarget
        rw [← hVertex] at hFirst hSecond hValency
        exact rd.rowOfEdge_eq_away old (hOld ▸ hAt) first second hFirst hSecond hValency
  | inr point =>
      cases point
      have hEndpoint : rd.candidate.datum.sourceEndpoint
          (freshVertex target) vertex.1.2 = vertex :=
        (congrArg (fun item ↦ rd.candidate.datum.sourceEndpoint item
          vertex.1.2) hTarget.symm).trans hSelf
      rw [← hEndpoint] at hFirst hSecond hValency
      exact rd.rowOfEdge_eq_right vertex.1.2 hValency first second hFirst hSecond

/-! ### The occurrence-induced stable-row equivalence -/

/-- The reverse row assignment descends through the member's stable
quotient. -/
noncomputable def stablePathDescend :
    StablePath rd.candidate.datum → StablePath data :=
  Quot.lift rd.rowOfEdge rd.rowOfEdge_eq_of_consecutive

@[simp] theorem stablePathDescend_mk (edge : NonDanglingEdge rd.candidate.datum) :
    rd.stablePathDescend edge.stablePath = rd.rowOfEdge edge := rfl

/-- Descent is a literal left inverse of the retained-occurrence lift. -/
theorem stablePathDescend_lift (path : StablePath data) :
    rd.stablePathDescend (rd.stablePathLift path) = path := by
  induction path using Quot.inductionOn with
  | h edge => exact rd.rowOfEdge_retained edge

theorem stablePathLift_injective : Function.Injective rd.stablePathLift :=
  Function.LeftInverse.injective rd.stablePathDescend_lift

/-- **The occurrence-induced stable-row equivalence of a member.** -/
noncomputable def stablePathEquiv :
    StablePath data ≃ StablePath rd.candidate.datum :=
  Equiv.ofBijective rd.stablePathLift
    ⟨rd.stablePathLift_injective, rd.stablePathLift_surjective⟩

@[simp] theorem stablePathEquiv_mk (edge : NonDanglingEdge data) :
    rd.stablePathEquiv edge.stablePath =
      (retainedEdge rd.candidate rd.valid.1 edge).stablePath := rfl

/-- The inverse of the row equivalence is the explicit reverse assignment. -/
@[simp] theorem stablePathEquiv_symm_apply (path : StablePath rd.candidate.datum) :
    rd.stablePathEquiv.symm path = rd.stablePathDescend path := by
  obtain ⟨row, hRow⟩ := rd.stablePathLift_surjective path
  rw [← hRow, rd.stablePathDescend_lift]
  exact rd.stablePathEquiv.symm_apply_apply row

/-- **The row equivalence agrees with the core's at a singleton anchor.** -/
theorem stablePathEquiv_ofOneBlock (rd : LimitChainCore.SelectedData data wall)
    (path : StablePath data) :
    (ofOneBlock rd).stablePathEquiv path = rd.stablePathEquiv path := rfl

/-! ### The honest natural stable-length matrix: the retained columns -/

theorem occurrences_retained (path : StablePath data) (place : target.edges) :
    occurrences rd.candidate.datum (rd.stablePathEquiv path)
        (occurrenceEquiv target wall rd.candidate.right (some place)) =
      (occurrences data path place).image rd.candidate.oldSourceEdge := by
  classical
  ext edge
  constructor
  · intro hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases rd.candidate edge with
      ⟨old, rfl⟩ | ⟨sheet, rfl⟩
    · have hOld : ¬ IsDangling data old := fun hDangling ↦ hSurvives
        ((rd.old_isDangling_iff rd.valid old).mpr hDangling)
      refine Finset.mem_image.mpr ⟨old, (mem_occurrences _ _ _).mpr
        ⟨⟨hOld, ?_⟩, ?_⟩, rfl⟩
      · exact rd.stablePathEquiv.injective
          ((rd.stablePathEquiv_mk ⟨old, hOld⟩).trans hRow)
      · exact Option.some.inj ((occurrenceEquiv target wall
          rd.candidate.right).injective hTarget)
    · have hLabels := (occurrenceEquiv target wall rd.candidate.right).injective hTarget
      cases hLabels
  · intro hMem
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld
    refine (mem_occurrences _ _ _).mpr
      ⟨⟨ResolutionSurvival.not_isDangling_oldSourceEdge rd.candidate
        rd.valid.1 old hSurvives, ?_⟩, ?_⟩
    · exact (rd.stablePathEquiv_mk ⟨old, hSurvives⟩).symm.trans
        (congrArg rd.stablePathEquiv hRow)
    · exact congrArg (fun label ↦ occurrenceEquiv target wall
        rd.candidate.right (some label)) hTarget

/-- **Every retained column of a member is the incoming wall column.** -/
theorem matrix_retained (path : StablePath data) (place : target.edges) :
    matrix rd.candidate.datum (rd.stablePathEquiv path)
        (occurrenceEquiv target wall rd.candidate.right (some place)) =
      matrix data path place := by
  classical
  unfold matrix
  rw [rd.occurrences_retained, Finset.sum_image]
  · exact Finset.sum_congr rfl fun edge _ ↦ by
      rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]
  · intro first _ second _ hEqual
    exact ResolutionCut.oldSourceEdge_injective _ hEqual

/-- The regrown column is supported on the surviving new occurrences. -/
theorem mem_occurrences_new_iff (path : StablePath data)
    (edge : rd.candidate.datum.SourceEdge) :
    edge ∈ occurrences rd.candidate.datum (rd.stablePathEquiv path)
        (occurrenceEquiv target wall rd.candidate.right none) ↔
      ∃ (sheet : Fin degree) (hSurvives : ¬ IsDangling rd.candidate.datum
          (rd.candidate.newSourceEdge sheet)),
        edge = rd.candidate.newSourceEdge sheet ∧
          (rd.newOldEdge sheet hSurvives).stablePath = path := by
  classical
  rw [mem_occurrences]
  constructor
  · rintro ⟨⟨hSurvives, hRow⟩, hTarget⟩
    rcases ResolutionPruning.sourceEdge_cases rd.candidate edge with
      ⟨old, rfl⟩ | ⟨sheet, rfl⟩
    · have hLabels := (occurrenceEquiv target wall rd.candidate.right).injective hTarget
      exact absurd hLabels (by simp)
    · refine ⟨sheet, hSurvives, rfl, rd.stablePathEquiv.injective ?_⟩
      rw [rd.stablePathEquiv_mk]
      exact (rd.new_stablePath_eq_retained sheet hSurvives).symm.trans hRow
  · rintro ⟨sheet, hSurvives, rfl, hRow⟩
    refine ⟨⟨hSurvives, ?_⟩, rfl⟩
    rw [← hRow, rd.stablePathEquiv_mk]
    exact rd.new_stablePath_eq_retained sheet hSurvives

/-! ### Incidence counts away from the distinguished blocks -/

/-- **Away from the wall retention preserves every incidence count.** -/
theorem incidenceCount_retained (vertex : data.SourceVertex)
    (hAway : vertex.1.1 ≠ wall) (path : StablePath data) :
    incidenceCount data vertex path =
      incidenceCount rd.candidate.datum
        (retainedVertex rd.candidate vertex) (rd.stablePathLift path) := by
  classical
  refine Finset.card_bij (fun edge _ ↦ retainedEdge rd.candidate rd.valid.1 edge) ?_ ?_ ?_
  · intro edge hEdge
    rw [Finset.mem_filter, mem_incidentEdges] at hEdge ⊢
    exact ⟨(incident_oldSourceEdge_iff rd.candidate vertex hAway edge.1).mpr hEdge.1,
      (rd.stablePathLift_mk edge).symm.trans
        (congrArg rd.stablePathLift hEdge.2)⟩
  · intro first _ second _ hEqual
    exact retainedEdge_injective rd.candidate rd.valid.1 hEqual
  · intro edge hEdge
    rw [Finset.mem_filter, mem_incidentEdges] at hEdge
    rcases nonDanglingEdge_cases rd.candidate rd.valid rd.genus_eq edge
      with ⟨old, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
    · refine ⟨old, ?_, rfl⟩
      rw [Finset.mem_filter, mem_incidentEdges]
      refine ⟨(incident_oldSourceEdge_iff rd.candidate vertex hAway old.1).mp hEdge.1, ?_⟩
      exact rd.stablePathLift_injective ((rd.stablePathLift_mk old).trans hEdge.2)
    · exact absurd hEdge.1 (not_incident_newSourceEdge rd.candidate vertex hAway sheet)

/-- **At a background wall vertex the replacement bijection preserves every
incidence count.** -/
theorem incidenceCount_background {sheet : Fin degree}
    (hSheet : ¬ IsSelected data wall anchors sheet) (path : StablePath data) :
    incidenceCount data (data.sourceEndpoint wall sheet) path =
      incidenceCount rd.candidate.datum
        (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet)
        (rd.stablePathLift path) := by
  classical
  refine Finset.card_bij
    (fun edge hEdge ↦ (⟨Background.replace rd.toBackgroundShape edge.1,
      Background.replace_survives rd.toBackgroundShape rd.valid hSheet edge.2
        ((mem_incidentEdges data _ edge).mp (Finset.mem_filter.mp hEdge).1)⟩ :
      NonDanglingEdge rd.candidate.datum)) ?_ ?_ ?_
  · intro edge hEdge
    have hIncident := (mem_incidentEdges data _ edge).mp (Finset.mem_filter.mp hEdge).1
    exact Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr
        (Background.replace_incident rd.toBackgroundShape hSheet hIncident),
      (rd.replace_stablePath hSheet edge.2 hIncident _).trans
        (congrArg rd.stablePathLift (Finset.mem_filter.mp hEdge).2)⟩
  · intro first hFirst second hSecond hEqual
    have hFirstMem : first.1 ∈ nonDanglingIncident data
        (data.sourceEndpoint wall sheet) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨first.2,
        (mem_incidentEdges data _ first).mp (Finset.mem_filter.mp hFirst).1⟩
    have hSecondMem : second.1 ∈ nonDanglingIncident data
        (data.sourceEndpoint wall sheet) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨second.2,
        (mem_incidentEdges data _ second).mp (Finset.mem_filter.mp hSecond).1⟩
    exact Subtype.ext (Background.replace_injOn rd.toBackgroundShape hSheet
      (Finset.mem_coe.mpr hFirstMem) (Finset.mem_coe.mpr hSecondMem)
      (congrArg Subtype.val hEqual))
  · intro edge hEdge
    have hIncident := (mem_incidentEdges _ _ edge).mp (Finset.mem_filter.mp hEdge).1
    have hMem : edge.1 ∈ nonDanglingIncident rd.candidate.datum
        (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hIncident⟩
    rw [Background.nonDanglingIncident_fresh_eq_image rd.toBackgroundShape rd.valid
      hSheet] at hMem
    obtain ⟨old, hOldMem, hReplace⟩ := Finset.mem_image.mp hMem
    obtain ⟨hOldSurvives, hOldIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOldMem
    refine ⟨⟨old, hOldSurvives⟩, ?_, Subtype.ext hReplace⟩
    refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hOldIncident,
      rd.stablePathLift_injective ?_⟩
    refine Eq.trans (rd.replace_stablePath hSheet hOldSurvives hOldIncident
      (Background.replace_survives rd.toBackgroundShape rd.valid hSheet hOldSurvives
        hOldIncident)).symm ?_
    exact Eq.trans (congrArg NonDanglingEdge.stablePath
      (Subtype.ext hReplace : (⟨Background.replace rd.toBackgroundShape old,
        Background.replace_survives rd.toBackgroundShape rd.valid hSheet hOldSurvives
          hOldIncident⟩ :
        NonDanglingEdge rd.candidate.datum) = edge))
      (Finset.mem_filter.mp hEdge).2

end SelectedData

/-! ## §6  The stable incidence graph at a set of anchors

`GraphData` carries one `selectedSide` and one `selectedFlag` **per anchor**,
and `branchImage` is a bijection onto the **union** of the branch stars.  Two
fields pay for the union:

* `anchors_sep`, that the anchors name distinct wall blocks -- without it
  `anchorOf` is not determined and two `selectedSide`s could disagree on one
  block; and
* `branch_ne`, that distinct anchors have distinct branch vertices.

`branch_ne` is **free** when the anchors sit on opposite sides of the new
edge (`branch_ne_of_side_ne`), which is exactly the `{w2-r1}` configuration:
`W2R1StableGraph.branch_side_ne` says the two branch vertices of a member lie
on opposite sides.  It is a genuine hypothesis only for two anchors on the
same side, where the census would have to say that the member does not fuse
the two blocks' endpoints there. -/

/-- Two expanded endpoints on opposite sides of the new edge are distinct. -/
theorem sourceEndpoint_side_ne (candidate : BalancedGlobal.Candidate target degree data wall)
    {first second : Bool} (hSide : first ≠ second) (i j : Fin degree) :
    candidate.datum.sourceEndpoint (wallSide target wall first) i ≠
      candidate.datum.sourceEndpoint (wallSide target wall second) j := by
  intro hEqual
  have hTarget : wallSide target wall first = wallSide target wall second :=
    congrArg (fun item : candidate.datum.SourceVertex ↦ item.1.1) hEqual
  cases first
  · cases second
    · exact hSide rfl
    · rw [wallSide_false, wallSide_true] at hTarget
      simp only [oldVertex, freshVertex] at hTarget
      exact absurd hTarget (by simp)
  · cases second
    · rw [wallSide_true, wallSide_false] at hTarget
      simp only [oldVertex, freshVertex] at hTarget
      exact absurd hTarget (by simp)
    · exact hSide rfl

/-- **Anchors on opposite sides of the new edge need no separation
hypothesis.** -/
theorem branch_ne_of_side_ne (candidate : BalancedGlobal.Candidate target degree data wall)
    (anchors : Finset (Fin degree)) (selectedSide : Fin degree → Bool)
    (hSide : ∀ first ∈ anchors, ∀ second ∈ anchors, first ≠ second →
      selectedSide first ≠ selectedSide second) :
    ∀ first ∈ anchors, ∀ second ∈ anchors, first ≠ second →
      candidate.datum.sourceEndpoint (wallSide target wall (selectedSide first)) first ≠
        candidate.datum.sourceEndpoint (wallSide target wall (selectedSide second)) second :=
  fun first hFirst second hSecond hNe ↦
    sourceEndpoint_side_ne candidate (hSide first hFirst second hSecond hNe) first second

/-- The anchor whose wall block a selected sheet lies in. -/
noncomputable def anchorOf (data : GluingDatum target degree) (wall : target.V)
    (anchors : Finset (Fin degree)) (sheet : Fin degree) : Fin degree :=
  if h : IsSelected data wall anchors sheet then h.choose else sheet

theorem anchorOf_mem {sheet : Fin degree} (h : IsSelected data wall anchors sheet) :
    anchorOf data wall anchors sheet ∈ anchors := by
  unfold anchorOf
  rw [dite_eq_left h]
  exact h.choose_spec.1

theorem anchorOf_rel {sheet : Fin degree} (h : IsSelected data wall anchors sheet) :
    (data.vertexPartition wall).Rel (anchorOf data wall anchors sheet) sheet := by
  unfold anchorOf
  rw [dite_eq_left h]
  exact h.choose_spec.2

theorem anchorOf_eq {anchor sheet : Fin degree}
    (hSep : ∀ first ∈ anchors, ∀ second ∈ anchors,
      (data.vertexPartition wall).Rel first second → first = second)
    (hMem : anchor ∈ anchors)
    (hRel : (data.vertexPartition wall).Rel anchor sheet) :
    anchorOf data wall anchors sheet = anchor :=
  hSep _ (anchorOf_mem (isSelected_of_rel hMem hRel)) anchor hMem
    ((anchorOf_rel (isSelected_of_rel hMem hRel)).trans hRel.symm)

/-- A member together with the flag dictionary at **each** of its branch
vertices above the distinguished blocks. -/
structure GraphData (data : GluingDatum target degree) (wall : target.V)
    (anchors : Finset (Fin degree)) extends SelectedData data wall anchors where
  /-- The anchors name distinct wall blocks. -/
  anchors_sep : ∀ first ∈ anchors, ∀ second ∈ anchors,
    (data.vertexPartition wall).Rel first second → first = second
  /-- Which expanded endpoint above each distinguished block is the member's
  branch vertex there: `false` the retained one, `true` the fresh one. -/
  selectedSide : Fin degree → Bool
  /-- The flag correspondence at each branch vertex. -/
  selectedFlag : Fin degree → data.SourceEdge → candidate.datum.SourceEdge
  selectedFlag_star : ∀ anchor ∈ anchors,
    nonDanglingIncident candidate.datum
        (candidate.datum.sourceEndpoint (wallSide target wall (selectedSide anchor)) anchor) =
      (nonDanglingIncident data (data.sourceEndpoint wall anchor)).image (selectedFlag anchor)
  selectedFlag_injOn : ∀ anchor ∈ anchors, Set.InjOn (selectedFlag anchor)
    ↑(nonDanglingIncident data (data.sourceEndpoint wall anchor))
  /-- Every other endpoint above a distinguished block is divalent or entirely
  pruned. -/
  selected_not_branch : ∀ anchor ∈ anchors, ∀ (side : Bool) (sheet : Fin degree),
    (data.vertexPartition wall).Rel anchor sheet →
    candidate.datum.sourceEndpoint (wallSide target wall side) sheet ≠
      candidate.datum.sourceEndpoint (wallSide target wall (selectedSide anchor)) anchor →
    nonDanglingValency candidate.datum
      (candidate.datum.sourceEndpoint (wallSide target wall side) sheet) ≤ 2
  selectedFlag_row : ∀ anchor ∈ anchors, ∀ (edge : data.SourceEdge)
    (hSurvives : ¬ IsDangling data edge),
    Incident data edge (data.sourceEndpoint wall anchor) →
    ∀ hFlag : ¬ IsDangling candidate.datum (selectedFlag anchor edge),
      NonDanglingEdge.stablePath (⟨selectedFlag anchor edge, hFlag⟩ :
          NonDanglingEdge candidate.datum) =
        (retainedEdge candidate valid.1 ⟨edge, hSurvives⟩).stablePath
  /-- Distinct anchors have distinct branch vertices. -/
  branch_ne : ∀ first ∈ anchors, ∀ second ∈ anchors, first ≠ second →
    candidate.datum.sourceEndpoint (wallSide target wall (selectedSide first)) first ≠
      candidate.datum.sourceEndpoint (wallSide target wall (selectedSide second)) second

namespace GraphData

variable (rd : GraphData data wall anchors)

/-- The member's branch vertex above one distinguished block. -/
noncomputable def branchVertex (anchor : Fin degree) : rd.candidate.datum.SourceVertex :=
  rd.candidate.datum.sourceEndpoint (wallSide target wall (rd.selectedSide anchor)) anchor

theorem branchVertex_star {anchor : Fin degree} (hMem : anchor ∈ anchors) :
    nonDanglingIncident rd.candidate.datum (rd.branchVertex anchor) =
      (nonDanglingIncident data (data.sourceEndpoint wall anchor)).image
        (rd.selectedFlag anchor) :=
  rd.selectedFlag_star anchor hMem

theorem selectedFlag_survives {anchor : Fin degree} (hMem : anchor ∈ anchors)
    {edge : data.SourceEdge}
    (hStar : edge ∈ nonDanglingIncident data (data.sourceEndpoint wall anchor)) :
    ¬ IsDangling rd.candidate.datum (rd.selectedFlag anchor edge) := by
  have hImage : rd.selectedFlag anchor edge ∈
      nonDanglingIncident rd.candidate.datum (rd.branchVertex anchor) := by
    rw [rd.branchVertex_star hMem]
    exact Finset.mem_image_of_mem _ hStar
  exact ((mem_nonDanglingIncident _ _ _).mp hImage).1

theorem selectedFlag_incident {anchor : Fin degree} (hMem : anchor ∈ anchors)
    {edge : data.SourceEdge}
    (hStar : edge ∈ nonDanglingIncident data (data.sourceEndpoint wall anchor)) :
    Incident rd.candidate.datum (rd.selectedFlag anchor edge) (rd.branchVertex anchor) := by
  have hImage : rd.selectedFlag anchor edge ∈
      nonDanglingIncident rd.candidate.datum (rd.branchVertex anchor) := by
    rw [rd.branchVertex_star hMem]
    exact Finset.mem_image_of_mem _ hStar
  exact ((mem_nonDanglingIncident _ _ _).mp hImage).2

/-- **At each distinguished wall vertex the branch flag preserves every
incidence count.** -/
theorem incidenceCount_selected {anchor : Fin degree} (hMem : anchor ∈ anchors)
    (path : StablePath data) :
    incidenceCount data (data.sourceEndpoint wall anchor) path =
      incidenceCount rd.candidate.datum (rd.branchVertex anchor)
        (rd.stablePathLift path) := by
  classical
  refine Finset.card_bij (fun edge hEdge ↦ (⟨rd.selectedFlag anchor edge.1,
    rd.selectedFlag_survives hMem ((mem_nonDanglingIncident _ _ _).mpr ⟨edge.2,
      (mem_incidentEdges data _ edge).mp (Finset.mem_filter.mp hEdge).1⟩)⟩ :
    NonDanglingEdge rd.candidate.datum)) ?_ ?_ ?_
  · intro edge hEdge
    have hIncident := (mem_incidentEdges data _ edge).mp (Finset.mem_filter.mp hEdge).1
    have hStar : edge.1 ∈ nonDanglingIncident data (data.sourceEndpoint wall anchor) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hIncident⟩
    exact Finset.mem_filter.mpr
      ⟨(mem_incidentEdges _ _ _).mpr (rd.selectedFlag_incident hMem hStar),
        (rd.selectedFlag_row anchor hMem edge.1 edge.2 hIncident _).trans
          ((rd.stablePathLift_mk edge).symm.trans
            (congrArg rd.stablePathLift (Finset.mem_filter.mp hEdge).2))⟩
  · intro first hFirst second hSecond hEqual
    have hFirstMem : first.1 ∈ nonDanglingIncident data
        (data.sourceEndpoint wall anchor) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨first.2,
        (mem_incidentEdges data _ first).mp (Finset.mem_filter.mp hFirst).1⟩
    have hSecondMem : second.1 ∈ nonDanglingIncident data
        (data.sourceEndpoint wall anchor) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨second.2,
        (mem_incidentEdges data _ second).mp (Finset.mem_filter.mp hSecond).1⟩
    exact Subtype.ext (rd.selectedFlag_injOn anchor hMem (Finset.mem_coe.mpr hFirstMem)
      (Finset.mem_coe.mpr hSecondMem) (congrArg Subtype.val hEqual))
  · intro edge hEdge
    have hMemStar : edge.1 ∈ nonDanglingIncident rd.candidate.datum
        (rd.branchVertex anchor) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2,
        (mem_incidentEdges _ _ edge).mp (Finset.mem_filter.mp hEdge).1⟩
    rw [rd.branchVertex_star hMem] at hMemStar
    obtain ⟨old, hOldMem, hFlag⟩ := Finset.mem_image.mp hMemStar
    obtain ⟨hOldSurvives, hOldIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOldMem
    refine ⟨⟨old, hOldSurvives⟩, ?_, Subtype.ext hFlag⟩
    refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hOldIncident,
      rd.stablePathLift_injective ?_⟩
    refine Eq.trans (rd.stablePathLift_mk ⟨old, hOldSurvives⟩) ?_
    refine Eq.trans (rd.selectedFlag_row anchor hMem old hOldSurvives hOldIncident
      (rd.selectedFlag_survives hMem hOldMem)).symm ?_
    exact Eq.trans (congrArg NonDanglingEdge.stablePath
      (Subtype.ext hFlag : (⟨rd.selectedFlag anchor old,
        rd.selectedFlag_survives hMem hOldMem⟩ :
        NonDanglingEdge rd.candidate.datum) = edge))
      (Finset.mem_filter.mp hEdge).2

/-! ### The branch-vertex correspondence -/

/-- The member vertex a source vertex becomes. -/
noncomputable def branchImage (vertex : data.SourceVertex) :
    rd.candidate.datum.SourceVertex := by
  classical
  exact if vertex.1.1 = wall then
      (if IsSelected data wall anchors vertex.1.2 then
        rd.branchVertex (anchorOf data wall anchors vertex.1.2)
      else rd.candidate.datum.sourceEndpoint (freshVertex target) vertex.1.2)
    else retainedVertex rd.candidate vertex

theorem branchImage_away {vertex : data.SourceVertex} (hAway : vertex.1.1 ≠ wall) :
    rd.branchImage vertex = retainedVertex rd.candidate vertex := by
  classical
  exact ite_eq_right hAway

theorem branchImage_anchorOf {vertex : data.SourceVertex} (hAt : vertex.1.1 = wall)
    (hSelected : IsSelected data wall anchors vertex.1.2) :
    rd.branchImage vertex = rd.branchVertex (anchorOf data wall anchors vertex.1.2) := by
  classical
  exact (ite_eq_left hAt).trans (ite_eq_left hSelected)

theorem branchImage_selected {vertex : data.SourceVertex} (hAt : vertex.1.1 = wall)
    {anchor : Fin degree} (hMem : anchor ∈ anchors)
    (hRel : (data.vertexPartition wall).Rel anchor vertex.1.2) :
    rd.branchImage vertex = rd.branchVertex anchor := by
  rw [rd.branchImage_anchorOf hAt (isSelected_of_rel hMem hRel),
    anchorOf_eq rd.anchors_sep hMem hRel]

theorem branchImage_background {vertex : data.SourceVertex} (hAt : vertex.1.1 = wall)
    (hBackground : ¬ IsSelected data wall anchors vertex.1.2) :
    rd.branchImage vertex =
      rd.candidate.datum.sourceEndpoint (freshVertex target) vertex.1.2 := by
  classical
  exact (ite_eq_left hAt).trans (ite_eq_right hBackground)

/-- Each branch vertex has the incoming distinguished valency. -/
theorem nonDanglingValency_branchVertex {anchor : Fin degree} (hMem : anchor ∈ anchors) :
    nonDanglingValency rd.candidate.datum (rd.branchVertex anchor) =
      nonDanglingValency data (data.sourceEndpoint wall anchor) := by
  classical
  rw [← card_nonDanglingIncident, ← card_nonDanglingIncident, rd.branchVertex_star hMem,
    Finset.card_image_of_injOn (rd.selectedFlag_injOn anchor hMem)]

/-- **Surviving valency is preserved.** -/
theorem nonDanglingValency_branchImage (vertex : data.SourceVertex) :
    nonDanglingValency rd.candidate.datum (rd.branchImage vertex) =
      nonDanglingValency data vertex := by
  classical
  by_cases hAt : vertex.1.1 = wall
  · have hVertex : data.sourceEndpoint wall vertex.1.2 = vertex :=
      (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr ⟨hAt.symm, rfl⟩
    by_cases hSelected : IsSelected data wall anchors vertex.1.2
    · have hMem := anchorOf_mem hSelected
      have hRel := anchorOf_rel hSelected
      have hAnchor : data.sourceEndpoint wall
          (anchorOf data wall anchors vertex.1.2) = vertex :=
        (sourceEndpoint_eq_of_rel data wall hRel).trans hVertex
      exact Eq.trans (congrArg (nonDanglingValency rd.candidate.datum)
          (rd.branchImage_anchorOf hAt hSelected))
        ((rd.nonDanglingValency_branchVertex hMem).trans
          (congrArg (nonDanglingValency data) hAnchor))
    · exact Eq.trans (congrArg (nonDanglingValency rd.candidate.datum)
          (rd.branchImage_background hAt hSelected))
        ((Background.nonDanglingValency_fresh_eq rd.toBackgroundShape rd.valid
          hSelected).trans (congrArg (nonDanglingValency data) hVertex))
  · exact Eq.trans (congrArg (nonDanglingValency rd.candidate.datum)
      (rd.branchImage_away hAt))
      (nonDanglingValency_retainedVertex rd.candidate rd.valid rd.genus_eq vertex hAt)

/-- **Every incidence count is preserved.** -/
theorem incidenceCount_branchImage (vertex : data.SourceVertex) (path : StablePath data) :
    incidenceCount data vertex path =
      incidenceCount rd.candidate.datum (rd.branchImage vertex) (rd.stablePathLift path) := by
  classical
  by_cases hAt : vertex.1.1 = wall
  · have hVertex : data.sourceEndpoint wall vertex.1.2 = vertex :=
      (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr ⟨hAt.symm, rfl⟩
    by_cases hSelected : IsSelected data wall anchors vertex.1.2
    · have hMem := anchorOf_mem hSelected
      have hAnchor : data.sourceEndpoint wall
          (anchorOf data wall anchors vertex.1.2) = vertex :=
        (sourceEndpoint_eq_of_rel data wall (anchorOf_rel hSelected)).trans hVertex
      refine Eq.trans ?_ (congrArg (fun item ↦ incidenceCount
        rd.candidate.datum item (rd.stablePathLift path))
        (rd.branchImage_anchorOf hAt hSelected)).symm
      exact (congrArg (fun item ↦ incidenceCount data item path) hAnchor).symm.trans
        (rd.incidenceCount_selected hMem path)
    · refine Eq.trans ?_ (congrArg (fun item ↦ incidenceCount
        rd.candidate.datum item (rd.stablePathLift path))
        (rd.branchImage_background hAt hSelected)).symm
      exact (congrArg (fun item ↦ incidenceCount data item path) hVertex).symm.trans
        (rd.incidenceCount_background hSelected path)
  · refine Eq.trans ?_ (congrArg (fun item ↦ incidenceCount
      rd.candidate.datum item (rd.stablePathLift path))
      (rd.branchImage_away hAt)).symm
    exact rd.incidenceCount_retained vertex hAt path

/-! #### The branch map is a bijection -/

theorem branchVertex_ne_background {anchor sheet : Fin degree} (hMem : anchor ∈ anchors)
    (hSheet : ¬ IsSelected data wall anchors sheet) :
    rd.candidate.datum.sourceEndpoint (freshVertex target) sheet ≠
      rd.branchVertex anchor := by
  intro hEqual
  cases hSide : rd.selectedSide anchor with
  | false =>
      have hTarget : freshVertex target = wallSide target wall (rd.selectedSide anchor) :=
        congrArg (fun item : rd.candidate.datum.SourceVertex ↦ item.1.1) hEqual
      rw [hSide] at hTarget
      simp only [wallSide_false, freshVertex, oldVertex] at hTarget
      exact absurd hTarget (by simp)
  | true =>
      have hBranch : rd.branchVertex anchor = rd.candidate.datum.sourceEndpoint
          (wallSide target wall (rd.selectedSide anchor)) anchor := rfl
      rw [hSide, wallSide_true] at hBranch
      have hRel : rd.pasted.right.Rel sheet anchor :=
        congrArg (fun item : rd.candidate.datum.SourceVertex ↦ item.1.2)
          (hEqual.trans hBranch)
      have hBlock : anchor ∈ rd.pasted.right.block sheet :=
        (rd.pasted.right.mem_block_iff _ _).mpr hRel
      rw [rd.pasted_right_block hSheet] at hBlock
      exact hSheet (isSelected_of_rel hMem
        (((data.vertexPartition wall).mem_block_iff _ _).mp hBlock).symm)

theorem branchVertex_ne_retained {vertex : data.SourceVertex} (hAway : vertex.1.1 ≠ wall)
    (anchor : Fin degree) :
    retainedVertex rd.candidate vertex ≠ rd.branchVertex anchor := by
  intro hEqual
  have hTarget : oldVertex target vertex.1.1 =
      wallSide target wall (rd.selectedSide anchor) :=
    congrArg (fun item : rd.candidate.datum.SourceVertex ↦ item.1.1) hEqual
  cases hSide : rd.selectedSide anchor with
  | false =>
      rw [hSide] at hTarget
      simp only [wallSide_false, oldVertex] at hTarget
      exact hAway (by simpa using hTarget)
  | true =>
      rw [hSide] at hTarget
      simp only [wallSide_true, oldVertex, freshVertex] at hTarget
      exact absurd hTarget (by simp)

theorem retained_ne_fresh {vertex : data.SourceVertex} (sheet : Fin degree) :
    retainedVertex rd.candidate vertex ≠
      rd.candidate.datum.sourceEndpoint (freshVertex target) sheet := by
  intro hEqual
  have hTarget : oldVertex target vertex.1.1 = freshVertex target :=
    congrArg (fun item : rd.candidate.datum.SourceVertex ↦ item.1.1) hEqual
  simp only [oldVertex, freshVertex] at hTarget
  exact absurd hTarget (by simp)

theorem branchImage_injective : Function.Injective rd.branchImage := by
  classical
  intro first second hEqual
  by_cases hFirstAt : first.1.1 = wall
  · by_cases hSecondAt : second.1.1 = wall
    · have hFirstRepr : (data.vertexPartition wall).repr first.1.2 = first.1.2 := by
        have := first.2
        rw [hFirstAt] at this
        exact this
      have hSecondRepr : (data.vertexPartition wall).repr second.1.2 = second.1.2 := by
        have := second.2
        rw [hSecondAt] at this
        exact this
      by_cases hFirstSel : IsSelected data wall anchors first.1.2
      · by_cases hSecondSel : IsSelected data wall anchors second.1.2
        · have hAnchors : anchorOf data wall anchors first.1.2 =
              anchorOf data wall anchors second.1.2 := by
            by_contra hNe
            exact rd.branch_ne _ (anchorOf_mem hFirstSel) _ (anchorOf_mem hSecondSel) hNe
              ((rd.branchImage_anchorOf hFirstAt hFirstSel).symm.trans
                (hEqual.trans (rd.branchImage_anchorOf hSecondAt hSecondSel)))
          have hRel : (data.vertexPartition wall).Rel first.1.2 second.1.2 :=
            (anchorOf_rel hFirstSel).symm.trans (hAnchors ▸ anchorOf_rel hSecondSel)
          exact Subtype.ext (Prod.ext (hFirstAt.trans hSecondAt.symm)
            (hFirstRepr.symm.trans (hRel.trans hSecondRepr)))
        · exact absurd ((rd.branchImage_background hSecondAt hSecondSel).symm.trans
            (hEqual.symm.trans (rd.branchImage_anchorOf hFirstAt hFirstSel)))
            (rd.branchVertex_ne_background (anchorOf_mem hFirstSel) hSecondSel)
      · by_cases hSecondSel : IsSelected data wall anchors second.1.2
        · exact absurd ((rd.branchImage_background hFirstAt hFirstSel).symm.trans
            (hEqual.trans (rd.branchImage_anchorOf hSecondAt hSecondSel)))
            (rd.branchVertex_ne_background (anchorOf_mem hSecondSel) hFirstSel)
        · have hFresh := (rd.branchImage_background hFirstAt hFirstSel).symm.trans
            (hEqual.trans (rd.branchImage_background hSecondAt hSecondSel))
          have hRel : rd.pasted.right.Rel first.1.2 second.1.2 :=
            congrArg (fun item : rd.candidate.datum.SourceVertex ↦ item.1.2) hFresh
          have hBlock : second.1.2 ∈ rd.pasted.right.block first.1.2 :=
            (rd.pasted.right.mem_block_iff _ _).mpr hRel
          rw [rd.pasted_right_block hFirstSel] at hBlock
          have hWall := ((data.vertexPartition wall).mem_block_iff _ _).mp hBlock
          exact Subtype.ext (Prod.ext (hFirstAt.trans hSecondAt.symm)
            (hFirstRepr.symm.trans (hWall.trans hSecondRepr)))
    · by_cases hFirstSel : IsSelected data wall anchors first.1.2
      · exact absurd ((rd.branchImage_away hSecondAt).symm.trans
          (hEqual.symm.trans (rd.branchImage_anchorOf hFirstAt hFirstSel)))
          (rd.branchVertex_ne_retained hSecondAt _)
      · exact absurd ((rd.branchImage_away hSecondAt).symm.trans
          (hEqual.symm.trans (rd.branchImage_background hFirstAt hFirstSel)))
          (rd.retained_ne_fresh first.1.2)
  · by_cases hSecondAt : second.1.1 = wall
    · by_cases hSecondSel : IsSelected data wall anchors second.1.2
      · exact absurd ((rd.branchImage_away hFirstAt).symm.trans
          (hEqual.trans (rd.branchImage_anchorOf hSecondAt hSecondSel)))
          (rd.branchVertex_ne_retained hFirstAt _)
      · exact absurd ((rd.branchImage_away hFirstAt).symm.trans
          (hEqual.trans (rd.branchImage_background hSecondAt hSecondSel)))
          (rd.retained_ne_fresh second.1.2)
    · have hRetained := (rd.branchImage_away hFirstAt).symm.trans
        (hEqual.trans (rd.branchImage_away hSecondAt))
      have hTarget : oldVertex target first.1.1 = oldVertex target second.1.1 :=
        congrArg (fun item : rd.candidate.datum.SourceVertex ↦ item.1.1) hRetained
      have hPlace : first.1.1 = second.1.1 := by
        simpa only [oldVertex, Sum.inl.injEq] using hTarget
      have hSheet : first.1.2 = second.1.2 := by
        have hFirstSheet := retainedVertex_sheet rd.candidate first hFirstAt
        have hSecondSheet := retainedVertex_sheet rd.candidate second hSecondAt
        exact hFirstSheet.symm.trans
          ((congrArg (fun item : rd.candidate.datum.SourceVertex ↦ item.1.2)
            hRetained).trans hSecondSheet)
      exact Subtype.ext (Prod.ext hPlace hSheet)

/-- **Every surviving branch vertex of the member is hit.** -/
theorem exists_branchImage (w : rd.candidate.datum.SourceVertex)
    (hBranch : 3 ≤ nonDanglingValency rd.candidate.datum w) :
    ∃ vertex : data.SourceVertex, rd.branchImage vertex = w := by
  classical
  have hSelf : rd.candidate.datum.sourceEndpoint w.1.1 w.1.2 = w :=
    (rd.candidate.datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, rfl⟩
  cases hTarget : w.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        have hEndpoint : rd.candidate.datum.sourceEndpoint
            (oldVertex target wall) w.1.2 = w :=
          (congrArg (fun item ↦ rd.candidate.datum.sourceEndpoint item w.1.2)
            hTarget.symm).trans hSelf
        by_cases hSel : IsSelected data wall anchors w.1.2
        · set anchor := anchorOf data wall anchors w.1.2 with hAnchorDef
          have hMem : anchor ∈ anchors := anchorOf_mem hSel
          have hRel : (data.vertexPartition wall).Rel anchor w.1.2 := anchorOf_rel hSel
          by_cases hIsBranch : rd.candidate.datum.sourceEndpoint
              (wallSide target wall false) w.1.2 = rd.branchVertex anchor
          · refine ⟨data.sourceEndpoint wall anchor, ?_⟩
            refine (rd.branchImage_selected rfl hMem
              ((data.vertexPartition wall).rel_repr_right _)).trans ?_
            simp only [wallSide_false] at hIsBranch
            exact hIsBranch.symm.trans hEndpoint
          · exfalso
            have hLe := rd.selected_not_branch anchor hMem false w.1.2 hRel hIsBranch
            simp only [wallSide_false] at hLe
            rw [hEndpoint] at hLe
            omega
        · exfalso
          have hLe : nonDanglingValency rd.candidate.datum
              (rd.candidate.datum.sourceEndpoint (oldVertex target wall) w.1.2) ≤ 2 := by
            rw [← card_nonDanglingIncident]
            exact (Finset.card_le_card (rd.nonDanglingIncident_old_subset hSel)).trans
              (le_of_eq (Finset.card_pair (rd.new_ne_old _ _)))
          rw [hEndpoint] at hLe
          omega
      · obtain ⟨old, hOld, hVertex⟩ := exists_retainedVertex_of_target
          rd.candidate w place hAt hTarget
        exact ⟨old, (rd.branchImage_away (hOld ▸ hAt)).trans hVertex⟩
  | inr point =>
      cases point
      have hEndpoint : rd.candidate.datum.sourceEndpoint (freshVertex target) w.1.2 = w :=
        (congrArg (fun item ↦ rd.candidate.datum.sourceEndpoint item w.1.2)
          hTarget.symm).trans hSelf
      by_cases hSel : IsSelected data wall anchors w.1.2
      · set anchor := anchorOf data wall anchors w.1.2 with hAnchorDef
        have hMem : anchor ∈ anchors := anchorOf_mem hSel
        have hRel : (data.vertexPartition wall).Rel anchor w.1.2 := anchorOf_rel hSel
        by_cases hIsBranch : rd.candidate.datum.sourceEndpoint
            (wallSide target wall true) w.1.2 = rd.branchVertex anchor
        · refine ⟨data.sourceEndpoint wall anchor, ?_⟩
          refine (rd.branchImage_selected rfl hMem
            ((data.vertexPartition wall).rel_repr_right _)).trans ?_
          simp only [wallSide_true] at hIsBranch
          exact hIsBranch.symm.trans hEndpoint
        · exfalso
          have hLe := rd.selected_not_branch anchor hMem true w.1.2 hRel hIsBranch
          simp only [wallSide_true] at hLe
          rw [hEndpoint] at hLe
          omega
      · refine ⟨data.sourceEndpoint wall w.1.2, ?_⟩
        have hBg : ¬ IsSelected data wall anchors
            ((data.vertexPartition wall).repr w.1.2) :=
          fun hRel ↦ hSel (isSelected_trans hRel
            ((data.vertexPartition wall).rel_repr_left w.1.2))
        refine (rd.branchImage_background rfl hBg).trans ?_
        exact (Background.fresh_endpoint_eq rd.toBackgroundShape hBg
          ((data.vertexPartition wall).rel_repr_left w.1.2)).trans hEndpoint

/-- **The bijection of surviving branch vertices.** -/
noncomputable def branchVertexEquiv :
    StableGraphIncidence.BranchVertex data ≃
      StableGraphIncidence.BranchVertex rd.candidate.datum :=
  Equiv.ofBijective
    (fun vertex ↦ (⟨rd.branchImage vertex.1, by
      rw [rd.nonDanglingValency_branchImage]
      exact vertex.2⟩ :
      StableGraphIncidence.BranchVertex rd.candidate.datum))
    ⟨by
      intro first second hEqual
      exact Subtype.ext (rd.branchImage_injective (congrArg Subtype.val hEqual)),
      by
      intro w
      obtain ⟨vertex, hVertex⟩ := rd.exists_branchImage w.1 w.2
      refine ⟨⟨vertex, ?_⟩, Subtype.ext hVertex⟩
      rw [← rd.nonDanglingValency_branchImage vertex, hVertex]
      exact w.2⟩

@[simp] theorem branchVertexEquiv_apply (vertex : StableGraphIncidence.BranchVertex data) :
    (rd.branchVertexEquiv vertex).1 = rd.branchImage vertex.1 := rfl

/-- **The stable incidence graph of the member is the incoming one**, with the
branch correspondence built on the union of the branch stars. -/
noncomputable def equivalence :
    StableGraphIncidence.Equivalence data rd.candidate.datum where
  vertex := rd.branchVertexEquiv
  row := rd.stablePathEquiv
  incidence := fun vertex path ↦ rd.incidenceCount_branchImage vertex.1 path

@[simp] theorem equivalence_row (path : StablePath data) :
    rd.equivalence.row path = rd.stablePathEquiv path := rfl

/-- Path ends transport, since the incoming source is connected. -/
theorem hasPathEnds (hEnds : HasPathEnds data) : HasPathEnds rd.candidate.datum :=
  rd.equivalence.hasPathEnds rd.valid.1 hEnds

end GraphData

/-! ### The one-block core as the singleton-anchor graph data -/

namespace GraphData

/-- **The core's graph data is the singleton-anchor instance.** -/
def ofOneBlock (rd : LimitChainCore.GraphData data wall) :
    GraphData data wall {rd.selected} where
  toSelectedData := SelectedData.ofOneBlock rd.toSelectedData
  anchors_sep := by
    intro first hFirst second hSecond _
    rw [Finset.mem_singleton.mp hFirst, Finset.mem_singleton.mp hSecond]
  selectedSide := fun _ ↦ rd.selectedSide
  selectedFlag := fun _ ↦ rd.selectedFlag
  selectedFlag_star := by
    intro anchor hAnchor
    rw [Finset.mem_singleton.mp hAnchor]
    exact rd.selectedFlag_star
  selectedFlag_injOn := by
    intro anchor hAnchor
    rw [Finset.mem_singleton.mp hAnchor]
    exact rd.selectedFlag_injOn
  selected_not_branch := by
    intro anchor hAnchor side sheet hRel hNe
    rw [Finset.mem_singleton.mp hAnchor] at hRel hNe
    exact rd.selected_not_branch side sheet hRel hNe
  selectedFlag_row := by
    intro anchor hAnchor edge hSurvives hIncident hFlag
    rw [Finset.mem_singleton.mp hAnchor] at hIncident
    exact rd.selectedFlag_row edge hSurvives hIncident hFlag
  branch_ne := by
    intro first hFirst second hSecond hNe
    exact absurd ((Finset.mem_singleton.mp hFirst).trans
      (Finset.mem_singleton.mp hSecond).symm) hNe

@[simp] theorem ofOneBlock_candidate (rd : LimitChainCore.GraphData data wall) :
    (ofOneBlock rd).candidate = rd.candidate := rfl

/-- **The branch map agrees with the core's at a singleton anchor.** -/
theorem branchImage_ofOneBlock (rd : LimitChainCore.GraphData data wall)
    (vertex : data.SourceVertex) :
    (ofOneBlock rd).branchImage vertex = rd.branchImage vertex := by
  classical
  by_cases hAt : vertex.1.1 = wall
  · by_cases hSel : (data.vertexPartition wall).Rel rd.selected vertex.1.2
    · rw [(ofOneBlock rd).branchImage_selected hAt (Finset.mem_singleton_self _) hSel,
        rd.branchImage_selected hAt hSel]
      rfl
    · rw [(ofOneBlock rd).branchImage_background hAt
        (fun h ↦ hSel ((isSelected_singleton _ _).mp h)),
        rd.branchImage_background hAt hSel]
      rfl
  · rw [(ofOneBlock rd).branchImage_away hAt, rd.branchImage_away hAt]
    rfl

/-- **The row half of the stable-incidence equivalence agrees with the
core's.** -/
theorem equivalence_row_ofOneBlock (rd : LimitChainCore.GraphData data wall)
    (path : StablePath data) :
    (ofOneBlock rd).equivalence.row path = rd.equivalence.row path := rfl

/-- **and so does the branch half.** -/
theorem equivalence_vertex_ofOneBlock (rd : LimitChainCore.GraphData data wall)
    (vertex : StableGraphIncidence.BranchVertex data) :
    ((ofOneBlock rd).equivalence.vertex vertex).1 = (rd.equivalence.vertex vertex).1 :=
  branchImage_ofOneBlock rd vertex.1

end GraphData

/-! ## §7  The regrown column at a set of anchors

`matrix_new_split` splits the regrown column into the **union** of the
distinguished blocks' regrown halves and one background `s`;
`matrix_new_split_pair` splits that union again for two separated anchors,
which is the shape of Equation (10) of Draisma--Vargas Part I (Case
`{w2-r1}`): `c⁽ⁱ⁾ = σ⁽ⁱ⁾(J_{A₀},1) +
σ⁽ⁱ⁾(J_{B₀},1) + s`. -/

namespace SelectedData

variable (rd : SelectedData data wall anchors)

/-- The sheets a member regrows onto one stable row. -/
def RegrownAt (path : StablePath data) (sheet : Fin degree) : Prop :=
  ∃ hSurvives : ¬ IsDangling rd.candidate.datum (rd.candidate.newSourceEdge sheet),
    (rd.newOldEdge sheet hSurvives).stablePath = path

/-- **The support of the regrown column, enumerated.** -/
theorem occurrences_new_eq (path : StablePath data) (sheets : List (Fin degree))
    (hMem : ∀ sheet ∈ sheets, RegrownAt rd path sheet)
    (hExhaustive : ∀ sheet : Fin degree, RegrownAt rd path sheet →
      rd.candidate.newSourceEdge sheet ∈ sheets.map rd.candidate.newSourceEdge) :
    occurrences rd.candidate.datum (rd.stablePathEquiv path)
        (occurrenceEquiv target wall rd.candidate.right none) =
      (sheets.map rd.candidate.newSourceEdge).toFinset := by
  classical
  ext item
  rw [rd.mem_occurrences_new_iff path item, List.mem_toFinset]
  constructor
  · rintro ⟨sheet, hSurvives, rfl, hRow⟩
    exact hExhaustive sheet ⟨hSurvives, hRow⟩
  · intro hItem
    obtain ⟨sheet, hSheet, rfl⟩ := List.mem_map.mp hItem
    obtain ⟨hSurvives, hRow⟩ := hMem sheet hSheet
    exact ⟨sheet, hSurvives, rfl, hRow⟩

/-- **The regrown column of a member, evaluated as a list.** -/
theorem matrix_new (path : StablePath data) (sheets : List (Fin degree))
    (hMem : ∀ sheet ∈ sheets, RegrownAt rd path sheet)
    (hExhaustive : ∀ sheet : Fin degree, RegrownAt rd path sheet →
      rd.candidate.newSourceEdge sheet ∈ sheets.map rd.candidate.newSourceEdge)
    (hNodup : (sheets.map rd.candidate.newSourceEdge).Nodup) :
    matrix rd.candidate.datum (rd.stablePathEquiv path)
        (occurrenceEquiv target wall rd.candidate.right none) =
      (sheets.map fun sheet ↦ (1 : ℚ) /
        rd.candidate.datum.sourceEdgeIndex (rd.candidate.newSourceEdge sheet)).sum := by
  classical
  unfold matrix
  rw [occurrences_new_eq rd path sheets hMem hExhaustive,
    List.sum_toFinset _ hNodup, List.map_map]
  rfl

/-! ### The `Finset` route -/

/-- The regrown column's occurrence set of the member, read in the incoming
row. -/
noncomputable def newOccurrences (path : StablePath data) :
    Finset rd.candidate.datum.SourceEdge :=
  occurrences rd.candidate.datum (rd.stablePathEquiv path)
    (occurrenceEquiv target wall rd.candidate.right none)

theorem mem_newOccurrences (path : StablePath data) (edge : rd.candidate.datum.SourceEdge) :
    edge ∈ rd.newOccurrences path ↔
      ∃ (sheet : Fin degree) (hSurvives : ¬ IsDangling rd.candidate.datum
          (rd.candidate.newSourceEdge sheet)),
        edge = rd.candidate.newSourceEdge sheet ∧
          (rd.newOldEdge sheet hSurvives).stablePath = path :=
  rd.mem_occurrences_new_iff path edge

/-- A new occurrence's canonical sheet lies in the wall block of the sheet
naming it. -/
theorem newSourceEdge_sheet_rel_iff (anchor sheet : Fin degree) :
    (data.vertexPartition wall).Rel anchor (rd.candidate.newSourceEdge sheet).1.2 ↔
      (data.vertexPartition wall).Rel anchor sheet := by
  rw [BalancedGlobal.Candidate.newSourceEdge_sheet]
  have hRefines : (pasted rd.candidate).right.Refines (data.vertexPartition wall) :=
    SheetPartition.IsJoin.right_refines (LocalResolution.paste_contracts
      (data.vertexPartition wall) rd.candidate.resolution rd.candidate.contracts)
  have hRel : (data.vertexPartition wall).Rel sheet
      ((pasted rd.candidate).newEdge.repr sheet) :=
    hRefines.rel ((pasted rd.candidate).edge_refines_right.rel
      ((pasted rd.candidate).newEdge.rel_repr_right sheet))
  exact ⟨fun h ↦ h.trans hRel.symm, fun h ↦ h.trans hRel⟩

theorem newSourceEdge_sheet_isSelected_iff (sheet : Fin degree) :
    IsSelected data wall anchors (rd.candidate.newSourceEdge sheet).1.2 ↔
      IsSelected data wall anchors sheet := by
  constructor
  · rintro ⟨anchor, hMem, hRel⟩
    exact ⟨anchor, hMem, (rd.newSourceEdge_sheet_rel_iff anchor sheet).mp hRel⟩
  · rintro ⟨anchor, hMem, hRel⟩
    exact ⟨anchor, hMem, (rd.newSourceEdge_sheet_rel_iff anchor sheet).mpr hRel⟩

theorem eq_newSourceEdge_of_mem (path : StablePath data)
    (edge : rd.candidate.datum.SourceEdge) (hMem : edge ∈ rd.newOccurrences path) :
    edge = rd.candidate.newSourceEdge edge.1.2 :=
  M11SplitRows.eq_newSourceEdge_of_target rd.candidate edge
    ((mem_occurrences _ _ _).mp hMem).2

/-- A surviving selected new occurrence sits in the regrown column exactly in
its representative's row. -/
theorem new_mem_iff_of_survives (sheet : Fin degree)
    (hRel : IsSelected data wall anchors sheet)
    (hSurvives : ¬ IsDangling rd.candidate.datum (rd.candidate.newSourceEdge sheet))
    (path : StablePath data) :
    rd.candidate.newSourceEdge sheet ∈ rd.newOccurrences path ↔
      path = NonDanglingEdge.stablePath
        (⟨rd.selectedRep sheet, rd.selectedRep_survives sheet hRel⟩ :
          NonDanglingEdge data) := by
  rw [rd.mem_newOccurrences]
  constructor
  · rintro ⟨other, hOther, hEqual, hRow⟩
    rw [← hRow]
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext
      ((rd.newOldSourceEdge_congr hEqual.symm).trans (rd.newOldSourceEdge_selected hRel)))
  · intro hPath
    refine ⟨sheet, hSurvives, rfl, ?_⟩
    rw [hPath]
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext (rd.newOldSourceEdge_selected hRel))

theorem new_not_mem_of_dangling (sheet : Fin degree)
    (hDangling : IsDangling rd.candidate.datum (rd.candidate.newSourceEdge sheet))
    (path : StablePath data) :
    rd.candidate.newSourceEdge sheet ∉ rd.newOccurrences path := by
  rw [newOccurrences, mem_occurrences]
  rintro ⟨⟨h, _⟩, _⟩
  exact h hDangling

end SelectedData

/-- The occurrences of one old wall column outside **every** distinguished
block: the background, whose cofactor-weighted sum is the `s` of every limit
box. -/
noncomputable def backgroundOccurrences (data : GluingDatum target degree) (wall : target.V)
    (anchors : Finset (Fin degree)) (path : StablePath data) (place : target.edges) :
    Finset data.SourceEdge :=
  (occurrences data path place).filter (fun edge ↦ ¬ IsSelected data wall anchors edge.1.2)

theorem mem_backgroundOccurrences (data : GluingDatum target degree) (wall : target.V)
    (anchors : Finset (Fin degree)) (path : StablePath data) (place : target.edges)
    (edge : data.SourceEdge) :
    edge ∈ backgroundOccurrences data wall anchors path place ↔
      edge ∈ occurrences data path place ∧ ¬ IsSelected data wall anchors edge.1.2 := by
  simp only [backgroundOccurrences, Finset.mem_filter]

/-- The background `s`, read on one old wall column and one old stable row. -/
noncomputable def backgroundColumn (data : GluingDatum target degree) (wall : target.V)
    (anchors : Finset (Fin degree)) (path : StablePath data) (place : target.edges) : ℚ :=
  ∑ edge ∈ backgroundOccurrences data wall anchors path place,
    (1 : ℚ) / data.sourceEdgeIndex edge

/-- **The background at a singleton anchor is the core's.** -/
theorem backgroundOccurrences_singleton (data : GluingDatum target degree) (wall : target.V)
    (anchor : Fin degree) (path : StablePath data) (place : target.edges) :
    backgroundOccurrences data wall {anchor} path place =
      LimitChainCore.backgroundOccurrences data wall anchor path place := by
  classical
  ext edge
  rw [mem_backgroundOccurrences, LimitChainCore.mem_backgroundOccurrences]
  exact and_congr_right fun _ ↦ not_congr (isSelected_singleton _ _)

theorem backgroundColumn_singleton (data : GluingDatum target degree) (wall : target.V)
    (anchor : Fin degree) (path : StablePath data) (place : target.edges) :
    backgroundColumn data wall {anchor} path place =
      LimitChainCore.backgroundColumn data wall anchor path place := by
  unfold backgroundColumn LimitChainCore.backgroundColumn
  rw [backgroundOccurrences_singleton]

namespace SelectedData

variable (rd : SelectedData data wall anchors)

/-- **The background half of the regrown column is the retained direction's
own background.** -/
theorem background_sum (path : StablePath data) :
    ∑ edge ∈ (rd.newOccurrences path).filter
        (fun edge ↦ ¬ IsSelected data wall anchors edge.1.2),
      (1 : ℚ) / rd.candidate.datum.sourceEdgeIndex edge =
    backgroundColumn data wall anchors path rd.retainedTarget := by
  classical
  symm
  unfold backgroundColumn
  refine Finset.sum_bij (fun edge _ ↦ rd.candidate.newSourceEdge edge.1.2) ?_ ?_ ?_ ?_
  · intro edge hEdge
    obtain ⟨hOld, hBackground⟩ :=
      (mem_backgroundOccurrences data wall anchors path rd.retainedTarget edge).mp hEdge
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld
    have hSelf := rd.sourceEdge_retained_self hTarget
    have hNew : ¬ IsDangling rd.candidate.datum (rd.candidate.newSourceEdge edge.1.2) := by
      rw [rd.new_isDangling_iff rd.valid hBackground, hSelf]
      exact hSurvives
    refine Finset.mem_filter.mpr ⟨(rd.mem_newOccurrences path _).mpr
      ⟨edge.1.2, hNew, rfl, ?_⟩, ?_⟩
    · rw [← hRow]
      exact congrArg NonDanglingEdge.stablePath (Subtype.ext
        ((rd.newOldSourceEdge_background hBackground).trans hSelf))
    · exact fun h ↦ hBackground ((rd.newSourceEdge_sheet_isSelected_iff edge.1.2).mp h)
  · intro first hFirst second hSecond hEqual
    obtain ⟨hFirstOld, hFirstBackground⟩ :=
      (mem_backgroundOccurrences data wall anchors path rd.retainedTarget first).mp hFirst
    obtain ⟨hSecondOld, _⟩ :=
      (mem_backgroundOccurrences data wall anchors path rd.retainedTarget second).mp hSecond
    have hRel := (Background.newSourceEdge_eq_iff rd.toBackgroundShape hFirstBackground).mp hEqual
    have hSource := (sourceEdge_eq_iff_rel data rd.retainedTarget first.1.2 second.1.2).mpr hRel
    rwa [rd.sourceEdge_retained_self ((mem_occurrences _ _ _).mp hFirstOld).2,
      rd.sourceEdge_retained_self ((mem_occurrences _ _ _).mp hSecondOld).2] at hSource
  · intro edge hEdge
    obtain ⟨hMem, hBackground⟩ := Finset.mem_filter.mp hEdge
    obtain ⟨sheet, hSurvives, rfl, hRow⟩ := (rd.mem_newOccurrences path edge).mp hMem
    have hSheet : ¬ IsSelected data wall anchors sheet :=
      fun h ↦ hBackground ((rd.newSourceEdge_sheet_isSelected_iff sheet).mpr h)
    have hOldSurvives : ¬ IsDangling data (data.sourceEdge rd.retainedTarget sheet) := by
      rw [← rd.newOldSourceEdge_background hSheet]
      exact rd.newOldSourceEdge_survives sheet hSurvives
    have hRefines : (data.edgePartition rd.retainedTarget).Refines
        (data.vertexPartition wall) :=
      refines_of_mem_incidentEdges data rd.target_mem
    have hRepr : ¬ IsSelected data wall anchors
        (data.sourceEdge rd.retainedTarget sheet).1.2 := fun h ↦
      hSheet (isSelected_trans h (hRefines.rel
        ((data.edgePartition rd.retainedTarget).rel_repr_left sheet)))
    refine ⟨data.sourceEdge rd.retainedTarget sheet, ?_, ?_⟩
    · refine (mem_backgroundOccurrences data wall anchors path rd.retainedTarget _).mpr
        ⟨(mem_occurrences _ _ _).mpr ⟨⟨hOldSurvives, ?_⟩, rfl⟩, hRepr⟩
      rw [← hRow]
      exact congrArg NonDanglingEdge.stablePath (Subtype.ext
        (rd.newOldSourceEdge_background hSheet).symm)
    · exact Background.newSourceEdge_eq_of_edge_rel rd.toBackgroundShape hSheet
        ((data.edgePartition rd.retainedTarget).rel_repr_right sheet)
  · intro edge hEdge
    obtain ⟨hOld, hBackground⟩ :=
      (mem_backgroundOccurrences data wall anchors path rd.retainedTarget edge).mp hEdge
    rw [rd.newIndex_eq hBackground,
      rd.sourceEdge_retained_self ((mem_occurrences _ _ _).mp hOld).2]

/-- **The regrown column, split into its selected and background halves.** -/
theorem matrix_new_split (path : StablePath data) :
    matrix rd.candidate.datum (rd.stablePathEquiv path)
        (occurrenceEquiv target wall rd.candidate.right none) =
      (∑ edge ∈ (rd.newOccurrences path).filter
          (fun edge ↦ IsSelected data wall anchors edge.1.2),
        (1 : ℚ) / rd.candidate.datum.sourceEdgeIndex edge) +
        backgroundColumn data wall anchors path rd.retainedTarget := by
  classical
  rw [← rd.background_sum path]
  exact (Finset.sum_filter_add_sum_filter_not (rd.newOccurrences path)
    (fun edge ↦ IsSelected data wall anchors edge.1.2)
    (fun edge ↦ (1 : ℚ) / rd.candidate.datum.sourceEdgeIndex edge)).symm

/-- **Equation (10)'s shape**: with two separated anchors the regrown column
is the sum of the two blocks' regrown halves and one background `s`. -/
theorem matrix_new_split_pair (first second : Fin degree)
    (hAnchors : anchors = {first, second})
    (hSep : ¬ (data.vertexPartition wall).Rel first second)
    (path : StablePath data) :
    matrix rd.candidate.datum (rd.stablePathEquiv path)
        (occurrenceEquiv target wall rd.candidate.right none) =
      (∑ edge ∈ (rd.newOccurrences path).filter
          (fun edge ↦ (data.vertexPartition wall).Rel first edge.1.2),
        (1 : ℚ) / rd.candidate.datum.sourceEdgeIndex edge) +
      (∑ edge ∈ (rd.newOccurrences path).filter
          (fun edge ↦ (data.vertexPartition wall).Rel second edge.1.2),
        (1 : ℚ) / rd.candidate.datum.sourceEdgeIndex edge) +
      backgroundColumn data wall anchors path rd.retainedTarget := by
  classical
  have hUnion : (rd.newOccurrences path).filter
        (fun edge ↦ IsSelected data wall anchors edge.1.2) =
      ((rd.newOccurrences path).filter
          (fun edge ↦ (data.vertexPartition wall).Rel first edge.1.2)) ∪
        ((rd.newOccurrences path).filter
          (fun edge ↦ (data.vertexPartition wall).Rel second edge.1.2)) := by
    ext edge
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hMem, anchor, hAnchor, hRel⟩
      rw [hAnchors] at hAnchor
      rcases Finset.mem_insert.mp hAnchor with hEq | hEq
      · exact Or.inl ⟨hMem, hEq ▸ hRel⟩
      · exact Or.inr ⟨hMem, (Finset.mem_singleton.mp hEq) ▸ hRel⟩
    · rintro (⟨hMem, hRel⟩ | ⟨hMem, hRel⟩)
      · exact ⟨hMem, first, by rw [hAnchors]; exact Finset.mem_insert_self _ _, hRel⟩
      · exact ⟨hMem, second, by
          rw [hAnchors]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hRel⟩
  have hDisjoint : Disjoint
      ((rd.newOccurrences path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel first edge.1.2))
      ((rd.newOccurrences path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel second edge.1.2)) := by
    rw [Finset.disjoint_left]
    intro edge hFirst hSecond
    exact hSep (((Finset.mem_filter.mp hFirst).2).trans
      ((Finset.mem_filter.mp hSecond).2).symm)
  rw [rd.matrix_new_split path, hUnion, Finset.sum_union hDisjoint]

/-- The regrown occurrences above **one** distinguished block, when two
sheets cover its regrown classes.  Stated for an arbitrary `anchor`, and
applied once at each member of `anchors`. -/
theorem selected_set (anchor first second : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel anchor first)
    (hSecond : (data.vertexPartition wall).Rel anchor second)
    (hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel anchor sheet →
      rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge first ∨
        rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge second)
    (path : StablePath data) :
    (rd.newOccurrences path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel anchor edge.1.2) =
      ({rd.candidate.newSourceEdge first, rd.candidate.newSourceEdge second} :
        Finset rd.candidate.datum.SourceEdge).filter
        (fun edge ↦ edge ∈ rd.newOccurrences path) := by
  classical
  ext edge
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hMemEdge, hRel⟩
    refine ⟨?_, hMemEdge⟩
    rw [rd.eq_newSourceEdge_of_mem path edge hMemEdge]
    exact hCover edge.1.2 hRel
  · rintro ⟨hEq, hMemEdge⟩
    refine ⟨hMemEdge, ?_⟩
    rcases hEq with rfl | rfl
    · exact (rd.newSourceEdge_sheet_rel_iff anchor first).mpr hFirst
    · exact (rd.newSourceEdge_sheet_rel_iff anchor second).mpr hSecond

/-- The same when one of the two regrown classes is pruned. -/
theorem selected_set_of_dangling (anchor first second : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel anchor first)
    (hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel anchor sheet →
      rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge first ∨
        rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge second)
    (hDangling : IsDangling rd.candidate.datum (rd.candidate.newSourceEdge second))
    (path : StablePath data) :
    (rd.newOccurrences path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel anchor edge.1.2) =
      ({rd.candidate.newSourceEdge first} : Finset rd.candidate.datum.SourceEdge).filter
        (fun edge ↦ edge ∈ rd.newOccurrences path) := by
  classical
  ext edge
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hMemEdge, hRel⟩
    refine ⟨?_, hMemEdge⟩
    have hEdgeNew := rd.eq_newSourceEdge_of_mem path edge hMemEdge
    rcases hCover edge.1.2 hRel with h | h
    · exact hEdgeNew.trans h
    · exact absurd (rd.new_not_mem_of_dangling second hDangling path)
        (fun hNot ↦ hNot (by rwa [← h, ← hEdgeNew]))
  · rintro ⟨rfl, hMemEdge⟩
    exact ⟨hMemEdge, (rd.newSourceEdge_sheet_rel_iff anchor first).mpr hFirst⟩

end SelectedData

end DraismaVargas.LocalCases.LimitChainTwoBlock
