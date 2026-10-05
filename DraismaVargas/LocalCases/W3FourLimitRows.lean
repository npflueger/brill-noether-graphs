module

public import DraismaVargas.LocalCases.W3FourStableGraph

@[expose] public section

/-!
# Figure 28's stable-row census, derived from the limit's own stable source

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{w3-r1-nd3-t2-(a=k₄)}`, its Figure 28 and Equation (2).

`W3FourStableGraph` reduces the whole Figure 28 family to one structure,
`LimitRows`: the limit's displayed stable rows, together with the statement
that above each of the three surviving directions `t₂`, `t₃`, `t₄` the
distinguished wall block `A₀` displays exactly one occurrence, in exactly one
row, with its own index.  Everything else in that module -- the four
determinants, `hDet`, `hAgree`, the certified positive exit -- is proved
against `LimitRows`.  `LimitRows.model` inhabits it only as a consistency
witness, which certifies nothing honest.

This module derives `LimitRows` from the actual incoming datum.

## What is proved here

* `stableRowPath` -- the limit's stable rows as lists of occurrences, indexed
  by `W4StableSource.StablePathLabelling`, which `ThirdEquation.W3SourceInput`
  supplies canonically through its `stablePath_card`
  (`StablePathLabelling.ofCardEq`).  Every surviving occurrence appears in
  exactly one of these lists and exactly once in it, and every dangling
  occurrence appears in none.
* `columnSum_stableRowPath` -- **these really are the limit's rows.**  The `t`
  entry computed from `stableRowPath` is literally
  `StableSourceMatrix.matrix data` at the corresponding stable path.  This is
  the honesty receipt for `oldPath`: it is not an arbitrary list family, it is
  the natural stable-length matrix of the incoming datum, relabelled.
* `grow_unique_of_wall_rel`, `other_unique_of_wall_rel`,
  `largest_unique_of_wall_rel` -- **the selected-block survival census.**  The
  only non-dangling occurrence above `t_j` whose sheet lies in `A₀` is `e_j`
  itself.  No new survival analysis is needed for this: the three survivors of
  `A₀` are already exhibited by `W3R1SourceProfile.Nd3Profile.surviving`, which
  `W3FourSourceCandidates.GrowProfile` carries as `surviving`, and the case's
  `nd = 3` uniqueness lemmas `grow_unique` / `other_unique` / `largest_unique`
  turn "three survivors above three distinct directions" into "one survivor per
  direction".  What this module adds is the step from a bare occurrence over
  `A₀` to an *incident* one, `incident_of_wall_rel`.
* `selectedSum_stableRowPath` -- one surviving occurrence in one stable row:
  the distinguished block's contribution to the `t` column of a stable row is
  its reciprocal index in the row containing it and zero in every other row.
* `limitRows` and `limitRowsOfInput` -- **`W3FourStableGraph.LimitRows`,
  derived.**  `limitRowsOfInput` needs only a `ThirdEquation.W3SourceInput` and
  a `W3FourSourceCandidates.GrowProfile`, which is exactly the payload
  `W3FourStableGraph.exists_figure28Receipts` already consumes.
* `exists_figure28Receipts_of_input` -- `exists_figure28Receipts` with its last
  supplied input removed: Figure 28's receipts, for the actual members, over
  the limit's actual stable rows.

## What is supplied rather than derived here

The census above is a census of the **limit**, which is what `LimitRows` names
and all that its three fields say: `oldPath row` is the list of occurrences the
limit's stable row `row` displays, and above each surviving direction the
distinguished block contributes one occurrence to one row.

It does **not** identify the limit's stable rows with the *outgoing* members'
stable rows.  `W3FourStableGraph.MemberColumn.presentation` puts the same
`oldPath` under each member's regrown occurrences, so making a member's
presented matrix the member's own `StableSourceMatrix.matrix` needs two further
things that are **not** proved here and are not assumed here:

* the retained half -- that the incoming stable row `row` becomes the outgoing
  stable row `row` under the occurrence correspondence of each of the four
  candidates.  This is the analogue of `W4OutgoingStableRows.stablePathEquiv`
  and `matrix_retained`, reached in the nd2 case only through
  `W3Nd2Survival`/`W3Nd2EndRows`/`W3Nd2Background`/`W3Nd2StableLift`/
  `W3Nd2RowDescent`;
* the regrown half -- `MemberColumn.selectedSheets` and `newSheets`
  *supply* each member's regrown row assignment, so the analogue of
  `W4OutgoingLimitMatrix.presented_matrix_eq` is not available from
  `W3FourStableGraph` alone; the honest regrown column is
  `W3FourRegrownColumn`'s.

Both belong to the outgoing stable graph of each candidate; neither is touched
here, and nothing here is weakened by their absence, because `LimitRows` is a
statement about the incoming datum alone.

## The branch swap

`LimitRows data wall geometry` is stated on the **incoming** datum alone.  The
two members that live on branch-swapped copies reach the common coordinate
system through their own `W3FourStableGraph.WallTransport`, carried by
`MemberColumn.transport`; the census is never transported.  So no analogue of
`WallTransport.ofSheetRelabeling` is needed here, and none is used.

## Which datum this is about

`ThirdEquation.W3SourceInput` carries `equation_c : data.targetExcess wall = 1`,
so everything here lives on the wall/limit side of the bridge recorded in
`FullDimensionalSource.false_of_changeMinimal_auxR0SourceInput`, exactly as
`W3FourClosure`, `W3FourSourceCandidates` and `W3FourStableGraph` do.
-/

namespace DraismaVargas.LocalCases.W3FourLimitRows

open DraismaVargas.Infrastructure
open TargetExpansion
open W4StableSource StableLocalProperties ThirdEquation W3R1SourceProfile
open W3FourSourceCandidates
open W3FourClosure
open W3FourStableGraph

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## The limit's own stable rows

`W4StableSource.StablePathLabelling` is a bijection between the limit's stable
paths and the row labels `Option target.edges`, and
`StablePathLabelling.ofCardEq` produces one from the cardinality equation that
`ThirdEquation.W3SourceInput` already carries.  `oldRowOf` sends a dangling
occurrence to `none` and a surviving one to the label of its stable path, so
the row lists below are a partition of the surviving occurrences. -/

section Rows

variable (labelling : StablePathLabelling data)

/-- The surviving occurrences the limit displays in one labelled stable row. -/
noncomputable def rowOccurrences (row : Option target.edges) :
    Finset data.SourceEdge :=
  letI : DecidablePred
      (fun edge : data.SourceEdge ↦ labelling.oldRowOf edge = some row) :=
    Classical.decPred _
  Finset.univ.filter fun edge ↦ labelling.oldRowOf edge = some row

theorem mem_rowOccurrences (row : Option target.edges)
    (edge : data.SourceEdge) :
    edge ∈ rowOccurrences labelling row ↔ labelling.oldRowOf edge = some row := by
  unfold rowOccurrences
  simp

/-- The limit's displayed stable rows, as occurrence lists.  Every surviving
occurrence appears in exactly one of them and exactly once in it; every
dangling occurrence appears in none. -/
noncomputable def stableRowPath (row : Option target.edges) :
    List data.SourceEdge :=
  (rowOccurrences labelling row).toList

theorem mem_stableRowPath (row : Option target.edges) (edge : data.SourceEdge) :
    edge ∈ stableRowPath labelling row ↔
      labelling.oldRowOf edge = some row := by
  rw [stableRowPath, Finset.mem_toList, mem_rowOccurrences]

theorem stableRowPath_nodup (row : Option target.edges) :
    (stableRowPath labelling row).Nodup :=
  Finset.nodup_toList _

/-- A dangling occurrence is displayed in no stable row. -/
theorem not_mem_stableRowPath_of_isDangling {edge : data.SourceEdge}
    (hDangling : IsDangling data edge) (row : Option target.edges) :
    edge ∉ stableRowPath labelling row := by
  rw [mem_stableRowPath, (labelling.oldRowOf_eq_none_iff edge).mpr hDangling]
  simp

/-- A surviving occurrence is displayed in the row of its own stable path. -/
theorem mem_stableRowPath_self {edge : data.SourceEdge}
    (hSurvives : ¬ IsDangling data edge) :
    edge ∈ stableRowPath labelling
      (labelling.row (NonDanglingEdge.stablePath
        (⟨edge, hSurvives⟩ : NonDanglingEdge data))) := by
  rw [mem_stableRowPath]
  exact labelling.oldRowOf_eq_some (⟨edge, hSurvives⟩ : NonDanglingEdge data)

/-- A row label names a stable path, and `oldRowOf` records exactly that. -/
theorem oldRowOf_eq_some_iff (edge : data.SourceEdge)
    (row : Option target.edges) :
    labelling.oldRowOf edge = some row ↔
      ∃ hSurvives : ¬ IsDangling data edge,
        NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data) =
          labelling.row.symm row := by
  classical
  constructor
  · intro hRow
    have hSurvives : ¬ IsDangling data edge := by
      intro hDangling
      rw [(labelling.oldRowOf_eq_none_iff edge).mpr hDangling] at hRow
      simp at hRow
    refine ⟨hSurvives, ?_⟩
    rw [labelling.oldRowOf_eq_some (⟨edge, hSurvives⟩ : NonDanglingEdge data)] at hRow
    exact labelling.row.eq_symm_apply.mpr (Option.some.inj hRow)
  · rintro ⟨hSurvives, hPath⟩
    rw [labelling.oldRowOf_eq_some (⟨edge, hSurvives⟩ : NonDanglingEdge data), hPath,
      Equiv.apply_symm_apply]

/-- **These are the limit's own rows.**  Every retained column computed from
`stableRowPath` is literally the corresponding entry of
`StableSourceMatrix.matrix data`, the natural stable-length matrix of the
incoming datum.  This is what makes `LimitRows.oldPath` honest rather than an
arbitrary list family. -/
theorem columnSum_stableRowPath (row : Option target.edges) (t : target.edges) :
    columnSum (stableRowPath labelling row) t =
      StableSourceMatrix.matrix data (labelling.row.symm row) t := by
  classical
  have hSubset : StableSourceMatrix.occurrences data (labelling.row.symm row) t ⊆
      rowOccurrences labelling row := by
    intro edge hEdge
    obtain ⟨⟨hSurvives, hPath⟩, _⟩ :=
      (StableSourceMatrix.mem_occurrences _ t edge).mp hEdge
    exact (mem_rowOccurrences labelling row edge).mpr
      ((oldRowOf_eq_some_iff labelling edge row).mpr ⟨hSurvives, hPath⟩)
  unfold columnSum stableRowPath
  rw [Finset.sum_map_toList,
    ← Finset.sum_subset hSubset (fun edge hEdge hNot ↦ ?_),
    StableSourceMatrix.matrix]
  · refine Finset.sum_congr rfl fun edge hEdge ↦ ?_
    exact ite_eq_left ((StableSourceMatrix.mem_occurrences _ t edge).mp hEdge).2.symm
  · refine ite_eq_right fun hTarget ↦ hNot ?_
    obtain ⟨hSurvives, hPath⟩ := (oldRowOf_eq_some_iff labelling edge row).mp
      ((mem_rowOccurrences labelling row edge).mp hEdge)
    exact (StableSourceMatrix.mem_occurrences _ t edge).mpr
      ⟨⟨hSurvives, hPath⟩, hTarget.symm⟩

end Rows

/-! ## One surviving occurrence in one stable row

The shape every `LimitRows` field has: if exactly one surviving occurrence
lies above `t` and over the distinguished wall block, then the block's
contribution to the `t` column is its reciprocal index in the row containing
it and zero everywhere else. -/

section Selected

variable (labelling : StablePathLabelling data)

theorem selectedSum_stableRowPath (geometry : FourStarGeometry data wall)
    (t : target.edges) {selected : data.SourceEdge}
    (hSurvives : ¬ IsDangling data selected)
    (hTarget : t = selected.1.1)
    (hRel : (data.vertexPartition wall).Rel geometry.growAnchor selected.1.2)
    (hUnique : ∀ edge : data.SourceEdge, ¬ IsDangling data edge → t = edge.1.1 →
      (data.vertexPartition wall).Rel geometry.growAnchor edge.1.2 →
      edge = selected)
    (row : Option target.edges) :
    selectedSum geometry (stableRowPath labelling row) t =
      if row = labelling.row (NonDanglingEdge.stablePath
          (⟨selected, hSurvives⟩ : NonDanglingEdge data)) then
        (1 : ℚ) / data.sourceEdgeIndex selected
      else 0 := by
  classical
  have hZero : ∀ edge ∈ rowOccurrences labelling row, edge ≠ selected →
      (if t = edge.1.1 ∧
          (data.vertexPartition wall).Rel geometry.growAnchor edge.1.2 then
        (1 : ℚ) / data.sourceEdgeIndex edge else 0) = 0 := by
    intro edge hEdge hNe
    refine ite_eq_right fun hCond ↦ hNe ?_
    obtain ⟨hEdgeSurvives, _⟩ := (oldRowOf_eq_some_iff labelling edge row).mp
      ((mem_rowOccurrences labelling row edge).mp hEdge)
    exact hUnique edge hEdgeSurvives hCond.1 hCond.2
  unfold selectedSum stableRowPath
  rw [Finset.sum_map_toList]
  by_cases hRow : row = labelling.row (NonDanglingEdge.stablePath
      (⟨selected, hSurvives⟩ : NonDanglingEdge data))
  · have hMem : selected ∈ rowOccurrences labelling row :=
      (mem_rowOccurrences labelling row selected).mpr
        (by rw [hRow]
            exact labelling.oldRowOf_eq_some
              (⟨selected, hSurvives⟩ : NonDanglingEdge data))
    rw [Finset.sum_eq_single_of_mem selected hMem hZero, ite_eq_left hRow,
      ite_eq_left ⟨hTarget, hRel⟩]
  · rw [ite_eq_right hRow]
    refine Finset.sum_eq_zero fun edge hEdge ↦ ?_
    by_cases hNe : edge = selected
    · refine absurd ?_ hRow
      have hMem := (mem_rowOccurrences labelling row edge).mp hEdge
      rw [hNe, labelling.oldRowOf_eq_some
        (⟨selected, hSurvives⟩ : NonDanglingEdge data)] at hMem
      exact (Option.some.inj hMem).symm
    · exact hZero edge hEdge hNe

end Selected

/-! ## The selected-block survival census

`W3FourSourceCandidates.GrowProfile` already carries the incoming survival
census of the distinguished block: `surviving` says its three non-dangling
incident occurrences are `e₂`, `e₃`, `e₄`, and `grow_unique`, `other_unique`,
`largest_unique` say each surviving direction is represented by one of them.
What is added here is the step from "an occurrence above `t` whose sheet lies
in `A₀`" to "an occurrence incident to `A₀`'s source vertex", which is where
the refinement `edgePartition t ≼ vertexPartition wall` enters. -/

section Census

variable {star : ThreeStar target wall} {input : W3SourceInput data star}

/-- An occurrence above a wall direction whose sheet lies in the distinguished
block is incident to that block's source vertex. -/
theorem incident_of_wall_rel (grown : GrowProfile input)
    {edge : data.SourceEdge}
    (hMem : edge.1.1 ∈ GluingDatum.incidentEdges wall)
    (hRel : (data.vertexPartition wall).Rel grown.growAnchor edge.1.2) :
    Incident data edge
      (WallBlock.sourceVertex data wall input.distinguishedBlock) :=
  (incident_wallBlock_sourceVertex_iff data input.distinguishedBlock edge).mpr
    ⟨hMem, (WallBlock.ofSheet_eq_iff_rel data wall input.distinguishedBlock
      edge.1.2).mpr (grown.growAnchor_wall_rel.trans hRel)⟩

/-- The grow survivor really survives. -/
theorem grow_survives (grown : GrowProfile input) :
    ¬ IsDangling data grown.grow.1 :=
  (mem_survivors data input.distinguishedBlock grown.grow).mp
    (by rw [grown.surviving]; simp)

/-- The second smaller survivor really survives. -/
theorem other_survives (grown : GrowProfile input) :
    ¬ IsDangling data grown.other.1 :=
  (mem_survivors data input.distinguishedBlock grown.other).mp
    (by rw [grown.surviving]; simp)

/-- The full-degree survivor really survives. -/
theorem largest_survives (grown : GrowProfile input) :
    ¬ IsDangling data grown.largest.1 :=
  (mem_survivors data input.distinguishedBlock grown.largest).mp
    (by rw [grown.surviving]; simp)

/-- **Above `t₂`, the distinguished block displays `e₂` alone.** -/
theorem grow_unique_of_wall_rel (grown : GrowProfile input)
    {edge : data.SourceEdge} (hSurvives : ¬ IsDangling data edge)
    (hTarget : grown.growTarget = edge.1.1)
    (hRel : (data.vertexPartition wall).Rel grown.growAnchor edge.1.2) :
    edge = grown.grow.1 := by
  have hMem : edge.1.1 ∈ GluingDatum.incidentEdges wall :=
    hTarget ▸ grown.growTarget_mem
  have hIncident := incident_of_wall_rel grown hMem hRel
  exact congrArg Subtype.val (grow_unique grown ⟨edge, hIncident⟩
    ((mem_survivors data input.distinguishedBlock _).mpr hSurvives) hTarget.symm)

/-- **Above `t₃`, the distinguished block displays `e₃` alone.** -/
theorem other_unique_of_wall_rel (grown : GrowProfile input)
    {edge : data.SourceEdge} (hSurvives : ¬ IsDangling data edge)
    (hTarget : grown.otherTarget = edge.1.1)
    (hRel : (data.vertexPartition wall).Rel grown.growAnchor edge.1.2) :
    edge = grown.other.1 := by
  have hMem : edge.1.1 ∈ GluingDatum.incidentEdges wall :=
    hTarget ▸ grown.otherTarget_mem
  have hIncident := incident_of_wall_rel grown hMem hRel
  exact congrArg Subtype.val (other_unique grown ⟨edge, hIncident⟩
    ((mem_survivors data input.distinguishedBlock _).mpr hSurvives) hTarget.symm)

/-- **Above `t₄`, the distinguished block displays `e₄` alone.** -/
theorem largest_unique_of_wall_rel (grown : GrowProfile input)
    {edge : data.SourceEdge} (hSurvives : ¬ IsDangling data edge)
    (hTarget : grown.largestTarget = edge.1.1)
    (hRel : (data.vertexPartition wall).Rel grown.growAnchor edge.1.2) :
    edge = grown.largest.1 := by
  have hMem : edge.1.1 ∈ GluingDatum.incidentEdges wall :=
    hTarget ▸ grown.largestTarget_mem
  have hIncident := incident_of_wall_rel grown hMem hRel
  exact congrArg Subtype.val (largest_unique grown ⟨edge, hIncident⟩
    ((mem_survivors data input.distinguishedBlock _).mpr hSurvives) hTarget.symm)

end Census

/-! ## `LimitRows`, derived -/

section Derivation

variable {star : ThreeStar target wall} {input : W3SourceInput data star}

/-- **The limit's stable-row census of case `{w3-r1-nd3-t2-(a=k₄)}`, derived.**

The rows are the limit's own stable paths (`columnSum_stableRowPath`), and each
of the three `selected_*` fields is the selected-block survival census above
one surviving direction. -/
noncomputable def limitRows (labelling : StablePathLabelling data)
    (grown : GrowProfile input) :
    LimitRows data wall (ofGrowProfile grown) where
  oldPath := stableRowPath labelling
  rowGrow := labelling.row (NonDanglingEdge.stablePath
    (⟨grown.grow.1, grow_survives grown⟩ : NonDanglingEdge data))
  rowOther := labelling.row (NonDanglingEdge.stablePath
    (⟨grown.other.1, other_survives grown⟩ : NonDanglingEdge data))
  rowLargest := labelling.row (NonDanglingEdge.stablePath
    (⟨grown.largest.1, largest_survives grown⟩ : NonDanglingEdge data))
  selected_grow := fun row ↦
    selectedSum_stableRowPath labelling (ofGrowProfile grown) grown.growTarget
      (grow_survives grown) rfl rfl
      (fun _ ↦ grow_unique_of_wall_rel grown) row
  selected_other := fun row ↦
    selectedSum_stableRowPath labelling (ofGrowProfile grown) grown.otherTarget
      (other_survives grown) rfl (ofGrowProfile grown).other_wall_rel
      (fun _ ↦ other_unique_of_wall_rel grown) row
  selected_largest := fun row ↦
    selectedSum_stableRowPath labelling (ofGrowProfile grown)
      grown.largestTarget (largest_survives grown) rfl
      (ofGrowProfile grown).largest_wall_rel
      (fun _ ↦ largest_unique_of_wall_rel grown) row

/-- The derived census displays the limit's own rows: its retained columns are
`StableSourceMatrix.matrix data`. -/
theorem limitRows_columnSum (labelling : StablePathLabelling data)
    (grown : GrowProfile input) (row : Option target.edges)
    (t : target.edges) :
    columnSum ((limitRows labelling grown).oldPath row) t =
      StableSourceMatrix.matrix data (labelling.row.symm row) t :=
  columnSum_stableRowPath labelling row t

/-- **`LimitRows` from the case's own hypotheses.**  The row labelling is the
canonical one supplied by `W3SourceInput.stablePath_card`. -/
noncomputable def limitRowsOfInput (grown : GrowProfile input) :
    LimitRows data wall (ofGrowProfile grown) :=
  limitRows (StablePathLabelling.ofCardEq data input.stablePath_card) grown

end Derivation

/-! ## Figure 28's receipts over the limit's actual rows -/

section Receipts

variable {star : ThreeStar target wall} {input : W3SourceInput data star}

/-- **`W3FourStableGraph.exists_figure28Receipts` with its last supplied input
removed.**  Figure 28's four members, with every `background_*` and `index_*`
receipt discharged from their resolutions, over the limit's *actual* stable
rows: `receipts.rows` is `limitRowsOfInput`, whose `oldPath` is
`StableSourceMatrix.matrix data` relabelled (`limitRows_columnSum`).

Together with `W3FourStableGraph.Figure28Receipts.det_one` … `det_four`,
`gaugeFamily` and `exists_valid_positive_exit_with_pencil`, this removes the
last hypothesis those theorems were stated against. -/
theorem exists_figure28Receipts_of_input
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1)
    (root : target.V) (hRoot : root ≠ wall)
    (hGrowFixed :
      TargetBranchRegion.edgeMoved wall root hRoot profile.first.1.1.1 = false)
    (hLargestFixed :
      TargetBranchRegion.edgeMoved wall root hRoot profile.largest.1.1.1 = false)
    (hOtherMoved :
      TargetBranchRegion.edgeMoved wall root hRoot profile.second.1.1.1 = true) :
    ∃ receipts : Figure28Receipts data wall
        (ofGrowProfile (growProfileFirst profile directions largest_index)),
      receipts.rows =
          limitRowsOfInput (growProfileFirst profile directions largest_index) ∧
        HEq (receipts.member 2).candidate
          (thirdCandidate profile directions largest_index) ∧
        HEq (receipts.member 3).candidate
          (fourthCandidate profile directions largest_index) :=
  exists_figure28Receipts profile directions largest_index root hRoot hGrowFixed
    hLargestFixed hOtherMoved
    (limitRowsOfInput (growProfileFirst profile directions largest_index))

end Receipts

end DraismaVargas.LocalCases.W3FourLimitRows
