module

public import DraismaVargas.LocalCases.W3FourRowDescent
public import DraismaVargas.LocalCases.W3FourLimitRows

@[expose] public section

/-!
# The regrown column, and Figure 28's presented matrices are the honest ones

Source: Draisma--Vargas Part I, Case {w3-r1-nd3-t2-(a=k4)}, Figure 28,
Equation (2), and the induced-labelling and limit-matrix argument of the
subsection on inherited properties (`lemma-limit-matrix-change`).

`W3FourRowDescent` produces, for each of Figure 28's four members, the
occurrence-induced stable-row equivalence `stablePathEquiv` and
`matrix_retained`: every column of the member's own `StableSourceMatrix.matrix`
other than the regrown one is literally the incoming wall column read through
that equivalence.  Of the regrown column it settles only the support and the
row of each occurrence (`mem_occurrences_new_iff`).  `W3FourStableGraph` and
`W3FourLimitRows` take each member's regrown row assignment as the data
`MemberColumn.selectedSheets`.

This module evaluates the regrown column, which is the
`W4OutgoingLimitMatrix.presented_matrix_eq` analogue for this case.

## What is proved here

* The gauge notion the regrown half needs is `LimitChainCore.Gauge`:
  `W3FourStableGraph.WallTransport` is only a map of occurrence sets
  preserving target occurrence and dilation index, which is all a length
  matrix reads and **not** enough to carry a stable row; a `Gauge` adds
  bijectivity, preservation of pruning, the induced row bijection and the wall
  partition.  Both gauges Figure 28 uses are of this kind: `Gauge.refl` for
  `M⁽³⁾`, `M⁽⁴⁾` and `Gauge.ofSheetRelabeling` -- the branch swap of
  Draisma--Vargas Part I -- for
  `M⁽¹⁾`, `M⁽²⁾`.  `Gauge.wallTransport` below is the forgetful map to
  `WallTransport`.
* The regrown column of a member is evaluated by the core's
  `SelectedData.matrix_new`: given a list of sheets whose regrown occurrences
  lie on one outgoing row and exhaust it, the column entry is the sum of their
  reciprocal new-edge indices, with `Nodup` **after** `newSourceEdge`.
* `ColumnData` -- one member packaged for the regrown column: its gauge, its
  `LimitChainCore.GraphData` (from `W3FourRowDescent`), the compatibility of
  the background direction with the gauge, and the displayed regrown
  occurrences over the distinguished block.  `ColumnData.memberColumn` produces the
  `W3FourStableGraph.MemberColumn`, with Figure 28's `σ⁽ᵠ⁾(J₀,1) = σ₀(J₀,α)`
  receipt *derived* from the row data's background shape rather than assumed.
* `ColumnData.backgroundSheets_regrownAt` / `_exhaustive` / `_nodup` -- **the
  background half of a regrown row, derived.**  Over the limit's own rows
  (`W3FourLimitRows.stableRowPath`) the list
  `W3FourStableGraph.backgroundSheetsOf` is the geometric one: it enumerates,
  once per regrown occurrence, exactly the wall blocks outside `A₀` that regrow
  onto that row.
* `ColumnData.presented_matrix_eq` and `presented_matrix_submatrix` -- **a
  member's presented matrix is that member's own natural stable-length
  matrix**, at the composite row correspondence `ColumnData.rowEquiv` and the
  canonical column correspondence `occurrenceEquiv`.  The retained columns go
  through `LimitChainCore.SelectedData.matrix_retained` and
  `Gauge.matrix_gauge`, the regrown column through `matrix_new`; no cardinality
  bijection is used.
* `growColumnData`, `positionTwoColumnData`, `positionOneColumnData` -- the
  four members packaged, with the selected census discharged from
  `W3FourSurvival`: a grow member regrows one class over `A₀`
  (`new_dangles_of_separate` kills the rest), `M⁽²⁾` regrows one
  (`newSourceEdge_eq_of_survives`, the detached singleton dangling), and
  `M⁽¹⁾` regrows **two distinct** ones (`newSourceEdge_cover`,
  `new_grow_ne_new_other`) -- which is why `det_one` has two selected terms.
* `exists_figure28Receipts_honest` -- **`W3FourStableGraph.exists_figure28Receipts`
  over the limit's own rows with every presented matrix proved honest.**  Its
  `receipts` feeds `Figure28Receipts.det_eq_figure28`, `gaugeFamily` and
  `exists_valid_positive_exit_with_pencil` unchanged, so all of those stand
  over matrices that are the members' own.

## What this does *not* claim

Nothing here asserts that any member is nonsingular; the exit theorem keeps its
own `det ≠ 0` gate.  Nothing here identifies the **incoming** member or
transports the exit back to original coordinates (that is done in
`W3FourIncomingMatching` and `W3FourHonestReceipts`).  The three rows
`rowGrow`, `rowOther`, `rowLargest` are not asserted distinct, and every
statement below holds verbatim when two of them coincide.

## Which datum this is about

Everything is stated on the wall/limit side of the bridge recorded in
`FullDimensionalSource.false_of_changeMinimal_auxR0SourceInput`, exactly as
`W3FourClosure`, `W3FourStableGraph`, `W3FourLimitRows`, `W3FourSurvival` and
`W3FourRowDescent` are.  The presentations are presentations of the
**outgoing** members' data, which is the other side; no single object is asked
to be both.
-/

namespace DraismaVargas.LocalCases.W3FourRegrownColumn

open DraismaVargas.Infrastructure
open TargetExpansion
open BalancedGlobal
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open ResolutionCoarseFine ResolutionM11
open ResolutionAwayFromWall StableSourceMatrix StablePathCount
open W3FourClosure (FourStarGeometry ofGrowProfile)
open W3FourSurvival
open W3FourStableGraph
open W3FourLimitRows
open LimitChainCore (Gauge GraphData sourceEdge_of_target)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data base : GluingDatum target degree}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## The forgetful map from a gauge to a length-matrix transport -/

/-- The underlying length-matrix transport of a gauge. -/
def _root_.DraismaVargas.LocalCases.LimitChainCore.Gauge.wallTransport
    (gauge : Gauge data base wall) : WallTransport data base where
  edge := gauge.edge
  target_eq := gauge.target_eq
  index_eq := gauge.index_eq

@[simp] theorem _root_.DraismaVargas.LocalCases.LimitChainCore.Gauge.wallTransport_edge
    (gauge : Gauge data base wall) (e : data.SourceEdge) :
    (gauge.wallTransport (wall := wall)).edge e = gauge.edge e := rfl

/-! ## The background half of a regrown row, read off the limit's own rows

`W3FourStableGraph.backgroundSheetsOf` lists the sheets of the occurrences a
displayed row carries above `t_α` outside the distinguished block.  Over the
limit's *own* rows (`W3FourLimitRows.stableRowPath`) that list is exactly the
geometric one: each such occurrence regrows, once, onto the corresponding
outgoing row. -/

section BackgroundList

theorem mem_backgroundSheetsOf (geometry : FourStarGeometry data wall)
    (displayed : List data.SourceEdge) (t : target.edges) (sheet : Fin degree) :
    sheet ∈ backgroundSheetsOf geometry displayed t ↔
      ∃ edge ∈ displayed, t = edge.1.1 ∧
        ¬ (data.vertexPartition wall).Rel geometry.growAnchor edge.1.2 ∧
        edge.1.2 = sheet := by
  classical
  unfold backgroundSheetsOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨edge, hEdge, hSome⟩
    by_cases hCond : t = edge.1.1 ∧
        ¬ (data.vertexPartition wall).Rel geometry.growAnchor edge.1.2
    · rw [ite_eq_left hCond] at hSome
      exact ⟨edge, hEdge, hCond.1, hCond.2, Option.some.inj hSome⟩
    · rw [ite_eq_right hCond] at hSome
      exact absurd hSome (by simp)
  · rintro ⟨edge, hEdge, hTarget, hRel, rfl⟩
    exact ⟨edge, hEdge, by rw [ite_eq_left ⟨hTarget, hRel⟩]⟩

/-- Distinct displayed occurrences above `t` have distinct sheets, so the
background list of a nodup row is nodup. -/
theorem backgroundSheetsOf_nodup (geometry : FourStarGeometry data wall)
    {displayed : List data.SourceEdge} (hNodup : displayed.Nodup)
    (t : target.edges) : (backgroundSheetsOf geometry displayed t).Nodup := by
  classical
  refine List.Nodup.filterMap ?_ hNodup
  intro first second sheet hFirst hSecond
  have hFirstInfo : t = first.1.1 ∧ first.1.2 = sheet := by
    by_cases hCond : t = first.1.1 ∧
        ¬ (data.vertexPartition wall).Rel geometry.growAnchor first.1.2
    · rw [Option.mem_def, ite_eq_left hCond] at hFirst
      exact ⟨hCond.1, Option.some.inj hFirst⟩
    · rw [Option.mem_def, ite_eq_right hCond] at hFirst
      exact absurd hFirst (by simp)
  have hSecondInfo : t = second.1.1 ∧ second.1.2 = sheet := by
    by_cases hCond : t = second.1.1 ∧
        ¬ (data.vertexPartition wall).Rel geometry.growAnchor second.1.2
    · rw [Option.mem_def, ite_eq_left hCond] at hSecond
      exact ⟨hCond.1, Option.some.inj hSecond⟩
    · rw [Option.mem_def, ite_eq_right hCond] at hSecond
      exact absurd hSecond (by simp)
  rw [← sourceEdge_of_target first t hFirstInfo.1,
    ← sourceEdge_of_target second t hSecondInfo.1, hFirstInfo.2, hSecondInfo.2]

end BackgroundList
/-! ## One Figure 28 member, packaged for the regrown column

`LimitChainCore.GraphData` is what the retained half needs; `ColumnData` adds
exactly what the regrown half needs on top of it: the gauge the member's base is reached by,
the compatibility of the background direction with that gauge, and the
displayed regrown occurrences over the distinguished block.  The last is the
only member-specific input, and it is discharged for all four members below. -/

/-- One Figure 28 member together with the regrown data the presented matrix
needs.  Everything else is inherited from the core's `GraphData`. -/
structure ColumnData (data : GluingDatum target degree) (wall : target.V)
    (geometry : FourStarGeometry data wall)
    (labelling : StablePathLabelling data) where
  /-- The gauge copy of the incoming datum the member lives on. -/
  base : GluingDatum target degree
  /-- The gauge itself. -/
  gauge : Gauge data base wall
  /-- The member's row descent, as `W3FourRowDescent` packages it. -/
  rowData : GraphData base wall
  /-- The row data's anchor names the distinguished wall block. -/
  anchor_rel : (data.vertexPartition wall).Rel geometry.growAnchor rowData.selected
  /-- and the background direction's own occurrences. -/
  background_sourceEdge : ∀ sheet : Fin degree,
    base.sourceEdge rowData.retainedTarget sheet =
      gauge.edge (data.sourceEdge rowData.retainedTarget sheet)
  /-- The regrown occurrences the member displays over the distinguished
  block, listed by the limit's stable rows. -/
  selectedSheets : Option target.edges → List (Fin degree)
  /-- Each of them is a surviving regrown occurrence of that row. -/
  selected_mem : ∀ (row : Option target.edges) (sheet : Fin degree),
    sheet ∈ selectedSheets row →
      (data.vertexPartition wall).Rel geometry.growAnchor sheet ∧
        rowData.RegrownAt (gauge.row (labelling.row.symm row)) sheet
  /-- No regrown occurrence is displayed twice. -/
  selected_nodup : ∀ row : Option target.edges,
    ((selectedSheets row).map rowData.candidate.newSourceEdge).Nodup
  /-- and none is missed. -/
  selected_exhaustive : ∀ (row : Option target.edges) (sheet : Fin degree),
    (data.vertexPartition wall).Rel geometry.growAnchor sheet →
    rowData.RegrownAt (gauge.row (labelling.row.symm row)) sheet →
      rowData.candidate.newSourceEdge sheet ∈
        (selectedSheets row).map rowData.candidate.newSourceEdge

namespace ColumnData

variable {geometry : FourStarGeometry data wall} {labelling : StablePathLabelling data}
  (cd : ColumnData data wall geometry labelling)

/-- The background condition read on the incoming datum. -/
theorem background_iff (sheet : Fin degree) :
    ¬ (cd.base.vertexPartition wall).Rel cd.rowData.selected sheet ↔
      ¬ (data.vertexPartition wall).Rel geometry.growAnchor sheet := by
  rw [cd.gauge.wall_eq]
  exact not_congr ⟨fun hRel ↦ cd.anchor_rel.trans hRel,
    fun hRel ↦ cd.anchor_rel.symm.trans hRel⟩

/-- **The member, as `W3FourStableGraph` presents it.**  Its background index
receipt -- Figure 28's `σ⁽ᵠ⁾(J₀,1) = σ₀(J₀,α)` -- is discharged from the row
data's own background shape rather than assumed. -/
noncomputable def memberColumn : MemberColumn data wall geometry where
  base := cd.base
  transport := cd.gauge.wallTransport
  candidate := cd.rowData.candidate
  backgroundTarget := cd.rowData.retainedTarget
  valid_of_old := fun _ ↦ cd.rowData.valid
  selectedSheets := cd.selectedSheets
  background_index := by
    intro sheet hSheet
    show cd.rowData.candidate.datum.sourceEdgeIndex
        (cd.rowData.candidate.newSourceEdge sheet) = _
    rw [cd.rowData.newIndex_eq ((cd.background_iff sheet).mpr hSheet),
      cd.background_sourceEdge sheet, cd.gauge.index_eq,
      GluingDatum.sourceEdgeIndex_sourceEdge]

@[simp] theorem memberColumn_candidate :
    cd.memberColumn.candidate = cd.rowData.candidate := rfl

@[simp] theorem memberColumn_selectedSheets :
    cd.memberColumn.selectedSheets = cd.selectedSheets := rfl

end ColumnData

/-! ## One member's canonical presentation, written for a single member

`W3FourStableGraph.MemberColumn.presentation` reads a whole family but uses
only the chosen index, so it is literally the presentation below. -/

/-- The canonical presentation of one member over one family of displayed
rows. -/
noncomputable def soloPresentation {geometry : FourStarGeometry data wall}
    (mc : MemberColumn data wall geometry)
    (oldPath : Option target.edges → List data.SourceEdge) :
    mc.candidate.datum.LengthMatrixPresentation (Option target.edges) where
  targetEdge := occurrenceEquiv target wall mc.candidate.right
  path row :=
    ((oldPath row).map fun edge ↦
        mc.candidate.oldSourceEdge (mc.transport.edge edge)) ++
      (mc.selectedSheets row ++
          backgroundSheetsOf geometry (oldPath row) mc.backgroundTarget).map
        mc.candidate.newSourceEdge

/-- It is the corresponding component of the family presentation. -/
theorem presentation_eq_solo {geometry : FourStarGeometry data wall} {n : ℕ}
    (member : Fin n → MemberColumn data wall geometry)
    (oldPath : Option target.edges → List data.SourceEdge) (i : Fin n) :
    MemberColumn.presentation member oldPath i =
      soloPresentation (member i) oldPath := rfl

theorem solo_matrix_some {geometry : FourStarGeometry data wall}
    (mc : MemberColumn data wall geometry)
    (oldPath : Option target.edges → List data.SourceEdge)
    (row : Option target.edges) (column : target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix (soloPresentation mc oldPath) row
        (some column) = columnSum (oldPath row) column :=
  MemberColumn.matrix_some_eq (fun _ : Fin 1 ↦ mc) oldPath 0 row column

theorem solo_matrix_none {geometry : FourStarGeometry data wall}
    (mc : MemberColumn data wall geometry)
    (oldPath : Option target.edges → List data.SourceEdge)
    (row : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix (soloPresentation mc oldPath) row
        none =
      ((mc.selectedSheets row ++
          backgroundSheetsOf geometry (oldPath row) mc.backgroundTarget).map
        fun sheet ↦ (1 : ℚ) / newIndex mc.candidate sheet).sum :=
  gaugePresentation_matrix_none (fun _ : Fin 1 ↦ mc.base)
    (fun _ : Fin 1 ↦ mc.transport) (fun _ : Fin 1 ↦ mc.candidate) oldPath
    (fun _ : Fin 1 ↦ fun row ↦ mc.selectedSheets row ++
      backgroundSheetsOf geometry (oldPath row) mc.backgroundTarget) 0 row

/-! ## The background regrown occurrences of a member, derived -/

namespace ColumnData

variable {geometry : FourStarGeometry data wall} {labelling : StablePathLabelling data}
  (cd : ColumnData data wall geometry labelling)

/-- **A background regrown occurrence represents the incoming `t_α`
occurrence through its own sheet**, transported by the gauge. -/
theorem background_newOldSourceEdge {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel geometry.growAnchor sheet) :
    cd.rowData.newOldSourceEdge sheet =
      cd.gauge.edge (data.sourceEdge cd.rowData.retainedTarget sheet) := by
  rw [cd.rowData.newOldSourceEdge_background
    ((cd.background_iff sheet).mpr hSheet), cd.background_sourceEdge sheet]

/-- Two background sheets carry one regrown occurrence exactly when their
incoming `t_α` occurrences agree. -/
theorem background_newSourceEdge_eq_iff {first second : Fin degree}
    (hFirst : ¬ (data.vertexPartition wall).Rel geometry.growAnchor first) :
    cd.rowData.candidate.newSourceEdge first =
        cd.rowData.candidate.newSourceEdge second ↔
      data.sourceEdge cd.rowData.retainedTarget first =
        data.sourceEdge cd.rowData.retainedTarget second := by
  rw [LimitChainCore.Background.newSourceEdge_eq_iff cd.rowData.toBackgroundShape
      ((cd.background_iff first).mpr hFirst),
    ← LimitChainCore.sourceEdge_eq_iff_rel cd.base
      cd.rowData.retainedTarget first second,
    cd.background_sourceEdge first, cd.background_sourceEdge second]
  exact ⟨fun hEqual ↦ cd.gauge.edge.injective hEqual, congrArg cd.gauge.edge⟩

/-- A background sheet's regrown occurrence lies outside the distinguished
block, as a sheet. -/
theorem background_of_newSourceEdge_eq {first second : Fin degree}
    (hFirst : ¬ (data.vertexPartition wall).Rel geometry.growAnchor first)
    (hEqual : cd.rowData.candidate.newSourceEdge first =
      cd.rowData.candidate.newSourceEdge second) :
    ¬ (data.vertexPartition wall).Rel geometry.growAnchor second := by
  have hRel : (cd.base.edgePartition cd.rowData.retainedTarget).Rel
      first second :=
    (LimitChainCore.Background.newSourceEdge_eq_iff cd.rowData.toBackgroundShape
      ((cd.background_iff first).mpr hFirst)).mp hEqual
  have hRefines : (cd.base.edgePartition cd.rowData.retainedTarget).Refines
      (cd.base.vertexPartition wall) :=
    refines_of_mem_incidentEdges cd.base cd.rowData.target_mem
  intro hSecond
  refine hFirst ?_
  have hWall : (cd.base.vertexPartition wall).Rel first second := hRefines.rel hRel
  rw [cd.gauge.wall_eq] at hWall
  exact hSecond.trans hWall.symm

/-- The member's background regrown sheets on one displayed row. -/
noncomputable def backgroundSheets (row : Option target.edges) : List (Fin degree) :=
  backgroundSheetsOf geometry (stableRowPath labelling row)
    cd.rowData.retainedTarget

/-- What a background sheet of a displayed row is: the sheet of an occurrence
that row displays above `t_α` outside the distinguished block. -/
theorem backgroundSheets_spec {row : Option target.edges} {sheet : Fin degree}
    (hMem : sheet ∈ cd.backgroundSheets row) :
    ¬ (data.vertexPartition wall).Rel geometry.growAnchor sheet ∧
      data.sourceEdge cd.rowData.retainedTarget sheet ∈
        stableRowPath labelling row ∧
      (data.sourceEdge cd.rowData.retainedTarget sheet).1.2 = sheet := by
  classical
  obtain ⟨edge, hEdge, hTarget, hRel, rfl⟩ :=
    (mem_backgroundSheetsOf geometry (stableRowPath labelling row)
      cd.rowData.retainedTarget sheet).mp hMem
  rw [sourceEdge_of_target edge _ hTarget]
  exact ⟨hRel, hEdge, rfl⟩

/-- and conversely. -/
theorem mem_backgroundSheets {row : Option target.edges} {edge : data.SourceEdge}
    (hMem : edge ∈ stableRowPath labelling row)
    (hTarget : cd.rowData.retainedTarget = edge.1.1)
    (hRel : ¬ (data.vertexPartition wall).Rel geometry.growAnchor edge.1.2) :
    edge.1.2 ∈ cd.backgroundSheets row :=
  (mem_backgroundSheetsOf geometry (stableRowPath labelling row)
    cd.rowData.retainedTarget edge.1.2).mpr
      ⟨edge, hMem, hTarget, hRel, rfl⟩

/-- **Every background sheet of a displayed row really regrows onto the
corresponding outgoing row.**  Both halves are the background shape's own:
the new occurrence has exactly its `t_α` representative's pruning status, and
it lies in that representative's stable row. -/
theorem backgroundSheets_regrownAt {row : Option target.edges} {sheet : Fin degree}
    (hMem : sheet ∈ cd.backgroundSheets row) :
    cd.rowData.RegrownAt (cd.gauge.row (labelling.row.symm row)) sheet := by
  obtain ⟨hRel, hDisplayed, _⟩ := cd.backgroundSheets_spec hMem
  obtain ⟨hOldSurvives, hOldRow⟩ :=
    (oldRowOf_eq_some_iff labelling
        (data.sourceEdge cd.rowData.retainedTarget sheet) row).mp
      ((mem_stableRowPath labelling row _).mp hDisplayed)
  have hImage : ¬ IsDangling cd.base
      (cd.gauge.edge (data.sourceEdge cd.rowData.retainedTarget sheet)) :=
    fun hDangling ↦ hOldSurvives ((cd.gauge.isDangling_iff _).mp hDangling)
  have hNewSurvives : ¬ IsDangling cd.rowData.candidate.datum
      (cd.rowData.candidate.newSourceEdge sheet) := by
    rw [cd.rowData.new_isDangling_iff cd.rowData.valid
      ((cd.background_iff sheet).mpr hRel), cd.background_sourceEdge sheet]
    exact hImage
  refine ⟨hNewSurvives, ?_⟩
  calc (cd.rowData.newOldEdge sheet hNewSurvives).stablePath
      = NonDanglingEdge.stablePath
          (⟨cd.gauge.edge
              (data.sourceEdge cd.rowData.retainedTarget sheet),
            hImage⟩ : NonDanglingEdge cd.base) :=
        congrArg NonDanglingEdge.stablePath
          (Subtype.ext (cd.background_newOldSourceEdge hRel))
    _ = cd.gauge.row (NonDanglingEdge.stablePath
          (⟨data.sourceEdge cd.rowData.retainedTarget sheet,
            hOldSurvives⟩ : NonDanglingEdge data)) :=
        (cd.gauge.row_mk _ hOldSurvives).symm
    _ = cd.gauge.row (labelling.row.symm row) := congrArg cd.gauge.row hOldRow

/-- **and the background sheets miss none of the regrown occurrences outside
the distinguished block.** -/
theorem backgroundSheets_exhaustive {row : Option target.edges} {sheet : Fin degree}
    (hRel : ¬ (data.vertexPartition wall).Rel geometry.growAnchor sheet)
    (hRegrown : cd.rowData.RegrownAt (cd.gauge.row (labelling.row.symm row)) sheet) :
    cd.rowData.candidate.newSourceEdge sheet ∈
      (cd.backgroundSheets row).map cd.rowData.candidate.newSourceEdge := by
  obtain ⟨hNewSurvives, hRow⟩ := hRegrown
  have hOldSurvives : ¬ IsDangling data
      (data.sourceEdge cd.rowData.retainedTarget sheet) := by
    intro hDangling
    refine cd.rowData.newOldSourceEdge_survives sheet hNewSurvives ?_
    rw [cd.background_newOldSourceEdge hRel]
    exact (cd.gauge.isDangling_iff _).mpr hDangling
  have hImage : ¬ IsDangling cd.base
      (cd.gauge.edge (data.sourceEdge cd.rowData.retainedTarget sheet)) :=
    fun hDangling ↦ hOldSurvives ((cd.gauge.isDangling_iff _).mp hDangling)
  have hOldRow : NonDanglingEdge.stablePath
      (⟨data.sourceEdge cd.rowData.retainedTarget sheet, hOldSurvives⟩ :
        NonDanglingEdge data) = labelling.row.symm row := by
    refine cd.gauge.row.injective ?_
    calc cd.gauge.row (NonDanglingEdge.stablePath
            (⟨data.sourceEdge cd.rowData.retainedTarget sheet,
              hOldSurvives⟩ : NonDanglingEdge data))
        = NonDanglingEdge.stablePath
            (⟨cd.gauge.edge
                (data.sourceEdge cd.rowData.retainedTarget sheet),
              hImage⟩ : NonDanglingEdge cd.base) :=
          cd.gauge.row_mk _ hOldSurvives
      _ = (cd.rowData.newOldEdge sheet hNewSurvives).stablePath :=
          congrArg NonDanglingEdge.stablePath
            (Subtype.ext (cd.background_newOldSourceEdge hRel).symm)
      _ = cd.gauge.row (labelling.row.symm row) := hRow
  have hRefines : (data.edgePartition cd.rowData.retainedTarget).Refines
      (data.vertexPartition wall) :=
    refines_of_mem_incidentEdges data cd.rowData.target_mem
  have hReprRel : ¬ (data.vertexPartition wall).Rel geometry.growAnchor
      (data.sourceEdge cd.rowData.retainedTarget sheet).1.2 := by
    intro hBad
    exact hRel (hBad.trans (hRefines.rel
      ((data.edgePartition cd.rowData.retainedTarget).rel_repr_left
        sheet)))
  refine List.mem_map.mpr
    ⟨(data.sourceEdge cd.rowData.retainedTarget sheet).1.2,
      cd.mem_backgroundSheets
        ((mem_stableRowPath labelling row _).mpr
          ((oldRowOf_eq_some_iff labelling _ row).mpr ⟨hOldSurvives, hOldRow⟩))
        rfl hReprRel, ?_⟩
  refine (cd.background_newSourceEdge_eq_iff hReprRel).mpr ?_
  exact sourceEdge_of_target
    (data.sourceEdge cd.rowData.retainedTarget sheet) _ rfl

/-- No background regrown occurrence is listed twice. -/
theorem backgroundSheets_nodup (row : Option target.edges) :
    ((cd.backgroundSheets row).map
      cd.rowData.candidate.newSourceEdge).Nodup := by
  classical
  refine List.Nodup.map_on ?_ (backgroundSheetsOf_nodup geometry
    (stableRowPath_nodup labelling row) cd.rowData.retainedTarget)
  intro first hFirst second hSecond hEqual
  obtain ⟨hFirstRel, _, hFirstRepr⟩ := cd.backgroundSheets_spec hFirst
  obtain ⟨_, _, hSecondRepr⟩ := cd.backgroundSheets_spec hSecond
  have hSource := (cd.background_newSourceEdge_eq_iff hFirstRel).mp hEqual
  rw [← hFirstRepr, ← hSecondRepr, hSource]

/-! ### The whole regrown row of a member -/

/-- The member's regrown occurrences on one displayed row: those over the
distinguished block, then those over every other wall block.  This is
`W3FourStableGraph.MemberColumn.newSheets` of the member. -/
theorem regrownSheets_mem (row : Option target.edges) (sheet : Fin degree)
    (hMem : sheet ∈ cd.selectedSheets row ++ cd.backgroundSheets row) :
    cd.rowData.RegrownAt (cd.gauge.row (labelling.row.symm row)) sheet := by
  rcases List.mem_append.mp hMem with hSelected | hBackground
  · exact (cd.selected_mem row sheet hSelected).2
  · exact cd.backgroundSheets_regrownAt hBackground

theorem regrownSheets_exhaustive (row : Option target.edges) (sheet : Fin degree)
    (hRegrown : cd.rowData.RegrownAt (cd.gauge.row (labelling.row.symm row)) sheet) :
    cd.rowData.candidate.newSourceEdge sheet ∈
      (cd.selectedSheets row ++ cd.backgroundSheets row).map
        cd.rowData.candidate.newSourceEdge := by
  classical
  rw [List.map_append, List.mem_append]
  by_cases hRel : (data.vertexPartition wall).Rel geometry.growAnchor sheet
  · exact Or.inl (cd.selected_exhaustive row sheet hRel hRegrown)
  · exact Or.inr (cd.backgroundSheets_exhaustive hRel hRegrown)

theorem regrownSheets_nodup (row : Option target.edges) :
    ((cd.selectedSheets row ++ cd.backgroundSheets row).map
      cd.rowData.candidate.newSourceEdge).Nodup := by
  classical
  rw [List.map_append]
  refine List.Nodup.append (cd.selected_nodup row) (cd.backgroundSheets_nodup row) ?_
  intro item hSelected hBackground
  obtain ⟨first, hFirst, hFirstEq⟩ := List.mem_map.mp hSelected
  obtain ⟨second, hSecond, hSecondEq⟩ := List.mem_map.mp hBackground
  obtain ⟨hFirstRel, _⟩ := cd.selected_mem row first hFirst
  obtain ⟨hSecondRel, _, _⟩ := cd.backgroundSheets_spec hSecond
  exact cd.background_of_newSourceEdge_eq hSecondRel
    (hSecondEq.trans hFirstEq.symm) hFirstRel

/-! ### The presented matrix of a member is that member's own matrix -/

/-- The composite row correspondence: a presented row label names a stable row
of the limit, the gauge carries it to the member's own base, and the member's
occurrence-induced row descent carries it to the member's own stable row. -/
noncomputable def rowEquiv :
    Option target.edges ≃ StablePath cd.rowData.candidate.datum :=
  labelling.row.symm.trans (cd.gauge.row.trans cd.rowData.stablePathEquiv)

@[simp] theorem rowEquiv_apply (row : Option target.edges) :
    cd.rowEquiv row =
      cd.rowData.stablePathEquiv (cd.gauge.row (labelling.row.symm row)) := rfl

/-- **The regrown column of the presented matrix is the member's own.** -/
theorem presented_matrix_none (row : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix
        (soloPresentation cd.memberColumn (stableRowPath labelling)) row none =
      matrix cd.rowData.candidate.datum (cd.rowEquiv row)
        (occurrenceEquiv target wall cd.rowData.candidate.right none) := by
  rw [solo_matrix_none, rowEquiv_apply,
    cd.rowData.matrix_new (cd.gauge.row (labelling.row.symm row))
      (cd.selectedSheets row ++ cd.backgroundSheets row)
      (cd.regrownSheets_mem row) (cd.regrownSheets_exhaustive row)
      (cd.regrownSheets_nodup row)]
  rfl

/-- **Every retained column of the presented matrix is the member's own.** -/
theorem presented_matrix_some (row : Option target.edges) (column : target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix
        (soloPresentation cd.memberColumn (stableRowPath labelling)) row
        (some column) =
      matrix cd.rowData.candidate.datum (cd.rowEquiv row)
        (occurrenceEquiv target wall cd.rowData.candidate.right
          (some column)) := by
  rw [solo_matrix_some, rowEquiv_apply,
    cd.rowData.matrix_retained (cd.gauge.row (labelling.row.symm row)) column,
    cd.gauge.matrix_gauge (labelling.row.symm row) column,
    columnSum_stableRowPath labelling row column]

/-- **A Figure 28 member's presented matrix is that member's own natural
stable-length matrix.**  This is the `W4OutgoingLimitMatrix.presented_matrix_eq`
analogue for the `w3Four` case: the retained columns through
`LimitChainCore.SelectedData.matrix_retained`, the regrown column through
`matrix_new`, and the gauge through `Gauge.matrix_gauge`.  No cardinality
bijection is used anywhere. -/
theorem presented_matrix_eq (row column : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix
        (soloPresentation cd.memberColumn (stableRowPath labelling)) row column =
      matrix cd.rowData.candidate.datum (cd.rowEquiv row)
        (occurrenceEquiv target wall cd.rowData.candidate.right column) := by
  cases column with
  | none => exact cd.presented_matrix_none row
  | some place => exact cd.presented_matrix_some row place

/-- The same as one matrix equation. -/
theorem presented_matrix_submatrix :
    GluingDatum.LengthMatrixPresentation.matrix
        (soloPresentation cd.memberColumn (stableRowPath labelling)) =
      (matrix cd.rowData.candidate.datum).submatrix cd.rowEquiv
        (occurrenceEquiv target wall cd.rowData.candidate.right) := by
  ext row column
  exact cd.presented_matrix_eq row column

end ColumnData

/-! ## Figure 28's `M⁽³⁾` and `M⁽⁴⁾`: the grow members

A grow member lives on the incoming datum itself, so its gauge is the identity
and its regrown occurrences over `A₀` are a single class: every other selected
new occurrence dangles
(`W3FourSurvival.GrowMember.new_dangles_of_separate`), and the surviving one
lies in `e₂`'s own stable row
(`W3FourSurvival.GrowMember.new_grow_stablePath`, already packaged by the row
data). -/

section GrowMember

variable {star : ThreeStar target wall} {input : W3SourceInput data star}

/-- The limit row displaying a grow member's own smaller survivor. -/
noncomputable def growRow (labelling : StablePathLabelling data)
    (grown : W3FourSourceCandidates.GrowProfile input)
    (survival : SelectedSurvival data wall (ofGrowProfile grown)) :
    Option target.edges :=
  labelling.row (NonDanglingEdge.stablePath
    (⟨data.sourceEdge grown.growTarget grown.growAnchor,
      survival.grow_survives⟩ : NonDanglingEdge data))

/-- A grow member's selected regrown occurrence represents `e₂`. -/
theorem grow_newOldSourceEdge (grown : W3FourSourceCandidates.GrowProfile input)
    (survival : SelectedSurvival data wall (ofGrowProfile grown))
    (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel grown.growAnchor sheet) :
    (W3FourRowDescent.GrowMember.rowData grown survival hValid).newOldSourceEdge
        sheet =
      data.sourceEdge grown.growTarget grown.growAnchor :=
  (W3FourRowDescent.GrowMember.rowData grown survival
    hValid).newOldSourceEdge_selected hSheet

/-- **A grow member has exactly one surviving regrown occurrence over `A₀`.**
Every selected sheet separated from the enlarged class regrows into a dangling
occurrence. -/
theorem grow_newSourceEdge_eq (grown : W3FourSourceCandidates.GrowProfile input)
    (survival : SelectedSurvival data wall (ofGrowProfile grown))
    (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel grown.growAnchor sheet)
    (hSurvives : ¬ IsDangling grown.growCandidate.datum
      (grown.growCandidate.newSourceEdge sheet)) :
    grown.growCandidate.newSourceEdge sheet =
      grown.growCandidate.newSourceEdge grown.growAnchor := by
  have hRel : grown.growPartition.Rel sheet grown.growAnchor := by
    by_contra hSeparate
    exact hSurvives (W3FourSurvival.GrowMember.new_dangles_of_separate grown
      survival hValid hSheet hSeparate)
  exact W3FourSurvival.GrowMember.newSourceEdge_eq_of_rel grown rfl hRel.symm

/-- **`M⁽³⁾` and `M⁽⁴⁾`, packaged for the regrown column.**  One `GrowProfile`
serves both, exactly as in `W3FourRowDescent`. -/
noncomputable def growColumnData (grown : W3FourSourceCandidates.GrowProfile input)
    (survival : SelectedSurvival data wall (ofGrowProfile grown))
    (hValid : data.Valid) (geometry : FourStarGeometry data wall)
    (labelling : StablePathLabelling data)
    (hAnchor : (data.vertexPartition wall).Rel geometry.growAnchor
      grown.growAnchor)
    (displayedRow : Option target.edges)
    (hDisplayedRow : displayedRow = growRow labelling grown survival)
    (anchor : Fin degree) (hAnchorEq : anchor = grown.growAnchor) :
    ColumnData data wall geometry labelling where
  base := data
  gauge := Gauge.refl data wall
  rowData := W3FourRowDescent.GrowMember.rowData grown survival hValid
  anchor_rel := hAnchor
  background_sourceEdge := fun _ ↦ rfl
  selectedSheets := single displayedRow anchor
  selected_mem := by
    subst hDisplayedRow
    subst hAnchorEq
    intro row sheet hMem
    simp only [single] at hMem
    split_ifs at hMem with hRow
    · rw [List.mem_singleton] at hMem
      subst hMem
      subst hRow
      refine ⟨hAnchor, W3FourSurvival.GrowMember.new_grow_survives grown survival
        hValid, ?_⟩
      have hValue : (W3FourRowDescent.GrowMember.rowData grown survival
              hValid).newOldEdge grown.growAnchor
            (W3FourSurvival.GrowMember.new_grow_survives grown survival hValid) =
          (⟨data.sourceEdge grown.growTarget grown.growAnchor,
            survival.grow_survives⟩ : NonDanglingEdge data) :=
        Subtype.ext (grow_newOldSourceEdge grown survival hValid rfl)
      refine Eq.trans (congrArg NonDanglingEdge.stablePath hValue) ?_
      exact (labelling.row.symm_apply_apply _).symm
    · exact absurd hMem (by simp)
  selected_nodup := by
    intro row
    simp only [single]
    split_ifs <;> simp
  selected_exhaustive := by
    subst hDisplayedRow
    subst hAnchorEq
    intro row sheet hRel hRegrown
    obtain ⟨hSurvives, hRow⟩ := hRegrown
    have hSheet : (data.vertexPartition wall).Rel grown.growAnchor sheet :=
      hAnchor.symm.trans hRel
    have hEqual := grow_newSourceEdge_eq grown survival hValid hSheet hSurvives
    have hPath : NonDanglingEdge.stablePath
        (⟨data.sourceEdge grown.growTarget grown.growAnchor,
          survival.grow_survives⟩ : NonDanglingEdge data) =
        labelling.row.symm row :=
      Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext
        (grow_newOldSourceEdge grown survival hValid hSheet).symm)) hRow
    have hRowEq : growRow labelling grown survival = row := by
      rw [growRow, hPath, Equiv.apply_symm_apply]
    subst hRowEq
    have hList : single (growRow labelling grown survival) grown.growAnchor
        (growRow labelling grown survival) = [grown.growAnchor] := by
      simp [single]
    rw [hList]
    exact List.mem_singleton.mpr hEqual

end GrowMember

/-! ## Reading a limit row off the member's own base

`M⁽¹⁾` and `M⁽²⁾` live on branch-swapped copies, so the rows their regrown
occurrences sit in are rows of the *copy*.  The gauge carries them back. -/

section GaugeRows

/-- The limit row a surviving occurrence of the member's base lies over. -/
noncomputable def gaugeRow (labelling : StablePathLabelling data)
    (gauge : Gauge data base wall) {edge : base.SourceEdge}
    (hSurvives : ¬ IsDangling base edge) : Option target.edges :=
  labelling.row (gauge.row.symm
    (NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge base)))

theorem gauge_row_gaugeRow (labelling : StablePathLabelling data)
    (gauge : Gauge data base wall) {edge : base.SourceEdge}
    (hSurvives : ¬ IsDangling base edge) :
    gauge.row (labelling.row.symm (gaugeRow labelling gauge hSurvives)) =
      NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge base) := by
  rw [gaugeRow, labelling.row.symm_apply_apply, gauge.row.apply_symm_apply]

theorem gaugeRow_eq (labelling : StablePathLabelling data)
    (gauge : Gauge data base wall) {edge : base.SourceEdge}
    (hSurvives : ¬ IsDangling base edge) {row : Option target.edges}
    (hRow : NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge base) =
      gauge.row (labelling.row.symm row)) :
    gaugeRow labelling gauge hSurvives = row := by
  rw [gaugeRow, hRow, gauge.row.symm_apply_apply, labelling.row.apply_symm_apply]

end GaugeRows

/-! ## Figure 28's `M⁽²⁾`: Position II.b

The detached singleton new occurrence dangles, so the member displays exactly
one regrown occurrence over `A₀`, in the row of `e₄`. -/

section PositionTwo

/-- `M⁽²⁾`'s selected regrown occurrence represents `e₄`. -/
theorem positionTwo_newOldSourceEdge
    (position : W3FourClosure.PositionTwo base wall)
    (survival : SelectedSurvival base wall position.toFourStarGeometry)
    (hValid : base.Valid) {sheet : Fin degree}
    (hSheet : (base.vertexPartition wall).Rel position.growAnchor sheet) :
    (W3FourRowDescent.PositionTwo.rowData position survival hValid).newOldSourceEdge
        sheet =
      base.sourceEdge position.largestTarget position.largestAnchor :=
  (W3FourRowDescent.PositionTwo.rowData position survival
    hValid).newOldSourceEdge_selected hSheet

/-- **`M⁽²⁾`, packaged for the regrown column.** -/
noncomputable def positionTwoColumnData
    (position : W3FourClosure.PositionTwo base wall)
    (survival : SelectedSurvival base wall position.toFourStarGeometry)
    (hValid : base.Valid) (geometry : FourStarGeometry data wall)
    (labelling : StablePathLabelling data) (gauge : Gauge data base wall)
    (hAnchor : (data.vertexPartition wall).Rel geometry.growAnchor
      position.growAnchor)
    (hBackground : ∀ sheet : Fin degree,
      base.sourceEdge position.largestTarget sheet =
        gauge.edge (data.sourceEdge position.largestTarget sheet))
    (displayedRow : Option target.edges)
    (hDisplayedRow : displayedRow =
      gaugeRow labelling gauge survival.largest_survives)
    (anchor : Fin degree) (hAnchorEq : anchor = position.growAnchor) :
    ColumnData data wall geometry labelling where
  base := base
  gauge := gauge
  rowData := W3FourRowDescent.PositionTwo.rowData position survival hValid
  anchor_rel := hAnchor
  background_sourceEdge := hBackground
  selectedSheets := single displayedRow anchor
  selected_mem := by
    subst hDisplayedRow
    subst hAnchorEq
    intro row sheet hMem
    simp only [single] at hMem
    split_ifs at hMem with hRow
    · rw [List.mem_singleton] at hMem
      subst hMem
      subst hRow
      refine ⟨hAnchor, W3FourSurvival.PositionTwo.new_grow_survives position
        survival hValid, ?_⟩
      have hValue : (W3FourRowDescent.PositionTwo.rowData position survival
              hValid).newOldEdge position.growAnchor
            (W3FourSurvival.PositionTwo.new_grow_survives position survival
              hValid) =
          (⟨base.sourceEdge position.largestTarget position.largestAnchor,
            survival.largest_survives⟩ : NonDanglingEdge base) :=
        Subtype.ext (positionTwo_newOldSourceEdge position survival hValid rfl)
      refine Eq.trans (congrArg NonDanglingEdge.stablePath hValue) ?_
      exact (gauge_row_gaugeRow labelling gauge survival.largest_survives).symm
    · exact absurd hMem (by simp)
  selected_nodup := by
    intro row
    simp only [single]
    split_ifs <;> simp
  selected_exhaustive := by
    subst hDisplayedRow
    subst hAnchorEq
    intro row sheet hRel hRegrown
    obtain ⟨hSurvives, hRow⟩ := hRegrown
    have hSheet : (base.vertexPartition wall).Rel position.growAnchor sheet := by
      rw [gauge.wall_eq]
      exact hAnchor.symm.trans hRel
    have hEqual := W3FourSurvival.PositionTwo.newSourceEdge_eq_of_survives position
      survival hValid sheet hSheet hSurvives
    have hValue : (⟨base.sourceEdge position.largestTarget
          position.largestAnchor, survival.largest_survives⟩ :
            NonDanglingEdge base) =
        (W3FourRowDescent.PositionTwo.rowData position survival hValid).newOldEdge
          sheet hSurvives :=
      Subtype.ext (positionTwo_newOldSourceEdge position survival hValid
        hSheet).symm
    have hPath : NonDanglingEdge.stablePath
        (⟨base.sourceEdge position.largestTarget position.largestAnchor,
          survival.largest_survives⟩ : NonDanglingEdge base) =
        gauge.row (labelling.row.symm row) :=
      Eq.trans (congrArg NonDanglingEdge.stablePath hValue) hRow
    have hRowEq := gaugeRow_eq labelling gauge survival.largest_survives hPath
    subst hRowEq
    have hList : single (gaugeRow labelling gauge survival.largest_survives)
        position.growAnchor
        (gaugeRow labelling gauge survival.largest_survives) =
        [position.growAnchor] := by
      simp [single]
    rw [hList]
    exact List.mem_singleton.mpr hEqual

end PositionTwo

/-! ## Figure 28's `M⁽¹⁾`: Position I

`fine` splits `A₀` into `e₂` and `e₃`, so **both** selected new occurrences
survive, and the member displays two regrown occurrences over `A₀`, in the rows
of `e₂` and `e₃`.  They are distinct occurrences
(`W3FourSurvival.PositionOne.new_grow_ne_new_other`), which is why
`det_one` has two selected terms. -/

section PositionOne

/-- `M⁽¹⁾`'s regrown occurrence on `e₂`'s side represents `e₂`. -/
theorem positionOne_newOldSourceEdge_grow
    (position : W3FourClosure.PositionOne base wall)
    (survival : SelectedSurvival base wall position.toFourStarGeometry)
    (hValid : base.Valid) {sheet : Fin degree}
    (hSheet : (base.vertexPartition wall).Rel position.growAnchor sheet)
    (hGrow : position.fine.Rel sheet position.growAnchor) :
    (W3FourRowDescent.PositionOne.rowData position survival hValid).newOldSourceEdge
        sheet =
      base.sourceEdge position.growTarget position.growAnchor := by
  rw [(W3FourRowDescent.PositionOne.rowData position survival
    hValid).newOldSourceEdge_selected hSheet]
  exact W3FourRowDescent.PositionOne.rep_of_grow position hGrow

/-- and the one on `e₃`'s side represents `e₃`. -/
theorem positionOne_newOldSourceEdge_other
    (position : W3FourClosure.PositionOne base wall)
    (survival : SelectedSurvival base wall position.toFourStarGeometry)
    (hValid : base.Valid) {sheet : Fin degree}
    (hSheet : (base.vertexPartition wall).Rel position.growAnchor sheet)
    (hGrow : ¬ position.fine.Rel sheet position.growAnchor) :
    (W3FourRowDescent.PositionOne.rowData position survival hValid).newOldSourceEdge
        sheet =
      base.sourceEdge position.otherTarget position.otherAnchor := by
  rw [(W3FourRowDescent.PositionOne.rowData position survival
    hValid).newOldSourceEdge_selected hSheet]
  exact W3FourRowDescent.PositionOne.rep_of_not_grow position hGrow

/-- **`M⁽¹⁾`, packaged for the regrown column.** -/
noncomputable def positionOneColumnData
    (position : W3FourClosure.PositionOne base wall)
    (survival : SelectedSurvival base wall position.toFourStarGeometry)
    (hValid : base.Valid) (geometry : FourStarGeometry data wall)
    (labelling : StablePathLabelling data) (gauge : Gauge data base wall)
    (hAnchor : (data.vertexPartition wall).Rel geometry.growAnchor
      position.growAnchor)
    (hBackground : ∀ sheet : Fin degree,
      base.sourceEdge position.largestTarget sheet =
        gauge.edge (data.sourceEdge position.largestTarget sheet))
    (rowGrow rowOther : Option target.edges)
    (hRowGrow : rowGrow = gaugeRow labelling gauge survival.grow_survives)
    (hRowOther : rowOther = gaugeRow labelling gauge survival.other_survives)
    (anchorGrow anchorOther : Fin degree)
    (hAnchorGrow : anchorGrow = position.growAnchor)
    (hAnchorOther : anchorOther = position.otherAnchor) :
    ColumnData data wall geometry labelling where
  base := base
  gauge := gauge
  rowData := W3FourRowDescent.PositionOne.rowData position survival hValid
  anchor_rel := hAnchor
  background_sourceEdge := hBackground
  selectedSheets := fun row ↦
    single rowGrow anchorGrow row ++ single rowOther anchorOther row
  selected_mem := by
    subst hRowGrow
    subst hRowOther
    subst hAnchorGrow
    subst hAnchorOther
    have hOtherAnchor : (data.vertexPartition wall).Rel geometry.growAnchor
        position.otherAnchor := by
      refine hAnchor.trans ?_
      rw [← gauge.wall_eq]
      exact position.other_wall_rel
    intro row sheet hMem
    rcases List.mem_append.mp hMem with hGrowMem | hOtherMem
    · simp only [single] at hGrowMem
      split_ifs at hGrowMem with hRow
      · rw [List.mem_singleton] at hGrowMem
        subst hGrowMem
        subst hRow
        refine ⟨hAnchor, W3FourSurvival.PositionOne.new_grow_survives position
          survival hValid, ?_⟩
        have hValue : (W3FourRowDescent.PositionOne.rowData position survival
                hValid).newOldEdge position.growAnchor
              (W3FourSurvival.PositionOne.new_grow_survives position survival
                hValid) =
            (⟨base.sourceEdge position.growTarget position.growAnchor,
              survival.grow_survives⟩ : NonDanglingEdge base) :=
          Subtype.ext (positionOne_newOldSourceEdge_grow position survival hValid
            rfl rfl)
        refine Eq.trans (congrArg NonDanglingEdge.stablePath hValue) ?_
        exact (gauge_row_gaugeRow labelling gauge survival.grow_survives).symm
      · exact absurd hGrowMem (by simp)
    · simp only [single] at hOtherMem
      split_ifs at hOtherMem with hRow
      · rw [List.mem_singleton] at hOtherMem
        subst hOtherMem
        subst hRow
        refine ⟨hOtherAnchor, W3FourSurvival.PositionOne.new_other_survives position
          survival hValid, ?_⟩
        have hValue : (W3FourRowDescent.PositionOne.rowData position survival
                hValid).newOldEdge position.otherAnchor
              (W3FourSurvival.PositionOne.new_other_survives position survival
                hValid) =
            (⟨base.sourceEdge position.otherTarget position.otherAnchor,
              survival.other_survives⟩ : NonDanglingEdge base) :=
          Subtype.ext (positionOne_newOldSourceEdge_other position survival hValid
            position.other_wall_rel
            (W3FourSurvival.PositionOne.fine_other_not_grow position))
        refine Eq.trans (congrArg NonDanglingEdge.stablePath hValue) ?_
        exact (gauge_row_gaugeRow labelling gauge survival.other_survives).symm
      · exact absurd hOtherMem (by simp)
  selected_nodup := by
    subst hRowGrow
    subst hRowOther
    subst hAnchorGrow
    subst hAnchorOther
    have hNe : position.candidate.newSourceEdge position.growAnchor ≠
        position.candidate.newSourceEdge position.otherAnchor :=
      W3FourSurvival.PositionOne.new_grow_ne_new_other position
    intro row
    simp only [single]
    split_ifs <;> simp [hNe]
  selected_exhaustive := by
    subst hRowGrow
    subst hRowOther
    subst hAnchorGrow
    subst hAnchorOther
    intro row sheet hRel hRegrown
    obtain ⟨hSurvives, hRow⟩ := hRegrown
    have hSheet : (base.vertexPartition wall).Rel position.growAnchor sheet := by
      rw [gauge.wall_eq]
      exact hAnchor.symm.trans hRel
    rcases W3FourSurvival.PositionOne.newSourceEdge_cover position hSheet with
      hCover | hCover
    · have hFine : position.fine.Rel sheet position.growAnchor :=
        (((W3FourSurvival.PositionOne.toReversedMember
          position).newSourceEdge_eq_iff_fine_rel
            (first := position.growAnchor) (second := sheet) rfl).mp
          hCover.symm).symm
      have hValue : (⟨base.sourceEdge position.growTarget position.growAnchor,
            survival.grow_survives⟩ : NonDanglingEdge base) =
          (W3FourRowDescent.PositionOne.rowData position survival
            hValid).newOldEdge sheet hSurvives :=
        Subtype.ext (positionOne_newOldSourceEdge_grow position survival hValid
          hSheet hFine).symm
      have hPath : NonDanglingEdge.stablePath
          (⟨base.sourceEdge position.growTarget position.growAnchor,
            survival.grow_survives⟩ : NonDanglingEdge base) =
          gauge.row (labelling.row.symm row) :=
        Eq.trans (congrArg NonDanglingEdge.stablePath hValue) hRow
      have hRowEq := gaugeRow_eq labelling gauge survival.grow_survives hPath
      subst hRowEq
      rw [List.map_append, List.mem_append]
      refine Or.inl ?_
      have hList : single (gaugeRow labelling gauge survival.grow_survives)
          position.growAnchor
          (gaugeRow labelling gauge survival.grow_survives) =
          [position.growAnchor] := by
        simp [single]
      rw [hList]
      exact List.mem_singleton.mpr hCover
    · have hNotGrow : ¬ position.fine.Rel sheet position.growAnchor := by
        intro hFine
        refine W3FourSurvival.PositionOne.new_grow_ne_new_other position ?_
        exact ((W3FourSurvival.PositionOne.toReversedMember
          position).newSourceEdge_eq_of_fine_rel (first := position.growAnchor)
            (second := sheet) rfl hFine.symm).symm.trans hCover
      have hValue : (⟨base.sourceEdge position.otherTarget position.otherAnchor,
            survival.other_survives⟩ : NonDanglingEdge base) =
          (W3FourRowDescent.PositionOne.rowData position survival
            hValid).newOldEdge sheet hSurvives :=
        Subtype.ext (positionOne_newOldSourceEdge_other position survival hValid
          hSheet hNotGrow).symm
      have hPath : NonDanglingEdge.stablePath
          (⟨base.sourceEdge position.otherTarget position.otherAnchor,
            survival.other_survives⟩ : NonDanglingEdge base) =
          gauge.row (labelling.row.symm row) :=
        Eq.trans (congrArg NonDanglingEdge.stablePath hValue) hRow
      have hRowEq := gaugeRow_eq labelling gauge survival.other_survives hPath
      subst hRowEq
      rw [List.map_append, List.mem_append]
      refine Or.inr ?_
      have hList : single (gaugeRow labelling gauge survival.other_survives)
          position.otherAnchor
          (gaugeRow labelling gauge survival.other_survives) =
          [position.otherAnchor] := by
        simp [single]
      rw [hList]
      exact List.mem_singleton.mpr hCover

end PositionOne

/-! ## The four members' presented matrices are their own

`W3FourStableGraph.MemberColumn.presentation` is `soloPresentation` of the
member (`presentation_eq_solo`, an identity), so the theorem below applies to
any family whose `i`-th member is one of the packaged ones and whose displayed
rows are the limit's own. -/

section Named

/-- `ColumnData.presented_matrix_eq` matched against an externally supplied
member and row family. -/
theorem presented_matrix_eq_of_eq {geometry : FourStarGeometry data wall}
    {labelling : StablePathLabelling data} (mc : MemberColumn data wall geometry)
    (oldPath : Option target.edges → List data.SourceEdge)
    (cd : ColumnData data wall geometry labelling)
    (hMember : mc = cd.memberColumn) (hOld : oldPath = stableRowPath labelling)
    (row column : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix (soloPresentation mc oldPath) row
        column =
      matrix cd.rowData.candidate.datum (cd.rowEquiv row)
        (occurrenceEquiv target wall cd.rowData.candidate.right column) := by
  subst hMember
  subst hOld
  exact cd.presented_matrix_eq row column

variable {star : ThreeStar target wall} {input : W3SourceInput data star}

/-- **`M⁽³⁾` and `M⁽⁴⁾`: the presented matrix is the member's own natural
stable-length matrix.** -/
theorem growMember_presented_matrix_eq
    (grown : W3FourSourceCandidates.GrowProfile input)
    (survival : SelectedSurvival data wall (ofGrowProfile grown))
    (hValid : data.Valid) (geometry : FourStarGeometry data wall)
    (labelling : StablePathLabelling data)
    (hAnchor : (data.vertexPartition wall).Rel geometry.growAnchor
      grown.growAnchor)
    (displayedRow : Option target.edges)
    (hDisplayedRow : displayedRow = growRow labelling grown survival)
    (anchor : Fin degree) (hAnchorEq : anchor = grown.growAnchor)
    (row column : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix
        (soloPresentation (growColumnData grown survival hValid geometry labelling
          hAnchor displayedRow hDisplayedRow anchor hAnchorEq).memberColumn
          (stableRowPath labelling)) row column =
      matrix grown.growCandidate.datum
        ((growColumnData grown survival hValid geometry labelling hAnchor
          displayedRow hDisplayedRow anchor hAnchorEq).rowEquiv row)
        (occurrenceEquiv target wall grown.growCandidate.right column) :=
  ColumnData.presented_matrix_eq _ row column

/-- **`M⁽²⁾`: the presented matrix is the member's own natural stable-length
matrix.** -/
theorem positionTwo_presented_matrix_eq
    (position : W3FourClosure.PositionTwo base wall)
    (survival : SelectedSurvival base wall position.toFourStarGeometry)
    (hValid : base.Valid) (geometry : FourStarGeometry data wall)
    (labelling : StablePathLabelling data) (gauge : Gauge data base wall)
    (hAnchor : (data.vertexPartition wall).Rel geometry.growAnchor
      position.growAnchor)
    (hBackground : ∀ sheet : Fin degree,
      base.sourceEdge position.largestTarget sheet =
        gauge.edge (data.sourceEdge position.largestTarget sheet))
    (displayedRow : Option target.edges)
    (hDisplayedRow : displayedRow =
      gaugeRow labelling gauge survival.largest_survives)
    (anchor : Fin degree) (hAnchorEq : anchor = position.growAnchor)
    (row column : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix
        (soloPresentation (positionTwoColumnData position survival hValid geometry
          labelling gauge hAnchor hBackground displayedRow hDisplayedRow anchor
          hAnchorEq).memberColumn (stableRowPath labelling)) row column =
      matrix position.candidate.datum
        ((positionTwoColumnData position survival hValid geometry labelling gauge
          hAnchor hBackground displayedRow hDisplayedRow anchor hAnchorEq).rowEquiv
          row)
        (occurrenceEquiv target wall position.candidate.right column) :=
  ColumnData.presented_matrix_eq _ row column

/-- **`M⁽¹⁾`: the presented matrix is the member's own natural stable-length
matrix.** -/
theorem positionOne_presented_matrix_eq
    (position : W3FourClosure.PositionOne base wall)
    (survival : SelectedSurvival base wall position.toFourStarGeometry)
    (hValid : base.Valid) (geometry : FourStarGeometry data wall)
    (labelling : StablePathLabelling data) (gauge : Gauge data base wall)
    (hAnchor : (data.vertexPartition wall).Rel geometry.growAnchor
      position.growAnchor)
    (hBackground : ∀ sheet : Fin degree,
      base.sourceEdge position.largestTarget sheet =
        gauge.edge (data.sourceEdge position.largestTarget sheet))
    (rowGrow rowOther : Option target.edges)
    (hRowGrow : rowGrow = gaugeRow labelling gauge survival.grow_survives)
    (hRowOther : rowOther = gaugeRow labelling gauge survival.other_survives)
    (anchorGrow anchorOther : Fin degree)
    (hAnchorGrow : anchorGrow = position.growAnchor)
    (hAnchorOther : anchorOther = position.otherAnchor)
    (row column : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix
        (soloPresentation (positionOneColumnData position survival hValid geometry
          labelling gauge hAnchor hBackground rowGrow rowOther hRowGrow hRowOther
          anchorGrow anchorOther hAnchorGrow hAnchorOther).memberColumn
          (stableRowPath labelling)) row column =
      matrix position.candidate.datum
        ((positionOneColumnData position survival hValid geometry labelling gauge
          hAnchor hBackground rowGrow rowOther hRowGrow hRowOther anchorGrow
          anchorOther hAnchorGrow hAnchorOther).rowEquiv row)
        (occurrenceEquiv target wall position.candidate.right column) :=
  ColumnData.presented_matrix_eq _ row column

/-- **Honesty of a presented matrix**: it *is* the candidate's own natural
stable-length matrix, in some relabelling of the stable rows and the canonical
relabelling of the columns.  This is the property
`W4OutgoingLimitMatrix.presented_matrix_submatrix` asserts in the W4 case. -/
def IsHonest {b : GluingDatum target degree}
    (candidate : Candidate target degree b wall)
    (presentation : candidate.datum.LengthMatrixPresentation
      (Option target.edges)) : Prop :=
  ∃ rowEquiv : Option target.edges ≃ StablePath candidate.datum,
    GluingDatum.LengthMatrixPresentation.matrix presentation =
      (matrix candidate.datum).submatrix rowEquiv
        (occurrenceEquiv target wall candidate.right)

/-- Every packaged member is honest. -/
theorem ColumnData.isHonest {geometry : FourStarGeometry data wall}
    {labelling : StablePathLabelling data}
    (cd : ColumnData data wall geometry labelling) :
    IsHonest cd.memberColumn.candidate
      (soloPresentation cd.memberColumn (stableRowPath labelling)) :=
  ⟨cd.rowEquiv, cd.presented_matrix_submatrix⟩

/-- and so is any member matched to a packaged one over the limit's own
rows. -/
theorem isHonest_of_eq {geometry : FourStarGeometry data wall}
    {labelling : StablePathLabelling data} (mc : MemberColumn data wall geometry)
    (oldPath : Option target.edges → List data.SourceEdge)
    (cd : ColumnData data wall geometry labelling)
    (hMember : mc = cd.memberColumn) (hOld : oldPath = stableRowPath labelling) :
    IsHonest mc.candidate (soloPresentation mc oldPath) := by
  subst hMember
  subst hOld
  exact cd.isHonest

end Named

/-! ## Figure 28's receipts, over honest matrices

`W3FourStableGraph.exists_figure28Receipts` built the four members and every
`background_*` and `index_*` receipt; `W3FourLimitRows.exists_figure28Receipts_of_input`
supplied the limit's own rows.  What neither could say is that the presented
matrices are the members' own.  They are. -/

section Figure28

variable {star : ThreeStar target wall} {input : W3SourceInput data star}

/-- The limit row of a surviving incoming occurrence, named from the member's
own base through the gauge. -/
theorem gaugeRow_eq_of_edge (labelling : StablePathLabelling data)
    (gauge : Gauge data base wall) {image : base.SourceEdge}
    (hImageSurvives : ¬ IsDangling base image) {edge : data.SourceEdge}
    (hSurvives : ¬ IsDangling data edge) (hEdge : image = gauge.edge edge) :
    gaugeRow labelling gauge hImageSurvives =
      labelling.row (NonDanglingEdge.stablePath
        (⟨edge, hSurvives⟩ : NonDanglingEdge data)) := by
  have hImage : ¬ IsDangling base (gauge.edge edge) := fun hDangling ↦
    hSurvives ((gauge.isDangling_iff edge).mp hDangling)
  have hValue : (⟨image, hImageSurvives⟩ : NonDanglingEdge base) =
      (⟨gauge.edge edge, hImage⟩ : NonDanglingEdge base) := Subtype.ext hEdge
  refine gaugeRow_eq labelling gauge hImageSurvives ?_
  rw [labelling.row.symm_apply_apply]
  exact (congrArg NonDanglingEdge.stablePath hValue).trans
    (gauge.row_mk edge hSurvives).symm

/-- A grow member's displayed row is the limit's own row of `e₂`. -/
theorem growRow_eq_rowOf (labelling : StablePathLabelling data)
    (grown : W3FourSourceCandidates.GrowProfile input)
    (survival : SelectedSurvival data wall (ofGrowProfile grown))
    (hSurvives : ¬ IsDangling data grown.grow.1) :
    growRow labelling grown survival =
      labelling.row (NonDanglingEdge.stablePath
        (⟨grown.grow.1, hSurvives⟩ : NonDanglingEdge data)) :=
  congrArg labelling.row (congrArg NonDanglingEdge.stablePath
    (Subtype.ext (GluingDatum.sourceEdge_self data grown.grow.1)))

/-- **Figure 28's four members, with their presented matrices proved honest.**

Same hypotheses as `W3FourStableGraph.exists_figure28Receipts` together with
`data.Valid`, with the rows fixed to the limit's own
(`W3FourLimitRows.limitRowsOfInput`) and one further conclusion: each member's
presented matrix **is** that member's own `StableSourceMatrix.matrix`, read
through a bijection of the stable rows and the canonical bijection of the
columns.  With `W3FourRowDescent`'s retained half this is the whole of the
limit-matrix identification for case `{w3-r1-nd3-t2-(a=k₄)}`. -/
theorem exists_figure28Receipts_honest (hValid : data.Valid)
    (profile : W3R1SourceProfile.Nd3Profile data input.distinguishedBlock)
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
        (ofGrowProfile
          (W3FourSourceCandidates.growProfileFirst profile directions
            largest_index)),
      receipts.rows =
          limitRowsOfInput
            (W3FourSourceCandidates.growProfileFirst profile directions
              largest_index) ∧
        HEq (receipts.member 2).candidate
          (W3FourSourceCandidates.thirdCandidate profile directions
            largest_index) ∧
        HEq (receipts.member 3).candidate
          (W3FourSourceCandidates.fourthCandidate profile directions
            largest_index) ∧
        ∀ i : Fin 4,
          IsHonest (receipts.member i).candidate (receipts.presentation i) := by
  classical
  let grownFirst := W3FourSourceCandidates.growProfileFirst profile directions
    largest_index
  let grownSecond := W3FourSourceCandidates.growProfileSecond profile directions
    largest_index
  let geometry : FourStarGeometry data wall := ofGrowProfile grownFirst
  let labelling : StablePathLabelling data :=
    StablePathLabelling.ofCardEq data input.stablePath_card
  let rows : LimitRows data wall geometry := limitRowsOfInput grownFirst
  obtain ⟨permOne, hFixOne, positionOne, hGaugeOne, hGeomOne, _, _,
    hIndexOneGrow, hIndexOneOther⟩ :=
    W3FourClosure.exists_member_one geometry root hRoot hGrowFixed hLargestFixed
      hOtherMoved
  obtain ⟨permTwo, hFixTwo, positionTwo, hGaugeTwo, hGeomTwo, _, _, hIndexTwo⟩ :=
    W3FourClosure.exists_member_two geometry root hRoot hGrowFixed hLargestFixed
      hOtherMoved
  have hWallOne := W3FourDisjointness.branchSwapOfPerm_vertexPartition_wall data
    wall root hRoot permOne hFixOne
  have hWallTwo := W3FourDisjointness.branchSwapOfPerm_vertexPartition_wall data
    wall root hRoot permTwo hFixTwo
  let gaugeOne : Gauge data
      (W3FourDisjointness.branchSwapOfPerm data wall root hRoot permOne
        hFixOne).apply wall :=
    Gauge.ofSheetRelabeling (W3FourDisjointness.branchSwapOfPerm data wall root
      hRoot permOne hFixOne) hValid.1 hWallOne
  let gaugeTwo : Gauge data
      (W3FourDisjointness.branchSwapOfPerm data wall root hRoot permTwo
        hFixTwo).apply wall :=
    Gauge.ofSheetRelabeling (W3FourDisjointness.branchSwapOfPerm data wall root
      hRoot permTwo hFixTwo) hValid.1 hWallTwo
  have hAnchorOne : positionOne.toFourStarGeometry.growAnchor =
      geometry.growAnchor := congrArg FourStarGeometry.growAnchor hGeomOne
  have hAnchorTwo : positionTwo.toFourStarGeometry.growAnchor =
      geometry.growAnchor := congrArg FourStarGeometry.growAnchor hGeomTwo
  have hGrowTargetOne : positionOne.toFourStarGeometry.growTarget =
      geometry.growTarget := congrArg FourStarGeometry.growTarget hGeomOne
  have hOtherTargetOne : positionOne.toFourStarGeometry.otherTarget =
      geometry.otherTarget := congrArg FourStarGeometry.otherTarget hGeomOne
  have hOtherAnchorOne : positionOne.toFourStarGeometry.otherAnchor =
      permOne geometry.otherAnchor :=
    congrArg FourStarGeometry.otherAnchor hGeomOne
  have hLargestOne : positionOne.toFourStarGeometry.largestTarget =
      geometry.largestTarget := congrArg FourStarGeometry.largestTarget hGeomOne
  have hLargestTwo : positionTwo.toFourStarGeometry.largestTarget =
      geometry.largestTarget := congrArg FourStarGeometry.largestTarget hGeomTwo
  have hLargestAnchorTwo : positionTwo.toFourStarGeometry.largestAnchor =
      geometry.largestAnchor :=
    congrArg FourStarGeometry.largestAnchor hGeomTwo
  have survivalOne : SelectedSurvival
      (W3FourDisjointness.branchSwapOfPerm data wall root hRoot permOne
        hFixOne).apply wall positionOne.toFourStarGeometry := by
    rw [hGeomOne]
    exact SelectedSurvival.swap geometry root hRoot permOne hFixOne
      (SelectedSurvival.ofGrowProfile grownFirst) hValid.1 hGrowFixed
      hLargestFixed hOtherMoved
  have survivalTwo : SelectedSurvival
      (W3FourDisjointness.branchSwapOfPerm data wall root hRoot permTwo
        hFixTwo).apply wall positionTwo.toFourStarGeometry := by
    rw [hGeomTwo]
    exact SelectedSurvival.swap geometry root hRoot permTwo hFixTwo
      (SelectedSurvival.ofGrowProfile grownFirst) hValid.1 hGrowFixed
      hLargestFixed hOtherMoved
  have hValidOne := hGaugeOne.valid hValid
  have hValidTwo := hGaugeTwo.valid hValid
  have hBackgroundOne : ∀ sheet : Fin degree,
      (W3FourDisjointness.branchSwapOfPerm data wall root hRoot permOne
          hFixOne).apply.sourceEdge positionOne.largestTarget sheet =
        gaugeOne.edge (data.sourceEdge positionOne.largestTarget sheet) := by
    intro sheet
    rw [hLargestOne]
    exact branchSwap_sourceEdge_of_fixed root hRoot permOne hFixOne
      geometry.largestTarget hLargestFixed sheet
  have hBackgroundTwo : ∀ sheet : Fin degree,
      (W3FourDisjointness.branchSwapOfPerm data wall root hRoot permTwo
          hFixTwo).apply.sourceEdge positionTwo.largestTarget sheet =
        gaugeTwo.edge (data.sourceEdge positionTwo.largestTarget sheet) := by
    intro sheet
    rw [hLargestTwo]
    exact branchSwap_sourceEdge_of_fixed root hRoot permTwo hFixTwo
      geometry.largestTarget hLargestFixed sheet
  have hRowGrowOne : rows.rowGrow =
      gaugeRow labelling gaugeOne survivalOne.grow_survives := by
    refine (gaugeRow_eq_of_edge labelling gaugeOne survivalOne.grow_survives
      (W3FourLimitRows.grow_survives grownFirst) ?_).symm
    rw [hGrowTargetOne, hAnchorOne, branchSwap_sourceEdge_of_fixed root hRoot
      permOne hFixOne geometry.growTarget hGrowFixed geometry.growAnchor]
    exact congrArg gaugeOne.edge (GluingDatum.sourceEdge_self data grownFirst.grow.1)
  have hRowOtherOne : rows.rowOther =
      gaugeRow labelling gaugeOne survivalOne.other_survives := by
    refine (gaugeRow_eq_of_edge labelling gaugeOne survivalOne.other_survives
      (W3FourLimitRows.other_survives grownFirst) ?_).symm
    rw [hOtherTargetOne, hOtherAnchorOne, branchSwap_sourceEdge_of_moved root hRoot
      permOne hFixOne geometry.otherTarget hOtherMoved geometry.otherAnchor]
    exact congrArg gaugeOne.edge
      (GluingDatum.sourceEdge_self data grownFirst.other.1)
  have hRowLargestTwo : rows.rowLargest =
      gaugeRow labelling gaugeTwo survivalTwo.largest_survives := by
    refine (gaugeRow_eq_of_edge labelling gaugeTwo survivalTwo.largest_survives
      (W3FourLimitRows.largest_survives grownFirst) ?_).symm
    rw [hLargestTwo, hLargestAnchorTwo, branchSwap_sourceEdge_of_fixed root hRoot
      permTwo hFixTwo geometry.largestTarget hLargestFixed geometry.largestAnchor]
    exact congrArg gaugeTwo.edge
      (GluingDatum.sourceEdge_self data grownFirst.largest.1)
  let cdOne : ColumnData data wall geometry labelling :=
    positionOneColumnData positionOne survivalOne hValidOne geometry labelling
      gaugeOne (by rw [hAnchorOne]; exact rfl) hBackgroundOne rows.rowGrow rows.rowOther
      hRowGrowOne hRowOtherOne geometry.growAnchor (permOne geometry.otherAnchor)
      hAnchorOne.symm hOtherAnchorOne.symm
  let cdTwo : ColumnData data wall geometry labelling :=
    positionTwoColumnData positionTwo survivalTwo hValidTwo geometry labelling
      gaugeTwo (by rw [hAnchorTwo]; exact rfl) hBackgroundTwo rows.rowLargest hRowLargestTwo
      geometry.growAnchor hAnchorTwo.symm
  let cdThree : ColumnData data wall geometry labelling :=
    growColumnData grownFirst (SelectedSurvival.ofGrowProfile grownFirst) hValid
      geometry labelling rfl rows.rowGrow
      (growRow_eq_rowOf labelling grownFirst
        (SelectedSurvival.ofGrowProfile grownFirst)
        (W3FourLimitRows.grow_survives grownFirst)).symm geometry.growAnchor rfl
  let cdFour : ColumnData data wall geometry labelling :=
    growColumnData grownSecond (SelectedSurvival.ofGrowProfile grownSecond) hValid
      geometry labelling geometry.other_wall_rel rows.rowOther
      (growRow_eq_rowOf labelling grownSecond
        (SelectedSurvival.ofGrowProfile grownSecond)
        (W3FourLimitRows.other_survives grownFirst)).symm geometry.otherAnchor rfl
  have hRelOne : ((W3FourDisjointness.branchSwapOfPerm data wall root hRoot permOne
        hFixOne).apply.vertexPartition wall).Rel
      positionOne.toFourStarGeometry.growAnchor geometry.growAnchor :=
    congrArg ((W3FourDisjointness.branchSwapOfPerm data wall root hRoot permOne
      hFixOne).apply.vertexPartition wall).repr hAnchorOne
  have hRelTwo : ((W3FourDisjointness.branchSwapOfPerm data wall root hRoot permTwo
        hFixTwo).apply.vertexPartition wall).Rel
      positionTwo.toFourStarGeometry.growAnchor geometry.growAnchor :=
    congrArg ((W3FourDisjointness.branchSwapOfPerm data wall root hRoot permTwo
      hFixTwo).apply.vertexPartition wall).repr hAnchorTwo
  have hRelOther : ((W3FourDisjointness.branchSwapOfPerm data wall root hRoot
        permOne hFixOne).apply.vertexPartition wall).Rel
      positionOne.toFourStarGeometry.growAnchor (permOne geometry.otherAnchor) := by
    rw [hWallOne, hAnchorOne]
    exact geometry.other_wall_rel.trans (hFixOne geometry.otherAnchor).symm
  have hIdxOneGrow : newIndex (positionOne.toFourStarGeometry.reversedCandidate
      positionOne.fine positionOne.fine_refines positionOne.grow_refines_fine
      positionOne.other_refines_fine positionOne.rightCounts) geometry.growAnchor =
      (data.edgePartition geometry.growTarget).blockCard geometry.growAnchor := by
    rw [reversedCandidate_newIndex_eq_blockCard positionOne.toFourStarGeometry
      positionOne.fine positionOne.fine_refines positionOne.grow_refines_fine
      positionOne.other_refines_fine positionOne.rightCounts hRelOne, hAnchorOne]
    exact hIndexOneGrow
  have hIdxOneOther : newIndex (positionOne.toFourStarGeometry.reversedCandidate
      positionOne.fine positionOne.fine_refines positionOne.grow_refines_fine
      positionOne.other_refines_fine positionOne.rightCounts)
      (permOne geometry.otherAnchor) =
      (data.edgePartition geometry.otherTarget).blockCard geometry.otherAnchor := by
    rw [reversedCandidate_newIndex_eq_blockCard positionOne.toFourStarGeometry
      positionOne.fine positionOne.fine_refines positionOne.grow_refines_fine
      positionOne.other_refines_fine positionOne.rightCounts hRelOther, hAnchorOne]
    exact hIndexOneOther
  have hIdxTwo : newIndex (positionTwo.toFourStarGeometry.reversedCandidate
      positionTwo.fine positionTwo.fine_refines positionTwo.grow_refines_fine
      positionTwo.other_refines_fine positionTwo.rightCounts) geometry.growAnchor
      + 1 =
      (data.edgePartition geometry.growTarget).blockCard geometry.growAnchor +
        (data.edgePartition geometry.otherTarget).blockCard geometry.otherAnchor := by
    rw [reversedCandidate_newIndex_eq_blockCard positionTwo.toFourStarGeometry
      positionTwo.fine positionTwo.fine_refines positionTwo.grow_refines_fine
      positionTwo.other_refines_fine positionTwo.rightCounts hRelTwo, hAnchorTwo]
    exact hIndexTwo
  refine ⟨{ rows := rows
            member := ![cdOne.memberColumn, cdTwo.memberColumn,
              cdThree.memberColumn, cdFour.memberColumn]
            otherSheet := permOne geometry.otherAnchor
            background_one := hLargestOne
            selected_one := rfl
            index_one_grow := hIdxOneGrow
            index_one_other := hIdxOneOther
            background_two := hLargestTwo
            selected_two := rfl
            index_two := hIdxTwo
            background_three := rfl
            selected_three := rfl
            index_three := growCandidate_newIndex_grow grownFirst
            background_four := rfl
            selected_four := rfl
            index_four := growCandidate_newIndex_grow grownSecond },
    rfl, HEq.rfl, HEq.rfl, ?_⟩
  intro i
  fin_cases i
  · exact cdOne.isHonest
  · exact cdTwo.isHonest
  · exact cdThree.isHonest
  · exact cdFour.isHonest

end Figure28

end DraismaVargas.LocalCases.W3FourRegrownColumn