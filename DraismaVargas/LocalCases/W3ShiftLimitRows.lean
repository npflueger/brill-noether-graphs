module

public import DraismaVargas.LocalCases.W3FourLimitRows
public import DraismaVargas.LocalCases.W3ShiftClosure

@[expose] public section

/-!
# Figure 29's length matrices: `W3ShiftClosure.LimitRows`, derived

Source: Draisma--Vargas Part I, case `{w3-r1-nd3-t2-(a>k₄)}`, Figure 29 and
Equation (3).

## What `W3ShiftClosure.LimitRows` actually is

It is **not** the analogue of `W3FourStableGraph.LimitRows`.  That structure is
a census of the incoming datum -- `LimitRows data wall geometry`, whose three
fields speak only about `data` -- and `W3FourLimitRows` derives it without ever
leaving the limit.  `W3ShiftClosure.LimitRows member coordinate`
mentions no incoming datum at all: its `presentation` field is a
`LengthMatrixPresentation` of each **outgoing** member `(member i).datum`, and
its `det` field is a determinant identity for those presented matrices.  The
right analogue of it on the Figure 28 side is
`W3FourStableGraph.Figure28Receipts`, not `W3FourStableGraph.LimitRows`.

So this module has to do the whole of `W3FourStableGraph`'s determinant
computation over again for Figure 29's pair, and not just `W3FourLimitRows`'s
census.  It does, and the census is one of its three inputs.

## What is proved here

* `selectedSumAt`, `backgroundSumAt`, `backgroundSheetsAt`, `columnSum_eq_at`,
  `sum_backgroundSheetsAt` -- the split of an incoming column at the
  distinguished wall block.  These are `W3FourStableGraph`'s `selectedSum`,
  `backgroundSum`, `backgroundSheetsOf`, `columnSum_eq` and
  `sum_backgroundSheetsOf` with the parameter `FourStarGeometry data wall`
  replaced by the bare sheet `anchor : Fin degree` that those five statements
  actually use.  They have to be restated rather than reused: a
  `FourStarGeometry` carries `largest_index : k₄ = |A₀|`, which is exactly the
  `(a = k₄)` selector that this case negates, so no `FourStarGeometry` exists on
  a shift datum.  Everything in `W3FourStableGraph`'s `Presentation` section --
  `WallTransport`, `gaugePresentation` and its four evaluation lemmas -- is
  geometry-free and is imported and used unchanged, as is `columnSum` itself
  and the whole of `W3FourLimitRows`.
* `ShiftMemberColumn` and `det_eq` -- the same for
  `W3FourStableGraph.MemberColumn`.  Both of Figure 29's members live over one
  gauge copy (`W3ShiftClosure.exists_gauge_shift_pair` produces a single
  `gaugeData` carrying both), so the per-member `base` and `WallTransport` of
  the Figure 28 version collapse to the identity gauge and are dropped.
* `moving_unique_of_wall_rel` and `selectedSum_stableRowPath` -- **the incoming
  census.**  Above the moving direction `t_α` the distinguished block `A₀`
  displays the one occurrence `e_α`, in one stable row, with index `k_α`.  The
  survival census is `ShiftProfile.surviving` and `moving_unique`, carried by
  the profile; what is added is `incident_of_wall_rel`, the step from
  an occurrence over `A₀` to one incident to `A₀`'s source vertex.
* `growCandidate_newIndex_background`, `shrinkCandidate_newIndex_background` --
  **Figure 29's `σ⁽ᵠ⁾(J₀,1) = σ₀(J₀,α)`, read off the actual resolutions.**
  Both members are built on `ShiftProfile.background`, which installs
  `ResolutionCoarseFine.fineResolution` of the *moving* direction on every
  background wall block, so `α` is the moving direction for both.
* `growCandidate_newIndex_moving` (`k_α + 1`) and
  `shrinkCandidate_newIndex_remainder` (`k_α − 1`) -- Figure 29's two displayed
  new-edge indices, as `newIndex` of the assembled candidates.
* `limitRows` -- **`W3ShiftClosure.LimitRows`, derived**, and `shiftMembers`,
  the two members it is stated on.  `limitRows` is a *total function* of the
  case's own payload: a `ThirdEquation.W3SourceInput`, a `ShiftProfile` and a
  `ShrinkData`, which is exactly what `W3ShiftSourceCandidates` consumes and
  what `W3ShiftClosure.exists_gauge_shift_pair` produces.
* `limitRows_columnSum` -- the honesty receipt for the retained half: every
  retained column of the presentations is
  `StableSourceMatrix.matrix gaugeData` at the corresponding stable path.
* `wallSum_eq_background` -- the honesty receipt for `σ₀(J₀,α)`: the `wallSum`
  the derived rows carry is the limit's own cofactor-weighted background sum, not
  a free constant chosen to make `wallRelation` hold.
* `exists_shift_limitRows` -- the gauge copy of
  `W3ShiftClosure.exists_gauge_shift_pair` together with the derived
  `LimitRows` on it, and `exists_equationThree_positive_exit_of_input` --
  `W3ShiftClosure.exists_equationThree_positive_exit` with its supplied
  `LimitRows` removed.

## Towards the incoming member

* `shiftMembers_ne` -- the pair's two members are distinct, separated by the
  dilation index of the regrown occurrence through the residual sheet: `k_α − 1`
  against `k_α + 1`, kept apart by the case's own `k_α ≥ 2`.  That observable is
  the `±1` half of "which member is the incoming one".
* `det_limitRows_zero`, `det_limitRows_one` -- the two determinants in closed
  form, `c(e_α)/(k_α(k_α − 1))` and `−c(e_α)/(k_α(k_α + 1))`.
* `det_limitRows_eq_zero_iff` and `det_limitRows_mul_neg` -- a member of the pair
  is nonsingular exactly when the limit's own cofactor `c(e_α)` is nonzero, and
  the two members then have opposite determinant sign.
* `exists_equationThree_positive_exit_other` -- consequently the exit's gate is a
  condition on the limit alone and its outgoing member is the *other* member of
  the pair, whichever of the two the incoming cover turns out to be.

The other half -- identifying the incoming cover with a named Figure 29
member, i.e. which direction moved -- is the analogue of
`W3Nd2IncomingMemberMatching` and is **not** done here: nothing in this module
goes near the incoming contraction apparatus (`IncomingTargetExpansion`,
`FullDimensionalSource`, `WallDegeneration`, the fibre census).  It is
`W3ShiftIncomingCensus` and `W3ShiftIncomingMatching`.

## What is supplied rather than derived

`ShiftMemberColumn.selectedSheets` supplies each member's *regrown* row
assignment, exactly as `W3FourStableGraph.MemberColumn.selectedSheets` does, and
`limitRows` fixes it to Figure 29's displayed one: a single regrown class in the
stable row of `e_α`.  The analogue of `W4OutgoingLimitMatrix.presented_matrix_eq`
-- that the presented matrix of a member is that member's own
`StableSourceMatrix.matrix` at its own stable rows -- is not proved here, for
either the retained or the regrown half, and nothing here assumes it (it is
`W3ShiftGraphData.commonMatrix_retained` and `W3ShiftHonestBalance.matrix_wall`).
That is the same boundary `W3FourStableGraph` and `W3FourLimitRows` record.

## The branch swap

Unlike Figure 28, the census here never has to cross a branch swap *and neither
does anything else*: `W3ShiftClosure.exists_gauge_shift_pair` performs the two
swaps first and hands back one gauge copy `gaugeData` carrying both members, so
everything below lives over a single datum and the identity `WallTransport` is
the only one used.

## Which datum this is about

`ThirdEquation.W3SourceInput` carries `equation_c : data.targetExcess wall = 1`,
so everything here lives on the wall/limit side of the bridge recorded in
`FullDimensionalSource.false_of_changeMinimal_auxR0SourceInput`, exactly as
`W3ShiftSourceCandidates` and `W3ShiftClosure` do.  The presentations are
presentations of the outgoing members' data, which is the other side.
-/

namespace DraismaVargas.LocalCases.W3ShiftLimitRows

open DraismaVargas.Infrastructure
open TargetExpansion
open BalancedGlobal
open ResolutionM11 ResolutionCoarseFine
open W4StableSource StableLocalProperties ThirdEquation W3R1SourceProfile
open W3ShiftSourceCandidates
open W3FourStableGraph (WallTransport columnSum single sum_ite_mul single_map_sum
  gaugePresentation gaugePresentation_matrix_some gaugePresentation_matrix_none
  gaugePresentation_agreeOffWall newIndex newIndex_eq)
open W3FourLimitRows (rowOccurrences mem_rowOccurrences stableRowPath
  mem_stableRowPath oldRowOf_eq_some_iff columnSum_stableRowPath)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## Splitting an incoming column at the distinguished wall block

`W3FourStableGraph`'s `selectedSum`, `backgroundSum`, `backgroundSheetsOf`,
`columnSum_eq` and `sum_backgroundSheetsOf` are stated against a
`W3FourClosure.FourStarGeometry`, but they use exactly one field of it, the
sheet `growAnchor` naming the distinguished wall block.  A shift datum has no
`FourStarGeometry` -- that structure's `largest_index` field is the `(a = k₄)`
selector this case negates -- so the five statements are restated here with the
bare anchor.  Nothing else of `W3FourStableGraph` is restated: `columnSum` and
the whole `Presentation` section are already geometry-free and are used as they
stand. -/

/-- The part of a row's `t` column contributed by the wall block of `anchor`. -/
noncomputable def selectedSumAt (wall : target.V) (anchor : Fin degree)
    (path : List data.SourceEdge) (t : target.edges) : ℚ :=
  (path.map fun e ↦
    if t = e.1.1 ∧ (data.vertexPartition wall).Rel anchor e.1.2 then
      (1 : ℚ) / data.sourceEdgeIndex e else 0).sum

/-- The part contributed by every other wall block: Figure 29's `σ₀(J₀, ·)`
before the cofactor weighting. -/
noncomputable def backgroundSumAt (wall : target.V) (anchor : Fin degree)
    (path : List data.SourceEdge) (t : target.edges) : ℚ :=
  (path.map fun e ↦
    if t = e.1.1 ∧ ¬(data.vertexPartition wall).Rel anchor e.1.2 then
      (1 : ℚ) / data.sourceEdgeIndex e else 0).sum

/-- The sheets of the background part, in the order the row displays them. -/
noncomputable def backgroundSheetsAt (wall : target.V) (anchor : Fin degree)
    (path : List data.SourceEdge) (t : target.edges) : List (Fin degree) :=
  path.filterMap fun e ↦
    if t = e.1.1 ∧ ¬(data.vertexPartition wall).Rel anchor e.1.2 then
      some e.1.2 else none

/-- The split itself. -/
theorem columnSum_eq_at (wall : target.V) (anchor : Fin degree)
    (path : List data.SourceEdge) (t : target.edges) :
    columnSum path t =
      selectedSumAt wall anchor path t + backgroundSumAt wall anchor path t := by
  classical
  induction path with
  | nil => simp [columnSum, selectedSumAt, backgroundSumAt]
  | cons e rest ih =>
      simp only [columnSum, selectedSumAt, backgroundSumAt, List.map_cons,
        List.sum_cons] at ih ⊢
      by_cases hTarget : t = e.1.1
      · by_cases hRel : (data.vertexPartition wall).Rel anchor e.1.2
        · rw [ite_eq_left hTarget, ite_eq_left ⟨hTarget, hRel⟩, ite_eq_right (by tauto)]
          rw [ih]; ring
        · rw [ite_eq_left hTarget, ite_eq_right (by tauto), ite_eq_left ⟨hTarget, hRel⟩]
          rw [ih]; ring
      · rw [ite_eq_right hTarget, ite_eq_right (by tauto), ite_eq_right (by tauto)]
        rw [ih]; ring

/-- **The background regrown occurrences of a row reproduce its `t` column,
minus the distinguished block's part.**  The only input is that the regrown
index at a background sheet is that sheet's `t` index, which is Figure 29's
`σ⁽ᵠ⁾(J₀, 1) = σ₀(J₀, α)`. -/
theorem sum_backgroundSheetsAt (wall : target.V) (anchor : Fin degree)
    (path : List data.SourceEdge) (t : target.edges) (index : Fin degree → ℕ)
    (hIndex : ∀ sheet, ¬(data.vertexPartition wall).Rel anchor sheet →
      index sheet = (data.edgePartition t).blockCard sheet) :
    ((backgroundSheetsAt wall anchor path t).map fun sheet ↦
        (1 : ℚ) / index sheet).sum =
      backgroundSumAt wall anchor path t := by
  classical
  induction path with
  | nil => simp [backgroundSheetsAt, backgroundSumAt]
  | cons e rest ih =>
      by_cases hCond : t = e.1.1 ∧
          ¬(data.vertexPartition wall).Rel anchor e.1.2
      · have hIdx : index e.1.2 = data.sourceEdgeIndex e := by
          rw [hIndex e.1.2 hCond.2]
          exact congrArg (fun p ↦ SheetPartition.blockCard p e.1.2)
            (congrArg data.edgePartition hCond.1)
        simp only [backgroundSheetsAt, backgroundSumAt, List.filterMap_cons,
          List.map_cons, List.sum_cons, ite_eq_left hCond] at ih ⊢
        rw [hIdx, ih]
      · simp only [backgroundSheetsAt, backgroundSumAt, List.filterMap_cons,
          List.map_cons, List.sum_cons, ite_eq_right hCond] at ih ⊢
        rw [ih, zero_add]

/-! ## The determinant of one Figure 29 member

The analogue of `W3FourStableGraph.MemberColumn`, with the same two
simplifications: the geometry is replaced by the bare anchor, and the per-member
gauge is dropped, both members of Figure 29's pair living over the one gauge
copy `W3ShiftClosure.exists_gauge_shift_pair` produces. -/

section Determinant

/-- Everything one member of Figure 29 supplies to the determinant computation:
its globally assembled candidate, the direction whose partition resolves the
*background* wall blocks on the new edge, and the list of regrown occurrences it
displays over the distinguished block in each stable row. -/
structure ShiftMemberColumn (data : GluingDatum target degree) (wall : target.V)
    (anchor : Fin degree) where
  /-- The member. -/
  candidate : Candidate target degree data wall
  /-- `t_α`: the direction whose partition the member installs on the new edge
  above every background wall block. -/
  backgroundTarget : target.edges
  /-- Which is exactly what this field says, index by index. -/
  background_index : ∀ sheet, ¬(data.vertexPartition wall).Rel anchor sheet →
    newIndex candidate sheet = (data.edgePartition backgroundTarget).blockCard sheet
  /-- The regrown occurrences the member displays over the distinguished block,
  listed by stable row. -/
  selectedSheets : Option target.edges → List (Fin degree)

namespace ShiftMemberColumn

variable {anchor : Fin degree} {n : ℕ}
  (member : Fin n → ShiftMemberColumn data wall anchor)
  (oldPath : Option target.edges → List data.SourceEdge)

/-- The complete regrown row of a member: its distinguished occurrences followed
by its background ones. -/
noncomputable def newSheets (i : Fin n) (row : Option target.edges) :
    List (Fin degree) :=
  (member i).selectedSheets row ++
    backgroundSheetsAt wall anchor (oldPath row) (member i).backgroundTarget

/-- The canonically presented members, over the one common datum. -/
noncomputable def presentation (i : Fin n) :
    ((member i).candidate).datum.LengthMatrixPresentation (Option target.edges) :=
  gaugePresentation (fun _ ↦ data) (fun _ ↦ WallTransport.refl data)
    (fun j ↦ (member j).candidate) oldPath (newSheets member oldPath) i

/-- Their common off-wall columns. -/
theorem presentation_agreeOffWall (first second : Fin n) :
    AgreeOffColumn
      (GluingDatum.LengthMatrixPresentation.matrix (presentation member oldPath first))
      (GluingDatum.LengthMatrixPresentation.matrix (presentation member oldPath second))
      none :=
  gaugePresentation_agreeOffWall _ _ _ _ _ first second

/-- The part of the regrown column contributed by the distinguished block. -/
noncomputable def selectedNewSum (i : Fin n) (row : Option target.edges) : ℚ :=
  (((member i).selectedSheets row).map fun sheet ↦
    (1 : ℚ) / newIndex (member i).candidate sheet).sum

/-- **The regrown column, evaluated.** -/
theorem matrix_none_eq (i : Fin n) (row : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix
        (presentation member oldPath i) row none =
      selectedNewSum member i row +
        (columnSum (oldPath row) (member i).backgroundTarget -
          selectedSumAt wall anchor (oldPath row) (member i).backgroundTarget) := by
  classical
  rw [presentation, gaugePresentation_matrix_none, newSheets, List.map_append,
    List.sum_append,
    sum_backgroundSheetsAt wall anchor (oldPath row) (member i).backgroundTarget
      (fun sheet ↦ newIndex (member i).candidate sheet)
      (fun sheet hSheet ↦ (member i).background_index sheet hSheet),
    columnSum_eq_at wall anchor (oldPath row) (member i).backgroundTarget]
  simp [selectedNewSum]

/-- The retained columns are the limit's own. -/
theorem matrix_some_eq (i : Fin n) (row : Option target.edges)
    (column : target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix
        (presentation member oldPath i) row (some column) =
      columnSum (oldPath row) column :=
  gaugePresentation_matrix_some _ _ _ _ _ i row column

variable (reference : Fin n)

/-- The family's common cofactor row, read from one chosen member. -/
noncomputable def cofactor (row : Option target.edges) : ℚ :=
  (GluingDatum.LengthMatrixPresentation.matrix
    (presentation member oldPath reference)).adjugate none row

/-- **The cofactor-weighted `t` column of the limit vanishes** for every
retained direction `t`: the off-diagonal entry of `adjugate M * M = det M • 1`.
This is what makes Figure 29's displayed limit relation
`c(e_α)/k_α + σ₀(J₀,α) = 0` a theorem rather than a hypothesis. -/
theorem sum_columnSum_mul_cofactor (column : target.edges) :
    ∑ row : Option target.edges,
      columnSum (oldPath row) column * cofactor member oldPath reference row = 0 := by
  classical
  have hZero := columnContribution_eq_zero
    (GluingDatum.LengthMatrixPresentation.matrix
      (presentation member oldPath reference))
    (wallColumn := (none : Option target.edges)) (column := some column)
    (by simp)
  rw [← hZero, columnContribution]
  exact Finset.sum_congr rfl fun row _ ↦ by
    rw [matrix_some_eq member oldPath reference row column]
    rfl

/-- **A Figure 29 member's determinant.**  It is the cofactor-weighted regrown
contribution of the distinguished wall block, minus the cofactor-weighted `t_α`
contribution of that same block.  Nothing else survives, because the background
blocks reproduce the limit's own `t_α` column, whose cofactor-weighted sum is
zero. -/
theorem det_eq (i : Fin n) :
    (GluingDatum.LengthMatrixPresentation.matrix
        (presentation member oldPath i)).det =
      (∑ row : Option target.edges,
          selectedNewSum member i row * cofactor member oldPath reference row) -
        ∑ row : Option target.edges,
          selectedSumAt wall anchor (oldPath row) (member i).backgroundTarget *
            cofactor member oldPath reference row := by
  classical
  rw [det_eq_sum_wallColumn_mul_commonCofactor
    (presentation_agreeOffWall member oldPath i reference)]
  have hSplit : ∀ row : Option target.edges,
      GluingDatum.LengthMatrixPresentation.matrix
          (presentation member oldPath i) row none *
        cofactor member oldPath reference row =
      selectedNewSum member i row * cofactor member oldPath reference row +
        columnSum (oldPath row) (member i).backgroundTarget *
          cofactor member oldPath reference row -
        selectedSumAt wall anchor (oldPath row) (member i).backgroundTarget *
          cofactor member oldPath reference row := by
    intro row
    rw [matrix_none_eq member oldPath i row]
    ring
  calc
    ∑ row : Option target.edges,
        GluingDatum.LengthMatrixPresentation.matrix
            (presentation member oldPath i) row none *
          (GluingDatum.LengthMatrixPresentation.matrix
            (presentation member oldPath reference)).adjugate none row
        = ∑ row : Option target.edges,
          (selectedNewSum member i row * cofactor member oldPath reference row +
            columnSum (oldPath row) (member i).backgroundTarget *
              cofactor member oldPath reference row -
            selectedSumAt wall anchor (oldPath row) (member i).backgroundTarget *
              cofactor member oldPath reference row) :=
      Finset.sum_congr rfl fun row _ ↦ hSplit row
    _ = (∑ row : Option target.edges,
            selectedNewSum member i row * cofactor member oldPath reference row) +
          (∑ row : Option target.edges,
            columnSum (oldPath row) (member i).backgroundTarget *
              cofactor member oldPath reference row) -
          ∑ row : Option target.edges,
            selectedSumAt wall anchor (oldPath row) (member i).backgroundTarget *
              cofactor member oldPath reference row := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_columnSum_mul_cofactor member oldPath reference
        (member i).backgroundTarget, add_zero]

/-- **One regrown class in one stable row, against a one-occurrence census.**
Figure 29's shape for both members: the member displays a single regrown class
through `sheet` in the row `r`, and above its background direction `t` the
distinguished block displays a single occurrence of reciprocal index `value`,
in that same row `r`. -/
theorem det_eq_of_single (i : Fin n) (r : Option target.edges) (sheet : Fin degree)
    (value : ℚ) (hSelected : (member i).selectedSheets = single r sheet)
    (hCensus : ∀ row, selectedSumAt wall anchor (oldPath row)
      (member i).backgroundTarget = if row = r then value else 0) :
    (GluingDatum.LengthMatrixPresentation.matrix
        (presentation member oldPath i)).det =
      (1 : ℚ) / newIndex (member i).candidate sheet *
          cofactor member oldPath reference r -
        value * cofactor member oldPath reference r := by
  classical
  have hNew : ∀ row : Option target.edges,
      selectedNewSum member i row =
        if row = r then (1 : ℚ) / newIndex (member i).candidate sheet else 0 := by
    intro row
    rw [selectedNewSum, hSelected]
    exact single_map_sum r sheet
      (fun s ↦ (1 : ℚ) / newIndex (member i).candidate s) row
  have hFirst : (∑ row : Option target.edges,
      selectedNewSum member i row * cofactor member oldPath reference row) =
      (1 : ℚ) / newIndex (member i).candidate sheet *
        cofactor member oldPath reference r := by
    simp only [hNew]
    exact sum_ite_mul r ((1 : ℚ) / newIndex (member i).candidate sheet)
      (cofactor member oldPath reference)
  have hSecond : (∑ row : Option target.edges,
      selectedSumAt wall anchor (oldPath row) (member i).backgroundTarget *
        cofactor member oldPath reference row) =
      value * cofactor member oldPath reference r := by
    simp only [hCensus]
    exact sum_ite_mul r value (cofactor member oldPath reference)
  rw [det_eq member oldPath reference i, hFirst, hSecond]

end ShiftMemberColumn

end Determinant

/-! ## The incoming census above the moving direction

`W3ShiftSourceCandidates.ShiftProfile` already carries the incoming survival
census of the distinguished block: `surviving` says its three non-dangling
incident occurrences are `e_α`, `e_β`, `e_γ`, and `moving_unique` says the
moving direction is represented by `e_α` alone.  What is added here is the step
from "an occurrence above `t_α` whose sheet lies in `A₀`" to "an occurrence
incident to `A₀`'s source vertex", which is where the refinement
`edgePartition t_α ≼ vertexPartition wall` enters. -/

section Census

variable {input : W3SourceInput data star}

/-- An occurrence above a wall direction whose sheet lies in the distinguished
block is incident to that block's source vertex. -/
theorem incident_of_wall_rel (shift : ShiftProfile input) {edge : data.SourceEdge}
    (hMem : edge.1.1 ∈ GluingDatum.incidentEdges wall)
    (hRel : (data.vertexPartition wall).Rel shift.movingAnchor edge.1.2) :
    Incident data edge
      (WallBlock.sourceVertex data wall input.distinguishedBlock) :=
  (incident_wallBlock_sourceVertex_iff data input.distinguishedBlock edge).mpr
    ⟨hMem, (WallBlock.ofSheet_eq_iff_rel data wall input.distinguishedBlock
      edge.1.2).mpr (shift.movingAnchor_wall_rel.trans hRel)⟩

/-- The moving survivor really survives. -/
theorem moving_survives (shift : ShiftProfile input) :
    ¬ IsDangling data shift.moving.1 :=
  (mem_survivors data input.distinguishedBlock shift.moving).mp
    (by rw [shift.surviving]; simp)

/-- **Above `t_α`, the distinguished block displays `e_α` alone.** -/
theorem moving_unique_of_wall_rel (shift : ShiftProfile input)
    {edge : data.SourceEdge} (hSurvives : ¬ IsDangling data edge)
    (hTarget : shift.movingTarget = edge.1.1)
    (hRel : (data.vertexPartition wall).Rel shift.movingAnchor edge.1.2) :
    edge = shift.moving.1 := by
  have hMem : edge.1.1 ∈ GluingDatum.incidentEdges wall :=
    hTarget ▸ shift.movingTarget_mem
  have hIncident := incident_of_wall_rel shift hMem hRel
  exact congrArg Subtype.val (moving_unique shift ⟨edge, hIncident⟩
    ((mem_survivors data input.distinguishedBlock _).mpr hSurvives) hTarget.symm)

/-- **One surviving occurrence in one stable row.**  The shape Figure 29's
determinant consumes: the distinguished block's contribution to the `t_α` column
of a stable row is `1/k_α` in the row containing `e_α` and zero in every other
row.  This is `W3FourLimitRows.selectedSum_stableRowPath` with the geometry
replaced by the bare anchor; the proof is the same. -/
theorem selectedSum_stableRowPath (labelling : StablePathLabelling data)
    (anchor : Fin degree) (t : target.edges) {selected : data.SourceEdge}
    (hSurvives : ¬ IsDangling data selected)
    (hTarget : t = selected.1.1)
    (hRel : (data.vertexPartition wall).Rel anchor selected.1.2)
    (hUnique : ∀ edge : data.SourceEdge, ¬ IsDangling data edge → t = edge.1.1 →
      (data.vertexPartition wall).Rel anchor edge.1.2 → edge = selected)
    (row : Option target.edges) :
    selectedSumAt wall anchor (stableRowPath labelling row) t =
      if row = labelling.row (NonDanglingEdge.stablePath
          (⟨selected, hSurvives⟩ : NonDanglingEdge data)) then
        (1 : ℚ) / data.sourceEdgeIndex selected
      else 0 := by
  classical
  have hZero : ∀ edge ∈ rowOccurrences labelling row, edge ≠ selected →
      (if t = edge.1.1 ∧ (data.vertexPartition wall).Rel anchor edge.1.2 then
        (1 : ℚ) / data.sourceEdgeIndex edge else 0) = 0 := by
    intro edge hEdge hNe
    refine ite_eq_right fun hCond ↦ hNe ?_
    obtain ⟨hEdgeSurvives, _⟩ := (oldRowOf_eq_some_iff labelling edge row).mp
      ((mem_rowOccurrences labelling row edge).mp hEdge)
    exact hUnique edge hEdgeSurvives hCond.1 hCond.2
  unfold selectedSumAt stableRowPath
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

end Census

/-! ## Figure 29's two new-edge indices, read off the actual resolutions -/

section MemberIndices

variable {input : W3SourceInput data star}

/-- **`σ⁽ᵠ⁾(J₀,1) = σ₀(J₀,α)` for the grow member.**  Every background wall
block is resolved with `ResolutionCoarseFine.fineResolution` of the moving
direction's own edge partition, which is what `ShiftProfile.background`
installs. -/
theorem growCandidate_newIndex_background (shift : ShiftProfile input)
    {sheet : Fin degree}
    (hSheet : ¬(data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    newIndex shift.growCandidate sheet =
      (data.edgePartition shift.movingTarget).blockCard sheet := by
  rw [newIndex_eq, LocalResolution.paste_newEdge_blockCard]
  have hRepr : ¬(data.vertexPartition wall).Rel shift.movingAnchor
      ((data.vertexPartition wall).repr sheet) := fun hRel ↦
    hSheet (hRel.trans ((data.vertexPartition wall).rel_repr_left sheet))
  have hResolution : shift.growCandidate.resolution
        ((data.vertexPartition wall).repr sheet) =
      LocalResolution.onBlock (data.vertexPartition wall) shift.movingAnchor
        (fineResolution (data.vertexPartition wall) shift.growPartition
          shift.growPartition_refines)
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (data.edgePartition shift.movingTarget) shift.movingTarget_refines)
        ((data.vertexPartition wall).repr sheet) := rfl
  rw [hResolution, LocalResolution.onBlock_of_not_rel _ _ _ _ _ hRepr]
  rfl

/-- The grow member's displayed index over the distinguished block is read from
its new divalent endpoint `A' = eₐ ∪ {x}`. -/
theorem growCandidate_newIndex_selected (shift : ShiftProfile input)
    {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    newIndex shift.growCandidate sheet = shift.growPartition.blockCard sheet := by
  rw [newIndex_eq, LocalResolution.paste_newEdge_blockCard]
  have hRepr : (data.vertexPartition wall).Rel shift.movingAnchor
      ((data.vertexPartition wall).repr sheet) :=
    hSheet.trans ((data.vertexPartition wall).rel_repr_left sheet).symm
  have hResolution : shift.growCandidate.resolution
        ((data.vertexPartition wall).repr sheet) =
      LocalResolution.onBlock (data.vertexPartition wall) shift.movingAnchor
        (fineResolution (data.vertexPartition wall) shift.growPartition
          shift.growPartition_refines)
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (data.edgePartition shift.movingTarget) shift.movingTarget_refines)
        ((data.vertexPartition wall).repr sheet) := rfl
  rw [hResolution, LocalResolution.onBlock_of_rel _ _ _ _ _ hRepr]
  rfl

/-- **Figure 29's `|e'| = k_α + 1`**, as the dilation index of the grow
member's regrown occurrence through the moving anchor. -/
theorem growCandidate_newIndex_moving (shift : ShiftProfile input) :
    newIndex shift.growCandidate shift.movingAnchor =
      data.sourceEdgeIndex shift.moving.1 + 1 :=
  (growCandidate_newIndex_selected shift
    (show (data.vertexPartition wall).Rel shift.movingAnchor shift.movingAnchor
      from rfl)).trans shift.growPartition_blockCard_movingAnchor

variable {shift : ShiftProfile input}

/-- **`σ⁽ᵠ⁾(J₀,1) = σ₀(J₀,α)` for the shrink member.**  Its background is the
same `ShiftProfile.background`, so the background direction is again `t_α`. -/
theorem shrinkCandidate_newIndex_background (shrink : ShrinkData shift)
    {sheet : Fin degree}
    (hSheet : ¬(data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    newIndex shrink.shrinkCandidate sheet =
      (data.edgePartition shift.movingTarget).blockCard sheet := by
  rw [newIndex_eq, LocalResolution.paste_newEdge_blockCard]
  have hRepr : ¬(data.vertexPartition wall).Rel shift.movingAnchor
      ((data.vertexPartition wall).repr sheet) := fun hRel ↦
    hSheet (hRel.trans ((data.vertexPartition wall).rel_repr_left sheet))
  have hResolution : shrink.shrinkCandidate.resolution
        ((data.vertexPartition wall).repr sheet) =
      LocalResolution.onBlock (data.vertexPartition wall) shift.movingAnchor
        shrink.selected
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (data.edgePartition shift.movingTarget) shift.movingTarget_refines)
        ((data.vertexPartition wall).repr sheet) := rfl
  rw [hResolution, LocalResolution.onBlock_of_not_rel _ _ _ _ _ hRepr]
  rfl

/-- The residual new-edge representative lies in the distinguished block. -/
theorem remainder_movingAnchor_rel (shrink : ShrinkData shift) :
    (data.vertexPartition wall).Rel shift.movingAnchor shrink.remainder :=
  shift.movingAnchor_wall_rel.symm.trans
    (shrink.transfer_wall_rel.trans shrink.remainder_wall_rel)

/-- **The grow member's index at the *residual* sheet is also `k_α + 1`.**  The
residual representative lies in the moving class, which the grow member's
divalent endpoint has enlarged by the extra sheet.  This is what lets the two
members be compared at one and the same sheet. -/
theorem growCandidate_newIndex_remainder (shrink : ShrinkData shift) :
    newIndex shift.growCandidate shrink.remainder =
      data.sourceEdgeIndex shift.moving.1 + 1 := by
  have hMovingRel : (data.edgePartition shift.movingTarget).Rel shift.movingAnchor
      shrink.remainder := shrink.transfer_moving.trans shrink.remainder_moving
  have hGrowRel : shift.growPartition.Rel shift.movingAnchor shrink.remainder :=
    (shift.growPartition_rel_movingAnchor_iff shrink.remainder).mpr (Or.inl hMovingRel)
  rw [growCandidate_newIndex_selected shift (remainder_movingAnchor_rel shrink),
    ← SheetPartition.blockCard_congr shift.growPartition hGrowRel]
  exact shift.growPartition_blockCard_movingAnchor

/-- **Figure 29's `|e'| = k_α − 1`**, as the dilation index of the shrink
member's regrown occurrence through the residual representative. -/
theorem shrinkCandidate_newIndex_remainder (shrink : ShrinkData shift) :
    newIndex shrink.shrinkCandidate shrink.remainder + 1 =
      data.sourceEdgeIndex shift.moving.1 := by
  rw [newIndex_eq, LocalResolution.paste_newEdge_blockCard]
  have hRepr : (data.vertexPartition wall).Rel shift.movingAnchor
      ((data.vertexPartition wall).repr shrink.remainder) :=
    (remainder_movingAnchor_rel shrink).trans
      ((data.vertexPartition wall).rel_repr_left shrink.remainder).symm
  have hResolution : shrink.shrinkCandidate.resolution
        ((data.vertexPartition wall).repr shrink.remainder) =
      LocalResolution.onBlock (data.vertexPartition wall) shift.movingAnchor
        shrink.selected
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (data.edgePartition shift.movingTarget) shift.movingTarget_refines)
        ((data.vertexPartition wall).repr shrink.remainder) := rfl
  rw [hResolution, LocalResolution.onBlock_of_rel _ _ _ _ _ hRepr]
  exact shrink.newEdge_blockCard_remainder

end MemberIndices

/-! ## `W3ShiftClosure.LimitRows`, derived -/

section Derivation

variable {input : W3SourceInput data star} {shift : ShiftProfile input}

/-- The canonical row labelling of the limit, supplied by
`W3SourceInput.stablePath_card` through `StablePathLabelling.ofCardEq`. -/
noncomputable def labelling (input : W3SourceInput data star) :
    StablePathLabelling data :=
  StablePathLabelling.ofCardEq data input.stablePath_card

/-- The stable row displaying the moving survivor `e_α`. -/
noncomputable def rowMoving (shift : ShiftProfile input) : Option target.edges :=
  (labelling input).row (NonDanglingEdge.stablePath
    (⟨shift.moving.1, moving_survives shift⟩ : NonDanglingEdge data))

/-- The limit's displayed stable rows, as occurrence lists. -/
noncomputable def oldPath (input : W3SourceInput data star) :
    Option target.edges → List data.SourceEdge :=
  stableRowPath (labelling input)

/-- **The incoming census, in the shape the determinant consumes.** -/
theorem selectedSum_oldPath (shift : ShiftProfile input)
    (row : Option target.edges) :
    selectedSumAt wall shift.movingAnchor (oldPath input row) shift.movingTarget =
      if row = rowMoving shift then
        (1 : ℚ) / data.sourceEdgeIndex shift.moving.1
      else 0 :=
  selectedSum_stableRowPath (labelling input) shift.movingAnchor shift.movingTarget
    (moving_survives shift) rfl rfl
    (fun _ ↦ moving_unique_of_wall_rel shift) row

/-- Figure 29's shrink member as a `ShiftMemberColumn`. -/
noncomputable def shrinkColumn (shrink : ShrinkData shift) :
    ShiftMemberColumn data wall shift.movingAnchor where
  candidate := shrink.shrinkCandidate
  backgroundTarget := shift.movingTarget
  background_index := fun _ hSheet ↦ shrinkCandidate_newIndex_background shrink hSheet
  selectedSheets := single (rowMoving shift) shrink.remainder

/-- Figure 29's grow member as a `ShiftMemberColumn`. -/
noncomputable def growColumn (shift : ShiftProfile input) :
    ShiftMemberColumn data wall shift.movingAnchor where
  candidate := shift.growCandidate
  backgroundTarget := shift.movingTarget
  background_index := fun _ hSheet ↦ growCandidate_newIndex_background shift hSheet
  selectedSheets := single (rowMoving shift) shift.movingAnchor

/-- Equation (3)'s pair, in the order `(k_α − 1, k_α + 1)` the weights
`W3ShiftClosure.equationThreeGaugeFamily` installs expect. -/
noncomputable def memberColumns (shrink : ShrinkData shift) :
    Fin 2 → ShiftMemberColumn data wall shift.movingAnchor :=
  ![shrinkColumn shrink, growColumn shift]

/-- **Equation (3)'s two members**: the Position II.b shrink member of new-edge
index `k_α − 1` and the Position II.a grow member of new-edge index
`k_α + 1`. -/
noncomputable def shiftMembers (shrink : ShrinkData shift) :
    Fin 2 → Candidate target degree data wall :=
  fun i ↦ (memberColumns shrink i).candidate

/-- Figure 29's `c(e_α)`: the cofactor of the stable row displaying `e_α`. -/
noncomputable def wallContribution (shrink : ShrinkData shift) : ℚ :=
  ShiftMemberColumn.cofactor (memberColumns shrink) (oldPath input) 0
    (rowMoving shift)

/-- `k_α` as a rational. -/
noncomputable def movingIndex (shift : ShiftProfile input) : ℚ :=
  (data.sourceEdgeIndex shift.moving.1 : ℚ)

/-- The shrink member's displayed index, as a rational: `k_α − 1`. -/
theorem shrink_newIndex_cast (shrink : ShrinkData shift) :
    ((newIndex shrink.shrinkCandidate shrink.remainder : ℕ) : ℚ) =
      movingIndex shift - 1 := by
  have h := shrinkCandidate_newIndex_remainder shrink
  have hCast : ((newIndex shrink.shrinkCandidate shrink.remainder : ℕ) : ℚ) + 1 =
      movingIndex shift := by
    rw [movingIndex, ← h]
    push_cast
    ring
  linarith

/-- The grow member's displayed index, as a rational: `k_α + 1`. -/
theorem grow_newIndex_cast (shift : ShiftProfile input) :
    ((newIndex shift.growCandidate shift.movingAnchor : ℕ) : ℚ) =
      movingIndex shift + 1 := by
  rw [growCandidate_newIndex_moving shift, movingIndex]
  push_cast
  ring

/-- The census above `t_α`, in the form each member's determinant consumes. -/
theorem census_memberColumns (shrink : ShrinkData shift) (j : Fin 2)
    (row : Option target.edges) :
    selectedSumAt wall shift.movingAnchor (oldPath input row)
        (memberColumns shrink j).backgroundTarget =
      if row = rowMoving shift then
        (1 : ℚ) / data.sourceEdgeIndex shift.moving.1 else 0 := by
  have hBackground : (memberColumns shrink j).backgroundTarget =
      shift.movingTarget := by
    fin_cases j <;> rfl
  rw [hBackground]
  exact selectedSum_oldPath shift row

/-- **Figure 29's `c⁽¹⁾ = c(e_α)/(k_α − 1) + σ₀(J₀,α)`.** -/
theorem det_memberColumns_zero (shrink : ShrinkData shift) :
    (GluingDatum.LengthMatrixPresentation.matrix
        (ShiftMemberColumn.presentation (memberColumns shrink) (oldPath input) 0)).det =
      wallContribution shrink / (movingIndex shift - 1) +
        -(wallContribution shrink / movingIndex shift) := by
  rw [ShiftMemberColumn.det_eq_of_single (memberColumns shrink) (oldPath input) 0 0
    (rowMoving shift) shrink.remainder
    ((1 : ℚ) / data.sourceEdgeIndex shift.moving.1) rfl (census_memberColumns shrink 0)]
  show (1 : ℚ) / (newIndex shrink.shrinkCandidate shrink.remainder : ℕ) *
      wallContribution shrink -
    (1 : ℚ) / (data.sourceEdgeIndex shift.moving.1 : ℕ) * wallContribution shrink = _
  rw [shrink_newIndex_cast shrink, show
    ((data.sourceEdgeIndex shift.moving.1 : ℕ) : ℚ) = movingIndex shift from rfl]
  ring

/-- **Figure 29's `c⁽²⁾ = c(e_α)/(k_α + 1) + σ₀(J₀,α)`.** -/
theorem det_memberColumns_one (shrink : ShrinkData shift) :
    (GluingDatum.LengthMatrixPresentation.matrix
        (ShiftMemberColumn.presentation (memberColumns shrink) (oldPath input) 1)).det =
      wallContribution shrink / (movingIndex shift + 1) +
        -(wallContribution shrink / movingIndex shift) := by
  rw [ShiftMemberColumn.det_eq_of_single (memberColumns shrink) (oldPath input) 0 1
    (rowMoving shift) shift.movingAnchor
    ((1 : ℚ) / data.sourceEdgeIndex shift.moving.1) rfl (census_memberColumns shrink 1)]
  show (1 : ℚ) / (newIndex shift.growCandidate shift.movingAnchor : ℕ) *
      wallContribution shrink -
    (1 : ℚ) / (data.sourceEdgeIndex shift.moving.1 : ℕ) * wallContribution shrink = _
  rw [grow_newIndex_cast shift, show
    ((data.sourceEdgeIndex shift.moving.1 : ℕ) : ℚ) = movingIndex shift from rfl]
  ring

/-- **Figure 29's two displayed determinants.** -/
theorem det_memberColumns (shrink : ShrinkData shift) (i : Fin 2) :
    (GluingDatum.LengthMatrixPresentation.matrix
        (ShiftMemberColumn.presentation (memberColumns shrink) (oldPath input) i)).det =
      ![wallContribution shrink / (movingIndex shift - 1) +
          -(wallContribution shrink / movingIndex shift),
        wallContribution shrink / (movingIndex shift + 1) +
          -(wallContribution shrink / movingIndex shift)] i := by
  fin_cases i
  · exact det_memberColumns_zero shrink
  · exact det_memberColumns_one shrink

/-- **`W3ShiftClosure.LimitRows`, derived.**

Each member's presentation is `W3FourStableGraph.gaugePresentation` over the
limit's own stable rows (`limitRows_columnSum` below), the two determinants are
Figure 29's displayed `c(e_α)/(k_α ∓ 1) + σ₀(J₀,α)`, the limit's wall relation
`c(e_α)/k_α + σ₀(J₀,α) = 0` is the vanishing of the cofactor-weighted `t_α`
column, and `1 < k_α` is `W3ShiftClosure.one_lt_movingIndex`. -/
noncomputable def limitRows (shrink : ShrinkData shift) :
    W3ShiftClosure.LimitRows (shiftMembers shrink) (Option target.edges) where
  presentation := ShiftMemberColumn.presentation (memberColumns shrink) (oldPath input)
  wallColumn := none
  movingIndex := movingIndex shift
  wallContribution := wallContribution shrink
  wallSum := -(wallContribution shrink / movingIndex shift)
  one_lt_movingIndex' := W3ShiftClosure.one_lt_movingIndex shift
  wallRelation := by ring
  det := det_memberColumns shrink
  agreeOffWall := fun first second ↦
    ShiftMemberColumn.presentation_agreeOffWall (memberColumns shrink)
      (oldPath input) first second

/-- **The rows really are the limit's own.**  Every retained column of every
member's presentation is literally `StableSourceMatrix.matrix data` at the
corresponding stable path: the presentations are built on the limit's actual
stable-length matrix, relabelled, not on an arbitrary list family. -/
theorem limitRows_columnSum (shrink : ShrinkData shift) (i : Fin 2)
    (row : Option target.edges) (column : target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink).presentation i) row (some column) =
      StableSourceMatrix.matrix data ((labelling input).row.symm row) column :=
  (ShiftMemberColumn.matrix_some_eq (memberColumns shrink) (oldPath input) i row
    column).trans (columnSum_stableRowPath (labelling input) row column)

/-- **`σ₀(J₀,α)` is the limit's own background sum, not a free constant.**
`limitRows` sets `wallSum` to `−c(e_α)/k_α`, which makes its `wallRelation`
field a `ring` identity; this theorem is what makes that honest.  The
cofactor-weighted `t_α` column of the whole limit vanishes
(`ShiftMemberColumn.sum_columnSum_mul_cofactor`, the off-diagonal entry of
`adjugate M * M = det M • 1`), and the distinguished block contributes exactly
`c(e_α)/k_α` to it by the census, so what is left -- the contribution of every
*other* wall block, which is what Figure 29's `σ₀(J₀,α)` names -- is
`−c(e_α)/k_α`. -/
theorem wallSum_eq_background (shrink : ShrinkData shift) :
    (limitRows shrink).wallSum =
      ∑ row : Option target.edges,
        backgroundSumAt wall shift.movingAnchor (oldPath input row)
            shift.movingTarget *
          ShiftMemberColumn.cofactor (memberColumns shrink) (oldPath input) 0 row := by
  classical
  have hTotal := ShiftMemberColumn.sum_columnSum_mul_cofactor (memberColumns shrink)
    (oldPath input) 0 shift.movingTarget
  have hSplit : ∀ row : Option target.edges,
      columnSum (oldPath input row) shift.movingTarget *
          ShiftMemberColumn.cofactor (memberColumns shrink) (oldPath input) 0 row =
        selectedSumAt wall shift.movingAnchor (oldPath input row)
              shift.movingTarget *
            ShiftMemberColumn.cofactor (memberColumns shrink) (oldPath input) 0 row +
          backgroundSumAt wall shift.movingAnchor (oldPath input row)
              shift.movingTarget *
            ShiftMemberColumn.cofactor (memberColumns shrink) (oldPath input) 0 row := by
    intro row
    rw [columnSum_eq_at wall shift.movingAnchor (oldPath input row)
      shift.movingTarget]
    ring
  rw [Finset.sum_congr rfl (fun row (_ : row ∈ Finset.univ) ↦ hSplit row),
    Finset.sum_add_distrib] at hTotal
  have hSelected : (∑ row : Option target.edges,
      selectedSumAt wall shift.movingAnchor (oldPath input row) shift.movingTarget *
        ShiftMemberColumn.cofactor (memberColumns shrink) (oldPath input) 0 row) =
      (1 : ℚ) / (data.sourceEdgeIndex shift.moving.1 : ℕ) * wallContribution shrink := by
    simp only [selectedSum_oldPath shift]
    exact sum_ite_mul (rowMoving shift)
      ((1 : ℚ) / (data.sourceEdgeIndex shift.moving.1 : ℕ))
      (ShiftMemberColumn.cofactor (memberColumns shrink) (oldPath input) 0)
  rw [hSelected] at hTotal
  have hRing : (1 : ℚ) / (data.sourceEdgeIndex shift.moving.1 : ℕ) *
      wallContribution shrink =
      wallContribution shrink / movingIndex shift := by
    rw [movingIndex]
    ring
  show -(wallContribution shrink / movingIndex shift) = _
  linarith

/-- The shrink member of the derived pair is Figure 29's Position II.b member. -/
theorem shiftMembers_zero (shrink : ShrinkData shift) :
    shiftMembers shrink 0 = shrink.shrinkCandidate := rfl

/-- The grow member of the derived pair is Figure 29's Position II.a member. -/
theorem shiftMembers_one (shrink : ShrinkData shift) :
    shiftMembers shrink 1 = shift.growCandidate := rfl

end Derivation

/-! ## Towards the incoming member: the pair is separated at the wall

The incoming-member identification asks which member of Figure 29's family the
incoming cover itself is.  The shift case makes one half of that question
wall-local, and that half is settled here.

Every Figure 29 member shifts exactly one direction by `±1`, so the question is
(a) which direction moved and (b) whether it grew or shrank.  For (b) the pair
carries its own separating observable: the dilation index of the regrown
occurrence through the residual sheet is `k_α − 1` for the shrink member and
`k_α + 1` for the grow member, and `k_α ≥ 2` keeps these apart.  What follows
from that at the level of the determinants is that the two members are always of
*opposite sign*, so whichever member the incoming cover turns out to be, the exit
lands on the other one, and the exit's own nonsingularity gate is a condition on
the **limit** alone -- `c(e_α) ≠ 0` -- rather than on the member.

What is *not* settled here is (a), and the identification of the incoming cover
with a named member: that is the analogue of `W3Nd2IncomingMemberMatching`
(`W3ShiftIncomingMatching`) and needs the incoming contraction apparatus
(`IncomingTargetExpansion`, `FullDimensionalSource`, `WallDegeneration`, the
fibre census), none of which is touched in this module. -/

section Separation

variable {input : W3SourceInput data star} {shift : ShiftProfile input}

/-- **The pair's two members are distinct**, separated by Figure 29's own
observable: the dilation index of the regrown occurrence through the residual
sheet is `k_α − 1` for the shrink member and `k_α + 1` for the grow member.  This
is the wall-local half of "which member is the incoming one": identifying it is
identifying whether the moving direction grew or shrank. -/
theorem shiftMembers_ne (shrink : ShrinkData shift) :
    shiftMembers shrink 0 ≠ shiftMembers shrink 1 := by
  intro hEq
  have hIndex : newIndex (shiftMembers shrink 0) shrink.remainder =
      newIndex (shiftMembers shrink 1) shrink.remainder := by rw [hEq]
  have hZero : newIndex (shiftMembers shrink 0) shrink.remainder + 1 =
      data.sourceEdgeIndex shift.moving.1 := shrinkCandidate_newIndex_remainder shrink
  have hOne : newIndex (shiftMembers shrink 1) shrink.remainder =
      data.sourceEdgeIndex shift.moving.1 + 1 := growCandidate_newIndex_remainder shrink
  omega

/-- `k_α > 1`, in the form the arithmetic below consumes. -/
theorem one_lt_movingIndex (shift : ShiftProfile input) :
    (1 : ℚ) < movingIndex shift :=
  W3ShiftClosure.one_lt_movingIndex shift

/-- **The shrink member's determinant in closed form**:
`c(e_α)/(k_α − 1) − c(e_α)/k_α = c(e_α)/(k_α(k_α − 1))`. -/
theorem det_limitRows_zero (shrink : ShrinkData shift) :
    (GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink).presentation 0)).det =
      wallContribution shrink / (movingIndex shift * (movingIndex shift - 1)) := by
  have hOne := one_lt_movingIndex shift
  have hk : movingIndex shift ≠ 0 := ne_of_gt (by linarith)
  have hk1 : movingIndex shift - 1 ≠ 0 := ne_of_gt (by linarith)
  refine (det_memberColumns_zero shrink).trans ?_
  field_simp
  ring

/-- **The grow member's determinant in closed form**:
`c(e_α)/(k_α + 1) − c(e_α)/k_α = −c(e_α)/(k_α(k_α + 1))`. -/
theorem det_limitRows_one (shrink : ShrinkData shift) :
    (GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink).presentation 1)).det =
      -(wallContribution shrink / (movingIndex shift * (movingIndex shift + 1))) := by
  have hOne := one_lt_movingIndex shift
  have hk : movingIndex shift ≠ 0 := ne_of_gt (by linarith)
  have hk2 : movingIndex shift + 1 ≠ 0 := ne_of_gt (by linarith)
  refine (det_memberColumns_one shrink).trans ?_
  field_simp
  ring

/-- **The exit's nonsingularity gate is a condition on the limit alone.**  A
member of the pair is nonsingular exactly when the limit's cofactor `c(e_α)` --
the cofactor of the stable row displaying `e_α` -- is nonzero.  Neither
alternative for the incoming member is therefore more or less available than the
other. -/
theorem det_limitRows_zero_eq_zero_iff (shrink : ShrinkData shift) :
    (GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink).presentation 0)).det = 0 ↔
      wallContribution shrink = 0 := by
  have hOne := one_lt_movingIndex shift
  have hk : movingIndex shift ≠ 0 := ne_of_gt (by linarith)
  have hk1 : movingIndex shift - 1 ≠ 0 := ne_of_gt (by linarith)
  rw [det_limitRows_zero shrink, div_eq_zero_iff]
  exact or_iff_left (mul_ne_zero hk hk1)

theorem det_limitRows_one_eq_zero_iff (shrink : ShrinkData shift) :
    (GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink).presentation 1)).det = 0 ↔
      wallContribution shrink = 0 := by
  have hOne := one_lt_movingIndex shift
  have hk : movingIndex shift ≠ 0 := ne_of_gt (by linarith)
  have hk2 : movingIndex shift + 1 ≠ 0 := ne_of_gt (by linarith)
  rw [det_limitRows_one shrink, neg_eq_zero, div_eq_zero_iff]
  exact or_iff_left (mul_ne_zero hk hk2)

theorem det_limitRows_eq_zero_iff (shrink : ShrinkData shift) (i : Fin 2) :
    (GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink).presentation i)).det = 0 ↔
      wallContribution shrink = 0 := by
  fin_cases i
  · exact det_limitRows_zero_eq_zero_iff shrink
  · exact det_limitRows_one_eq_zero_iff shrink

/-- **Equation (3)'s two members always have opposite determinant sign.**  The
product is `−c(e_α)²/(k_α²(k_α − 1)(k_α + 1))`, and `k_α ≥ 2` makes the
denominator positive, so the sign is decided by the limit alone.  This is what
makes the incoming-member alternative harmless for the exit: whichever of the
two the incoming cover is, the other one is an outgoing member of opposite
sign. -/
theorem det_limitRows_mul_neg (shrink : ShrinkData shift)
    (hContribution : wallContribution shrink ≠ 0) :
    (GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink).presentation 0)).det *
      (GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink).presentation 1)).det < 0 := by
  have hOne := one_lt_movingIndex shift
  have hk : (0 : ℚ) < movingIndex shift := by linarith
  have hk1 : (0 : ℚ) < movingIndex shift - 1 := by linarith
  have hk2 : (0 : ℚ) < movingIndex shift + 1 := by linarith
  have hSquare : 0 < wallContribution shrink ^ 2 := by
    rcases lt_trichotomy (wallContribution shrink) 0 with hNeg | hZero | hPos
    · nlinarith
    · exact absurd hZero hContribution
    · nlinarith
  have hProduct : (wallContribution shrink /
        (movingIndex shift * (movingIndex shift - 1))) *
      -(wallContribution shrink / (movingIndex shift * (movingIndex shift + 1))) =
      -(wallContribution shrink ^ 2 /
        (movingIndex shift * (movingIndex shift - 1) *
          (movingIndex shift * (movingIndex shift + 1)))) := by
    field_simp
  rw [det_limitRows_zero shrink, det_limitRows_one shrink, hProduct]
  have hDenominator : (0 : ℚ) < movingIndex shift * (movingIndex shift - 1) *
      (movingIndex shift * (movingIndex shift + 1)) :=
    mul_pos (mul_pos hk hk1) (mul_pos hk hk2)
  have := div_pos hSquare hDenominator
  linarith

/-- A member never has opposite sign to itself, so an outgoing member of
opposite sign is the *other* member of the pair. -/
theorem ne_of_det_mul_neg (shrink : ShrinkData shift) {i j : Fin 2}
    (hSign : (GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink).presentation i)).det *
      (GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink).presentation j)).det < 0) : j ≠ i := by
  intro hEq
  rw [hEq] at hSign
  nlinarith [mul_self_nonneg (GluingDatum.LengthMatrixPresentation.matrix
    ((limitRows shrink).presentation i)).det]

end Separation

/-! ## Equation (3)'s exit over the derived rows -/

section Exit

variable {input : W3SourceInput data star} {shift : ShiftProfile input}

/-- **The gauge copy, carrying the derived `LimitRows`.**  The shift analogue
of `W3FourLimitRows.exists_figure28Receipts_of_input`: from a datum of the case
and any one of Figure 29's three orientations, a gauge copy of the whole shift
datum together with Equation (3)'s two members over it and the honest
length-matrix data `W3ShiftClosure.exists_equationThree_positive_exit` consumes,
with the moving direction, the moving index and the source genus of the
*original* datum. -/
theorem exists_shift_limitRows (hRetained : W3ShiftClosure.RetainedBelow shift)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ∃ (gaugeData : GluingDatum target degree) (gaugeInput : W3SourceInput gaugeData star)
      (gaugeShift : ShiftProfile gaugeInput) (shrink : ShrinkData gaugeShift),
      (data.Valid → gaugeData.Valid) ∧
      genus gaugeData.sourceGraph = genus data.sourceGraph ∧
      gaugeShift.movingTarget = shift.movingTarget ∧
      gaugeData.sourceEdgeIndex gaugeShift.moving.1 =
        data.sourceEdgeIndex shift.moving.1 ∧
      (limitRows shrink).movingIndex = (data.sourceEdgeIndex shift.moving.1 : ℚ) := by
  obtain ⟨gaugeData, gaugeInput, gaugeShift, copy, hSheet⟩ :=
    W3ShiftClosure.exists_gaugeCopy_shrinkSheet input shift hRetained hConnected hGenus
  obtain ⟨shrink⟩ := exists_shrinkData gaugeShift hSheet
  exact ⟨gaugeData, gaugeInput, gaugeShift, shrink, copy.valid_of_old,
    copy.sourceGenus, copy.movingTarget, copy.movingIndex,
    congrArg (fun index : ℕ ↦ (index : ℚ)) copy.movingIndex⟩

/-- **`W3ShiftClosure.exists_equationThree_positive_exit` with its supplied
`LimitRows` removed.**  Equation (3)'s certified positive exit, run on the pair's
*derived* length matrices: from the incoming member's nonsingular presentation
and a wall-crossing velocity there is an outgoing member of opposite determinant
sign, valid, reached along a segment that stays in the positive cone and matching
the incoming metric, with a cleared pencil at every point of it.

The gauge datum is the incoming datum itself here; the branch swaps that produce
it are `exists_shift_limitRows` above, whose `gaugeData` this is applied to.

`incoming` is universally quantified: identifying which of the two members the
incoming cover is, and on which direction, is the incoming-member problem and is
**not** solved here (see `W3ShiftIncomingMatching`). -/
theorem exists_equationThree_positive_exit_of_input (shrink : ShrinkData shift)
    (hValid : data.Valid) (hTargetConnected : graph_connected target)
    (hTargetGenus : genus target = 0) (root : target.V) (incoming : Fin 2)
    (hincoming : (GluingDatum.LengthMatrixPresentation.matrix
      ((limitRows shrink).presentation incoming)).det ≠ 0)
    (z incomingVelocity : Option target.edges → ℚ)
    (outgoingVelocity : Fin 2 → Option target.edges → ℚ)
    (hz : z none = 0) (hzpos : ∀ i, i ≠ none → 0 < z i)
    (hSystems : ∀ outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink).presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink).presentation incoming)).mulVec incomingVelocity =
      (GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink).presentation outgoing)).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity none < 0) :
    ∃ outgoing,
      (shiftMembers shrink outgoing).datum.Valid ∧
      (GluingDatum.LengthMatrixPresentation.matrix
          ((limitRows shrink).presentation incoming)).det *
        (GluingDatum.LengthMatrixPresentation.matrix
          ((limitRows shrink).presentation outgoing)).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
          ((limitRows shrink).presentation outgoing)).mulVec
            (z + t • outgoingVelocity outgoing) =
          (GluingDatum.LengthMatrixPresentation.matrix
            ((limitRows shrink).presentation incoming)).mulVec z +
          t • (GluingDatum.LengthMatrixPresentation.matrix
            ((limitRows shrink).presentation incoming)).mulVec incomingVelocity ∧
        Nonempty (Candidate.ClearedPencil (shiftMembers shrink outgoing)
          ((limitRows shrink).presentation outgoing)
          (z + t • outgoingVelocity outgoing)) :=
  W3ShiftClosure.exists_equationThree_positive_exit data (fun h ↦ h)
    (shiftMembers shrink) (limitRows shrink) hValid hTargetConnected hTargetGenus
    root incoming hincoming z incomingVelocity outgoingVelocity hz hzpos hSystems
    hIncomingDirection

/-- **The exit lands on the *other* member of the pair, and its gate is a
condition on the limit alone.**

Two things are gained over `exists_equationThree_positive_exit_of_input`, and
both come from `det_limitRows_mul_neg`: the nonsingularity hypothesis is replaced
by `c(e_α) ≠ 0`, a statement about the limit's own cofactor rather than about a
member, so it does not presuppose which member the incoming cover is; and the
outgoing member is certified distinct from the incoming one.

This is the half of the incoming-member problem the shift case makes wall-local.
The other half -- identifying the incoming cover with a named Figure 29 member,
which direction it moved and whether it grew or shrank -- is the analogue of
`W3Nd2IncomingMemberMatching` and is **not** proved here (see
`W3ShiftIncomingMatching`).  `shiftMembers_ne` records the observable that
settles the `±1` half of it. -/
theorem exists_equationThree_positive_exit_other (shrink : ShrinkData shift)
    (hValid : data.Valid) (hTargetConnected : graph_connected target)
    (hTargetGenus : genus target = 0) (root : target.V) (incoming : Fin 2)
    (hContribution : wallContribution shrink ≠ 0)
    (z incomingVelocity : Option target.edges → ℚ)
    (outgoingVelocity : Fin 2 → Option target.edges → ℚ)
    (hz : z none = 0) (hzpos : ∀ i, i ≠ none → 0 < z i)
    (hSystems : ∀ outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink).presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink).presentation incoming)).mulVec incomingVelocity =
      (GluingDatum.LengthMatrixPresentation.matrix
        ((limitRows shrink).presentation outgoing)).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity none < 0) :
    ∃ outgoing,
      outgoing ≠ incoming ∧
      (shiftMembers shrink outgoing).datum.Valid ∧
      (GluingDatum.LengthMatrixPresentation.matrix
          ((limitRows shrink).presentation incoming)).det *
        (GluingDatum.LengthMatrixPresentation.matrix
          ((limitRows shrink).presentation outgoing)).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
          ((limitRows shrink).presentation outgoing)).mulVec
            (z + t • outgoingVelocity outgoing) =
          (GluingDatum.LengthMatrixPresentation.matrix
            ((limitRows shrink).presentation incoming)).mulVec z +
          t • (GluingDatum.LengthMatrixPresentation.matrix
            ((limitRows shrink).presentation incoming)).mulVec incomingVelocity ∧
        Nonempty (Candidate.ClearedPencil (shiftMembers shrink outgoing)
          ((limitRows shrink).presentation outgoing)
          (z + t • outgoingVelocity outgoing)) := by
  obtain ⟨outgoing, hValidOut, hSign, hRest⟩ :=
    exists_equationThree_positive_exit_of_input shrink hValid hTargetConnected
      hTargetGenus root incoming
      (fun hDet ↦ hContribution ((det_limitRows_eq_zero_iff shrink incoming).mp hDet))
      z incomingVelocity outgoingVelocity hz hzpos hSystems hIncomingDirection
  exact ⟨outgoing, ne_of_det_mul_neg shrink hSign, hValidOut, hSign, hRest⟩

end Exit

end DraismaVargas.LocalCases.W3ShiftLimitRows
