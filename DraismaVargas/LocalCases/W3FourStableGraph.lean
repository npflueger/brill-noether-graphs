module

public import DraismaVargas.LocalCases.W3FourClosure

@[expose] public section

/-!
# Figure 28's four members: honest length matrices, and Equation (2) without `hDet`

Source: Draisma--Vargas Part I, case `{w3-r1-nd3-t2-(a=k₄)}`, its Positions
(set up in case `{w3-r1-nd3-t2}`), Figure 28 and Equation (2), and the general
`σ` bookkeeping of §6.2 (the balancing condition) and §6.7 (case-work), read
with the conventions recorded in `W3FourClosure`.

`W3FourClosure` builds all four members, proves them valid and genus
preserving with Figure 28's displayed new-edge indices, and assembles them into
`BalancedGlobal.Family` and into `GaugeFamily` -- the gauge-mixed analogue of
`BalancedGlobal.PresentedFamily`, which Figure 28 forces because `M⁽¹⁾` and
`M⁽²⁾` live on *branch-swapped* copies of the incoming datum.  There Figure
28's four determinants and the common off-wall columns enter
`equationTwoFamily` and `equationTwoGaugeFamily` as the named hypotheses `hDet`
and `hAgree`.  This module discharges both.

## What is proved here

* `WallTransport` and `WallTransport.ofSheetRelabeling` -- the only thing a
  length matrix reads off an occurrence is its target occurrence and its
  dilation index, and **every sheet relabelling of a gluing datum preserves
  both**.  So a branch swap is invisible to the matrix, which is what lets
  members living on different gauge copies be presented in one coordinate
  system.
* `gaugePresentation` -- the presentation of a wall family from paths, with the
  members allowed to sit over *different* gluing data, one per member, each
  reached by its own `WallTransport`.  `gaugePresentation_matrix_some` and
  `gaugePresentation_matrix_none` evaluate every entry, and
  `gaugePresentation_agreeOffWall` is **`hAgree`, discharged**: the retained
  columns are computed from the common old path alone.
* `columnSum`, `selectedSum`, `backgroundSum`, `backgroundSheetsOf` and
  `sum_backgroundSheetsOf` -- the split of an incoming column at the
  distinguished wall block, and the identity that turns a member's *background*
  regrown occurrences back into the limit's own `t_α` column.  The only input is
  an index identity at each background sheet, which is exactly Figure 28's
  `σ⁽ᵠ⁾(J₀, 1) = σ₀(J₀, α)`.
* `MemberColumn.det_eq` -- **the determinant of one member, evaluated**: the
  cofactor-weighted regrown contribution of the distinguished block minus its
  cofactor-weighted `t_α` contribution.  Nothing else survives, because the
  cofactor-weighted `t_α` column of the whole limit vanishes
  (`MemberColumn.sum_columnSum_mul_cofactor`, the off-diagonal entry of
  `adjugate M * M = det M • 1`).
* `reversedCandidate_newIndex_background` / `growCandidate_newIndex_background`
  -- **Figure 28's `α = 4, 4, 2, 3` read off the actual resolutions.**  Both
  `W3FourClosure.FourStarGeometry.wallBackground` and
  `W3FourSourceCandidates.GrowProfile.background` install
  `ResolutionCoarseFine.fineResolution` of one surviving direction on every
  background wall block: `t₄` for the two reversed members `M⁽¹⁾`, `M⁽²⁾` and
  the grow direction `t₂`, `t₃` for `M⁽³⁾`, `M⁽⁴⁾`.  That is the whole content
  of the paper's `σ⁽ᵠ⁾(J₀,1) = σ₀(J₀,α)` line, and it agrees with the figure.
* `Figure28Receipts.det_one` … `det_four` -- **Figure 28's four displayed
  determinants**, `c(e₂)/k₂ + c(e₃)/k₃ + σ₀(J₀,4)`,
  `c(e₄)/(k₂+k₃-1) + σ₀(J₀,4)`, `c(e₂)/(k₂+1) + σ₀(J₀,2)` and
  `c(e₃)/(k₃+1) + σ₀(J₀,3)`, with `σ₀(J₀,j) = -c(e_j)/k_j` *proved*, not
  assumed: the three relations displayed beside `M₀` in Figure 28 are the
  vanishing of the cofactor-weighted `t_j` columns.
* `Figure28Receipts.gaugeFamily` -- **`W3FourClosure.equationTwoGaugeFamily`
  with `hDet` and `hAgree` supplied**, and
  `Figure28Receipts.exists_valid_positive_exit_with_pencil` -- the certified
  positive exit with a cleared pencil for this case, carrying no determinant
  and no off-wall-agreement hypothesis at all.
* `exists_figure28Receipts` -- the receipts are those of the **actual** members:
  `M⁽³⁾`, `M⁽⁴⁾` are `W3FourSourceCandidates.thirdCandidate`/`fourthCandidate`
  (recorded by `HEq` in the conclusion, the two members' data being the incoming
  datum itself), and `M⁽¹⁾`, `M⁽²⁾` are the Position I and Position II.b members
  that `W3FourClosure.exists_member_one`/`exists_member_two` build on
  branch-swapped copies, carrying their `BranchGauge.valid`.
* `LimitRows.model` and `nonempty_figure28Receipts` -- nothing above is vacuous.

## What is not proved here

**The stable-row census is a hypothesis here.**  `LimitRows` names the rows
displaying `e₂`, `e₃`, `e₄` and says that the distinguished wall block
contributes exactly `1/k_j` to the `t_j` column of that row and nothing to any
other row.  It is not derived from `ThirdEquation.W3SourceInput` in this
module; `W3FourLimitRows` derives it from the limit's own stable source.
Correspondingly:

* `MemberColumn.selectedSheets` and `MemberColumn.newSheets` **supply** the
  regrown row assignment rather than deriving it from the outgoing stable graph.
  `GluingDatum.LengthMatrixPresentation` deliberately takes its paths as data
  (see `DraismaVargas.Infrastructure.LengthMatrix`), and `GlobalW4`'s
  `canonicalPresentationOfPaths` is used the same way, with honesty proved one
  module later (`W4OutgoingLimitMatrix.presented_matrix_eq`).  The analogue for
  these four members -- that `MemberColumn.presentation` is
  `StableSourceMatrix.matrix` of the member at its honest stable rows -- is
  `W3FourRegrownColumn.ColumnData.presented_matrix_eq` with
  `exists_figure28Receipts_honest`, and `W3FourHonestBalance` packages the
  honest gauge family.
* No `StableGraphIncidence.Equivalence` between the incoming cover and any of
  the four members is built here, and no survival or endpoint census
  (`nonDanglingIncident`) is computed; the equivalences are
  `W3FourRowDescent.{PositionOne, PositionTwo, GrowMember}.equivalence`,
  packaged with the gauge in `W3FourStableIncidence.exists_figure28Dictionaries`.
  `LimitRows.model` is a consistency witness only: it makes nothing vacuous and
  certifies nothing honest.
* The incoming-member identification and the original-coordinate exit are
  `W3FourIncomingMatching` and `W3FourArbitraryExit`.

**Where the geometry really did the work.**  Splitting `hDet` this way is the
mathematical content of the module: the determinant of a member is
`(regrown contribution of A₀) - (its t_α contribution)`, and the *first* term is
fixed by the member's own local resolution while the *second* is fixed by which
direction resolves the background.  Both are wall-local and are discharged above
from `FourStarGeometry` and from the two candidate constructions.  What is not
wall-local, and therefore cannot be discharged from `W3SourceInput` at the wall,
is *which stable row* displays each occurrence; that is the whole of `LimitRows`.

## Why the hypotheses can hold at once

`Figure28Receipts` bundles a census of the limit with four members' receipts.
`exists_figure28Receipts` produces the four members' half from an arbitrary
`ThirdEquation.W3SourceInput`, an arbitrary `W3R1SourceProfile.Nd3Profile`, the
case's index identity and the three branch flags -- the same hypotheses
`W3FourClosure.exists_equationTwo_family` uses, and satisfiable together for the
reasons recorded there.  `LimitRows.model` produces the census half on *any*
datum of the case, using only that `t₂`, `t₃`, `t₄` are distinct.  Composing
them, `nonempty_figure28Receipts` inhabits the whole structure, so no theorem
stated against it is vacuous.  The four determinant values are not constrained
to be nonzero anywhere, and nothing here asserts that any member is nonsingular
-- `BalancingValencyTwo.PositiveBalance` is a signed balance, and the exit
theorem keeps its own `det ≠ 0` gate.

Nothing here asks the three rows `rowGrow`, `rowOther`, `rowLargest` to be
distinct: two surviving occurrences at a branch vertex may represent one stable
row, and every determinant formula above holds verbatim in that case.  That is
why the regrown assignments are built by `List` concatenation of `single`s
rather than by a case split on the row.

## Which datum this is about

The census, the members and the gauges all live on the wall/limit side of the
bridge recorded in
`FullDimensionalSource.false_of_changeMinimal_auxR0SourceInput`, exactly as
`W3FourClosure` and `W3FourSourceCandidates` do.  The presentations are
presentations of the **outgoing** members' data, which is the other side; no
single object is asked to be both.
-/namespace DraismaVargas.LocalCases.W3FourStableGraph

open DraismaVargas.Infrastructure
open TargetExpansion
open BalancedGlobal
open ResolutionM11 ResolutionCoarseFine ThirdEquation W3R1SourceProfile
open W3FourDisjointness
open W3FourClosure

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## What a gauge move leaves of the incoming occurrence set -/

/-- The only thing a length matrix reads off a source occurrence: which target
occurrence it lies above, and its dilation index.  A `WallTransport` is a map
of occurrence sets preserving both, which is all that a *gauge* -- a branch
swap -- has to supply for the four Figure 28 members to be presented in one
common coordinate system. -/
structure WallTransport (data base : GluingDatum target degree) where
  /-- The underlying map of occurrence-labelled source edges. -/
  edge : data.SourceEdge → base.SourceEdge
  /-- It preserves the target occurrence an edge lies above. -/
  target_eq : ∀ e, (edge e).1.1 = e.1.1
  /-- It preserves the dilation index. -/
  index_eq : ∀ e, base.sourceEdgeIndex (edge e) = data.sourceEdgeIndex e

namespace WallTransport

/-- The identity gauge, for a member built on the incoming datum itself. -/
def refl (data : GluingDatum target degree) : WallTransport data data where
  edge := _root_.id
  target_eq _ := rfl
  index_eq _ := rfl

/-- **Every sheet relabelling is a gauge for the length matrix.**  The
branch swap of `W3FourDisjointness.branchSwapOfPerm` is one of these, so the
two members that live on branch-swapped copies present in the same coordinates
as the two that live on the incoming datum. -/
def ofSheetRelabeling (relabeling : data.SheetRelabeling) :
    WallTransport data relabeling.apply where
  edge := relabeling.sourceEdgeEquiv
  target_eq _ := rfl
  index_eq e := by
    change ((data.edgePartition e.1.1).relabel
      (relabeling.edgePermutation e.1.1)).blockCard
        (relabeling.edgePermutation e.1.1 e.1.2) = _
    exact SheetPartition.relabel_blockCard _ _ _

end WallTransport


/-! ## Canonically presented gauge-mixed families

The canonical presentation of a wall family from paths (compare
`GlobalW4.canonicalPresentationOfPaths`) builds the members from one common list
of retained old occurrences per stable row plus the regrown occurrences assigned
to that row, and derives off-wall agreement from the construction. It requires
every member to sit over **one** gluing datum, which Figure 28's four members do
not: `M⁽¹⁾` and `M⁽²⁾` live on branch-swapped copies. The version below carries
one `WallTransport` per member, which is exactly what a branch swap supplies,
and is otherwise the same construction. -/

section Presentation

variable {n : ℕ}

/-- The canonical presentation of one member of a gauge-mixed wall family:
push the common old path through that member's gauge, lift it into the member,
then adjoin the regrown occurrences assigned to that row. -/
noncomputable def gaugePresentation
    (base : Fin n → GluingDatum target degree)
    (transport : ∀ i, WallTransport data (base i))
    (member : ∀ i, Candidate target degree (base i) wall)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin n → Option target.edges → List (Fin degree))
    (i : Fin n) :
    (member i).datum.LengthMatrixPresentation (Option target.edges) where
  targetEdge := occurrenceEquiv target wall (member i).right
  path row :=
    ((oldPath row).map fun e ↦ (member i).oldSourceEdge ((transport i).edge e)) ++
      (newSheets i row).map (member i).newSourceEdge

variable (base : Fin n → GluingDatum target degree)
  (transport : ∀ i, WallTransport data (base i))
  (member : ∀ i, Candidate target degree (base i) wall)
  (oldPath : Option target.edges → List data.SourceEdge)
  (newSheets : Fin n → Option target.edges → List (Fin degree))

/-- The dilation index of a member's regrown occurrence through a sheet. -/
noncomputable def newIndex {b : GluingDatum target degree}
    (candidate : Candidate target degree b wall) (sheet : Fin degree) : ℕ :=
  candidate.datum.sourceEdgeIndex (candidate.newSourceEdge sheet)

/-- It is the new-edge block cardinality of the pasted local resolution. -/
theorem newIndex_eq {b : GluingDatum target degree}
    (candidate : Candidate target degree b wall) (sheet : Fin degree) :
    newIndex candidate sheet =
      (LocalResolution.paste (b.vertexPartition wall) candidate.resolution
        candidate.contracts).newEdge.blockCard sheet :=
  Candidate.sourceEdgeIndex_newSourceEdge candidate sheet

/-- A retained occurrence contributes its own original reciprocal index to its
own old column, whichever gauge it was pushed through. -/
theorem gaugePresentation_coefficient_old (i : Fin n) (e : data.SourceEdge)
    (column : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.coefficient
        (gaugePresentation base transport member oldPath newSheets i)
        ((member i).oldSourceEdge ((transport i).edge e)) column =
      if column = some e.1.1 then (1 : ℚ) / data.sourceEdgeIndex e else 0 := by
  classical
  have hTarget : ((member i).oldSourceEdge ((transport i).edge e)).1.1 =
      occurrenceEquiv target wall (member i).right (some e.1.1) := by
    rw [Candidate.oldSourceEdge_target, (transport i).target_eq e]
  have hIndex : (member i).datum.sourceEdgeIndex
      ((member i).oldSourceEdge ((transport i).edge e)) = data.sourceEdgeIndex e := by
    rw [Candidate.sourceEdgeIndex_oldSourceEdge, (transport i).index_eq e]
  unfold GluingDatum.LengthMatrixPresentation.coefficient
  rw [hIndex, hTarget]
  have hSymm : (gaugePresentation base transport member oldPath newSheets
      i).targetEdge.symm (occurrenceEquiv target wall (member i).right
        (some e.1.1)) = some e.1.1 := by
    change (occurrenceEquiv target wall (member i).right).symm
      (occurrenceEquiv target wall (member i).right (some e.1.1)) = _
    exact Equiv.symm_apply_apply _ _
  rw [hSymm]

/-- A regrown occurrence contributes zero to every retained old column. -/
theorem gaugePresentation_coefficient_new_some (i : Fin n) (sheet : Fin degree)
    (column : target.edges) :
    GluingDatum.LengthMatrixPresentation.coefficient
        (gaugePresentation base transport member oldPath newSheets i)
        ((member i).newSourceEdge sheet) (some column) = 0 := by
  classical
  unfold GluingDatum.LengthMatrixPresentation.coefficient
  have hSymm : (gaugePresentation base transport member oldPath newSheets
      i).targetEdge.symm ((member i).newSourceEdge sheet).1.1 = none := by
    change (occurrenceEquiv target wall (member i).right).symm
      (occurrenceEquiv target wall (member i).right none) = _
    exact Equiv.symm_apply_apply _ _
  rw [hSymm]
  simp

/-- A regrown occurrence contributes its reciprocal new-edge index to the
regrown column. -/
theorem gaugePresentation_coefficient_new_none (i : Fin n) (sheet : Fin degree) :
    GluingDatum.LengthMatrixPresentation.coefficient
        (gaugePresentation base transport member oldPath newSheets i)
        ((member i).newSourceEdge sheet) none =
      (1 : ℚ) / newIndex (member i) sheet := by
  classical
  unfold GluingDatum.LengthMatrixPresentation.coefficient
  have hSymm : (gaugePresentation base transport member oldPath newSheets
      i).targetEdge.symm ((member i).newSourceEdge sheet).1.1 = none := by
    change (occurrenceEquiv target wall (member i).right).symm
      (occurrenceEquiv target wall (member i).right none) = _
    exact Equiv.symm_apply_apply _ _
  rw [hSymm]
  simp [newIndex]

/-- The common old column: every retained entry is computed from the common
old path alone, through any member's gauge. -/
theorem gaugePresentation_matrix_some (i : Fin n) (row : Option target.edges)
    (column : target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix
        (gaugePresentation base transport member oldPath newSheets i) row
        (some column) =
      ((oldPath row).map fun e ↦
        if column = e.1.1 then (1 : ℚ) / data.sourceEdgeIndex e else 0).sum := by
  classical
  unfold GluingDatum.LengthMatrixPresentation.matrix
    GluingDatum.LengthMatrixPresentation.row
  show ((((oldPath row).map fun e ↦
        (member i).oldSourceEdge ((transport i).edge e)) ++
      (newSheets i row).map (member i).newSourceEdge).map fun edge ↦
        GluingDatum.LengthMatrixPresentation.coefficient
          (gaugePresentation base transport member oldPath newSheets i) edge
          (some column)).sum = _
  rw [List.map_append, List.sum_append, List.map_map, List.map_map]
  have hNew : (((newSheets i row).map fun sheet ↦
      GluingDatum.LengthMatrixPresentation.coefficient
        (gaugePresentation base transport member oldPath newSheets i)
        ((member i).newSourceEdge sheet) (some column))).sum = 0 := by
    rw [List.map_congr_left (fun sheet _ ↦
      gaugePresentation_coefficient_new_some base transport member oldPath
        newSheets i sheet column)]
    simp
  have hOld : (((oldPath row).map fun e ↦
      GluingDatum.LengthMatrixPresentation.coefficient
        (gaugePresentation base transport member oldPath newSheets i)
        ((member i).oldSourceEdge ((transport i).edge e)) (some column))).sum =
      ((oldPath row).map fun e ↦
        if column = e.1.1 then (1 : ℚ) / data.sourceEdgeIndex e else 0).sum := by
    refine congrArg List.sum (List.map_congr_left fun e _ ↦ ?_)
    rw [gaugePresentation_coefficient_old base transport member oldPath
      newSheets i e (some column)]
    by_cases hEq : column = e.1.1
    · rw [ite_eq_left hEq, ite_eq_left (congrArg some hEq)]
    · rw [ite_eq_right hEq, ite_eq_right (fun h ↦ hEq (Option.some.inj h))]
  change (((oldPath row).map fun e ↦
      GluingDatum.LengthMatrixPresentation.coefficient
        (gaugePresentation base transport member oldPath newSheets i)
        ((member i).oldSourceEdge ((transport i).edge e)) (some column))).sum +
    (((newSheets i row).map fun sheet ↦
      GluingDatum.LengthMatrixPresentation.coefficient
        (gaugePresentation base transport member oldPath newSheets i)
        ((member i).newSourceEdge sheet) (some column))).sum = _
  rw [hOld, hNew, add_zero]

/-- The regrown column: only the assigned new sheets contribute, each through
its own new-edge index. -/
theorem gaugePresentation_matrix_none (i : Fin n) (row : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix
        (gaugePresentation base transport member oldPath newSheets i) row none =
      ((newSheets i row).map fun sheet ↦
        (1 : ℚ) / newIndex (member i) sheet).sum := by
  classical
  unfold GluingDatum.LengthMatrixPresentation.matrix
    GluingDatum.LengthMatrixPresentation.row
  show ((((oldPath row).map fun e ↦
        (member i).oldSourceEdge ((transport i).edge e)) ++
      (newSheets i row).map (member i).newSourceEdge).map fun edge ↦
        GluingDatum.LengthMatrixPresentation.coefficient
          (gaugePresentation base transport member oldPath newSheets i) edge
          none).sum = _
  rw [List.map_append, List.sum_append, List.map_map, List.map_map]
  have hOld : (((oldPath row).map fun e ↦
      GluingDatum.LengthMatrixPresentation.coefficient
        (gaugePresentation base transport member oldPath newSheets i)
        ((member i).oldSourceEdge ((transport i).edge e)) none)).sum = 0 := by
    rw [List.map_congr_left (fun e _ ↦ by
      rw [gaugePresentation_coefficient_old base transport member oldPath
        newSheets i e none, ite_eq_right (by simp)]
      : ∀ e ∈ oldPath row,
        GluingDatum.LengthMatrixPresentation.coefficient
          (gaugePresentation base transport member oldPath newSheets i)
          ((member i).oldSourceEdge ((transport i).edge e)) none = 0)]
    simp
  have hNew : (((newSheets i row).map fun sheet ↦
      GluingDatum.LengthMatrixPresentation.coefficient
        (gaugePresentation base transport member oldPath newSheets i)
        ((member i).newSourceEdge sheet) none)).sum =
      ((newSheets i row).map fun sheet ↦
        (1 : ℚ) / newIndex (member i) sheet).sum :=
    congrArg List.sum (List.map_congr_left fun sheet _ ↦
      gaugePresentation_coefficient_new_none base transport member oldPath
        newSheets i sheet)
  change (((oldPath row).map fun e ↦
      GluingDatum.LengthMatrixPresentation.coefficient
        (gaugePresentation base transport member oldPath newSheets i)
        ((member i).oldSourceEdge ((transport i).edge e)) none)).sum +
    (((newSheets i row).map fun sheet ↦
      GluingDatum.LengthMatrixPresentation.coefficient
        (gaugePresentation base transport member oldPath newSheets i)
        ((member i).newSourceEdge sheet) none)).sum = _
  rw [hOld, hNew, zero_add]

/-- **Off-wall agreement, from the construction.**  This is the `hAgree`
hypothesis of `W3FourClosure.equationTwoFamily` and
`W3FourClosure.equationTwoGaugeFamily`, discharged: every column other than
the regrown one is read off the common old path, and the gauges preserve both
the target occurrence and the index of every retained occurrence. -/
theorem gaugePresentation_agreeOffWall (first second : Fin n) :
    AgreeOffColumn
      (GluingDatum.LengthMatrixPresentation.matrix
        (gaugePresentation base transport member oldPath newSheets first))
      (GluingDatum.LengthMatrixPresentation.matrix
        (gaugePresentation base transport member oldPath newSheets second))
      none := by
  intro row column hColumn
  cases column with
  | none => exact (hColumn rfl).elim
  | some edge =>
      rw [gaugePresentation_matrix_some, gaugePresentation_matrix_some]

end Presentation

/-! ## Splitting an incoming column at the distinguished wall block

Figure 28's `σ₀(J₀, α)` is the part of the limit's `t_α` column contributed by
the *other* wall blocks.  The three functions below are that split, at the level
of one displayed stable row: `columnSum` is the whole `t` entry of the row,
`selectedSum` the part contributed by occurrences lying over the distinguished
wall block `A₀`, and `backgroundSum` the rest.  `backgroundSheetsOf` lists the
sheets of the background part, which is exactly the list of regrown occurrences
a Figure 28 member displays in that row above its background blocks. -/

section Columns

variable (geometry : FourStarGeometry data wall)

/-- The `t` entry of one displayed row of the limit. -/
noncomputable def columnSum (path : List data.SourceEdge) (t : target.edges) : ℚ :=
  (path.map fun e ↦
    if t = e.1.1 then (1 : ℚ) / data.sourceEdgeIndex e else 0).sum

/-- Its part contributed by the distinguished wall block. -/
noncomputable def selectedSum (path : List data.SourceEdge) (t : target.edges) : ℚ :=
  (path.map fun e ↦
    if t = e.1.1 ∧ (data.vertexPartition wall).Rel geometry.growAnchor e.1.2 then
      (1 : ℚ) / data.sourceEdgeIndex e else 0).sum

/-- Its part contributed by every other wall block: Figure 28's `σ₀(J₀, ·)`
before the cofactor weighting. -/
noncomputable def backgroundSum (path : List data.SourceEdge) (t : target.edges) : ℚ :=
  (path.map fun e ↦
    if t = e.1.1 ∧ ¬(data.vertexPartition wall).Rel geometry.growAnchor e.1.2 then
      (1 : ℚ) / data.sourceEdgeIndex e else 0).sum

/-- The sheets of the background part, in the order the row displays them. -/
noncomputable def backgroundSheetsOf (path : List data.SourceEdge)
    (t : target.edges) : List (Fin degree) :=
  path.filterMap fun e ↦
    if t = e.1.1 ∧ ¬(data.vertexPartition wall).Rel geometry.growAnchor e.1.2 then
      some e.1.2 else none

/-- The split itself. -/
theorem columnSum_eq (path : List data.SourceEdge) (t : target.edges) :
    columnSum path t = selectedSum geometry path t + backgroundSum geometry path t := by
  classical
  induction path with
  | nil => simp [columnSum, selectedSum, backgroundSum]
  | cons e rest ih =>
      simp only [columnSum, selectedSum, backgroundSum, List.map_cons,
        List.sum_cons] at ih ⊢
      by_cases hTarget : t = e.1.1
      · by_cases hRel : (data.vertexPartition wall).Rel geometry.growAnchor e.1.2
        · rw [ite_eq_left hTarget, ite_eq_left ⟨hTarget, hRel⟩, ite_eq_right (by tauto)]
          rw [ih]; ring
        · rw [ite_eq_left hTarget, ite_eq_right (by tauto), ite_eq_left ⟨hTarget, hRel⟩]
          rw [ih]; ring
      · rw [ite_eq_right hTarget, ite_eq_right (by tauto), ite_eq_right (by tauto)]
        rw [ih]; ring

/-- **The background regrown occurrences of a row reproduce its `t` column,
minus the distinguished block's part.**  The only input is that the regrown
index at a background sheet is that sheet's `t` index -- which is what
"the background blocks are resolved with the `t_α` partition on the new edge"
says, and is exactly Figure 28's `σ⁽ᵠ⁾(J₀, 1) = σ₀(J₀, α)`. -/
theorem sum_backgroundSheetsOf (path : List data.SourceEdge) (t : target.edges)
    (index : Fin degree → ℕ)
    (hIndex : ∀ sheet, ¬(data.vertexPartition wall).Rel geometry.growAnchor sheet →
      index sheet = (data.edgePartition t).blockCard sheet) :
    ((backgroundSheetsOf geometry path t).map fun sheet ↦
        (1 : ℚ) / index sheet).sum =
      backgroundSum geometry path t := by
  classical
  induction path with
  | nil => simp [backgroundSheetsOf, backgroundSum]
  | cons e rest ih =>
      by_cases hCond : t = e.1.1 ∧
          ¬(data.vertexPartition wall).Rel geometry.growAnchor e.1.2
      · have hIdx : index e.1.2 = data.sourceEdgeIndex e := by
          rw [hIndex e.1.2 hCond.2]
          exact congrArg (fun p ↦ SheetPartition.blockCard p e.1.2)
            (congrArg data.edgePartition hCond.1)
        simp only [backgroundSheetsOf, backgroundSum, List.filterMap_cons,
          List.map_cons, List.sum_cons, ite_eq_left hCond] at ih ⊢
        rw [hIdx, ih]
      · simp only [backgroundSheetsOf, backgroundSum, List.filterMap_cons,
          List.map_cons, List.sum_cons, ite_eq_right hCond] at ih ⊢
        rw [ih, zero_add]

end Columns

/-! ## The determinant of one Figure 28 member -/

section Determinant

/-- Everything one member of Figure 28 supplies to the determinant
computation: the gauge it lives on, its globally assembled candidate, the
surviving direction whose partition resolves the *background* wall blocks on
the new edge, and the list of regrown occurrences it displays over the
distinguished block in each stable row. -/
structure MemberColumn (data : GluingDatum target degree) (wall : target.V)
    (geometry : FourStarGeometry data wall) where
  /-- The gauge copy of the incoming datum this member lives on. -/
  base : GluingDatum target degree
  /-- The gauge itself. -/
  transport : WallTransport data base
  /-- The member. -/
  candidate : Candidate target degree base wall
  /-- `t_α`: the direction whose partition the member installs on the new edge
  above every background wall block. -/
  backgroundTarget : target.edges
  /-- Which is exactly what this field says, index by index. -/
  background_index : ∀ sheet,
    ¬(data.vertexPartition wall).Rel geometry.growAnchor sheet →
    newIndex candidate sheet = (data.edgePartition backgroundTarget).blockCard sheet
  /-- The gauge is a gauge: the copy is valid whenever the incoming datum is.
  This is `W3FourDisjointness.BranchGauge.valid`. -/
  valid_of_old : data.Valid → base.Valid
  /-- The regrown occurrences the member displays over the distinguished
  block, listed by stable row. -/
  selectedSheets : Option target.edges → List (Fin degree)

namespace MemberColumn

variable {geometry : FourStarGeometry data wall} {n : ℕ}
  (member : Fin n → MemberColumn data wall geometry)
  (oldPath : Option target.edges → List data.SourceEdge)

/-- The complete regrown row of a member: its distinguished occurrences
followed by its background ones. -/
noncomputable def newSheets (i : Fin n) (row : Option target.edges) :
    List (Fin degree) :=
  (member i).selectedSheets row ++
    backgroundSheetsOf geometry (oldPath row) (member i).backgroundTarget

/-- The four canonically presented members. -/
noncomputable def presentation (i : Fin n) :
    ((member i).candidate).datum.LengthMatrixPresentation (Option target.edges) :=
  gaugePresentation (fun j ↦ (member j).base) (fun j ↦ (member j).transport)
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

/-- **The regrown column, evaluated.**  In every stable row it is the
distinguished block's own regrown contribution plus the limit's `t_α` entry of
that row with the distinguished block's part removed. -/
theorem matrix_none_eq (i : Fin n) (row : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix
        (presentation member oldPath i) row none =
      selectedNewSum member i row +
        (columnSum (oldPath row) (member i).backgroundTarget -
          selectedSum geometry (oldPath row) (member i).backgroundTarget) := by
  classical
  rw [presentation, gaugePresentation_matrix_none, newSheets, List.map_append,
    List.sum_append,
    sum_backgroundSheetsOf geometry (oldPath row) (member i).backgroundTarget
      (fun sheet ↦ newIndex (member i).candidate sheet)
      (fun sheet hSheet ↦ (member i).background_index sheet hSheet),
    columnSum_eq geometry (oldPath row) (member i).backgroundTarget]
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

/-- The cofactor row belongs to the *family*, not to one member: all the
presentations agree off the regrown column, so their `none`-column adjugate rows
coincide.  This is why Figure 28's `c(e₂)`, `c(e₃)`, `c(e₄)` are well defined. -/
theorem cofactor_eq (first second : Fin n) (row : Option target.edges) :
    cofactor member oldPath first row = cofactor member oldPath second row :=
  adjugate_wallRow_eq_of_agreeOffColumn
    (presentation_agreeOffWall member oldPath first second) row

/-- **The cofactor-weighted `t` column of the limit vanishes** for every
retained direction `t`.  This is the off-diagonal entry of
`adjugate M * M = det M • 1`, and it is what makes Figure 28's three displayed
limit relations `c(e_j)/k_j + σ₀(J₀, j) = 0` theorems rather than
hypotheses. -/
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

/-- **A Figure 28 member's determinant.**  It is the cofactor-weighted regrown
contribution of the distinguished wall block, minus the cofactor-weighted `t_α`
contribution of that same block.  Nothing else survives: the background blocks
reproduce the limit's own `t_α` column, whose cofactor-weighted sum is zero. -/
theorem det_eq (i : Fin n) :
    (GluingDatum.LengthMatrixPresentation.matrix
        (presentation member oldPath i)).det =
      (∑ row : Option target.edges,
          selectedNewSum member i row * cofactor member oldPath reference row) -
        ∑ row : Option target.edges,
          selectedSum geometry (oldPath row) (member i).backgroundTarget *
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
        selectedSum geometry (oldPath row) (member i).backgroundTarget *
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
            selectedSum geometry (oldPath row) (member i).backgroundTarget *
              cofactor member oldPath reference row) :=
      Finset.sum_congr rfl fun row _ ↦ hSplit row
    _ = (∑ row : Option target.edges,
            selectedNewSum member i row * cofactor member oldPath reference row) +
          (∑ row : Option target.edges,
            columnSum (oldPath row) (member i).backgroundTarget *
              cofactor member oldPath reference row) -
          ∑ row : Option target.edges,
            selectedSum geometry (oldPath row) (member i).backgroundTarget *
              cofactor member oldPath reference row := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_columnSum_mul_cofactor member oldPath reference
        (member i).backgroundTarget, add_zero]

end MemberColumn

end Determinant

/-! ## The limit's stable-row census

Figure 28's four determinants are read against three quantities of the limit
`M₀`: the cofactors `c(e₂)`, `c(e₃)`, `c(e₄)` of the stable rows displaying its
three surviving wall occurrences.  The structure below is the exact census that
names them.  Nothing here asks the three rows to be distinct: two surviving
occurrences at a branch vertex may represent one stable row (a stable loop), and
the determinant formulas below hold verbatim in that case. -/

section Census

/-- The limit's displayed stable rows, together with the identification of the
distinguished wall block's contribution to each of the three surviving
directions.  Each `selected_*` field says: above `t_j`, the distinguished wall
block displays exactly the one occurrence `e_j`, in the row `row_j`, with its
own index `k_j`. -/
structure LimitRows (data : GluingDatum target degree) (wall : target.V)
    (geometry : FourStarGeometry data wall) where
  /-- The displayed old occurrences of each stable row. -/
  oldPath : Option target.edges → List data.SourceEdge
  /-- The row displaying `e₂`. -/
  rowGrow : Option target.edges
  /-- The row displaying `e₃`. -/
  rowOther : Option target.edges
  /-- The row displaying `e₄`. -/
  rowLargest : Option target.edges
  /-- Above `t₂` the block displays `e₂` alone, in `rowGrow`. -/
  selected_grow : ∀ row, selectedSum geometry (oldPath row) geometry.growTarget =
    if row = rowGrow then
      (1 : ℚ) / (data.edgePartition geometry.growTarget).blockCard geometry.growAnchor
    else 0
  /-- Above `t₃` the block displays `e₃` alone, in `rowOther`. -/
  selected_other : ∀ row, selectedSum geometry (oldPath row) geometry.otherTarget =
    if row = rowOther then
      (1 : ℚ) / (data.edgePartition geometry.otherTarget).blockCard geometry.otherAnchor
    else 0
  /-- Above `t₄` the block displays `e₄` alone, in `rowLargest`. -/
  selected_largest : ∀ row,
    selectedSum geometry (oldPath row) geometry.largestTarget =
    if row = rowLargest then
      (1 : ℚ) /
        (data.edgePartition geometry.largestTarget).blockCard geometry.largestAnchor
    else 0

/-- A regrown row assignment displaying one occurrence through `sheet` in row
`r`, and nothing anywhere else. -/
noncomputable def single (r : Option target.edges) (sheet : Fin degree) :
    Option target.edges → List (Fin degree) :=
  fun row ↦ if row = r then [sheet] else []

variable {geometry : FourStarGeometry data wall}

theorem sum_ite_mul (r : Option target.edges) (value : ℚ)
    (cofactor : Option target.edges → ℚ) :
    ∑ row : Option target.edges, (if row = r then value else 0) * cofactor row =
      value * cofactor r := by
  classical
  simp only [ite_mul, zero_mul]
  exact Finset.sum_ite_eq' Finset.univ r (fun row ↦ value * cofactor row) |>.trans
    (by simp)

theorem single_map_sum (r : Option target.edges) (sheet : Fin degree)
    (weight : Fin degree → ℚ) (row : Option target.edges) :
    ((single r sheet row).map weight).sum =
      if row = r then weight sheet else 0 := by
  unfold single
  split_ifs <;> simp

namespace MemberColumn

variable {n : ℕ} (member : Fin n → MemberColumn data wall geometry)
  (oldPath : Option target.edges → List data.SourceEdge) (reference : Fin n)

/-- One displayed regrown occurrence: the cofactor-weighted regrown
contribution is its reciprocal index times its row's cofactor. -/
theorem sum_selectedNewSum_single (i : Fin n) (r : Option target.edges)
    (sheet : Fin degree)
    (hSel : (member i).selectedSheets = single r sheet) :
    ∑ row : Option target.edges,
        selectedNewSum member i row * cofactor member oldPath reference row =
      (1 : ℚ) / newIndex (member i).candidate sheet *
        cofactor member oldPath reference r := by
  classical
  rw [← sum_ite_mul r ((1 : ℚ) / newIndex (member i).candidate sheet)
    (cofactor member oldPath reference)]
  refine Finset.sum_congr rfl fun row _ ↦ ?_
  rw [selectedNewSum, hSel, single_map_sum]

/-- Two displayed regrown occurrences, in possibly equal rows. -/
theorem sum_selectedNewSum_pair (i : Fin n)
    (first second : Option target.edges) (sheetFirst sheetSecond : Fin degree)
    (hSel : (member i).selectedSheets =
      fun row ↦ single first sheetFirst row ++ single second sheetSecond row) :
    ∑ row : Option target.edges,
        selectedNewSum member i row * cofactor member oldPath reference row =
      (1 : ℚ) / newIndex (member i).candidate sheetFirst *
          cofactor member oldPath reference first +
        (1 : ℚ) / newIndex (member i).candidate sheetSecond *
          cofactor member oldPath reference second := by
  classical
  rw [← sum_ite_mul first ((1 : ℚ) / newIndex (member i).candidate sheetFirst)
      (cofactor member oldPath reference),
    ← sum_ite_mul second ((1 : ℚ) / newIndex (member i).candidate sheetSecond)
      (cofactor member oldPath reference), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun row _ ↦ ?_
  rw [selectedNewSum, hSel]
  simp only [List.map_append, List.sum_append, single_map_sum]
  ring

end MemberColumn

end Census

/-! ## The regrown indices of Figure 28's four members, from their resolutions

Both `W3FourClosure.FourStarGeometry.reversedCandidate` (which carries `M⁽¹⁾`
and `M⁽²⁾`) and `W3FourSourceCandidates.GrowProfile.growCandidate` (which
carries `M⁽³⁾` and `M⁽⁴⁾`) install `ResolutionCoarseFine.fineResolution` of one
surviving direction on every background wall block.  That is the whole content
of Figure 28's `σ⁽ᵠ⁾(J₀, 1) = σ₀(J₀, α)`, and the two lemmas below read it off
as an index identity: `α = 4` for the two reversed members and `α = 2, 3` for
the two grow members. -/

section MemberIndices

theorem reversedCandidate_newIndex_background {base : GluingDatum target degree}
    (geom : FourStarGeometry base wall) (fine : SheetPartition degree)
    (hFine : fine.Refines (base.vertexPartition wall))
    (hGrow : (base.edgePartition geom.growTarget).Refines fine)
    (hOther : (base.edgePartition geom.otherTarget).Refines fine)
    (hCounts : ∀ sheet, (base.vertexPartition wall).Rel geom.growAnchor sheet →
      fine.blockCountWithin fine sheet +
          (base.edgePartition geom.growTarget).blockCountWithin fine sheet +
          (base.edgePartition geom.otherTarget).blockCountWithin fine sheet ≥
        fine.blockCard sheet + 2)
    {sheet : Fin degree}
    (hSheet : ¬(base.vertexPartition wall).Rel geom.growAnchor sheet) :
    newIndex (geom.reversedCandidate fine hFine hGrow hOther hCounts) sheet =
      (base.edgePartition geom.largestTarget).blockCard sheet := by
  rw [newIndex_eq, LocalResolution.paste_newEdge_blockCard]
  have hRepr : ¬(base.vertexPartition wall).Rel geom.growAnchor
      ((base.vertexPartition wall).repr sheet) := fun hRel ↦
    hSheet (hRel.trans ((base.vertexPartition wall).rel_repr_left sheet))
  have hResolution :
      (geom.reversedCandidate fine hFine hGrow hOther hCounts).resolution
          ((base.vertexPartition wall).repr sheet) =
        LocalResolution.onBlock (base.vertexPartition wall) geom.growAnchor
          ((fineResolution (base.vertexPartition wall) fine hFine).reverse)
          geom.wallBackground.resolution
          ((base.vertexPartition wall).repr sheet) := rfl
  rw [hResolution, LocalResolution.onBlock_of_not_rel _ _ _ _ _ hRepr]
  rfl

theorem reversedCandidate_newIndex_selected {base : GluingDatum target degree}
    (geom : FourStarGeometry base wall) (fine : SheetPartition degree)
    (hFine : fine.Refines (base.vertexPartition wall))
    (hGrow : (base.edgePartition geom.growTarget).Refines fine)
    (hOther : (base.edgePartition geom.otherTarget).Refines fine)
    (hCounts : ∀ sheet, (base.vertexPartition wall).Rel geom.growAnchor sheet →
      fine.blockCountWithin fine sheet +
          (base.edgePartition geom.growTarget).blockCountWithin fine sheet +
          (base.edgePartition geom.otherTarget).blockCountWithin fine sheet ≥
        fine.blockCard sheet + 2)
    {sheet : Fin degree}
    (hSheet : (base.vertexPartition wall).Rel geom.growAnchor sheet) :
    newIndex (geom.reversedCandidate fine hFine hGrow hOther hCounts) sheet =
      fine.blockCard sheet := by
  rw [newIndex_eq, LocalResolution.paste_newEdge_blockCard]
  have hRepr : (base.vertexPartition wall).Rel geom.growAnchor
      ((base.vertexPartition wall).repr sheet) :=
    hSheet.trans ((base.vertexPartition wall).rel_repr_left sheet).symm
  have hResolution :
      (geom.reversedCandidate fine hFine hGrow hOther hCounts).resolution
          ((base.vertexPartition wall).repr sheet) =
        LocalResolution.onBlock (base.vertexPartition wall) geom.growAnchor
          ((fineResolution (base.vertexPartition wall) fine hFine).reverse)
          geom.wallBackground.resolution
          ((base.vertexPartition wall).repr sheet) := rfl
  rw [hResolution, LocalResolution.onBlock_of_rel _ _ _ _ _ hRepr]
  rfl

variable {star : ThreeStar target wall} {input : W3SourceInput data star}

theorem growCandidate_newIndex_background
    (grown : W3FourSourceCandidates.GrowProfile input) {sheet : Fin degree}
    (hSheet : ¬(data.vertexPartition wall).Rel grown.growAnchor sheet) :
    newIndex grown.growCandidate sheet =
      (data.edgePartition grown.growTarget).blockCard sheet := by
  rw [newIndex_eq, LocalResolution.paste_newEdge_blockCard]
  have hRepr : ¬(data.vertexPartition wall).Rel grown.growAnchor
      ((data.vertexPartition wall).repr sheet) := fun hRel ↦
    hSheet (hRel.trans ((data.vertexPartition wall).rel_repr_left sheet))
  have hResolution : grown.growCandidate.resolution
        ((data.vertexPartition wall).repr sheet) =
      LocalResolution.onBlock (data.vertexPartition wall) grown.growAnchor
        (fineResolution (data.vertexPartition wall) grown.growPartition
          grown.growPartition_refines)
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (data.edgePartition grown.growTarget) grown.growTarget_refines)
        ((data.vertexPartition wall).repr sheet) := rfl
  rw [hResolution, LocalResolution.onBlock_of_not_rel _ _ _ _ _ hRepr]
  rfl

theorem growCandidate_newIndex_selected
    (grown : W3FourSourceCandidates.GrowProfile input) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel grown.growAnchor sheet) :
    newIndex grown.growCandidate sheet = grown.growPartition.blockCard sheet := by
  rw [newIndex_eq, LocalResolution.paste_newEdge_blockCard]
  have hRepr : (data.vertexPartition wall).Rel grown.growAnchor
      ((data.vertexPartition wall).repr sheet) :=
    hSheet.trans ((data.vertexPartition wall).rel_repr_left sheet).symm
  have hResolution : grown.growCandidate.resolution
        ((data.vertexPartition wall).repr sheet) =
      LocalResolution.onBlock (data.vertexPartition wall) grown.growAnchor
        (fineResolution (data.vertexPartition wall) grown.growPartition
          grown.growPartition_refines)
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (data.edgePartition grown.growTarget) grown.growTarget_refines)
        ((data.vertexPartition wall).repr sheet) := rfl
  rw [hResolution, LocalResolution.onBlock_of_rel _ _ _ _ _ hRepr]
  rfl

end MemberIndices

/-! ## Figure 28's four determinants -/

section Figure28

variable {geometry : FourStarGeometry data wall}

/-- The displayed index `k₂ = |e₂|`. -/
noncomputable abbrev indexGrow (geometry : FourStarGeometry data wall) : ℕ :=
  (data.edgePartition geometry.growTarget).blockCard geometry.growAnchor

/-- The displayed index `k₃ = |e₃|`. -/
noncomputable abbrev indexOther (geometry : FourStarGeometry data wall) : ℕ :=
  (data.edgePartition geometry.otherTarget).blockCard geometry.otherAnchor

/-- The displayed index `k₄ = |e₄|`. -/
noncomputable abbrev indexLargest (geometry : FourStarGeometry data wall) : ℕ :=
  (data.edgePartition geometry.largestTarget).blockCard geometry.largestAnchor

/-- `k₄ = k₂ + k₃`, the defining identity of case `(a = k₄)`. -/
theorem indexLargest_eq (geometry : FourStarGeometry data wall) :
    indexLargest geometry = indexGrow geometry + indexOther geometry := by
  rw [indexLargest, geometry.largest_index, ← geometry.index_sum]

/-- **Figure 28's four members with the receipts their determinants consume.**

The four `background_*` fields say which surviving direction resolves the
background wall blocks on the new edge: `t₄` for `M⁽¹⁾` and `M⁽²⁾`, `t₂` for
`M⁽³⁾` and `t₃` for `M⁽⁴⁾`.  That is Figure 28's line
`σ⁽ᵠ⁾(J₀, 1) = σ₀(J₀, α)`.  The four `selected_*` fields say which regrown
occurrences the member displays over the distinguished block and in which
stable rows, and the `index_*` fields are their displayed indices
`|e'| = k₂, k₃`, `|e'| = k₂ + k₃ - 1`, `|e'| = k₂ + 1`, `|e'| = k₃ + 1`. -/
structure Figure28Receipts (data : GluingDatum target degree) (wall : target.V)
    (geometry : FourStarGeometry data wall) where
  /-- The limit's stable-row census. -/
  rows : LimitRows data wall geometry
  /-- The four members. -/
  member : Fin 4 → MemberColumn data wall geometry
  /-- The sheet carrying `M⁽¹⁾`'s second regrown class `e''` on its own gauge
  copy; the branch swap moves `e₃`, so this need not be `otherAnchor`. -/
  otherSheet : Fin degree
  /-- `M⁽¹⁾` resolves its background with `t₄`. -/
  background_one : (member 0).backgroundTarget = geometry.largestTarget
  /-- `M⁽¹⁾` displays `e'` in the row of `e₂` and `e''` in the row of `e₃`. -/
  selected_one : (member 0).selectedSheets = fun row ↦
    single rows.rowGrow geometry.growAnchor row ++
      single rows.rowOther otherSheet row
  /-- `|e'| = k₂`. -/
  index_one_grow : newIndex (member 0).candidate geometry.growAnchor =
    indexGrow geometry
  /-- `|e''| = k₃`. -/
  index_one_other : newIndex (member 0).candidate otherSheet = indexOther geometry
  /-- `M⁽²⁾` resolves its background with `t₄`. -/
  background_two : (member 1).backgroundTarget = geometry.largestTarget
  /-- `M⁽²⁾` displays one regrown class, in the row of `e₄`. -/
  selected_two : (member 1).selectedSheets = single rows.rowLargest geometry.growAnchor
  /-- `|e'| = k₄ - 1 = k₂ + k₃ - 1`. -/
  index_two : newIndex (member 1).candidate geometry.growAnchor + 1 =
    indexGrow geometry + indexOther geometry
  /-- `M⁽³⁾` resolves its background with `t₂`. -/
  background_three : (member 2).backgroundTarget = geometry.growTarget
  /-- `M⁽³⁾` displays one regrown class, in the row of `e₂`. -/
  selected_three : (member 2).selectedSheets = single rows.rowGrow geometry.growAnchor
  /-- `|e'| = k₂ + 1`. -/
  index_three : newIndex (member 2).candidate geometry.growAnchor =
    indexGrow geometry + 1
  /-- `M⁽⁴⁾` resolves its background with `t₃`. -/
  background_four : (member 3).backgroundTarget = geometry.otherTarget
  /-- `M⁽⁴⁾` displays one regrown class, in the row of `e₃`. -/
  selected_four : (member 3).selectedSheets = single rows.rowOther geometry.otherAnchor
  /-- `|e'| = k₃ + 1`. -/
  index_four : newIndex (member 3).candidate geometry.otherAnchor =
    indexOther geometry + 1

namespace Figure28Receipts

variable (receipts : Figure28Receipts data wall geometry)

/-- The four canonically presented members. -/
noncomputable def presentation (i : Fin 4) :
    ((receipts.member i).candidate).datum.LengthMatrixPresentation
      (Option target.edges) :=
  MemberColumn.presentation receipts.member receipts.rows.oldPath i

/-- The family's common cofactor row. -/
noncomputable def cofactor (row : Option target.edges) : ℚ :=
  MemberColumn.cofactor receipts.member receipts.rows.oldPath 0 row

/-- Figure 28's `c(e₂)`. -/
noncomputable def cTwo : ℚ := receipts.cofactor receipts.rows.rowGrow

/-- Figure 28's `c(e₃)`. -/
noncomputable def cThree : ℚ := receipts.cofactor receipts.rows.rowOther

/-- Figure 28's `c(e₄)`. -/
noncomputable def cFour : ℚ := receipts.cofactor receipts.rows.rowLargest

theorem sum_selected_grow :
    ∑ row : Option target.edges,
        selectedSum geometry (receipts.rows.oldPath row) geometry.growTarget *
          receipts.cofactor row =
      (1 : ℚ) / (indexGrow geometry : ℚ) * receipts.cTwo := by
  classical
  rw [cTwo, ← sum_ite_mul receipts.rows.rowGrow ((1 : ℚ) / (indexGrow geometry : ℚ))
    receipts.cofactor]
  exact Finset.sum_congr rfl fun row _ ↦ by
    rw [receipts.rows.selected_grow row]

theorem sum_selected_other :
    ∑ row : Option target.edges,
        selectedSum geometry (receipts.rows.oldPath row) geometry.otherTarget *
          receipts.cofactor row =
      (1 : ℚ) / (indexOther geometry : ℚ) * receipts.cThree := by
  classical
  rw [cThree, ← sum_ite_mul receipts.rows.rowOther ((1 : ℚ) / (indexOther geometry : ℚ))
    receipts.cofactor]
  exact Finset.sum_congr rfl fun row _ ↦ by
    rw [receipts.rows.selected_other row]

theorem sum_selected_largest :
    ∑ row : Option target.edges,
        selectedSum geometry (receipts.rows.oldPath row) geometry.largestTarget *
          receipts.cofactor row =
      (1 : ℚ) / (indexLargest geometry : ℚ) * receipts.cFour := by
  classical
  rw [cFour, ← sum_ite_mul receipts.rows.rowLargest ((1 : ℚ) / (indexLargest geometry : ℚ))
    receipts.cofactor]
  exact Finset.sum_congr rfl fun row _ ↦ by
    rw [receipts.rows.selected_largest row]

/-- **`M⁽¹⁾`'s determinant** `c(e₂)/k₂ + c(e₃)/k₃ + σ⁽¹⁾(J₀,1)`, with
`σ⁽¹⁾(J₀,1) = σ₀(J₀,4) = -c(e₄)/k₄`. -/
theorem det_one :
    (GluingDatum.LengthMatrixPresentation.matrix (receipts.presentation 0)).det =
      (1 : ℚ) / (indexGrow geometry : ℚ) * receipts.cTwo +
        (1 : ℚ) / (indexOther geometry : ℚ) * receipts.cThree -
        (1 : ℚ) / (indexLargest geometry : ℚ) * receipts.cFour := by
  classical
  have hNew := MemberColumn.sum_selectedNewSum_pair receipts.member
    receipts.rows.oldPath 0 0 receipts.rows.rowGrow receipts.rows.rowOther
    geometry.growAnchor receipts.otherSheet receipts.selected_one
  have hBg : ∑ row : Option target.edges,
      selectedSum geometry (receipts.rows.oldPath row)
          ((receipts.member 0).backgroundTarget) *
        MemberColumn.cofactor receipts.member receipts.rows.oldPath 0 row =
      (1 : ℚ) / (indexLargest geometry : ℚ) * receipts.cFour := by
    rw [receipts.background_one]
    exact receipts.sum_selected_largest
  rw [presentation, MemberColumn.det_eq receipts.member receipts.rows.oldPath 0 0,
    hNew, hBg, receipts.index_one_grow, receipts.index_one_other]
  rfl

/-- **`M⁽²⁾`'s determinant** `c(e₄)/(k₂+k₃-1) + σ₀(J₀,4)`. -/
theorem det_two :
    (GluingDatum.LengthMatrixPresentation.matrix (receipts.presentation 1)).det =
      (1 : ℚ) / ((indexGrow geometry : ℚ) + (indexOther geometry : ℚ) - 1) *
          receipts.cFour -
        (1 : ℚ) / (indexLargest geometry : ℚ) * receipts.cFour := by
  classical
  have hNew := MemberColumn.sum_selectedNewSum_single receipts.member
    receipts.rows.oldPath 0 1 receipts.rows.rowLargest geometry.growAnchor
    receipts.selected_two
  have hBg : ∑ row : Option target.edges,
      selectedSum geometry (receipts.rows.oldPath row)
          ((receipts.member 1).backgroundTarget) *
        MemberColumn.cofactor receipts.member receipts.rows.oldPath 0 row =
      (1 : ℚ) / (indexLargest geometry : ℚ) * receipts.cFour := by
    rw [receipts.background_two]
    exact receipts.sum_selected_largest
  have hCast : ((newIndex (receipts.member 1).candidate geometry.growAnchor : ℕ) : ℚ)
      + 1 = (indexGrow geometry : ℚ) + (indexOther geometry : ℚ) := by
    exact_mod_cast congrArg (fun m : ℕ ↦ (m : ℚ)) receipts.index_two
  have hIdx : ((newIndex (receipts.member 1).candidate geometry.growAnchor : ℕ) : ℚ)
      = (indexGrow geometry : ℚ) + (indexOther geometry : ℚ) - 1 := by linarith
  rw [presentation, MemberColumn.det_eq receipts.member receipts.rows.oldPath 0 1,
    hNew, hBg, hIdx]
  rfl

/-- **`M⁽³⁾`'s determinant** `c(e₂)/(k₂+1) + σ₀(J₀,2)`. -/
theorem det_three :
    (GluingDatum.LengthMatrixPresentation.matrix (receipts.presentation 2)).det =
      (1 : ℚ) / ((indexGrow geometry : ℚ) + 1) * receipts.cTwo -
        (1 : ℚ) / (indexGrow geometry : ℚ) * receipts.cTwo := by
  classical
  have hNew := MemberColumn.sum_selectedNewSum_single receipts.member
    receipts.rows.oldPath 0 2 receipts.rows.rowGrow geometry.growAnchor
    receipts.selected_three
  have hBg : ∑ row : Option target.edges,
      selectedSum geometry (receipts.rows.oldPath row)
          ((receipts.member 2).backgroundTarget) *
        MemberColumn.cofactor receipts.member receipts.rows.oldPath 0 row =
      (1 : ℚ) / (indexGrow geometry : ℚ) * receipts.cTwo := by
    rw [receipts.background_three]
    exact receipts.sum_selected_grow
  have hIdx : ((newIndex (receipts.member 2).candidate geometry.growAnchor : ℕ) : ℚ)
      = (indexGrow geometry : ℚ) + 1 := by
    rw [receipts.index_three]; push_cast; ring
  rw [presentation, MemberColumn.det_eq receipts.member receipts.rows.oldPath 0 2,
    hNew, hBg, hIdx]
  rfl

/-- **`M⁽⁴⁾`'s determinant** `c(e₃)/(k₃+1) + σ₀(J₀,3)`. -/
theorem det_four :
    (GluingDatum.LengthMatrixPresentation.matrix (receipts.presentation 3)).det =
      (1 : ℚ) / ((indexOther geometry : ℚ) + 1) * receipts.cThree -
        (1 : ℚ) / (indexOther geometry : ℚ) * receipts.cThree := by
  classical
  have hNew := MemberColumn.sum_selectedNewSum_single receipts.member
    receipts.rows.oldPath 0 3 receipts.rows.rowOther geometry.otherAnchor
    receipts.selected_four
  have hBg : ∑ row : Option target.edges,
      selectedSum geometry (receipts.rows.oldPath row)
          ((receipts.member 3).backgroundTarget) *
        MemberColumn.cofactor receipts.member receipts.rows.oldPath 0 row =
      (1 : ℚ) / (indexOther geometry : ℚ) * receipts.cThree := by
    rw [receipts.background_four]
    exact receipts.sum_selected_other
  have hIdx : ((newIndex (receipts.member 3).candidate geometry.otherAnchor : ℕ) : ℚ)
      = (indexOther geometry : ℚ) + 1 := by
    rw [receipts.index_four]; push_cast; ring
  rw [presentation, MemberColumn.det_eq receipts.member receipts.rows.oldPath 0 3,
    hNew, hBg, hIdx]
  rfl

/-- **Figure 28's determinant column, as the paper displays it.**  The three
`σ₀` terms are not free parameters here: `σ₀(J₀, j)` *is* `-c(e_j)/k_j`, by the
vanishing of the cofactor-weighted `t_j` column of the limit
(`MemberColumn.sum_columnSum_mul_cofactor`).  So the three relations displayed
beside `M₀` in Figure 28 hold by construction, and this is the `hDet` of
`W3FourClosure.equationTwoGaugeFamily`. -/
theorem det_eq_figure28 (i : Fin 4) :
    (GluingDatum.LengthMatrixPresentation.matrix (receipts.presentation i)).det =
      ![receipts.cTwo / (indexGrow geometry : ℚ) +
          receipts.cThree / (indexOther geometry : ℚ) +
          -(receipts.cFour / ((indexGrow geometry : ℚ) + (indexOther geometry : ℚ))),
        receipts.cFour /
            ((indexGrow geometry : ℚ) + (indexOther geometry : ℚ) - 1) +
          -(receipts.cFour / ((indexGrow geometry : ℚ) + (indexOther geometry : ℚ))),
        receipts.cTwo / ((indexGrow geometry : ℚ) + 1) +
          -(receipts.cTwo / (indexGrow geometry : ℚ)),
        receipts.cThree / ((indexOther geometry : ℚ) + 1) +
          -(receipts.cThree / (indexOther geometry : ℚ))] i := by
  have hLargest : ((indexLargest geometry : ℕ) : ℚ) =
      (indexGrow geometry : ℚ) + (indexOther geometry : ℚ) := by
    rw [indexLargest_eq]; push_cast; ring
  fin_cases i
  · show (GluingDatum.LengthMatrixPresentation.matrix
        (receipts.presentation 0)).det =
      receipts.cTwo / (indexGrow geometry : ℚ) +
        receipts.cThree / (indexOther geometry : ℚ) +
        -(receipts.cFour / ((indexGrow geometry : ℚ) + (indexOther geometry : ℚ)))
    rw [receipts.det_one, hLargest]
    ring
  · show (GluingDatum.LengthMatrixPresentation.matrix
        (receipts.presentation 1)).det =
      receipts.cFour /
          ((indexGrow geometry : ℚ) + (indexOther geometry : ℚ) - 1) +
        -(receipts.cFour / ((indexGrow geometry : ℚ) + (indexOther geometry : ℚ)))
    rw [receipts.det_two, hLargest]
    ring
  · show (GluingDatum.LengthMatrixPresentation.matrix
        (receipts.presentation 2)).det =
      receipts.cTwo / ((indexGrow geometry : ℚ) + 1) +
        -(receipts.cTwo / (indexGrow geometry : ℚ))
    rw [receipts.det_three]
    ring
  · show (GluingDatum.LengthMatrixPresentation.matrix
        (receipts.presentation 3)).det =
      receipts.cThree / ((indexOther geometry : ℚ) + 1) +
        -(receipts.cThree / (indexOther geometry : ℚ))
    rw [receipts.det_four]
    ring

theorem one_le_indexGrow (geometry : FourStarGeometry data wall) :
    (1 : ℚ) ≤ (indexGrow geometry : ℚ) := by
  exact_mod_cast (data.edgePartition geometry.growTarget).blockCard_pos
    geometry.growAnchor

theorem one_le_indexOther (geometry : FourStarGeometry data wall) :
    (1 : ℚ) ≤ (indexOther geometry : ℚ) := by
  exact_mod_cast (data.edgePartition geometry.otherTarget).blockCard_pos
    geometry.otherAnchor

/-- **Figure 28's four members as a gauge-mixed presented family, with `hDet`
and `hAgree` proved rather than assumed.**

`W3FourClosure.equationTwoGaugeFamily` takes the four Figure 28 determinants
and the common off-wall columns as hypotheses; here both come from the
construction.  `hAgree` is `MemberColumn.presentation_agreeOffWall`, an
identity of the canonically presented off-wall columns; `hDet` is
`det_eq_figure28`, the cofactor expansion of each member down its own regrown
column.  The three limit relations `c(e_j)/k_j + σ₀(J₀,j) = 0` are supplied by
taking `σ₀(J₀,j) = -c(e_j)/k_j`, which is what
`MemberColumn.sum_columnSum_mul_cofactor` proves. -/
noncomputable def gaugeFamily :
    W3FourClosure.GaugeFamily (coordinate := Option target.edges) 4 data wall :=
  equationTwoGaugeFamily (fun i ↦ (receipts.member i).base)
    (fun i ↦ (receipts.member i).valid_of_old)
    (fun i ↦ (receipts.member i).candidate) receipts.presentation none
    (k₂ := (indexGrow geometry : ℚ)) (k₃ := (indexOther geometry : ℚ))
    (c₂ := receipts.cTwo) (c₃ := receipts.cThree) (c₄ := receipts.cFour)
    (s₂ := -(receipts.cTwo / (indexGrow geometry : ℚ)))
    (s₃ := -(receipts.cThree / (indexOther geometry : ℚ)))
    (s₄ := -(receipts.cFour /
      ((indexGrow geometry : ℚ) + (indexOther geometry : ℚ))))
    (one_le_indexGrow geometry) (one_le_indexOther geometry)
    (add_neg_cancel _) (add_neg_cancel _) (add_neg_cancel _)
    receipts.det_eq_figure28
    (fun first second ↦ MemberColumn.presentation_agreeOffWall receipts.member
      receipts.rows.oldPath first second)

/-- **The certified positive exit for case `{w3-r1-nd3-t2-(a=k₄)}`, with no
determinant hypothesis.** This is
`W3FourClosure.GaugeFamily.exists_valid_positive_exit_with_pencil` applied to
`gaugeFamily`: Figure 28's four determinants and the common off-wall columns,
which that theorem takes as hypotheses, are the theorems `det_eq_figure28` and
`MemberColumn.presentation_agreeOffWall` here. The hypotheses left are the
incoming datum's validity, the target's connectedness and genus, one nonsingular
member, and the incoming velocity data -- together with the `LimitRows` census
carried by `receipts`. -/
theorem exists_valid_positive_exit_with_pencil (hValid : data.Valid)
    (hTargetConnected : graph_connected target) (hTargetGenus : genus target = 0)
    (root : target.V) (incoming : Fin 4)
    (hincoming : (GluingDatum.LengthMatrixPresentation.matrix
      (receipts.presentation incoming)).det ≠ 0)
    (z incomingVelocity : Option target.edges → ℚ)
    (outgoingVelocity : Fin 4 → Option target.edges → ℚ)
    (hz : z none = 0) (hzpos : ∀ i, i ≠ none → 0 < z i)
    (hSystems : ∀ outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        (receipts.presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        (receipts.presentation incoming)).mulVec incomingVelocity =
      (GluingDatum.LengthMatrixPresentation.matrix
        (receipts.presentation outgoing)).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity none < 0) :
    ∃ outgoing,
      ((receipts.member outgoing).candidate).datum.Valid ∧
      (GluingDatum.LengthMatrixPresentation.matrix
          (receipts.presentation incoming)).det *
        (GluingDatum.LengthMatrixPresentation.matrix
          (receipts.presentation outgoing)).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            (receipts.presentation outgoing)).mulVec
              (z + t • outgoingVelocity outgoing) =
          (GluingDatum.LengthMatrixPresentation.matrix
            (receipts.presentation incoming)).mulVec z +
            t • (GluingDatum.LengthMatrixPresentation.matrix
              (receipts.presentation incoming)).mulVec incomingVelocity ∧
        Nonempty (BalancedGlobal.Candidate.ClearedPencil
          ((receipts.member outgoing).candidate)
          (receipts.presentation outgoing)
          (z + t • outgoingVelocity outgoing)) :=
  W3FourClosure.GaugeFamily.exists_valid_positive_exit_with_pencil
    receipts.gaugeFamily hValid
    hTargetConnected hTargetGenus root incoming hincoming z incomingVelocity
    outgoingVelocity hz hzpos hSystems hIncomingDirection

@[simp] theorem gaugeFamily_presentation (i : Fin 4) :
    receipts.gaugeFamily.presentation i = receipts.presentation i := rfl

@[simp] theorem gaugeFamily_candidate (i : Fin 4) :
    receipts.gaugeFamily.candidate i = (receipts.member i).candidate := rfl

@[simp] theorem gaugeFamily_wallColumn :
    receipts.gaugeFamily.wallColumn = none := rfl

@[simp] theorem gaugeFamily_weight :
    receipts.gaugeFamily.weight =
      ![1, (indexGrow geometry : ℚ) + (indexOther geometry : ℚ) - 1,
        (indexGrow geometry : ℚ) + 1, (indexOther geometry : ℚ) + 1] := rfl

end Figure28Receipts

end Figure28

/-! ## The four actual members as `MemberColumn`s

Nothing above says that `Figure28Receipts` is inhabited.  This section builds
its four members from the objects `W3FourClosure` and `W3FourSourceCandidates`
actually produce, so that the only other input is the limit's stable-row
census `LimitRows`. -/

section Actual

/-- One regrown index of a reversed member, read at the selected anchor, which
is the form `W3FourClosure.exists_member_one` and `exists_member_two` report. -/
theorem reversedCandidate_newIndex_eq_blockCard {base : GluingDatum target degree}
    (geom : FourStarGeometry base wall) (fine : SheetPartition degree)
    (hFine : fine.Refines (base.vertexPartition wall))
    (hGrowR : (base.edgePartition geom.growTarget).Refines fine)
    (hOtherR : (base.edgePartition geom.otherTarget).Refines fine)
    (hCounts : ∀ sheet, (base.vertexPartition wall).Rel geom.growAnchor sheet →
      fine.blockCountWithin fine sheet +
          (base.edgePartition geom.growTarget).blockCountWithin fine sheet +
          (base.edgePartition geom.otherTarget).blockCountWithin fine sheet ≥
        fine.blockCard sheet + 2)
    {sheet : Fin degree}
    (hSheet : (base.vertexPartition wall).Rel geom.growAnchor sheet) :
    newIndex (geom.reversedCandidate fine hFine hGrowR hOtherR hCounts) sheet =
      ((geom.reversedCandidate fine hFine hGrowR hOtherR hCounts).resolution
        geom.growAnchor).newEdge.blockCard sheet := by
  rw [reversedCandidate_newIndex_selected geom fine hFine hGrowR hOtherR hCounts
      hSheet,
    FourStarGeometry.reversedCandidate_newEdge geom fine hFine hGrowR hOtherR
      hCounts (show (base.vertexPartition wall).Rel geom.growAnchor
        geom.growAnchor from rfl)]

/-- `M⁽¹⁾` or `M⁽²⁾` as a `MemberColumn` over the incoming datum: the member
lives on a gauge copy, its background blocks carry the `t₄` partition, and
every comparison with the incoming datum is routed through the branch swap's
own identities. -/
noncomputable def reversedMemberColumn (geometry : FourStarGeometry data wall)
    {base : GluingDatum target degree} (geom : FourStarGeometry base wall)
    (fine : SheetPartition degree)
    (hFine : fine.Refines (base.vertexPartition wall))
    (hGrowR : (base.edgePartition geom.growTarget).Refines fine)
    (hOtherR : (base.edgePartition geom.otherTarget).Refines fine)
    (hCounts : ∀ sheet, (base.vertexPartition wall).Rel geom.growAnchor sheet →
      fine.blockCountWithin fine sheet +
          (base.edgePartition geom.growTarget).blockCountWithin fine sheet +
          (base.edgePartition geom.otherTarget).blockCountWithin fine sheet ≥
        fine.blockCard sheet + 2)
    (transport : WallTransport data base) (valid : data.Valid → base.Valid)
    (hWall : base.vertexPartition wall = data.vertexPartition wall)
    (hAnchor : geom.growAnchor = geometry.growAnchor)
    (hLargest : geom.largestTarget = geometry.largestTarget)
    (hPartition : base.edgePartition geometry.largestTarget =
      data.edgePartition geometry.largestTarget)
    (selectedSheets : Option target.edges → List (Fin degree)) :
    MemberColumn data wall geometry where
  base := base
  transport := transport
  candidate := geom.reversedCandidate fine hFine hGrowR hOtherR hCounts
  backgroundTarget := geometry.largestTarget
  valid_of_old := valid
  background_index := by
    intro sheet hSheet
    rw [reversedCandidate_newIndex_background geom fine hFine hGrowR hOtherR
      hCounts (by rw [hWall, hAnchor]; exact hSheet), hLargest, hPartition]
  selectedSheets := selectedSheets

theorem reversedMemberColumn_candidate (geometry : FourStarGeometry data wall)
    {base : GluingDatum target degree} (geom : FourStarGeometry base wall)
    (fine : SheetPartition degree)
    (hFine : fine.Refines (base.vertexPartition wall))
    (hGrowR : (base.edgePartition geom.growTarget).Refines fine)
    (hOtherR : (base.edgePartition geom.otherTarget).Refines fine)
    (hCounts : ∀ sheet, (base.vertexPartition wall).Rel geom.growAnchor sheet →
      fine.blockCountWithin fine sheet +
          (base.edgePartition geom.growTarget).blockCountWithin fine sheet +
          (base.edgePartition geom.otherTarget).blockCountWithin fine sheet ≥
        fine.blockCard sheet + 2)
    (transport : WallTransport data base) (valid : data.Valid → base.Valid)
    (hWall : base.vertexPartition wall = data.vertexPartition wall)
    (hAnchor : geom.growAnchor = geometry.growAnchor)
    (hLargest : geom.largestTarget = geometry.largestTarget)
    (hPartition : base.edgePartition geometry.largestTarget =
      data.edgePartition geometry.largestTarget)
    (selectedSheets : Option target.edges → List (Fin degree)) :
    (reversedMemberColumn geometry geom fine hFine hGrowR hOtherR hCounts
      transport valid hWall hAnchor hLargest hPartition selectedSheets).candidate =
      geom.reversedCandidate fine hFine hGrowR hOtherR hCounts := rfl

variable {star : ThreeStar target wall} {input : W3SourceInput data star}

/-- `M⁽³⁾` or `M⁽⁴⁾` as a `MemberColumn`: the member lives on the incoming
datum itself, and its background blocks carry its own grow direction's
partition. -/
noncomputable def growMemberColumn (geometry : FourStarGeometry data wall)
    (grown : W3FourSourceCandidates.GrowProfile input)
    (hAnchor : (data.vertexPartition wall).Rel geometry.growAnchor grown.growAnchor)
    (selectedSheets : Option target.edges → List (Fin degree)) :
    MemberColumn data wall geometry where
  base := data
  transport := WallTransport.refl data
  candidate := grown.growCandidate
  backgroundTarget := grown.growTarget
  valid_of_old := _root_.id
  background_index := fun _ hSheet ↦
    growCandidate_newIndex_background grown fun hRel ↦ hSheet (hAnchor.trans hRel)
  selectedSheets := selectedSheets

theorem growMemberColumn_candidate (geometry : FourStarGeometry data wall)
    (grown : W3FourSourceCandidates.GrowProfile input)
    (hAnchor : (data.vertexPartition wall).Rel geometry.growAnchor grown.growAnchor)
    (selectedSheets : Option target.edges → List (Fin degree)) :
    (growMemberColumn geometry grown hAnchor selectedSheets).candidate =
      grown.growCandidate := rfl

/-- Its displayed index `|e'| = k + 1`. -/
theorem growCandidate_newIndex_grow
    (grown : W3FourSourceCandidates.GrowProfile input) :
    newIndex grown.growCandidate grown.growAnchor =
      data.sourceEdgeIndex grown.grow.1 + 1 := by
  rw [growCandidate_newIndex_selected grown rfl]
  exact grown.growPartition_blockCard_growAnchor

/-- **Figure 28's four members supply a `Figure28Receipts`.**

`M⁽³⁾` and `M⁽⁴⁾` are `W3FourSourceCandidates.thirdCandidate` and
`fourthCandidate` on the incoming datum; `M⁽¹⁾` and `M⁽²⁾` are the Position I
and Position II.b members that `W3FourClosure.exists_member_one` and
`exists_member_two` build on branch-swapped copies, with their gauges.  Every
`background_*` and `index_*` receipt is discharged from the members'
resolutions.

The one other input is `rows`: the limit's stable-row census.  It is not
constructed here -- that is the stable-graph half of the case
(`W3FourLimitRows`) -- and this theorem is exactly the statement that nothing
else is needed. -/
theorem exists_figure28Receipts
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
      TargetBranchRegion.edgeMoved wall root hRoot profile.second.1.1.1 = true)
    (rows : LimitRows data wall
      (ofGrowProfile
        (W3FourSourceCandidates.growProfileFirst profile directions largest_index))) :
    ∃ receipts : Figure28Receipts data wall
        (ofGrowProfile
          (W3FourSourceCandidates.growProfileFirst profile directions largest_index)),
      receipts.rows = rows ∧
        HEq (receipts.member 2).candidate
          (W3FourSourceCandidates.thirdCandidate profile directions largest_index) ∧
        HEq (receipts.member 3).candidate
          (W3FourSourceCandidates.fourthCandidate profile directions largest_index) := by
  classical
  let geometry : FourStarGeometry data wall :=
    ofGrowProfile
      (W3FourSourceCandidates.growProfileFirst profile directions largest_index)
  obtain ⟨permOne, hFixOne, positionOne, hGaugeOne, hGeomOne, _, _,
    hIndexOneGrow, hIndexOneOther⟩ :=
    exists_member_one geometry root hRoot hGrowFixed hLargestFixed hOtherMoved
  obtain ⟨permTwo, hFixTwo, positionTwo, hGaugeTwo, hGeomTwo, _, _, hIndexTwo⟩ :=
    exists_member_two geometry root hRoot hGrowFixed hLargestFixed hOtherMoved
  have hWallOne := branchSwapOfPerm_vertexPartition_wall data wall root hRoot
    permOne hFixOne
  have hWallTwo := branchSwapOfPerm_vertexPartition_wall data wall root hRoot
    permTwo hFixTwo
  have hAnchorOne : positionOne.toFourStarGeometry.growAnchor = geometry.growAnchor :=
    congrArg FourStarGeometry.growAnchor hGeomOne
  have hAnchorTwo : positionTwo.toFourStarGeometry.growAnchor = geometry.growAnchor :=
    congrArg FourStarGeometry.growAnchor hGeomTwo
  have hLargestOne :
      positionOne.toFourStarGeometry.largestTarget = geometry.largestTarget :=
    congrArg FourStarGeometry.largestTarget hGeomOne
  have hLargestTwo :
      positionTwo.toFourStarGeometry.largestTarget = geometry.largestTarget :=
    congrArg FourStarGeometry.largestTarget hGeomTwo
  have hPartitionOne := branchSwapOfPerm_edgePartition_of_fixed data wall root hRoot
    permOne hFixOne geometry.largestTarget hLargestFixed
  have hPartitionTwo := branchSwapOfPerm_edgePartition_of_fixed data wall root hRoot
    permTwo hFixTwo geometry.largestTarget hLargestFixed
  have hRelOne : ((branchSwapOfPerm data wall root hRoot permOne
        hFixOne).apply.vertexPartition wall).Rel
      positionOne.toFourStarGeometry.growAnchor geometry.growAnchor :=
    congrArg ((branchSwapOfPerm data wall root hRoot permOne
      hFixOne).apply.vertexPartition wall).repr hAnchorOne
  have hRelTwo : ((branchSwapOfPerm data wall root hRoot permTwo
        hFixTwo).apply.vertexPartition wall).Rel
      positionTwo.toFourStarGeometry.growAnchor geometry.growAnchor :=
    congrArg ((branchSwapOfPerm data wall root hRoot permTwo
      hFixTwo).apply.vertexPartition wall).repr hAnchorTwo
  have hRelOther : ((branchSwapOfPerm data wall root hRoot permOne
        hFixOne).apply.vertexPartition wall).Rel
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
  exact ⟨{
    rows := rows
    member := ![
      reversedMemberColumn geometry positionOne.toFourStarGeometry positionOne.fine
        positionOne.fine_refines positionOne.grow_refines_fine
        positionOne.other_refines_fine positionOne.rightCounts
        (WallTransport.ofSheetRelabeling
          (branchSwapOfPerm data wall root hRoot permOne hFixOne))
        hGaugeOne.valid hWallOne hAnchorOne hLargestOne hPartitionOne
        (fun row ↦ single rows.rowGrow geometry.growAnchor row ++
          single rows.rowOther (permOne geometry.otherAnchor) row),
      reversedMemberColumn geometry positionTwo.toFourStarGeometry positionTwo.fine
        positionTwo.fine_refines positionTwo.grow_refines_fine
        positionTwo.other_refines_fine positionTwo.rightCounts
        (WallTransport.ofSheetRelabeling
          (branchSwapOfPerm data wall root hRoot permTwo hFixTwo))
        hGaugeTwo.valid hWallTwo hAnchorTwo hLargestTwo hPartitionTwo
        (single rows.rowLargest geometry.growAnchor),
      growMemberColumn geometry
        (W3FourSourceCandidates.growProfileFirst profile directions largest_index)
        rfl (single rows.rowGrow geometry.growAnchor),
      growMemberColumn geometry
        (W3FourSourceCandidates.growProfileSecond profile directions largest_index)
        geometry.other_wall_rel (single rows.rowOther geometry.otherAnchor)]
    otherSheet := permOne geometry.otherAnchor
    background_one := rfl
    selected_one := rfl
    index_one_grow := hIdxOneGrow
    index_one_other := hIdxOneOther
    background_two := rfl
    selected_two := rfl
    index_two := hIdxTwo
    background_three := rfl
    selected_three := rfl
    index_three := growCandidate_newIndex_grow
      (W3FourSourceCandidates.growProfileFirst profile directions largest_index)
    background_four := rfl
    selected_four := rfl
    index_four := growCandidate_newIndex_grow
      (W3FourSourceCandidates.growProfileSecond profile directions largest_index) },
    rfl, HEq.rfl, HEq.rfl⟩

end Actual

/-! ## `LimitRows` is inhabited

The census bundles three statements about one `oldPath`.  They hold together,
and the witness is the obvious one: put each of the three surviving
occurrences `e₂`, `e₃`, `e₄` in a row of its own, labelled by its own target
direction, which the case's `grow_ne_other`, `grow_ne_largest`,
`other_ne_largest` keep distinct.

This is a *consistency* witness, not the honest census: nothing in `LimitRows`
forces `oldPath` to enumerate the limit's actual stable paths, and the model
below certainly does not.  Its job is to show that no theorem stated against
`LimitRows` is vacuous. -/

section Model

theorem selectedSum_nil (geometry : FourStarGeometry data wall)
    (t : target.edges) : selectedSum geometry [] t = 0 := by
  simp [selectedSum]

theorem selectedSum_singleton (geometry : FourStarGeometry data wall)
    (e : data.SourceEdge) (t : target.edges) :
    selectedSum geometry [e] t =
      if t = e.1.1 ∧ (data.vertexPartition wall).Rel geometry.growAnchor e.1.2 then
        (1 : ℚ) / data.sourceEdgeIndex e else 0 := by
  classical
  simp [selectedSum]

theorem sourceEdgeIndex_sourceEdge (t : target.edges) (s : Fin degree) :
    data.sourceEdgeIndex (data.sourceEdge t s) = (data.edgePartition t).blockCard s :=
  SheetPartition.blockCard_congr _ ((data.edgePartition t).rel_repr_left s)

theorem wall_rel_sourceEdge_sheet (geometry : FourStarGeometry data wall)
    (t : target.edges) (hRefines : (data.edgePartition t).Refines
      (data.vertexPartition wall)) (s : Fin degree)
    (hs : (data.vertexPartition wall).Rel geometry.growAnchor s) :
    (data.vertexPartition wall).Rel geometry.growAnchor
      (data.sourceEdge t s).1.2 :=
  hs.trans (hRefines.rel ((data.edgePartition t).rel_repr_left s).symm)

/-- The consistency witness: one row per surviving direction. -/
noncomputable def modelOldPath (geometry : FourStarGeometry data wall)
    (row : Option target.edges) : List data.SourceEdge :=
  if row = some geometry.growTarget then
    [data.sourceEdge geometry.growTarget geometry.growAnchor]
  else if row = some geometry.otherTarget then
    [data.sourceEdge geometry.otherTarget geometry.otherAnchor]
  else if row = some geometry.largestTarget then
    [data.sourceEdge geometry.largestTarget geometry.largestAnchor]
  else []

/-- **`LimitRows` is inhabited on every datum of the case.** -/
noncomputable def LimitRows.model (geometry : FourStarGeometry data wall) :
    LimitRows data wall geometry where
  oldPath := modelOldPath geometry
  rowGrow := some geometry.growTarget
  rowOther := some geometry.otherTarget
  rowLargest := some geometry.largestTarget
  selected_grow := by
    classical
    intro row
    unfold modelOldPath
    by_cases hGrow : row = some geometry.growTarget
    · rw [ite_eq_left hGrow, ite_eq_left hGrow, selectedSum_singleton,
        ite_eq_left ⟨rfl, wall_rel_sourceEdge_sheet geometry _ geometry.grow_refines _ rfl⟩,
        sourceEdgeIndex_sourceEdge]
    · rw [ite_eq_right hGrow, ite_eq_right hGrow]
      by_cases hOther : row = some geometry.otherTarget
      · rw [ite_eq_left hOther, selectedSum_singleton,
          ite_eq_right (fun h ↦ geometry.grow_ne_other h.1)]
      · rw [ite_eq_right hOther]
        by_cases hLargest : row = some geometry.largestTarget
        · rw [ite_eq_left hLargest, selectedSum_singleton,
            ite_eq_right (fun h ↦ geometry.grow_ne_largest h.1)]
        · rw [ite_eq_right hLargest, selectedSum_nil]
  selected_other := by
    classical
    intro row
    unfold modelOldPath
    by_cases hGrow : row = some geometry.growTarget
    · rw [ite_eq_left hGrow, selectedSum_singleton,
        ite_eq_right (fun h ↦ geometry.grow_ne_other h.1.symm),
        ite_eq_right (fun h ↦ geometry.grow_ne_other
          (Option.some.inj (hGrow.symm.trans h)))]
    · rw [ite_eq_right hGrow]
      by_cases hOther : row = some geometry.otherTarget
      · rw [ite_eq_left hOther, ite_eq_left hOther, selectedSum_singleton,
          ite_eq_left ⟨rfl, wall_rel_sourceEdge_sheet geometry _ geometry.other_refines _
            geometry.other_wall_rel⟩, sourceEdgeIndex_sourceEdge]
      · rw [ite_eq_right hOther, ite_eq_right hOther]
        by_cases hLargest : row = some geometry.largestTarget
        · rw [ite_eq_left hLargest, selectedSum_singleton,
            ite_eq_right (fun h ↦ geometry.other_ne_largest h.1)]
        · rw [ite_eq_right hLargest, selectedSum_nil]
  selected_largest := by
    classical
    intro row
    unfold modelOldPath
    by_cases hGrow : row = some geometry.growTarget
    · rw [ite_eq_left hGrow, selectedSum_singleton,
        ite_eq_right (fun h ↦ geometry.grow_ne_largest h.1.symm),
        ite_eq_right (fun h ↦ geometry.grow_ne_largest
          (Option.some.inj (hGrow.symm.trans h)))]
    · rw [ite_eq_right hGrow]
      by_cases hOther : row = some geometry.otherTarget
      · rw [ite_eq_left hOther, selectedSum_singleton,
          ite_eq_right (fun h ↦ geometry.other_ne_largest h.1.symm),
          ite_eq_right (fun h ↦ geometry.other_ne_largest
            (Option.some.inj (hOther.symm.trans h)))]
      · rw [ite_eq_right hOther]
        by_cases hLargest : row = some geometry.largestTarget
        · rw [ite_eq_left hLargest, ite_eq_left hLargest, selectedSum_singleton,
            ite_eq_left ⟨rfl, wall_rel_sourceEdge_sheet geometry _ geometry.largest_refines
              _ geometry.largest_wall_rel⟩, sourceEdgeIndex_sourceEdge]
        · rw [ite_eq_right hLargest, selectedSum_nil, ite_eq_right hLargest]

end Model

/-- **Non-vacuity.**  On every datum of the case carrying the three branch
flags, `Figure28Receipts` is inhabited, hence so are `gaugeFamily` and the
four determinant identities.  The census used is `LimitRows.model`, which is a
consistency witness and not the limit's honest stable-row census; what this
theorem rules out is a vacuous `Figure28Receipts`, not a wrong one. -/
theorem nonempty_figure28Receipts
    {star : ThreeStar target wall} {input : W3SourceInput data star}
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
    Nonempty (Figure28Receipts data wall
      (ofGrowProfile
        (W3FourSourceCandidates.growProfileFirst profile directions largest_index))) :=
  let ⟨receipts, _⟩ := exists_figure28Receipts profile directions largest_index root
    hRoot hGrowFixed hLargestFixed hOtherMoved (LimitRows.model _)
  ⟨receipts⟩

end DraismaVargas.LocalCases.W3FourStableGraph
