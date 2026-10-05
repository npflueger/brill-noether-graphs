module

public import DraismaVargas.LocalCases.W3FourRegrownColumn

@[expose] public section

/-!
# Equation (2) on the honest matrices

Source: Draisma--Vargas Part I, case `{w3-r1-nd3-t2-(a=k₄)}`, Figure 28 and
Equation (2).

`W3FourClosure.exists_equationTwo_family` proves Equation (2) with Figure 28's
four determinants and the common off-wall columns entering as the named
hypotheses `hDet` and `hAgree`.  `W3FourStableGraph.Figure28Receipts.gaugeFamily`
discharges both from a `Figure28Receipts`, over presented matrices that are
*supplied* rather than shown to be the members' own, and
`W3FourRegrownColumn.exists_figure28Receipts_honest` shows that they are the
members' own.  This module is the composition, together with the one bridge the
composition does not by itself provide.

## The composition question, answered

`Figure28Receipts.gaugeFamily` already carries no `hDet` and no `hAgree`: both
are theorems of *any* `Figure28Receipts`, honest or not
(`det_eq_figure28`, `MemberColumn.presentation_agreeOffWall`).  And
`exists_figure28Receipts_honest` states its honesty conclusion on literally
`receipts.presentation i`, which is `receipts.gaugeFamily.presentation i` by
`rfl`.  So **the honest Equation (2) family is a two-line composition**; there
is no gap between the receipts' `det` field and `exists_equationTwo_family`'s
`hDet` form, and none between the gauge copies and the original datum, because
`GaugeFamily` stores one `base` per member and `gaugeFamily` takes those bases
to be `(receipts.member i).base` -- the receipts' own copies.

What honesty adds is therefore not a hypothesis removed but a *meaning*
supplied: the matrices whose determinants Equation (2) balances are the
members' own `StableSourceMatrix.matrix`.

## What is proved here

* `HonestFigure28` -- a `Figure28Receipts` together with the honesty of all four
  presented matrices, which is exactly what `exists_figure28Receipts_honest`
  returns.
* `HonestFigure28.gaugeFamily` -- **Equation (2)'s `GaugeFamily 4 data wall` on
  the honest matrices**, weights `![1, k₂+k₃-1, k₂+1, k₃+1]`, bases the
  receipts' gauge copies, with no determinant and no agreement hypothesis.
* `HonestFigure28.labelling` -- **the bridge**.  `IsHonest` is an existential
  over a row relabelling; `W4StableSource.StableLengthMatrixLabelling` is the
  bundled form the full-dimensional interface consumes.  `labelling i` is that
  bundle, and `labelling_matrix` says its length matrix is *the family's own*
  presented matrix, so the family's determinant gate and the member's honest
  determinant gate are the same condition.  This is what
  `W3FourStableIncidence` needs and what `IsHonest` alone does not give.
* `exists_honestFigure28` and `exists_equationTwo_honest_family` -- the honest
  family on exactly the hypotheses `exists_figure28Receipts_honest` takes:
  `data.Valid`, an `Nd3Profile`, distinct directions, the case's index identity
  and the three branch flags.
* `HonestFigure28.exists_valid_positive_exit_with_pencil` -- the certified
  positive exit with a cleared pencil, over honest matrices.

## What this does *not* claim

Nothing here asserts that any member is nonsingular; the exit keeps its own
`det ≠ 0` gate on the selected member.  Nothing here identifies the **incoming**
member or transports the exit to the original coordinates.  And nothing here is
a `BalancedGlobal.PresentedFamily`: Figure 28's members do not live over one
`GluingDatum` value (Part I works with isomorphism classes, and the members are
realized on different branch-swapped representatives; see `W3FourClosure`),
which is why `GaugeFamily` is the right structure and why `base` is a field.
-/

namespace DraismaVargas.LocalCases.W3FourHonestBalance

open DraismaVargas.Infrastructure
open TargetExpansion
open BalancedGlobal
open W4StableSource StableSourceMatrix
open ThirdEquation
open W3FourClosure (FourStarGeometry ofGrowProfile)
open W3FourStableGraph
open W3FourRegrownColumn (IsHonest)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## The honest labelling of an honest presentation

`IsHonest` says a presented matrix *is* the candidate's own stable-length
matrix, at some relabelling of the rows and the canonical relabelling of the
columns.  `W4StableSource.StableLengthMatrixLabelling` is the same data bundled,
and it is the form `FullDimensionalSource.FullDimensionalSourcePresentation`
asks for.  The two are interchangeable, and the matrices agree on the nose. -/

section HonestLabelling

variable {base : GluingDatum target degree}
  {candidate : Candidate target degree base wall}
  {presentation : candidate.datum.LengthMatrixPresentation (Option target.edges)}

/-- An honest presentation, read as an honest stable length-matrix labelling of
the member's own datum. -/
noncomputable def honestLabelling (honest : IsHonest candidate presentation) :
    StableLengthMatrixLabelling candidate.datum (Option target.edges) where
  targetEdge := occurrenceEquiv target wall candidate.right
  row := honest.choose.symm

@[simp] theorem honestLabelling_targetEdge (honest : IsHonest candidate presentation) :
    (honestLabelling (wall := wall) honest).targetEdge =
      occurrenceEquiv target wall candidate.right := rfl

/-- **Its length matrix is the presented one.**  So a nonsingularity gate stated
on the family's presented matrix is a gate on the member's honest matrix, and
conversely. -/
theorem honestLabelling_matrix (honest : IsHonest candidate presentation) :
    GluingDatum.LengthMatrixPresentation.matrix
        (honestLabelling (wall := wall) honest).presentation =
      GluingDatum.LengthMatrixPresentation.matrix presentation := by
  ext row column
  rw [labelling_matrix_eq, honest.choose_spec]
  rfl

theorem honestLabelling_det_ne_zero (honest : IsHonest candidate presentation)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix presentation).det ≠ 0) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (honestLabelling (wall := wall) honest).presentation).det ≠ 0 := by
  rw [honestLabelling_matrix honest]
  exact hDet

end HonestLabelling

/-! ## Figure 28's receipts, with every presented matrix honest -/

variable {geometry : FourStarGeometry data wall}

/-- **Figure 28's four members over the limit's own stable rows, with each
presented matrix proved to be that member's own stable-length matrix.**  This is
precisely the output of `W3FourRegrownColumn.exists_figure28Receipts_honest`. -/
structure HonestFigure28 (data : GluingDatum target degree) (wall : target.V)
    (geometry : FourStarGeometry data wall) where
  /-- The receipts: the limit's census and the four members' columns. -/
  receipts : Figure28Receipts data wall geometry
  /-- Every presented matrix is the member's own. -/
  honest : ∀ i, IsHonest (receipts.member i).candidate (receipts.presentation i)

namespace HonestFigure28

variable (honestReceipts : HonestFigure28 data wall geometry)

/-- The gauge copy member `i` lives on. -/
noncomputable def base (i : Fin 4) : GluingDatum target degree :=
  (honestReceipts.receipts.member i).base

/-- Member `i` itself. -/
noncomputable def candidate (i : Fin 4) :
    Candidate target degree (honestReceipts.base i) wall :=
  (honestReceipts.receipts.member i).candidate

/-- **Equation (2)'s family on the honest matrices.**  `hDet` and `hAgree` are
not hypotheses of anything below: both are discharged at
`W3FourStableGraph.Figure28Receipts.gaugeFamily`, and the matrices they are
about are the members' own. -/
noncomputable def gaugeFamily :
    W3FourClosure.GaugeFamily (coordinate := Option target.edges) 4 data wall :=
  honestReceipts.receipts.gaugeFamily

@[simp] theorem gaugeFamily_base (i : Fin 4) :
    honestReceipts.gaugeFamily.base i = honestReceipts.base i := rfl

@[simp] theorem gaugeFamily_candidate (i : Fin 4) :
    honestReceipts.gaugeFamily.candidate i = honestReceipts.candidate i := rfl

@[simp] theorem gaugeFamily_presentation (i : Fin 4) :
    honestReceipts.gaugeFamily.presentation i =
      honestReceipts.receipts.presentation i := rfl

@[simp] theorem gaugeFamily_wallColumn :
    honestReceipts.gaugeFamily.wallColumn = none := rfl

/-- **The displayed weights of Equation (2)**: `1`, `k₂+k₃-1`, `k₂+1`, `k₃+1`. -/
@[simp] theorem gaugeFamily_weight :
    honestReceipts.gaugeFamily.weight =
      ![1, (indexGrow geometry : ℚ) + (indexOther geometry : ℚ) - 1,
        (indexGrow geometry : ℚ) + 1, (indexOther geometry : ℚ) + 1] := rfl

/-- Every member of the family is honestly presented. -/
theorem gaugeFamily_honest (i : Fin 4) :
    IsHonest (honestReceipts.gaugeFamily.candidate i)
      (honestReceipts.gaugeFamily.presentation i) :=
  honestReceipts.honest i

/-- **The member's own honest stable length-matrix labelling.** -/
noncomputable def labelling (i : Fin 4) :
    StableLengthMatrixLabelling (honestReceipts.candidate i).datum
      (Option target.edges) :=
  honestLabelling (wall := wall) (honestReceipts.honest i)

@[simp] theorem labelling_targetEdge (i : Fin 4) :
    (honestReceipts.labelling i).targetEdge =
      occurrenceEquiv target wall (honestReceipts.candidate i).right := rfl

/-- **and its matrix is the family's own presented matrix.** -/
theorem labelling_matrix (i : Fin 4) :
    GluingDatum.LengthMatrixPresentation.matrix (honestReceipts.labelling i).presentation =
      GluingDatum.LengthMatrixPresentation.matrix
        (honestReceipts.gaugeFamily.presentation i) :=
  honestLabelling_matrix (honestReceipts.honest i)

theorem labelling_det_ne_zero (i : Fin 4)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix
      (honestReceipts.gaugeFamily.presentation i)).det ≠ 0) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (honestReceipts.labelling i).presentation).det ≠ 0 := by
  rw [honestReceipts.labelling_matrix i]
  exact hDet

/-- Member `i`'s datum is valid whenever the incoming one is, through its own
gauge. -/
theorem candidate_valid (i : Fin 4) (hValid : data.Valid) :
    (honestReceipts.candidate i).datum.Valid :=
  (honestReceipts.candidate i).datum_valid
    ((honestReceipts.receipts.member i).valid_of_old hValid)

/-- **The certified positive exit with a cleared pencil, over honest
matrices.**  Verbatim `Figure28Receipts.exists_valid_positive_exit_with_pencil`
at these receipts: no determinant hypothesis beyond the selected member's own,
and no off-wall-agreement hypothesis at all. -/
theorem exists_valid_positive_exit_with_pencil (hValid : data.Valid)
    (hTargetConnected : graph_connected target) (hTargetGenus : genus target = 0)
    (root : target.V) (incoming : Fin 4)
    (hincoming : (GluingDatum.LengthMatrixPresentation.matrix
      (honestReceipts.gaugeFamily.presentation incoming)).det ≠ 0)
    (z incomingVelocity : Option target.edges → ℚ)
    (outgoingVelocity : Fin 4 → Option target.edges → ℚ)
    (hz : z none = 0) (hzpos : ∀ i, i ≠ none → 0 < z i)
    (hSystems : ∀ outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        (honestReceipts.gaugeFamily.presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        (honestReceipts.gaugeFamily.presentation incoming)).mulVec incomingVelocity =
      (GluingDatum.LengthMatrixPresentation.matrix
        (honestReceipts.gaugeFamily.presentation outgoing)).mulVec
          (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity none < 0) :
    ∃ outgoing,
      (honestReceipts.candidate outgoing).datum.Valid ∧
      (GluingDatum.LengthMatrixPresentation.matrix
          (honestReceipts.gaugeFamily.presentation incoming)).det *
        (GluingDatum.LengthMatrixPresentation.matrix
          (honestReceipts.gaugeFamily.presentation outgoing)).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            (honestReceipts.gaugeFamily.presentation outgoing)).mulVec
              (z + t • outgoingVelocity outgoing) =
          (GluingDatum.LengthMatrixPresentation.matrix
            (honestReceipts.gaugeFamily.presentation incoming)).mulVec z +
            t • (GluingDatum.LengthMatrixPresentation.matrix
              (honestReceipts.gaugeFamily.presentation incoming)).mulVec incomingVelocity ∧
        Nonempty (BalancedGlobal.Candidate.ClearedPencil
          (honestReceipts.candidate outgoing)
          (honestReceipts.gaugeFamily.presentation outgoing)
          (z + t • outgoingVelocity outgoing)) :=
  honestReceipts.receipts.exists_valid_positive_exit_with_pencil hValid
    hTargetConnected hTargetGenus root incoming hincoming z incomingVelocity
    outgoingVelocity hz hzpos hSystems hIncomingDirection

/-- **The selected member's honest matrix is nonsingular exactly when the
family's is**, so the exit's own gate delivers an honest nonsingularity receipt
for the outgoing member. -/
theorem labelling_det_ne_zero_of_opposite (incoming outgoing : Fin 4)
    (hOpposite : (GluingDatum.LengthMatrixPresentation.matrix
        (honestReceipts.gaugeFamily.presentation incoming)).det *
      (GluingDatum.LengthMatrixPresentation.matrix
        (honestReceipts.gaugeFamily.presentation outgoing)).det < 0) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (honestReceipts.labelling outgoing).presentation).det ≠ 0 := by
  refine honestReceipts.labelling_det_ne_zero outgoing ?_
  intro hZero
  rw [hZero, mul_zero] at hOpposite
  exact lt_irrefl 0 hOpposite

end HonestFigure28

/-! ## Existence, on exactly the case's own hypotheses -/

section Existence

variable {star : ThreeStar target wall} {input : W3SourceInput data star}

open W3FourSourceCandidates (growProfileFirst thirdCandidate fourthCandidate)

/-- **Figure 28's honest receipts exist**, on exactly the hypotheses
`W3FourRegrownColumn.exists_figure28Receipts_honest` takes. -/
theorem exists_honestFigure28 (hValid : data.Valid)
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
    ∃ honestReceipts : HonestFigure28 data wall
        (ofGrowProfile (growProfileFirst profile directions largest_index)),
      honestReceipts.receipts.rows =
          W3FourLimitRows.limitRowsOfInput
            (growProfileFirst profile directions largest_index) ∧
        HEq (honestReceipts.candidate 2)
          (thirdCandidate profile directions largest_index) ∧
        HEq (honestReceipts.candidate 3)
          (fourthCandidate profile directions largest_index) := by
  obtain ⟨receipts, hRows, hThird, hFourth, hHonest⟩ :=
    W3FourRegrownColumn.exists_figure28Receipts_honest hValid profile directions
      largest_index root hRoot hGrowFixed hLargestFixed hOtherMoved
  exact ⟨⟨receipts, hHonest⟩, hRows, hThird, hFourth⟩

/-- **Equation (2) on the honest matrices.**  A genuine
`BalancedGlobal.GaugeFamily 4 data wall` with Figure 28's weights, whose four
presented matrices are the four members' own stable-length matrices, on exactly
the hypotheses above -- no `hDet`, no `hAgree`, and no nonsingularity of any
member. -/
theorem exists_equationTwo_honest_family (hValid : data.Valid)
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
    ∃ family : W3FourClosure.GaugeFamily (coordinate := Option target.edges) 4 data wall,
      family.wallColumn = none ∧
        family.weight =
          ![1,
            (indexGrow (ofGrowProfile
              (growProfileFirst profile directions largest_index)) : ℚ) +
              (indexOther (ofGrowProfile
                (growProfileFirst profile directions largest_index)) : ℚ) - 1,
            (indexGrow (ofGrowProfile
              (growProfileFirst profile directions largest_index)) : ℚ) + 1,
            (indexOther (ofGrowProfile
              (growProfileFirst profile directions largest_index)) : ℚ) + 1] ∧
        (∀ i, IsHonest (family.candidate i) (family.presentation i)) ∧
        HEq (family.candidate 2) (thirdCandidate profile directions largest_index) ∧
        HEq (family.candidate 3) (fourthCandidate profile directions largest_index) := by
  obtain ⟨honestReceipts, _, hThird, hFourth⟩ :=
    exists_honestFigure28 hValid profile directions largest_index root hRoot
      hGrowFixed hLargestFixed hOtherMoved
  exact ⟨honestReceipts.gaugeFamily, rfl, rfl, honestReceipts.gaugeFamily_honest,
    hThird, hFourth⟩

end Existence

end DraismaVargas.LocalCases.W3FourHonestBalance
