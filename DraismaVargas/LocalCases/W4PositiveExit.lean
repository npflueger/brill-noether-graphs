module

public import DraismaVargas.LocalCases.W4CommonBalance
public import DraismaVargas.LocalCases.W4IncomingPairingReceipts
public import DraismaVargas.LocalCases.RelabelFullDimensional
public import DraismaVargas.LocalCases.FiniteAtlasMarch

@[expose] public section

/-!
# The W4 positive exit in the incoming cover's original coordinates

This is the W4 counterpart of the M11 exit (`M11CertifiedOpposite`,
`M11IncomingMatching`).  It has two halves.

## Half one: the exit inside the actual W4 family (`section Member`, `section Exit`)

Given an `AuxR0SourceInput` for a four-valent wall and a full-dimensional
presentation of **one identified member** `member input incoming` of the three
outgoing candidates, `exists_member_positive_exit_with_pencil` produces an
opposite-sign outgoing member with its own honest full-dimensional
presentation, a positive small rational step, the exact affine source-metric
equation, and a cleared positive-scale rank-one pencil.

Everything here is assembled from results proved elsewhere and nothing is
re-derived:

* `W4CommonBalance.honestPresentedFamily` is the balanced family consumed;
  its balance is Equation (1) (`W4CommonBalance.determinant_balance`), and its
  `exists_valid_positive_exit_with_pencil` supplies the selection, the step and
  the pencil.  **No member other than the selected one is assumed nonsingular**
  -- `incomingDet_ne_zero` is the identified member's own `det_ne_zero`, and the
  outgoing one comes from the opposite sign.
* `W4OutgoingStableRows.stablePathEquiv` (the occurrence-induced row map with
  its geometric inverse) and `W4OutgoingStableRows.equivalence` (branch/row
  incidence, preserved at every pair) supply `initialLabelling`, `between` and
  the transport of full-dimensionality along
  `StableGraphFullDimensional.presentationOfEquivalence`.
* `W4OutgoingSurvival` and `W4OutgoingLimitMatrix` enter through those and
  through `W4CommonBalance`.  What keeps the transported presentation
  full-dimensional is `W4OutgoingStableRows.member_sourceGenus` together with
  `TargetExpansion.graph_edge_card` (the dimension formula stays saturated,
  `candidate_targetEdgeCard`), while trivalence and path ends come from the
  stable-incidence equivalence itself inside
  `StableGraphFullDimensional.presentationOfEquivalence`.

M11's `consecutive_retained` does not hold for W4, and nothing here ports it --
the row map used throughout is
`stablePathEquiv`, whose well-definedness is row equality, not preservation of
`Consecutive`.

## Half two: the original coordinates (`section Incoming`)

`exists_matchedPresentation` is the step that distinguishes this exit from a
local statement.  It takes the **actual incoming** full-dimensional
presentation `fd`
of `data` and returns a full-dimensional presentation of the outgoing candidate
`member input q` selected by the incoming target placement
`q = W4IncomingTargetNormalization.pairing`, together with

* the **same complete matrix**, not merely the same determinant sign;
* the **same target-occurrence dictionary**, literally
  `fd.labelling.targetEdge.trans (edgeEquiv targetIso)`;
* the **original contracted column**: the coordinate carrying the regrown wall
  occurrence is `fd.labelling.targetEdge.symm contracted`;
* the **retained rows**: a stable-incidence equivalence `certificate` between
  `data` and the candidate with
  `matched.labelling.row = certificate.row.symm.trans fd.labelling.row`.

Its inputs are exactly the incoming stack:
`W4IncomingTargetNormalization` (the placement, the target isomorphism and the
`Option` dictionary), `W4IncomingGlobalMatching.partition_sameBlocks` and
`W4IncomingRepresentatives.stored_representative_normalization` (through
`W4IncomingPairingReceipts.stored_representative_normalization_of_forest`, which
discharges the receipts from the bundle plus `hForest`), plus
`RelabelFullDimensional` for the transport.  No incoming family membership, no
`NoReturn`, no row bijection and no matrix identity is assumed here; all of them
are theorems of those modules.

Two small local bridges name the family member:

* `blockPattern_eq` -- the pattern read off `input.blockPicture` by
  `W4IncomingGlobalMatching.blockPattern` is `input.activeProfile.blockPattern`,
  because both forget the same `ActiveBlockClassification.Kind`
  (`AuxR0SourceInput.blockPicture_kind`).
* `receipts_candidate_datum_eq_member` -- at one fixed pattern every
  `GlobalW4.PairingReceipts` has the same `candidate`, since its three
  remaining fields are propositions; so the candidate that
  `stored_representative_normalization_of_forest` normalizes onto **is**
  `W4OutgoingStableRows.member input q`.

`exists_positive_exit_with_pencil` then states the whole exit in `fd`'s own
coordinates: `OriginalCoordinateExit`, whose column conjunct carries the full
dictionary `columns = M11IncomingCoordinates.incomingColumnEquiv hc hab hOne` --
`none` is the contracted occurrence and `some e` a retained one, and each is
sent to the outgoing member's occurrence of the same name.

## Which object lives on which side of the wall bridge

`FullDimensionalSourcePresentation` and `AuxR0SourceInput` **cannot share a
datum** (`FullDimensionalSource.false_of_changeMinimal_auxR0SourceInput`), and
they do not here:

* `data : GluingDatum target degree` with `fd` is the **full-dimensional**,
  change-minimal incoming cover -- one target occurrence *more*;
* `contractDatum data hc hab hOne`, on `contract target hab hOne`, is the
  **codimension-one wall datum**, and it is the datum the `AuxR0SourceInput`
  `input` and the whole outgoing W4 stack live on.

`W4Bridge.auxR0SourceInput_of_contraction` is the map from the first to the
second, and `wallInput` is that map;
`exists_positive_exit_with_pencil_of_contraction` is the same exit with the
wall interface built by it rather than supplied, so the only inputs are the
contraction bundle (`fd`, `hForest`, `hCompat`, `hStable`, `hTrivalent`) and the
incoming positivity data.  `hForest` is exactly what
`W4Bridge`/`W4IncomingPairingReceipts` name: the source-topology receipt for the
contracted occurrence, used here both to build the wall datum's validity and to
discharge the pairing receipts.

**Joint satisfiability.**  The bundle is not self-contradictory for the two
reasons `W4Bridge` proves -- `targetExcess_contractDatum_merge_eq_one` derives
the wall's Equation (C) *from* change-minimality upstairs, and
`not_nonempty_labelling_contractDatum` shows the wall datum has no square
labelling of its own, so neither `FullDimensionalSource` inconsistency can be
turned against it.  No explicit instance is exhibited in this module:
`TrivalenceClosure.card_target_edges_eq_of_presentation` forces
`t ∈ {3, 9, 15, …}`, so the least admissible shape is `t = 9`, `degree = 3`,
`genus(source) = 4` (see `W4Bridge`).  This module adds no hypothesis of its
own beyond the ones named above.

## Not proved here

The pencil is on the selected outgoing candidate's **literal source
subdivision**, not on any externally requested graph; transporting it to a
requested graph belongs to the terminal stage of the construction and is not
claimed here.  Nothing is asserted about the other two outgoing members'
nonsingularity, and no prescribed-endpoint theorem is used.

Source: Draisma--Vargas Part I, Equation (1) and Figures 26--27, and Case
`{aux-r0}`.  Part I's displays of Equations (1) and (w4-nd2) are written in a
notation that differs from the forms used here (Equation (1) carries a free
index `q` on its right-hand side, and the two sides of (w4-nd2) are not matched
term by term), so nothing is transcribed from them: everything consumed here is
the Lean statement (`W4CommonBalance.sum_det_eq_sum_sigma_star`,
`W4OutgoingLimitMatrix.sum_matrix_new_eq_sum_wall`).
-/

namespace DraismaVargas.LocalCases.W4PositiveExit

open DraismaVargas.Infrastructure TargetExpansion GraphContraction GluingContraction
open ContractionRamification
open W4StableSource W4Assembly W4TargetPairings W4SourceClassification
open W4OutgoingStableRows FullDimensionalSource WallDegeneration
open StableSourceMatrix

section Member

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : FourStar target wall}
  [DecidableEq target.edges]
  (input : AuxR0SourceInput data star)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation (member input incoming).datum coordinate)

/-- Coordinates for the zeroth member, induced from an identified member's
honest labelling by the proved geometric row and occurrence equivalences. -/
noncomputable def initialLabelling :
    StableLengthMatrixLabelling (member input 0).datum coordinate where
  row := ((stablePathEquiv input 0).symm.trans (stablePathEquiv input incoming)).trans
    incomingFD.labelling.row
  targetEdge := incomingFD.labelling.targetEdge.trans
    ((occurrenceEquiv target wall (member input incoming).right).symm.trans
      (occurrenceEquiv target wall (member input 0).right))

/-- The induced honest labelling of every member. -/
noncomputable def outgoingLabelling (outgoing : Fin 3) :
    StableLengthMatrixLabelling (member input outgoing).datum coordinate :=
  W4CommonBalance.labelling input (initialLabelling input incoming incomingFD) outgoing

theorem outgoingLabelling_self :
    outgoingLabelling input incoming incomingFD incoming = incomingFD.labelling := by
  cases incomingFD with
  | mk valid targetConnected targetGenus saturated labelling det_ne_zero trivalent pathEnds =>
    cases labelling with
    | mk targetEdge row =>
      simp only [outgoingLabelling, initialLabelling, W4CommonBalance.labelling,
        W4CommonBalance.sourceCoordinates, W4CommonBalance.targetCoordinates]
      congr 1
      · ext column
        exact (congrArg (occurrenceEquiv target wall (member input incoming).right)
          (Equiv.symm_apply_apply (occurrenceEquiv target wall (member input 0).right) _)).trans
          (Equiv.apply_symm_apply (occurrenceEquiv target wall (member input incoming).right)
            (targetEdge column))
      · ext path
        exact congrArg row
          ((congrArg (stablePathEquiv input incoming)
            (Equiv.symm_apply_apply (stablePathEquiv input 0) _)).trans
            (Equiv.apply_symm_apply (stablePathEquiv input incoming) path))

/-- The honest square matrices of the actual induced member labellings. -/
noncomputable def memberMatrix (outgoing : Fin 3) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix
    (outgoingLabelling input incoming incomingFD outgoing).presentation

theorem memberMatrix_self :
    memberMatrix input incoming incomingFD incoming =
      GluingDatum.LengthMatrixPresentation.matrix incomingFD.labelling.presentation :=
  congrArg
    (fun labelling : StableLengthMatrixLabelling (member input incoming).datum coordinate ↦
      GluingDatum.LengthMatrixPresentation.matrix labelling.presentation)
    (outgoingLabelling_self input incoming incomingFD)

theorem incomingDet_ne_zero :
    (memberMatrix input incoming incomingFD incoming).det ≠ 0 := by
  rw [memberMatrix_self]
  exact incomingFD.det_ne_zero

/-- The regrown wall column, named in the identified member's coordinates. -/
noncomputable def wallColumn : coordinate :=
  W4CommonBalance.wallColumn input (initialLabelling input incoming incomingFD)

/-- The wall column is the identified member's own regrown occurrence. -/
theorem wallColumn_eq :
    wallColumn input incoming incomingFD =
      incomingFD.labelling.targetEdge.symm
        (occurrenceEquiv target wall (member input incoming).right none) := by
  refine (Equiv.symm_apply_eq _).mpr ?_
  refine Eq.symm ?_
  exact (Equiv.symm_apply_apply (occurrenceEquiv target wall (member input 0).right) _).trans
    ((congrArg (occurrenceEquiv target wall (member input incoming).right).symm
      (Equiv.apply_symm_apply incomingFD.labelling.targetEdge _)).trans
      (Equiv.symm_apply_apply (occurrenceEquiv target wall (member input incoming).right) none))

/-- Every column of every induced member labelling is the identified
member's own column, transported by the canonical occurrence dictionaries. -/
theorem outgoingLabelling_targetEdge (outgoing : Fin 3) (column : coordinate) :
    (outgoingLabelling input incoming incomingFD outgoing).targetEdge column =
      occurrenceEquiv target wall (member input outgoing).right
        ((occurrenceEquiv target wall (member input incoming).right).symm
          (incomingFD.labelling.targetEdge column)) :=
  congrArg (occurrenceEquiv target wall (member input outgoing).right)
    (Equiv.symm_apply_apply (occurrenceEquiv target wall (member input 0).right) _)

/-- **The contracted column stays the wall column.**  The coordinate carrying
the identified member's regrown occurrence carries every other member's
regrown occurrence too. -/
theorem outgoingLabelling_wallColumn (outgoing : Fin 3) :
    (outgoingLabelling input incoming incomingFD outgoing).targetEdge
        (wallColumn input incoming incomingFD) =
      occurrenceEquiv target wall (member input outgoing).right none := by
  refine (outgoingLabelling_targetEdge input incoming incomingFD outgoing _).trans ?_
  refine congrArg (occurrenceEquiv target wall (member input outgoing).right) ?_
  refine Eq.trans (congrArg (occurrenceEquiv target wall (member input incoming).right).symm ?_)
    (Equiv.symm_apply_apply (occurrenceEquiv target wall (member input incoming).right) none)
  exact (congrArg incomingFD.labelling.targetEdge (wallColumn_eq input incoming incomingFD)).trans
    (Equiv.apply_symm_apply incomingFD.labelling.targetEdge _)

/-- Canonical outgoing chart velocity, used only at nonsingular members. -/
noncomputable def outgoingVelocity (incomingVelocity : coordinate → ℚ) (outgoing : Fin 3) :
    coordinate → ℚ :=
  FiniteAtlasMarch.chartCoordinates
    (memberMatrix input incoming incomingFD outgoing)
    ((memberMatrix input incoming incomingFD incoming).mulVec incomingVelocity)

theorem outgoingVelocity_system (incomingVelocity : coordinate → ℚ) (outgoing : Fin 3)
    (hDet : (memberMatrix input incoming incomingFD outgoing).det ≠ 0) :
    (memberMatrix input incoming incomingFD incoming).mulVec incomingVelocity =
      (memberMatrix input incoming incomingFD outgoing).mulVec
        (outgoingVelocity input incoming incomingFD incomingVelocity outgoing) :=
  (FiniteAtlasMarch.mulVec_chartCoordinates _ hDet _).symm

end Member

section Candidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : FourStar target wall}
  [DecidableEq target.edges]
  (input : AuxR0SourceInput data star)

theorem candidate_valid (pairing : Fin 3) : (member input pairing).datum.Valid :=
  (member input pairing).datum_valid input.valid

theorem candidate_targetConnected (hConnected : graph_connected target) (pairing : Fin 3) :
    graph_connected (TargetExpansion.graph target wall (member input pairing).right) :=
  TargetExpansion.graph_connected target wall _ hConnected

theorem candidate_targetGenus (hGenus : genus target = 0) (pairing : Fin 3) :
    genus (TargetExpansion.graph target wall (member input pairing).right) = 0 :=
  (TargetExpansion.graph_genus target wall _).trans hGenus

theorem candidate_targetEdgeCard (pairing : Fin 3) :
    (TargetExpansion.graph target wall (member input pairing).right).edges.card =
      target.edges.card + 1 :=
  TargetExpansion.graph_edge_card target wall _

/-- Compare any two actual outgoing candidates through the incoming stable
graph.  Both halves are the proved occurrence-induced equivalences. -/
noncomputable def between (first second : Fin 3) :
    StableGraphIncidence.Equivalence (member input first).datum (member input second).datum :=
  (equivalence input first).symm.trans (equivalence input second)

end Candidates

section Exit

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : FourStar target wall}
  [DecidableEq target.edges]
  (input : AuxR0SourceInput data star)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation (member input incoming).datum coordinate)

/-- Transport the identified member's full-dimensional data to a chosen
outgoing candidate.  Only that candidate's own matrix is required
nonsingular. -/
noncomputable def outgoingPresentation (hConnected : graph_connected target)
    (hGenus : genus target = 0) (outgoing : Fin 3)
    (hDet : (memberMatrix input incoming incomingFD outgoing).det ≠ 0) :
    FullDimensionalSourcePresentation (member input outgoing).datum coordinate :=
  StableGraphFullDimensional.presentationOfEquivalence incomingFD
    (between input incoming outgoing)
    (candidate_valid input outgoing)
    (candidate_targetConnected input hConnected outgoing)
    (candidate_targetGenus input hGenus outgoing)
    ((candidate_targetEdgeCard input outgoing).trans
      (candidate_targetEdgeCard input incoming).symm)
    ((member_sourceGenus input outgoing).trans (member_sourceGenus input incoming).symm)
    (outgoingLabelling input incoming incomingFD outgoing)
    hDet

theorem outgoingPresentation_labelling (hConnected : graph_connected target)
    (hGenus : genus target = 0) (outgoing : Fin 3)
    (hDet : (memberMatrix input incoming incomingFD outgoing).det ≠ 0) :
    (outgoingPresentation input incoming incomingFD hConnected hGenus outgoing hDet).labelling =
      outgoingLabelling input incoming incomingFD outgoing := rfl

/-- **The positive exit inside the actual W4 family.**  Equation (1) selects a
genuinely nonsingular opposite-sign outgoing candidate; the chart solver
supplies its velocity; the metric equation is exact; and the positive
coordinates clear at an explicit scale to a rank-one pencil on that
candidate's literal source subdivision.  The incoming datum is still an
identified member here. -/
theorem exists_member_positive_exit_with_pencil
    (hConnected : graph_connected target) (hGenus : genus target = 0) (root : target.V)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (wallColumn input incoming incomingFD) = 0)
    (hzpos : ∀ i, i ≠ wallColumn input incoming incomingFD → 0 < z i)
    (hDirection : incomingVelocity (wallColumn input incoming incomingFD) < 0) :
    ∃ outgoing : Fin 3,
      ∃ outgoingFD : FullDimensionalSourcePresentation (member input outgoing).datum coordinate,
        outgoingFD.labelling = outgoingLabelling input incoming incomingFD outgoing ∧
        (memberMatrix input incoming incomingFD incoming).det *
            (memberMatrix input incoming incomingFD outgoing).det < 0 ∧
        ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (z + t • outgoingVelocity input incoming incomingFD
            incomingVelocity outgoing) i) ∧
          (memberMatrix input incoming incomingFD outgoing).mulVec
              (z + t • outgoingVelocity input incoming incomingFD
                incomingVelocity outgoing) =
            (memberMatrix input incoming incomingFD incoming).mulVec z +
              t • (memberMatrix input incoming incomingFD incoming).mulVec incomingVelocity ∧
          ∃ realization : (member input outgoing).datum.IntegralRealization,
            ∃ scale : ℕ, 0 < scale ∧
              (∀ column,
                (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                  (scale : ℚ) * (z + t • outgoingVelocity input incoming incomingFD
                    incomingVelocity outgoing) column) ∧
              Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  obtain ⟨outgoing, _hValid, hSign, δ, hδ, hStep⟩ :=
    (W4CommonBalance.honestPresentedFamily input
        (initialLabelling input incoming incomingFD)).exists_valid_positive_exit_with_pencil
      input.valid hConnected hGenus root incoming
      (incomingDet_ne_zero input incoming incomingFD) z incomingVelocity
      (outgoingVelocity input incoming incomingFD incomingVelocity) hz hzpos
      (fun outgoing hDet ↦
        outgoingVelocity_system input incoming incomingFD incomingVelocity outgoing hDet)
      hDirection
  refine ⟨outgoing,
    outgoingPresentation input incoming incomingFD hConnected hGenus outgoing
      (BalancedGlobal.det_ne_zero_of_mul_det_neg hSign),
    rfl, hSign, δ, hδ, ?_⟩
  intro t ht htδ
  obtain ⟨hPositive, hMetric, ⟨pencil⟩⟩ := hStep t ht htδ
  exact ⟨hPositive, hMetric, pencil.realization, pencil.scale, pencil.scale_pos,
    pencil.targetLength_eq, pencil.bnExists⟩

end Exit

section Incoming

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*}
  [Fintype coordinate] [DecidableEq coordinate]
  {a b : target.V} {contracted : target.edges}

/-! ### Casting a presentation along an equality of data -/

private theorem cast_matrix {G : CFGraph} {first second : GluingDatum G degree}
    (h : first = second) (p : FullDimensionalSourcePresentation first coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (h ▸ p : FullDimensionalSourcePresentation second coordinate).labelling.presentation =
      GluingDatum.LengthMatrixPresentation.matrix p.labelling.presentation := by
  cases h
  rfl

private theorem cast_targetEdge {G : CFGraph} {first second : GluingDatum G degree}
    (h : first = second) (p : FullDimensionalSourcePresentation first coordinate) :
    (h ▸ p : FullDimensionalSourcePresentation second coordinate).labelling.targetEdge =
      p.labelling.targetEdge := by
  cases h
  rfl

private theorem cast_row {G H : CFGraph} {source : GluingDatum H degree}
    {first second : GluingDatum G degree} (h : first = second)
    (p : FullDimensionalSourcePresentation first coordinate)
    (e : StableGraphIncidence.Equivalence source first)
    (row : StablePath source ≃ coordinate)
    (hRow : p.labelling.row = e.row.symm.trans row) :
    (h ▸ p : FullDimensionalSourcePresentation second coordinate).labelling.row =
      (h ▸ e : StableGraphIncidence.Equivalence source second).row.symm.trans row := by
  cases h
  exact hRow

/-! ### The incoming cover is the candidate selected by its own placement -/

/-- The candidate assembled from any receipts at the source input's own
canonical block pattern **is** the outgoing family member of that pairing.
Both are `GlobalW4.PairingReceipts.candidate` at the same pattern, and every
remaining field of `GlobalW4.PairingReceipts` is a proposition. -/
theorem receipts_candidate_datum_eq_member {wall : target.V}
    {data : GluingDatum target degree} {star : FourStar target wall}
    [DecidableEq target.edges] (input : AuxR0SourceInput data star)
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : GlobalW4.PairingReceipts data star pattern pairing)
    (hPattern : pattern = input.activeProfile.blockPattern) :
    receipts.candidate.datum = (member input pairing).datum := by
  subst hPattern
  rfl

/-- The block pattern read off the source input's own auxiliary pictures is
its canonical active-branch pattern: both forget the same block kind. -/
theorem blockPattern_eq (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : FourStar (contract target hab hOne) ⟨a, hab⟩)
    (input : AuxR0SourceInput (contractDatum data hc hab hOne) star) :
    W4IncomingGlobalMatching.blockPattern data hc hab hOne star input.blockPicture =
      input.activeProfile.blockPattern := by
  funext sheet
  show (input.blockPicture _).kind.pattern = (input.activeProfile.classification _).kind.pattern
  rw [input.blockPicture_kind]

/-- **The incoming cover, in the outgoing family's coordinates.**  The actual
incoming full-dimensional presentation transports to an honest
full-dimensional presentation of the outgoing candidate selected by the
incoming target placement, with the *same* complete matrix, the *same*
target-occurrence dictionary composed with the canonical target isomorphism,
the original contracted column at the regrown wall occurrence, and the
occurrence-induced stable-incidence equivalence carrying its rows. -/
theorem exists_matchedPresentation
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : FourStar (contract target hab hOne) ⟨a, hab⟩)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    [DecidableEq (contract target hab hOne).edges]
    (input : AuxR0SourceInput (contractDatum data hc hab hOne) star) :
    ∃ matched : FullDimensionalSourcePresentation
        (member input (W4IncomingTargetNormalization.pairing data fd hc hab hOne star)).datum
        coordinate,
      GluingDatum.LengthMatrixPresentation.matrix matched.labelling.presentation =
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation ∧
      matched.labelling.targetEdge =
        fd.labelling.targetEdge.trans (GluingTransport.edgeEquiv
          (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star)) ∧
      matched.labelling.targetEdge.symm
          (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
            (member input
              (W4IncomingTargetNormalization.pairing data fd hc hab hOne star)).right none) =
        fd.labelling.targetEdge.symm contracted ∧
      ∃ certificate : StableGraphIncidence.Equivalence data
          (member input
            (W4IncomingTargetNormalization.pairing data fd hc hab hOne star)).datum,
        matched.labelling.row = certificate.row.symm.trans fd.labelling.row := by
  classical
  obtain ⟨sheets, hSheets⟩ :=
    W4IncomingPairingReceipts.stored_representative_normalization_of_forest
      data fd hc hab hOne star hForest hCompat input.blockPicture
  have hEq : sheets.apply =
      (member input (W4IncomingTargetNormalization.pairing data fd hc hab hOne star)).datum :=
    hSheets.trans (receipts_candidate_datum_eq_member input _
      (blockPattern_eq data hc hab hOne star input))
  let iso := W4IncomingTargetNormalization.targetIso data fd hc hab hOne star
  let targetFD := RelabelFullDimensional.targetPresentation iso fd
  let sheetFD := RelabelFullDimensional.sheetPresentation sheets targetFD
  have hEdge : (hEq ▸ sheetFD :
      FullDimensionalSourcePresentation _ coordinate).labelling.targetEdge =
      fd.labelling.targetEdge.trans (GluingTransport.edgeEquiv iso) :=
    cast_targetEdge hEq sheetFD
  refine ⟨hEq ▸ sheetFD, ?_, hEdge, ?_, ?_⟩
  · exact (cast_matrix hEq sheetFD).trans
      ((RelabelFullDimensional.sheet_matrix_eq sheets targetFD.valid.1 targetFD.labelling).trans
        (RelabelFullDimensional.target_matrix_eq iso data fd.valid.1 fd.labelling))
  · have hCol := W4IncomingTargetNormalization.targetIso_occurrence data fd hc hab hOne star none
    refine (Equiv.symm_apply_eq _).mpr ?_
    refine hCol.symm.trans ?_
    refine Eq.trans ?_ (DFunLike.congr_fun hEdge.symm (fd.labelling.targetEdge.symm contracted))
    exact congrArg (GluingTransport.edgeEquiv iso)
      (fd.labelling.targetEdge.apply_symm_apply contracted).symm
  · exact ⟨hEq ▸ ((TargetRelabelStable.graphEquivalence iso data fd.valid.1).trans
      (StableGraphIncidence.sheetRelabel sheets targetFD.valid.1)),
      cast_row hEq sheetFD _ fd.labelling.row rfl⟩

/-- **The conclusion, in the incoming cover's own coordinates.**  A real
outgoing family member with an honest full-dimensional presentation; the
occurrence-induced stable-incidence equivalence against the **original**
incoming datum; the **complete column dictionary**, saying that the coordinate
carrying the incoming occurrence `columns c` carries exactly the outgoing
member's occurrence `c` -- at `c = none` the contracted occurrence becomes the
regrown wall occurrence, and at `c = some e` each retained occurrence keeps its
name; opposite determinant sign against the **original** incoming matrix; a
positive small rational step whose affine source-metric equation is the
original one; and an integral realization with positive clearing scale and
rank-one pencil on the outgoing member's literal source subdivision.

Every matrix here is `fd`'s own honest square matrix, in `fd`'s own coordinate
type, and every column is named by `fd`'s own target-edge labelling; nothing is
read in the candidate's convenient labelling.  The pencil is on the outgoing
member's own source subdivision, **not** on any externally requested graph. -/
def OriginalCoordinateExit {wallTarget : CFGraph} {wall : wallTarget.V}
    {wallDatum : GluingDatum wallTarget degree} {star : FourStar wallTarget wall}
    [DecidableEq wallTarget.edges] (input : AuxR0SourceInput wallDatum star)
    {data : GluingDatum target degree}
    (fd : FullDimensionalSourcePresentation data coordinate)
    (columns : Option wallTarget.edges ≃ target.edges)
    (z incomingVelocity : coordinate → ℚ) : Prop :=
  ∃ outgoing : Fin 3,
    ∃ outgoingFD : FullDimensionalSourcePresentation (member input outgoing).datum coordinate,
      Nonempty (StableGraphIncidence.Equivalence data (member input outgoing).datum) ∧
      (∀ c : Option wallTarget.edges,
        outgoingFD.labelling.targetEdge (fd.labelling.targetEdge.symm (columns c)) =
          occurrenceEquiv wallTarget wall (member input outgoing).right c) ∧
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).det *
          (GluingDatum.LengthMatrixPresentation.matrix
            outgoingFD.labelling.presentation).det < 0 ∧
      ∃ velocity : coordinate → ℚ, ∃ δ : ℚ, 0 < δ ∧
        ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (z + t • velocity) i) ∧
          (GluingDatum.LengthMatrixPresentation.matrix
              outgoingFD.labelling.presentation).mulVec (z + t • velocity) =
            (GluingDatum.LengthMatrixPresentation.matrix
              fd.labelling.presentation).mulVec z +
              t • (GluingDatum.LengthMatrixPresentation.matrix
                fd.labelling.presentation).mulVec incomingVelocity ∧
          ∃ realization : (member input outgoing).datum.IntegralRealization,
            ∃ scale : ℕ, 0 < scale ∧
              (∀ column,
                (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                  (scale : ℚ) * (z + t • velocity) column) ∧
              Utilities.BNExists realization.sourceSpec.graph 1 degree

/-- **The original-coordinate positive exit.**  Every actual incoming
W4 cover of the wall has a positive, source-certified exit stated entirely in
the incoming cover's own coordinates: the wall coordinate is the contracted
occurrence `contracted` read through the incoming honest labelling, and the
incoming matrix and affine metric equation are the incoming presentation's
own.  No incoming family membership, no row bijection and no matrix identity
is assumed -- all three are theorems of the incoming stack -- and no
outgoing member other than the selected one is assumed nonsingular. -/
theorem exists_positive_exit_with_pencil
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : FourStar (contract target hab hOne) ⟨a, hab⟩)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    [DecidableEq (contract target hab hOne).edges]
    (input : AuxR0SourceInput (contractDatum data hc hab hOne) star)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fd.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fd.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fd.labelling.targetEdge.symm contracted) < 0) :
    OriginalCoordinateExit input fd (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne) z
      incomingVelocity := by
  obtain ⟨matched, hMatrix, hEdge, hWall, certificate, _hRow⟩ :=
    exists_matchedPresentation data fd hc hab hOne star hForest hCompat input
  have hWall' :
      wallColumn input (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) matched =
        fd.labelling.targetEdge.symm contracted :=
    (wallColumn_eq input (W4IncomingTargetNormalization.pairing data fd hc hab hOne star)
      matched).trans hWall
  have hSelf :
      memberMatrix input (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) matched
          (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) =
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation :=
    (memberMatrix_self input (W4IncomingTargetNormalization.pairing data fd hc hab hOne star)
      matched).trans hMatrix
  obtain ⟨outgoing, outgoingFD, hLabelling, hSign, δ, hδ, hStep⟩ :=
    exists_member_positive_exit_with_pencil input
      (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) matched
      (graph_connected_contract target hab hOne fd.targetConnected)
      ((genus_contract target hab hOne).trans fd.targetGenus) ⟨a, hab⟩
      z incomingVelocity (hWall' ▸ hz) (hWall' ▸ hzpos) (hWall' ▸ hDirection)
  have hOutMatrix :
      memberMatrix input (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) matched
          outgoing =
        GluingDatum.LengthMatrixPresentation.matrix outgoingFD.labelling.presentation :=
    congrArg
      (fun labelling : StableLengthMatrixLabelling (member input outgoing).datum coordinate ↦
        GluingDatum.LengthMatrixPresentation.matrix labelling.presentation) hLabelling.symm
  refine ⟨outgoing, outgoingFD,
    ⟨certificate.trans (between input
      (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) outgoing)⟩,
    ?_, ?_,
    outgoingVelocity input (W4IncomingTargetNormalization.pairing data fd hc hab hOne star)
      matched incomingVelocity outgoing,
    δ, hδ, ?_⟩
  · intro c
    refine (congrArg
      (fun labelling : StableLengthMatrixLabelling (member input outgoing).datum coordinate ↦
        labelling.targetEdge (fd.labelling.targetEdge.symm
          (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne c))) hLabelling).trans ?_
    refine (outgoingLabelling_targetEdge input
      (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) matched outgoing _).trans ?_
    refine congrArg (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
      (member input outgoing).right) ?_
    refine Eq.trans (congrArg (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
      (member input (W4IncomingTargetNormalization.pairing data fd hc hab hOne star)).right).symm
      ?_) (Equiv.symm_apply_apply _ c)
    refine (DFunLike.congr_fun hEdge (fd.labelling.targetEdge.symm
      (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne c))).trans ?_
    refine Eq.trans ?_ (W4IncomingTargetNormalization.targetIso_occurrence
      data fd hc hab hOne star c)
    exact congrArg (GluingTransport.edgeEquiv
      (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star))
      (fd.labelling.targetEdge.apply_symm_apply _)
  · simpa only [hSelf, hOutMatrix] using hSign
  · intro t ht htδ
    obtain ⟨hPositive, hMetric, hPencil⟩ := hStep t ht htδ
    exact ⟨hPositive, by simpa only [hSelf, hOutMatrix] using hMetric, hPencil⟩

/-! ### The wall interface, built from the contraction itself -/

/-- The W4 wall interface consumed above, produced by `W4Bridge` from exactly
the contraction receipts: `fd` on the full-dimensional side, `hForest`,
`hStable` and `hTrivalent` on the wall side, and the reflected half of
`hCompat`.  Nothing else is supplied. -/
theorem wallInput (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : FourStar (contract target hab hOne) ⟨a, hab⟩)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hStable : Nonempty (StablePath (contractDatum data hc hab hOne) ≃ StablePath data))
    (hTrivalent : ∀ sourceBlock : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      nonDanglingValency (contractDatum data hc hab hOne)
        (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ sourceBlock) ≤ 3) :
    AuxR0SourceInput (contractDatum data hc hab hOne) star :=
  W4Bridge.auxR0SourceInput_of_contraction data hc hab hOne fd hForest hStable hCompat.2
    hTrivalent

/-- **The original-coordinate exit with both sides of the wall bridge supplied
at once.**  The hypotheses are exactly the contraction bundle of
`W4Bridge.auxR0SourceInput_of_contraction` plus the incoming positivity data;
the wall interface is not a free parameter. -/
theorem exists_positive_exit_with_pencil_of_contraction
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : FourStar (contract target hab hOne) ⟨a, hab⟩)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hStable : Nonempty (StablePath (contractDatum data hc hab hOne) ≃ StablePath data))
    (hTrivalent : ∀ sourceBlock : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      nonDanglingValency (contractDatum data hc hab hOne)
        (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ sourceBlock) ≤ 3)
    [DecidableEq (contract target hab hOne).edges]
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fd.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fd.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fd.labelling.targetEdge.symm contracted) < 0) :
    OriginalCoordinateExit
      (wallInput data fd hc hab hOne star hForest hCompat hStable hTrivalent) fd
      (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne) z incomingVelocity :=
  exists_positive_exit_with_pencil data fd hc hab hOne star hForest hCompat
    (wallInput data fd hc hab hOne star hForest hCompat hStable hTrivalent) z incomingVelocity
    hz hzpos hDirection

end Incoming

end DraismaVargas.LocalCases.W4PositiveExit
