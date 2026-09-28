import DraismaVargasCount.GeneralKExitSetup

/-!
# The general-`K` type-change link at a four-valent wall

Vargas, Part II (arXiv:2609.09109), the valency-4 limits of the section on changing
combinatorial type (Case `{v4-nd4}`).  This module builds, for every admissible `K`, the
type-change link through the member of index `K`; it is an input of the type-change
parity at valency-four limits (step 3 of `Assembly`).

## What is proved

* `linkK`: the `K`-member `OuterWalk.TypeChangeLink m wd`, assembled as
  `NonTrivalentValencyFourExit.typeChangeLink_of_receipts` assembles the `K = 0`
  one.  Its `base` is `position.datum` (the general-`K` gauged wall datum), its
  `baseValid` is `Position.datum_valid`, and its `candidate` is `GeneralKExitSetup.candK`.
  The presentation, its agreement and its tracking are arguments.
* `columnReceipt_linkK`: the `ColumnReceipt` of `linkK`, from two column clauses on the
  presentation.  The base isomorphism is `(LabelGauge.gaugedDataIso _).symm`, whose target
  map is the identity, so `base_col` holds by `rfl` as in `columnReceipt_four`.
* `record_K`: the `K` record at the bridge sheet: the minus endpoint's new-edge count is
  `K + 1`, and the new source-edge index `k₁` satisfies `k₁ + 2K + 1 = k_α + k_β`.  It comes
  from `Position.candidate_K_receipts` and `candidate_newSourceEdge_index`.
* `tracksK_of_equivalence`: **inference [I] below, in usable form.**  Any
  type-change link's tracking transports to the `K`-member along a stable-graph incidence
  equivalence, provided the rows are labelled through it (`InteriorGraphTracking.throughIncidence`).
  The dart map is then the given link's dart map composed with the equivalence.
* `tracksK_of_movedIncidence`: the other reduction.  The tracking follows from a
  branch-vertex bijection and the moved star count
  (`MovedIncidenceIso.tracksOfMovedIncidence`, with `hOp` free from the incoming tracking).
* `exists_typeChangeLinkK_of_inputs`: **the `K`-links exist**, for every admissible `K`,
  from one input per pairing and position: a background, a presentation with agreement, a
  tracking, and the two column clauses.
* `exists_typeChangeLinkK_of_equivalence`: the same conclusion, from
  * the literal background `CanonicalBackground` (`hA2`), and
  * a strengthened presentation hypothesis (`hB6T`): an outgoing presentation agreeing
    with the incoming matrix off the wall column, the two column clauses, and the rows
    labelled through an incidence equivalence with some link `link₀`.
* `exists_odd_far_class_of_links`: the chain to `odd_mSpecializesRight_of_columnReceipt`.
  For each admissible `K`, a column-receipted `K`-link gives one far class, with the same
  parity as the regrowth's, in the regrowth's own metric limit.

## Tempting inferences, checked

* **[I] "the stable graph at `K ≥ 1` is `graph.move m`" is not refuted.**  The stable graph
  is still `H_S`.  The `K` sheets of `A₋ \ A₊` (and the `K'` sheets of `A₊ \ A₋`) are
  singleton classes on the far side.  Each carries only its new occurrence and old
  occurrences outside the gauged branch classes, so it is a dangling leaf and contributes no
  branch vertex.  `A₋` keeps `α, β` and the bridge, and `A₊` keeps `γ, δ` and the bridge.
  This is a paper-level check.  It has **not** been machine-checked at any instance.
* **But `tracks` cannot be obtained from a bare matrix agreement.**  `Tracks fd G label`
  constrains `fd.labelling.row` (its `row_map`), and `ColumnReceipt` constrains
  `fd.labelling.targetEdge`.  A presentation hypothesis of the form
  `∃ fdOut, AgreeOffColumn wd.incomingMatrix (matrix fdOut) wd.column` constrains only the
  matrix off one column.  It fixes neither the row labelling nor the column labelling.
  Recovering them would need a rigidity theorem (the matrix determines the labelling up to
  automorphism), which is not proved here.  The `K = 0` exit never needed one:
  its presentation `wallOutgoingFD` is a concrete definition whose rows
  (`outLabelling_row_retained`, `outLabelling_row_bridge`) and columns (`targetEdge_reindex`)
  are theorems.  **The presentation hypothesis must export its labelling dictionary**, as
  `hB6T` does here.
* The `Tracks` port itself, whether via `tracksK_of_movedIncidence` or via
  `tracksK_of_equivalence`, needs an explicit classification of the branch vertices and
  stable rows of `candK`.  That classification is strictly stronger than the facts that the
  candidate has valency at most three, that its extra sheets dangle, and that the bridge
  survives.  It is the `K ≥ 1` analogue of `NonTrivalentValencyFourTracks`
  (`candBranchEquiv`) and `NonTrivalentValencyFourStarCount`, both written over the
  `K = 0` candidate.

## What is NOT proved

* **Every hypothesis of the two forms of the `K`-link existence.**
  * `exists_typeChangeLinkK_of_inputs` takes `hInputs`: for some pairing and every
    position, a background, a presentation of `candK` with `AgreeOffColumn`, a `Tracks` of
    `graph.move m`, and the two column clauses.
  * `exists_typeChangeLinkK_of_equivalence` takes `hA2` (`CanonicalBackground`, which fails
    in general: `GeneralKBackground.not_exists_literalBackground`) and `hB6T` (the
    presentation hypothesis plus the column clauses plus an incidence equivalence
    `StableGraphIncidence.Equivalence link₀.candidate.datum candK.datum` with the rows
    labelled through it).
* The incidence equivalence (the `K ≥ 1` stable graph is the `K = 0` one) and the move's
  pairing.  The move enters only through the existential pairing of `hB6T`.
* `K`-rigidity: distinct `K` give distinct classes (see `ValencyFourSplit`).
* No new `Prop` is introduced; all hypotheses are inline.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.GeneralKLink

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.Count.GeneralKReceipts
open DraismaVargas.Count.GeneralKExitSetup

section Wall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
    ⟨wd.a, wd.hab⟩)
  (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
  (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      anchorBlock) = 4)
  (pairing : Fin 3)

local notation "vSrc" =>
  (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    wallStar (wd.hForest m) anchorBlock hAnchor)
local notation "vNG" =>
  (NonTrivalentUniqueFourValent.wall_noGlue wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (wd.hForest m))
local notation "vProf" =>
  (NonTrivalentUniqueFourValent.ordinaryBlockProfile_of_single_row wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne wallStar (wd.hForest m) wd.coordinates (label m.base) wd.hRows
    wd.hZeroCoord anchorBlock hAnchor)
local notation "vConn" =>
  (NonTrivalentUniqueFourValent.wall_target_connected wd.cover wd.fullDim wd.hab wd.hOne)
local notation "vGen" =>
  (NonTrivalentUniqueFourValent.wall_target_genus wd.cover wd.fullDim wd.hab wd.hOne)

variable (position : GeneralKReceipts.Position
    (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      wallStar (wd.hForest m) anchorBlock hAnchor) pairing
    (smallerSide (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor) pairing))
  (geometry : GeneralKReceipts.PairingBackground position.datum wallStar pairing
    anchorBlock.1)

local notation "cK" => (candK m wd wallStar anchorBlock hAnchor pairing position geometry)

/-- **The `K`-member type-change link**, assembled as
`NonTrivalentValencyFourExit.typeChangeLink_of_receipts` assembles the `K = 0` one:
`base := position.datum`, `candidate := candK`, and the presentation, its tracking and its
common minor supplied. -/
noncomputable def linkK
    (fdOut : FullDimensionalSourcePresentation (cK).datum coordinate)
    (tracks : Tracks fdOut (graph.move m) label)
    (agree : AgreeOffColumn wd.incomingMatrix
      (GluingDatum.LengthMatrixPresentation.matrix fdOut.labelling.presentation) wd.column) :
    TypeChangeLink m wd where
  base := position.datum
  baseValid := position.datum_valid
    (NonTrivalentUniqueFourValent.wall_valid wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hForest m))
  candidate := cK
  outgoingFD := fdOut
  tracks := tracks
  agree := agree

/-- **The column receipt of the `K`-member link**, on the pattern of
`ColumnReceiptExport.columnReceipt_four`.  `base_col` uses `(LabelGauge.gaugedDataIso _).symm`,
whose target map is the identity; the two column clauses are those that the `K = 0`
presentation satisfies by `LinkReceiptExport.targetEdge_reindex`. -/
theorem columnReceipt_linkK
    (fdOut : FullDimensionalSourcePresentation (cK).datum coordinate)
    (tracks : Tracks fdOut (graph.move m) label)
    (agree : AgreeOffColumn wd.incomingMatrix
      (GluingDatum.LengthMatrixPresentation.matrix fdOut.labelling.presentation) wd.column)
    (hColNew : fdOut.labelling.targetEdge wd.column =
      occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ (cK).right none)
    (hColOld : ∀ j : {column : coordinate //
        column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted},
      fdOut.labelling.targetEdge j.1 =
        occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ (cK).right
          (some (StablePathFacetContraction.punctureTargetEquiv wd.fullDim.labelling wd.hc
            wd.hab wd.hOne j))) :
    ColumnReceiptExport.ColumnReceipt
      (linkK m wd wallStar anchorBlock hAnchor pairing position geometry fdOut tracks agree) :=
  ⟨hColNew, (position.gauge.gaugedDataIso wallStar).symm, fun j ↦ hColOld j⟩

/-- **Inference [I] in usable form.**  Any type-change link's tracking of `graph.move m`
transports to a presentation of the `K`-member along a stable-graph incidence equivalence,
provided the rows are labelled through it.  The resulting dart map is the given link's
dart map composed with the equivalence (`InteriorGraphTracking.throughIncidence`). -/
noncomputable def tracksK_of_equivalence (link₀ : TypeChangeLink m wd)
    (fdOut : FullDimensionalSourcePresentation (cK).datum coordinate)
    (certificate : StableGraphIncidence.Equivalence link₀.candidate.datum (cK).datum)
    (hRows : fdOut.labelling.row = certificate.row.symm.trans link₀.outgoingFD.labelling.row) :
    Tracks fdOut (graph.move m) label :=
  throughIncidence link₀.tracks fdOut certificate hRows

/-- **The tracking from the moved star count** (`MovedIncidenceIso.tracksOfMovedIncidence`):
a branch-vertex bijection with the vertices of `graph` and the star count against the
permuted vertex map.  `hOp` is free from the incoming tracking. -/
noncomputable def tracksK_of_movedIncidence
    (fdOut : FullDimensionalSourcePresentation (cK).datum coordinate)
    (vertexEquiv : StableGraphIncidence.BranchVertex (cK).datum ≃ V)
    (hIncidence : ∀ (v : StableGraphIncidence.BranchVertex (cK).datum)
      (r : StablePath (cK).datum),
      StablePathCount.incidenceCount (cK).datum v.1 r =
        Nat.card {d : D // graph.vert (m.perm d) = vertexEquiv v ∧
          label d = fdOut.labelling.row r}) :
    Tracks fdOut (graph.move m) label :=
  MovedIncidenceIso.tracksOfMovedIncidence (cK).datum fdOut graph m label vertexEquiv
    (MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks) hIncidence

/-- Reading a Boolean-indexed pair back as the indexed value. -/
theorem ite_endpoint {α : Type*} (b : Bool) (f : Bool → α) :
    (if b then f true else f false) = f b := by
  cases b <;> rfl

/-- **The `K` record of the `K`-member**, at the bridge sheet: it lies in the anchor block,
the minus endpoint's new-edge count there is `K + 1` (`Position.candidate_K_receipts`), and
the new source-edge index `k₁` satisfies `k₁ + 2K + 1 = k_α + k_β`
(`Position.candidate_newSourceEdge_index`). -/
theorem record_K :
    ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition ⟨wd.a, wd.hab⟩).Rel
        anchorBlock.1 position.split.bridge ∧
      ((cK).resolution position.split.bridge).newEdge.blockCountWithin
          (if smallerSide vSrc pairing then ((cK).resolution position.split.bridge).right
            else ((cK).resolution position.split.bridge).left) position.split.bridge =
        position.split.K + 1 ∧
      (cK).datum.sourceEdgeIndex ((cK).newSourceEdge position.split.bridge) +
          2 * position.split.K + 1 =
        sideIndex vSrc pairing (smallerSide vSrc pairing) := by
  have hRel : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
      ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 position.split.bridge :=
    (((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition ⟨wd.a, wd.hab⟩).mem_block_iff
      _ _).mp (position.split.bridgeSheets_subset position.split.bridge_mem_bridgeSheets)
  have hRes : (cK).resolution position.split.bridge = position.selected :=
    position.candidate_resolution_of_wall_rel vConn vGen vNG geometry _
      (by rw [position.datum_vertexPartition_wall]; exact hRel)
  refine ⟨hRel, ?_, position.candidate_newSourceEdge_index vConn vGen vNG geometry⟩
  have hK := (position.candidate_K_receipts vConn vGen vNG geometry).1
  rw [position.candidate_resolution_anchor vConn vGen vNG geometry] at hK
  rw [hRes]
  have hIte := ite_endpoint (smallerSide vSrc pairing) position.endpoint
  rw [← position.selected_left, ← position.selected_right] at hIte
  rw [hIte]
  exact hK

/-- **The `K`-links, from their per-position inputs.**  For the pairing named by `hInputs` and every admissible
`K`, a position exists (`exists_position_of_range`).  The inputs at that position give the
link (`linkK`), its column receipt (`columnReceipt_linkK`) and its `K` record (`record_K`). -/
theorem exists_typeChangeLinkK_of_inputs
    (hInputs : ∃ p : Fin 3,
      ∀ pos : GeneralKReceipts.Position vSrc p (smallerSide vSrc p),
        ∃ geo : GeneralKReceipts.PairingBackground pos.datum wallStar p anchorBlock.1,
        ∃ fdOut : FullDimensionalSourcePresentation
            (candK m wd wallStar anchorBlock hAnchor p pos geo).datum coordinate,
          AgreeOffColumn wd.incomingMatrix
            (GluingDatum.LengthMatrixPresentation.matrix fdOut.labelling.presentation)
            wd.column ∧
          Nonempty (Tracks fdOut (graph.move m) label) ∧
          fdOut.labelling.targetEdge wd.column =
            occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
              (candK m wd wallStar anchorBlock hAnchor p pos geo).right none ∧
          ∀ j : {column : coordinate //
              column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted},
            fdOut.labelling.targetEdge j.1 =
              occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
                (candK m wd wallStar anchorBlock hAnchor p pos geo).right
                (some (StablePathFacetContraction.punctureTargetEquiv wd.fullDim.labelling
                  wd.hc wd.hab wd.hOne j))) :
    ∃ pairing : Fin 3, ∀ K : ℕ,
      (∀ l, K + 1 ≤ (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim
          wd.hc wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor).index l) →
      (∀ l, K + (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
          wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor).index l ≤
        ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          ⟨wd.a, wd.hab⟩).blockCard anchorBlock.1) →
      ∃ link : TypeChangeLink m wd, ColumnReceiptExport.ColumnReceipt link ∧
        ∃ sheet : Fin degree,
          ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
            ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 sheet ∧
          (link.candidate.resolution sheet).newEdge.blockCountWithin
              (if smallerSide (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover
                  wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor)
                  pairing
                then (link.candidate.resolution sheet).right
                else (link.candidate.resolution sheet).left) sheet = K + 1 ∧
          link.candidate.datum.sourceEdgeIndex (link.candidate.newSourceEdge sheet) + 2 * K + 1 =
            sideIndex (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim
              wd.hc wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor) pairing
              (smallerSide (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover
                wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor)
                pairing) := by
  obtain ⟨p, hp⟩ := hInputs
  refine ⟨p, fun K hLower hUpper ↦ ?_⟩
  obtain ⟨pos, hK, -⟩ := exists_position_of_range vSrc p vNG
    (NonTrivalentUniqueFourValent.wall_ramification wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      wallStar (wd.hForest m) anchorBlock) hLower hUpper
  obtain ⟨geo, fdOut, hAgree, ⟨tracks⟩, hColNew, hColOld⟩ := hp pos
  subst hK
  obtain ⟨hRel, hCount, hIndex⟩ := record_K m wd wallStar anchorBlock hAnchor p pos geo
  exact ⟨linkK m wd wallStar anchorBlock hAnchor p pos geo fdOut tracks hAgree,
    columnReceipt_linkK m wd wallStar anchorBlock hAnchor p pos geo fdOut tracks hAgree
      hColNew hColOld, pos.split.bridge, hRel, hCount, hIndex⟩

/-! **Caution: the next theorem's `hA2` is `CanonicalBackground`, which fails in
general** (`GeneralKBackground.not_exists_literalBackground`), so the theorem may be
vacuous.  `exists_typeChangeLinkK_of_inputs` above does not use it, and the variant
built on `GeneralKSourceFacts.LocalCanonicalBackground` replaces it. -/

/-- **The `K`-links, from the literal background and a strengthened presentation
hypothesis.**  `hA2` is the literal background `CanonicalBackground`.  `hB6T` is the
existence of an outgoing presentation agreeing with the incoming matrix off the wall
column, strengthened in three ways:
* the two column clauses of the presentation;
* an incidence equivalence of the `K`-member's stable graph with the stable graph of some
  link `link₀` (for instance the `K = 0` one);
* the presentation's rows labelled through that equivalence.

The tracking is `tracksK_of_equivalence`.  The bare agreement off the wall column does not
suffice (see the module docstring). -/
theorem exists_typeChangeLinkK_of_equivalence
    (hA2 : ∀ (p : Fin 3) (pos : GeneralKReceipts.Position vSrc p (smallerSide vSrc p)),
      ∃ geo : GeneralKReceipts.PairingBackground pos.datum wallStar p anchorBlock.1,
        CanonicalBackground m wd wallStar anchorBlock hAnchor p pos geo)
    (hB6T : ∃ p : Fin 3,
      ∀ (pos : GeneralKReceipts.Position vSrc p (smallerSide vSrc p))
        (geo : GeneralKReceipts.PairingBackground pos.datum wallStar p anchorBlock.1),
        CanonicalBackground m wd wallStar anchorBlock hAnchor p pos geo →
        ∃ fdOut : FullDimensionalSourcePresentation
            (candK m wd wallStar anchorBlock hAnchor p pos geo).datum coordinate,
          AgreeOffColumn wd.incomingMatrix
            (GluingDatum.LengthMatrixPresentation.matrix fdOut.labelling.presentation)
            wd.column ∧
          fdOut.labelling.targetEdge wd.column =
            occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
              (candK m wd wallStar anchorBlock hAnchor p pos geo).right none ∧
          (∀ j : {column : coordinate //
              column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted},
            fdOut.labelling.targetEdge j.1 =
              occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
                (candK m wd wallStar anchorBlock hAnchor p pos geo).right
                (some (StablePathFacetContraction.punctureTargetEquiv wd.fullDim.labelling
                  wd.hc wd.hab wd.hOne j))) ∧
          ∃ (link₀ : TypeChangeLink m wd)
            (certificate : StableGraphIncidence.Equivalence link₀.candidate.datum
              (candK m wd wallStar anchorBlock hAnchor p pos geo).datum),
            fdOut.labelling.row =
              certificate.row.symm.trans link₀.outgoingFD.labelling.row) :
    ∃ pairing : Fin 3, ∀ K : ℕ,
      (∀ l, K + 1 ≤ (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim
          wd.hc wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor).index l) →
      (∀ l, K + (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
          wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor).index l ≤
        ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          ⟨wd.a, wd.hab⟩).blockCard anchorBlock.1) →
      ∃ link : TypeChangeLink m wd, ColumnReceiptExport.ColumnReceipt link ∧
        ∃ sheet : Fin degree,
          ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
            ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 sheet ∧
          (link.candidate.resolution sheet).newEdge.blockCountWithin
              (if smallerSide (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover
                  wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor)
                  pairing
                then (link.candidate.resolution sheet).right
                else (link.candidate.resolution sheet).left) sheet = K + 1 ∧
          link.candidate.datum.sourceEdgeIndex (link.candidate.newSourceEdge sheet) + 2 * K + 1 =
            sideIndex (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim
              wd.hc wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor) pairing
              (smallerSide (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover
                wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor)
                pairing) := by
  obtain ⟨p, hp⟩ := hB6T
  refine exists_typeChangeLinkK_of_inputs m wd wallStar anchorBlock hAnchor ⟨p, fun pos ↦ ?_⟩
  obtain ⟨geo, hBg⟩ := hA2 p pos
  obtain ⟨fdOut, hAgree, hColNew, hColOld, link₀, certificate, hRows⟩ := hp pos geo hBg
  exact ⟨geo, fdOut, hAgree,
    ⟨tracksK_of_equivalence m wd wallStar anchorBlock hAnchor p pos geo link₀ fdOut certificate
      hRows⟩, hColNew, hColOld⟩

end Wall

section Facet

open FacetAdapterPilot MemberCertifiedPencil ValencyThreeGeneral FacetMachine
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)

variable {n p degree : ℕ} {c : CubicCore n p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- **An odd far class at the regrowth's own limit.**  Column-receipted links for every admissible `K` give, for each
such `K`, a far class with the regrowth's parity that specialises to the regrowth's own
labelled metric limit (`GeneralKExitSetup.odd_mSpecializesRight_of_columnReceipt`). -/
theorem exists_odd_far_class_of_links (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀))
    {admissible : ℕ → Prop}
    {record : ℕ → TypeChangeLink (pulledMove w ms m') (moveWallData m' hd hG hDegree w ms) → Prop}
    (hLinks : ∀ K, admissible K →
      ∃ link : TypeChangeLink (pulledMove w ms m') (moveWallData m' hd hG hDegree w ms),
        ColumnReceiptExport.ColumnReceipt link ∧ record K link)
    (K : ℕ) (hK : admissible K) :
    ∃ link : TypeChangeLink (pulledMove w ms m') (moveWallData m' hd hG hDegree w ms),
      record K link ∧
      ((FrameClass.mk (farFrame m' hd hG hDegree w ms link)).IsOdd ↔
          (FrameClass.mk w.frame).IsOdd) ∧
        MSpecializesRight (FrameClass.mk (farFrame m' hd hG hDegree w ms link))
          (MetricFacetLimit.ofLeft (c' := (farCore m').core) w) := by
  obtain ⟨link, hrec, hRecord⟩ := hLinks K hK
  exact ⟨link, hRecord,
    odd_mSpecializesRight_of_columnReceipt m' hd hG hDegree w ms link hrec⟩

end Facet

end DraismaVargas.Count.GeneralKLink
