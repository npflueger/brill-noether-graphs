import DraismaVargas.LocalCases.NonTrivalentValencyThreePathEnds
import DraismaVargas.LocalCases.MovedIncidenceIso
import DraismaVargas.LocalCases.WallSplitIncidence

/-!
# The vertex dictionary of the valency-three Type III type change, and (H-III)

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 (a combinatorial type
change is recorded as a Whitehead move on the *ambient* tracked graph; the
labelling convention (1)) and Section 5.3 (Case {v3-nd4}, Type III, base tree
`T_2`: the anchor `A` resolves into `A_u` and `A_v` joined by the new
occurrence `h_1`, with the two doubled-direction survivors at `A_u` and the two
simple ones at `A_v`), together with Draisma--Vargas Part I (arXiv:1909.12924):
the stable graph `H(M)` of a gluing datum and its row labels, and
`lemma-ndval-of-GqA0`.

This module supplies the `tracks` field of the valency-three Type III link.
`NonTrivalentValencyThreeExit` provides the outgoing presentation and
`typeChangeLink_of_receipts`; `NonTrivalentValencyThreePathEnds` removes its
`hPathEnds` hypothesis (`typeChangeLink_of_receipts'`); and `WallSplitIncidence`
and `MovedIncidenceIso` provide the two valency-agnostic halves of `tracks`.
What `MovedIncidenceIso.tracksOfMovedIncidence` then needs is a branch-vertex
bijection `vertexEquiv : BranchVertex cand.datum ≃ V` and the star count
`hIncidence` against the *permuted* vertex map of `graph.move m`.  This module
delivers the bijection, the hypothesis (H-III) that pins the anchor half of the
star count, and the wall-side geometry both rest on.

## What is proved

### 1.  The vanishing occurrence

* `facetRow`, `facetEdge`: the vanishing row of the incoming cover is the chart
  row of the move's contracted dart, and it has a surviving occurrence.
* `nonDanglingValency_ne_two_of_incident_facetRow`,
  `three_le_nonDanglingValency_end`: **its ends are branch vertices.**  A
  divalent end would carry a second surviving occurrence on the same row, hence
  a second surviving occurrence over the contracted target occurrence, which
  `NoContractedReturn` forbids; at a three-valent wall `NoContractedReturn`
  holds unconditionally (`noContractedReturn_of_threeStar`).
* `eq_facetEdge`: consequently the vanishing row is that single occurrence
  `h_1`; `leftEnd`, `rightEnd` are its two ends (`A_u`, `A_v` upstairs).

### 2.  The anchor

* `four_le_nonDanglingValency_map_leftEnd` and
  `sourceVertexMap_leftEnd_eq_anchorVertex`: **the vanishing occurrence lies
  over the anchor.**  `lemma-ndval-of-GqA0`
  (`WallSplitIncidence.nonDanglingValency_eq_sum_activeFibre`) gives
  `nd(W) >= 4` at the image of `leftEnd`, while every other wall block is
  trivalent (`NonTrivalentAnchorValency`, through
  `NonTrivalentValencyThreeExit.ordinaryBlock_trivalent`).
* `eq_leftEnd_or_eq_rightEnd_of_mem_activeFibre`: **the anchor fibre carries
  exactly `leftEnd` and `rightEnd` as branch vertices**, because
  `nd(A) = 4 = 2 + sum (nd(V) - 2)` and each summand is `0` or `1`.
* `wallDatum_trivalent_away_anchor`: the wall datum is trivalent away from the
  anchor, off the merged vertex by
  `NonTrivalentValencyTwoExit.wallDatum_trivalent_away` and at an ordinary
  block by `NonTrivalentValencyThreeExit.ordinaryBlock_trivalent`.
* `branchEquivAnchorComplement`: the branch-vertex dictionary of
  `WallSplitIncidence`,
  `{v : BranchVertex M // v <> leftEnd, rightEnd} ~ {w : BranchVertex M_0 // w <> A}`,
  **without its `hFibre` hypothesis**: the proof only needs the branch
  pair above, not the full fibre `activeFibreVertices A = {leftEnd, rightEnd}`,
  which is *not* available at a three-valent wall (see "What is NOT proved").

### 3.  (H-III)

* `PrescribedDoubledMove m wd wallStar src`: the two darts the Whitehead move
  places together with `m.base` -- the moved star of `graph.vert m.base` with
  `m.base` removed -- are, under `wd.tracks.iso.dart`, darts carrying the two
  stable **rows** of the doubled-direction survivors of the anchor, in the
  orientation that puts `A_u` at `graph.vert m.base` (first conjunct: `m.base`
  is the dart of `h_1` at the `A_u` end).  The clause is at the level of rows
  (`d.2.1.stablePath = ...`): a survivor may reach its end of `h_1` through a
  pass-through occurrence over the contracted target edge, and it is the row,
  not the occurrence, that the star count consumes
  (`IncomingPairing.label_dart_of_row`).  The other orientation is
  normalised by the caller with `CubicDartGraph.MoveData.swap`, which leaves
  `graph.move m` unchanged.
* `prescribedDoubledMove_of_occurrence`: the occurrence-level clause
  (`first.2.1 = doubledLift ...`) implies (H-III).
* `prescribedDoubledMove_of_rows`: (H-III) from the orientation clause together
  with two moved darts carrying the two doubled rows -- the shape
  `IncomingPairing.exists_movedStar_darts` produces, and the one the valency
  dispatcher consumes.  At row level separation is automatic
  (`IncomingPairing.vertex_of_movedStar_eq_pair`), so `DoubledSeparated` is not
  a hypothesis of it.
* `DoubledSeparated`: the geometric content of a *type change* -- the two
  doubled-direction survivors lift to occurrences at the two **different** ends
  of `h_1`.  Without it `A_u` sees exactly the star of `leftEnd` and no
  Whitehead move takes place.
* `prescribedMove` and `prescribedDoubledMove_prescribedMove`: **non-vacuity of
  (H-III), in relative form.**  Given the orientation and `DoubledSeparated`,
  the move that contracts the *same* edge as `m` and exchanges the doubled
  survivor at the `A_v` end with the remaining dart at the `A_u` end satisfies
  (H-III).  (An absolute `exists m, PrescribedDoubledMove m wd ...` does not
  typecheck: `wd : WallData arrival` with
  `arrival : FacetArrival degree graph label (label m.base)` fixes `m.base`, so
  the witness has to be produced with that same `base` field, which is what
  `prescribedMove` does.)

### 4.  The branch vertices of the candidate, and `vertexEquiv`

* `candVertex`: the outgoing vertex over a wall-datum vertex other than the
  anchor -- `endpointVertex true` over the merged target vertex,
  `ResolutionAwayFromWall.retainedVertex` away from it -- and
  `nonDanglingValency_candVertex`: its surviving valency is unchanged
  (`NonTrivalentValencyThreeDescent.nonDanglingValency_endpointVertex_true_ordinary`
  and `ResolutionAwayFromWall.nonDanglingValency_retainedVertex`).
* `candBranchMap`, `candBranchEquiv`: **the branch vertices of the Type III
  candidate are the branch vertices of the wall datum other than the anchor,
  plus `A_u` and `A_v`.**  Surjectivity is the case analysis of
  `NonTrivalentValencyThreeExit.candidate_trivalent` read as a classification:
  over `u` an ordinary block has `nd(C_u) <= 2` and a non-selected fine class
  `nd <= 1`, so neither is a branch vertex; over `v` an ordinary block keeps
  `nd(B_v) = nd(B)`.
* `coverBranchEquiv`, `vertexEquiv`: the composite
  `BranchVertex cand.datum ~ BranchVertex M_0-minus-A + Bool ~
   BranchVertex M-minus-ends + Bool ~ BranchVertex M ~ V`,
  the last step being the incoming tracking `wd.tracks.iso.vtx`.
* `vertexEquiv_anchor_false`, `vertexEquiv_anchor_true`: under (H-III)'s
  orientation, `A_u` goes to `graph.vert m.base` and `A_v` to
  `graph.vert (graph.op m.base)`; `vertexEquiv_inl` reads the rest as
  `sourceVertexMap` followed by the incoming tracking.

### 5.  Three pieces of the star count

* `move_vert_eq_iff_of_ne`: away from the two ends of the vanishing occurrence
  the Whitehead move does not change the star -- `m.perm` is the transposition
  of `m.left` and `m.right`, which sit at those two ends.
* `card_star_eq_incidenceCount`: the star of a branch vertex of the *incoming*
  cover, counted in the tracked ambient graph
  (`MovedIncidenceIso.DatumGraphIncidence.ofIso` at the incoming tracking, with
  the row label read through the chart).
* `injective_retainedRow` and `incidenceCount_retainedVertex_retainedRow`:
  **away from the merged target vertex the candidate does not change the
  star.**  This is transport (T1) below off the wall; it is
  `ResolutionStableIncidence.incidenceCount_retainedVertex` with its row
  *equivalence* hypothesis weakened to injectivity of
  `NonTrivalentValencyThreeDescent.retainedRow` (whose complement is the bridge
  row), which is what that proof actually uses.

### 6.  The link, reduced to the star count

* `typeChangeLink_of_incidence`: **`OuterWalk.TypeChangeLink` at a three-valent
  wall from the star count alone.**  Feeding `vertexEquiv` to
  `MovedIncidenceIso.tracksOfMovedIncidence` and the result to
  `NonTrivalentValencyThreePathEnds.typeChangeLink_of_receipts'` leaves exactly
  one geometric hypothesis, `hIncidence` (`hOp` is free from the incoming
  tracking through `MovedIncidenceIso.label_op_of_tracks`).

## What is NOT proved here: the hypotheses that remain

1. `hIncidence` and hence `tracks`: the star count
   `incidenceCount cand.datum v r =
    Nat.card {d // (graph.move m).vert d = vertexEquiv v and label d = row r}`.
   Away from the anchor it is the composite of two transports.  This composite
   is not proved in this file; `NonTrivalentValencyThreeStarCount` proves it,
   establishing both transports at an ordinary wall block too:
   * (T1) `incidenceCount M_0 w r =
     incidenceCount cand.datum (candVertex w) (retainedRow r)`.  Off the merged
   target vertex this is `incidenceCount_retainedVertex_retainedRow` above;
   **at an ordinary wall block** it is
   `NonTrivalentValencyThreeStarCount.incidenceCount_endpointVertex_true_ordinary`,
   from the census of `NonTrivalentValencyThreeDescent`
   (`nonDanglingIncident_endpointVertex_true_ordinary`, which lists the star of
   `B_v` as the retained copies of `star_true(B)` together with one new
   occurrence per member of `star_false(B)`, plus
   `stablePath_retainedEdge_eq_newSourceEdge`, which puts that new occurrence
   on the row of the doubled-direction survivor it replaces).
   * (T2) `incidenceCount M_0 w r =
     incidenceCount M (branchEquivAnchorComplement.symm w) (incomingRow r)`.
   Off the merged target vertex this is
   `WallSplitIncidence.incidenceCount_sourceVertexMap`; **at an ordinary wall
   block** it is the valency-agnostic
   `WallSplitIncidenceOrdinary.incidenceCount_unramified`, *not* a special case
   of `WallSplitIncidence.incidenceCount_anchor`, whose `hFacetOver` hypothesis
   fails there (the internal occurrence of an ordinary fibre is not on the
   vanishing row).  The proof: an ordinary wall block is unramified
   (`NonTrivalentValencyThreeRigidity.localRamification_eq_zero_of_ne_anchor`),
   so `...internalEdges_subsingleton` and `...activeFibreVertices_eq_endpoints`
   make its fibre a point or a pair; in the pair case
   `lemma-ndval-of-GqA0` forces the two constituents to be trivalent and
   divalent, `NoContractedReturn` makes the internal occurrence the divalent
   one's only contracted occurrence, and its second occurrence lies on the same
   row, which is exactly the bookkeeping the count needs.
   At the anchor the count is the one (H-III) prescribes, together with the
   exact stars `NonTrivalentValencyThreeRows.nonDanglingIncident_endpointVertex_false/true`
   and `move_vert_eq_iff_of_ne` / `card_star_eq_incidenceCount` on the dart side;
   `NonTrivalentValencyThreeStarCount.typeChangeLink_of_prescribedDoubledMove`
   packages the result as `OuterWalk.TypeChangeLink` at a three-valent wall
   from (H-III) and `wallStar` alone.
2. `DoubledSeparated`, and (H-III) itself.  (H-III) is the per-vertex match at
   the anchor; `DoubledSeparated` is what makes the wall crossing an actual
   type change.  Neither is derived here.  With (H-III) stated at row level,
   `DoubledSeparated` is the geometric input of the *relative* witness only:
   the dispatcher discharges (H-III) through `prescribedDoubledMove_of_rows`,
   where separation of the two named rows is automatic
   (`IncomingPairing.vertex_of_movedStar_eq_pair`).
3. `wallStar : ThirdEquation.ThreeStar (contract wd.coverTarget wd.hab wd.hOne)
   <wd.a, wd.hab>`, exactly as in `NonTrivalentValencyThreeExit.exists_anchor_of_wallData`
   and `NonTrivalentValencyThreePathEnds.typeChangeLink_of_receipts'`: the
   valency dispatcher of `OuterWalk.WallData.valency` is not built here.

No structure is introduced.  The two `Prop` definitions are used as follows:
`PrescribedDoubledMove` has the relative witness
`prescribedDoubledMove_prescribedMove`; `DoubledSeparated` is a named
hypothesis of that witness, in the same style as
`StablePathFacetContraction.NoContractedReturn`, and is not inhabited here.

## Consumers

`NonTrivalentValencyThreeStarCount` proves (T1) and (T2) above and
delivers `typeChangeLink_of_prescribedDoubledMove`: `OuterWalk.TypeChangeLink`
at a three-valent wall from (H-III) and `wallStar` alone, via
`MovedIncidenceIso.tracksOfMovedIncidence` and hence the `tracks` field of
`NonTrivalentValencyThreePathEnds.typeChangeLink_of_receipts'`.  The
`hFibre`-free `branchEquivAnchorComplement` is also the form the valency-two
and valency-four exits need, since neither wall gives
`activeFibreVertices A = {leftEnd, rightEnd}` for free either.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeTracks

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.PrunedFibreValency
open DraismaVargas.LocalCases.PrunedFibreTree
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.ClassInjectivity
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

/-! ## 1.  The vanishing row is a single occurrence between two branch vertices -/

/-- The vanishing stable row of the incoming cover: the chart row of the move's
contracted dart. -/
def facetRow : StablePath wd.cover := wd.fullDim.labelling.row.symm (label m.base)

/-- Every surviving occurrence of the vanishing row lies over the contracted
target occurrence. -/
theorem over_contracted_of_facetRow (e : NonDanglingEdge wd.cover)
    (he : e.stablePath = facetRow m wd) : e.1.1.1 = wd.contracted :=
  LeafFacetNoReturn.facetRow_over_contracted wd.cover wd.fullDim wd.coordinates (label m.base)
    wd.hZeroCoord wd.hPosCoord wd.hFacetZero e he

/-- **The ends of the vanishing row are not divalent.**  A divalent end would
carry a second surviving occurrence on the same row, hence a second surviving
occurrence over the contracted target occurrence, which `NoContractedReturn`
forbids. -/
theorem nonDanglingValency_ne_two_of_incident_facetRow
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (e : NonDanglingEdge wd.cover) (he : e.stablePath = facetRow m wd)
    (v : wd.cover.SourceVertex) (hv : Incident wd.cover e.1 v) :
    nonDanglingValency wd.cover v ≠ 2 := by
  classical
  intro hTwo
  obtain ⟨other, hNe, hPair⟩ := nonDanglingIncident_eq_pair wd.cover hTwo e.2 hv
  have hOtherMem : other ∈ nonDanglingIncident wd.cover v := by
    rw [hPair]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨hOtherSurv, hOtherInc⟩ := (mem_nonDanglingIncident _ _ _).mp hOtherMem
  have hRow : NonDanglingEdge.stablePath
      (⟨other, hOtherSurv⟩ : NonDanglingEdge wd.cover) = e.stablePath :=
    PrunedFibreStablePath.stablePath_eq_of_incident_divalent wd.cover ⟨other, hOtherSurv⟩ e v
      hOtherInc hv hTwo
  have hOtherOver : other.1.1 = wd.contracted :=
    over_contracted_of_facetRow m wd (⟨other, hOtherSurv⟩ : NonDanglingEdge wd.cover)
      (hRow.trans he)
  exact hNe (NonTrivalentValencyThreeExit.noContractedReturn_of_valency_three m wd wallStar
    v hTwo other e.1 hOtherOver (over_contracted_of_facetRow m wd e he) hOtherSurv e.2
    hOtherInc hv)

/-- The vanishing row has a surviving occurrence. -/
theorem exists_facetEdge : ∃ e : NonDanglingEdge wd.cover, e.stablePath = facetRow m wd :=
  Quot.exists_rep _

/-- **The vanishing occurrence `h₁`**: the unique surviving occurrence of the
vanishing row. -/
def facetEdge : NonDanglingEdge wd.cover := Classical.choose (exists_facetEdge m wd)

theorem facetEdge_stablePath : (facetEdge m wd).stablePath = facetRow m wd :=
  Classical.choose_spec (exists_facetEdge m wd)

theorem facetEdge_over_contracted : (facetEdge m wd).1.1.1 = wd.contracted :=
  over_contracted_of_facetRow m wd _ (facetEdge_stablePath m wd)

/-- The `A_u` end of the vanishing occurrence. -/
def leftEnd : wd.cover.SourceVertex := (wd.cover.sourceEnds (facetEdge m wd).1).1

/-- The `A_v` end of the vanishing occurrence. -/
def rightEnd : wd.cover.SourceVertex := (wd.cover.sourceEnds (facetEdge m wd).1).2

theorem incident_facetEdge_leftEnd : Incident wd.cover (facetEdge m wd).1 (leftEnd m wd) :=
  Or.inl rfl

theorem incident_facetEdge_rightEnd : Incident wd.cover (facetEdge m wd).1 (rightEnd m wd) :=
  Or.inr rfl

theorem leftEnd_ne_rightEnd : leftEnd m wd ≠ rightEnd m wd :=
  wd.cover.sourceEnds_ne (facetEdge m wd).1

/-- Both ends of the vanishing occurrence are branch vertices of the incoming
cover. -/
theorem three_le_nonDanglingValency_end
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (v : wd.cover.SourceVertex) (hv : Incident wd.cover (facetEdge m wd).1 v) :
    3 ≤ nonDanglingValency wd.cover v := by
  have hTwo := nonDanglingValency_ne_two_of_incident_facetRow m wd wallStar _
    (facetEdge_stablePath m wd) v hv
  have hOne := NonDanglingValency.nonDanglingValency_ne_one wd.cover wd.fullDim.connected v
  have hZero := nonDanglingValency_ne_zero_of_incident wd.cover (facetEdge m wd).2 hv
  omega

theorem nonDanglingValency_leftEnd_ne_two
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    nonDanglingValency wd.cover (wd.cover.sourceEnds (facetEdge m wd).1).1 ≠ 2 := by
  show nonDanglingValency wd.cover (leftEnd m wd) ≠ 2
  have := three_le_nonDanglingValency_end m wd wallStar (leftEnd m wd)
    (incident_facetEdge_leftEnd m wd)
  omega

theorem nonDanglingValency_rightEnd_ne_two
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    nonDanglingValency wd.cover (wd.cover.sourceEnds (facetEdge m wd).1).2 ≠ 2 := by
  show nonDanglingValency wd.cover (rightEnd m wd) ≠ 2
  have := three_le_nonDanglingValency_end m wd wallStar (rightEnd m wd)
    (incident_facetEdge_rightEnd m wd)
  omega

/-- **Uniqueness of the vanishing occurrence.** -/
theorem eq_facetEdge
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (e : NonDanglingEdge wd.cover) (he : e.stablePath = facetRow m wd) :
    e = facetEdge m wd := by
  exact NonTrivalentUniqueFourValent.eq_of_stablePath_eq_of_ends_ne_two (facetEdge m wd)
    (nonDanglingValency_leftEnd_ne_two m wd wallStar)
    (nonDanglingValency_rightEnd_ne_two m wd wallStar) e
    (he.trans (facetEdge_stablePath m wd).symm)


/-! ## 2.  The vanishing occurrence sits inside the anchor fibre -/

section Anchor

variable {wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}

/-- The anchor of the wall datum: the four-valent merged source vertex. -/
def anchorVertex
    (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex :=
  WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk

theorem nonDanglingValency_anchorVertex
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk) :
    nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (anchorVertex m wd anchorBlk) = 4 :=
  NonTrivalentValencyThreeRows.nonDanglingValency_anchor src

theorem leftEnd_target : (leftEnd m wd).1.1 = wd.a := by
  have h : (wd.cover.sourceEnds (facetEdge m wd).1).1.1.1 =
      ((facetEdge m wd).1.1.1 : wd.coverTarget.V × wd.coverTarget.V).1 :=
    sourceEnds_fst_fst wd.cover (facetEdge m wd).1
  show (wd.cover.sourceEnds (facetEdge m wd).1).1.1.1 = wd.a
  rw [h, facetEdge_over_contracted m wd]

theorem rightEnd_target : (rightEnd m wd).1.1 = wd.b := by
  have h : (wd.cover.sourceEnds (facetEdge m wd).1).2.1.1 =
      ((facetEdge m wd).1.1.1 : wd.coverTarget.V × wd.coverTarget.V).2 :=
    sourceEnds_snd_fst wd.cover (facetEdge m wd).1
  show (wd.cover.sourceEnds (facetEdge m wd).1).2.1.1 = wd.b
  rw [h, facetEdge_over_contracted m wd]

/-- Both ends of the vanishing occurrence lie in one fibre. -/
theorem sourceVertexMap_leftEnd_eq_rightEnd :
    sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd) =
      sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (rightEnd m wd) :=
  sourceVertexMap_sourceEnds_eq_of_contracted wd.cover wd.hc wd.hab wd.hOne
    (facetEdge m wd).1 (facetEdge_over_contracted m wd)

theorem leftEnd_mem_activeFibre :
    leftEnd m wd ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd)) :=
  (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne _ _).mpr
    ⟨rfl, nonDanglingValency_ne_zero_of_incident wd.cover (facetEdge m wd).2
      (incident_facetEdge_leftEnd m wd)⟩

theorem rightEnd_mem_activeFibre :
    rightEnd m wd ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd)) :=
  (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne _ _).mpr
    ⟨(sourceVertexMap_leftEnd_eq_rightEnd m wd).symm,
      nonDanglingValency_ne_zero_of_incident wd.cover (facetEdge m wd).2
        (incident_facetEdge_rightEnd m wd)⟩

/-- **The fibre of the vanishing occurrence is four-valent downstairs.**  Both
of its ends are branch vertices, so `lemma-ndval-of-GqA0` gives at least `4`. -/
theorem four_le_nonDanglingValency_map_leftEnd
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    4 ≤ nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd)) := by
  classical
  have hSum := WallSplitIncidence.nonDanglingValency_eq_sum_activeFibre wd.cover wd.hc wd.hab
    wd.hOne (wd.hCompat m) (wd.hForest m)
    (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd))
    ⟨leftEnd m wd, leftEnd_mem_activeFibre m wd⟩
  set fibre := activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
    (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd)) with hfibre
  have hNonneg : ∀ u ∈ fibre, (0 : ℤ) ≤ (nonDanglingValency wd.cover u : ℤ) - 2 := by
    intro u hu
    have := WallSplitIncidence.two_le_nonDanglingValency_of_mem_activeFibre wd.cover wd.hc wd.hab
      wd.hOne wd.fullDim.connected _ u hu
    omega
  have hPair : ({leftEnd m wd, rightEnd m wd} : Finset wd.cover.SourceVertex) ⊆ fibre := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact leftEnd_mem_activeFibre m wd
    · exact rightEnd_mem_activeFibre m wd
  have hLe := Finset.sum_le_sum_of_subset_of_nonneg hPair (fun u hu _ ↦ hNonneg u hu)
  rw [Finset.sum_pair (leftEnd_ne_rightEnd m wd)] at hLe
  have hL := three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_leftEnd m wd)
  have hR := three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_rightEnd m wd)
  omega


/-- **The vanishing occurrence lies over the anchor.**  Its fibre is
four-valent downstairs, and every wall block other than the anchor is
trivalent. -/
theorem sourceVertexMap_leftEnd_eq_anchorVertex
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk) :
    sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd) = anchorVertex m wd anchorBlk := by
  classical
  have hMap : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd) =
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) (leftEnd m wd).1.2 := by
    show (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
        (GraphContraction.fold wd.coverTarget wd.hab (leftEnd m wd).1.1) (leftEnd m wd).1.2 = _
    rw [leftEnd_target m wd, GraphContraction.fold_a]
  have hFour := four_le_nonDanglingValency_map_leftEnd m wd wallStar
  rw [hMap] at hFour
  by_cases hRel : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel anchorBlk.1
        (leftEnd m wd).1.2
  · rw [hMap]
    exact (NonTrivalentValencyThreeExit.sourceEndpoint_eq_of_rel hRel).symm
  · exact absurd (NonTrivalentValencyThreeExit.ordinaryBlock_trivalent wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne (wd.hForest m) src (leftEnd m wd).1.2 hRel) (by omega)

/-- **The anchor fibre carries exactly the two ends of the vanishing
occurrence as branch vertices.** -/
theorem eq_leftEnd_or_eq_rightEnd_of_mem_activeFibre
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (u : wd.cover.SourceVertex)
    (hu : u ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne (anchorVertex m wd anchorBlk))
    (hThree : 3 ≤ nonDanglingValency wd.cover u) :
    u = leftEnd m wd ∨ u = rightEnd m wd := by
  classical
  by_contra hBad
  obtain ⟨hBadL, hBadR⟩ := not_or.mp hBad
  have hSum := WallSplitIncidence.nonDanglingValency_eq_sum_activeFibre wd.cover wd.hc wd.hab
    wd.hOne (wd.hCompat m) (wd.hForest m) (anchorVertex m wd anchorBlk) ⟨u, hu⟩
  rw [nonDanglingValency_anchorVertex m wd src] at hSum
  have hL : leftEnd m wd ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (anchorVertex m wd anchorBlk) := by
    rw [← sourceVertexMap_leftEnd_eq_anchorVertex m wd wallStar src]
    exact leftEnd_mem_activeFibre m wd
  have hR : rightEnd m wd ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (anchorVertex m wd anchorBlk) := by
    rw [← sourceVertexMap_leftEnd_eq_anchorVertex m wd wallStar src]
    exact rightEnd_mem_activeFibre m wd
  have hNonneg : ∀ w ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (anchorVertex m wd anchorBlk), (0 : ℤ) ≤ (nonDanglingValency wd.cover w : ℤ) - 2 := by
    intro w hw
    have := WallSplitIncidence.two_le_nonDanglingValency_of_mem_activeFibre wd.cover wd.hc wd.hab
      wd.hOne wd.fullDim.connected _ w hw
    omega
  have hTriple : ({leftEnd m wd, rightEnd m wd, u} : Finset wd.cover.SourceVertex) ⊆
      activeFibreVertices wd.cover wd.hc wd.hab wd.hOne (anchorVertex m wd anchorBlk) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hL
    · exact hR
    · exact hu
  have hLe := Finset.sum_le_sum_of_subset_of_nonneg hTriple (fun w hw _ ↦ hNonneg w hw)
  rw [show ({leftEnd m wd, rightEnd m wd, u} : Finset wd.cover.SourceVertex) =
      insert (leftEnd m wd) {rightEnd m wd, u} from rfl,
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact not_or.mpr ⟨leftEnd_ne_rightEnd m wd, fun h ↦ hBadL h.symm⟩),
    Finset.sum_pair (fun h ↦ hBadR h.symm)] at hLe
  have hLv := three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_leftEnd m wd)
  have hRv := three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_rightEnd m wd)
  omega


/-- **The wall datum is trivalent away from the anchor.**  Off the merged
target vertex this is the incoming trivalence
(`NonTrivalentValencyTwoExit.wallDatum_trivalent_away`); at a wall block other
than the anchor it is the bound of `NonTrivalentAnchorValency`, read through
`NonTrivalentValencyThreeExit.ordinaryBlock_trivalent`. -/
theorem wallDatum_trivalent_away_anchor
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hw : w ≠ anchorVertex m wd anchorBlk) :
    nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne) w ≤ 3 := by
  classical
  by_cases hTarget : w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
  · have hSelf : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) w.1.2 = w :=
      (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hTarget.symm, rfl⟩
    have hRel : ¬ ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel anchorBlk.1 w.1.2 := by
      intro hBad
      exact hw ((NonTrivalentValencyThreeExit.sourceEndpoint_eq_of_rel hBad).trans hSelf).symm
    rw [← hSelf]
    exact NonTrivalentValencyThreeExit.ordinaryBlock_trivalent wd.cover wd.fullDim wd.hc wd.hab
      wd.hOne (wd.hForest m) src w.1.2 hRel
  · exact NonTrivalentValencyTwoExit.wallDatum_trivalent_away wd.cover wd.fullDim wd.hc wd.hab
      wd.hOne (wd.hForest m) w hTarget

/-- **The branch-vertex dictionary across the wall contraction**, with the
`hFibre` hypothesis of `WallSplitIncidence` replaced by the branch-pair
statement proved above:
away from the anchor `sourceVertexMap` is a bijection from the branch vertices
of the incoming cover other than the two ends of the vanishing occurrence onto
the branch vertices of the wall datum other than the anchor. -/
def branchEquivAnchorComplement
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk) :
    {v : BranchVertex wd.cover // v.1 ≠ leftEnd m wd ∧ v.1 ≠ rightEnd m wd} ≃
      {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
        w.1 ≠ anchorVertex m wd anchorBlk} := by
  classical
  have hNeAnchor : ∀ v : wd.cover.SourceVertex, 3 ≤ nonDanglingValency wd.cover v →
      v ≠ leftEnd m wd → v ≠ rightEnd m wd →
      sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v ≠ anchorVertex m wd anchorBlk := by
    intro v hv hvl hvr hBad
    have hMem : v ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
        (anchorVertex m wd anchorBlk) :=
      (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne _ v).mpr ⟨hBad, by omega⟩
    rcases eq_leftEnd_or_eq_rightEnd_of_mem_activeFibre m wd wallStar src v hMem hv with h | h
    · exact hvl h
    · exact hvr h
  refine Equiv.ofBijective
    (fun v ↦ ⟨⟨sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1,
      WallSplitIncidence.three_le_nonDanglingValency_sourceVertexMap wd.cover wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) wd.fullDim.connected v.1.1 v.1.2⟩,
      hNeAnchor v.1.1 v.1.2 v.2.1 v.2.2⟩) ⟨?_, ?_⟩
  · intro v v' hEq
    have hMap : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1 =
        sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v'.1.1 :=
      congrArg (fun w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
        w.1 ≠ anchorVertex m wd anchorBlk} ↦ w.1.1) hEq
    have hLe := wallDatum_trivalent_away_anchor m wd wallStar src
      (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1)
      (hNeAnchor v.1.1 v.1.2 v.2.1 v.2.2)
    have hMemV : v.1.1 ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
        (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1) :=
      (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne _ v.1.1).mpr
        ⟨rfl, by have := v.1.2; omega⟩
    have hMemV' : v'.1.1 ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
        (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1) :=
      (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne _ v'.1.1).mpr
        ⟨hMap.symm, by have := v'.1.2; omega⟩
    exact Subtype.ext (Subtype.ext (WallSplitIncidence.eq_of_mem_activeFibre_of_three_le wd.cover
      wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) wd.fullDim.connected _ hLe v.1.1 v'.1.1
      hMemV hMemV' v.1.2 v'.1.2))
  · intro w
    obtain ⟨u, hu, hThree⟩ := WallSplitIncidence.exists_three_le_mem_activeFibre wd.cover wd.hc
      wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) w.1.1 w.1.2
    obtain ⟨hMapU, -⟩ := (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne w.1.1 u).mp hu
    have hul : u ≠ leftEnd m wd := by
      intro hBad
      refine w.2 ?_
      rw [← hMapU, hBad, sourceVertexMap_leftEnd_eq_anchorVertex m wd wallStar src]
    have hur : u ≠ rightEnd m wd := by
      intro hBad
      refine w.2 ?_
      rw [← hMapU, hBad, ← sourceVertexMap_leftEnd_eq_rightEnd m wd,
        sourceVertexMap_leftEnd_eq_anchorVertex m wd wallStar src]
    exact ⟨⟨⟨u, hThree⟩, hul, hur⟩, Subtype.ext (Subtype.ext hMapU)⟩

@[simp] theorem branchEquivAnchorComplement_apply
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (v : {v : BranchVertex wd.cover // v.1 ≠ leftEnd m wd ∧ v.1 ≠ rightEnd m wd}) :
    (branchEquivAnchorComplement m wd wallStar src v).1.1 =
      sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1 := rfl


/-! ## 3.  (H-III): the prescribed doubled-direction move -/

/-- The `A_u` end of the vanishing occurrence, as a branch vertex. -/
def leftBranch (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    BranchVertex wd.cover :=
  ⟨leftEnd m wd,
    three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_leftEnd m wd)⟩

/-- The `A_v` end of the vanishing occurrence, as a branch vertex. -/
def rightBranch (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    BranchVertex wd.cover :=
  ⟨rightEnd m wd,
    three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_rightEnd m wd)⟩

/-- The dart of the vanishing occurrence at the `A_u` end. -/
def facetDartLeft (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    StableSourceDarts.Dart wd.cover :=
  ⟨leftBranch m wd wallStar, ⟨facetEdge m wd, incident_facetEdge_leftEnd m wd⟩⟩

/-- The dart of the vanishing occurrence at the `A_v` end. -/
def facetDartRight (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    StableSourceDarts.Dart wd.cover :=
  ⟨rightBranch m wd wallStar, ⟨facetEdge m wd, incident_facetEdge_rightEnd m wd⟩⟩

/-- A surviving occurrence of the wall datum, read as a surviving occurrence of
the incoming cover. -/
def liftEdge (g : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    NonDanglingEdge wd.cover :=
  WallDegeneration.nonDanglingEmbedding wd.cover (wd.hCompat m).1 g

theorem stablePath_liftEdge (g : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (liftEdge m wd g).stablePath =
      incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m)
        g.stablePath := rfl

section Doubled

variable {wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}

theorem firstDoubled_survives
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk) :
    ¬ IsDangling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (Prescribed.firstDoubled src).1 :=
  (W3R1SourceProfile.mem_survivors _ _ _).mp
    ((mem_directionSurvivors _ _ _ _ _).mp (Prescribed.firstDoubled_mem src)).1

theorem secondDoubled_survives
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk) :
    ¬ IsDangling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (Prescribed.secondDoubled src).1 :=
  (W3R1SourceProfile.mem_survivors _ _ _).mp
    ((mem_directionSurvivors _ _ _ _ _).mp (Prescribed.secondDoubled_mem src)).1

/-- The two doubled-direction survivors of the anchor (the paper's `e_2`, `e_5`)
as surviving occurrences of the incoming cover. -/
def doubledLift
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (side : Bool) : NonDanglingEdge wd.cover :=
  liftEdge m wd (if side then ⟨(Prescribed.secondDoubled src).1, secondDoubled_survives m wd src⟩
    else ⟨(Prescribed.firstDoubled src).1, firstDoubled_survives m wd src⟩)

/-- **(H-III), the per-vertex match at the anchor.**  The two darts that the
Whitehead move `m` places together with `m.base` -- that is, the moved star of
`graph.vert m.base` with `m.base` removed -- carry the two stable **rows** of
the doubled-direction survivors of the anchor, in the orientation that puts
`A_u` at `graph.vert m.base`: the first conjunct says that `m.base` is the dart
of the vanishing occurrence at the `A_u` end.

The survivor clause is at the level of rows, `d.2.1.stablePath = ...`, not of
occurrences.  That is what the star count consumes
(`NonTrivalentValencyThreeStarCount.label_dart_doubled`, through
`IncomingPairing.label_dart_of_row`), and it is the only form that is
satisfiable at the incoming shapes the paper's Case (r1) allows: a
doubled-direction survivor may reach its end of the vanishing occurrence through
a *pass-through* occurrence over the contracted target edge, in which case no
dart at that end is the survivor's own occurrence.

The other orientation is normalised away by the caller with
`CubicDartGraph.MoveData.swap`, which leaves `graph.move m` unchanged
(`CubicDartGraph.move_swap`) and exchanges `m.base` with `graph.op m.base`. -/
def PrescribedDoubledMove
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk) :
    Prop :=
  wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base ∧
    ∃ first second : StableSourceDarts.Dart wd.cover,
      first.2.1.stablePath = (doubledLift m wd src false).stablePath ∧
        second.2.1.stablePath = (doubledLift m wd src true).stablePath ∧
        (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
          {wd.tracks.iso.dart first, wd.tracks.iso.dart second}

/-- **The occurrence-level clause implies (H-III).**  If the two darts the move
places with `m.base` *are* the occurrences of the two doubled-direction
survivors -- the occurrence-level form of the condition -- then
they carry their rows, so (H-III) holds.  The converse fails: a survivor may
reach its end of the vanishing occurrence through a pass-through occurrence over
the contracted target edge, and then no dart at that end is that occurrence. -/
theorem prescribedDoubledMove_of_occurrence
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base)
    (first second : StableSourceDarts.Dart wd.cover)
    (hFirst : first.2.1 = doubledLift m wd src false)
    (hSecond : second.2.1 = doubledLift m wd src true)
    (hStar : (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart first, wd.tracks.iso.dart second}) :
    PrescribedDoubledMove m wd wallStar src :=
  ⟨hBase, first, second, by rw [hFirst], by rw [hSecond], hStar⟩

/-- **(H-III) from the orientation clause and two moved darts carrying the two
doubled rows.**  This is the shape the valency dispatcher consumes: it obtains
the two darts from `IncomingPairing.exists_movedStar_darts` (which also says
that one sits at each end of the vanishing occurrence, so no separation
hypothesis is needed here), checks that their rows are the doubled pair, and
applies this lemma.  For the other order of the pair, apply it to `y`, `x` after
`Finset.pair_comm`. -/
theorem prescribedDoubledMove_of_rows
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base)
    (x y : StableSourceDarts.Dart wd.cover)
    (hx : x.2.1.stablePath = (doubledLift m wd src false).stablePath)
    (hy : y.2.1.stablePath = (doubledLift m wd src true).stablePath)
    (hStar : (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart x, wd.tracks.iso.dart y}) :
    PrescribedDoubledMove m wd wallStar src :=
  ⟨hBase, x, y, hx, hy, hStar⟩

end Doubled


/-! ## 4.  The branch vertices of the outgoing candidate -/

/-- A wall-datum vertex over the merged target vertex is the source endpoint of
its own sheet. -/
theorem sourceEndpoint_self (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hw : w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)) :
    (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) w.1.2 = w :=
  (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hw.symm, rfl⟩

/-- A wall vertex other than the anchor is an ordinary block. -/
theorem not_rel_anchor_of_ne
    {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hw : w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b))
    (hne : w ≠ anchorVertex m wd anchorBlk) :
    ¬ ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel anchorBlk.1 w.1.2 := by
  intro hBad
  exact hne (((NonTrivalentValencyThreeExit.sourceEndpoint_eq_of_rel hBad).trans
    (sourceEndpoint_self m wd w hw)).symm)

section Candidate

variable {wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
  (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)

open scoped Classical in
/-- **The outgoing vertex over a wall-datum vertex other than the anchor.**
Over the merged target vertex the candidate keeps the whole block on the
trivalent side `v`; away from it the vertex is simply retained. -/
def candVertex (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex) :
    (Prescribed.validCandidate src hNoGlue hValid).datum.SourceVertex :=
  if w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) then
    NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid true w.1.2
  else ResolutionAwayFromWall.retainedVertex (Prescribed.validCandidate src hNoGlue hValid) w

theorem candVertex_wall (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hw : w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)) :
    candVertex m wd src hNoGlue hValid w =
      NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid true w.1.2 := by
  unfold candVertex
  rw [if_pos hw]

theorem candVertex_away (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hw : w.1.1 ≠ (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)) :
    candVertex m wd src hNoGlue hValid w =
      ResolutionAwayFromWall.retainedVertex (Prescribed.validCandidate src hNoGlue hValid) w := by
  unfold candVertex
  rw [if_neg hw]

/-- **The surviving valency is unchanged.** -/
theorem nonDanglingValency_candVertex
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hne : w ≠ anchorVertex m wd anchorBlk) :
    nonDanglingValency (Prescribed.validCandidate src hNoGlue hValid).datum
        (candVertex m wd src hNoGlue hValid w) =
      nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne) w := by
  classical
  by_cases hw : w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
  · rw [candVertex_wall m wd src hNoGlue hValid w hw,
      NonTrivalentValencyThreeDescent.nonDanglingValency_endpointVertex_true_ordinary src hNoGlue
        hValid (not_rel_anchor_of_ne m wd w hw hne),
      sourceEndpoint_self m wd w hw]
  · rw [candVertex_away m wd src hNoGlue hValid w hw,
      ResolutionAwayFromWall.nonDanglingValency_retainedVertex
        (Prescribed.validCandidate src hNoGlue hValid) hValid
        (NonTrivalentValencyThreeRows.candidate_sourceGenus src hNoGlue hValid) w hw]


theorem anchorVertex_target
    (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    (anchorVertex m wd anchorBlk).1.1 =
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) :=
  ((GluingDatum.sourceEndpoint_eq_iff (contractDatum wd.cover wd.hc wd.hab wd.hOne) _ _ _).mp
    rfl).1.symm

theorem candVertex_wall_target (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hw : w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)) :
    (candVertex m wd src hNoGlue hValid w).1.1 =
      TargetExpansion.freshVertex (contract wd.coverTarget wd.hab wd.hOne) := by
  rw [candVertex_wall m wd src hNoGlue hValid w hw]
  exact ((GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mp rfl).1.symm

theorem candVertex_away_target (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hw : w.1.1 ≠ (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)) :
    (candVertex m wd src hNoGlue hValid w).1.1 =
      TargetExpansion.oldVertex (contract wd.coverTarget wd.hab wd.hOne) w.1.1 := by
  rw [candVertex_away m wd src hNoGlue hValid w hw]
  exact ((GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mp rfl).1.symm

theorem endpointVertex_target (side : Bool) (y : Fin degree) :
    (NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid side y).1.1 =
      (if side then TargetExpansion.freshVertex (contract wd.coverTarget wd.hab wd.hOne)
        else TargetExpansion.oldVertex (contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩) :=
  ((GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mp rfl).1.symm

/-- Two vertices of the candidate over the fresh target vertex coincide
exactly when their sheets are related there. -/
theorem endpointVertex_true_inj {y y' : Fin degree}
    (hEq : NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid true y =
      NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid true y') :
    ((Prescribed.validCandidate src hNoGlue hValid).datum.vertexPartition
      (TargetExpansion.freshVertex (contract wd.coverTarget wd.hab wd.hOne))).Rel y y' := by
  have h := (GluingDatum.sourceEndpoint_eq_iff
      (Prescribed.validCandidate src hNoGlue hValid).datum
      (TargetExpansion.freshVertex (contract wd.coverTarget wd.hab wd.hOne)) y
      (NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid true y')).mp hEq
  set part := (Prescribed.validCandidate src hNoGlue hValid).datum.vertexPartition
    (TargetExpansion.freshVertex (contract wd.coverTarget wd.hab wd.hOne)) with hpart
  have h2 : part.repr y =
      part.repr (NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid true y').1.2 :=
    h.2
  have hs : (NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid true y').1.2 =
      part.repr y' := rfl
  show part.repr y = part.repr y'
  rw [h2, hs, part.repr_idem]


/-- **The branch vertices of the outgoing candidate.**  Every branch vertex of
the Type III candidate is either the outgoing copy of a branch vertex of the
wall datum other than the anchor, or one of the two anchor ends `A_u`, `A_v`. -/
def candBranchMap :
    ({w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
        w.1 ≠ anchorVertex m wd anchorBlk} ⊕ Bool) →
      BranchVertex (Prescribed.validCandidate src hNoGlue hValid).datum
  | Sum.inl w => ⟨candVertex m wd src hNoGlue hValid w.1.1, by
      rw [nonDanglingValency_candVertex m wd src hNoGlue hValid w.1.1 w.2]
      exact w.1.2⟩
  | Sum.inr side => ⟨NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid side
      (Prescribed.selectedRepresentative src),
      (NonTrivalentValencyThreeRows.nonDanglingValency_endpointVertex src hNoGlue hValid
        side).ge⟩

theorem candBranchMap_injective :
    Function.Injective (candBranchMap m wd src hNoGlue hValid (anchorBlk := anchorBlk)) := by
  classical
  have hWallTarget : ∀ w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
      w.1 ≠ anchorVertex m wd anchorBlk},
      w.1.1.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) →
      ¬ ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel anchorBlk.1 w.1.1.1.2 :=
    fun w hw ↦ not_rel_anchor_of_ne m wd w.1.1 hw w.2
  rintro (w | side) (w' | side') hEq <;>
    have hv : (candBranchMap m wd src hNoGlue hValid (anchorBlk := anchorBlk) _).1 =
        (candBranchMap m wd src hNoGlue hValid (anchorBlk := anchorBlk) _).1 :=
      congrArg Subtype.val hEq
  · by_cases hw : w.1.1.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) <;>
      by_cases hw' : w'.1.1.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
    · have hEq2 : NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid true w.1.1.1.2 =
          NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid true w'.1.1.1.2 := by
        rw [← candVertex_wall m wd src hNoGlue hValid w.1.1 hw,
          ← candVertex_wall m wd src hNoGlue hValid w'.1.1 hw']
        exact hv
      have hRel := (NonTrivalentValencyThreeDescent.candidate_vertexPartition_rel_ordinary src
        hNoGlue hValid true (hWallTarget w hw)).mp
          (endpointVertex_true_inj m wd src hNoGlue hValid hEq2)
      have hSheet : w.1.1.1.2 = w'.1.1.1.2 := by
        have h1 : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
            w.1.1.1.1).repr w.1.1.1.2 = w.1.1.1.2 := w.1.1.2
        have h2 : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
            w'.1.1.1.1).repr w'.1.1.1.2 = w'.1.1.1.2 := w'.1.1.2
        rw [hw] at h1
        rw [hw'] at h2
        rw [← h1, ← h2]
        exact hRel
      exact congrArg Sum.inl (Subtype.ext (Subtype.ext (Subtype.ext
        (Prod.ext (hw.trans hw'.symm) hSheet))))
    · exact absurd ((candVertex_wall_target m wd src hNoGlue hValid w.1.1 hw).symm.trans
        ((congrArg (fun z : (Prescribed.validCandidate src hNoGlue hValid).datum.SourceVertex ↦
          z.1.1) hv).trans (candVertex_away_target m wd src hNoGlue hValid w'.1.1 hw')))
        (Sum.inr_ne_inl)
    · exact absurd ((candVertex_away_target m wd src hNoGlue hValid w.1.1 hw).symm.trans
        ((congrArg (fun z : (Prescribed.validCandidate src hNoGlue hValid).datum.SourceVertex ↦
          z.1.1) hv).trans (candVertex_wall_target m wd src hNoGlue hValid w'.1.1 hw')))
        (Sum.inl_ne_inr)
    · have hRet : ResolutionAwayFromWall.retainedVertex
          (Prescribed.validCandidate src hNoGlue hValid) w.1.1 =
          ResolutionAwayFromWall.retainedVertex
            (Prescribed.validCandidate src hNoGlue hValid) w'.1.1 := by
        rw [← candVertex_away m wd src hNoGlue hValid w.1.1 hw,
          ← candVertex_away m wd src hNoGlue hValid w'.1.1 hw']
        exact hv
      exact congrArg Sum.inl (Subtype.ext (Subtype.ext
        (ResolutionStableIncidence.retainedVertex_injective_away
          (Prescribed.validCandidate src hNoGlue hValid) w.1.1 w'.1.1 hw hw' hRet)))
  · exfalso
    have hv' : candVertex m wd src hNoGlue hValid w.1.1 =
        NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid side'
          (Prescribed.selectedRepresentative src) := hv
    have hTarget := congrArg (fun z :
      (Prescribed.validCandidate src hNoGlue hValid).datum.SourceVertex ↦ z.1.1) hv'
    rw [endpointVertex_target m wd src hNoGlue hValid side'
      (Prescribed.selectedRepresentative src)] at hTarget
    by_cases hw : w.1.1.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
    · rw [candVertex_wall_target m wd src hNoGlue hValid w.1.1 hw] at hTarget
      cases side' with
      | false => exact Sum.inr_ne_inl hTarget
      | true =>
        have hEq2 : NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid true w.1.1.1.2 =
            NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid true
              (Prescribed.selectedRepresentative src) := by
          rw [← candVertex_wall m wd src hNoGlue hValid w.1.1 hw]
          exact hv'
        have hRel := (NonTrivalentValencyThreeDescent.candidate_vertexPartition_rel_ordinary src
          hNoGlue hValid true (hWallTarget w hw)).mp
            (endpointVertex_true_inj m wd src hNoGlue hValid hEq2)
        exact hWallTarget w hw ((NonTrivalentValencyThreeRows.rep_wall_rel src).trans hRel.symm)
    · rw [candVertex_away_target m wd src hNoGlue hValid w.1.1 hw] at hTarget
      cases side' with
      | false => exact hw (Sum.inl_injective hTarget)
      | true => exact Sum.inl_ne_inr hTarget
  · exfalso
    have hv' : NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid side
          (Prescribed.selectedRepresentative src) =
        candVertex m wd src hNoGlue hValid w'.1.1 := hv
    have hTarget := congrArg (fun z :
      (Prescribed.validCandidate src hNoGlue hValid).datum.SourceVertex ↦ z.1.1) hv'
    rw [endpointVertex_target m wd src hNoGlue hValid side
      (Prescribed.selectedRepresentative src)] at hTarget
    by_cases hw : w'.1.1.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
    · rw [candVertex_wall_target m wd src hNoGlue hValid w'.1.1 hw] at hTarget
      cases side with
      | false => exact Sum.inl_ne_inr hTarget
      | true =>
        have hEq2 : NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid true
              (Prescribed.selectedRepresentative src) =
            NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid true w'.1.1.1.2 := by
          rw [← candVertex_wall m wd src hNoGlue hValid w'.1.1 hw]
          exact hv'
        have hRel := (NonTrivalentValencyThreeDescent.candidate_vertexPartition_rel_ordinary src
          hNoGlue hValid true (hWallTarget w' hw)).mp
            (endpointVertex_true_inj m wd src hNoGlue hValid hEq2.symm)
        exact hWallTarget w' hw ((NonTrivalentValencyThreeRows.rep_wall_rel src).trans hRel.symm)
    · rw [candVertex_away_target m wd src hNoGlue hValid w'.1.1 hw] at hTarget
      cases side with
      | false => exact hw (Sum.inl_injective hTarget.symm)
      | true => exact Sum.inr_ne_inl hTarget
  · have hv' : NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid side
          (Prescribed.selectedRepresentative src) =
        NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid side'
          (Prescribed.selectedRepresentative src) := hv
    have hTarget := congrArg (fun z :
      (Prescribed.validCandidate src hNoGlue hValid).datum.SourceVertex ↦ z.1.1) hv'
    rw [endpointVertex_target m wd src hNoGlue hValid side
      (Prescribed.selectedRepresentative src),
      endpointVertex_target m wd src hNoGlue hValid side'
        (Prescribed.selectedRepresentative src)] at hTarget
    cases side <;> cases side' <;>
      first
        | rfl
        | exact absurd hTarget Sum.inl_ne_inr
        | exact absurd hTarget Sum.inr_ne_inl


theorem candBranchMap_surjective :
    Function.Surjective (candBranchMap m wd src hNoGlue hValid (anchorBlk := anchorBlk)) := by
  classical
  intro v
  by_cases hFresh : v.1.1.1 =
      TargetExpansion.freshVertex (contract wd.coverTarget wd.hab wd.hOne)
  · have hV : NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid true v.1.1.2 = v.1 :=
      NonTrivalentValencyThreeExit.eq_endpointVertex wd.cover wd.hc wd.hab wd.hOne src hNoGlue
        hValid true v.1 (by rw [hFresh]; rfl)
    by_cases hRel : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel anchorBlk.1 v.1.1.2
    · refine ⟨Sum.inr true, Subtype.ext ?_⟩
      show NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid true
        (Prescribed.selectedRepresentative src) = v.1
      rw [NonTrivalentValencyThreeRows.endpointVertex_eq src hNoGlue hValid true
        (NonTrivalentValencyThreeRows.rep_wall_rel src)
        ((NonTrivalentValencyThreeRows.rep_wall_rel src).symm.trans hRel)]
      exact hV
    · have hNd0 := NonTrivalentValencyThreeDescent.nonDanglingValency_endpointVertex_true_ordinary
        src hNoGlue hValid hRel
      rw [hV] at hNd0
      have hNd : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
            (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) v.1.1.2) =
          nonDanglingValency (Prescribed.validCandidate src hNoGlue hValid).datum v.1 := hNd0.symm
      have hwne : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
          (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) v.1.1.2 ≠
          anchorVertex m wd anchorBlk := by
        intro hBad
        refine hRel ?_
        have h := ((GluingDatum.sourceEndpoint_eq_iff
          (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) v.1.1.2
          (anchorVertex m wd anchorBlk)).mp hBad).2
        set part := (contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) with hpart
        have hx : part.repr (anchorVertex m wd anchorBlk).1.2 = part.repr anchorBlk.1 :=
          part.repr_idem anchorBlk.1
        show part.repr anchorBlk.1 = part.repr v.1.1.2
        rw [← hx]
        exact h.symm
      refine ⟨Sum.inl ⟨⟨(contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) v.1.1.2,
        by rw [hNd]; exact v.2⟩, hwne⟩, Subtype.ext ?_⟩
      show candVertex m wd src hNoGlue hValid
        ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
          (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) v.1.1.2) = v.1
      rw [candVertex_wall m wd src hNoGlue hValid _ rfl]
      show NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid true
        (((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).repr v.1.1.2) = v.1
      rw [NonTrivalentValencyThreeDescent.endpointVertex_eq_ordinary src hNoGlue hValid true
        (NonTrivalentValencyThreeDescent.not_rel_repr hRel)
        (((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).rel_repr_left v.1.1.2)]
      exact hV
  · obtain ⟨place, hplace⟩ : ∃ place,
        v.1.1.1 = TargetExpansion.oldVertex (contract wd.coverTarget wd.hab wd.hOne) place := by
      cases h : v.1.1.1 with
      | inl p => exact ⟨p, rfl⟩
      | inr u => exact absurd h hFresh
    by_cases hwall : place = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
    · have hV : NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid false v.1.1.2 =
          v.1 :=
        NonTrivalentValencyThreeExit.eq_endpointVertex wd.cover wd.hc wd.hab wd.hOne src hNoGlue
          hValid false v.1 (by rw [hplace, hwall]; rfl)
      by_cases hAnchor : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel anchorBlk.1 v.1.1.2
      · by_cases hFine : (Prescribed.finePartition src).Rel
            (Prescribed.selectedRepresentative src) v.1.1.2
        · refine ⟨Sum.inr false, Subtype.ext ?_⟩
          show NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid false
            (Prescribed.selectedRepresentative src) = v.1
          rw [NonTrivalentValencyThreeRows.endpointVertex_eq src hNoGlue hValid false
            (NonTrivalentValencyThreeRows.rep_wall_rel src) hFine]
          exact hV
        · exfalso
          rcases Prescribed.finePartition_rel_or_singleton src v.1.1.2 hAnchor with h | hSing
          · exact hFine h
          · have hCard := Finset.card_le_card
              (NonTrivalentValencyThreeRows.nonDanglingIncident_singleton_subset src hNoGlue
                hValid hAnchor hSing hFine)
            rw [card_nonDanglingIncident, Finset.card_singleton, hV] at hCard
            have := v.2
            omega
      · exfalso
        have hCard := Finset.card_le_card
          (NonTrivalentValencyThreeDescent.nonDanglingIncident_endpointVertex_false_subset_ordinary
            src hNoGlue hValid hAnchor)
        rw [card_nonDanglingIncident, hV] at hCard
        have hPair := Finset.card_insert_le
          ((Prescribed.validCandidate src hNoGlue hValid).oldSourceEdge
            (NonTrivalentValencyThreeDescent.doubledOccurrence src v.1.1.2))
          ({(Prescribed.validCandidate src hNoGlue hValid).newSourceEdge v.1.1.2} :
            Finset (Prescribed.validCandidate src hNoGlue hValid).datum.SourceEdge)
        rw [Finset.card_singleton] at hPair
        have := v.2
        omega
    · obtain ⟨old, hOld, hRet⟩ := ResolutionAwayFromWall.exists_retainedVertex_of_target
        (Prescribed.validCandidate src hNoGlue hValid) v.1 place hwall hplace
      have hAway : old.1.1 ≠ (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) := by
        rw [hOld]
        exact hwall
      have hNd : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne) old =
          nonDanglingValency (Prescribed.validCandidate src hNoGlue hValid).datum v.1 := by
        rw [← hRet, ResolutionAwayFromWall.nonDanglingValency_retainedVertex
          (Prescribed.validCandidate src hNoGlue hValid) hValid
          (NonTrivalentValencyThreeRows.candidate_sourceGenus src hNoGlue hValid) old hAway]
      have hne : old ≠ anchorVertex m wd anchorBlk := by
        intro hBad
        exact hAway (by rw [hBad]; exact anchorVertex_target m wd anchorBlk)
      refine ⟨Sum.inl ⟨⟨old, by rw [hNd]; exact v.2⟩, hne⟩, Subtype.ext ?_⟩
      show candVertex m wd src hNoGlue hValid old = v.1
      rw [candVertex_away m wd src hNoGlue hValid old hAway]
      exact hRet


/-- **The branch vertices of the Type III candidate.** -/
def candBranchEquiv :
    ({w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
        w.1 ≠ anchorVertex m wd anchorBlk} ⊕ Bool) ≃
      BranchVertex (Prescribed.validCandidate src hNoGlue hValid).datum :=
  Equiv.ofBijective (candBranchMap m wd src hNoGlue hValid)
    ⟨candBranchMap_injective m wd src hNoGlue hValid,
      candBranchMap_surjective m wd src hNoGlue hValid⟩

end Candidate

/-! ## 5.  The vertex dictionary of the type change -/

section Vertex

variable {wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}

/-- The two ends of the vanishing occurrence complete the branch vertices of
the incoming cover. -/
def coverBranchMap
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    ({v : BranchVertex wd.cover // v.1 ≠ leftEnd m wd ∧ v.1 ≠ rightEnd m wd} ⊕ Bool) →
      BranchVertex wd.cover
  | Sum.inl v => v.1
  | Sum.inr side => if side then rightBranch m wd wallStar else leftBranch m wd wallStar

/-- The two ends of the vanishing occurrence complete the branch vertices of
the incoming cover. -/
def coverBranchEquiv
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    ({v : BranchVertex wd.cover // v.1 ≠ leftEnd m wd ∧ v.1 ≠ rightEnd m wd} ⊕ Bool) ≃
      BranchVertex wd.cover := by
  classical
  refine Equiv.ofBijective (coverBranchMap m wd wallStar) ⟨?_, ?_⟩
  · rintro (v | side) (v' | side') hEq
    · exact congrArg Sum.inl (Subtype.ext hEq)
    · exfalso
      cases side' with
      | false => exact v.2.1 (congrArg Subtype.val hEq)
      | true => exact v.2.2 (congrArg Subtype.val hEq)
    · exfalso
      cases side with
      | false => exact v'.2.1 (congrArg Subtype.val hEq).symm
      | true => exact v'.2.2 (congrArg Subtype.val hEq).symm
    · cases side <;> cases side' <;> first
        | rfl
        | exact absurd (congrArg Subtype.val hEq) (leftEnd_ne_rightEnd m wd)
        | exact absurd (congrArg Subtype.val hEq) (leftEnd_ne_rightEnd m wd).symm
  · intro u
    by_cases hl : u.1 = leftEnd m wd
    · exact ⟨Sum.inr false, Subtype.ext hl.symm⟩
    · by_cases hr : u.1 = rightEnd m wd
      · exact ⟨Sum.inr true, Subtype.ext hr.symm⟩
      · exact ⟨Sum.inl ⟨u, hl, hr⟩, rfl⟩

/-- **The vertex dictionary of the valency-three type change.**  Away from the
anchor it is the retained (or ordinary-block) vertex of the wall datum, read
back to the incoming cover by the branch dictionary of the wall contraction and
then through the incoming tracking; the two anchor ends `A_u` and `A_v` go to
the two ends of the vanishing occurrence. -/
def vertexEquiv
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid) :
    BranchVertex (Prescribed.validCandidate src hNoGlue hValid).datum ≃ V :=
  ((candBranchEquiv m wd src hNoGlue hValid).symm.trans
    (Equiv.sumCongr (branchEquivAnchorComplement m wd wallStar src).symm
      (Equiv.refl Bool))).trans
    ((coverBranchEquiv m wd wallStar).trans wd.tracks.iso.vtx)

@[simp] theorem vertexEquiv_inl
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
      w.1 ≠ anchorVertex m wd anchorBlk}) :
    vertexEquiv m wd wallStar src hNoGlue hValid
        (candBranchMap m wd src hNoGlue hValid (Sum.inl w)) =
      wd.tracks.iso.vtx ((branchEquivAnchorComplement m wd wallStar src).symm w).1 := by
  have h : (candBranchEquiv m wd src hNoGlue hValid).symm
      (candBranchMap m wd src hNoGlue hValid (Sum.inl w)) = Sum.inl w :=
    (candBranchEquiv m wd src hNoGlue hValid).symm_apply_apply (Sum.inl w)
  show wd.tracks.iso.vtx (coverBranchMap m wd wallStar
    (Equiv.sumCongr (branchEquivAnchorComplement m wd wallStar src).symm (Equiv.refl Bool)
      ((candBranchEquiv m wd src hNoGlue hValid).symm
        (candBranchMap m wd src hNoGlue hValid (Sum.inl w))))) = _
  rw [h]
  rfl

@[simp] theorem vertexEquiv_anchor
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid) (side : Bool) :
    vertexEquiv m wd wallStar src hNoGlue hValid
        (candBranchMap m wd src hNoGlue hValid (Sum.inr side)) =
      wd.tracks.iso.vtx (if side then rightBranch m wd wallStar else leftBranch m wd wallStar) := by
  have h : (candBranchEquiv m wd src hNoGlue hValid).symm
      (candBranchMap m wd src hNoGlue hValid (Sum.inr side)) = Sum.inr side :=
    (candBranchEquiv m wd src hNoGlue hValid).symm_apply_apply (Sum.inr side)
  show wd.tracks.iso.vtx (coverBranchMap m wd wallStar
    (Equiv.sumCongr (branchEquivAnchorComplement m wd wallStar src).symm (Equiv.refl Bool)
      ((candBranchEquiv m wd src hNoGlue hValid).symm
        (candBranchMap m wd src hNoGlue hValid (Sum.inr side))))) = _
  rw [h]
  rfl

end Vertex

/-! ### The orientation prescribed by (H-III) -/

section Orientation

variable {wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}

theorem facetDartLeft_ne_facetDartRight
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    facetDartRight m wd wallStar ≠ facetDartLeft m wd wallStar := by
  intro hBad
  exact (leftEnd_ne_rightEnd m wd)
    (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.1.1) hBad).symm

/-- The two darts of the vanishing occurrence are opposite. -/
theorem opposite_facetDartLeft
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    StableSourceDarts.opposite wd.cover wd.fullDim.connected wd.fullDim.pathEnds
        (facetDartLeft m wd wallStar) = facetDartRight m wd wallStar :=
  (StableSourceDarts.opposite_eq_of_row_eq wd.cover wd.fullDim.connected wd.fullDim.pathEnds
    (d := facetDartLeft m wd wallStar) (e := facetDartRight m wd wallStar) rfl
    (facetDartLeft_ne_facetDartRight m wd wallStar)).symm

/-- **Under (H-III) the `A_u` end of the vanishing occurrence sits at
`graph.vert m.base`.** -/
theorem vert_base_eq
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    graph.vert m.base = wd.tracks.iso.vtx (leftBranch m wd wallStar) := by
  have h := wd.tracks.iso.vert_map (facetDartLeft m wd wallStar)
  rw [hBase] at h
  exact h

/-- **Under (H-III) the `A_v` end sits at `graph.vert (graph.op m.base)`.** -/
theorem vert_opBase_eq
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    graph.vert (graph.op m.base) = wd.tracks.iso.vtx (rightBranch m wd wallStar) := by
  have hOp : graph.op m.base = wd.tracks.iso.dart (facetDartRight m wd wallStar) := by
    have h2 := wd.tracks.iso.op_map (facetDartLeft m wd wallStar)
    have h3 : (StableSourceDarts.ofDatum wd.cover wd.fullDim.connected wd.fullDim.trivalent
        wd.fullDim.pathEnds).op (facetDartLeft m wd wallStar) =
        facetDartRight m wd wallStar := opposite_facetDartLeft m wd wallStar
    rw [hBase, h3] at h2
    exact h2
  rw [hOp]
  exact wd.tracks.iso.vert_map (facetDartRight m wd wallStar)

/-- **`A_u` goes to `graph.vert m.base`.**  This is the anchor half of the
vertex dictionary, in the orientation (H-III) prescribes. -/
theorem vertexEquiv_anchor_false
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    vertexEquiv m wd wallStar src hNoGlue hValid
        (candBranchMap m wd src hNoGlue hValid (Sum.inr false)) = graph.vert m.base := by
  rw [vertexEquiv_anchor m wd wallStar src hNoGlue hValid false,
    vert_base_eq m wd wallStar hBase]
  rfl

/-- **`A_v` goes to `graph.vert (graph.op m.base)`.** -/
theorem vertexEquiv_anchor_true
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    vertexEquiv m wd wallStar src hNoGlue hValid
        (candBranchMap m wd src hNoGlue hValid (Sum.inr true)) =
      graph.vert (graph.op m.base) := by
  rw [vertexEquiv_anchor m wd wallStar src hNoGlue hValid true,
    vert_opBase_eq m wd wallStar hBase]
  rfl


/-! ### Non-vacuity of (H-III) -/

/-- **The geometric content of a type change at a valency-three wall**: the two
doubled-direction survivors of the anchor lift to occurrences at the *two
different* ends of the vanishing occurrence.  Without it `A_u` sees exactly the
star of `leftEnd` and no Whitehead move takes place. -/
def DoubledSeparated
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk) :
    Prop :=
  Incident wd.cover (doubledLift m wd src false).1 (leftEnd m wd) ∧
    Incident wd.cover (doubledLift m wd src true).1 (rightEnd m wd)

theorem facetEdge_ne_doubledLift
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (side : Bool) : (facetEdge m wd).1 ≠ (doubledLift m wd src side).1 := by
  intro hBad
  refine incomingRow_ne_facet wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m)
    (wd.hForest m) wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero
    (NonDanglingEdge.stablePath (if side then
      (⟨(Prescribed.secondDoubled src).1, secondDoubled_survives m wd src⟩ :
        NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
      else ⟨(Prescribed.firstDoubled src).1, firstDoubled_survives m wd src⟩)) ?_
  rw [← stablePath_liftEdge m wd]
  show NonDanglingEdge.stablePath (doubledLift m wd src side) = facetRow m wd
  rw [show doubledLift m wd src side = facetEdge m wd from Subtype.ext hBad.symm]
  exact facetEdge_stablePath m wd

/-- A third surviving occurrence at the `A_u` end, distinct from the vanishing
occurrence and from the doubled-direction survivor there. -/
theorem exists_thirdEdge
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hSep : DoubledSeparated m wd wallStar src) :
    ∃ e : NonDanglingEdge wd.cover, Incident wd.cover e.1 (leftEnd m wd) ∧
      e ≠ facetEdge m wd ∧ e ≠ doubledLift m wd src false := by
  classical
  have hNd : nonDanglingValency wd.cover (leftEnd m wd) = 3 := by
    have h1 := three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_leftEnd m wd)
    have h2 : nonDanglingValency wd.cover (leftEnd m wd) ≤ 3 :=
      wd.fullDim.trivalent (leftEnd m wd)
    omega
  have hNe := facetEdge_ne_doubledLift m wd wallStar src false
  set pair : Finset wd.cover.SourceEdge :=
    {(facetEdge m wd).1, (doubledLift m wd src false).1} with hpair
  have hsub : pair ⊆ nonDanglingIncident wd.cover (leftEnd m wd) := by
    intro e he
    rw [hpair] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨(facetEdge m wd).2, incident_facetEdge_leftEnd m wd⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr ⟨(doubledLift m wd src false).2, hSep.1⟩
  have hcard : (nonDanglingIncident wd.cover (leftEnd m wd) \ pair).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, card_nonDanglingIncident, hNd, hpair,
      Finset.card_pair hNe]
  obtain ⟨e, he⟩ := Finset.card_pos.mp
    (by omega : 0 < (nonDanglingIncident wd.cover (leftEnd m wd) \ pair).card)
  rw [Finset.mem_sdiff, hpair] at he
  obtain ⟨hMem, hNotMem⟩ := he
  obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hNotMem
  exact ⟨⟨e, hSurv⟩, hInc, fun h ↦ hNotMem (Or.inl (congrArg Subtype.val h)),
    fun h ↦ hNotMem (Or.inr (congrArg Subtype.val h))⟩


/-- The third dart at the `A_u` end: neither the vanishing occurrence nor the
doubled-direction survivor there. -/
def thirdEdge
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hSep : DoubledSeparated m wd wallStar src) : NonDanglingEdge wd.cover :=
  Classical.choose (exists_thirdEdge m wd wallStar src hSep)

theorem thirdEdge_spec
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hSep : DoubledSeparated m wd wallStar src) :
    Incident wd.cover (thirdEdge m wd wallStar src hSep).1 (leftEnd m wd) ∧
      thirdEdge m wd wallStar src hSep ≠ facetEdge m wd ∧
      thirdEdge m wd wallStar src hSep ≠ doubledLift m wd src false :=
  Classical.choose_spec (exists_thirdEdge m wd wallStar src hSep)

/-- The dart of the doubled-direction survivor at the `A_u` end. -/
def doubledDartLeft
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hSep : DoubledSeparated m wd wallStar src) : StableSourceDarts.Dart wd.cover :=
  ⟨leftBranch m wd wallStar, ⟨doubledLift m wd src false, hSep.1⟩⟩

/-- The dart of the doubled-direction survivor at the `A_v` end. -/
def doubledDartRight
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hSep : DoubledSeparated m wd wallStar src) : StableSourceDarts.Dart wd.cover :=
  ⟨rightBranch m wd wallStar, ⟨doubledLift m wd src true, hSep.2⟩⟩

/-- The remaining dart at the `A_u` end. -/
def thirdDart
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hSep : DoubledSeparated m wd wallStar src) : StableSourceDarts.Dart wd.cover :=
  ⟨leftBranch m wd wallStar, ⟨thirdEdge m wd wallStar src hSep,
    (thirdEdge_spec m wd wallStar src hSep).1⟩⟩

theorem op_base_eq
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    graph.op m.base = wd.tracks.iso.dart (facetDartRight m wd wallStar) := by
  have h2 := wd.tracks.iso.op_map (facetDartLeft m wd wallStar)
  have h3 : (StableSourceDarts.ofDatum wd.cover wd.fullDim.connected wd.fullDim.trivalent
      wd.fullDim.pathEnds).op (facetDartLeft m wd wallStar) =
      facetDartRight m wd wallStar := opposite_facetDartLeft m wd wallStar
  rw [hBase, h3] at h2
  exact h2

/-- **The Whitehead move prescribed by the two doubled-direction survivors.**
It contracts the edge of `m.base` and exchanges the doubled survivor at the
`A_v` end with the remaining dart at the `A_u` end. -/
def prescribedMove
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hSep : DoubledSeparated m wd wallStar src)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) : graph.MoveData where
  base := m.base
  left := wd.tracks.iso.dart (thirdDart m wd wallStar src hSep)
  right := wd.tracks.iso.dart (doubledDartRight m wd wallStar src hSep)
  nonloop := m.nonloop
  left_vert := (wd.tracks.iso.vert_map (thirdDart m wd wallStar src hSep)).trans
    (vert_base_eq m wd wallStar hBase).symm
  left_ne := by
    intro hBad
    exact (thirdEdge_spec m wd wallStar src hSep).2.1
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1)
        (wd.tracks.iso.dart.injective (hBad.trans hBase.symm)))
  right_vert := (wd.tracks.iso.vert_map (doubledDartRight m wd wallStar src hSep)).trans
    (vert_opBase_eq m wd wallStar hBase).symm
  right_ne := by
    intro hBad
    exact (facetEdge_ne_doubledLift m wd wallStar src true)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1.1)
        (wd.tracks.iso.dart.injective
          (hBad.trans (op_base_eq m wd wallStar hBase)))).symm


/-- **Non-vacuity of (H-III), in relative form.**  At a wall of the outer walk
whose vanishing occurrence is oriented with its `A_u` end at `graph.vert m.base`
and whose two doubled-direction survivors sit at the two different ends, the
Whitehead move `prescribedMove` -- which contracts the *same* edge as `m` --
satisfies (H-III).  This is the precise sense in which (H-III) only normalises
the choice of `left` and `right` in the move: it is the separation
`DoubledSeparated` that is geometric. -/
theorem prescribedDoubledMove_prescribedMove
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hSep : DoubledSeparated m wd wallStar src)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    PrescribedDoubledMove (prescribedMove m wd wallStar src hSep hBase) wd wallStar src := by
  classical
  set m' := prescribedMove m wd wallStar src hSep hBase with hm'
  set dLeft := doubledDartLeft m wd wallStar src hSep with hdLeft
  set dRight := doubledDartRight m wd wallStar src hSep with hdRight
  have hLeftNeRight : dLeft ≠ dRight := by
    intro hBad
    exact (leftEnd_ne_rightEnd m wd)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.1.1) hBad)
  have hLeftNeThird : dLeft ≠ thirdDart m wd wallStar src hSep := by
    intro hBad
    exact (thirdEdge_spec m wd wallStar src hSep).2.2
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1) hBad).symm
  have hBaseNeLeft : m.base ≠ wd.tracks.iso.dart dLeft := by
    intro hBad
    exact (facetEdge_ne_doubledLift m wd wallStar src false)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1.1)
        (wd.tracks.iso.dart.injective (hBase.trans hBad)))
  have hBaseNeRight : m.base ≠ wd.tracks.iso.dart dRight := by
    intro hBad
    exact (facetEdge_ne_doubledLift m wd wallStar src true)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1.1)
        (wd.tracks.iso.dart.injective (hBase.trans hBad)))
  refine ⟨hBase, dLeft, dRight, rfl, rfl, ?_⟩
  have hStar : (Finset.univ.filter fun d ↦ (graph.move m').vert d = graph.vert m.base) =
      {m.base, wd.tracks.iso.dart dRight, wd.tracks.iso.dart dLeft} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases hd with rfl | rfl | rfl
      · exact congrArg graph.vert m'.perm_base
      · exact (congrArg graph.vert m'.perm_right).trans m'.left_vert
      · have h1 : wd.tracks.iso.dart dLeft ≠ m'.left :=
          fun hBad ↦ hLeftNeThird (wd.tracks.iso.dart.injective hBad)
        have h2 : wd.tracks.iso.dart dLeft ≠ m'.right :=
          fun hBad ↦ hLeftNeRight (wd.tracks.iso.dart.injective hBad)
        show graph.vert (m'.perm (wd.tracks.iso.dart dLeft)) = graph.vert m.base
        rw [m'.perm_of_ne h1 h2, wd.tracks.iso.vert_map dLeft, vert_base_eq m wd wallStar hBase]
        rfl
    · rw [(graph.move m').card_fibre (graph.vert m.base)]
      exact le_of_eq (Finset.card_eq_three.mpr ⟨_, _, _, hBaseNeRight, hBaseNeLeft,
        fun hBad ↦ hLeftNeRight (wd.tracks.iso.dart.injective hBad).symm, rfl⟩).symm
  show (Finset.univ.filter fun d ↦ (graph.move m').vert d = graph.vert m.base).erase m.base =
    {wd.tracks.iso.dart dLeft, wd.tracks.iso.dart dRight}
  rw [hStar, Finset.erase_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact not_or.mpr ⟨hBaseNeRight, hBaseNeLeft⟩), Finset.pair_comm]

end Orientation

/-! ## 6.  Three pieces of the star count -/

/-- **Away from the two ends of the vanishing occurrence the Whitehead move
does not change the star.**  The permutation `m.perm` is the transposition of
`m.left` and `m.right`, whose vertices are the two ends themselves. -/
theorem move_vert_eq_iff_of_ne {x : V} (hBase : x ≠ graph.vert m.base)
    (hOpBase : x ≠ graph.vert (graph.op m.base)) (d : D) :
    (graph.move m).vert d = x ↔ graph.vert d = x := by
  classical
  by_cases hl : d = m.left
  · subst hl
    constructor
    · intro hBad
      exact absurd ((congrArg graph.vert m.perm_left).symm.trans hBad).symm
        (fun h ↦ hOpBase (h.trans m.right_vert))
    · intro hBad
      exact absurd hBad.symm (fun h ↦ hBase (h.trans m.left_vert))
  · by_cases hr : d = m.right
    · subst hr
      constructor
      · intro hBad
        exact absurd ((congrArg graph.vert m.perm_right).symm.trans hBad).symm
          (fun h ↦ hBase (h.trans m.left_vert))
      · intro hBad
        exact absurd hBad.symm (fun h ↦ hOpBase (h.trans m.right_vert))
    · show graph.vert (m.perm d) = x ↔ _
      rw [m.perm_of_ne hl hr]

/-- **The star of a branch vertex of the incoming cover, counted in the tracked
ambient graph.**  This is `MovedIncidenceIso.DatumGraphIncidence.ofIso` applied
to the incoming tracking, with the row label read through the chart. -/
theorem card_star_eq_incidenceCount (u : BranchVertex wd.cover)
    (row : StablePath wd.cover) :
    incidenceCount wd.cover u.1 row =
      Nat.card {d : D // graph.vert d = wd.tracks.iso.vtx u ∧
        label d = wd.fullDim.labelling.row row} := by
  classical
  have hDict := (MovedIncidenceIso.DatumGraphIncidence.ofIso wd.cover wd.fullDim.connected
    wd.fullDim.trivalent wd.fullDim.pathEnds wd.tracks.iso).incidence u row
  refine hDict.trans (Nat.card_congr (Equiv.subtypeEquivRight fun d ↦ ?_))
  have hLabel : label d = wd.fullDim.labelling.row
      (StableSourceDarts.row wd.cover (wd.tracks.iso.dart.symm d)) := by
    have h := wd.tracks.row_map (wd.tracks.iso.dart.symm d)
    rwa [Equiv.apply_symm_apply] at h
  constructor
  · rintro ⟨hv, hr⟩
    refine ⟨hv, ?_⟩
    rw [hLabel]
    exact congrArg wd.fullDim.labelling.row hr
  · rintro ⟨hv, hr⟩
    refine ⟨hv, ?_⟩
    show StableSourceDarts.row wd.cover (wd.tracks.iso.dart.symm d) = row
    refine wd.fullDim.labelling.row.injective ?_
    rw [← hLabel, hr]

section Retained

variable {wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
  (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)

/-- **The retained-row map is injective**, from the row dictionary of
`NonTrivalentValencyThreeRowEquiv`. -/
theorem injective_retainedRow :
    Function.Injective (NonTrivalentValencyThreeDescent.retainedRow src hNoGlue hValid) := by
  intro r r' h
  have h2 := congrArg (NonTrivalentValencyThreeRowEquiv.rowEquiv src hNoGlue hValid) h
  rw [NonTrivalentValencyThreeRowEquiv.rowEquiv_retainedRow src hNoGlue hValid r,
    NonTrivalentValencyThreeRowEquiv.rowEquiv_retainedRow src hNoGlue hValid r'] at h2
  exact Option.some_injective _ h2

/-- **Away from the merged target vertex the candidate does not change the
star.**  This is `ResolutionStableIncidence.incidenceCount_retainedVertex` with
its row *equivalence* hypothesis weakened to injectivity of the retained-row
map, which is what `NonTrivalentValencyThreeDescent.retainedRow` supplies (its
complement is the bridge row).  The proof uses the equivalence only through
`row.injective`. -/
theorem incidenceCount_retainedVertex_retainedRow
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hAway : w.1.1 ≠ (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b))
    (row : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) w row =
      incidenceCount (Prescribed.validCandidate src hNoGlue hValid).datum
        (ResolutionAwayFromWall.retainedVertex
          (Prescribed.validCandidate src hNoGlue hValid) w)
        (NonTrivalentValencyThreeDescent.retainedRow src hNoGlue hValid row) := by
  classical
  unfold incidenceCount
  apply Finset.card_bij (fun edge _ ↦ ResolutionAwayFromWall.retainedEdge
    (Prescribed.validCandidate src hNoGlue hValid) hValid.1 edge)
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge ⊢
    refine ⟨(ResolutionAwayFromWall.incident_oldSourceEdge_iff
      (Prescribed.validCandidate src hNoGlue hValid) w hAway edge.1).mpr hEdge.1, ?_⟩
    rw [← NonTrivalentValencyThreeDescent.retainedRow_mk src hNoGlue hValid edge, hEdge.2]
  · intro first _ second _ hEq
    exact ResolutionAwayFromWall.retainedEdge_injective
      (Prescribed.validCandidate src hNoGlue hValid) hValid.1 hEq
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge
    have hMem : edge.1 ∈ nonDanglingIncident (Prescribed.validCandidate src hNoGlue hValid).datum
        (ResolutionAwayFromWall.retainedVertex
          (Prescribed.validCandidate src hNoGlue hValid) w) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hEdge.1⟩
    rw [ResolutionAwayFromWall.nonDanglingIncident_retainedVertex
      (Prescribed.validCandidate src hNoGlue hValid) hValid
      (NonTrivalentValencyThreeRows.candidate_sourceGenus src hNoGlue hValid) w hAway] at hMem
    obtain ⟨old, hOld, hEqual⟩ := Finset.mem_image.mp hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOld
    refine ⟨⟨old, hSurvives⟩, ?_, Subtype.ext hEqual⟩
    refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hIncident,
      injective_retainedRow m wd src hNoGlue hValid ?_⟩
    rw [NonTrivalentValencyThreeDescent.retainedRow_mk src hNoGlue hValid
      (⟨old, hSurvives⟩ : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)),
      show ResolutionAwayFromWall.retainedEdge (Prescribed.validCandidate src hNoGlue hValid)
        hValid.1 ⟨old, hSurvives⟩ = edge from Subtype.ext hEqual]
    exact hEdge.2

end Retained

/-! ## 7.  The link, reduced to the star count -/

section Link

variable {wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
  (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)

/-- **`OuterWalk.TypeChangeLink` at a three-valent wall, from the star count
alone.**  `NonTrivalentValencyThreeExit.typeChangeLink_of_receipts` has two
hypotheses, `hPathEnds` and `tracks`; `NonTrivalentValencyThreePathEnds`
discharges the first, and `MovedIncidenceIso` reduces `tracks` to a
branch-vertex bijection and a star count against the permuted vertex map.  With
`vertexEquiv` supplying the bijection, exactly one geometric hypothesis is
left: the star count `hIncidence`.  At a branch vertex away from the anchor it
is the composite of the two transports (T1) and (T2) of the module docstring,
and at `A_u`/`A_v` it is what (H-III) prescribes together with the exact
anchor stars of `NonTrivalentValencyThreeRows`. -/
def typeChangeLink_of_incidence
    (hIncidence : ∀ (v : BranchVertex (Prescribed.validCandidate src hNoGlue hValid).datum)
        (r : StablePath (Prescribed.validCandidate src hNoGlue hValid).datum),
      incidenceCount (Prescribed.validCandidate src hNoGlue hValid).datum v.1 r =
        Nat.card {d : D // graph.vert (m.perm d) =
            vertexEquiv m wd wallStar src hNoGlue hValid v ∧
          label d = (NonTrivalentValencyThreeExit.wallOutgoingFD m wd src hNoGlue hValid
            (NonTrivalentValencyThreePathEnds.hasPathEnds_wallData m wd src hNoGlue
              hValid)).labelling.row r}) :
    TypeChangeLink m wd :=
  NonTrivalentValencyThreePathEnds.typeChangeLink_of_receipts' m wd src hNoGlue hValid
    (MovedIncidenceIso.tracksOfMovedIncidence _ _ graph m label
      (vertexEquiv m wd wallStar src hNoGlue hValid)
      (MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks) hIncidence)

end Link

end Anchor

end

end DraismaVargas.LocalCases.NonTrivalentValencyThreeTracks
