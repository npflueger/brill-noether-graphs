import DraismaVargas.LocalCases.LeafFacetNoReturn
import DraismaVargas.LocalCases.NonTrivalentValencyThreeDescent
import DraismaVargas.LocalCases.NonTrivalentValencyTwoExit

/-!
# `HasPathEnds` of the wall datum, and its transport to the Part II candidates

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1: the labelling
convention (1) (apart from `h_1^(q)`, the edges of `H^(q)` correspond
bijectively to those of `H_0`) and `lemma-above-w0` (rigidity above `w_0`),
together with Section 5.4 (Case {v2-nd4}, base tree `T_2` = Base II) and
Section 5.3 (Case {v3-nd4}, Type III); Draisma--Vargas Part I
(arXiv:1909.12924): the stable graph of a gluing datum and the source/row
isomorphisms of the subsection on inherited properties.

`NonTrivalentValencyTwoExit` assembles the outgoing
`FullDimensionalSourcePresentation` at a two-valent wall with exactly one
geometric field left open,
`pathEnds : HasPathEnds (Prescribed.validCandidate sel).datum`, and reduces it
by `hasPathEnds_of_retainedRowEnds` to *every retained row of the candidate has
a path end*.  That reduction needs `HasPathEnds` of the **wall datum**
`contractDatum cover hc hab hOne`, which the usual producers of `HasPathEnds`
do not supply: every one of them goes through
`StableGraphIncidence.Equivalence`, and across a type
change no stable-graph equivalence exists (the four-valent anchor is one branch
vertex downstairs and two trivalent ones upstairs).  This module proves the wall
datum's `HasPathEnds` directly and transports it.

## The two ingredients

1. **A stable row entering a contracted fibre leaves it**
   (`exists_retained_incident_fibre`).  Stated for an arbitrary datum and an
   arbitrary contracted target occurrence: if a surviving occurrence `f` over
   `t_1` lies on a stable row that has *some* occurrence away from `t_1`, then
   that row already has such an occurrence incident to a source vertex of `f`'s
   own fibre.  The proof is the chain invariant `FibreAnchored`, the fibre-local
   analogue of `StablePathFacetContraction.Anchored`: walking along the row from
   `f`, every contracted step stays in the same fibre
   (`sourceVertexMap_eq_of_incident_contracted`), so the first retained step is
   attached to that fibre.  No forest, dangling-compatibility or
   full-dimensionality receipt enters.

2. **The pruned-fibre valency statement**
   (`PrunedFibreTree.nonDanglingValency_eq_two_of_sourceVertexMap_eq`): if the
   merged vertex is divalent then every active constituent of its fibre is
   divalent.  This is what makes a path end survive the contraction: an incoming
   end `(f, V)` has `nd(V) != 2`, hence `nd_W(sourceVertexMap V) != 2`.

Together: given a surviving wall occurrence `g`, apply the incoming
`fd.pathEnds` to `nonDanglingEmbedding g`.  If the resulting end occurrence is
retained, descend it; if it lies over `t_1`, ingredient 1 replaces it by a
retained occurrence of the same row incident to the same fibre.  Either way the
merged vertex is the end.  The occurrence still lies on `g`'s wall row by
`LeafFacetNoReturn.stablePath_descend_eq_iff'`.

## What is proved

* `exists_retained_incident_fibre`, `FibreAnchored`, `fibreAnchored_contracted`,
  `fibreAnchored_of_consecutive`: ingredient 1, stated generally, since the
  valency-three and valency-four exits need the same fact.
* `hasPathEnds_contractDatum_offRow`, `hasPathEnds_contractDatum`: **`HasPathEnds`
  of the wall datum** at a Part II one-zero-row facet, from
  `LeafFacetNoReturn.NoContractedReturnOffRow` -- the weakened no-return
  condition, which unlike `StablePathFacetContraction.NoContractedReturn` is
  *true* in the `1 + 3` sub-case of a two-valent wall.
  `hasPathEnds_contractDatum_of_noContractedReturn` is the version taking the
  strong condition.  The metric receipt `hRows` is **not** used.
* `Two.exists_isPathEnd_anchor`, `Two.exists_isPathEnd_ordinary`,
  `Two.exists_isPathEnd_of_wall_end`: a path end of the wall datum transports to
  a path end of the outgoing Base II candidate, on the retained row of the same
  occurrence.  Away from the wall `ResolutionAwayFromWall` keeps the valency; at
  an ordinary block the census of `NonTrivalentValencyTwoDescent` gives
  `nd(B_s) = |star_s(B)| + [new survives]`, and the only bad case
  (`|star_s(B)| = 1` with the new occurrence surviving) is repaired by
  `stablePath_retainedEdge_eq_newSourceEdge`, which moves the end to the other
  side, whose valency is `nd(B)` itself; at the anchor a thin survivor meets the
  trivalent `A_v`, the two selected thick survivors meet the trivalent `A_u`,
  and a third thick survivor reaches `A_v` through
  `newSourceEdge_stablePath_eq_retained`.
* `hasPathEnds_candidate`: **`HasPathEnds` of the outgoing valency-two Base II
  candidate**, discharging the last geometric field of
  `NonTrivalentValencyTwoExit.outgoingFD`.
* `hasPathEnds_wallData` and `typeChangeLink_of_receipts'`: the same at the wall
  data of the outer walk, and `NonTrivalentValencyTwoExit.typeChangeLink_of_receipts`
  with its `hPathEnds` hypothesis removed.
* `Three.exists_isPathEnd_anchor`, `Three.exists_isPathEnd_ordinary`,
  `Three.exists_isPathEnd_of_wall_end`: the same transport at a three-valent
  wall, for the valency-three exit.  It is shorter: `nd(B_v) = nd(B)` at an ordinary block and
  `exists_trivalentEndEdge` already carries every survivor to `B_v`, while both
  anchor classes are trivalent.

## What is NOT proved -- the hypotheses that remain explicit

1. `hNoReturn`.  The wall datum's `HasPathEnds` is proved from
   `LeafFacetNoReturn.NoContractedReturnOffRow data contracted
   (fd.labelling.row.symm facet)`, not unconditionally.  It is discharged at a
   `2 + 2` two-valent wall and at every three- or four-valent wall by
   `StablePathFacetContraction.noContractedReturn_of_nonleaf`, and in the
   `1 + 3` sub-case by `LeafFacetNoReturn.noReturn_off_facet`.
   `typeChangeLink_of_receipts'` below takes the strong
   `StablePathFacetContraction.NoContractedReturn` that
   `NonTrivalentValencyTwoExit.typeChangeLink_of_receipts` takes;
   `NonTrivalentValencyTwoExitFree` removes it.
2. `tracks`.  `typeChangeLink_of_receipts'` carries the
   `InteriorGraphTracking.Tracks` hypothesis of `NonTrivalentValencyTwoExit`;
   only `hPathEnds` is removed.
3. The valency-three statements are the *transport*: the analogue of
   `NonTrivalentValencyTwoExit.hasPathEnds_of_retainedRowEnds` at a three-valent
   wall (the row equivalence of `NonTrivalentValencyThreeRowEquiv` read as a
   reduction to the retained rows) belongs to the valency-three exit
   (`NonTrivalentValencyThreeExit`, `NonTrivalentValencyThreePathEnds`), and is
   not built here.

`FibreAnchored` is a predicate, not a structure; `fibreAnchored_contracted`
inhabits it at every surviving occurrence over the contracted target
occurrence, and `exists_retained_incident_fibre` is the statement it serves.

## Consumers

`NonTrivalentValencyTwoExit.outgoingFD` / `.typeChangeLink_of_receipts` (hence
`OuterWalk.TypeChangeLink` at Part II, Case {v2-nd4}), and the valency-three
exit at Case {v3-nd4} (`NonTrivalentValencyThreePathEnds`).
-/

namespace DraismaVargas.LocalCases.WallDatumPathEnds

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.WallDegeneration

variable {target : CFGraph} {degree : ℕ}

section Exit

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

/-- All source vertices incident to one occurrence over the contracted target
occurrence lie in one and the same fibre. -/
theorem sourceVertexMap_eq_of_incident_contracted
    {e : data.SourceEdge} (he : e.1.1 = contracted) {v w : data.SourceVertex}
    (hv : Incident data e v) (hw : Incident data e w) :
    sourceVertexMap data hc hab hOne v = sourceVertexMap data hc hab hOne w := by
  have hEq := sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne e he
  rcases hv with hv | hv <;> rcases hw with hw | hw <;> rw [← hv, ← hw]
  · exact hEq
  · exact hEq.symm

/-- The invariant carried along the stable row while it is still inside the
fibre over the contracted target occurrence. -/
def FibreAnchored (row : StablePath data) (u : data.SourceVertex)
    (z : NonDanglingEdge data) : Prop :=
  z.stablePath = row →
    ((z.1.1.1 = contracted ∧ ∀ v : data.SourceVertex, Incident data z.1 v →
        sourceVertexMap data hc hab hOne v = sourceVertexMap data hc hab hOne u) ∨
      ∃ (y : NonDanglingEdge data) (v : data.SourceVertex),
        y.stablePath = row ∧ y.1.1.1 ≠ contracted ∧ Incident data y.1 v ∧
          sourceVertexMap data hc hab hOne v = sourceVertexMap data hc hab hOne u)

/-- Non-vacuity of the invariant: an occurrence over the contracted target
occurrence is anchored at its own fibre. -/
theorem fibreAnchored_contracted (row : StablePath data)
    {f : NonDanglingEdge data} (hf : f.1.1.1 = contracted)
    {u : data.SourceVertex} (hu : Incident data f.1 u) :
    FibreAnchored data hc hab hOne row u f :=
  fun _ ↦ Or.inl ⟨hf, fun _ hv ↦
    sourceVertexMap_eq_of_incident_contracted data hc hab hOne hf hv hu⟩

/-- The invariant is closed under stable adjacency. -/
theorem fibreAnchored_of_consecutive (row : StablePath data) (u : data.SourceVertex)
    (first second : NonDanglingEdge data) (hCons : Consecutive data first second)
    (hFirst : FibreAnchored data hc hab hOne row u first) :
    FibreAnchored data hc hab hOne row u second := by
  intro hSecondRow
  have hFirstRow : first.stablePath = row :=
    (stablePath_eq_of_consecutive hCons).trans hSecondRow
  rcases hFirst hFirstRow with ⟨hT, hFibre⟩ | hGoal
  · obtain ⟨-, meeting, hIncFirst, hIncSecond, -⟩ := hCons
    have hMeet := hFibre meeting hIncFirst
    by_cases hSecondT : second.1.1.1 = contracted
    · refine Or.inl ⟨hSecondT, fun v hv ↦ ?_⟩
      exact (sourceVertexMap_eq_of_incident_contracted data hc hab hOne hSecondT hv
        hIncSecond).trans hMeet
    · exact Or.inr ⟨second, meeting, hSecondRow, hSecondT, hIncSecond, hMeet⟩
  · exact Or.inr hGoal

/-- **A stable row entering a contracted fibre leaves it.**  If a surviving
occurrence `f` over the contracted target occurrence lies on a stable row that
has at least one occurrence away from the contracted target occurrence, then
that row already has such an occurrence incident to the very fibre of `f`.

No forest, dangling-compatibility or full-dimensionality receipt is used: the
statement is the chain invariant of `StablePathFacetContraction.Anchored` run
inside a single fibre.  The valency-two, valency-three and valency-four exits
all consume it. -/
theorem exists_retained_incident_fibre
    {f : NonDanglingEdge data} (hf : f.1.1.1 = contracted)
    {u : data.SourceVertex} (hu : Incident data f.1 u)
    {x : NonDanglingEdge data} (hx : x.1.1.1 ≠ contracted)
    (hRow : x.stablePath = f.stablePath) :
    ∃ (y : NonDanglingEdge data) (v : data.SourceVertex),
      y.stablePath = f.stablePath ∧ y.1.1.1 ≠ contracted ∧ Incident data y.1 v ∧
        sourceVertexMap data hc hab hOne v = sourceVertexMap data hc hab hOne u := by
  have hTransfer := eqvGen_iff_of_closed
    (property := FibreAnchored data hc hab hOne f.stablePath u)
    (fibreAnchored_of_consecutive data hc hab hOne f.stablePath u)
    ((stablePath_eq_iff f x).mp hRow.symm)
  rcases hTransfer.mp (fibreAnchored_contracted data hc hab hOne f.stablePath hf hu) hRow with
    ⟨hT, -⟩ | hGoal
  · exact absurd hT hx
  · exact hGoal

end Exit


/-! ## 2.  `HasPathEnds` of the wall datum -/

section WallEnds

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hCompat : DanglingCompatible data hc hab hOne)
  (hForest : ContractionForest data a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hNoReturn : LeafFacetNoReturn.NoContractedReturnOffRow data contracted
    (fd.labelling.row.symm facet))
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)

include fd hCompat hForest hNoReturn hZeroCoord hPosCoord hFacetZero in
/-- **`HasPathEnds` of the wall datum, from the weakened no-return
condition.** -/
theorem hasPathEnds_contractDatum_offRow :
    HasPathEnds (contractDatum data hc hab hOne) := by
  classical
  intro g
  have hERet : (nonDanglingEmbedding data hCompat.1 g).1.1.1 ≠ contracted :=
    sourceEdgeEmbedding_ne_contracted data hc hab hOne g.1
  obtain ⟨f, V, hfRow, hfInc, hfNd⟩ := fd.pathEnds (nonDanglingEmbedding data hCompat.1 g)
  obtain ⟨y, v, hyRow, hyRet, hyInc, hvMap⟩ :
      ∃ (y : NonDanglingEdge data) (v : data.SourceVertex),
        y.stablePath = (nonDanglingEmbedding data hCompat.1 g).stablePath ∧
          y.1.1.1 ≠ contracted ∧ Incident data y.1 v ∧
            sourceVertexMap data hc hab hOne v = sourceVertexMap data hc hab hOne V := by
    by_cases hfT : f.1.1.1 = contracted
    · obtain ⟨y, v, hRow, hRet, hInc, hMap⟩ := exists_retained_incident_fibre data hc hab hOne
        hfT hfInc hERet hfRow.symm
      exact ⟨y, v, hRow.trans hfRow, hRet, hInc, hMap⟩
    · exact ⟨f, V, hfRow, hfT, hfInc, rfl⟩
  refine ⟨descend data hc hab hOne hCompat y hyRet,
    sourceVertexMap data hc hab hOne v, ?_, ?_, ?_⟩
  · refine (LeafFacetNoReturn.stablePath_descend_eq_iff' data fd hc hab hOne hCompat hForest
      coordinates facet hNoReturn hZeroCoord hPosCoord hFacetZero y hyRet g.stablePath).mpr ?_
    rw [incomingRow_mk]
    exact hyRow
  · exact incident_descend data hc hab hOne hCompat hyRet hyInc
  · intro hTwo
    refine hfNd (PrunedFibreTree.nonDanglingValency_eq_two_of_sourceVertexMap_eq data hc hab hOne
      fd.connected hCompat hForest _ hTwo V hvMap.symm ?_)
    exact ClassInjectivity.nonDanglingValency_ne_zero_of_incident data f.2 hfInc

include fd hForest hNoReturn hZeroCoord hPosCoord hFacetZero in
/-- **`HasPathEnds` of the wall datum at a Part II one-zero-row facet.** -/
theorem hasPathEnds_contractDatum :
    HasPathEnds (contractDatum data hc hab hOne) :=
  hasPathEnds_contractDatum_offRow data fd hc hab hOne
    (WallAdmissibility.danglingCompatible_of_contractionForest data hc hab hOne hForest)
    hForest coordinates facet hNoReturn hZeroCoord hPosCoord hFacetZero

include fd hForest hZeroCoord hPosCoord hFacetZero in
/-- The same statement under the strong no-return condition. -/
theorem hasPathEnds_contractDatum_of_noContractedReturn
    (hStrong : NoContractedReturn data contracted) :
    HasPathEnds (contractDatum data hc hab hOne) :=
  hasPathEnds_contractDatum data fd hc hab hOne hForest coordinates facet
    (LeafFacetNoReturn.noContractedReturnOffRow_of_noContractedReturn data contracted
      (fd.labelling.row.symm facet) hStrong)
    hZeroCoord hPosCoord hFacetZero

end WallEnds

/-! ## 3.  Transport to the valency-two candidate -/

namespace Two

open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.W3R1SourceProfile
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRows

noncomputable section

variable {wall : target.V} {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall}
  (source : TwoBranchAnchor data star anchor)
  (sel : Prescribed.Selection data star anchor) (hValid : data.Valid)

theorem direction_cases (label : Fin 2) :
    label = Prescribed.thickDirection data star anchor ∨
      label = Prescribed.thinDirection data star anchor := by
  have hThin : Prescribed.thinDirection data star anchor =
      Prescribed.thickDirection data star anchor + 1 := rfl
  rw [hThin]
  rcases NonTrivalentValencyTwoAnchor.eq_zero_or_one label with hl | hl <;>
    rcases NonTrivalentValencyTwoAnchor.eq_zero_or_one
      (Prescribed.thickDirection data star anchor) with ht | ht <;>
    rw [hl, ht] <;> decide

include source in
/-- **The anchor half of the transport.**  A surviving occurrence at the anchor
block of the wall datum keeps a path end on its own retained row of the
candidate: a thin survivor meets the trivalent `A_v`, the two selected thick
survivors meet the trivalent `A_u`, and a third thick survivor reaches `A_v`
along the second new occurrence, which sits on its own retained row. -/
theorem exists_isPathEnd_anchor
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hSurv : ¬ IsDangling data edge.1) :
    ∃ (first : NonDanglingEdge (Prescribed.validCandidate sel).datum)
      (vertex : (Prescribed.validCandidate sel).datum.SourceVertex),
      first.stablePath = (ResolutionAwayFromWall.retainedEdge (Prescribed.validCandidate sel)
          hValid.1 ⟨edge.1, hSurv⟩).stablePath ∧
        IsPathEnd (Prescribed.validCandidate sel).datum first.1 vertex := by
  classical
  have hLabel : edge ∈ directionSurvivors data star anchor
      (survivorLabel data star anchor edge) :=
    (mem_directionSurvivors data star anchor _ edge).mpr
      ⟨(mem_survivors data anchor edge).mpr hSurv,
        (edge_survivorLabel data star anchor edge).symm⟩
  rcases direction_cases (data := data) (star := star) (anchor := anchor)
    (survivorLabel data star anchor edge) with hDir | hDir
  · -- a thick survivor
    rw [hDir] at hLabel
    by_cases hFirst : edge = Prescribed.firstSelected sel
    · refine ⟨ResolutionAwayFromWall.retainedEdge _ hValid.1 ⟨edge.1, hSurv⟩,
        endpointVertex sel false (Prescribed.selectedRepresentative sel), rfl, ?_, ?_⟩
      · subst hFirst
        exact retained_survivor_incident sel false hLabel
          rightAssignment_thickDirection (rep_wall_rel sel) rfl
      · rw [nonDanglingValency_endpointVertex_false source sel hValid]
        omega
    · by_cases hSecond : edge = Prescribed.secondSelected sel
      · refine ⟨ResolutionAwayFromWall.retainedEdge _ hValid.1 ⟨edge.1, hSurv⟩,
          endpointVertex sel false (Prescribed.selectedRepresentative sel), rfl, ?_, ?_⟩
        · subst hSecond
          exact retained_survivor_incident sel false hLabel
            rightAssignment_thickDirection (rep_wall_rel sel)
            (finePartition_rel_second sel)
        · rw [nonDanglingValency_endpointVertex_false source sel hValid]
          omega
      · have hRetained : edge ∈ retainedThick sel :=
          Finset.mem_erase.mpr ⟨hSecond, hLabel⟩
        refine ⟨⟨(Prescribed.validCandidate sel).newSourceEdge (occurrenceSheet edge),
          newSourceEdge_survives source sel hValid hLabel⟩,
          endpointVertex sel true (occurrenceSheet edge), ?_, ?_, ?_⟩
        · exact newSourceEdge_stablePath_eq_retained source sel hValid hRetained hFirst
        · exact bridgeEdge_incident sel true (occurrenceSheet edge)
        · rw [← endpointVertex_eq sel true (rep_wall_rel sel)
            ((rep_wall_rel sel).symm.trans (occurrenceSheet_wall_rel edge)),
            nonDanglingValency_endpointVertex_true source sel hValid]
          omega
  · -- a thin survivor
    rw [hDir] at hLabel
    refine ⟨ResolutionAwayFromWall.retainedEdge _ hValid.1 ⟨edge.1, hSurv⟩,
      endpointVertex sel true (Prescribed.selectedRepresentative sel), rfl, ?_, ?_⟩
    · exact retained_survivor_incident sel true hLabel rightAssignment_thinDirection
        (rep_wall_rel sel)
        ((rep_wall_rel sel).symm.trans (occurrenceSheet_wall_rel edge))
    · rw [nonDanglingValency_endpointVertex_true source sel hValid]
      omega

/-- **The ordinary-block half of the transport.**  At a wall block other than
the anchor the candidate installs the neutral resolution, so the census of
`NonTrivalentValencyTwoDescent` applies: the retained copy of a survivor keeps
the block's surviving valency on its own side unless that side carries exactly
one survivor and the block's new occurrence survives, and then the new
occurrence -- which lies on the same stable row -- meets the other side, whose
surviving valency is the block's own. -/
theorem exists_isPathEnd_ordinary
    {h : NonDanglingEdge data} {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hInc : Incident data h.1 (data.sourceEndpoint wall x))
    (hNd : nonDanglingValency data (data.sourceEndpoint wall x) ≠ 2) :
    ∃ (first : NonDanglingEdge (Prescribed.validCandidate sel).datum)
      (vertex : (Prescribed.validCandidate sel).datum.SourceVertex),
      first.stablePath = (ResolutionAwayFromWall.retainedEdge (Prescribed.validCandidate sel)
          hValid.1 h).stablePath ∧
        IsPathEnd (Prescribed.validCandidate sel).datum first.1 vertex := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Bool,
      Prescribed.rightAssignment data star anchor h.1.1.1 = s := ⟨_, rfl⟩
  have hOld : h.1 ∈ NonTrivalentValencyTwoDescent.ordinaryStar data star anchor x s := by
    rw [NonTrivalentValencyTwoDescent.mem_ordinaryStar]
    exact ⟨⟨h.2, hInc⟩, hs⟩
  have hSum := NonTrivalentValencyTwoDescent.card_ordinaryStar_add
    (data := data) (star := star) (anchor := anchor) x
  have hFlip : (NonTrivalentValencyTwoDescent.ordinaryStar data star anchor x s).card +
      (NonTrivalentValencyTwoDescent.ordinaryStar data star anchor x (!s)).card =
        nonDanglingValency data (data.sourceEndpoint wall x) := by
    cases s
    · exact hSum
    · rw [Nat.add_comm]; exact hSum
  have hPos : (NonTrivalentValencyTwoDescent.ordinaryStar data star anchor x s).card ≠ 0 :=
    Finset.card_ne_zero_of_mem hOld
  by_cases hDang : IsDangling (Prescribed.validCandidate sel).datum
      ((Prescribed.validCandidate sel).newSourceEdge x)
  · have hOther :
        (NonTrivalentValencyTwoDescent.ordinaryStar data star anchor x (!s)).card = 0 := by
      by_contra hBad
      refine ((NonTrivalentValencyTwoDescent.newSourceEdge_survives_iff_ordinary
        sel hValid hX).mpr ?_) hDang
      cases s
      · exact ⟨hPos, hBad⟩
      · exact ⟨hBad, hPos⟩
    refine ⟨ResolutionAwayFromWall.retainedEdge (Prescribed.validCandidate sel) hValid.1 h,
      endpointVertex sel s x, rfl, ?_, ?_⟩
    · exact NonTrivalentValencyTwoDescent.incident_retainedEdge_endpointVertex sel hValid
        s hX hOld
    · rw [NonTrivalentValencyTwoDescent.nonDanglingValency_endpointVertex_of_new_dangling
        sel hValid s hX hDang]
      omega
  · by_cases hCard : (NonTrivalentValencyTwoDescent.ordinaryStar data star anchor x s).card = 1
    · refine ⟨⟨(Prescribed.validCandidate sel).newSourceEdge x, hDang⟩,
        endpointVertex sel (!s) x, ?_, ?_, ?_⟩
      · exact (NonTrivalentValencyTwoDescent.stablePath_retainedEdge_eq_newSourceEdge
          sel hValid s hX hOld hCard hDang).symm
      · exact NonTrivalentValencyTwoDescent.newSourceEdge_incident_endpointVertex sel (!s) x
      · rw [NonTrivalentValencyTwoDescent.nonDanglingValency_endpointVertex_of_new_survives
          sel hValid (!s) hX hDang]
        omega
    · refine ⟨ResolutionAwayFromWall.retainedEdge (Prescribed.validCandidate sel) hValid.1 h,
        endpointVertex sel s x, rfl, ?_, ?_⟩
      · exact NonTrivalentValencyTwoDescent.incident_retainedEdge_endpointVertex sel hValid
          s hX hOld
      · rw [NonTrivalentValencyTwoDescent.nonDanglingValency_endpointVertex_of_new_survives
          sel hValid s hX hDang]
        omega

include source in
/-- **A path end of the wall datum transports to a path end of the outgoing
candidate, on the retained row of the same occurrence.**  Away from the wall the
retained vertex has the same surviving valency; at an ordinary block and at the
anchor the two halves above apply. -/
theorem exists_isPathEnd_of_wall_end
    {h : NonDanglingEdge data} {w : data.SourceVertex}
    (hInc : Incident data h.1 w) (hNd : nonDanglingValency data w ≠ 2) :
    ∃ (first : NonDanglingEdge (Prescribed.validCandidate sel).datum)
      (vertex : (Prescribed.validCandidate sel).datum.SourceVertex),
      first.stablePath = (ResolutionAwayFromWall.retainedEdge (Prescribed.validCandidate sel)
          hValid.1 h).stablePath ∧
        IsPathEnd (Prescribed.validCandidate sel).datum first.1 vertex := by
  classical
  by_cases hAt : w.1.1 = wall
  · have hVertex : data.sourceEndpoint wall w.1.2 = w :=
      (GluingDatum.sourceEndpoint_eq_iff data wall w.1.2 w).mpr ⟨hAt.symm, rfl⟩
    by_cases hAnchor : (data.vertexPartition wall).Rel anchor.1 w.1.2
    · have hwEq : WallBlock.sourceVertex data wall anchor = w :=
        (GluingDatum.sourceEndpoint_eq_iff data wall anchor.1 w).mpr ⟨hAt.symm, hAnchor⟩
      have hIncAnchor : Incident data h.1 (WallBlock.sourceVertex data wall anchor) := by
        rw [hwEq]; exact hInc
      exact exists_isPathEnd_anchor source sel hValid (edge := ⟨h.1, hIncAnchor⟩) h.2
    · refine exists_isPathEnd_ordinary sel hValid hAnchor ?_ ?_
      · rw [hVertex]; exact hInc
      · rw [hVertex]; exact hNd
  · refine ⟨ResolutionAwayFromWall.retainedEdge (Prescribed.validCandidate sel) hValid.1 h,
      ResolutionAwayFromWall.retainedVertex (Prescribed.validCandidate sel) w, rfl, ?_, ?_⟩
    · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff
        (Prescribed.validCandidate sel) w hAt h.1).mpr hInc
    · rw [ResolutionAwayFromWall.nonDanglingValency_retainedVertex
        (Prescribed.validCandidate sel) hValid (candidate_sourceGenus sel) w hAt]
      exact hNd

end

end Two

/-! ## 4.  The outgoing presentation's last geometric receipt -/

section Conclusion

open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate

noncomputable section

variable {targetIn : CFGraph} {deg : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (cover : GluingDatum targetIn deg)
  (fd : FullDimensionalSourcePresentation cover coordinate)
  {a b : targetIn.V} {contracted : targetIn.edges}
  (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges targetIn a b = 1)
  (hForest : ContractionForest cover a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hNoReturn : LeafFacetNoReturn.NoContractedReturnOffRow cover contracted
    (fd.labelling.row.symm facet))
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)
  {wallStar : TwoStar (contract targetIn hab hOne) ⟨a, hab⟩}
  {anchorBlk : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩}
  (src : TwoBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent (contractDatum cover hc hab hOne)
    ⟨a, hab⟩ anchorBlk)

include src fd hForest hNoReturn hZeroCoord hPosCoord hFacetZero hOrd in
/-- **`HasPathEnds` of the outgoing valency-two Base II candidate.**  This is
the last geometric receipt of `NonTrivalentValencyTwoExit.outgoingFD`. -/
theorem hasPathEnds_candidate :
    HasPathEnds (Prescribed.validCandidate sel).datum := by
  classical
  have hValid : (contractDatum cover hc hab hOne).Valid :=
    NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest
  have hEnds : HasPathEnds (contractDatum cover hc hab hOne) :=
    hasPathEnds_contractDatum cover fd hc hab hOne hForest coordinates facet hNoReturn
      hZeroCoord hPosCoord hFacetZero
  refine NonTrivalentValencyTwoExit.hasPathEnds_of_retainedRowEnds cover fd hc hab hOne hForest
    src sel hOrd ?_
  intro r
  obtain ⟨g, hg⟩ := Quot.exists_rep r
  have hgr : NonDanglingEdge.stablePath g = r := hg
  obtain ⟨wallEdge, w, hRow, hInc, hNd⟩ := hEnds g
  obtain ⟨first, vertex, hFirst, hEnd⟩ :=
    Two.exists_isPathEnd_of_wall_end src sel hValid hInc hNd
  refine ⟨first, vertex, ?_, hEnd⟩
  rw [hFirst, ← NonTrivalentValencyTwoDescent.retainedRow_mk src sel hValid wallEdge, hRow, hgr]

end

end Conclusion

/-! ## 5.  The link at a wall of the outer walk -/

section Link

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate

noncomputable section

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {deg : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival deg graph label (label m.base)}
  (wd : WallData arrival)
  (hNoReturn : NoContractedReturn wd.cover wd.contracted)
  {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)

include src hNoReturn hOrd in
/-- **The path-ends receipt at the wall data of the outer walk.** -/
theorem hasPathEnds_wallData : HasPathEnds (Prescribed.validCandidate sel).datum :=
  hasPathEnds_candidate wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m)
    wd.coordinates (label m.base)
    (LeafFacetNoReturn.noContractedReturnOffRow_of_noContractedReturn wd.cover wd.contracted
      (wd.fullDim.labelling.row.symm (label m.base)) hNoReturn)
    wd.hZeroCoord wd.hPosCoord wd.hFacetZero src sel hOrd

/-- **`NonTrivalentValencyTwoExit.typeChangeLink_of_receipts` with the path-ends
hypothesis discharged.** -/
def typeChangeLink_of_receipts'
    (tracks : Tracks (NonTrivalentValencyTwoExit.wallOutgoingFD m wd hNoReturn src sel hOrd
      (hasPathEnds_wallData m wd hNoReturn src sel hOrd)) (graph.move m) label) :
    TypeChangeLink m wd :=
  NonTrivalentValencyTwoExit.typeChangeLink_of_receipts m wd hNoReturn src sel hOrd
    (hasPathEnds_wallData m wd hNoReturn src sel hOrd) tracks

end

end Link

/-! ## 6.  The same transport at a three-valent wall -/

namespace Three

open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W3R1SourceProfile
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeRows

noncomputable section

variable {wall : target.V} {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall}
  (source : ThreeBranchAnchor data star anchor)
  (hNoGlue : DanglingEdgeNoGlue data) (hValid : data.Valid)

/-- **The anchor half at a three-valent wall.**  Both endpoint classes `A_u`
and `A_v` of the prescribed Type III resolution are trivalent, and every
survivor of the anchor is carried to one of them: a doubled-direction survivor
to `A_u`, a simple-direction survivor to `A_v`. -/
theorem exists_isPathEnd_anchor
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hSurv : ¬ IsDangling data edge.1) :
    ∃ (first : NonDanglingEdge (Prescribed.validCandidate source hNoGlue hValid).datum)
      (vertex : (Prescribed.validCandidate source hNoGlue hValid).datum.SourceVertex),
      first.stablePath = (ResolutionAwayFromWall.retainedEdge
          (Prescribed.validCandidate source hNoGlue hValid) hValid.1
            ⟨edge.1, hSurv⟩).stablePath ∧
        IsPathEnd (Prescribed.validCandidate source hNoGlue hValid).datum first.1 vertex := by
  classical
  have hLabel : edge ∈ directionSurvivors data star anchor
      (survivorLabel data star anchor edge) :=
    (mem_directionSurvivors data star anchor _ edge).mpr
      ⟨(mem_survivors data anchor edge).mpr hSurv,
        (directionEdge_survivorLabel data star anchor edge).symm⟩
  by_cases hDoubled : survivorLabel data star anchor edge = Prescribed.doubled source
  · rw [hDoubled] at hLabel
    refine ⟨ResolutionAwayFromWall.retainedEdge
        (Prescribed.validCandidate source hNoGlue hValid) hValid.1 ⟨edge.1, hSurv⟩,
      endpointVertex source hNoGlue hValid false (Prescribed.selectedRepresentative source),
      rfl, ?_, ?_⟩
    · exact retained_survivor_incident source hNoGlue hValid false hLabel
        (rightAssignment_doubledDirection source) (endpointPartition_rel_doubled source hLabel)
    · rw [nonDanglingValency_endpointVertex source hNoGlue hValid false]
      omega
  · refine ⟨ResolutionAwayFromWall.retainedEdge
        (Prescribed.validCandidate source hNoGlue hValid) hValid.1 ⟨edge.1, hSurv⟩,
      endpointVertex source hNoGlue hValid true (Prescribed.selectedRepresentative source),
      rfl, ?_, ?_⟩
    · refine retained_survivor_incident source hNoGlue hValid true hLabel
        (Prescribed.rightAssignment_of_ne source
          (fun hEq ↦ hDoubled (directionEdge_injective star hEq)))
        (endpointPartition_rel_wall source (Prescribed.occurrenceSheet_wall_rel edge))
    · rw [nonDanglingValency_endpointVertex source hNoGlue hValid true]
      omega

/-- **The ordinary-block half at a three-valent wall.**  Every survivor of an
ordinary block reaches the trivalent end `B_v` along its own row
(`NonTrivalentValencyThreeDescent.exists_trivalentEndEdge`), and `B_v` carries
exactly the block's own surviving valency. -/
theorem exists_isPathEnd_ordinary
    {h : NonDanglingEdge data} {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hInc : Incident data h.1 (data.sourceEndpoint wall x))
    (hNd : nonDanglingValency data (data.sourceEndpoint wall x) ≠ 2) :
    ∃ (first : NonDanglingEdge (Prescribed.validCandidate source hNoGlue hValid).datum)
      (vertex : (Prescribed.validCandidate source hNoGlue hValid).datum.SourceVertex),
      first.stablePath = (ResolutionAwayFromWall.retainedEdge
          (Prescribed.validCandidate source hNoGlue hValid) hValid.1 h).stablePath ∧
        IsPathEnd (Prescribed.validCandidate source hNoGlue hValid).datum first.1 vertex := by
  classical
  have hOld : h.1 ∈ NonTrivalentValencyThreeDescent.ordinaryStar source x
      (Prescribed.rightAssignment source h.1.1.1) := by
    rw [NonTrivalentValencyThreeDescent.mem_ordinaryStar]
    exact ⟨⟨h.2, hInc⟩, rfl⟩
  obtain ⟨e, hIncE, hRowE, -⟩ :=
    NonTrivalentValencyThreeDescent.exists_trivalentEndEdge source hNoGlue hValid hX hOld
  refine ⟨e, endpointVertex source hNoGlue hValid true x, hRowE, hIncE, ?_⟩
  rw [NonTrivalentValencyThreeDescent.nonDanglingValency_endpointVertex_true_ordinary
    source hNoGlue hValid hX]
  exact hNd

/-- **A path end of the wall datum transports to a path end of the outgoing
Type III candidate**, on the retained row of the same occurrence.  This is the
valency-three input the Type III exit needs in place of the last field of
`FullDimensionalSourcePresentation`. -/
theorem exists_isPathEnd_of_wall_end
    {h : NonDanglingEdge data} {w : data.SourceVertex}
    (hInc : Incident data h.1 w) (hNd : nonDanglingValency data w ≠ 2) :
    ∃ (first : NonDanglingEdge (Prescribed.validCandidate source hNoGlue hValid).datum)
      (vertex : (Prescribed.validCandidate source hNoGlue hValid).datum.SourceVertex),
      first.stablePath = (ResolutionAwayFromWall.retainedEdge
          (Prescribed.validCandidate source hNoGlue hValid) hValid.1 h).stablePath ∧
        IsPathEnd (Prescribed.validCandidate source hNoGlue hValid).datum first.1 vertex := by
  classical
  by_cases hAt : w.1.1 = wall
  · have hVertex : data.sourceEndpoint wall w.1.2 = w :=
      (GluingDatum.sourceEndpoint_eq_iff data wall w.1.2 w).mpr ⟨hAt.symm, rfl⟩
    by_cases hAnchor : (data.vertexPartition wall).Rel anchor.1 w.1.2
    · have hwEq : WallBlock.sourceVertex data wall anchor = w :=
        (GluingDatum.sourceEndpoint_eq_iff data wall anchor.1 w).mpr ⟨hAt.symm, hAnchor⟩
      have hIncAnchor : Incident data h.1 (WallBlock.sourceVertex data wall anchor) := by
        rw [hwEq]; exact hInc
      exact exists_isPathEnd_anchor source hNoGlue hValid (edge := ⟨h.1, hIncAnchor⟩) h.2
    · refine exists_isPathEnd_ordinary source hNoGlue hValid hAnchor ?_ ?_
      · rw [hVertex]; exact hInc
      · rw [hVertex]; exact hNd
  · refine ⟨ResolutionAwayFromWall.retainedEdge
        (Prescribed.validCandidate source hNoGlue hValid) hValid.1 h,
      ResolutionAwayFromWall.retainedVertex
        (Prescribed.validCandidate source hNoGlue hValid) w, rfl, ?_, ?_⟩
    · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff
        (Prescribed.validCandidate source hNoGlue hValid) w hAt h.1).mpr hInc
    · rw [ResolutionAwayFromWall.nonDanglingValency_retainedVertex
        (Prescribed.validCandidate source hNoGlue hValid) hValid
        (candidate_sourceGenus source hNoGlue hValid) w hAt]
      exact hNd

end

end Three

end DraismaVargas.LocalCases.WallDatumPathEnds
