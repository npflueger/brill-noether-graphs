import DraismaVargas.LocalCases.W3FourHonestBalance
import DraismaVargas.LocalCases.StableGraphFullDimensional

/-!
# Figure 28's certified exit, one member at a time

Source: Draisma--Vargas Part I, Case {w3-r1-nd3-t2-(a=k4)}, Figure 28 and
Equation (2).

`W3FourRowDescent` proves, for each of Figure 28's four members, that the
member's stable incidence graph **is** the incoming one
(`PositionOne.equivalence`, `PositionTwo.equivalence`, `GrowMember.equivalence`).
This module turns that into what the semantic step wants: a
`FullDimensionalSource.FullDimensionalSourcePresentation` on a member, gated on
that member's own nonsingularity, together with the statement that it presents
*that member's* honest labelling -- the `W3FourHonestBalance.HonestFigure28`
labelling, whose matrix is the Equation (2) family's own presented matrix.

## Why the incoming datum cannot be the source of the transport

`StableGraphFullDimensional.presentationOfEquivalence` needs
`target₂.edges.card = target₁.edges.card`.  A member's datum lives over
`TargetExpansion.graph target wall right`, which has **one edge more** than
`target`, so the incoming datum `data` is never an admissible source: consistently
with `FullDimensionalSourcePresentation.stablePath_card`, the incoming wall datum carries
`|E(target)| + 1` stable rows and no square honest labelling at all.  Every
transport below is therefore **member to member**, between two of Figure 28's
four members, whose expanded targets differ only in the `right` field and so have
equal edge count (`expanded_targetEdgeCard`, by `simp`).

## Why the gauge copies do not obstruct it

The four members do **not** share one base: `M⁽¹⁾` and `M⁽²⁾` live on
branch-swapped copies (Part I works with isomorphism classes of gluing datums,
and for a fixed datum value the two cannot both be regrown), and
`W3FourRowDescent`'s equivalences are
stated from each member's *own* base.  A branch swap is a genuine
`GluingDatum.SheetRelabeling`, and `StableGraphIncidence.sheetRelabel` is an
incidence equivalence along one, so composing gives an equivalence from the
incoming datum to each member.  Composing two of those in opposite directions is
the member-to-member dictionary.  Nothing else crosses the swap; in particular no
census and no presentation is transported member to member.

## What is proved here

* `MemberDictionary` -- one member packaged for the exit: its gauge copy, that
  copy's validity implication, the member itself, its stable-incidence dictionary
  to the incoming datum, and its source genus.
* `growDictionary`, `positionOneDictionary`, `positionTwoDictionary` -- the three
  shapes of Figure 28 member, packaged.  `GrowMember` covers `M⁽³⁾` and `M⁽⁴⁾`.
* `exists_figure28Dictionaries` -- **all four members packaged at once**, on
  exactly the hypotheses `W3FourRegrownColumn.exists_figure28Receipts_honest`
  takes, with `M⁽³⁾`, `M⁽⁴⁾` the actual `thirdCandidate`, `fourthCandidate`.
* `outgoingPresentation` and `MemberDictionary.outgoingPresentation` -- the
  transport, gated on the outgoing member's own nonsingularity, with
  `presentation_eq` an identity of the supplied labelling.
* `growOutgoingPresentation`, `positionOneOutgoingPresentation`,
  `positionTwoOutgoingPresentation` -- **the four members' own exits**, each
  from any other member over the same expanded wall.
* `HonestFigure28Exit.presentationAt` -- the exit at a position of the honest
  receipts, gated on the **Equation (2) family's** determinant at that position
  and presenting `HonestFigure28.labelling`, so the family's nonsingularity gate
  and the member's honest one are literally the same condition.
* `HonestFigure28Exit.exists_valid_positive_exit_presentation` -- the positive exit
  of `W3FourHonestBalance` with a full-dimensional presentation of the outgoing
  member attached: the exit's own `det(incoming) * det(outgoing) < 0` discharges
  `presentationAt`'s gate.

## What this does *not* claim

Nothing here identifies the **incoming** member of the case, and nothing here
transports the exit back to the original (unexpanded) coordinates (that is done
in `W3FourIncomingMatching` and `W3FourHonestReceipts`).  The full-dimensional
presentation of *some* member is an input to every
statement below, never a conclusion; what is proved is that it propagates to all
four.
-/

namespace DraismaVargas.LocalCases.W3FourStableIncidence

open DraismaVargas.Infrastructure
open TargetExpansion
open BalancedGlobal
open W4StableSource StableSourceMatrix
open FullDimensionalSource
open ThirdEquation
open W3FourSurvival
open W3FourDisjointness
open W3FourClosure (FourStarGeometry ofGrowProfile)
open W3FourSourceCandidates (GrowProfile growProfileFirst growProfileSecond
  thirdCandidate fourthCandidate)
open W3FourHonestBalance (HonestFigure28)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}
  {star : ThreeStar target wall} {input : W3SourceInput data star}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## §1  The geometric receipts of an expanded target -/

theorem expanded_targetConnected (hConnected : graph_connected target)
    (right : target.edges → Bool) :
    graph_connected (TargetExpansion.graph target wall right) :=
  TargetExpansion.graph_connected target wall right hConnected

theorem expanded_targetGenus (hGenus : genus target = 0) (right : target.edges → Bool) :
    genus (TargetExpansion.graph target wall right) = 0 := by
  simpa using hGenus

/-- **Two Figure 28 members expand the same wall**, so their targets have the
same number of edges whatever their `right` fields are.  This is the receipt
`StableGraphFullDimensional.presentationOfEquivalence` needs and the reason the
transport has to be member to member. -/
theorem expanded_targetEdgeCard (first second : target.edges → Bool) :
    (TargetExpansion.graph target wall second).edges.card =
      (TargetExpansion.graph target wall first).edges.card := by
  simp

/-! ## §2  The four members, packaged with their dictionaries

`W3FourRowDescent` states each member's equivalence from the member's **own**
base.  `MemberDictionary` carries the composite with the gauge, so that every
member speaks about the one incoming datum and any two of them can be composed. -/

/-- One Figure 28 member, packaged for the exit. -/
structure MemberDictionary (data : GluingDatum target degree) (wall : target.V) where
  /-- The gauge copy of the incoming datum the member lives on. -/
  base : GluingDatum target degree
  /-- The copy is valid whenever the incoming datum is; this is
  `W3FourDisjointness.BranchGauge.valid`. -/
  valid_of_old : data.Valid → base.Valid
  /-- The member. -/
  candidate : Candidate target degree base wall
  /-- **Its stable incidence graph is the incoming one.** -/
  equivalence : StableGraphIncidence.Equivalence data candidate.datum
  /-- and it preserves the complete quotient-source genus. -/
  sourceGenus : genus candidate.datum.sourceGraph = genus data.sourceGraph

namespace MemberDictionary

variable (member : MemberDictionary data wall)

/-- The member's own datum is valid whenever the incoming one is. -/
theorem datum_valid (hValid : data.Valid) : member.candidate.datum.Valid :=
  member.candidate.datum_valid (member.valid_of_old hValid)

end MemberDictionary

/-- **A grow member's package**, hence `M⁽³⁾`'s and `M⁽⁴⁾`'s: both live over the
incoming datum itself, so the gauge is the identity. -/
noncomputable def growDictionary (grown : GrowProfile input)
    (survival : SelectedSurvival data wall (ofGrowProfile grown))
    (hValid : data.Valid) : MemberDictionary data wall where
  base := data
  valid_of_old := fun hOld ↦ hOld
  candidate := grown.growCandidate
  equivalence := W3FourRowDescent.GrowMember.equivalence grown survival hValid
  sourceGenus := grown.growCandidate_sourceGenus

@[simp] theorem growDictionary_candidate (grown : GrowProfile input)
    (survival : SelectedSurvival data wall (ofGrowProfile grown))
    (hValid : data.Valid) :
    (growDictionary grown survival hValid).candidate = grown.growCandidate := rfl

/-- **`M⁽¹⁾`'s package.**  Position I lives on a branch-swapped copy, and the
swap is a `GluingDatum.SheetRelabeling`, so the incoming stable graph reaches the
copy by `StableGraphIncidence.sheetRelabel` and the copy reaches the member by
`W3FourRowDescent.PositionOne.equivalence`. -/
noncomputable def positionOneDictionary (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (hGauge : data.Valid → relabeling.apply.Valid)
    (position : W3FourClosure.PositionOne relabeling.apply wall)
    (survival : SelectedSurvival relabeling.apply wall position.toFourStarGeometry)
    (hValid : relabeling.apply.Valid) : MemberDictionary data wall where
  base := relabeling.apply
  valid_of_old := hGauge
  candidate := position.candidate
  equivalence := (StableGraphIncidence.sheetRelabel relabeling hConnected).trans
    (W3FourRowDescent.PositionOne.equivalence position survival hValid)
  sourceGenus := (W3FourClosure.PositionOne.candidate_sourceGenus position).trans
    relabeling.sourceGraphLaplacianEquiv.genus_eq

@[simp] theorem positionOneDictionary_candidate (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (hGauge : data.Valid → relabeling.apply.Valid)
    (position : W3FourClosure.PositionOne relabeling.apply wall)
    (survival : SelectedSurvival relabeling.apply wall position.toFourStarGeometry)
    (hValid : relabeling.apply.Valid) :
    (positionOneDictionary relabeling hConnected hGauge position survival hValid).candidate =
      position.candidate := rfl

/-- **`M⁽²⁾`'s package**, the same way. -/
noncomputable def positionTwoDictionary (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (hGauge : data.Valid → relabeling.apply.Valid)
    (position : W3FourClosure.PositionTwo relabeling.apply wall)
    (survival : SelectedSurvival relabeling.apply wall position.toFourStarGeometry)
    (hValid : relabeling.apply.Valid) : MemberDictionary data wall where
  base := relabeling.apply
  valid_of_old := hGauge
  candidate := position.candidate
  equivalence := (StableGraphIncidence.sheetRelabel relabeling hConnected).trans
    (W3FourRowDescent.PositionTwo.equivalence position survival hValid)
  sourceGenus := (W3FourClosure.PositionTwo.candidate_sourceGenus position).trans
    relabeling.sourceGraphLaplacianEquiv.genus_eq

@[simp] theorem positionTwoDictionary_candidate (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (hGauge : data.Valid → relabeling.apply.Valid)
    (position : W3FourClosure.PositionTwo relabeling.apply wall)
    (survival : SelectedSurvival relabeling.apply wall position.toFourStarGeometry)
    (hValid : relabeling.apply.Valid) :
    (positionTwoDictionary relabeling hConnected hGauge position survival hValid).candidate =
      position.candidate := rfl

/-- **Figure 28's four members, each with a stable-graph dictionary to the
incoming datum**, on exactly the hypotheses
`W3FourRegrownColumn.exists_figure28Receipts_honest` and
`W3FourClosure.exists_equationTwo_family` take.  Positions `2` and `3` are the
actual Position II.a members over the incoming datum itself. -/
theorem exists_figure28Dictionaries (hValid : data.Valid)
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
    ∃ member : Fin 4 → MemberDictionary data wall,
      (member 2).base = data ∧ (member 3).base = data ∧
        HEq (member 2).candidate (thirdCandidate profile directions largest_index) ∧
        HEq (member 3).candidate (fourthCandidate profile directions largest_index) := by
  classical
  let grownFirst := growProfileFirst profile directions largest_index
  let grownSecond := growProfileSecond profile directions largest_index
  let geometry : FourStarGeometry data wall := ofGrowProfile grownFirst
  obtain ⟨permOne, hFixOne, positionOne, hGaugeOne, hGeomOne, _, _, _, _⟩ :=
    W3FourClosure.exists_member_one geometry root hRoot hGrowFixed hLargestFixed
      hOtherMoved
  obtain ⟨permTwo, hFixTwo, positionTwo, hGaugeTwo, hGeomTwo, _, _, _⟩ :=
    W3FourClosure.exists_member_two geometry root hRoot hGrowFixed hLargestFixed
      hOtherMoved
  have survivalOne : SelectedSurvival
      (branchSwapOfPerm data wall root hRoot permOne hFixOne).apply wall
        positionOne.toFourStarGeometry := by
    rw [hGeomOne]
    exact SelectedSurvival.swap geometry root hRoot permOne hFixOne
      (SelectedSurvival.ofGrowProfile grownFirst) hValid.1 hGrowFixed
      hLargestFixed hOtherMoved
  have survivalTwo : SelectedSurvival
      (branchSwapOfPerm data wall root hRoot permTwo hFixTwo).apply wall
        positionTwo.toFourStarGeometry := by
    rw [hGeomTwo]
    exact SelectedSurvival.swap geometry root hRoot permTwo hFixTwo
      (SelectedSurvival.ofGrowProfile grownFirst) hValid.1 hGrowFixed
      hLargestFixed hOtherMoved
  refine ⟨![positionOneDictionary (branchSwapOfPerm data wall root hRoot permOne hFixOne)
      hValid.1 hGaugeOne.valid positionOne survivalOne (hGaugeOne.valid hValid),
    positionTwoDictionary (branchSwapOfPerm data wall root hRoot permTwo hFixTwo)
      hValid.1 hGaugeTwo.valid positionTwo survivalTwo (hGaugeTwo.valid hValid),
    growDictionary grownFirst (SelectedSurvival.ofGrowProfile grownFirst) hValid,
    growDictionary grownSecond (SelectedSurvival.ofGrowProfile grownSecond) hValid],
    rfl, rfl, HEq.rfl, HEq.rfl⟩

/-! ## §3  The outgoing presentations -/

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **Figure 28's certified exit.**  Transport a full-dimensional presentation
along a stable incidence dictionary between two members over one expanded wall,
gated on the outgoing member's own nonsingularity.  `saturated` needs only that
both members expand the same target and preserve the incoming source genus;
`trivalent` and `pathEnds` are transported by
`StableGraphFullDimensional.presentationOfEquivalence`. -/
noncomputable def outgoingPresentation
    {sourceRight outgoingRight : target.edges → Bool}
    {sourceDatum : GluingDatum (TargetExpansion.graph target wall sourceRight) degree}
    {outgoingDatum : GluingDatum (TargetExpansion.graph target wall outgoingRight) degree}
    (certificate : StableGraphIncidence.Equivalence sourceDatum outgoingDatum)
    (hOutgoingValid : outgoingDatum.Valid)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hSourceGenus : genus sourceDatum.sourceGraph = genus data.sourceGraph)
    (hOutgoingGenus : genus outgoingDatum.sourceGraph = genus data.sourceGraph)
    (sourceFD : FullDimensionalSourcePresentation sourceDatum coordinate)
    (labelling : StableLengthMatrixLabelling outgoingDatum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    FullDimensionalSourcePresentation outgoingDatum coordinate :=
  StableGraphFullDimensional.presentationOfEquivalence sourceFD certificate hOutgoingValid
    (expanded_targetConnected hConnected outgoingRight)
    (expanded_targetGenus hGenus outgoingRight)
    (expanded_targetEdgeCard sourceRight outgoingRight)
    (hOutgoingGenus.trans hSourceGenus.symm)
    labelling hDet

@[simp] theorem outgoingPresentation_labelling
    {sourceRight outgoingRight : target.edges → Bool}
    {sourceDatum : GluingDatum (TargetExpansion.graph target wall sourceRight) degree}
    {outgoingDatum : GluingDatum (TargetExpansion.graph target wall outgoingRight) degree}
    (certificate : StableGraphIncidence.Equivalence sourceDatum outgoingDatum)
    (hOutgoingValid : outgoingDatum.Valid)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hSourceGenus : genus sourceDatum.sourceGraph = genus data.sourceGraph)
    (hOutgoingGenus : genus outgoingDatum.sourceGraph = genus data.sourceGraph)
    (sourceFD : FullDimensionalSourcePresentation sourceDatum coordinate)
    (labelling : StableLengthMatrixLabelling outgoingDatum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    (outgoingPresentation (data := data) certificate hOutgoingValid hConnected hGenus
      hSourceGenus hOutgoingGenus sourceFD labelling hDet).labelling = labelling := rfl

namespace MemberDictionary

/-- **One Figure 28 member's exit, from another.**  The member-to-member
dictionary is the composite of the two members' dictionaries to the incoming
datum, one reversed; the gauge copies never appear in the conclusion. -/
noncomputable def outgoingPresentation (source outgoing : MemberDictionary data wall)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (sourceFD : FullDimensionalSourcePresentation source.candidate.datum coordinate)
    (labelling : StableLengthMatrixLabelling outgoing.candidate.datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    FullDimensionalSourcePresentation outgoing.candidate.datum coordinate :=
  W3FourStableIncidence.outgoingPresentation (data := data)
    (source.equivalence.symm.trans outgoing.equivalence) (outgoing.datum_valid hValid)
    hConnected hGenus source.sourceGenus outgoing.sourceGenus sourceFD labelling hDet

/-- It presents the outgoing member's own labelling. -/
@[simp] theorem outgoingPresentation_labelling (source outgoing : MemberDictionary data wall)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (sourceFD : FullDimensionalSourcePresentation source.candidate.datum coordinate)
    (labelling : StableLengthMatrixLabelling outgoing.candidate.datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    (source.outgoingPresentation outgoing hValid hConnected hGenus sourceFD labelling
      hDet).labelling = labelling := rfl

theorem outgoingPresentation_presentation_eq (source outgoing : MemberDictionary data wall)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (sourceFD : FullDimensionalSourcePresentation source.candidate.datum coordinate)
    (labelling : StableLengthMatrixLabelling outgoing.candidate.datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    (source.outgoingPresentation outgoing hValid hConnected hGenus sourceFD labelling
      hDet).labelling.presentation = labelling.presentation := rfl

end MemberDictionary

/-! ### The four members' own exits

`M⁽³⁾` and `M⁽⁴⁾` are the two `GrowProfile`s of the case, so `GrowMember` covers
both; `M⁽¹⁾` and `M⁽²⁾` each live on their own branch-swapped copy. -/

/-- **A grow member's outgoing presentation**, hence `M⁽³⁾`'s and `M⁽⁴⁾`'s. -/
noncomputable def growOutgoingPresentation (source : MemberDictionary data wall)
    (grown : GrowProfile input)
    (survival : SelectedSurvival data wall (ofGrowProfile grown))
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (sourceFD : FullDimensionalSourcePresentation source.candidate.datum coordinate)
    (labelling : StableLengthMatrixLabelling grown.growCandidate.datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    FullDimensionalSourcePresentation grown.growCandidate.datum coordinate :=
  source.outgoingPresentation (growDictionary grown survival hValid) hValid hConnected
    hGenus sourceFD labelling hDet

theorem growOutgoingPresentation_presentation_eq (source : MemberDictionary data wall)
    (grown : GrowProfile input)
    (survival : SelectedSurvival data wall (ofGrowProfile grown))
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (sourceFD : FullDimensionalSourcePresentation source.candidate.datum coordinate)
    (labelling : StableLengthMatrixLabelling grown.growCandidate.datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    (growOutgoingPresentation source grown survival hValid hConnected hGenus sourceFD
      labelling hDet).labelling.presentation = labelling.presentation := rfl

/-- **`M⁽¹⁾`'s outgoing presentation.** -/
noncomputable def positionOneOutgoingPresentation (source : MemberDictionary data wall)
    (relabeling : data.SheetRelabeling) (hGauge : data.Valid → relabeling.apply.Valid)
    (position : W3FourClosure.PositionOne relabeling.apply wall)
    (survival : SelectedSurvival relabeling.apply wall position.toFourStarGeometry)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (sourceFD : FullDimensionalSourcePresentation source.candidate.datum coordinate)
    (labelling : StableLengthMatrixLabelling position.candidate.datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    FullDimensionalSourcePresentation position.candidate.datum coordinate :=
  source.outgoingPresentation
    (positionOneDictionary relabeling hValid.1 hGauge position survival (hGauge hValid))
    hValid hConnected hGenus sourceFD labelling hDet

theorem positionOneOutgoingPresentation_presentation_eq (source : MemberDictionary data wall)
    (relabeling : data.SheetRelabeling) (hGauge : data.Valid → relabeling.apply.Valid)
    (position : W3FourClosure.PositionOne relabeling.apply wall)
    (survival : SelectedSurvival relabeling.apply wall position.toFourStarGeometry)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (sourceFD : FullDimensionalSourcePresentation source.candidate.datum coordinate)
    (labelling : StableLengthMatrixLabelling position.candidate.datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    (positionOneOutgoingPresentation source relabeling hGauge position survival hValid
      hConnected hGenus sourceFD labelling hDet).labelling.presentation =
      labelling.presentation := rfl

/-- **`M⁽²⁾`'s outgoing presentation.** -/
noncomputable def positionTwoOutgoingPresentation (source : MemberDictionary data wall)
    (relabeling : data.SheetRelabeling) (hGauge : data.Valid → relabeling.apply.Valid)
    (position : W3FourClosure.PositionTwo relabeling.apply wall)
    (survival : SelectedSurvival relabeling.apply wall position.toFourStarGeometry)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (sourceFD : FullDimensionalSourcePresentation source.candidate.datum coordinate)
    (labelling : StableLengthMatrixLabelling position.candidate.datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    FullDimensionalSourcePresentation position.candidate.datum coordinate :=
  source.outgoingPresentation
    (positionTwoDictionary relabeling hValid.1 hGauge position survival (hGauge hValid))
    hValid hConnected hGenus sourceFD labelling hDet

theorem positionTwoOutgoingPresentation_presentation_eq (source : MemberDictionary data wall)
    (relabeling : data.SheetRelabeling) (hGauge : data.Valid → relabeling.apply.Valid)
    (position : W3FourClosure.PositionTwo relabeling.apply wall)
    (survival : SelectedSurvival relabeling.apply wall position.toFourStarGeometry)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (sourceFD : FullDimensionalSourcePresentation source.candidate.datum coordinate)
    (labelling : StableLengthMatrixLabelling position.candidate.datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    (positionTwoOutgoingPresentation source relabeling hGauge position survival hValid
      hConnected hGenus sourceFD labelling hDet).labelling.presentation =
      labelling.presentation := rfl

/-! ## §4  The exit at a position of the honest Equation (2) family

`W3FourHonestBalance.HonestFigure28.labelling i` is the honest stable labelling
of member `i`, and its matrix is the family's own presented matrix
(`labelling_matrix`).  So stating the exit here gates it on the **Equation (2)
determinant** at that position, and `presentation_eq` is an identity of the
family's honest labelling.  `HonestFigure28` carries no source-genus field --
`W3FourStableGraph.MemberColumn` has none -- so the two genus receipts and the
member-to-member dictionary are hypotheses at this level; §2's packages discharge
all three for the members the case actually builds. -/

namespace HonestFigure28Exit

variable {geometry : FourStarGeometry data wall}
  (honestReceipts : HonestFigure28 data wall geometry)

/-- **Figure 28's certified exit at a position of the honest receipts.** -/
noncomputable def presentationAt (incoming outgoing : Fin 4)
    (certificate : StableGraphIncidence.Equivalence
      (honestReceipts.candidate incoming).datum (honestReceipts.candidate outgoing).datum)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hIncomingGenus :
      genus (honestReceipts.candidate incoming).datum.sourceGraph = genus data.sourceGraph)
    (hOutgoingGenus :
      genus (honestReceipts.candidate outgoing).datum.sourceGraph = genus data.sourceGraph)
    (incomingFD : FullDimensionalSourcePresentation
      (honestReceipts.candidate incoming).datum (Option target.edges))
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix
      (honestReceipts.gaugeFamily.presentation outgoing)).det ≠ 0) :
    FullDimensionalSourcePresentation (honestReceipts.candidate outgoing).datum
      (Option target.edges) :=
  outgoingPresentation (data := data) certificate
    (honestReceipts.candidate_valid outgoing hValid) hConnected hGenus hIncomingGenus
    hOutgoingGenus incomingFD (honestReceipts.labelling outgoing)
    (honestReceipts.labelling_det_ne_zero outgoing hDet)

/-- **It presents the family's own honest labelling.** -/
theorem presentationAt_presentation_eq (incoming outgoing : Fin 4)
    (certificate : StableGraphIncidence.Equivalence
      (honestReceipts.candidate incoming).datum (honestReceipts.candidate outgoing).datum)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hIncomingGenus :
      genus (honestReceipts.candidate incoming).datum.sourceGraph = genus data.sourceGraph)
    (hOutgoingGenus :
      genus (honestReceipts.candidate outgoing).datum.sourceGraph = genus data.sourceGraph)
    (incomingFD : FullDimensionalSourcePresentation
      (honestReceipts.candidate incoming).datum (Option target.edges))
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix
      (honestReceipts.gaugeFamily.presentation outgoing)).det ≠ 0) :
    (presentationAt honestReceipts incoming outgoing certificate hValid hConnected hGenus
        hIncomingGenus hOutgoingGenus incomingFD hDet).labelling.presentation =
      (honestReceipts.labelling outgoing).presentation := rfl

/-- **and its length matrix is Equation (2)'s own.** -/
theorem presentationAt_matrix (incoming outgoing : Fin 4)
    (certificate : StableGraphIncidence.Equivalence
      (honestReceipts.candidate incoming).datum (honestReceipts.candidate outgoing).datum)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hIncomingGenus :
      genus (honestReceipts.candidate incoming).datum.sourceGraph = genus data.sourceGraph)
    (hOutgoingGenus :
      genus (honestReceipts.candidate outgoing).datum.sourceGraph = genus data.sourceGraph)
    (incomingFD : FullDimensionalSourcePresentation
      (honestReceipts.candidate incoming).datum (Option target.edges))
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix
      (honestReceipts.gaugeFamily.presentation outgoing)).det ≠ 0) :
    GluingDatum.LengthMatrixPresentation.matrix
        (presentationAt honestReceipts incoming outgoing certificate hValid hConnected
          hGenus hIncomingGenus hOutgoingGenus incomingFD hDet).labelling.presentation =
      GluingDatum.LengthMatrixPresentation.matrix
        (honestReceipts.gaugeFamily.presentation outgoing) :=
  honestReceipts.labelling_matrix outgoing

/-- **The positive exit, with the outgoing member's full-dimensional
presentation attached.**

`W3FourHonestBalance.HonestFigure28.exists_valid_positive_exit_with_pencil`
produces an outgoing member whose determinant has the opposite sign to the
incoming one; that is already the nonsingularity `presentationAt` asks for.  So
on the four dictionaries and the four source-genus receipts -- which §2 supplies
for the members the case builds -- Equation (2)'s exit hands back a member that
is valid, strictly opposite, positively reachable with a cleared pencil, **and**
full-dimensionally presented in the honest coordinates. -/
theorem exists_valid_positive_exit_presentation
    (certificate : ∀ i j, StableGraphIncidence.Equivalence
      (honestReceipts.candidate i).datum (honestReceipts.candidate j).datum)
    (memberGenus : ∀ i,
      genus (honestReceipts.candidate i).datum.sourceGraph = genus data.sourceGraph)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (root : target.V) (incoming : Fin 4)
    (incomingFD : FullDimensionalSourcePresentation
      (honestReceipts.candidate incoming).datum (Option target.edges))
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
      (GluingDatum.LengthMatrixPresentation.matrix
          (honestReceipts.gaugeFamily.presentation incoming)).det *
        (GluingDatum.LengthMatrixPresentation.matrix
          (honestReceipts.gaugeFamily.presentation outgoing)).det < 0 ∧
      (∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        Nonempty (BalancedGlobal.Candidate.ClearedPencil
          (honestReceipts.candidate outgoing)
          (honestReceipts.gaugeFamily.presentation outgoing)
          (z + t • outgoingVelocity outgoing))) ∧
      ∃ outgoingFD : FullDimensionalSourcePresentation
          (honestReceipts.candidate outgoing).datum (Option target.edges),
        GluingDatum.LengthMatrixPresentation.matrix outgoingFD.labelling.presentation =
          GluingDatum.LengthMatrixPresentation.matrix
            (honestReceipts.gaugeFamily.presentation outgoing) := by
  obtain ⟨outgoing, _, hOpposite, δ, hδ, hPencil⟩ :=
    honestReceipts.exists_valid_positive_exit_with_pencil hValid hConnected hGenus root
      incoming hincoming z incomingVelocity outgoingVelocity hz hzpos hSystems
      hIncomingDirection
  have hDet : (GluingDatum.LengthMatrixPresentation.matrix
      (honestReceipts.gaugeFamily.presentation outgoing)).det ≠ 0 := by
    intro hZero
    rw [hZero, mul_zero] at hOpposite
    exact lt_irrefl 0 hOpposite
  refine ⟨outgoing, hOpposite, ⟨δ, hδ, fun t ht htδ ↦ ⟨(hPencil t ht htδ).1,
    (hPencil t ht htδ).2.2⟩⟩,
    presentationAt honestReceipts incoming outgoing (certificate incoming outgoing) hValid
      hConnected hGenus (memberGenus incoming) (memberGenus outgoing) incomingFD hDet, ?_⟩
  exact presentationAt_matrix honestReceipts incoming outgoing
    (certificate incoming outgoing) hValid hConnected hGenus (memberGenus incoming)
    (memberGenus outgoing) incomingFD hDet

end HonestFigure28Exit

end DraismaVargas.LocalCases.W3FourStableIncidence
