import DraismaVargas.LocalCases.W2MkkGraphData
import DraismaVargas.LocalCases.W2MkkLimitColumns
import DraismaVargas.LocalCases.StableGraphFullDimensional

/-!
# Figure 34's certified exit, one member at a time

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-kk}`, Figure 34.

`W2MkkGraphData` identifies each Figure 34 member's stable incidence graph with
the incoming one.  This module turns that into what the semantic step wants: a
`FullDimensionalSource.FullDimensionalSourcePresentation` on a member, gated on
that member's own nonsingularity, together with the statement that it presents
*that member's* honest labelling.

## Why this is stated per member and not over a family

`W2MkkSourceCandidates.no_common_geometry` forbids putting Figure 34's two
detaching members over one datum, so `M⁽²⁾` lives over the branch-swapped datum
and Figure 34's three members are not a `BalancedGlobal.Family` over `data`.
That obstruction is not addressed here (the gauge families of
`W2MkkArbitraryExit` handle it).  What is discharged is everything on the
member side of it:

* the transport itself, `StableGraphFullDimensional.presentationOfEquivalence`,
  needs a member-to-member dictionary and two numerical receipts.  Both Figure
  34 members over one datum share the expanded target
  `TargetExpansion.graph target wall (orientedStar profile).right` -- their
  `right` fields are literally the oriented two-star's -- so the edge-count
  receipt is `rfl`-level and the source-genus receipt is each member's own
  `genus_eq`;
* the honest labelling is not invented here.  `presentationAt` is gated on
  `W2MkkCommonBalance.LimitColumns.squareMatrix` and carries
  `W2MkkCommonBalance.LimitColumns.labelling` -- the family's own honest
  labelling -- so `presentation_eq` is `rfl` against it.  The receipt is
  `W2MkkLimitColumns.limitColumns`, which inhabits it on the case's actual
  input in both orientations, so nothing below is conditional on an
  uninhabited structure.

`M⁽²⁾` is obtained, here as in `W2MkkStableLift`, by instantiating the
detaching definitions at the branch-swapped datum; nothing below is transported
across the branch swap.

## Where the members come from

The two Figure 34 members over one datum are `W2MkkLimitColumns.localMember`
and `W2MkkLimitColumns.joinedMember`; this module defines none of its own.
Their data are the candidates of `W2MkkSourceCandidates` on the nose
(`localMember_datum`, `joinedMember_datum`, both `rfl`), so §2's dictionaries
and §5's candidate-level exits apply to them without any transport, which is
what §6 records.
-/

namespace DraismaVargas.LocalCases.W2MkkStableIncidence

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StableSourceMatrix
open ResolutionM11 GlobalM11Arbitrary
open ResolutionAwayFromWall
open FullDimensionalSource
open W2MkkSourceCandidates
open W2MkkStableGraph W2MkkStableLift W2MkkRowDescent W2MkkLimitMatrix
open W2MkkGraphData
open W2MkkCommonBalance (LimitMember LimitColumns)
open W2MkkLimitColumns

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-! ## §1  The geometric receipts of an expanded target -/

theorem expanded_targetConnected (hConnected : graph_connected target)
    (right : target.edges → Bool) :
    graph_connected (TargetExpansion.graph target wall right) :=
  TargetExpansion.graph_connected target wall right hConnected

theorem expanded_targetGenus (hGenus : genus target = 0) (right : target.edges → Bool) :
    genus (TargetExpansion.graph target wall right) = 0 := by
  simpa using hGenus

theorem expanded_targetEdgeCard (first second : target.edges → Bool) :
    (TargetExpansion.graph target wall second).edges.card =
      (TargetExpansion.graph target wall first).edges.card := by
  simp

/-! ## §2  The member-to-member stable incidence dictionaries -/

/-- From a detaching member to `M⁽³⁾`, through the incoming stable graph. -/
noncomputable def detachToJoined (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree) :
    StableGraphIncidence.Equivalence (detach.candidate shape).datum
      (joinedCandidate profile distinguished).datum :=
  (detachEquivalence input shape detach).symm.trans
    (joinedEquivalence input shape distinguished)

/-- From `M⁽³⁾` to a detaching member. -/
noncomputable def joinedToDetach (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree) :
    StableGraphIncidence.Equivalence (joinedCandidate profile distinguished).datum
      (detach.candidate shape).datum :=
  (joinedEquivalence input shape distinguished).symm.trans
    (detachEquivalence input shape detach)

/-! ## §3  The outgoing presentations -/

/-- **Figure 34's certified exit.**  Transport a full-dimensional presentation
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
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
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
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (sourceFD : FullDimensionalSourcePresentation sourceDatum coordinate)
    (labelling : StableLengthMatrixLabelling outgoingDatum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    (outgoingPresentation (data := data) certificate hOutgoingValid hConnected hGenus
      hSourceGenus hOutgoingGenus sourceFD labelling hDet).labelling = labelling := rfl

/-! ### The two members' own exits -/

/-- **`M⁽³⁾`'s outgoing presentation**, from a detaching member's. -/
noncomputable def joinedOutgoingPresentation (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) (distinguished : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (detachFD : FullDimensionalSourcePresentation (detach.candidate shape).datum coordinate)
    (labelling : StableLengthMatrixLabelling
      (joinedCandidate profile distinguished).datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    FullDimensionalSourcePresentation (joinedCandidate profile distinguished).datum coordinate :=
  outgoingPresentation (data := data) (detachToJoined input shape detach distinguished)
    ((joinedCandidate profile distinguished).datum_valid input.valid) hConnected hGenus
    (detach_sourceGenus shape detach) (joined_sourceGenus profile distinguished)
    detachFD labelling hDet

/-- It presents `M⁽³⁾`'s own labelling. -/
theorem joinedOutgoingPresentation_presentation_eq (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) (distinguished : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (detachFD : FullDimensionalSourcePresentation (detach.candidate shape).datum coordinate)
    (labelling : StableLengthMatrixLabelling
      (joinedCandidate profile distinguished).datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    (joinedOutgoingPresentation input shape detach distinguished hConnected hGenus
      detachFD labelling hDet).labelling.presentation = labelling.presentation := rfl

/-- **A detaching member's outgoing presentation**, from `M⁽³⁾`'s. -/
noncomputable def detachOutgoingPresentation (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) (distinguished : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (joinedFD : FullDimensionalSourcePresentation
      (joinedCandidate profile distinguished).datum coordinate)
    (labelling : StableLengthMatrixLabelling (detach.candidate shape).datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    FullDimensionalSourcePresentation (detach.candidate shape).datum coordinate :=
  outgoingPresentation (data := data) (joinedToDetach input shape detach distinguished)
    ((detach.candidate shape).datum_valid input.valid) hConnected hGenus
    (joined_sourceGenus profile distinguished) (detach_sourceGenus shape detach)
    joinedFD labelling hDet

/-- It presents the detaching member's own labelling. -/
theorem detachOutgoingPresentation_presentation_eq (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) (distinguished : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (joinedFD : FullDimensionalSourcePresentation
      (joinedCandidate profile distinguished).datum coordinate)
    (labelling : StableLengthMatrixLabelling (detach.candidate shape).datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    (detachOutgoingPresentation input shape detach distinguished hConnected hGenus
      joinedFD labelling hDet).labelling.presentation = labelling.presentation := rfl

/-- **A member's own relabelling exit.**  The identity dictionary, so the same
member with any nonsingular honest labelling of its own. -/
noncomputable def selfOutgoingPresentation
    {expandedRight : target.edges → Bool}
    {expandedDatum : GluingDatum (TargetExpansion.graph target wall expandedRight) degree}
    (hValid : expandedDatum.Valid)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hSourceGenus : genus expandedDatum.sourceGraph = genus data.sourceGraph)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (sourceFD : FullDimensionalSourcePresentation expandedDatum coordinate)
    (labelling : StableLengthMatrixLabelling expandedDatum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    FullDimensionalSourcePresentation expandedDatum coordinate :=
  outgoingPresentation (data := data) (StableGraphIncidence.Equivalence.refl expandedDatum)
    hValid hConnected hGenus hSourceGenus hSourceGenus sourceFD labelling hDet

/-! ## §4  The exit on the inhabited receipt

`W2MkkLimitColumns.limitColumns` inhabits `W2MkkCommonBalance.LimitColumns` on
the case's actual input, in both orientations.  Stating the exit at a position
of such a receipt gates it on `LimitColumns.squareMatrix` -- the determinant
`W2MkkCommonBalance.LimitColumns.determinant_balance` and `positiveBalance`
talk about -- and makes `presentation_eq` an identity of the family's own
honest `LimitColumns.labelling`.

`LimitMember` carries no source-genus field, so the two genus receipts are
hypotheses here; for the two positions over the incoming datum §5 discharges
them from `detach_sourceGenus` and `joined_sourceGenus`. -/

/-- **Figure 34's certified exit at a position of a limit-column receipt.** -/
noncomputable def presentationAt {shape : Shape profile} (limit : LimitColumns profile shape)
    (incoming outgoing : Fin 3)
    (certificate : StableGraphIncidence.Equivalence
      (limit.member incoming).datum (limit.member outgoing).datum)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hIncomingGenus : genus (limit.member incoming).datum.sourceGraph = genus data.sourceGraph)
    (hOutgoingGenus : genus (limit.member outgoing).datum.sourceGraph = genus data.sourceGraph)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate)
    (hDet : (limit.squareMatrix initial outgoing).det ≠ 0) :
    FullDimensionalSourcePresentation (limit.member outgoing).datum coordinate :=
  outgoingPresentation (data := data) certificate ((limit.member outgoing).valid_of_old hValid)
    hConnected hGenus hIncomingGenus hOutgoingGenus incomingFD
    (limit.labelling initial outgoing) hDet

/-- **It presents the family's own honest labelling.**  This is the
`presentation_eq` of `A04FourTags.FullDimSupply`, at member level. -/
theorem presentationAt_presentation_eq {shape : Shape profile}
    (limit : LimitColumns profile shape) (incoming outgoing : Fin 3)
    (certificate : StableGraphIncidence.Equivalence
      (limit.member incoming).datum (limit.member outgoing).datum)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hIncomingGenus : genus (limit.member incoming).datum.sourceGraph = genus data.sourceGraph)
    (hOutgoingGenus : genus (limit.member outgoing).datum.sourceGraph = genus data.sourceGraph)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate)
    (hDet : (limit.squareMatrix initial outgoing).det ≠ 0) :
    (presentationAt limit incoming outgoing certificate hValid hConnected hGenus
      hIncomingGenus hOutgoingGenus initial incomingFD hDet).labelling.presentation =
      (limit.labelling initial outgoing).presentation := rfl

/-! ## §5  The two positions over the incoming datum

`W2MkkLimitColumns.localMember` and `W2MkkLimitColumns.joinedMember` carry the
candidates of `W2MkkSourceCandidates` on the nose, so §2's dictionaries and the
two genus receipts typecheck at these positions without any transport.  Base
II.2.1.M puts the local detaching member at position `0`, Base II.2.2.M at
position `1`; `M⁽³⁾` is at position `2` in both. -/

section FirstOrientation

variable (input : W2SourceInput data star) (shape : Shape profile)
  (member : FirstMember profile) (distinguished : Fin degree)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **`M⁽³⁾`'s outgoing presentation in the Base II.2.1.M orientation**, from
`M⁽¹⁾`'s. -/
noncomputable def firstOrientationJoinedPresentation
    (initial : StableLengthMatrixLabelling
      ((firstOrientation input shape member distinguished hConnected hGenus).member 0).datum
      coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      ((firstOrientation input shape member distinguished hConnected hGenus).member 0).datum
      coordinate)
    (hDet : ((firstOrientation input shape member distinguished hConnected
      hGenus).squareMatrix initial 2).det ≠ 0) :
    FullDimensionalSourcePresentation
      ((firstOrientation input shape member distinguished hConnected hGenus).member 2).datum
      coordinate :=
  presentationAt (firstOrientation input shape member distinguished hConnected hGenus) 0 2
    (detachToJoined input shape member.toDetachData distinguished) input.valid hConnected hGenus
    (detach_sourceGenus shape member.toDetachData) (joined_sourceGenus profile distinguished)
    initial incomingFD hDet

theorem firstOrientationJoinedPresentation_presentation_eq
    (initial : StableLengthMatrixLabelling
      ((firstOrientation input shape member distinguished hConnected hGenus).member 0).datum
      coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      ((firstOrientation input shape member distinguished hConnected hGenus).member 0).datum
      coordinate)
    (hDet : ((firstOrientation input shape member distinguished hConnected
      hGenus).squareMatrix initial 2).det ≠ 0) :
    (firstOrientationJoinedPresentation input shape member distinguished hConnected hGenus
        initial incomingFD hDet).labelling.presentation =
      ((firstOrientation input shape member distinguished hConnected hGenus).labelling
        initial 2).presentation := rfl

/-- **`M⁽¹⁾`'s outgoing presentation**, from `M⁽³⁾`'s. -/
noncomputable def firstOrientationLocalPresentation
    (initial : StableLengthMatrixLabelling
      ((firstOrientation input shape member distinguished hConnected hGenus).member 0).datum
      coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      ((firstOrientation input shape member distinguished hConnected hGenus).member 2).datum
      coordinate)
    (hDet : ((firstOrientation input shape member distinguished hConnected
      hGenus).squareMatrix initial 0).det ≠ 0) :
    FullDimensionalSourcePresentation
      ((firstOrientation input shape member distinguished hConnected hGenus).member 0).datum
      coordinate :=
  presentationAt (firstOrientation input shape member distinguished hConnected hGenus) 2 0
    (joinedToDetach input shape member.toDetachData distinguished) input.valid hConnected hGenus
    (joined_sourceGenus profile distinguished) (detach_sourceGenus shape member.toDetachData)
    initial incomingFD hDet

theorem firstOrientationLocalPresentation_presentation_eq
    (initial : StableLengthMatrixLabelling
      ((firstOrientation input shape member distinguished hConnected hGenus).member 0).datum
      coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      ((firstOrientation input shape member distinguished hConnected hGenus).member 2).datum
      coordinate)
    (hDet : ((firstOrientation input shape member distinguished hConnected
      hGenus).squareMatrix initial 0).det ≠ 0) :
    (firstOrientationLocalPresentation input shape member distinguished hConnected hGenus
        initial incomingFD hDet).labelling.presentation =
      ((firstOrientation input shape member distinguished hConnected hGenus).labelling
        initial 0).presentation := rfl

end FirstOrientation

section SecondOrientation

variable (input : W2SourceInput data star) (shape : Shape profile)
  (member : SecondMember profile) (distinguished : Fin degree)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **`M⁽³⁾`'s outgoing presentation in the Base II.2.2.M orientation**, from
`M⁽²⁾`'s. -/
noncomputable def secondOrientationJoinedPresentation
    (initial : StableLengthMatrixLabelling
      ((secondOrientation input shape member distinguished hConnected hGenus).member 0).datum
      coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      ((secondOrientation input shape member distinguished hConnected hGenus).member 1).datum
      coordinate)
    (hDet : ((secondOrientation input shape member distinguished hConnected
      hGenus).squareMatrix initial 2).det ≠ 0) :
    FullDimensionalSourcePresentation
      ((secondOrientation input shape member distinguished hConnected hGenus).member 2).datum
      coordinate :=
  presentationAt (secondOrientation input shape member distinguished hConnected hGenus) 1 2
    (detachToJoined input shape member.toDetachData distinguished) input.valid hConnected hGenus
    (detach_sourceGenus shape member.toDetachData) (joined_sourceGenus profile distinguished)
    initial incomingFD hDet

theorem secondOrientationJoinedPresentation_presentation_eq
    (initial : StableLengthMatrixLabelling
      ((secondOrientation input shape member distinguished hConnected hGenus).member 0).datum
      coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      ((secondOrientation input shape member distinguished hConnected hGenus).member 1).datum
      coordinate)
    (hDet : ((secondOrientation input shape member distinguished hConnected
      hGenus).squareMatrix initial 2).det ≠ 0) :
    (secondOrientationJoinedPresentation input shape member distinguished hConnected hGenus
        initial incomingFD hDet).labelling.presentation =
      ((secondOrientation input shape member distinguished hConnected hGenus).labelling
        initial 2).presentation := rfl

/-- **`M⁽²⁾`'s outgoing presentation**, from `M⁽³⁾`'s. -/
noncomputable def secondOrientationLocalPresentation
    (initial : StableLengthMatrixLabelling
      ((secondOrientation input shape member distinguished hConnected hGenus).member 0).datum
      coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      ((secondOrientation input shape member distinguished hConnected hGenus).member 2).datum
      coordinate)
    (hDet : ((secondOrientation input shape member distinguished hConnected
      hGenus).squareMatrix initial 1).det ≠ 0) :
    FullDimensionalSourcePresentation
      ((secondOrientation input shape member distinguished hConnected hGenus).member 1).datum
      coordinate :=
  presentationAt (secondOrientation input shape member distinguished hConnected hGenus) 2 1
    (joinedToDetach input shape member.toDetachData distinguished) input.valid hConnected hGenus
    (joined_sourceGenus profile distinguished) (detach_sourceGenus shape member.toDetachData)
    initial incomingFD hDet

theorem secondOrientationLocalPresentation_presentation_eq
    (initial : StableLengthMatrixLabelling
      ((secondOrientation input shape member distinguished hConnected hGenus).member 0).datum
      coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      ((secondOrientation input shape member distinguished hConnected hGenus).member 2).datum
      coordinate)
    (hDet : ((secondOrientation input shape member distinguished hConnected
      hGenus).squareMatrix initial 1).det ≠ 0) :
    (secondOrientationLocalPresentation input shape member distinguished hConnected hGenus
        initial incomingFD hDet).labelling.presentation =
      ((secondOrientation input shape member distinguished hConnected hGenus).labelling
        initial 1).presentation := rfl

end SecondOrientation

/-! ## §6  The members of `W2MkkLimitColumns` are these candidates on the nose -/

/-- The detaching member's dictionary is a dictionary for
`W2MkkLimitColumns.localMember`. -/
noncomputable def localMember_equivalence (input : W2SourceInput data star)
    (shape : Shape profile)
    (detach : DetachData profile) :
    StableGraphIncidence.Equivalence data (localMember input shape detach).datum :=
  detachEquivalence input shape detach

/-- and `M⁽³⁾`'s for `W2MkkLimitColumns.joinedMember`. -/
noncomputable def joinedMember_equivalence (input : W2SourceInput data star)
    (shape : Shape profile)
    (distinguished : Fin degree) :
    StableGraphIncidence.Equivalence data (joinedMember input shape distinguished).datum :=
  joinedEquivalence input shape distinguished

/-- Both members' row maps are the row bijections this module's dictionaries
use, so nothing is reindexed between the limit-matrix modules and the exit. -/
theorem localMember_row_eq (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) :
    (localMember input shape detach).row = (detachEquivalence input shape detach).row := rfl

theorem joinedMember_row_eq (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) :
    (joinedMember input shape distinguished).row =
      (joinedEquivalence input shape distinguished).row := rfl

end DraismaVargas.LocalCases.W2MkkStableIncidence
