module

public import DraismaVargas.LocalCases.W2M1kGraphData
public import DraismaVargas.LocalCases.W2M1kLimitMatrix
public import DraismaVargas.LocalCases.W2M1kCommonBalance
public import DraismaVargas.LocalCases.StableGraphFullDimensional

@[expose] public section

/-!
# Figure 33's certified exit, one member at a time

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w2-r2-nd3-M-1k}`, Figure 33 and
Equation (7).

`W2M1kGraphData` identifies each of Figure 33's two divalent members' stable
incidence graphs with the incoming one.  This module turns that into what the
semantic step wants: a
`FullDimensionalSource.FullDimensionalSourcePresentation` on a member, gated on
that member's own nonsingularity, together with the statement that it presents
*that member's* honest labelling.

## Why this is stated per member and not over a family

`W2M1kSourceCandidates.no_common_geometry` forbids putting Figure 33's `M⁽¹⁾`
and `M⁽²⁾` over one datum, so `M⁽²⁾` lives over the branch-swapped datum
`W2M1kSwapped.swappedData` and Figure 33's three members are not a
`BalancedGlobal.Family` over `data` (`W2M1kGaugeFamily` packages them as a
`BalancedGlobal.GaugeFamily` instead).  That obstruction is *not* addressed
here.  What is discharged is everything on the member side of it:

* the transport itself, `StableGraphFullDimensional.presentationOfEquivalence`,
  needs a member-to-member dictionary and two numerical receipts.  Both
  divalent Figure 33 members over one datum carry the two-star's own side
  assignment (`W2M1kStableGraph.divided_right`, `joined_right`), so they expand
  the same target up to the edge-count receipt, which is `simp`-level for *any*
  two wall-side assignments (`expanded_targetEdgeCard`); the source-genus
  receipts are `W2M1kSourceCandidates.divided_sourceGenus` and
  `joined_sourceGenus`;
* the honest labelling is not invented here.  `presentationAt` is gated on
  `W2M1kCommonBalance.LimitColumns.squareMatrix` and carries
  `W2M1kCommonBalance.LimitColumns.labelling` -- the family's own honest
  labelling, the one `LimitColumns.determinant_balance` and `positiveBalance`
  talk about -- so `presentation_eq` is `rfl` against it.

The two costs of the corresponding Figure 34 construction
(`W2MkkStableIncidence`) are both present here as well, and for the same
structural reasons: `LimitMember` carries **no** source-genus field, so
`presentationAt`'s two genus receipts are hypotheses rather than discharged
inside it (§5 discharges them at candidate level), and `LimitColumns` is a
receipt this module consumes and does not build (`W2M1kLimitColumns.limitColumns`
builds it).  Figure 33 adds a third: two positions of the family are not served
by the dictionaries of §2, and §6 records how they are handled.

## Where the members come from

This module defines no member of its own.  The two divalent members are
`W2M1kSourceCandidates.DividedData.candidate` and
`W2M1kSourceCandidates.joinedCandidate`, and the dictionaries of §2 are
`W2M1kGraphData`'s, so nothing below is transported across the branch swap;
`M⁽²⁾` as Figure 33's *member 2* is obtained, here as in `W2M1kStableLift`, by
instantiating the divided definitions at `W2M1kSwapped.swappedData`.
-/

namespace DraismaVargas.LocalCases.W2M1kStableIncidence

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StableSourceMatrix
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary
open ResolutionAwayFromWall
open FullDimensionalSource
open W2M1kSourceCandidates
open W2M1kStableGraph W2M1kStableLift W2M1kRowDescent W2M1kLimitMatrix
open W2M1kGraphData
open W2M1kCommonBalance (LimitMember LimitColumns)

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

/-! ## §2  The member-to-member stable incidence dictionaries

Both are composites through the *incoming* stable graph: that is the whole
content of `LimitChainCore.GraphData.equivalence`, and it is what lets a
presentation cross from one Figure 33 member to another without any statement
about the two members' own geometries. -/

/-- From `M⁽²⁾` to `M⁽³⁾`, through the incoming stable graph. -/
noncomputable def dividedToJoined (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (geometry : GlobalM1k.Geometry data wall) :
    StableGraphIncidence.Equivalence (DividedData.candidate shape divided).datum
      (joinedCandidate star geometry).datum :=
  (dividedEquivalence input shape divided).symm.trans (joinedEquivalence input shape geometry)

/-- From `M⁽³⁾` to `M⁽²⁾`. -/
noncomputable def joinedToDivided (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (geometry : GlobalM1k.Geometry data wall) :
    StableGraphIncidence.Equivalence (joinedCandidate star geometry).datum
      (DividedData.candidate shape divided).datum :=
  (joinedEquivalence input shape geometry).symm.trans (dividedEquivalence input shape divided)

/-! ## §3  The outgoing presentations -/

/-- **Figure 33's certified exit.**  Transport a full-dimensional presentation
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

/-! ### The two divalent members' own exits, with the genus receipts
discharged -/

/-- **`M⁽³⁾`'s outgoing presentation**, from `M⁽²⁾`'s. -/
noncomputable def joinedOutgoingPresentation (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile)
    (geometry : GlobalM1k.Geometry data wall)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (dividedFD : FullDimensionalSourcePresentation
      (DividedData.candidate shape divided).datum coordinate)
    (labelling : StableLengthMatrixLabelling (joinedCandidate star geometry).datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    FullDimensionalSourcePresentation (joinedCandidate star geometry).datum coordinate :=
  outgoingPresentation (data := data) (dividedToJoined input shape divided geometry)
    ((joinedCandidate star geometry).datum_valid input.valid) hConnected hGenus
    (divided_sourceGenus shape divided) (joined_sourceGenus geometry)
    dividedFD labelling hDet

/-- It presents `M⁽³⁾`'s own labelling. -/
theorem joinedOutgoingPresentation_presentation_eq (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile)
    (geometry : GlobalM1k.Geometry data wall)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (dividedFD : FullDimensionalSourcePresentation
      (DividedData.candidate shape divided).datum coordinate)
    (labelling : StableLengthMatrixLabelling (joinedCandidate star geometry).datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    (joinedOutgoingPresentation input shape divided geometry hConnected hGenus
      dividedFD labelling hDet).labelling.presentation = labelling.presentation := rfl

/-- **`M⁽²⁾`'s outgoing presentation**, from `M⁽³⁾`'s. -/
noncomputable def dividedOutgoingPresentation (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile)
    (geometry : GlobalM1k.Geometry data wall)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (joinedFD : FullDimensionalSourcePresentation
      (joinedCandidate star geometry).datum coordinate)
    (labelling : StableLengthMatrixLabelling
      (DividedData.candidate shape divided).datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    FullDimensionalSourcePresentation (DividedData.candidate shape divided).datum coordinate :=
  outgoingPresentation (data := data) (joinedToDivided input shape divided geometry)
    ((DividedData.candidate shape divided).datum_valid input.valid) hConnected hGenus
    (joined_sourceGenus geometry) (divided_sourceGenus shape divided)
    joinedFD labelling hDet

/-- It presents `M⁽²⁾`'s own labelling. -/
theorem dividedOutgoingPresentation_presentation_eq (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile)
    (geometry : GlobalM1k.Geometry data wall)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (joinedFD : FullDimensionalSourcePresentation
      (joinedCandidate star geometry).datum coordinate)
    (labelling : StableLengthMatrixLabelling
      (DividedData.candidate shape divided).datum coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    (dividedOutgoingPresentation input shape divided geometry hConnected hGenus
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

/-! ## §4  The exit at a position of a limit-column receipt

Stating the exit at a position of a `W2M1kCommonBalance.LimitColumns` gates it
on `LimitColumns.squareMatrix` -- the determinant
`W2M1kCommonBalance.LimitColumns.determinant_balance` and `positiveBalance`
talk about -- and makes `presentation_eq` an identity of the family's own
honest `LimitColumns.labelling`.

`LimitMember` carries no source-genus field, so the two genus receipts are
hypotheses here; §3 discharges them for the two divalent candidates, and §5
says how a position's receipt is assembled from them. -/

/-- **Figure 33's certified exit at a position of a limit-column receipt.** -/
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

/-! ## §5  A position's certificate is a dictionary against the incoming datum

Every dictionary used here identifies a member's stable incidence
graph with the **incoming** one, so a member-to-member certificate at any two
positions of a `LimitColumns` is the composite of two of them.  Stating the
exit this way is what lets positions over the incoming datum and the remote
position be supplied by the same interface. -/

/-- The member-to-member certificate assembled from two dictionaries against
the incoming stable graph. -/
noncomputable def positionCertificate {shape : Shape profile}
    (limit : LimitColumns profile shape) (incoming outgoing : Fin 3)
    (incomingDictionary : StableGraphIncidence.Equivalence data (limit.member incoming).datum)
    (outgoingDictionary : StableGraphIncidence.Equivalence data (limit.member outgoing).datum) :
    StableGraphIncidence.Equivalence (limit.member incoming).datum
      (limit.member outgoing).datum :=
  incomingDictionary.symm.trans outgoingDictionary

/-- **The exit at a position, from the two dictionaries and the two genus
receipts.**  For a position over the incoming datum both are already proved:
`W2M1kGraphData.joinedEquivalence` with
`W2M1kSourceCandidates.joined_sourceGenus` for `M⁽³⁾`, and
`W2M1kGraphData.dividedEquivalence` with
`W2M1kSourceCandidates.divided_sourceGenus` for `M⁽²⁾`.  For the remote
position see §6. -/
noncomputable def presentationAtOfDictionaries {shape : Shape profile}
    (limit : LimitColumns profile shape) (incoming outgoing : Fin 3)
    (incomingDictionary : StableGraphIncidence.Equivalence data (limit.member incoming).datum)
    (outgoingDictionary : StableGraphIncidence.Equivalence data (limit.member outgoing).datum)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hIncomingGenus : genus (limit.member incoming).datum.sourceGraph = genus data.sourceGraph)
    (hOutgoingGenus : genus (limit.member outgoing).datum.sourceGraph = genus data.sourceGraph)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate)
    (hDet : (limit.squareMatrix initial outgoing).det ≠ 0) :
    FullDimensionalSourcePresentation (limit.member outgoing).datum coordinate :=
  presentationAt limit incoming outgoing
    (positionCertificate limit incoming outgoing incomingDictionary outgoingDictionary)
    hValid hConnected hGenus hIncomingGenus hOutgoingGenus initial incomingFD hDet

theorem presentationAtOfDictionaries_presentation_eq {shape : Shape profile}
    (limit : LimitColumns profile shape) (incoming outgoing : Fin 3)
    (incomingDictionary : StableGraphIncidence.Equivalence data (limit.member incoming).datum)
    (outgoingDictionary : StableGraphIncidence.Equivalence data (limit.member outgoing).datum)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hIncomingGenus : genus (limit.member incoming).datum.sourceGraph = genus data.sourceGraph)
    (hOutgoingGenus : genus (limit.member outgoing).datum.sourceGraph = genus data.sourceGraph)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate)
    (hDet : (limit.squareMatrix initial outgoing).det ≠ 0) :
    (presentationAtOfDictionaries limit incoming outgoing incomingDictionary outgoingDictionary
        hValid hConnected hGenus hIncomingGenus hOutgoingGenus initial incomingFD
        hDet).labelling.presentation =
      (limit.labelling initial outgoing).presentation := rfl

/-! ## §6  The two positions not served by §2

Nothing below is proved here; this section records the exact shape of the two
inputs that the positions not covered by §2 need, and where they come from.

**Position `0`, the leaf member `M⁽¹⁾`.**  `W2M1kStableLift.leaf_not_wallCandidate`
is a theorem: Base I.a's retained endpoint is a target leaf, carries no wall
direction, and therefore admits no `LimitChainCore.WallCandidate`, hence no
`BackgroundShape`, `LiftData`, `SelectedData` or `GraphData`.  So position `0`
cannot be served by this module's §2 at all.  What it needs is exactly one
object and one receipt (supplied by `W2M1kLeafStableGraph.leafEquivalence` and
`leafPresentationAt`, which §5 accepts verbatim):

* `StableGraphIncidence.Equivalence data (LeafPair.candidate input shape pair).datum`
  -- a branch-vertex bijection plus a row bijection preserving `incidenceCount`,
  built by hand on the `M11SplitStableLift` / `M11SplitRowDescent` pattern.  The
  census already fixes every ingredient.  Its branch vertex above `A₀` is the
  **fresh trivalent** endpoint over `A₀ ∖ {x}`, anchored at any sheet of that
  set -- `pair.second` serves -- of surviving valency three
  (`W2M1kStableGraph.leaf_nonDanglingValency_fresh_branch`), with surviving star
  `{e₂, e₃, new(pair.second)}` (`leaf_nonDanglingIncident_fresh_branch`).  So the
  flag **retains `e₂` and `e₃` and sends `e₁` to the regrown occurrence through
  `pair.second`**, and the one row identity it needs is
  `leaf_new_second_stablePath_eq` (that occurrence lies in `e₁`'s row, which is
  also where `leaf_new_pin_stablePath_eq` puts the other survivor -- Figure 33's
  factor `c⁽¹⁾ = 2c(e₁)`).  Every other endpoint above `A₀` is divalent or
  entirely pruned: the fresh endpoint over `{x}` carries `e₁` and the regrown
  occurrence through `x` (`leaf_nonDanglingValency_fresh_pin` = 2), the retained
  leaf endpoint over `{x, pair.second}` carries the two surviving regrown
  occurrences (`leaf_nonDanglingValency_left_pair` = 2, with
  `leaf_left_vertex_eq` identifying the two sheets' endpoints) and every other
  retained endpoint is empty (`leaf_nonDanglingIncident_left_singleton` and
  `leaf_nonDanglingIncident_left_background`, both via the census's new reader
  `nonDanglingIncident_empty_of_card_one`);
* `genus (LeafPair.candidate input shape pair).datum.sourceGraph = genus data.sourceGraph`
  -- already proved, `W2M1kSourceCandidates.leaf_sourceGenus`.

The obstruction is *only* to the core route: `LimitChainCore.GraphData` asks for
a `SelectedData`, which asks for a `WallCandidate`, which `M⁽¹⁾` has not got.
The object above is strictly weaker than a `GraphData` -- it is what
`GraphData.equivalence` *produces* -- so no part of the core has to be
generalised to accept the leaf member.  Its `row` field is not free either: it
must be the leaf member's own bespoke row-descent bijection, the one the leaf
limit-matrix evaluations are stated against, or the retained columns and the
dictionary would be reading different rows.

With those two in hand, position `0` enters §5 verbatim; nothing in §3, §4 or §5
has to change to accept it.  Note that the leaf member's outgoing target is
`T_∅` and not `T_2` (`leaf_target_valencies` = `(1, 3)`), which is *not* an
obstruction here: `expanded_targetEdgeCard` compares two wall-side assignments
of one `target`, and all three Figure 33 members expand the same `target` at the
same `wall`.

**Position `1`, the remote copy of `M⁽²⁾`.**  Position `1` is the one
`GlobalM1k.swappedCandidates` fills with `SecondPattern.remoteCertified`, over
`W2M1kSwapped.swappedData star geometry`, which is by definition
`(ResolutionM11.wallBranchSwap data wall (M11RemoteCandidates.branchRoot star 1)
(M11RemoteCandidates.branchRoot_ne star 1) geometry.first geometry.second
geometry.first_second).apply` -- a global sheet relabelling of `data`.  Its
dictionary against the incoming stable graph is therefore the composite

* `StableGraphIncidence.sheetRelabel relabeling input.valid.1 :
  Equivalence data (swappedData star geometry)`, the relabelling bridge, with
* `W2M1kGraphData.dividedEquivalence` instantiated at the swapped datum, the
  swapped profile, shape and `DividedData` that
  `W2M1kSwapped.AlignedProfile.swappedSecondPattern` supplies,

and its genus receipt is `divided_sourceGenus` at the swapped datum composed
with `LaplacianEquiv.genus_eq` applied to the relabelling's own
`GluingDatum.SheetRelabeling.sourceGraphLaplacianEquiv`.  **This is the same
general statement M-kk needs** -- the pair
`Nonempty (StableGraphIncidence.Equivalence data relabeling.apply)` together
with `genus relabeling.apply.sourceGraph = genus data.sourceGraph`, for an
arbitrary compatible relabelling, with no case data whatsoever.  M-1k needs no
bespoke variant of it: the only M-1k-specific step is instantiating the
divided definitions of `W2M1kGraphData` at `W2M1kSwapped.swappedData`, which is
substitution, not a new proof.
-/

end DraismaVargas.LocalCases.W2M1kStableIncidence
