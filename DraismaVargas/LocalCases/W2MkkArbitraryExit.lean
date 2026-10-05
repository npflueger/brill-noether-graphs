module

public import DraismaVargas.LocalCases.W2MkkIncomingMatching
public import DraismaVargas.LocalCases.FiniteAtlasMarch

@[expose] public section

/-!
# Figure 34's certified exit, and the arbitrary incoming `w2Mkk` cover

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-kk}`, Figure 34 and
Equation (8).

`W2MkkLimitColumns` inhabits `W2MkkCommonBalance.LimitColumns` on the case's
actual input, in both orientations, so Equation (8) and its positive balance
hold unconditionally.  This module turns that balance into the **certified
exit**: a valid outgoing member of strictly opposite determinant sign, a
positive rational step that stays in the positive cone, the exact affine metric
equation, and an explicit cleared rank-one pencil on the selected member's own
source subdivision.

## Why this is stated over `LimitMember` and not over a family

`W2MkkSourceCandidates.no_common_geometry` forbids putting Figure 34's two
detaching members over one gluing datum, so the three members are not a
`BalancedGlobal.PresentedFamily`: `M⁽¹⁾` or `M⁽²⁾` -- whichever the incoming
datum does not carry -- lives over `W2MkkTransport.swapRelabeling …|>.apply`.
`BalancedGlobal.GaugeFamily` was introduced for exactly that and would serve,
but it asks for `candidate : ∀ i, BalancedGlobal.Candidate target degree
(base i) wall`, i.e. for each member's *occurrence-level* data, and
`W2MkkCommonBalance.LimitMember` deliberately keeps only the outgoing datum, the
validity implication, the row bijection and the retained columns.

Nothing is lost, and the reason is worth recording because it is why
`LimitMember` was given that shape: what
`BalancedGlobal.Candidate.clearedPencil` actually consumes of a candidate is

* `candidate.datum.Valid`,
* connectedness and genus zero of the **expanded** target, and
* one vertex of it,

and every one of those is available from a `LimitMember` directly --
`valid_of_old`, `W2MkkStableIncidence.expanded_targetConnected` /
`expanded_targetGenus` (the expansion of a connected genus-zero target, for
*any* side assignment), and `TargetExpansion.oldVertex`.  So the pencil is
built here at datum level, exactly as `W3Nd2PositiveExit.exists_clearedPencil`
builds it, and the exit needs no family structure at all.  This is what the
position-freeness of `LimitMember` buys.

## What is proved

* `exists_clearedPencil` -- positive rational coordinates on any Figure 34
  member clear, at the datum's own `rationalRealizationScale`, to an integral
  realization carrying the degree-`degree` rank-one pencil.
* `outgoingVelocity`, `outgoingVelocity_system` -- the canonical chart velocity
  at a nonsingular member, which is what discharges the compatible-length-system
  gate.
* `exists_positive_exit_with_pencil` -- **the exit**, at every position of the
  receipt, remote included.
* `exists_positive_exit_with_presentation` -- the same with an outgoing
  `FullDimensionalSource.FullDimensionalSourcePresentation`, taking the
  per-position stable-incidence dictionary and source-genus receipt as
  hypotheses; `localMember_dictionary`, `joinedMember_dictionary` and the two
  `*OrientationDictionary` families discharge them at the two positions over the
  incoming datum, and `remoteMember_dictionary_of` reduces the third to
  `RemoteDictionary`.
* `initialLabelling`, `labelling_self`, `squareMatrix_self`,
  `wallColumn_initialLabelling` -- one identified member's honest labelling
  induces the common square coordinate order, and transport to the receipt's
  position `0` and back is the identity on it.  No stable-incidence dictionary
  enters this cancellation: `W2MkkCommonBalance.LimitColumns.labelling` builds
  each member's row map out of `LimitMember.row`, so it is between the receipt's
  own row bijections.  (`W3Nd3ArbitraryExit` and `W2PArbitraryExit` route the
  same cancellation through `between`, because their families carry no row
  field.)
* `exists_positive_exit_in_original_coordinates` -- the exit against a supplied
  original matrix and original wall column.  The identification of an
  arbitrary incoming `w2Mkk` cover with a named Figure 34 member, carrying an
  honest presentation in the original coordinates, is `W2MkkIncomingMatching`
  and `W2MkkGraphTracking.exists_matched_tracking`.
* `firstGaugeFamily` / `secondGaugeFamily` -- Figure 34 packaged as a
  `BalancedGlobal.GaugeFamily`, which is what `WallProgress.WallInput.family`
  is.  Not used by the exit, which is datum-level; it is the gauge family that
  `A04MoreTags` routes for `w2Mkk`, stated here because the members are.

## What the remote slot needs, exactly

`RemoteDictionary` names it: a `StableGraphIncidence.Equivalence` between the
incoming datum and the branch-swapped copy `W2MkkTransport.swapRelabeling
profile other hOther |>.apply`.  `W2MkkGraphData.detachEquivalence` supplies the
dictionary from the *swapped* datum to the remote member
(`detachEquivalence (W2MkkTransport.swapInput …) (W2MkkTransport.swapShape …)
(W2MkkLimitColumns.remoteDetach …)`), and `W2MkkTransport.swapGauge` carries the
stable **rows** and the whole natural matrix across the swap
(`LimitChainCore.Gauge.row`, `Gauge.matrix_gauge`); the remaining input is the
branch half -- the flag dictionary at the swapped datum's own branch vertex,
i.e. the statement that the branch swap is a stable-incidence isomorphism and
not merely a row bijection.  `SheetRelabelIncidence` supplies exactly that, for
an arbitrary compatible sheet relabelling, so the dictionaries extend to all
three positions and `exists_positive_exit_with_presentation` applies
unconditionally (as `A04MoreTags` uses it).

Note that the exit itself already covers the remote outgoing member.
`exists_positive_exit_with_pencil` is proved at every position of the
receipt, remote included, because the pencil is datum-level.  The remote
dictionary is needed only for the extra clause "and the outgoing member carries
a full-dimensional presentation in the incoming coordinates".
-/

namespace DraismaVargas.LocalCases.W2MkkArbitraryExit

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StableSourceMatrix
open ResolutionM11
open FullDimensionalSource
open W2MkkSourceCandidates
open W2MkkCommonBalance (LimitMember LimitColumns)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  {shape : Shape profile}

/-! ## §1  The cleared pencil at any Figure 34 member -/

/-- **Positive coordinates clear at a Figure 34 member.**  Only the member's
outgoing datum enters, so this holds at the remote position as well as at the
two over the incoming datum. -/
theorem exists_clearedPencil (limit : LimitColumns profile shape) (position : Fin 3)
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (labelling : StableLengthMatrixLabelling (limit.member position).datum coordinate)
    (coordinates : coordinate → ℚ) (hPositive : ∀ i, 0 < coordinates i) :
    ∃ realization : (limit.member position).datum.IntegralRealization,
      ∃ scale : ℕ, 0 < scale ∧
        (∀ column, (realization.targetLength (labelling.targetEdge column) : ℚ) =
          (scale : ℚ) * coordinates column) ∧
        Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  classical
  let datum := (limit.member position).datum
  let targetLength : (TargetExpansion.graph target wall (limit.member position).right).edges → ℚ :=
    fun edge ↦ coordinates (labelling.targetEdge.symm edge)
  have hTargetPositive : ∀ edge, 0 < targetLength edge := fun edge ↦ hPositive _
  let realization :=
    GluingDatum.IntegralRealization.ofPositiveRational datum targetLength hTargetPositive
  refine ⟨realization, datum.rationalRealizationScale targetLength,
    datum.rationalRealizationScale_pos targetLength, ?_, ?_⟩
  · intro column
    change ((GluingDatum.IntegralRealization.ofPositiveRational datum targetLength
      hTargetPositive).targetLength (labelling.targetEdge column) : ℚ) = _
    rw [GluingDatum.IntegralRealization.ofPositiveRational_targetLength_cast]
    simp [targetLength]
  · exact (realization.bnExists_and_effective_of_connected_genus_zero_target
      ((limit.member position).valid_of_old hValid).1
      (W2MkkStableIncidence.expanded_targetConnected hConnected (limit.member position).right)
      (W2MkkStableIncidence.expanded_targetGenus hGenus (limit.member position).right)
      (TargetExpansion.oldVertex target wall)).1

/-! ## §2  The canonical outgoing chart velocity -/

section Velocity

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- The chart velocity at an outgoing member, solving the compatible length
system against the incoming one. -/
noncomputable def outgoingVelocity (limit : LimitColumns profile shape)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (incoming : Fin 3) (incomingVelocity : coordinate → ℚ) (outgoing : Fin 3) :
    coordinate → ℚ :=
  FiniteAtlasMarch.chartCoordinates (limit.squareMatrix initial outgoing)
    ((limit.squareMatrix initial incoming).mulVec incomingVelocity)

/-- It does solve it, whenever the outgoing member is nonsingular -- which the
selected member always is. -/
theorem outgoingVelocity_system (limit : LimitColumns profile shape)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (incoming : Fin 3) (incomingVelocity : coordinate → ℚ) (outgoing : Fin 3)
    (hDet : (limit.squareMatrix initial outgoing).det ≠ 0) :
    (limit.squareMatrix initial incoming).mulVec incomingVelocity =
      (limit.squareMatrix initial outgoing).mulVec
        (outgoingVelocity limit initial incoming incomingVelocity outgoing) :=
  (FiniteAtlasMarch.mulVec_chartCoordinates _ hDet _).symm

end Velocity

/-! ## §3  The certified exit -/

section Exit

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **Figure 34's certified exit.**  Equation (8) -- `W2MkkCommonBalance`'s
`positiveBalance`, discharged on the case's actual input by
`W2MkkLimitColumns.limitColumns` -- selects a genuinely nonsingular
opposite-sign member; the one-column cone-wall calculation supplies the positive
rational step, the exact affine metric equation and the whole-segment
positivity; and the member's own datum clears the rank-one pencil.

Only the chosen incoming member is assumed nonsingular.  No assumption is made
about which Figure 34 position the selected outgoing member is, so the remote
position is covered like the other two. -/
theorem exists_positive_exit_with_pencil (limit : LimitColumns profile shape)
    (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 3) (hIncoming : (limit.squareMatrix initial incoming).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (limit.wallColumn initial) = 0)
    (hzpos : ∀ i, i ≠ limit.wallColumn initial → 0 < z i)
    (hDirection : incomingVelocity (limit.wallColumn initial) < 0) :
    ∃ outgoing : Fin 3,
      (limit.member outgoing).datum.Valid ∧
      (limit.squareMatrix initial incoming).det *
        (limit.squareMatrix initial outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity limit initial incoming incomingVelocity
          outgoing) i) ∧
        (limit.squareMatrix initial outgoing).mulVec
            (z + t • outgoingVelocity limit initial incoming incomingVelocity outgoing) =
          (limit.squareMatrix initial incoming).mulVec z +
            t • (limit.squareMatrix initial incoming).mulVec incomingVelocity ∧
        ∃ realization : (limit.member outgoing).datum.IntegralRealization,
          ∃ scale : ℕ, 0 < scale ∧
            (∀ column,
              (realization.targetLength
                ((limit.labelling initial outgoing).targetEdge column) : ℚ) =
                (scale : ℚ) * (z + t • outgoingVelocity limit initial incoming
                  incomingVelocity outgoing) column) ∧
            Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  obtain ⟨outgoing, hSign⟩ :=
    BalancingValencyTwo.exists_opposite_of_positiveBalance
      (limit.positiveBalance input initial) hIncoming
  have hOutDet : (limit.squareMatrix initial outgoing).det ≠ 0 :=
    BalancedGlobal.det_ne_zero_of_mul_det_neg hSign
  obtain ⟨δ, hδ, hStep⟩ := crosses_into_positive_cone
    (limit.matrices_agree initial incoming outgoing) hSign hz hzpos
    (outgoingVelocity_system limit initial incoming incomingVelocity outgoing hOutDet)
    hDirection
  refine ⟨outgoing, (limit.member outgoing).valid_of_old input.valid, hSign, δ, hδ, ?_⟩
  intro t ht htδ
  obtain ⟨hPositive, hMetric⟩ := hStep t ht htδ
  exact ⟨hPositive, hMetric,
    exists_clearedPencil limit outgoing input.valid hConnected hGenus
      (limit.labelling initial outgoing) _ hPositive⟩

end Exit


/-! ## §4  The exit with an outgoing full-dimensional presentation

`W2MkkStableIncidence.presentationAt` transports a full-dimensional presentation
from one position of the receipt to another along a stable-incidence dictionary,
gated on the outgoing position's own determinant, and carries the family's own
honest labelling.  The dictionary and the source-genus receipt are taken here as
per-position hypotheses; §5 discharges both at the two positions over the
incoming datum, and says exactly what the remote one needs. -/

section Presented

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The certified exit with an outgoing full-dimensional source.**  Everything
of `exists_positive_exit_with_pencil`, plus a
`FullDimensionalSource.FullDimensionalSourcePresentation` on the selected
outgoing member presenting the family's own honest labelling.  This is the
shape `W3Nd3ArbitraryExit.exists_member_positive_exit_with_pencil` has, at
`Fin 3`. -/
theorem exists_positive_exit_with_presentation (limit : LimitColumns profile shape)
    (input : W2SourceInput data star)
    (dictionary : ∀ position : Fin 3,
      StableGraphIncidence.Equivalence data (limit.member position).datum)
    (sourceGenus : ∀ position : Fin 3,
      genus (limit.member position).datum.sourceGraph = genus data.sourceGraph)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate)
    (hIncoming : (limit.squareMatrix initial incoming).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (limit.wallColumn initial) = 0)
    (hzpos : ∀ i, i ≠ limit.wallColumn initial → 0 < z i)
    (hDirection : incomingVelocity (limit.wallColumn initial) < 0) :
    ∃ outgoing : Fin 3,
      ∃ outgoingFD : FullDimensionalSourcePresentation (limit.member outgoing).datum coordinate,
        outgoingFD.labelling = limit.labelling initial outgoing ∧
        (limit.squareMatrix initial incoming).det *
          (limit.squareMatrix initial outgoing).det < 0 ∧
        ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (z + t • outgoingVelocity limit initial incoming incomingVelocity
            outgoing) i) ∧
          (limit.squareMatrix initial outgoing).mulVec
              (z + t • outgoingVelocity limit initial incoming incomingVelocity outgoing) =
            (limit.squareMatrix initial incoming).mulVec z +
              t • (limit.squareMatrix initial incoming).mulVec incomingVelocity ∧
          ∃ realization : (limit.member outgoing).datum.IntegralRealization,
            ∃ scale : ℕ, 0 < scale ∧
              (∀ column,
                (realization.targetLength
                  ((limit.labelling initial outgoing).targetEdge column) : ℚ) =
                  (scale : ℚ) * (z + t • outgoingVelocity limit initial incoming
                    incomingVelocity outgoing) column) ∧
              Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  obtain ⟨outgoing, _hValid, hSign, δ, hδ, hStep⟩ :=
    exists_positive_exit_with_pencil limit input initial hConnected hGenus incoming hIncoming
      z incomingVelocity hz hzpos hDirection
  have hOutDet : (limit.squareMatrix initial outgoing).det ≠ 0 :=
    BalancedGlobal.det_ne_zero_of_mul_det_neg hSign
  exact ⟨outgoing,
    W2MkkStableIncidence.presentationAt limit incoming outgoing
      ((dictionary incoming).symm.trans (dictionary outgoing)) input.valid hConnected hGenus
      (sourceGenus incoming) (sourceGenus outgoing) initial incomingFD hOutDet,
    rfl, hSign, δ, hδ, hStep⟩

end Presented

/-! ## §5  The dictionaries: two discharged here, the third reduced to `RemoteDictionary` -/

section Dictionaries

variable (input : W2SourceInput data star) (shape : Shape profile)

/-- The detaching member over the incoming datum has the incoming stable
incidence graph. -/
noncomputable def localMember_dictionary (detach : DetachData profile) :
    StableGraphIncidence.Equivalence data
      (W2MkkLimitColumns.localMember input shape detach).datum :=
  W2MkkGraphData.detachEquivalence input shape detach

/-- `M⁽³⁾` over the incoming datum has the incoming stable incidence graph. -/
noncomputable def joinedMember_dictionary (distinguished : Fin degree) :
    StableGraphIncidence.Equivalence data
      (W2MkkLimitColumns.joinedMember input shape distinguished).datum :=
  W2MkkGraphData.joinedEquivalence input shape distinguished

theorem localMember_sourceGenus (detach : DetachData profile) :
    genus (W2MkkLimitColumns.localMember input shape detach).datum.sourceGraph =
      genus data.sourceGraph :=
  detach_sourceGenus shape detach

theorem joinedMember_sourceGenus (distinguished : Fin degree) :
    genus (W2MkkLimitColumns.joinedMember input shape distinguished).datum.sourceGraph =
      genus data.sourceGraph :=
  joined_sourceGenus profile distinguished

/-- **What the remote Figure 34 slot needs, and nothing more.**  A
stable-incidence dictionary between the incoming datum and its branch-swapped
copy.  `W2MkkTransport.swapGauge` already carries the stable rows and the whole
natural matrix across the swap; this is the branch half of the same statement. -/
def RemoteDictionary (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) : Prop :=
  Nonempty (StableGraphIncidence.Equivalence data
    (W2MkkTransport.swapRelabeling profile other hOther).apply)

/-- **And it suffices.**  Composed with `W2MkkGraphData.detachEquivalence` over
the swapped datum, a remote dictionary gives the remote member the incoming
stable incidence graph, which is the only clause of
`exists_positive_exit_with_presentation` the remote slot needs beyond the
member's own data. -/
noncomputable def remoteMember_dictionary_of (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other)
    (swap : StableGraphIncidence.Equivalence data
      (W2MkkTransport.swapRelabeling profile other hOther).apply) :
    StableGraphIncidence.Equivalence data
      (W2MkkLimitColumns.remoteMember input shape other hOther).datum :=
  swap.trans (W2MkkGraphData.detachEquivalence
    (W2MkkTransport.swapInput input other hOther)
    (W2MkkTransport.swapShape shape input.valid.1 other hOther)
    (W2MkkLimitColumns.remoteDetach input shape other hOther))

/-- The remote member's source genus, which the same composition supplies with
no extra input: a detaching member over any datum preserves it. -/
theorem remoteMember_sourceGenus (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other)
    (hSwapGenus : genus (W2MkkTransport.swapRelabeling profile other hOther).apply.sourceGraph =
      genus data.sourceGraph) :
    genus (W2MkkLimitColumns.remoteMember input shape other hOther).datum.sourceGraph =
      genus data.sourceGraph :=
  (detach_sourceGenus (W2MkkTransport.swapShape shape input.valid.1 other hOther)
    (W2MkkLimitColumns.remoteDetach input shape other hOther)).trans hSwapGenus

end Dictionaries



/-! ## §9  The two orientations' dictionary families

`W2MkkLimitColumns.limitColumns` branches on which endpoint block the pinned
sheet lies in, and the two branches put the local detaching member at different
Figure 34 positions.  In each branch two of the three positions are over the
incoming datum and one is remote, so each family is built from §5's two
discharged dictionaries and one supplied remote one. -/

section Families

variable (input : W2SourceInput data star) (shape : Shape profile)
  (distinguished : Fin degree)
  (hConnected : graph_connected target) (hGenus : genus target = 0)

/-- **Base II.2.1.M orientation.**  Position `0` is the local `M⁽¹⁾`, position
`1` the remote `M⁽²⁾`, position `2` is `M⁽³⁾`. -/
noncomputable def firstOrientationDictionary (member : FirstMember profile)
    (remote : StableGraphIncidence.Equivalence data
      (W2MkkTransport.swapRelabeling profile (secondSheet profile)
        (W2MkkTransport.secondSheet_together profile)).apply) :
    ∀ position : Fin 3, StableGraphIncidence.Equivalence data
      ((W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
        hGenus).member position).datum
  | 0 => localMember_dictionary input shape member.toDetachData
  | 1 => remoteMember_dictionary_of input shape (secondSheet profile)
      (W2MkkTransport.secondSheet_together profile) remote
  | 2 => joinedMember_dictionary input shape distinguished

theorem firstOrientationSourceGenus (member : FirstMember profile)
    (hSwapGenus : genus (W2MkkTransport.swapRelabeling profile (secondSheet profile)
      (W2MkkTransport.secondSheet_together profile)).apply.sourceGraph =
      genus data.sourceGraph) :
    ∀ position : Fin 3,
      genus ((W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
        hGenus).member position).datum.sourceGraph = genus data.sourceGraph
  | 0 => localMember_sourceGenus input shape member.toDetachData
  | 1 => remoteMember_sourceGenus input shape (secondSheet profile)
      (W2MkkTransport.secondSheet_together profile) hSwapGenus
  | 2 => joinedMember_sourceGenus input shape distinguished

/-- **Base II.2.2.M orientation.**  Position `0` is the remote `M⁽¹⁾`, position
`1` the local `M⁽²⁾`, position `2` is `M⁽³⁾`. -/
noncomputable def secondOrientationDictionary (member : SecondMember profile)
    (remote : StableGraphIncidence.Equivalence data
      (W2MkkTransport.swapRelabeling profile (firstSheet profile)
        (W2MkkTransport.firstSheet_together profile)).apply) :
    ∀ position : Fin 3, StableGraphIncidence.Equivalence data
      ((W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
        hGenus).member position).datum
  | 0 => remoteMember_dictionary_of input shape (firstSheet profile)
      (W2MkkTransport.firstSheet_together profile) remote
  | 1 => localMember_dictionary input shape member.toDetachData
  | 2 => joinedMember_dictionary input shape distinguished

theorem secondOrientationSourceGenus (member : SecondMember profile)
    (hSwapGenus : genus (W2MkkTransport.swapRelabeling profile (firstSheet profile)
      (W2MkkTransport.firstSheet_together profile)).apply.sourceGraph =
      genus data.sourceGraph) :
    ∀ position : Fin 3,
      genus ((W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
        hGenus).member position).datum.sourceGraph = genus data.sourceGraph
  | 0 => remoteMember_sourceGenus input shape (firstSheet profile)
      (W2MkkTransport.firstSheet_together profile) hSwapGenus
  | 1 => localMember_sourceGenus input shape member.toDetachData
  | 2 => joinedMember_sourceGenus input shape distinguished

end Families

/-! ## §7  Reading the exit in the incoming cover's own coordinates

One identified member's honest labelling fixes the common square coordinate
order, and transport to the receipt's position `0` and back is the identity on
it.  Unlike `W3Nd3ArbitraryExit` and `W2PArbitraryExit`, no stable-incidence
dictionary enters here: `W2MkkCommonBalance.LimitColumns.labelling` builds each
member's row map out of `LimitMember.row`, which is part of the receipt, so the
cancellation is between the receipt's own row bijections. -/

section OriginalCoordinates

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- A stable length-matrix labelling is its two equivalences. -/
private theorem labelling_eq_of_fields {datum : GluingDatum target degree}
    {first second : StableLengthMatrixLabelling datum coordinate}
    (hTarget : first.targetEdge = second.targetEdge) (hRow : first.row = second.row) :
    first = second := by
  cases first
  cases second
  cases hTarget
  cases hRow
  rfl

/-- One identified member's honest labelling, read back at position `0`: the
only source of the common square coordinate order. -/
noncomputable def initialLabelling (limit : LimitColumns profile shape) (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate) :
    StableLengthMatrixLabelling (limit.member 0).datum coordinate where
  row := ((limit.member 0).row).symm.trans
    (((limit.member incoming).row).trans incomingFD.labelling.row)
  targetEdge := incomingFD.labelling.targetEdge.trans
    ((limit.columnEquiv incoming).symm.trans (limit.columnEquiv 0))

/-- **Transport to position `0` and back is the identity.**  Both the row
bijection and the occurrence dictionary cancel. -/
theorem labelling_self (limit : LimitColumns profile shape) (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate) :
    limit.labelling (initialLabelling limit incoming incomingFD) incoming =
      incomingFD.labelling := by
  refine labelling_eq_of_fields ?_ ?_
  · ext column
    simp [LimitColumns.labelling, LimitColumns.targetCoordinates, initialLabelling]
  · ext path
    simp [LimitColumns.labelling, LimitColumns.sourceCoordinates, initialLabelling]

/-- Hence the identified member's own honest square matrix is its own. -/
theorem squareMatrix_self (limit : LimitColumns profile shape) (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate) :
    limit.squareMatrix (initialLabelling limit incoming incomingFD) incoming =
      GluingDatum.LengthMatrixPresentation.matrix incomingFD.labelling.presentation := by
  unfold LimitColumns.squareMatrix
  rw [labelling_self limit incoming incomingFD]

/-- And it is nonsingular, because the identified member is full-dimensional. -/
theorem squareMatrix_self_ne_zero (limit : LimitColumns profile shape) (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate) :
    (limit.squareMatrix (initialLabelling limit incoming incomingFD) incoming).det ≠ 0 := by
  rw [squareMatrix_self limit incoming incomingFD]
  exact incomingFD.det_ne_zero

/-- **The common wall coordinate is the identified member's own wall column.**
Composed with the column clause of the incoming-member identification this is
the *original* contracted column of the incoming target. -/
theorem wallColumn_initialLabelling (limit : LimitColumns profile shape) (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate) :
    limit.wallColumn (initialLabelling limit incoming incomingFD) =
      incomingFD.labelling.targetEdge.symm
        (occurrenceEquiv target wall (limit.member incoming).right none) := by
  simp [LimitColumns.wallColumn, LimitColumns.targetCoordinates, initialLabelling,
    LimitColumns.columnEquiv]

end OriginalCoordinates


/-! ## §8  The exit against the incoming cover's own matrix

`originalMatrix` and `originalWallColumn` are exactly what the incoming-member
identification pins to the incoming cover's own length matrix and its own
contracted column; the theorem is stated against them so that the two halves
compose without either mentioning the other's hypotheses. -/

section Original

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The certified exit in the original coordinates.**  Given one Figure 34
position carrying a full-dimensional presentation whose length matrix is the
incoming cover's and whose wall column is the incoming cover's own contracted
column, Equation (8) selects a valid outgoing member of strictly opposite
determinant sign against the *original* matrix; the whole segment stays
positive; the affine metric equation is the original one; and the cleared
rank-one pencil sits on the selected member's actual source subdivision.

The family has three positions (`Fin 3`), and the per-position stable-incidence
dictionary is an explicit argument because one Figure 34 position is remote
(§5). -/
theorem exists_positive_exit_in_original_coordinates (limit : LimitColumns profile shape)
    (input : W2SourceInput data star)
    (dictionary : ∀ position : Fin 3,
      StableGraphIncidence.Equivalence data (limit.member position).datum)
    (sourceGenus : ∀ position : Fin 3,
      genus (limit.member position).datum.sourceGraph = genus data.sourceGraph)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate)
    (originalMatrix : Matrix coordinate coordinate ℚ)
    (hMatrix : GluingDatum.LengthMatrixPresentation.matrix incomingFD.labelling.presentation =
      originalMatrix)
    (originalWallColumn : coordinate)
    (hWall : incomingFD.labelling.targetEdge.symm
      (occurrenceEquiv target wall (limit.member incoming).right none) = originalWallColumn)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z originalWallColumn = 0)
    (hzpos : ∀ i, i ≠ originalWallColumn → 0 < z i)
    (hDirection : incomingVelocity originalWallColumn < 0) :
    ∃ outgoing : Fin 3,
      ∃ outgoingFD : FullDimensionalSourcePresentation (limit.member outgoing).datum coordinate,
        Nonempty (StableGraphIncidence.Equivalence data (limit.member outgoing).datum) ∧
        originalMatrix.det *
          (GluingDatum.LengthMatrixPresentation.matrix
            outgoingFD.labelling.presentation).det < 0 ∧
        ∃ velocity : coordinate → ℚ, ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (z + t • velocity) i) ∧
          (GluingDatum.LengthMatrixPresentation.matrix
              outgoingFD.labelling.presentation).mulVec (z + t • velocity) =
            originalMatrix.mulVec z + t • originalMatrix.mulVec incomingVelocity ∧
          ∃ realization : (limit.member outgoing).datum.IntegralRealization,
            ∃ scale : ℕ, 0 < scale ∧
              (∀ column,
                (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                  (scale : ℚ) * (z + t • velocity) column) ∧
              Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  have hWallColumn : limit.wallColumn (initialLabelling limit incoming incomingFD) =
      originalWallColumn :=
    (wallColumn_initialLabelling limit incoming incomingFD).trans hWall
  have hIncomingMatrix :
      limit.squareMatrix (initialLabelling limit incoming incomingFD) incoming =
        originalMatrix := (squareMatrix_self limit incoming incomingFD).trans hMatrix
  obtain ⟨outgoing, outgoingFD, hLabelling, hSign, δ, hδ, hStep⟩ :=
    exists_positive_exit_with_presentation limit input dictionary sourceGenus
      (initialLabelling limit incoming incomingFD) hConnected hGenus incoming incomingFD
      (squareMatrix_self_ne_zero limit incoming incomingFD) z incomingVelocity
      (hWallColumn ▸ hz) (hWallColumn ▸ hzpos) (hWallColumn ▸ hDirection)
  have hOutMatrix : GluingDatum.LengthMatrixPresentation.matrix
      outgoingFD.labelling.presentation =
      limit.squareMatrix (initialLabelling limit incoming incomingFD) outgoing := by
    rw [hLabelling]
    rfl
  refine ⟨outgoing, outgoingFD, ⟨dictionary outgoing⟩, ?_,
    outgoingVelocity limit (initialLabelling limit incoming incomingFD) incoming
      incomingVelocity outgoing, δ, hδ, ?_⟩
  · rw [hOutMatrix, ← hIncomingMatrix]
    exact hSign
  · intro t ht htδ
    obtain ⟨hPositive, hMetric, hPencil⟩ := hStep t ht htδ
    refine ⟨hPositive, ?_, ?_⟩
    · rw [hOutMatrix, ← hIncomingMatrix]
      exact hMetric
    · rw [hLabelling]
      exact hPencil

end Original


/-! ## §11  Figure 34 as a `BalancedGlobal.GaugeFamily`

`WallProgress.WallInput.family` is a `BalancedGlobal.GaugeFamily` -- one base
datum per member -- which is exactly the shape a case with a remote member
needs, and M-kk is such a case.  Packaging Figure 34 into one is mechanical, and
the only thing it asks for beyond `W2MkkCommonBalance.LimitColumns` is the three
**candidates**: `LimitMember` deliberately keeps only the outgoing datum, so the
occurrence-level `BalancedGlobal.Candidate` that `GaugeFamily.candidate` wants
has to be re-supplied alongside the receipt.  Every field below is then
`rfl`-level against the receipt (`presentation_matrix`), and no hypothesis is
added.

This is not used by §1--§10 -- the exit is datum-level and needs no family -- and
it does not import `WallProgress`; it is the gauge family for `w2Mkk`, stated
where the members are.  Write the `presentation` field with term-mode equations: a
tactic-mode `intro i; match i with …` does not refine the expected type per
branch and the ensuing `isDefEq` on `LimitColumns.squareMatrix` does not
terminate within the default heartbeat budget. -/

section Gauge

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Base II.2.1.M's three base data: the incoming datum, the branch-swapped
copy, the incoming datum. -/
noncomputable def firstBase (profile : W2R2SourceProfile.SourceProfile data star block) :
    Fin 3 → GluingDatum target degree
  | 0 => data
  | 1 => (W2MkkTransport.swapRelabeling profile (secondSheet profile)
      (W2MkkTransport.secondSheet_together profile)).apply
  | 2 => data

/-- Its three candidates, each over its own base. -/
noncomputable def firstCandidate (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (member : FirstMember profile) :
    ∀ i : Fin 3, BalancedGlobal.Candidate target degree (firstBase profile i) wall
  | 0 => member.toDetachData.candidate shape
  | 1 => (W2MkkLimitColumns.remoteDetach input shape (secondSheet profile)
      (W2MkkTransport.secondSheet_together profile)).candidate
      (W2MkkTransport.swapShape shape input.valid.1 (secondSheet profile)
        (W2MkkTransport.secondSheet_together profile))
  | 2 => joinedCandidate profile distinguished

/-- The receipt's own honest presentations, typed at those candidates. -/
noncomputable def firstPresentation (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (member : FirstMember profile)
    (initial : StableLengthMatrixLabelling
      ((W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
        hGenus).member 0).datum coordinate) :
    ∀ i : Fin 3,
      (firstCandidate input shape distinguished member i).datum.LengthMatrixPresentation
        coordinate
  | 0 => ((W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
      hGenus).labelling initial 0).presentation
  | 1 => ((W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
      hGenus).labelling initial 1).presentation
  | 2 => ((W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
      hGenus).labelling initial 2).presentation

omit [Fintype coordinate] in
theorem firstPresentation_matrix (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (member : FirstMember profile)
    (initial : StableLengthMatrixLabelling
      ((W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
        hGenus).member 0).datum coordinate) (i : Fin 3) :
    GluingDatum.LengthMatrixPresentation.matrix
        (firstPresentation input shape distinguished hConnected hGenus member initial i) =
      (W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
        hGenus).squareMatrix initial i := by
  fin_cases i <;> rfl

/-- **Figure 34 as a gauge family, Base II.2.1.M orientation.**  The weights are
the members' own new-edge indices `k₁-1`, `k₂-1`, `k₁+k₂`, the balance is
Equation (8), and the off-wall agreement is the retained-column receipt. -/
noncomputable def firstGaugeFamily (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (member : FirstMember profile)
    (initial : StableLengthMatrixLabelling
      ((W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
        hGenus).member 0).datum coordinate) :
    BalancedGlobal.GaugeFamily (coordinate := coordinate) 3 data wall where
  base := firstBase profile
  valid_of_old := fun i hValid ↦ by
    match i with
    | 0 => exact hValid
    | 1 => exact (W2MkkTransport.swapRelabeling profile (secondSheet profile)
             (W2MkkTransport.secondSheet_together profile)).valid hValid
    | 2 => exact hValid
  candidate := firstCandidate input shape distinguished member
  presentation := firstPresentation input shape distinguished hConnected hGenus member initial
  wallColumn := (W2MkkLimitColumns.firstOrientation input shape member distinguished
    hConnected hGenus).wallColumn initial
  weight := ![(data.sourceEdgeIndex profile.first.1 : ℚ) - 1,
    (data.sourceEdgeIndex profile.second.1 : ℚ) - 1,
    (data.sourceEdgeIndex profile.first.1 : ℚ) + (data.sourceEdgeIndex profile.second.1 : ℚ)]
  positiveBalance := by
    have h := (W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
      hGenus).positiveBalance input initial
    exact ⟨h.1, by simpa only [firstPresentation_matrix] using h.2⟩
  agreeOffWall := fun first second ↦ by
    rw [firstPresentation_matrix, firstPresentation_matrix]
    exact (W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
      hGenus).matrices_agree initial first second

/-- Base II.2.2.M's three base data: the branch-swapped copy, the incoming
datum, the incoming datum. -/
noncomputable def secondBase (profile : W2R2SourceProfile.SourceProfile data star block) :
    Fin 3 → GluingDatum target degree
  | 0 => (W2MkkTransport.swapRelabeling profile (firstSheet profile)
      (W2MkkTransport.firstSheet_together profile)).apply
  | 1 => data
  | 2 => data

noncomputable def secondCandidate (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (member : SecondMember profile) :
    ∀ i : Fin 3, BalancedGlobal.Candidate target degree (secondBase profile i) wall
  | 0 => (W2MkkLimitColumns.remoteDetach input shape (firstSheet profile)
      (W2MkkTransport.firstSheet_together profile)).candidate
      (W2MkkTransport.swapShape shape input.valid.1 (firstSheet profile)
        (W2MkkTransport.firstSheet_together profile))
  | 1 => member.toDetachData.candidate shape
  | 2 => joinedCandidate profile distinguished

noncomputable def secondPresentation (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (member : SecondMember profile)
    (initial : StableLengthMatrixLabelling
      ((W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
        hGenus).member 0).datum coordinate) :
    ∀ i : Fin 3,
      (secondCandidate input shape distinguished member i).datum.LengthMatrixPresentation
        coordinate
  | 0 => ((W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
      hGenus).labelling initial 0).presentation
  | 1 => ((W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
      hGenus).labelling initial 1).presentation
  | 2 => ((W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
      hGenus).labelling initial 2).presentation

omit [Fintype coordinate] in
theorem secondPresentation_matrix (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (member : SecondMember profile)
    (initial : StableLengthMatrixLabelling
      ((W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
        hGenus).member 0).datum coordinate) (i : Fin 3) :
    GluingDatum.LengthMatrixPresentation.matrix
        (secondPresentation input shape distinguished hConnected hGenus member initial i) =
      (W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
        hGenus).squareMatrix initial i := by
  fin_cases i <;> rfl

/-- **Figure 34 as a gauge family, Base II.2.2.M orientation.** -/
noncomputable def secondGaugeFamily (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (member : SecondMember profile)
    (initial : StableLengthMatrixLabelling
      ((W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
        hGenus).member 0).datum coordinate) :
    BalancedGlobal.GaugeFamily (coordinate := coordinate) 3 data wall where
  base := secondBase profile
  valid_of_old := fun i hValid ↦ by
    match i with
    | 0 => exact (W2MkkTransport.swapRelabeling profile (firstSheet profile)
             (W2MkkTransport.firstSheet_together profile)).valid hValid
    | 1 => exact hValid
    | 2 => exact hValid
  candidate := secondCandidate input shape distinguished member
  presentation := secondPresentation input shape distinguished hConnected hGenus member initial
  wallColumn := (W2MkkLimitColumns.secondOrientation input shape member distinguished
    hConnected hGenus).wallColumn initial
  weight := ![(data.sourceEdgeIndex profile.first.1 : ℚ) - 1,
    (data.sourceEdgeIndex profile.second.1 : ℚ) - 1,
    (data.sourceEdgeIndex profile.first.1 : ℚ) + (data.sourceEdgeIndex profile.second.1 : ℚ)]
  positiveBalance := by
    have h := (W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
      hGenus).positiveBalance input initial
    exact ⟨h.1, by simpa only [secondPresentation_matrix] using h.2⟩
  agreeOffWall := fun first second ↦ by
    rw [secondPresentation_matrix, secondPresentation_matrix]
    exact (W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
      hGenus).matrices_agree initial first second

end Gauge

end DraismaVargas.LocalCases.W2MkkArbitraryExit
