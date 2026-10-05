module

public import DraismaVargas.LocalCases.W2M1kLimitColumns
public import DraismaVargas.LocalCases.W2M1kLeafStableGraph
public import DraismaVargas.LocalCases.SheetRelabelIncidence
public import DraismaVargas.LocalCases.FiniteAtlasMarch

@[expose] public section

/-!
# Figure 33's certified exit, at the receipt level

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-1k}`, Figure 33 and
**Equation (7)**, with the factor of two in the second bracket of Equation (7)
explained in `W2M1kCommonBalance`.

`W2M1kLimitColumns.limitColumns` inhabits `W2M1kCommonBalance.LimitColumns` on
the case's actual input in both orientations, so Equation (7) and its positive
balance hold unconditionally.  This module turns that balance into the
**certified exit**: a valid outgoing member of strictly opposite determinant
sign, a positive rational step that stays in the positive cone, the exact affine
metric equation, and an explicit cleared rank-one pencil on the selected
member's own source subdivision.

It is the M-1k analogue of `W2MkkArbitraryExit` §§1--5 and §§7--9.  The
arbitrary-incoming half -- which Figure 33 member the incoming cover *is* -- is
`W2M1kIncomingCensus` and `W2M1kIncomingMatching`, and
`W2M1kClosureUnconditional.headline_cases` names the orientation the incoming
datum decides.

## Why this is stated over `LimitMember` and not over a family

`W2M1kSourceCandidates.not_leafPair_and_dividedData` forbids
putting Figure 33's `M⁽¹⁾` and `M⁽²⁾` over one gluing datum, so the three
members are not a `BalancedGlobal.PresentedFamily`: whichever of the two the
incoming datum does not carry lives over `W2M1kTransport.swapRelabeling …|>.apply`.
`BalancedGlobal.GaugeFamily` was introduced for exactly that and would serve,
but it asks for each member's *occurrence-level* data, while
`W2M1kCommonBalance.LimitMember` deliberately keeps only the outgoing datum, the
validity implication, the row bijection and the retained columns.

Nothing is lost, for the reason `W2MkkArbitraryExit` records: what
`BalancedGlobal.Candidate.clearedPencil` actually consumes of a candidate is
`candidate.datum.Valid`, connectedness and genus zero of the **expanded**
target, and one vertex of it -- and every one of those is available from a
`LimitMember` directly (`valid_of_old`,
`W2M1kStableIncidence.expanded_targetConnected` / `expanded_targetGenus`, and
`TargetExpansion.oldVertex`).  So the pencil is built here at datum level and
the exit needs no family structure at all.  The `BalancedGlobal.GaugeFamily`
packaging and the full-dimensional supply are in `W2M1kGaugeFamily` and
`A04M1kWiring`.

## What M-1k does that M-kk does not

Figure 33's three members do **not** share a wall-side assignment.  `M⁽²⁾` and
`M⁽³⁾` use the two-star's own (`W2M1kStableGraph.divided_right`,
`joined_right`), while `M⁽¹⁾` sends *both* wall directions to the fresh endpoint
(`W2M1kLeaves.leaf_right`, `= true` for every occurrence): Base I.a's retained
end is a target **leaf**.  Nothing in this module notices -- the exit is stated
per `LimitMember` and `expanded_targetConnected` / `expanded_targetGenus` hold
for an arbitrary side assignment -- but it is what makes the incoming half a
trichotomy rather than M-kk's dichotomy, and it is recorded here because the
dictionary families of §6 are the last place the three members are named
together.

## Main results

* `exists_clearedPencil` -- positive rational coordinates on any Figure 33
  member clear, at the datum's own `rationalRealizationScale`, to an integral
  realization carrying the degree-`degree` rank-one pencil.
* `outgoingVelocity`, `outgoingVelocity_system` -- the canonical chart velocity
  at a nonsingular member.
* `exists_positive_exit_with_pencil` -- **the exit**, at every position of the
  receipt, remote included.
* `exists_positive_exit_with_presentation` -- the same with an outgoing
  `FullDimensionalSource.FullDimensionalSourcePresentation`, taking the
  per-position stable-incidence dictionary and source-genus receipt as
  hypotheses.
* `localLeafMember_dictionary`, `localDividedMember_dictionary`,
  `joinedMember_dictionary`, `remoteDividedMember_dictionary`,
  `remoteLeafMember_dictionary` -- the five per-member dictionaries, **all
  discharged**: the remote half is `SheetRelabelIncidence` at
  `W2M1kTransport.swapRelabeling` (§5).
* `alignedOrientationDictionary` / `separatedOrientationDictionary` and their
  genus families -- the three positions of each orientation.
* `initialLabelling`, `labelling_self`, `squareMatrix_self`,
  `wallColumn_initialLabelling` -- one identified member's honest labelling
  induces the common square coordinate order, and transport to the receipt's
  position `0` and back is the identity on it.
* `exists_positive_exit_in_original_coordinates` -- the exit against a supplied
  original matrix and original wall column.

No stable-incidence dictionary enters the coordinate cancellation of §7:
`W2M1kCommonBalance.LimitColumns.labelling` builds each member's row map out of
`LimitMember.row`, so it is between the receipt's own row bijections.
-/

namespace DraismaVargas.LocalCases.W2M1kArbitraryExit

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StableSourceMatrix
open ResolutionM11 ResolutionM1k
open FullDimensionalSource
open W2M1kSourceCandidates
open W2M1kTransport
open W2M1kCommonBalance (LimitMember LimitColumns)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  {shape : Shape profile}

/-! ## §1  The cleared pencil at any Figure 33 member -/

/-- **Positive coordinates clear at a Figure 33 member.**  Only the member's
outgoing datum enters, so this holds at the remote position, and at the leaf
position whose expanded target is `T_∅`, exactly as at the other two. -/
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
      (W2M1kStableIncidence.expanded_targetConnected hConnected (limit.member position).right)
      (W2M1kStableIncidence.expanded_targetGenus hGenus (limit.member position).right)
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

/-- **Figure 33's certified exit.**  Equation (7) -- `W2M1kCommonBalance`'s
`positiveBalance`, discharged on the case's actual input by
`W2M1kLimitColumns.limitColumns` -- selects a genuinely nonsingular
opposite-sign member; the one-column cone-wall calculation supplies the positive
rational step, the exact affine metric equation and the whole-segment
positivity; and the member's own datum clears the rank-one pencil.

Only the chosen incoming member is assumed nonsingular.  No assumption is made
about which Figure 33 position the selected outgoing member is, so the remote
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

`W2M1kStableIncidence.presentationAt` transports a full-dimensional presentation
from one position of the receipt to another along a stable-incidence dictionary,
gated on the outgoing position's own determinant, and carries the family's own
honest labelling.  The dictionary and the source-genus receipt are taken here as
per-position hypotheses; §5 and §6 discharge both at all three positions of both
orientations. -/

section Presented

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The certified exit with an outgoing full-dimensional source.**  Everything
of `exists_positive_exit_with_pencil`, plus a
`FullDimensionalSource.FullDimensionalSourcePresentation` on the selected
outgoing member presenting the family's own honest labelling. -/
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
    W2M1kStableIncidence.presentationAt limit incoming outgoing
      ((dictionary incoming).symm.trans (dictionary outgoing)) input.valid hConnected hGenus
      (sourceGenus incoming) (sourceGenus outgoing) initial incomingFD hOutDet,
    rfl, hSign, δ, hδ, hStep⟩

end Presented


/-! ## §5  The five per-member dictionaries, all discharged

The remote half is `SheetRelabelIncidence` at `W2M1kTransport.swapRelabeling`,
so nothing in this module is conditional on a dictionary the case does not
have. -/

section Dictionaries

variable (input : W2SourceInput data star) (shape : Shape profile)

/-- `M⁽¹⁾` over the incoming datum has the incoming stable incidence graph. -/
noncomputable def localLeafMember_dictionary (pair : LeafPair profile) :
    StableGraphIncidence.Equivalence data
      (W2M1kLimitColumns.localLeafMember input shape pair).datum :=
  W2M1kLeafStableGraph.leafEquivalence input shape pair

theorem localLeafMember_sourceGenus (pair : LeafPair profile) :
    genus (W2M1kLimitColumns.localLeafMember input shape pair).datum.sourceGraph =
      genus data.sourceGraph :=
  leaf_sourceGenus input shape pair

/-- `M⁽²⁾` over the incoming datum has the incoming stable incidence graph. -/
noncomputable def localDividedMember_dictionary (divided : DividedData profile) :
    StableGraphIncidence.Equivalence data
      (W2M1kLimitColumns.localDividedMember input shape divided).datum :=
  W2M1kGraphData.dividedEquivalence input shape divided

theorem localDividedMember_sourceGenus (divided : DividedData profile) :
    genus (W2M1kLimitColumns.localDividedMember input shape divided).datum.sourceGraph =
      genus data.sourceGraph :=
  divided_sourceGenus shape divided

/-- `M⁽³⁾` over the incoming datum has the incoming stable incidence graph. -/
noncomputable def joinedMember_dictionary (geometry : GlobalM1k.Geometry data wall) :
    StableGraphIncidence.Equivalence data
      (W2M1kLimitColumns.joinedMember input shape geometry).datum :=
  W2M1kGraphData.joinedEquivalence input shape geometry

theorem joinedMember_sourceGenus (geometry : GlobalM1k.Geometry data wall) :
    genus (W2M1kLimitColumns.joinedMember input shape geometry).datum.sourceGraph =
      genus data.sourceGraph :=
  joined_sourceGenus geometry

/-- **The branch swap as a stable-incidence equivalence.**  `W2M1kTransport.swapGauge`
already carries the stable rows and the whole natural matrix across the swap
through `LimitChainCore.Gauge`; this is the *branch* half, and it comes from the
same relabelling and the same connectedness.  No case data enters:
`SheetRelabelIncidence.equivalence` is stated for an arbitrary relabelling. -/
noncomputable def swapEquivalence (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    StableGraphIncidence.Equivalence data (swapRelabeling profile other hOther).apply :=
  SheetRelabelIncidence.equivalence (swapRelabeling profile other hOther) hConnected

/-- **The source genus is preserved by the branch swap.**  This needs no
connectedness: relabelling permutes occurrences and preserves every
quotient-source edge multiplicity. -/
theorem swap_sourceGenus (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    genus (swapRelabeling profile other hOther).apply.sourceGraph = genus data.sourceGraph :=
  SheetRelabelIncidence.sourceGenus_eq (swapRelabeling profile other hOther)

/-- **The remote `M⁽²⁾` has the incoming stable incidence graph.**  The branch
half from `swapEquivalence`, the member half from `W2M1kGraphData.dividedEquivalence`
over the copy. -/
noncomputable def remoteDividedMember_dictionary (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (divided : DividedData (swapProfile profile input.valid.1 other hOther)) :
    StableGraphIncidence.Equivalence data
      (W2M1kLimitColumns.remoteDividedMember input shape other hOther divided).datum :=
  (swapEquivalence input.valid.1 other hOther).trans
    (W2M1kGraphData.dividedEquivalence (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) divided)

theorem remoteDividedMember_sourceGenus (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (divided : DividedData (swapProfile profile input.valid.1 other hOther)) :
    genus (W2M1kLimitColumns.remoteDividedMember input shape other hOther
        divided).datum.sourceGraph = genus data.sourceGraph :=
  (divided_sourceGenus (swapShape shape input.valid.1 other hOther) divided).trans
    (swap_sourceGenus other hOther)

/-- **The remote `M⁽¹⁾` has the incoming stable incidence graph.**  The mirror,
through `W2M1kLeafStableGraph.leafEquivalence` over the copy. -/
noncomputable def remoteLeafMember_dictionary (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (pair : LeafPair (swapProfile profile input.valid.1 other hOther)) :
    StableGraphIncidence.Equivalence data
      (W2M1kLimitColumns.remoteLeafMember input shape other hOther pair).datum :=
  (swapEquivalence input.valid.1 other hOther).trans
    (W2M1kLeafStableGraph.leafEquivalence (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) pair)

theorem remoteLeafMember_sourceGenus (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (pair : LeafPair (swapProfile profile input.valid.1 other hOther)) :
    genus (W2M1kLimitColumns.remoteLeafMember input shape other hOther
        pair).datum.sourceGraph = genus data.sourceGraph :=
  (leaf_sourceGenus (swapInput input other hOther)
    (swapShape shape input.valid.1 other hOther) pair).trans (swap_sourceGenus other hOther)

end Dictionaries


/-! ## §6  The two orientations' dictionary families

`W2M1kLimitColumns.limitColumns` branches on the datum's own orientation -- the
decidable `pinSheet profile 0 = pinSheet profile 1` -- and the two branches put
the local member at different Figure 33 positions.  In each branch two of the
three positions are over the incoming datum and one is remote. -/

section Families

variable (input : W2SourceInput data star) (shape : Shape profile)
  (hTargetConnected : graph_connected target) (hGenus : genus target = 0)

/-- **Base I.a orientation** (`p₀ = p₁`): position `0` is the local `M⁽¹⁾`,
position `1` the remote `M⁽²⁾`, position `2` is `M⁽³⁾`. -/
noncomputable def alignedOrientationDictionary (pair : LeafPair profile) :
    ∀ position : Fin 3, StableGraphIncidence.Equivalence data
      ((W2M1kLimitColumns.alignedOrientation input shape pair hTargetConnected
        hGenus).member position).datum
  | 0 => localLeafMember_dictionary input shape pair
  | 1 => remoteDividedMember_dictionary input shape pair.second pair.rel_second
      (W2M1kLimitColumns.remoteDivided input shape pair hTargetConnected hGenus)
  | 2 => joinedMember_dictionary input shape (pair.geometry shape)

theorem alignedOrientationSourceGenus (pair : LeafPair profile) :
    ∀ position : Fin 3,
      genus ((W2M1kLimitColumns.alignedOrientation input shape pair hTargetConnected
        hGenus).member position).datum.sourceGraph = genus data.sourceGraph
  | 0 => localLeafMember_sourceGenus input shape pair
  | 1 => remoteDividedMember_sourceGenus input shape pair.second pair.rel_second
      (W2M1kLimitColumns.remoteDivided input shape pair hTargetConnected hGenus)
  | 2 => joinedMember_sourceGenus input shape (pair.geometry shape)

/-- **Base II.2.2.M orientation** (`p₀ ≠ p₁`): position `0` is the remote
`M⁽¹⁾`, position `1` the local `M⁽²⁾`, position `2` is `M⁽³⁾`. -/
noncomputable def separatedOrientationDictionary (divided : DividedData profile) :
    ∀ position : Fin 3, StableGraphIncidence.Equivalence data
      ((W2M1kLimitColumns.separatedOrientation input shape divided hTargetConnected
        hGenus).member position).datum
  | 0 => remoteLeafMember_dictionary input shape (pinSheet profile 1)
      (W2SourceTransport.alignedTogether profile)
      (W2M1kLimitColumns.remoteLeaf input shape hTargetConnected hGenus)
  | 1 => localDividedMember_dictionary input shape divided
  | 2 => joinedMember_dictionary input shape (divided.geometry shape)

theorem separatedOrientationSourceGenus (divided : DividedData profile) :
    ∀ position : Fin 3,
      genus ((W2M1kLimitColumns.separatedOrientation input shape divided hTargetConnected
        hGenus).member position).datum.sourceGraph = genus data.sourceGraph
  | 0 => remoteLeafMember_sourceGenus input shape (pinSheet profile 1)
      (W2SourceTransport.alignedTogether profile)
      (W2M1kLimitColumns.remoteLeaf input shape hTargetConnected hGenus)
  | 1 => localDividedMember_sourceGenus input shape divided
  | 2 => joinedMember_sourceGenus input shape (divided.geometry shape)

end Families


/-! ## §7  Reading the exit in the incoming cover's own coordinates

One identified member's honest labelling fixes the common square coordinate
order, and transport to the receipt's position `0` and back is the identity on
it.  No stable-incidence dictionary enters here:
`W2M1kCommonBalance.LimitColumns.labelling` builds each member's row map out of
`LimitMember.row`, which is part of the receipt, so the cancellation is between
the receipt's own row bijections. -/

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

/-- **The common wall coordinate is the identified member's own wall column.** -/
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

/-- **The certified exit in the original coordinates.**  Given one Figure 33
position carrying a full-dimensional presentation whose length matrix is the
incoming cover's and whose wall column is the incoming cover's own contracted
column, Equation (7) selects a valid outgoing member of strictly opposite
determinant sign against the *original* matrix; the whole segment stays
positive; the affine metric equation is the original one; and the cleared
rank-one pencil sits on the selected member's actual source subdivision. -/
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

end DraismaVargas.LocalCases.W2M1kArbitraryExit
