import DraismaVargas.LocalCases.W2MkkLimitMatrix
import DraismaVargas.LocalCases.W2MkkCommonBalance
import DraismaVargas.LocalCases.W2MkkTransport

/-!
# Figure 34's limit columns, inhabited: Equation (8) unconditionally

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{w2-r2-nd3-M-kk}`, its Figure 34 and **Equation (8)**.

`W2MkkCommonBalance` proves Equation (8), `determinant_balance`,
`positiveBalance`, `exists_valid_opposite` and `canonicalFamily`
**conditionally** on an inhabitant of `W2MkkCommonBalance.LimitColumns`.  This
file builds that inhabitant from the three member constructions and so
discharges the condition on the case's actual input.  It is the M-kk analogue of `W2PLimitMatrix.limitColumns`
/ `nonempty_limitColumns` for Figure 35.

## The three members

* Position `2`, `M⁽³⁾` (Base II.1.M), is `W2MkkSourceCandidates.joinedCandidate`
  over the incoming datum, with `W2MkkRowDescent.joinedStablePathEquiv` and
  `W2MkkLimitMatrix.joined_matrix_retained` / `thirdMember_regrown`.
* Positions `0` and `1`, `M⁽¹⁾` and `M⁽²⁾` (Base II.2.1.M, II.2.2.M), are
  `W2MkkSourceCandidates.DetachData.candidate`.  **Only one of them lives over
  the incoming datum.**  `W2MkkSourceCandidates.no_common_geometry` and
  `not_firstMember_and_secondMember` show no `w2Mkk` datum carries both: the
  dangling `t₃` occurrence pins a sheet, that sheet lies in exactly one of the
  two `t₂` endpoint blocks, and which one decides which member is available.
  The other member is built over the branch-swapped copy of the datum that
  `W2MkkTransport` supplies, and is a member *for* the incoming datum through
  `GluingDatum.SheetRelabeling.valid`, exactly as
  `GlobalMkk.DivalentPattern.remoteCertified` certifies one.

`W2MkkCommonBalance.LimitMember` was designed for precisely this: its
`valid_of_old` is an implication `data.Valid → datum.Valid`, not an identity of
data, so a remote member inhabits it.

## Both orientations

`limitColumns` is total on the case's actual input.  It branches on the datum's
own orientation -- `W2MkkSourceCandidates.pinSheet_mem` decides it -- and in
each branch the member the datum **does** carry sits in its own Figure 34 slot
over the incoming datum itself (`limitColumns_eq_firstOrientation`,
`limitColumns_eq_secondOrientation` identify which), while the other slot is
filled remotely.  Nothing is assumed about which orientation occurs.

## What is not built here

The `LimitChainCore.GraphData` packaging and the presented-family equivalence
are built elsewhere; this file produces a `BalancedGlobal.Family`, not a
`PresentedFamily`, exactly as `W2MkkCommonBalance.LimitColumns.family` does and
for the same reason (`GlobalMkk`'s swapped route, as in
`GlobalMkk.swappedBalancedFamily`).
-/

namespace DraismaVargas.LocalCases.W2MkkLimitColumns

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StableSourceMatrix
open ResolutionM11 GlobalM11Arbitrary
open W2MkkSourceCandidates
open W2MkkTransport

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-! ## The two members over the incoming datum -/

/-- **A detaching member over the incoming datum itself.**  Which of `M⁽¹⁾`,
`M⁽²⁾` it is, is decided by the datum through the pinned sheet; the member,
the row bijection and the retained columns are uniform in that choice. -/
noncomputable def localMember (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) : W2MkkCommonBalance.LimitMember data wall where
  right := (detach.candidate shape).right
  datum := (detach.candidate shape).datum
  valid_of_old := (detach.candidate shape).datum_valid
  row := W2MkkRowDescent.detachStablePathEquiv input shape detach
  retained := W2MkkLimitMatrix.detach_matrix_retained input shape detach

@[simp] theorem localMember_datum (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) :
    (localMember input shape detach).datum = (detach.candidate shape).datum := rfl

/-- `c⁽¹⁾ = c(e₁)/(k₁-1) + c(e₂)/k₂ + s`, when the datum's pinned sheet lies in
`e₁`. -/
theorem localMember_regrown_first (input : W2SourceInput data star) (shape : Shape profile)
    (member : FirstMember profile) (path : StablePath data) :
    (localMember input shape member.toDetachData).newColumnValue path =
      W2MkkCommonBalance.firstNewColumn profile path :=
  W2MkkLimitMatrix.firstMember_regrown_of input shape member path

/-- `c⁽²⁾ = c(e₁)/k₁ + c(e₂)/(k₂-1) + s`, when it lies in `e₂`. -/
theorem localMember_regrown_second (input : W2SourceInput data star) (shape : Shape profile)
    (member : SecondMember profile) (path : StablePath data) :
    (localMember input shape member.toDetachData).newColumnValue path =
      W2MkkCommonBalance.secondNewColumn profile path :=
  W2MkkLimitMatrix.secondMember_regrown_of input shape member path

/-- **`M⁽³⁾` over the incoming datum.**  It needs no occurrence hypothesis, so
it is available over every datum of the case. -/
noncomputable def joinedMember (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) : W2MkkCommonBalance.LimitMember data wall where
  right := (joinedCandidate profile distinguished).right
  datum := (joinedCandidate profile distinguished).datum
  valid_of_old := (joinedCandidate profile distinguished).datum_valid
  row := W2MkkRowDescent.joinedStablePathEquiv input shape distinguished
  retained := W2MkkLimitMatrix.joined_matrix_retained input shape distinguished

@[simp] theorem joinedMember_datum (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) :
    (joinedMember input shape distinguished).datum =
      (joinedCandidate profile distinguished).datum := rfl

/-- `c⁽³⁾ = c(e₃)/(k₁+k₂) + s`. -/
theorem joinedMember_regrown (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (path : StablePath data) :
    (joinedMember input shape distinguished).newColumnValue path =
      W2MkkCommonBalance.thirdNewColumn profile path :=
  W2MkkLimitMatrix.thirdMember_regrown input shape distinguished path

/-! ## The remote member

The detachment datum over the gauge copy is not a choice the reader makes: the
copy's pinned endpoint block has `k₁ ≥ 2` or `k₂ ≥ 2` sheets, so
`W2MkkSourceCandidates.exists_detachData` supplies a partner. -/

/-- The detachment datum over the branch-swapped copy. -/
noncomputable def remoteDetach (input : W2SourceInput data star) (shape : Shape profile)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    DetachData (swapProfile profile input.valid.1 other hOther) :=
  (exists_detachData (swapShape shape input.valid.1 other hOther)).some

/-- **A detaching member of Figure 34 over the branch-swapped copy, read as a
member for the incoming datum.**  `valid_of_old` composes the relabelling's own
validity transport with the candidate's; `row` composes the gauge's stable-row
bijection with the row descent over the copy; `retained` composes
`W2MkkLimitMatrix.detach_matrix_retained` over the copy with
`LimitChainCore.Gauge.matrix_gauge`. -/
noncomputable def remoteMember (input : W2SourceInput data star) (shape : Shape profile)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    W2MkkCommonBalance.LimitMember data wall where
  right := ((remoteDetach input shape other hOther).candidate
    (swapShape shape input.valid.1 other hOther)).right
  datum := ((remoteDetach input shape other hOther).candidate
    (swapShape shape input.valid.1 other hOther)).datum
  valid_of_old := fun hValid ↦ ((remoteDetach input shape other hOther).candidate
    (swapShape shape input.valid.1 other hOther)).datum_valid
      ((swapRelabeling profile other hOther).valid hValid)
  row := (swapGauge profile input.valid.1 other hOther).row.trans
    (W2MkkRowDescent.detachStablePathEquiv (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) (remoteDetach input shape other hOther))
  retained := fun path place ↦
    (W2MkkLimitMatrix.detach_matrix_retained (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) (remoteDetach input shape other hOther)
      ((swapGauge profile input.valid.1 other hOther).row path) place).trans
      ((swapGauge profile input.valid.1 other hOther).matrix_gauge path place)

/-- `e₁`'s stable row travels by the gauge. -/
theorem swapProfile_firstRow (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    W2MkkLimitMatrix.firstRow (swapProfile profile hConnected other hOther) =
      (swapGauge profile hConnected other hOther).row
        (W2MkkCommonBalance.firstRow profile) :=
  ((swapGauge profile hConnected other hOther).row_mk profile.first.1
    profile.first_survives).symm

/-- `e₂`'s stable row travels by the gauge. -/
theorem swapProfile_secondRow (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    W2MkkLimitMatrix.secondRow (swapProfile profile hConnected other hOther) =
      (swapGauge profile hConnected other hOther).row
        (W2MkkCommonBalance.secondRow profile) :=
  ((swapGauge profile hConnected other hOther).row_mk profile.second.1
    profile.second_survives).symm

/-- **The remote member's regrown column is Figure 34's `c⁽²⁾`**, read in the
*incoming* datum's rows and at the *incoming* datum's indices: the rows travel
by the gauge, `k₁` and `k₂` are gauge invariants, and `s` is carried by
`W2MkkTransport.swap_backgroundColumn`. -/
theorem remoteMember_regrown_second (input : W2SourceInput data star) (shape : Shape profile)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other)
    (hPin : (endpointPartition (swapProfile profile input.valid.1 other hOther)).Rel
      (secondSheet (swapProfile profile input.valid.1 other hOther))
      (pinSheet (swapProfile profile input.valid.1 other hOther)))
    (path : StablePath data) :
    (remoteMember input shape other hOther).newColumnValue path =
      W2MkkCommonBalance.secondNewColumn profile path := by
  have h := W2MkkLimitMatrix.secondMember_regrown (swapInput input other hOther)
    (swapShape shape input.valid.1 other hOther) (remoteDetach input shape other hOther)
    hPin ((swapGauge profile input.valid.1 other hOther).row path)
  rw [swapProfile_firstRow, swapProfile_secondRow, swapProfile_first_index,
    swapProfile_second_index, swap_backgroundColumn] at h
  simp only [EmbeddingLike.apply_eq_iff_eq] at h
  exact h

/-- The mirror statement: the remote member's regrown column is `c⁽¹⁾`. -/
theorem remoteMember_regrown_first (input : W2SourceInput data star) (shape : Shape profile)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other)
    (hPin : (endpointPartition (swapProfile profile input.valid.1 other hOther)).Rel
      (firstSheet (swapProfile profile input.valid.1 other hOther))
      (pinSheet (swapProfile profile input.valid.1 other hOther)))
    (path : StablePath data) :
    (remoteMember input shape other hOther).newColumnValue path =
      W2MkkCommonBalance.firstNewColumn profile path := by
  have h := W2MkkLimitMatrix.firstMember_regrown (swapInput input other hOther)
    (swapShape shape input.valid.1 other hOther) (remoteDetach input shape other hOther)
    hPin ((swapGauge profile input.valid.1 other hOther).row path)
  rw [swapProfile_firstRow, swapProfile_secondRow, swapProfile_first_index,
    swapProfile_second_index, swap_backgroundColumn] at h
  simp only [EmbeddingLike.apply_eq_iff_eq] at h
  exact h

/-- **`M⁽²⁾` remotely**, over the copy obtained by swapping the pinned sheet
with `e₂`'s canonical sheet.  Available over *every* datum of the case. -/
noncomputable def remoteSecondMember (input : W2SourceInput data star) (shape : Shape profile) :
    W2MkkCommonBalance.LimitMember data wall :=
  remoteMember input shape (secondSheet profile) (secondSheet_together profile)

theorem remoteSecondMember_regrown (input : W2SourceInput data star) (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (path : StablePath data) :
    (remoteSecondMember input shape).newColumnValue path =
      W2MkkCommonBalance.secondNewColumn profile path :=
  remoteMember_regrown_second input shape (secondSheet profile) (secondSheet_together profile)
    (swapProfile_pin_second shape hTargetConnected hGenus input.valid.1) path

/-- **`M⁽¹⁾` remotely**, the mirror construction. -/
noncomputable def remoteFirstMember (input : W2SourceInput data star) (shape : Shape profile) :
    W2MkkCommonBalance.LimitMember data wall :=
  remoteMember input shape (firstSheet profile) (firstSheet_together profile)

theorem remoteFirstMember_regrown (input : W2SourceInput data star) (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (path : StablePath data) :
    (remoteFirstMember input shape).newColumnValue path =
      W2MkkCommonBalance.firstNewColumn profile path :=
  remoteMember_regrown_first input shape (firstSheet profile) (firstSheet_together profile)
    (swapProfile_pin_first shape hTargetConnected hGenus input.valid.1) path

/-! ## The join, one orientation at a time -/

/-- **Base II.2.1.M orientation**: the datum carries `M⁽¹⁾`, so position `0` is
over the incoming datum and position `1` is remote. -/
noncomputable def firstOrientation (input : W2SourceInput data star) (shape : Shape profile)
    (member : FirstMember profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    W2MkkCommonBalance.LimitColumns profile shape where
  member := ![localMember input shape member.toDetachData, remoteSecondMember input shape,
    joinedMember input shape distinguished]
  regrown := by
    intro position path
    fin_cases position
    · exact localMember_regrown_first input shape member path
    · exact remoteSecondMember_regrown input shape hTargetConnected hGenus path
    · exact joinedMember_regrown input shape distinguished path

/-- **Base II.2.2.M orientation**: the datum carries `M⁽²⁾`, so position `1` is
over the incoming datum and position `0` is remote. -/
noncomputable def secondOrientation (input : W2SourceInput data star) (shape : Shape profile)
    (member : SecondMember profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    W2MkkCommonBalance.LimitColumns profile shape where
  member := ![remoteFirstMember input shape, localMember input shape member.toDetachData,
    joinedMember input shape distinguished]
  regrown := by
    intro position path
    fin_cases position
    · exact remoteFirstMember_regrown input shape hTargetConnected hGenus path
    · exact localMember_regrown_second input shape member path
    · exact joinedMember_regrown input shape distinguished path

@[simp] theorem firstOrientation_member_zero (input : W2SourceInput data star)
    (shape : Shape profile) (member : FirstMember profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    (firstOrientation input shape member distinguished hTargetConnected hGenus).member 0 =
      localMember input shape member.toDetachData := rfl

@[simp] theorem secondOrientation_member_one (input : W2SourceInput data star)
    (shape : Shape profile) (member : SecondMember profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    (secondOrientation input shape member distinguished hTargetConnected hGenus).member 1 =
      localMember input shape member.toDetachData := rfl

/-- **`W2MkkCommonBalance.LimitColumns` is inhabited on the case's actual
input, in both orientations.**  The datum decides which orientation occurs --
`W2MkkSourceCandidates.pinSheet_mem` -- and no hypothesis about that choice is
imposed.  The two standing target hypotheses are the ones
`W2MkkSourceCandidates.singleLabel_fixed` already consumes. -/
noncomputable def limitColumns (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    W2MkkCommonBalance.LimitColumns profile shape :=
  if hPin : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile) then
    firstOrientation input shape ⟨detach, hPin⟩ distinguished hTargetConnected hGenus
  else
    secondOrientation input shape ⟨detach, (pinSheet_mem shape).resolve_left hPin⟩
      distinguished hTargetConnected hGenus

theorem limitColumns_eq_firstOrientation (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (hPin : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile)) :
    limitColumns input shape detach distinguished hTargetConnected hGenus =
      firstOrientation input shape ⟨detach, hPin⟩ distinguished hTargetConnected hGenus :=
  dif_pos hPin

theorem limitColumns_eq_secondOrientation (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (hPin : ¬ (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile))
    (hSecond : (endpointPartition profile).Rel (secondSheet profile) (pinSheet profile)) :
    limitColumns input shape detach distinguished hTargetConnected hGenus =
      secondOrientation input shape ⟨detach, hSecond⟩ distinguished hTargetConnected hGenus :=
  dif_neg hPin

/-- **The member the incoming datum carries sits in its own Figure 34 slot,
over the incoming datum.**  Base II.2.1.M. -/
theorem limitColumns_member_zero_of_first (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (hPin : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile)) :
    (limitColumns input shape detach distinguished hTargetConnected hGenus).member 0 =
      localMember input shape detach := by
  rw [limitColumns_eq_firstOrientation input shape detach distinguished hTargetConnected
    hGenus hPin]
  rfl

/-- Base II.2.2.M. -/
theorem limitColumns_member_one_of_second (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (hPin : ¬ (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile))
    (hSecond : (endpointPartition profile).Rel (secondSheet profile) (pinSheet profile)) :
    (limitColumns input shape detach distinguished hTargetConnected hGenus).member 1 =
      localMember input shape detach := by
  rw [limitColumns_eq_secondOrientation input shape detach distinguished hTargetConnected
    hGenus hPin hSecond]
  rfl

/-- `M⁽³⁾` is over the incoming datum in either orientation. -/
theorem limitColumns_member_two (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    (limitColumns input shape detach distinguished hTargetConnected hGenus).member 2 =
      joinedMember input shape distinguished := by
  unfold limitColumns
  split <;> rfl

/-- **Non-vacuity.**  Every actual `w2Mkk` datum of the case, on a connected
genus-zero target, inhabits `W2MkkCommonBalance.LimitColumns`, so nothing
downstream of it is vacuous. -/
theorem nonempty_limitColumns (input : W2SourceInput data star) (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    Nonempty (W2MkkCommonBalance.LimitColumns profile shape) :=
  ⟨limitColumns input shape (exists_detachData shape).some block.1 hTargetConnected hGenus⟩

/-! ## The unconditional statements -/

section Coordinates

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **Equation (8) at a supplied honest square labelling, unconditionally.**
`W2MkkCommonBalance.LimitColumns.determinant_balance` is proved there
conditionally on an inhabitant; here the condition is discharged. -/
theorem determinant_balance (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      ((limitColumns input shape detach distinguished hTargetConnected
        hGenus).member 0).datum coordinate) :
    ((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) *
          ((limitColumns input shape detach distinguished hTargetConnected
            hGenus).squareMatrix initial 0).det +
        ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) *
          ((limitColumns input shape detach distinguished hTargetConnected
            hGenus).squareMatrix initial 1).det +
        ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) *
          ((limitColumns input shape detach distinguished hTargetConnected
            hGenus).squareMatrix initial 2).det = 0 :=
  (limitColumns input shape detach distinguished hTargetConnected
    hGenus).determinant_balance input initial

/-- The positive balance at a supplied labelling, unconditionally. -/
theorem positiveBalance (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      ((limitColumns input shape detach distinguished hTargetConnected
        hGenus).member 0).datum coordinate) :
    BalancingValencyTwo.PositiveBalance
      ![(data.sourceEdgeIndex profile.first.1 : ℚ) - 1,
        (data.sourceEdgeIndex profile.second.1 : ℚ) - 1,
        (data.sourceEdgeIndex profile.first.1 : ℚ) +
          (data.sourceEdgeIndex profile.second.1 : ℚ)]
      (fun position ↦ ((limitColumns input shape detach distinguished hTargetConnected
        hGenus).squareMatrix initial position).det) :=
  (limitColumns input shape detach distinguished hTargetConnected
    hGenus).positiveBalance input initial

/-- Figure 34's balanced family at a supplied labelling, unconditionally. -/
noncomputable def family (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      ((limitColumns input shape detach distinguished hTargetConnected
        hGenus).member 0).datum coordinate) :
    BalancedGlobal.Family (coordinate := coordinate) 3 data :=
  (limitColumns input shape detach distinguished hTargetConnected hGenus).family input initial

end Coordinates

/-- **Equation (8) for Figure 34's three actual members, unconditionally.**
`W2MkkCommonBalance.LimitColumns.canonical_determinant_balance` is proved there
conditionally on an inhabitant; here the condition is discharged.  The
weights are the members' own new-edge indices `k₁-1`, `k₂-1`, `k₁+k₂`, and no
member is assumed nonsingular. -/
theorem canonical_determinant_balance (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    ((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) *
          ((limitColumns input shape detach distinguished hTargetConnected
            hGenus).canonicalMatrix input 0).det +
        ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) *
          ((limitColumns input shape detach distinguished hTargetConnected
            hGenus).canonicalMatrix input 1).det +
        ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) *
          ((limitColumns input shape detach distinguished hTargetConnected
            hGenus).canonicalMatrix input 2).det = 0 :=
  (limitColumns input shape detach distinguished hTargetConnected
    hGenus).canonical_determinant_balance input

/-- The positive balance of Figure 34's three determinants, unconditionally. -/
theorem canonical_positiveBalance (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    BalancingValencyTwo.PositiveBalance
      ![(data.sourceEdgeIndex profile.first.1 : ℚ) - 1,
        (data.sourceEdgeIndex profile.second.1 : ℚ) - 1,
        (data.sourceEdgeIndex profile.first.1 : ℚ) +
          (data.sourceEdgeIndex profile.second.1 : ℚ)]
      (fun position ↦ ((limitColumns input shape detach distinguished hTargetConnected
        hGenus).canonicalMatrix input position).det) :=
  (limitColumns input shape detach distinguished hTargetConnected hGenus).positiveBalance input _

/-- **Figure 34's balanced family, unconditionally.**  Possibly singular
members are kept; this is a `Family`, not a `PresentedFamily`, because one
member is remote. -/
noncomputable def canonicalFamily (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    BalancedGlobal.Family (coordinate := Option target.edges) 3 data :=
  (limitColumns input shape detach distinguished hTargetConnected hGenus).canonicalFamily input

theorem canonicalFamily_candidate_datum (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (position : Fin 3) :
    ((canonicalFamily input shape detach distinguished hTargetConnected
        hGenus).candidate position).datum =
      ((limitColumns input shape detach distinguished hTargetConnected
        hGenus).member position).datum := rfl

/-- **Any nonsingular chosen member has an actual valid opposite-sign member**,
unconditionally; no nonsingularity is imposed on the other two. -/
theorem exists_valid_opposite (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 3)
    (hIncoming : ((limitColumns input shape detach distinguished hTargetConnected
      hGenus).canonicalMatrix input incoming).det ≠ 0) :
    ∃ outgoing, ((limitColumns input shape detach distinguished hTargetConnected
        hGenus).member outgoing).datum.Valid ∧
      ((limitColumns input shape detach distinguished hTargetConnected
          hGenus).canonicalMatrix input incoming).det *
        ((limitColumns input shape detach distinguished hTargetConnected
          hGenus).canonicalMatrix input outgoing).det < 0 :=
  (limitColumns input shape detach distinguished hTargetConnected
    hGenus).exists_valid_opposite input _ incoming hIncoming

end DraismaVargas.LocalCases.W2MkkLimitColumns
