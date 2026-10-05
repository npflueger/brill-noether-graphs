module

public import DraismaVargas.LocalCases.W2M1kLimitMatrix
public import DraismaVargas.LocalCases.W2M1kLeafLimitMatrix
public import DraismaVargas.LocalCases.W2M1kCommonBalance
public import DraismaVargas.LocalCases.W2M1kTransport

@[expose] public section

/-!
# Figure 33's limit columns, inhabited: Equation (7) unconditionally

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{w2-r2-nd3-M-1k}`, its Figure 33 and **Equation (7)**.  The identity proved
here differs from the display of Equation (7) in Part I as follows: both
brackets carry the factor two, `2(k c(e_1) + c(e_2) + k s) + 2(c(e_3) + k s)`,
as in Equation (6), whereas Part I displays the second bracket without it.
Both brackets vanish at a solution, so the balance is the same.

`W2M1kCommonBalance` proves Equation (7), `determinant_balance`,
`positiveBalance`, `exists_valid_opposite` and `canonicalFamily`
**conditionally** on an inhabitant of `W2M1kCommonBalance.LimitColumns`.  This
file builds that inhabitant from the three member constructions and so
discharges the condition on the case's actual input.  It is the M-1k analogue of `W2MkkLimitColumns` for Figure
34, and of `W2PLimitMatrix.limitColumns` / `nonempty_limitColumns` for Figure
35.

## The three members

* Position `0`, `M⁽¹⁾` (Base I.a), is `W2M1kSourceCandidates.LeafPair.candidate`
  with `W2M1kLeafRowDescent.leafStablePathEquiv` and
  `W2M1kLeafLimitMatrix.leaf_matrix_retained` / `leafMember_regrown`.
* Position `1`, `M⁽²⁾` (Base II.2.2.M), is
  `W2M1kSourceCandidates.DividedData.candidate` with
  `W2M1kRowDescent.dividedStablePathEquiv` and
  `W2M1kLimitMatrix.divided_matrix_retained` / `dividedMember_regrown`.
* Position `2`, `M⁽³⁾` (Base II.1.M), is `W2M1kSourceCandidates.joinedCandidate`
  with `W2M1kRowDescent.joinedStablePathEquiv` and
  `W2M1kLimitMatrix.joined_matrix_retained` / `joinedMember_regrown`.  It
  imposes no occurrence condition, so it lives over the incoming datum in every
  orientation.

**Positions `0` and `1` never live over the same datum.**  Writing `p₀`, `p₁`
for the unique index-one occurrence's
sheet in the two wall directions, `M⁽¹⁾` requires `p₀ = p₁`
(`LeafPair.aligned`) and `M⁽²⁾` requires `p₀ ≠ p₁` (`DividedData.pins_ne`), so
`W2M1kSourceCandidates.not_leafPair_and_dividedData` closes the door on a
receipt over one datum and `exists_leafPair_or_dividedData` says exactly one of
the two is available.  A receipt that places all three members over one datum
is therefore **vacuous over every datum**.  The member the incoming datum does
not carry is
built over the branch-swapped copy `W2M1kTransport` supplies, and is a member
*for* the incoming datum through `GluingDatum.SheetRelabeling.valid` composed
with `BalancedGlobal.Candidate.datum_valid` -- which is exactly what
`GlobalM1k.SecondPattern.remoteCertified` does, and what `LimitMember`'s
`valid_of_old` field (an implication `data.Valid → datum.Valid`, not an identity
of data) was designed for.

## Both orientations

`limitColumns` is total on the case's actual input.  It branches on the datum's
own orientation -- the decidable `pinSheet profile 0 = pinSheet profile 1` -- and
in each branch the member the datum **does** carry sits in its own Figure 33
slot over the incoming datum itself, while the other slot is filled remotely:

* `alignedOrientation` (`p₀ = p₁`, the datum is `M⁽¹⁾`-shaped): position `0` is
  local, position `1` is remote over the copy that swaps `p₀` with the leaf
  pair's second sheet (`W2M1kTransport.swapProfile_pins_ne`).  This is the
  orientation `GlobalM1k.swappedCandidates` is written for.
* `separatedOrientation` (`p₀ ≠ p₁`, the datum is `M⁽²⁾`-shaped): position `1`
  is local, position `0` is remote over the copy that swaps `p₀` with `p₁`
  (`W2M1kTransport.swapProfile_aligned`, the transport form of
  `W2SourceTransport.alignedProfile_aligned`).

So M-1k differs from M-kk here: position `1` is the remote one in the aligned
orientation only.  Over an `M⁽²⁾`-shaped datum the roles are exchanged --
position `1` local, position `0` remote -- and
`limitColumns_member_one_of_separated` /
`limitColumns_member_zero_of_aligned` record which. Nothing is assumed about
which orientation occurs, and `nonempty_limitColumns` is unconditional.

The remote member's regrown column is read back in the **incoming** datum's
stable rows and at the **incoming** datum's indices: the rows travel by
`LimitChainCore.Gauge.row_mk`, `k` is a gauge invariant
(`W2M1kTransport.swapShape_k`, a `rfl`), and Figure 33's background `s` is
carried by `W2M1kTransport.swap_backgroundColumn` after one anchor move by
`W2M1kLimitMatrix.backgroundColumn_congr`.  The leaf member needs no background
transport at all: its box has none (`σ¹(J₀,1) = σ¹(J₁,1) = 0`).

## What is not built here

The `LimitChainCore.GraphData` packaging and the presented-family equivalence
are built elsewhere; this file produces a `BalancedGlobal.Family`, not a
`PresentedFamily`, exactly as `W2M1kCommonBalance.LimitColumns.family` does and
for the same reason -- one member is remote, so `GlobalM1k`'s swapped route
(`GlobalM1k.swappedBalancedFamily`, `W2M1kSwapped.SwappedBundle`) is the one
available.
-/

namespace DraismaVargas.LocalCases.W2M1kLimitColumns

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StableSourceMatrix
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary
open W2M1kSourceCandidates
open W2M1kRowDescent W2M1kLeafRowDescent
open W2M1kTransport

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-! ## The three members over the incoming datum -/

/-- **`M⁽¹⁾` over the incoming datum.**  Available exactly when the datum is
aligned, which is what a `LeafPair` records. -/
noncomputable def localLeafMember (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) : W2M1kCommonBalance.LimitMember data wall where
  right := (LeafPair.candidate input shape pair).right
  datum := (LeafPair.candidate input shape pair).datum
  valid_of_old := (LeafPair.candidate input shape pair).datum_valid
  row := leafStablePathEquiv input shape pair
  retained := W2M1kLeafLimitMatrix.leaf_matrix_retained input shape pair

@[simp] theorem localLeafMember_datum (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    (localLeafMember input shape pair).datum = (LeafPair.candidate input shape pair).datum := rfl

/-- `c⁽¹⁾ = 2c(e₁)`, with no background term. -/
theorem localLeafMember_regrown (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (path : StablePath data) :
    (localLeafMember input shape pair).newColumnValue path =
      W2M1kCommonBalance.firstNewColumn profile path :=
  (W2M1kLeafLimitMatrix.leafMember_regrown input shape pair path).trans
    (W2M1kCommonBalance.firstNewColumn_eq_two_mul profile path).symm

/-- **`M⁽²⁾` over the incoming datum.**  Available exactly when the datum's two
pinned sheets are distinct, which is what a `DividedData` records. -/
noncomputable def localDividedMember (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) : W2M1kCommonBalance.LimitMember data wall where
  right := (DividedData.candidate shape divided).right
  datum := (DividedData.candidate shape divided).datum
  valid_of_old := (DividedData.candidate shape divided).datum_valid
  row := dividedStablePathEquiv input shape divided
  retained := W2M1kLimitMatrix.divided_matrix_retained input shape divided

@[simp] theorem localDividedMember_datum (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) :
    (localDividedMember input shape divided).datum =
      (DividedData.candidate shape divided).datum := rfl

/-- `c⁽²⁾ = c(e₁) + c(e₂)/(k-1) + s`.  The one anchor move is
`W2M1kLimitMatrix.backgroundColumn_congr`: the limit matrix reads `s` at the
pinned sheet, the receipt at the block's own representative, and Figure 33's `s`
is a function of the wall block rather than of its anchor. -/
theorem localDividedMember_regrown (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (path : StablePath data) :
    (localDividedMember input shape divided).newColumnValue path =
      W2M1kCommonBalance.secondNewColumn profile shape path := by
  refine (W2M1kLimitMatrix.dividedMember_regrown input shape divided path).trans ?_
  show _ = W2M1kCommonBalance.secondNewColumn profile shape path
  unfold W2M1kCommonBalance.secondNewColumn
  rw [W2M1kLimitMatrix.backgroundColumn_congr data wall
    ((pinSheet_rel (profile := profile) profile.doubleLabel).symm) path (star.edge 0)]
  rfl

/-- **`M⁽³⁾` over the incoming datum.**  It needs no occurrence hypothesis, so it
is available over every datum of the case in either orientation. -/
noncomputable def joinedMember (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) : W2M1kCommonBalance.LimitMember data wall where
  right := (joinedCandidate star geometry).right
  datum := (joinedCandidate star geometry).datum
  valid_of_old := (joinedCandidate star geometry).datum_valid
  row := joinedStablePathEquiv input shape geometry
  retained := W2M1kLimitMatrix.joined_matrix_retained input shape geometry

@[simp] theorem joinedMember_datum (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) :
    (joinedMember input shape geometry).datum = (joinedCandidate star geometry).datum := rfl

/-- `c⁽³⁾ = c(e₃)/(k+1) + s`. -/
theorem joinedMember_regrown (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (path : StablePath data) :
    (joinedMember input shape geometry).newColumnValue path =
      W2M1kCommonBalance.thirdNewColumn profile shape path :=
  W2M1kLimitMatrix.joinedMember_regrown input shape geometry path

/-! ## The rows travel by the gauge -/

/-- `e₁`'s stable row travels by the gauge. -/
theorem swapProfile_firstRow (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    W2M1kLimitMatrix.firstRow (swapProfile profile hConnected other hOther) =
      (swapGauge profile hConnected other hOther).row (W2M1kCommonBalance.firstRow profile) :=
  ((swapGauge profile hConnected other hOther).row_mk profile.first.1
    profile.first_survives).symm

/-- `e₂`'s stable row travels by the gauge. -/
theorem swapProfile_secondRow (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    W2M1kLimitMatrix.secondRow (swapProfile profile hConnected other hOther) =
      (swapGauge profile hConnected other hOther).row (W2M1kCommonBalance.secondRow profile) :=
  ((swapGauge profile hConnected other hOther).row_mk profile.second.1
    profile.second_survives).symm

/-- `e₃`'s stable row travels by the gauge. -/
theorem swapProfile_thirdRow (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    W2M1kLimitMatrix.thirdRow (swapProfile profile hConnected other hOther) =
      (swapGauge profile hConnected other hOther).row (W2M1kCommonBalance.thirdRow profile) :=
  ((swapGauge profile hConnected other hOther).row_mk profile.third.1
    profile.third_survives).symm

/-! ## The two remote members -/

/-- **`M⁽²⁾` over the branch-swapped copy, read as a member for the incoming
datum.**  `valid_of_old` composes the relabelling's own validity transport with
the candidate's -- the route `GlobalM1k.SecondPattern.remoteCertified` takes;
`row` composes the gauge's stable-row bijection with the row descent over the
copy; `retained` composes `W2M1kLimitMatrix.divided_matrix_retained` over the
copy with `LimitChainCore.Gauge.matrix_gauge`. -/
noncomputable def remoteDividedMember (input : W2SourceInput data star) (shape : Shape profile)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (divided : DividedData (swapProfile profile input.valid.1 other hOther)) :
    W2M1kCommonBalance.LimitMember data wall where
  right := (DividedData.candidate (swapShape shape input.valid.1 other hOther) divided).right
  datum := (DividedData.candidate (swapShape shape input.valid.1 other hOther) divided).datum
  valid_of_old := fun hValid ↦
    (DividedData.candidate (swapShape shape input.valid.1 other hOther) divided).datum_valid
      ((swapRelabeling profile other hOther).valid hValid)
  row := (swapGauge profile input.valid.1 other hOther).row.trans
    (dividedStablePathEquiv (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) divided)
  retained := fun path place ↦
    (W2M1kLimitMatrix.divided_matrix_retained (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) divided
      ((swapGauge profile input.valid.1 other hOther).row path) place).trans
      ((swapGauge profile input.valid.1 other hOther).matrix_gauge path place)

/-- **The remote `M⁽²⁾`'s regrown column is Figure 33's `c⁽²⁾`**, read in the
*incoming* datum's rows and at the *incoming* datum's indices: the rows travel
by the gauge, `k` is a gauge invariant, and `s` is carried by
`W2M1kTransport.swap_backgroundColumn` after one anchor move. -/
theorem remoteDividedMember_regrown (input : W2SourceInput data star) (shape : Shape profile)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (divided : DividedData (swapProfile profile input.valid.1 other hOther))
    (path : StablePath data) :
    (remoteDividedMember input shape other hOther divided).newColumnValue path =
      W2M1kCommonBalance.secondNewColumn profile shape path := by
  have hAnchor : ((swapRelabeling profile other hOther).apply.vertexPartition wall).Rel
      (pinSheet (swapProfile profile input.valid.1 other hOther)
        (swapProfile profile input.valid.1 other hOther).doubleLabel) block.1 := by
    have hRel := (pinSheet_rel
      (profile := swapProfile profile input.valid.1 other hOther)
      (swapProfile profile input.valid.1 other hOther).doubleLabel).symm
    rwa [swapBlock_val] at hRel
  have h := W2M1kLimitMatrix.dividedMember_regrown (swapInput input other hOther)
    (swapShape shape input.valid.1 other hOther) divided
    ((swapGauge profile input.valid.1 other hOther).row path)
  rw [swapProfile_firstRow, swapProfile_secondRow,
    W2M1kLimitMatrix.backgroundColumn_congr _ wall hAnchor, swap_backgroundColumn] at h
  simp only [EmbeddingLike.apply_eq_iff_eq] at h
  exact h

/-- **`M⁽¹⁾` over the branch-swapped copy, read as a member for the incoming
datum.**  The mirror of `remoteDividedMember`; the leaf member's box has no
background term, so no background transport is needed here. -/
noncomputable def remoteLeafMember (input : W2SourceInput data star) (shape : Shape profile)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (pair : LeafPair (swapProfile profile input.valid.1 other hOther)) :
    W2M1kCommonBalance.LimitMember data wall where
  right := (LeafPair.candidate (swapInput input other hOther)
    (swapShape shape input.valid.1 other hOther) pair).right
  datum := (LeafPair.candidate (swapInput input other hOther)
    (swapShape shape input.valid.1 other hOther) pair).datum
  valid_of_old := fun hValid ↦ (LeafPair.candidate (swapInput input other hOther)
    (swapShape shape input.valid.1 other hOther) pair).datum_valid
      ((swapRelabeling profile other hOther).valid hValid)
  row := (swapGauge profile input.valid.1 other hOther).row.trans
    (leafStablePathEquiv (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) pair)
  retained := fun path place ↦
    (W2M1kLeafLimitMatrix.leaf_matrix_retained (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) pair
      ((swapGauge profile input.valid.1 other hOther).row path) place).trans
      ((swapGauge profile input.valid.1 other hOther).matrix_gauge path place)

/-- **The remote `M⁽¹⁾`'s regrown column is Figure 33's `c⁽¹⁾ = 2c(e₁)`**, read
in the incoming datum's rows. -/
theorem remoteLeafMember_regrown (input : W2SourceInput data star) (shape : Shape profile)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (pair : LeafPair (swapProfile profile input.valid.1 other hOther))
    (path : StablePath data) :
    (remoteLeafMember input shape other hOther pair).newColumnValue path =
      W2M1kCommonBalance.firstNewColumn profile path := by
  have h := W2M1kLeafLimitMatrix.leafMember_regrown (swapInput input other hOther)
    (swapShape shape input.valid.1 other hOther) pair
    ((swapGauge profile input.valid.1 other hOther).row path)
  rw [swapProfile_firstRow] at h
  simp only [EmbeddingLike.apply_eq_iff_eq] at h
  rw [W2M1kCommonBalance.firstNewColumn_eq_two_mul]
  exact h

/-! ## The remote data are not a choice the reader makes -/

/-- The `M⁽²⁾` datum over the copy of an **aligned** datum.  Swapping the pinned
sheet with the leaf pair's second sheet separates the copy's two pinned sheets,
and a block of size `k + 1 ≥ 3` then supplies the residual class. -/
noncomputable def remoteDivided (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) :
    DividedData (swapProfile profile input.valid.1 pair.second pair.rel_second) :=
  (exists_dividedData (swapShape shape input.valid.1 pair.second pair.rel_second)
    (swapProfile_pins_ne shape input.valid.1 pair.aligned hTargetConnected hGenus
      pair.second pair.rel_second pair.ne_second)).some

/-- The `M⁽¹⁾` datum over the copy of a **separated** datum.  Swapping the two
pinned sheets aligns the copy, and the same block supplies the leaf pair. -/
noncomputable def remoteLeaf (input : W2SourceInput data star) (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    LeafPair (swapProfile profile input.valid.1 (pinSheet profile 1)
      (W2SourceTransport.alignedTogether profile)) :=
  (exists_leafPair (swapShape shape input.valid.1 (pinSheet profile 1)
      (W2SourceTransport.alignedTogether profile))
    (swapProfile_aligned shape input.valid.1 hTargetConnected hGenus)).some

/-! ## The join, one orientation at a time -/

/-- **Base I.a orientation**: `p₀ = p₁`, so the datum carries `M⁽¹⁾`; position
`0` is over the incoming datum and position `1` is remote.  This is the
orientation `GlobalM1k.swappedCandidates` describes. -/
noncomputable def alignedOrientation (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) : W2M1kCommonBalance.LimitColumns profile shape where
  member := ![localLeafMember input shape pair,
    remoteDividedMember input shape pair.second pair.rel_second
      (remoteDivided input shape pair hTargetConnected hGenus),
    joinedMember input shape (pair.geometry shape)]
  regrown := by
    intro position path
    fin_cases position
    · exact localLeafMember_regrown input shape pair path
    · exact remoteDividedMember_regrown input shape pair.second pair.rel_second
        (remoteDivided input shape pair hTargetConnected hGenus) path
    · exact joinedMember_regrown input shape (pair.geometry shape) path

/-- **Base II.2.2.M orientation**: `p₀ ≠ p₁`, so the datum carries `M⁽²⁾`;
position `1` is over the incoming datum and position `0` is remote: here it is
position `0`, not position `1`, that is remote. -/
noncomputable def separatedOrientation (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) : W2M1kCommonBalance.LimitColumns profile shape where
  member := ![remoteLeafMember input shape (pinSheet profile 1)
      (W2SourceTransport.alignedTogether profile)
      (remoteLeaf input shape hTargetConnected hGenus),
    localDividedMember input shape divided,
    joinedMember input shape (divided.geometry shape)]
  regrown := by
    intro position path
    fin_cases position
    · exact remoteLeafMember_regrown input shape (pinSheet profile 1)
        (W2SourceTransport.alignedTogether profile)
        (remoteLeaf input shape hTargetConnected hGenus) path
    · exact localDividedMember_regrown input shape divided path
    · exact joinedMember_regrown input shape (divided.geometry shape) path

@[simp] theorem alignedOrientation_member_zero (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    (alignedOrientation input shape pair hTargetConnected hGenus).member 0 =
      localLeafMember input shape pair := rfl

@[simp] theorem separatedOrientation_member_one (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    (separatedOrientation input shape divided hTargetConnected hGenus).member 1 =
      localDividedMember input shape divided := rfl

/-- **Position `1` of the aligned orientation is the remote `M⁽²⁾`**, over the
copy `W2M1kTransport.swapRelabeling_apply_eq_swappedData_leaf` identifies with
`W2M1kSwapped.swappedData` at `M⁽¹⁾`'s own geometry. -/
@[simp] theorem alignedOrientation_member_one (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    (alignedOrientation input shape pair hTargetConnected hGenus).member 1 =
      remoteDividedMember input shape pair.second pair.rel_second
        (remoteDivided input shape pair hTargetConnected hGenus) := rfl

/-- **Position `0` of the separated orientation is the remote `M⁽¹⁾`**, over the
copy `W2M1kTransport.swapRelabeling_apply_eq_swappedData_divided` identifies
with `W2M1kSwapped.swappedData` at `M⁽²⁾`'s own geometry.  This is the
orientation in which it is position `0`, not position `1`, that is remote. -/
@[simp] theorem separatedOrientation_member_zero (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    (separatedOrientation input shape divided hTargetConnected hGenus).member 0 =
      remoteLeafMember input shape (pinSheet profile 1)
        (W2SourceTransport.alignedTogether profile)
        (remoteLeaf input shape hTargetConnected hGenus) := rfl

@[simp] theorem alignedOrientation_member_two (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    (alignedOrientation input shape pair hTargetConnected hGenus).member 2 =
      joinedMember input shape (pair.geometry shape) := rfl

@[simp] theorem separatedOrientation_member_two (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    (separatedOrientation input shape divided hTargetConnected hGenus).member 2 =
      joinedMember input shape (divided.geometry shape) := rfl

/-- **`W2M1kCommonBalance.LimitColumns` is inhabited on the case's actual input,
in both orientations.**  The datum decides which orientation occurs -- exactly
one of `LeafPair`, `DividedData` is available over it
(`exists_leafPair_or_dividedData`, `not_leafPair_and_dividedData`) -- and no
hypothesis about that choice is imposed.  The two standing target hypotheses are
the ones `W2M1kSwapped.separated` already consumes. -/
noncomputable def limitColumns (input : W2SourceInput data star) (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    W2M1kCommonBalance.LimitColumns profile shape :=
  if hAligned : pinSheet profile 0 = pinSheet profile 1 then
    alignedOrientation input shape (exists_leafPair shape hAligned).some
      hTargetConnected hGenus
  else
    separatedOrientation input shape (exists_dividedData shape hAligned).some
      hTargetConnected hGenus

theorem limitColumns_eq_alignedOrientation (input : W2SourceInput data star)
    (shape : Shape profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) (hAligned : pinSheet profile 0 = pinSheet profile 1) :
    limitColumns input shape hTargetConnected hGenus =
      alignedOrientation input shape (exists_leafPair shape hAligned).some
        hTargetConnected hGenus :=
  dite_eq_left hAligned

theorem limitColumns_eq_separatedOrientation (input : W2SourceInput data star)
    (shape : Shape profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) (hSeparated : pinSheet profile 0 ≠ pinSheet profile 1) :
    limitColumns input shape hTargetConnected hGenus =
      separatedOrientation input shape (exists_dividedData shape hSeparated).some
        hTargetConnected hGenus :=
  dite_eq_right hSeparated

/-- **Over an `M⁽¹⁾`-shaped datum the leaf member sits in its own Figure 33
slot, over the incoming datum.**  Base I.a. -/
theorem limitColumns_member_zero_of_aligned (input : W2SourceInput data star)
    (shape : Shape profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) (hAligned : pinSheet profile 0 = pinSheet profile 1) :
    (limitColumns input shape hTargetConnected hGenus).member 0 =
      localLeafMember input shape (exists_leafPair shape hAligned).some := by
  rw [limitColumns_eq_alignedOrientation input shape hTargetConnected hGenus hAligned]
  rfl

/-- **Over an `M⁽²⁾`-shaped datum the divided member sits in its own Figure 33
slot, over the incoming datum, and it is position `0` that is remote.**  Base
II.2.2.M. -/
theorem limitColumns_member_one_of_separated (input : W2SourceInput data star)
    (shape : Shape profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) (hSeparated : pinSheet profile 0 ≠ pinSheet profile 1) :
    (limitColumns input shape hTargetConnected hGenus).member 1 =
      localDividedMember input shape (exists_dividedData shape hSeparated).some := by
  rw [limitColumns_eq_separatedOrientation input shape hTargetConnected hGenus hSeparated]
  rfl

/-- `M⁽³⁾` is over the incoming datum in either orientation. -/
theorem limitColumns_member_two_of_aligned (input : W2SourceInput data star)
    (shape : Shape profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) (hAligned : pinSheet profile 0 = pinSheet profile 1) :
    (limitColumns input shape hTargetConnected hGenus).member 2 =
      joinedMember input shape (((exists_leafPair shape hAligned).some).geometry shape) := by
  rw [limitColumns_eq_alignedOrientation input shape hTargetConnected hGenus hAligned]
  rfl

theorem limitColumns_member_two_of_separated (input : W2SourceInput data star)
    (shape : Shape profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) (hSeparated : pinSheet profile 0 ≠ pinSheet profile 1) :
    (limitColumns input shape hTargetConnected hGenus).member 2 =
      joinedMember input shape (((exists_dividedData shape hSeparated).some).geometry shape) := by
  rw [limitColumns_eq_separatedOrientation input shape hTargetConnected hGenus hSeparated]
  rfl

/-- **Non-vacuity.**  Every actual `w2M1k` datum of the case, on a connected
genus-zero target, inhabits `W2M1kCommonBalance.LimitColumns`, so nothing
downstream of it is vacuous.  Contrast a receipt with `LeafPair` and
`DividedData` over one datum as hypotheses, which is empty
(`not_leafPair_and_dividedData`). -/
theorem nonempty_limitColumns (input : W2SourceInput data star) (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    Nonempty (W2M1kCommonBalance.LimitColumns profile shape) :=
  ⟨limitColumns input shape hTargetConnected hGenus⟩

/-! ## The unconditional statements -/

section Coordinates

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **Equation (7) at a supplied honest square labelling, unconditionally.**
`W2M1kCommonBalance.LimitColumns.determinant_balance` is proved there
conditionally on an inhabitant; here the condition is discharged. -/
theorem determinant_balance (input : W2SourceInput data star) (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      ((limitColumns input shape hTargetConnected hGenus).member 0).datum coordinate) :
    1 * ((limitColumns input shape hTargetConnected hGenus).squareMatrix initial 0).det +
        2 * ((shape.k : ℚ) - 1) *
          ((limitColumns input shape hTargetConnected hGenus).squareMatrix initial 1).det +
        2 * ((shape.k : ℚ) + 1) *
          ((limitColumns input shape hTargetConnected hGenus).squareMatrix initial 2).det = 0 :=
  (limitColumns input shape hTargetConnected hGenus).determinant_balance input initial

/-- The positive balance at a supplied labelling, unconditionally. -/
theorem positiveBalance (input : W2SourceInput data star) (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      ((limitColumns input shape hTargetConnected hGenus).member 0).datum coordinate) :
    BalancingValencyTwo.PositiveBalance
      ![1, 2 * ((shape.k : ℚ) - 1), 2 * ((shape.k : ℚ) + 1)]
      (fun position ↦ ((limitColumns input shape hTargetConnected
        hGenus).squareMatrix initial position).det) :=
  (limitColumns input shape hTargetConnected hGenus).positiveBalance input initial

/-- Figure 33's balanced family at a supplied labelling, unconditionally. -/
noncomputable def family (input : W2SourceInput data star) (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      ((limitColumns input shape hTargetConnected hGenus).member 0).datum coordinate) :
    BalancedGlobal.Family (coordinate := coordinate) 3 data :=
  (limitColumns input shape hTargetConnected hGenus).family input initial

end Coordinates

/-- **Equation (7) for Figure 33's three actual members, unconditionally**
(with both brackets carrying the factor two; see the module docstring).
`W2M1kCommonBalance.LimitColumns.canonical_determinant_balance` is proved there
conditionally on an inhabitant; here the condition is discharged.  The weights
are
`1`, `2(k-1)`, `2(k+1)` -- the members' own new-edge block cardinalities,
doubled at the two positions whose boxes are not already doubled -- and no
member is assumed nonsingular. -/
theorem canonical_determinant_balance (input : W2SourceInput data star) (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    1 * ((limitColumns input shape hTargetConnected hGenus).canonicalMatrix input 0).det +
        2 * ((shape.k : ℚ) - 1) *
          ((limitColumns input shape hTargetConnected hGenus).canonicalMatrix input 1).det +
        2 * ((shape.k : ℚ) + 1) *
          ((limitColumns input shape hTargetConnected hGenus).canonicalMatrix input 2).det = 0 :=
  (limitColumns input shape hTargetConnected hGenus).canonical_determinant_balance input

/-- The positive balance of Figure 33's three determinants, unconditionally. -/
theorem canonical_positiveBalance (input : W2SourceInput data star) (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    BalancingValencyTwo.PositiveBalance
      ![1, 2 * ((shape.k : ℚ) - 1), 2 * ((shape.k : ℚ) + 1)]
      (fun position ↦ ((limitColumns input shape hTargetConnected
        hGenus).canonicalMatrix input position).det) :=
  (limitColumns input shape hTargetConnected hGenus).positiveBalance input _

/-- **Figure 33's balanced family, unconditionally.**  Possibly singular members
are kept; this is a `Family`, not a `PresentedFamily`, because one member is
remote. -/
noncomputable def canonicalFamily (input : W2SourceInput data star) (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    BalancedGlobal.Family (coordinate := Option target.edges) 3 data :=
  (limitColumns input shape hTargetConnected hGenus).canonicalFamily input

theorem canonicalFamily_candidate_datum (input : W2SourceInput data star) (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (position : Fin 3) :
    ((canonicalFamily input shape hTargetConnected hGenus).candidate position).datum =
      ((limitColumns input shape hTargetConnected hGenus).member position).datum := rfl

/-- **Any nonsingular chosen member has an actual valid opposite-sign member**,
unconditionally; no nonsingularity is imposed on the other two.  Validity of the
remote member is `GluingDatum.SheetRelabeling.valid` composed with
`BalancedGlobal.Candidate.datum_valid`, which is
`GlobalM1k.SecondPattern.remoteCertified`'s own route. -/
theorem exists_valid_opposite (input : W2SourceInput data star) (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 3)
    (hIncoming : ((limitColumns input shape hTargetConnected
      hGenus).canonicalMatrix input incoming).det ≠ 0) :
    ∃ outgoing, ((limitColumns input shape hTargetConnected
        hGenus).member outgoing).datum.Valid ∧
      ((limitColumns input shape hTargetConnected hGenus).canonicalMatrix input incoming).det *
        ((limitColumns input shape hTargetConnected
          hGenus).canonicalMatrix input outgoing).det < 0 :=
  (limitColumns input shape hTargetConnected hGenus).exists_valid_opposite input _
    incoming hIncoming

end DraismaVargas.LocalCases.W2M1kLimitColumns
