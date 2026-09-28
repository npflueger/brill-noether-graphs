import DraismaVargas.LocalCases.W2R1IncomingMatching
import DraismaVargas.LocalCases.FiniteAtlasMarch

/-!
# `{w2-r1}`: the positive exit of an identified member, and the incoming side

Source: Draisma--Vargas Part I, case `{w2-r1}`, sub-cases `{w2-r1-nd3}`
(Figure 37) and `{w2-r1-nd2}` (Figure 38), and **Equation (10)**.

`W2R1IncomingMatching.exists_member_normalization` proves that an arbitrary
incoming `{w2-r1}` datum *is* one of Equation (10)'s two members, together with
a normalization receipt; `W2R1CommonBalance` proves Equation (10) and, from the
`W2R1LimitMatrix.limitColumns` receipt, the positive exit for an *identified*
member; `W2R1GraphData` transports a full-dimensional presentation between
members along the two-block stable-incidence dictionary.  This file combines
the last two into the identified-member exit with an outgoing full-dimensional
presentation, and states the incoming-side facts the wall dispatcher needs.

## What is proved here

* `memberMatrix`, `wallColumn`, `outgoingVelocity`, `outgoingVelocity_system`
  -- the transport inputs, the canonical outgoing chart velocity, and the
  linear system it solves.
* `exists_member_positive_exit_with_pencil` -- the identified-member exit with
  an *outgoing full-dimensional presentation* and the cleared pencil unpacked
  into its realization, scale and `BNExists` clauses.
* `family_presentation_incoming`, `family_incoming_nonzero`,
  `family_incoming_matrix` -- the incoming-side facts `hW25Incoming`,
  `hW25IncomingNonzero` and `hW25IncomingMatrix` of
  `A04FourTags.presentedProgressOfSupplies`, modulo the state--classifier
  equation, in the shape `A04MoreTags.ofW2P_incomingNonzero` /
  `ofW2P_incomingMatrix` state them for `w2P`.  They are stated on
  `W2R1GraphData.family` itself rather than on a `WallInput` wrapper, because
  `WallInput.ofTrivalent` only forwards `family`; the wall-input packaging is
  `A04R1Wiring`.
* `exists_w2R1_payload` -- the `w2R1` tag of the classifier names the `r1`
  leaf, and that leaf is a `W2R1SourceCandidates.Pair`.

Only the *selected* outgoing member is ever required nonsingular; that is
derived from Equation (10) --
`W2R1CommonBalance.LimitColumns.determinant_balance` through `positiveBalance`
and `BalancingValencyTwo.exists_opposite_of_positiveBalance` -- so no
nonsingularity is assumed of the unselected member.  No incoming family
membership, no `NoReturn`, no row bijection and no matrix identity is
hypothesised: each is proved upstream and consumed here.

The cleared pencil is on the **actual source subdivision** of the selected
member's realization.  Nothing here claims a requested `Spec`, a terminal
refinement, or a metric-length dictionary; those belong to the terminal
identification and the transport back to the requested core.

## Hypotheses, and why they can hold at once

The bundle of §3 is exactly the one
`W2R1IncomingMatching.exists_member_normalization` consumes: an actual
full-dimensional incoming presentation whose contraction of the single edge
between `a` and `b` is a forest, a genuine two-star at the contracted wall, a
W2 source input for it, and a `W2R1SourceCandidates.Pair` -- two distinct
ramification-one wall blocks with their literal occurrence profiles and the
`background ∉ {A₀, B₀}` clause.  `IncomingSourceCases.W2.Classification.r1`
hands out exactly those.  Nothing is added: in particular the `(2,2)` incoming
wall is *proved* (`W2R1IncomingCensus.divalent_endpoints`), and so is the
two-block selected census (`W2R1IncomingCensus.exists_member_selected_counts`).
-/

namespace DraismaVargas.LocalCases.W2R1ArbitraryIncomingExit

/-! ## A coordinate cancellation, at abstract types -/

section Cancellation

variable {α β γ δ : Type*}

/-- Going out through one occurrence dictionary and back through another
cancels, read backwards at the wall column: the common coordinate order's
`none` is the identified member's own wall occurrence. -/
private theorem symm_trans_cancel (e : α ≃ β) (A : γ ≃ β) (B : γ ≃ δ) (x : γ) :
    ((e.trans (A.symm.trans B)).trans B.symm).symm x = e.symm (A x) := by
  simp

end Cancellation


/-! ## §1  The identified-member exit, with a full-dimensional outgoing source -/

section Member

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open FullDimensionalSource
open W2R1SourceCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (pair : Pair data star) (hValid : data.Valid) (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation (pair.candidate incoming).datum coordinate)

/-- The two members' honest square matrices in the coordinate order one
identified member induces. -/
noncomputable def memberMatrix (outgoing : Fin 2) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix
    (W2R1GraphData.outgoingLabelling pair hValid incoming incomingFD outgoing).presentation

/-- The coordinate naming the regrown wall column. -/
noncomputable def wallColumn : coordinate :=
  W2R1CommonBalance.LimitColumns.wallColumn
    (W2R1GraphData.initialLabelling pair hValid incoming incomingFD)

/-- Canonical outgoing chart velocity at a nonsingular selected member. -/
noncomputable def outgoingVelocity (incomingVelocity : coordinate → ℚ)
    (outgoing : Fin 2) : coordinate → ℚ :=
  FiniteAtlasMarch.chartCoordinates
    (memberMatrix pair hValid incoming incomingFD outgoing)
    ((memberMatrix pair hValid incoming incomingFD incoming).mulVec incomingVelocity)

theorem outgoingVelocity_system (incomingVelocity : coordinate → ℚ) (outgoing : Fin 2)
    (hDet : (memberMatrix pair hValid incoming incomingFD outgoing).det ≠ 0) :
    (memberMatrix pair hValid incoming incomingFD incoming).mulVec incomingVelocity =
      (memberMatrix pair hValid incoming incomingFD outgoing).mulVec
        (outgoingVelocity pair hValid incoming incomingFD incomingVelocity outgoing) :=
  (FiniteAtlasMarch.mulVec_chartCoordinates _ hDet _).symm

/-- **The identified-member Equation (10) continuation.**  Equation (10)
selects a genuinely nonsingular opposite-sign member, the two-block
stable-incidence dictionary equips it with a full-dimensional presentation, and
the one-column cone-wall calculation supplies the positive rational step
together with its cleared rank-one pencil on the member's literal source
subdivision.  Only the chosen incoming member is assumed nonsingular. -/
theorem exists_member_positive_exit_with_pencil
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (wallColumn pair hValid incoming incomingFD) = 0)
    (hzpos : ∀ i, i ≠ wallColumn pair hValid incoming incomingFD → 0 < z i)
    (hIncomingDirection : incomingVelocity (wallColumn pair hValid incoming incomingFD) < 0) :
    ∃ outgoing : Fin 2,
      ∃ outgoingFD : FullDimensionalSourcePresentation
          (pair.candidate outgoing).datum coordinate,
        outgoingFD.labelling =
            W2R1GraphData.outgoingLabelling pair hValid incoming incomingFD outgoing ∧
        (memberMatrix pair hValid incoming incomingFD incoming).det *
            (memberMatrix pair hValid incoming incomingFD outgoing).det < 0 ∧
        ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (z + t • outgoingVelocity pair hValid incoming incomingFD
            incomingVelocity outgoing) i) ∧
          (memberMatrix pair hValid incoming incomingFD outgoing).mulVec
              (z + t • outgoingVelocity pair hValid incoming incomingFD
                incomingVelocity outgoing) =
            (memberMatrix pair hValid incoming incomingFD incoming).mulVec z +
              t • (memberMatrix pair hValid incoming incomingFD
                incoming).mulVec incomingVelocity ∧
          ∃ realization : (pair.candidate outgoing).datum.IntegralRealization,
            ∃ scale : ℕ, 0 < scale ∧
              (∀ column,
                (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                  (scale : ℚ) *
                    (z + t • outgoingVelocity pair hValid incoming incomingFD
                      incomingVelocity outgoing) column) ∧
              Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  have hIncoming : ((W2R1LimitMatrix.limitColumns pair hValid).squareMatrix
      (W2R1GraphData.initialLabelling pair hValid incoming incomingFD) incoming).det ≠ 0 :=
    W2R1GraphData.incomingDet_ne_zero pair hValid incoming incomingFD
  obtain ⟨outgoing, _hValid, hSign, δ, hδ, hStep⟩ :=
    (W2R1LimitMatrix.limitColumns pair hValid).exists_valid_positive_exit_with_pencil hValid
      (W2R1GraphData.initialLabelling pair hValid incoming incomingFD)
      hConnected hGenus wall incoming hIncoming z incomingVelocity
      (outgoingVelocity pair hValid incoming incomingFD incomingVelocity)
      hz hzpos
      (fun outgoing hDet ↦ outgoingVelocity_system pair hValid incoming incomingFD
        incomingVelocity outgoing hDet)
      hIncomingDirection
  have hOutgoing : (memberMatrix pair hValid incoming incomingFD outgoing).det ≠ 0 :=
    BalancedGlobal.det_ne_zero_of_mul_det_neg hSign
  refine ⟨outgoing,
    W2R1GraphData.outgoingPresentation pair hValid hConnected hGenus incoming outgoing
      incomingFD hOutgoing,
    rfl, hSign, δ, hδ, ?_⟩
  intro t ht htδ
  obtain ⟨hPositive, hMetric, ⟨pencil⟩⟩ := hStep t ht htδ
  exact ⟨hPositive, hMetric, pencil.realization, pencil.scale, pencil.scale_pos,
    pencil.targetLength_eq, pencil.bnExists⟩


/-! ### The incoming side of `WallProgress.presentedProgressOfWallInputs`

`hW25Incoming` is the identified position, `hW25IncomingNonzero` and
`hW25IncomingMatrix` the two facts about the family's presentation there.  They
are stated on `W2R1GraphData.family` itself; `WallInput.ofTrivalent` forwards
`family` unchanged, so the `WallInput` wrapper adds nothing mathematical and
lives in `A04R1Wiring`. -/

variable (input : W2SourceInput data star)

/-- **The `{w2-r1}` family presents the identified incoming member by its own
honest labelling.**  `W2R1GraphData.outgoingLabelling_self`: transport to the
common first member and back cancels both equivalences. -/
theorem family_presentation_incoming
    (incomingFD : FullDimensionalSourcePresentation (pair.candidate incoming).datum coordinate) :
    (W2R1GraphData.family pair input incoming incomingFD).presentation incoming =
      StableLengthMatrixLabelling.presentation incomingFD.labelling := by
  change (W2R1GraphData.outgoingLabelling pair input.valid incoming incomingFD
    incoming).presentation = _
  rw [W2R1GraphData.outgoingLabelling_self pair input.valid incoming incomingFD]

/-- **`hW25IncomingNonzero` for `w2R1`.** -/
theorem family_incoming_nonzero
    (incomingFD : FullDimensionalSourcePresentation (pair.candidate incoming).datum coordinate) :
    (GluingDatum.LengthMatrixPresentation.matrix
      ((W2R1GraphData.family pair input incoming incomingFD).presentation incoming)).det ≠ 0 := by
  rw [family_presentation_incoming pair incoming input incomingFD]
  exact incomingFD.det_ne_zero

/-- **`hW25IncomingMatrix` for `w2R1`, modulo the state--classifier equation.**
`hChart` is the whole of what is not local-case data: that the chart the march
currently occupies is the identified member's own honest length matrix. -/
theorem family_incoming_matrix
    (incomingFD : FullDimensionalSourcePresentation (pair.candidate incoming).datum coordinate)
    (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((W2R1GraphData.family pair input incoming incomingFD).presentation incoming) = chart := by
  rw [family_presentation_incoming pair incoming input incomingFD]
  exact hChart

end Member


/-! ## §3  From the classifier's tag

`IncomingSourceCases.Classification` is the ten-way router; its `w2R1` leaf is
`IncomingSourceCases.W2.Classification.r1`, whose fields are two distinct wall
blocks, their two `w2-r1` source profiles, and the `background ∉ {A₀, B₀}`
clause.  Those six fields **are** `W2R1SourceCandidates.Pair`, field for field,
so the payload extraction is a constructor match with nothing discarded. -/

section Classified

open DraismaVargas.Infrastructure GraphContraction GluingContraction
open ContractionRamification W4Assembly W4StableSource StableLocalProperties
open W2R1Target SecondEquation FullDimensionalSource WallDegeneration TargetExpansion
open W2R1SourceCandidates

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W2SourceInput (contractDatum data hc hab hOne) star)

/-- **The `w2R1` tag names the `r1` leaf, and the `r1` leaf is a `Pair`.** -/
theorem exists_w2R1_payload
    (classification : IncomingSourceCases.W2.Classification
      (contractDatum data hc hab hOne) star input)
    (hTag : classification.sourceCase = ClassifiedContinuation.SourceCase.w2R1) :
    Nonempty (Pair (contractDatum data hc hab hOne) star) := by
  cases classification with
  | m11 _ _ _ _ _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | m1k _ _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | mkk _ _ _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | p _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | r1 first second distinct firstProfile secondProfile background =>
      exact ⟨⟨first, second, distinct, firstProfile, secondProfile, background⟩⟩

end Classified

end DraismaVargas.LocalCases.W2R1ArbitraryIncomingExit
