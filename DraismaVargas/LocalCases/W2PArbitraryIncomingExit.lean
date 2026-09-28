import DraismaVargas.LocalCases.W2PIncomingMatching
import DraismaVargas.LocalCases.W2PArbitraryExit
import DraismaVargas.LocalCases.FiniteAtlasMarch
import DraismaVargas.LocalCases.IncomingSourceCases

/-!
# `{w2-r2-nd3-P}`: the exit at an identified member, and the `w2P` payload

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-P}`, Figure 35 and
Equation (9).

`W2PIncomingMatching.exists_member_normalization` proves that an arbitrary
incoming `w2P` datum *is* one of the three named Figure 35 members, together
with a normalization receipt; `W2PCommonBalance` proves Equation (9) and, from
the `W2PLimitMatrix.limitColumns` receipt, the positive exit for an
*identified* member; `W2PArbitraryExit` transports a full-dimensional
presentation between members along the stable-incidence dictionary.  This file
combines the last two into an identified-member exit with a full-dimensional
outgoing source, and extracts the chain's hypothesis bundle from the
classifier's `w2P` tag.  `W2PGraphTracking` then restates the exit in the
**incoming cover's own coordinates**, together with the tracking of the
row-labelled graph.

## What "original coordinate" means, and where it comes from

The original-coordinate form of the exit is phrased against `fullDim`, the
incoming cover's own honest full-dimensional presentation:

* the wall coordinate is `fullDim.labelling.targetEdge.symm contracted`, the
  column of the actual contracted edge of the incoming target, in the incoming
  cover's own coordinate order;
* both determinants and the affine metric equation use
  `GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation`,
  the incoming cover's own length matrix on its own retained stable rows.

Neither is re-derived here.  `W3Nd2IncomingMemberMatching.NormalizedAgainst`
records that the transported member carries an honest presentation whose
`targetEdge` is the original labelling composed with the actual occurrence map
and whose length matrix is equal to the original one **entry by entry**; the
`Option` column dictionary of `exists_member_normalization` identifies `none`
with the literal contracted occurrence
(`M11IncomingCoordinates.incomingColumnEquiv_none`), which turns the member's
wall column into the original one.

## What is proved here

* `memberMatrix`, `wallColumn`, `outgoingVelocity`, `outgoingVelocity_system`
  -- the transport inputs, the canonical outgoing chart velocity, and the
  linear system it solves.
* `exists_member_positive_exit_with_pencil` -- the identified-member exit with
  an *outgoing full-dimensional presentation* and the cleared pencil unpacked
  into its realization, scale and `BNExists` clauses: full-dimensional
  outgoing source, opposite determinant sign, positivity on the whole segment,
  the exact affine metric equation, and the cleared rank-one pencil at an
  explicit integral scale.
* `exists_w2P_payload` -- the `w2P` tag names the `p` leaf of the
  classification, and that leaf is this chain's hypothesis bundle.

Only the *selected* outgoing member is ever required nonsingular; that is
derived from Equation (9) -- `W2PCommonBalance.LimitColumns.determinant_balance`
through `positiveBalance` and `BalancingValencyTwo.exists_opposite_of_positiveBalance`
-- so no nonsingularity is assumed of the unselected members.  No incoming
family membership, no `NoReturn`, no row bijection and no matrix identity is
hypothesised: each is proved in the modules above and used here.

The cleared pencil is on the **actual source subdivision** of the selected
member's realization.  Nothing here claims a requested `Spec`, a terminal
refinement, or a metric-length dictionary; those belong to the terminal stage
of the construction.

## Hypotheses, and why they can hold at once

The bundle is exactly the one `W2PIncomingMatching.exists_member_normalization`
consumes: an actual full-dimensional incoming presentation whose contraction of
the single edge between `a` and `b` is a forest, a genuine two-star at the
contracted wall, a W2 source input for it, a `w2-r2-nd3` source profile of a
wall block with `W2PSourceCandidates.Shape` (Cardinality P), and the
classifier's `background` field.  `IncomingSourceCases.W2.Classification.p`
hands out exactly those.  Nothing is added: in particular the `(2,2)` incoming
wall is *proved* (`W2PIncomingCensus.divalent_endpoints`), not assumed, and so
is the selected-class census.
-/

namespace DraismaVargas.LocalCases.W2PArbitraryIncomingExit

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
open W2PSourceCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (input : W2SourceInput data star) (shape : Shape profile) (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    (W2PCommonBalance.members profile shape incoming).datum coordinate)

/-- The three members' honest square matrices in the coordinate order one
identified member induces. -/
noncomputable def memberMatrix (outgoing : Fin 3) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix
    (W2PArbitraryExit.outgoingLabelling input shape incoming incomingFD outgoing).presentation

/-- The coordinate naming the regrown wall column. -/
noncomputable def wallColumn : coordinate :=
  W2PCommonBalance.LimitColumns.wallColumn
    (W2PArbitraryExit.initialLabelling input shape incoming incomingFD)

/-- Canonical outgoing chart velocity at a nonsingular selected member. -/
noncomputable def outgoingVelocity (incomingVelocity : coordinate → ℚ)
    (outgoing : Fin 3) : coordinate → ℚ :=
  FiniteAtlasMarch.chartCoordinates
    (memberMatrix input shape incoming incomingFD outgoing)
    ((memberMatrix input shape incoming incomingFD incoming).mulVec incomingVelocity)

theorem outgoingVelocity_system (incomingVelocity : coordinate → ℚ) (outgoing : Fin 3)
    (hDet : (memberMatrix input shape incoming incomingFD outgoing).det ≠ 0) :
    (memberMatrix input shape incoming incomingFD incoming).mulVec incomingVelocity =
      (memberMatrix input shape incoming incomingFD outgoing).mulVec
        (outgoingVelocity input shape incoming incomingFD incomingVelocity outgoing) :=
  (FiniteAtlasMarch.mulVec_chartCoordinates _ hDet _).symm

/-- **The identified-member Figure 35 continuation.**  Equation (9) selects a
genuinely nonsingular opposite-sign member, the stable-incidence dictionary
equips it with a full-dimensional presentation, and the one-column cone-wall
calculation supplies the positive rational step together with its cleared
rank-one pencil on the member's literal source subdivision.  Only the chosen
incoming member is assumed nonsingular. -/
theorem exists_member_positive_exit_with_pencil
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (wallColumn input shape incoming incomingFD) = 0)
    (hzpos : ∀ i, i ≠ wallColumn input shape incoming incomingFD → 0 < z i)
    (hIncomingDirection : incomingVelocity (wallColumn input shape incoming incomingFD) < 0) :
    ∃ outgoing : Fin 3,
      ∃ outgoingFD : FullDimensionalSourcePresentation
          (W2PCommonBalance.members profile shape outgoing).datum coordinate,
        outgoingFD.labelling =
            W2PArbitraryExit.outgoingLabelling input shape incoming incomingFD outgoing ∧
        (memberMatrix input shape incoming incomingFD incoming).det *
            (memberMatrix input shape incoming incomingFD outgoing).det < 0 ∧
        ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (z + t • outgoingVelocity input shape incoming incomingFD
            incomingVelocity outgoing) i) ∧
          (memberMatrix input shape incoming incomingFD outgoing).mulVec
              (z + t • outgoingVelocity input shape incoming incomingFD
                incomingVelocity outgoing) =
            (memberMatrix input shape incoming incomingFD incoming).mulVec z +
              t • (memberMatrix input shape incoming incomingFD
                incoming).mulVec incomingVelocity ∧
          ∃ realization :
              (W2PCommonBalance.members profile shape outgoing).datum.IntegralRealization,
            ∃ scale : ℕ, 0 < scale ∧
              (∀ column,
                (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                  (scale : ℚ) *
                    (z + t • outgoingVelocity input shape incoming incomingFD
                      incomingVelocity outgoing) column) ∧
              Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  have hIncoming : ((W2PLimitMatrix.limitColumns input shape).squareMatrix
      (W2PArbitraryExit.initialLabelling input shape incoming incomingFD) incoming).det ≠ 0 :=
    W2PArbitraryExit.incomingDet_ne_zero input shape incoming incomingFD
  obtain ⟨outgoing, _hValid, hSign, δ, hδ, hStep⟩ :=
    (W2PLimitMatrix.limitColumns input shape).exists_valid_positive_exit_with_pencil input
      (W2PArbitraryExit.initialLabelling input shape incoming incomingFD)
      hConnected hGenus wall incoming hIncoming z incomingVelocity
      (outgoingVelocity input shape incoming incomingFD incomingVelocity)
      hz hzpos
      (fun outgoing hDet ↦ outgoingVelocity_system input shape incoming incomingFD
        incomingVelocity outgoing hDet)
      hIncomingDirection
  have hOutgoing : (memberMatrix input shape incoming incomingFD outgoing).det ≠ 0 :=
    BalancedGlobal.det_ne_zero_of_mul_det_neg hSign
  refine ⟨outgoing,
    W2PArbitraryExit.outgoingPresentation input shape hConnected hGenus incoming outgoing
      incomingFD hOutgoing,
    rfl, hSign, δ, hδ, ?_⟩
  intro t ht htδ
  obtain ⟨hPositive, hMetric, ⟨pencil⟩⟩ := hStep t ht htδ
  exact ⟨hPositive, hMetric, pencil.realization, pencil.scale, pencil.scale_pos,
    pencil.targetLength_eq, pencil.bnExists⟩

end Member


/-! ## §3  From the classifier's tag

`IncomingSourceCases.Classification` is the ten-way router; its `w2P` leaf is
`IncomingSourceCases.W2.Classification.p`, whose fields are a wall block, a
`w2-r2-nd3` source profile, Cardinality P (`deleted_target`), the two index
equations, and the `background` clause.  Only `deleted_target` and `background`
are used below: the two index equations are `W2PSourceCandidates.Shape`'s own
consequences (`Shape.cardinality`). -/

section Classified

open DraismaVargas.Infrastructure GraphContraction GluingContraction
open ContractionRamification W4Assembly W4StableSource StableLocalProperties
open W2R1Target SecondEquation FullDimensionalSource WallDegeneration TargetExpansion
open W2PSourceCandidates
open W2PIncomingCensus

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W2SourceInput (contractDatum data hc hab hOne) star)

/-- **The `w2P` tag names the `p` leaf, and the `p` leaf is this chain's
bundle.**  The two index equations of the constructor are dropped: they are
`W2PSourceCandidates.Shape.cardinality`, derived from `deleted_target`. -/
theorem exists_w2P_payload
    (classification : IncomingSourceCases.W2.Classification
      (contractDatum data hc hab hOne) star input)
    (hTag : classification.sourceCase = ClassifiedContinuation.SourceCase.w2P) :
    ∃ wallBlock : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      ∃ sourceProfile : W2R2SourceProfile.SourceProfile
          (contractDatum data hc hab hOne) star wallBlock,
        ∃ _ : Shape sourceProfile,
          ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
            other ≠ wallBlock →
              (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0 := by
  cases classification with
  | m11 _ _ _ _ _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | m1k _ _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | mkk _ _ _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | r1 _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | p wallBlock sourceProfile hDeleted _ _ hBackground =>
      exact ⟨wallBlock, sourceProfile,
        shape_of_w2P data hc hab hOne star sourceProfile hDeleted, hBackground⟩

end Classified


end DraismaVargas.LocalCases.W2PArbitraryIncomingExit
