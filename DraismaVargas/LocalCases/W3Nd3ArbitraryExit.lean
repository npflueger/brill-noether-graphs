module

public import DraismaVargas.LocalCases.W3Nd3IncomingMatching
public import DraismaVargas.LocalCases.W3Nd3CommonBalance
public import DraismaVargas.LocalCases.StableGraphFullDimensional
public import DraismaVargas.LocalCases.FiniteAtlasMarch

@[expose] public section

/-!
# Case {w3-r1-nd3-t3}: the identified-member exit, with a full-dimensional outgoing source

Source: Draisma--Vargas Part I, Case {w3-r1-nd3-t3} (the nd3 case of Case
{w3}), Figure 30 and Equation (4).  Figure 30 gives `M⁽¹⁾` a single new edge
`e'` with `|e'| = k₄` and `M⁽²⁾` two new edges with `|e'| = k₂`, `|e''| = k₃`;
the prose of the case attaches these to `α = 3` and `α = 4` the other way
round, and every module of this chain follows the figure.

`W3Nd3IncomingMatching.exists_member_normalization` proves that an arbitrary
incoming nd3 datum *is* one of the two named Figure 30 members, together with a
normalization receipt; `W3Nd3CommonBalance` proves Equation (4) and, from it,
the positive exit for an *identified* member.  This file equips that exit with
a full-dimensional presentation of the outgoing member.  The restatement in
the **incoming cover's own coordinates**, with graph and row tracking attached,
is `W3Nd3GraphTracking`.

## Original coordinates

In the original-coordinate form, everything in the conclusion is phrased
against `fullDim`, the incoming cover's own honest full-dimensional
presentation:

* the wall coordinate is `fullDim.labelling.targetEdge.symm contracted`, i.e. the
  column of the actual contracted edge of the incoming target, in the incoming
  cover's own coordinate order;
* both the incoming determinant and the affine metric equation use
  `GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation`,
  the incoming cover's own length matrix on its own retained stable rows.

Neither is re-derived.  The receipt's clauses supply them directly:
`W3Nd2IncomingMemberMatching.NormalizedAgainst` records that the transported
member carries an honest presentation whose `targetEdge` is the *original*
labelling composed with the actual occurrence map, and whose length matrix is
equal to the original one **entry by entry**, not merely up to determinant or
sign.  The Option column dictionary of `exists_member_normalization` then
identifies `none` with the literal contracted occurrence
(`M11IncomingCoordinates.incomingColumnEquiv_none`), which is what turns the
member's wall column into the original one.

## What is proved here

The nd2 analogue of this step is `W3Nd2PositiveExit` (the identified-member
exit, which transports a full-dimensional presentation to the selected member).
In nd3 it has no separate module: `W3Nd3CommonBalance.exists_valid_positive_exit_with_pencil`
stops at `BalancedGlobal.PresentedFamily`, returning the selected member's
*validity* and a `BalancedGlobal.Candidate.ClearedPencil`, and takes the
outgoing chart velocity as a hypothesis.  This file therefore assembles:

* `equivalence`, `equivalence_row`, `between` -- the two actual Figure 30
  members are stable-incidence equivalent to the incoming stable graph, by
  `W3Nd3LimitMatrix.coarseStableGraphEquivalence` and
  `fineStableGraphEquivalence`, with exactly the row maps
  `W3Nd3CommonBalance.rowEquiv` uses in the matrix calculation.
* `candidate_targetConnected`, `candidate_targetGenus`,
  `candidate_targetEdgeCard`, `candidate_sourceGenus` -- the four transport
  inputs of `StableGraphFullDimensional.presentationOfEquivalence`.
* `initialLabelling`, `outgoingLabelling`, `outgoingPresentation`,
  `outgoingLabelling_self`, `incomingDet_ne_zero` -- one identified member's
  honest labelling induces the common square coordinate order, and transport
  to that member and back is the identity on it.
* `outgoingVelocity`, `outgoingVelocity_system` -- the canonical chart velocity
  discharging `exists_valid_positive_exit_with_pencil`'s `hSystems`
  hypothesis at any nonsingular member.
* `exists_member_positive_exit_with_pencil` -- the identified-member exit with
  an *outgoing full-dimensional presentation* and the cleared pencil unpacked
  into its realization, scale and `BNExists` clauses.

Only the *selected* outgoing member is ever required nonsingular; that is
derived from Equation (4) -- `W3Nd3CommonBalance.determinant_balance`, through
`W3Nd3CommonBalance.positiveBalance` and
`BalancedGlobal.det_ne_zero_of_mul_det_neg` -- so no nonsingularity is assumed
of the unselected member.  No incoming family membership, no `NoReturn`, no row
bijection and no matrix identity is hypothesised: each is proved upstream and
consumed here.

The cleared pencil is on the **actual source subdivision** of the selected
member's realization.  Nothing here claims a requested `Spec`, a terminal
refinement, or a metric-length dictionary; those belong to the reduction to a
cubic model and to the terminal faces.

No FourStar theorem is applied to this ThreeStar case, and
`GlobalCoarseFine.nd3BalancedFamily` stays unclaimed: as
`W3Nd3CommonBalance` records, that family wants
`TrivalentPattern … geometry.fineLocal` while Figure 30's `M⁽²⁾` uses
`W3Nd3SourceCandidates.selectedResolution`.  Everything below routes through
`BalancedGlobal.PresentedFamily`, which imposes no pattern requirement, and
nothing in this file touches `GlobalCoarseFine`.

## The nd2 divergences, and where each is absorbed

1. **There is no residual sheet** in nd3; the doubled direction cuts `A₀` into
   two blocks that already exhaust it.  That divergence is entirely absorbed by
   `W3Nd3IncomingMatching.block_eq_of_cover_pair_local` upstream: the receipt
   consumed here has the same shape as nd2's, so no step below sees it.
2. **The divalent original endpoint is a branch vertex** in nd3.  This is
   absorbed by `W3Nd3IncomingCensus`, and
   `W3Nd3IncomingMatching.selected_endpoint_joined`'s disjunction is *not* an
   `M⁽¹⁾`/`M⁽²⁾` alternative; the member alternative used here is the
   orientation dichotomy
   `W3Nd3IncomingCensus.divalentOccurrence_eq_shared_or_largest`, already packaged
   inside `exists_member_normalization`.
3. **`old_wall_branch_background` is false** in nd3 and is not used anywhere
   below, directly or through a lemma of this chain.

## Hypotheses, and why they can hold at once

The bundle is exactly the one `W3Nd3IncomingMatching.exists_member_normalization`
consumes, shown jointly satisfiable by
`W3Nd3IncomingCensus.selected_fibre_census_of_shared` and `_of_largest`: an
actual full-dimensional incoming presentation whose contraction of the single
edge between `a` and `b` is a forest with dangling compatibility, a genuine
trivalent star at the contracted wall, a `W3SourceInput` for it, a Figure 30
nd3 profile of its distinguished block, and the doubled direction `hSame`.
Both branches of the orientation dichotomy genuinely occur, so neither the
statement nor its proof is vacuous.  The three exit hypotheses -- the wall
coordinate vanishes, every other coordinate is positive, and the incoming
velocity points inward there -- are the standard wall data and are satisfied by
any interior point approaching the wall.  Nothing is added to the bundle.
-/

namespace DraismaVargas.LocalCases.W3Nd3ArbitraryExit

/-! ## Two coordinate cancellations, at abstract types

The composite labellings below mix `W3Nd3CommonBalance.columnEquiv`, whose
codomain is written with `candidates`, and the member labellings, whose target
type is written with `members`.  The two are the same type but not the same
expression, so the composites are not type-correct at the transparency a
rewrite uses.  Both cancellations are therefore proved once at abstract types,
where nothing has to be unfolded, and applied by unification. -/

section Cancellation

variable {α β γ δ ε : Type*}

/-- Going out through one occurrence dictionary and back through another
cancels: this is the target-edge half of `outgoingLabelling_self`. -/
private theorem trans_cancel_target (e : α ≃ β) (A : γ ≃ β) (B : γ ≃ δ) :
    ((e.trans (A.symm.trans B)).trans B.symm).trans A = e := by
  ext x
  simp

/-- The same cancellation read backwards at the wall column: the common
coordinate order's `none` is the identified member's own wall occurrence. -/
private theorem symm_trans_cancel (e : α ≃ β) (A : γ ≃ β) (B : γ ≃ δ) (x : γ) :
    ((e.trans (A.symm.trans B)).trans B.symm).symm x = e.symm (A x) := by
  simp

/-- Transporting stable rows to the first member and back cancels: this is the
row half of `outgoingLabelling_self`. -/
private theorem trans_cancel_row (R : α ≃ β) (S : α ≃ γ) (T : β ≃ γ)
    (hT : T = R.symm.trans S) (r : γ ≃ ε) :
    S.symm.trans (R.trans (T.trans r)) = r := by
  subst hT
  ext x
  simp

end Cancellation

section Fields

open DraismaVargas.Infrastructure W4StableSource

variable {target : CFGraph} {degree : ℕ} {datum : GluingDatum target degree}
  {coordinate : Type*}

/-- A stable length-matrix labelling is its two equivalences. -/
private theorem labelling_eq_of_fields
    {first second : StableLengthMatrixLabelling datum coordinate}
    (hTarget : first.targetEdge = second.targetEdge) (hRow : first.row = second.row) :
    first = second := by
  cases first
  cases second
  cases hTarget
  cases hRow
  rfl

end Fields


/-! ## The identified-member exit, with a full-dimensional outgoing source -/

section Member

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource ThirdEquation FullDimensionalSource
open W3R1SourceProfile W3Nd3SourceCandidates W3Nd3LimitMatrix

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  (input : W3SourceInput data star)
  (profile : Nd3Profile data input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Each actual Figure 30 member is equivalent to the original stable
incidence graph, with exactly the row map used in the matrix calculation. -/
noncomputable def equivalence (position : Fin 2) :
    StableGraphIncidence.Equivalence data
      (W3Nd3CommonBalance.candidates input profile hSame position).datum :=
  Fin.cases (coarseStableGraphEquivalence input profile hSame)
    (Fin.cases (fineStableGraphEquivalence input profile hSame)
      (fun i ↦ Fin.elim0 i)) position

theorem equivalence_row (position : Fin 2) :
    (equivalence input profile hSame position).row =
      W3Nd3CommonBalance.rowEquiv input profile hSame position := by
  fin_cases position <;> rfl

/-- Compare any two actual members through the old stable graph. -/
noncomputable def between (first second : Fin 2) :
    StableGraphIncidence.Equivalence
      (W3Nd3CommonBalance.candidates input profile hSame first).datum
      (W3Nd3CommonBalance.candidates input profile hSame second).datum :=
  (equivalence input profile hSame first).symm.trans
    (equivalence input profile hSame second)

theorem candidate_targetConnected (hConnected : graph_connected target)
    (position : Fin 2) :
    graph_connected
      (W3Nd3CommonBalance.candidates input profile hSame position).outgoingTarget := by
  change graph_connected (TargetExpansion.graph target wall _)
  exact TargetExpansion.graph_connected target wall _ hConnected

theorem candidate_targetGenus (hGenus : genus target = 0) (position : Fin 2) :
    genus (W3Nd3CommonBalance.candidates input profile hSame position).outgoingTarget = 0 := by
  change genus (TargetExpansion.graph target wall _) = 0
  simpa using hGenus

theorem candidate_targetEdgeCard (position : Fin 2) :
    (W3Nd3CommonBalance.candidates input profile hSame position).outgoingTarget.edges.card =
      target.edges.card + 1 := by
  change (TargetExpansion.graph target wall _).edges.card = _
  simp

theorem candidate_sourceGenus (position : Fin 2) :
    genus (W3Nd3CommonBalance.candidates input profile hSame position).datum.sourceGraph =
      genus data.sourceGraph := by
  fin_cases position
  · exact coarseCandidate_sourceGenus input profile hSame
  · exact fineCandidate_sourceGenus input profile hSame

/-- One identified member's honest labelling, read back on the first member:
this is the only source of the common square coordinate order. -/
noncomputable def initialLabelling (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd3CommonBalance.candidates input profile hSame incoming).datum coordinate) :
    StableLengthMatrixLabelling
      (W3Nd3CommonBalance.candidates input profile hSame 0).datum coordinate where
  row := (between input profile hSame 0 incoming).row.trans incomingFD.labelling.row
  targetEdge := incomingFD.labelling.targetEdge.trans
    ((W3Nd3CommonBalance.columnEquiv input profile hSame incoming).symm.trans
      (W3Nd3CommonBalance.columnEquiv input profile hSame 0))

noncomputable def outgoingLabelling (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd3CommonBalance.candidates input profile hSame incoming).datum coordinate)
    (outgoing : Fin 2) :
    StableLengthMatrixLabelling
      (W3Nd3CommonBalance.candidates input profile hSame outgoing).datum coordinate :=
  W3Nd3CommonBalance.labelling input profile hSame
    (initialLabelling input profile hSame incoming incomingFD) outgoing

/-- Transport a full-dimensional presentation to a chosen actual member.
Only that member's compatible matrix must be nonsingular. -/
noncomputable def outgoingPresentation
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming outgoing : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd3CommonBalance.candidates input profile hSame incoming).datum coordinate)
    (outgoingDet :
      (GluingDatum.LengthMatrixPresentation.matrix
        (outgoingLabelling input profile hSame incoming incomingFD
          outgoing).presentation).det ≠ 0) :
    FullDimensionalSourcePresentation
      (W3Nd3CommonBalance.candidates input profile hSame outgoing).datum coordinate :=
  StableGraphFullDimensional.presentationOfEquivalence incomingFD
    (between input profile hSame incoming outgoing)
    ((W3Nd3CommonBalance.candidates input profile hSame outgoing).valid_of_old input.valid)
    (candidate_targetConnected input profile hSame hConnected outgoing)
    (candidate_targetGenus input profile hSame hGenus outgoing)
    ((candidate_targetEdgeCard input profile hSame outgoing).trans
      (candidate_targetEdgeCard input profile hSame incoming).symm)
    ((candidate_sourceGenus input profile hSame outgoing).trans
      (candidate_sourceGenus input profile hSame incoming).symm)
    (outgoingLabelling input profile hSame incoming incomingFD outgoing)
    outgoingDet

/-- Transport to the common first member and back cancels both actual row
and target-occurrence equivalences. -/
theorem outgoingLabelling_self (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd3CommonBalance.candidates input profile hSame incoming).datum coordinate) :
    outgoingLabelling input profile hSame incoming incomingFD incoming =
      incomingFD.labelling := by
  have hBetween :
      (between input profile hSame 0 incoming).row =
        (W3Nd3CommonBalance.rowEquiv input profile hSame 0).symm.trans
          (W3Nd3CommonBalance.rowEquiv input profile hSame incoming) := by
    change (equivalence input profile hSame 0).row.symm.trans
        (equivalence input profile hSame incoming).row = _
    rw [equivalence_row input profile hSame 0,
      equivalence_row input profile hSame incoming]
    rfl
  exact labelling_eq_of_fields (trans_cancel_target _ _ _)
    (trans_cancel_row _ _ _ hBetween _)

theorem incomingDet_ne_zero (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd3CommonBalance.candidates input profile hSame incoming).datum coordinate) :
    (W3Nd3CommonBalance.squareMatrix input profile hSame
      (initialLabelling input profile hSame incoming incomingFD) incoming).det ≠ 0 := by
  change (GluingDatum.LengthMatrixPresentation.matrix
    (outgoingLabelling input profile hSame incoming incomingFD
      incoming).presentation).det ≠ 0
  rw [outgoingLabelling_self input profile hSame incoming incomingFD]
  exact incomingFD.det_ne_zero

section Exit

variable (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (W3Nd3CommonBalance.candidates input profile hSame incoming).datum coordinate)

/-- The matrices are the actual induced-member presentations. -/
noncomputable def memberMatrix (outgoing : Fin 2) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix
    (outgoingLabelling input profile hSame incoming incomingFD outgoing).presentation

/-- The coordinate naming the regrown wall column. -/
noncomputable def wallColumn : coordinate :=
  W3Nd3CommonBalance.wallColumn input profile hSame
    (initialLabelling input profile hSame incoming incomingFD)

/-- Canonical outgoing chart velocity at a nonsingular selected member. -/
noncomputable def outgoingVelocity (incomingVelocity : coordinate → ℚ)
    (outgoing : Fin 2) : coordinate → ℚ :=
  FiniteAtlasMarch.chartCoordinates
    (memberMatrix input profile hSame incoming incomingFD outgoing)
    ((memberMatrix input profile hSame incoming incomingFD incoming).mulVec
      incomingVelocity)

theorem outgoingVelocity_system (incomingVelocity : coordinate → ℚ)
    (outgoing : Fin 2)
    (hDet : (memberMatrix input profile hSame incoming incomingFD outgoing).det ≠ 0) :
    (memberMatrix input profile hSame incoming incomingFD incoming).mulVec
        incomingVelocity =
      (memberMatrix input profile hSame incoming incomingFD outgoing).mulVec
        (outgoingVelocity input profile hSame incoming incomingFD incomingVelocity
          outgoing) :=
  (FiniteAtlasMarch.mulVec_chartCoordinates _ hDet _).symm

/-- **The identified-member Figure 30 continuation.**  Equation (4) selects a
genuinely nonsingular opposite-sign member, stable incidence equips it with a
full-dimensional presentation, and the one-column cone-wall calculation supplies
the positive rational step together with its cleared rank-one pencil on the
member's literal source subdivision.  Only the chosen incoming member is assumed
nonsingular; its incoming datum remains an identified member of the actual
`Fin 2` family. -/
theorem exists_member_positive_exit_with_pencil
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (wallColumn input profile hSame incoming incomingFD) = 0)
    (hzpos : ∀ i, i ≠ wallColumn input profile hSame incoming incomingFD → 0 < z i)
    (hIncomingDirection :
      incomingVelocity (wallColumn input profile hSame incoming incomingFD) < 0) :
    ∃ outgoing : Fin 2,
      ∃ outgoingFD : FullDimensionalSourcePresentation
          (W3Nd3CommonBalance.candidates input profile hSame outgoing).datum coordinate,
        outgoingFD.labelling =
            outgoingLabelling input profile hSame incoming incomingFD outgoing ∧
        (memberMatrix input profile hSame incoming incomingFD incoming).det *
            (memberMatrix input profile hSame incoming incomingFD outgoing).det < 0 ∧
        ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (z + t • outgoingVelocity input profile hSame incoming incomingFD
            incomingVelocity outgoing) i) ∧
          (memberMatrix input profile hSame incoming incomingFD outgoing).mulVec
              (z + t • outgoingVelocity input profile hSame incoming incomingFD
                incomingVelocity outgoing) =
            (memberMatrix input profile hSame incoming incomingFD incoming).mulVec z +
              t • (memberMatrix input profile hSame incoming incomingFD
                incoming).mulVec incomingVelocity ∧
          ∃ realization :
              (W3Nd3CommonBalance.candidates input profile hSame
                outgoing).datum.IntegralRealization,
            ∃ scale : ℕ, 0 < scale ∧
              (∀ column,
                (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                  (scale : ℚ) *
                    (z + t • outgoingVelocity input profile hSame incoming incomingFD
                      incomingVelocity outgoing) column) ∧
              Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  have hIncoming : (W3Nd3CommonBalance.squareMatrix input profile hSame
      (initialLabelling input profile hSame incoming incomingFD) incoming).det ≠ 0 :=
    incomingDet_ne_zero input profile hSame incoming incomingFD
  obtain ⟨outgoing, _hValid, hSign, δ, hδ, hStep⟩ :=
    W3Nd3CommonBalance.exists_valid_positive_exit_with_pencil input profile hSame
      (initialLabelling input profile hSame incoming incomingFD)
      hConnected hGenus wall incoming hIncoming z incomingVelocity
      (outgoingVelocity input profile hSame incoming incomingFD incomingVelocity)
      hz hzpos
      (fun outgoing hDet ↦ outgoingVelocity_system input profile hSame incoming
        incomingFD incomingVelocity outgoing hDet)
      hIncomingDirection
  have hOutgoing :
      (memberMatrix input profile hSame incoming incomingFD outgoing).det ≠ 0 :=
    BalancedGlobal.det_ne_zero_of_mul_det_neg hSign
  refine ⟨outgoing,
    outgoingPresentation input profile hSame hConnected hGenus incoming outgoing
      incomingFD hOutgoing,
    rfl, hSign, δ, hδ, ?_⟩
  intro t ht htδ
  obtain ⟨hPositive, hMetric, ⟨pencil⟩⟩ := hStep t ht htδ
  exact ⟨hPositive, hMetric, pencil.realization, pencil.scale, pencil.scale_pos,
    pencil.targetLength_eq, pencil.bnExists⟩

end Exit

end Member

end DraismaVargas.LocalCases.W3Nd3ArbitraryExit
