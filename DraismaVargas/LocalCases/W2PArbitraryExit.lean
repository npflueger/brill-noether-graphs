module

public import DraismaVargas.LocalCases.W2PGraphData
public import DraismaVargas.LocalCases.W2PLimitMatrix
public import DraismaVargas.LocalCases.StableGraphFullDimensional

@[expose] public section

/-!
# Figure 35's certified exit: the outgoing full-dimensional presentation

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-P}`, Figure 35 and
Equation (9).

`W2PGraphData` supplies the three members' stable incidence dictionaries and
`W2PLimitMatrix` the honest limit matrices; `W2PCommonBalance.LimitColumns`
assembles both into `honestPresentedFamily`.  This module closes the chain the
same way `W3Nd3ArbitraryExit` closes the nd3 pair: one identified member's
full-dimensional presentation fixes the common square coordinate order, and
`StableGraphFullDimensional.presentationOfEquivalence` transports it to any
member whose own honest matrix is nonsingular.

## What the transport needs, and where each input comes from

| `presentationOfEquivalence` input | supplied by |
|---|---|
| `certificate` | `between`, from `W2PGraphData`'s three `GraphData.equivalence` |
| `destinationValid` | `BalancedGlobal.Candidate.datum_valid` |
| `destinationTargetConnected`, `destinationTargetGenus` | `TargetExpansion` |
| `targetEdgeCard` | both expanded targets are `TargetExpansion.graph` |
| `sourceGenus` | `W2PSourceCandidates`' three `*_sourceGenus` |
| `destinationLabelling` | `W2PCommonBalance.LimitColumns.labelling` |

Nothing else is asked of the case: `saturated`, `trivalent` and `pathEnds`
are what the stable-incidence equivalence transports, and the only other gate
is the chosen outgoing member's own determinant.

## The gated pair

`familyFullDim` and `familyFullDim_presentation` are exactly
`A04FourTags.FullDimSupply`'s two fields, stated over
`W2PCommonBalance.LimitColumns.honestPresentedFamily` rather than over a
`WallProgress.WallInput`; the wall-input packaging is done in `A04MoreTags`
(`ofW2P`). Both fields are literal, because the family carries the *honest*
presentations `StableLengthMatrixLabelling.presentation ∘ labelling` that
`presentationOfEquivalence` transports -- the same coincidence `A04FourTags`
records for `w3Nd2CoarseFine`, `w3Nd3CoarseFine` and `w4`.
-/

namespace DraismaVargas.LocalCases.W2PArbitraryExit

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open FullDimensionalSource
open ResolutionM11 GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2PSourceCandidates
open W2PSurvival W2PStableLift W2PRowDescent W2PGraphData

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## §1  The three stable incidence dictionaries, indexed -/

/-- **Each actual Figure 35 member is equivalent to the incoming stable
incidence graph**, with exactly the row map used in the matrix calculation.
The member implicits are pinned exactly as in `W2PLimitMatrix.rowEquiv`. -/
noncomputable def equivalence (input : W2SourceInput data star) (shape : Shape profile) :
    ∀ position : Fin 3,
      StableGraphIncidence.Equivalence data
        (W2PCommonBalance.members profile shape position).datum :=
  Fin.cases (n := 2) (motive := fun position ↦ StableGraphIncidence.Equivalence data
      (W2PCommonBalance.members profile shape position).datum)
    (firstEquivalence shape input)
    (Fin.cases (n := 1) (motive := fun i : Fin 2 ↦ StableGraphIncidence.Equivalence data
        (W2PCommonBalance.members profile shape i.succ).datum)
      (secondEquivalence shape input)
      (Fin.cases (n := 0) (motive := fun j : Fin 1 ↦ StableGraphIncidence.Equivalence data
          (W2PCommonBalance.members profile shape j.succ.succ).datum)
        (thirdEquivalence shape input)
        (fun k ↦ k.elim0)))

@[simp] theorem equivalence_zero (input : W2SourceInput data star) (shape : Shape profile) :
    equivalence input shape 0 = firstEquivalence shape input := rfl

@[simp] theorem equivalence_one (input : W2SourceInput data star) (shape : Shape profile) :
    equivalence input shape 1 = secondEquivalence shape input := rfl

@[simp] theorem equivalence_two (input : W2SourceInput data star) (shape : Shape profile) :
    equivalence input shape 2 = thirdEquivalence shape input := rfl

/-- **The dictionary's row map is the limit matrices' row map.**  This is what
makes the transported presentation a presentation of the *honest* matrix. -/
theorem equivalence_row (input : W2SourceInput data star) (shape : Shape profile)
    (position : Fin 3) :
    (equivalence input shape position).row =
      (W2PLimitMatrix.limitColumns input shape).row position := by
  fin_cases position <;> rfl

/-- Compare any two actual members through the incoming stable graph. -/
noncomputable def between (input : W2SourceInput data star) (shape : Shape profile)
    (first second : Fin 3) :
    StableGraphIncidence.Equivalence
      (W2PCommonBalance.members profile shape first).datum
      (W2PCommonBalance.members profile shape second).datum :=
  (equivalence input shape first).symm.trans (equivalence input shape second)

/-! ## §2  What the transport asks of each member -/

theorem member_valid (input : W2SourceInput data star) (shape : Shape profile)
    (position : Fin 3) :
    (W2PCommonBalance.members profile shape position).datum.Valid :=
  (W2PCommonBalance.members profile shape position).datum_valid input.valid

theorem member_targetConnected (shape : Shape profile) (hConnected : graph_connected target)
    (position : Fin 3) :
    graph_connected (TargetExpansion.graph target wall
      (W2PCommonBalance.members profile shape position).right) :=
  TargetExpansion.graph_connected target wall _ hConnected

theorem member_targetGenus (shape : Shape profile) (hGenus : genus target = 0)
    (position : Fin 3) :
    genus (TargetExpansion.graph target wall
      (W2PCommonBalance.members profile shape position).right) = 0 := by
  simpa using hGenus

theorem member_targetEdgeCard (shape : Shape profile) (position : Fin 3) :
    (TargetExpansion.graph target wall
      (W2PCommonBalance.members profile shape position).right).edges.card =
      target.edges.card + 1 := by
  simp

theorem member_sourceGenus (shape : Shape profile) (position : Fin 3) :
    genus (W2PCommonBalance.members profile shape position).datum.sourceGraph =
      genus data.sourceGraph := by
  fin_cases position
  · exact firstMember_sourceGenus shape
  · exact secondMember_sourceGenus shape
  · exact thirdMember_sourceGenus shape

/-! ## §3  The identified-member exit -/

section Exit

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- One identified member's honest labelling, read back on the first member:
the only source of the common square coordinate order. -/
noncomputable def initialLabelling (input : W2SourceInput data star) (shape : Shape profile)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (W2PCommonBalance.members profile shape incoming).datum coordinate) :
    StableLengthMatrixLabelling
      (W2PCommonBalance.members profile shape 0).datum coordinate where
  row := (between input shape 0 incoming).row.trans incomingFD.labelling.row
  targetEdge := incomingFD.labelling.targetEdge.trans
    ((W2PCommonBalance.columnEquiv profile shape incoming).symm.trans
      (W2PCommonBalance.columnEquiv profile shape 0))

/-- The induced honest square labelling of each of the three members. -/
noncomputable def outgoingLabelling (input : W2SourceInput data star) (shape : Shape profile)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (W2PCommonBalance.members profile shape incoming).datum coordinate)
    (outgoing : Fin 3) :
    StableLengthMatrixLabelling
      (W2PCommonBalance.members profile shape outgoing).datum coordinate :=
  (W2PLimitMatrix.limitColumns input shape).labelling
    (initialLabelling input shape incoming incomingFD) outgoing

/-- **Transport a full-dimensional presentation to a chosen Figure 35 member.**
Only that member's own compatible matrix must be nonsingular; the remaining
combinatorial fields are what the stable-incidence dictionary carries. -/
noncomputable def outgoingPresentation (input : W2SourceInput data star)
    (shape : Shape profile) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming outgoing : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (W2PCommonBalance.members profile shape incoming).datum coordinate)
    (outgoingDet : (GluingDatum.LengthMatrixPresentation.matrix
      (outgoingLabelling input shape incoming incomingFD outgoing).presentation).det ≠ 0) :
    FullDimensionalSourcePresentation
      (W2PCommonBalance.members profile shape outgoing).datum coordinate :=
  StableGraphFullDimensional.presentationOfEquivalence incomingFD
    (between input shape incoming outgoing)
    (member_valid input shape outgoing)
    (member_targetConnected shape hConnected outgoing)
    (member_targetGenus shape hGenus outgoing)
    ((member_targetEdgeCard shape outgoing).trans (member_targetEdgeCard shape incoming).symm)
    ((member_sourceGenus shape outgoing).trans (member_sourceGenus shape incoming).symm)
    (outgoingLabelling input shape incoming incomingFD outgoing)
    outgoingDet

@[simp] theorem outgoingPresentation_labelling (input : W2SourceInput data star)
    (shape : Shape profile) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming outgoing : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (W2PCommonBalance.members profile shape incoming).datum coordinate)
    (outgoingDet : (GluingDatum.LengthMatrixPresentation.matrix
      (outgoingLabelling input shape incoming incomingFD outgoing).presentation).det ≠ 0) :
    (outgoingPresentation input shape hConnected hGenus incoming outgoing incomingFD
        outgoingDet).labelling =
      outgoingLabelling input shape incoming incomingFD outgoing := rfl

/-! ## §4  The full-dimensional supply, over the honest Figure 35 family -/

/-- The honest presented family of Figure 35's three members, in the square
coordinates one identified member induces. -/
noncomputable def family (input : W2SourceInput data star) (shape : Shape profile)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (W2PCommonBalance.members profile shape incoming).datum coordinate) :
    BalancedGlobal.PresentedFamily (coordinate := coordinate) 3 data wall :=
  (W2PLimitMatrix.limitColumns input shape).honestPresentedFamily input
    (initialLabelling input shape incoming incomingFD)

@[simp] theorem family_candidate (input : W2SourceInput data star) (shape : Shape profile)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (W2PCommonBalance.members profile shape incoming).datum coordinate)
    (outgoing : Fin 3) :
    (family input shape incoming incomingFD).candidate outgoing =
      W2PCommonBalance.members profile shape outgoing := rfl

@[simp] theorem family_presentation (input : W2SourceInput data star) (shape : Shape profile)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (W2PCommonBalance.members profile shape incoming).datum coordinate)
    (outgoing : Fin 3) :
    (family input shape incoming incomingFD).presentation outgoing =
      (outgoingLabelling input shape incoming incomingFD outgoing).presentation := rfl

/-- **The first supply field for `{w2-r2-nd3-P}`**: an outgoing full-dimensional
presentation at every nonsingular member of Figure 35's honest family. -/
noncomputable def familyFullDim (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0) (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (W2PCommonBalance.members profile shape incoming).datum coordinate) :
    ∀ outgoing : Fin 3,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((family input shape incoming incomingFD).presentation outgoing)).det ≠ 0 →
      FullDimensionalSourcePresentation
        ((family input shape incoming incomingFD).candidate outgoing).datum coordinate :=
  fun outgoing hdet ↦ outgoingPresentation input shape hConnected hGenus incoming outgoing
    incomingFD hdet

/-- **The second supply field for `{w2-r2-nd3-P}`**: it is a presentation *of that
member*, because the family carries the honest presentations the transport
installs. -/
theorem familyFullDim_presentation (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0) (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (W2PCommonBalance.members profile shape incoming).datum coordinate) :
    ∀ (outgoing : Fin 3)
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        ((family input shape incoming incomingFD).presentation outgoing)).det ≠ 0),
      (familyFullDim input shape hConnected hGenus incoming incomingFD outgoing
          hdet).labelling.presentation =
        (family input shape incoming incomingFD).presentation outgoing :=
  fun _ _ ↦ rfl

/-! ## §5  Transport to the chosen member and back is the identity -/

/-- **Transport to the common first member and back cancels both the actual
row equivalence and the target-occurrence equivalence**, so the identified
incoming member's honest square matrix is its own, and is nonsingular. -/
theorem outgoingLabelling_self (input : W2SourceInput data star) (shape : Shape profile)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (W2PCommonBalance.members profile shape incoming).datum coordinate) :
    outgoingLabelling input shape incoming incomingFD incoming = incomingFD.labelling := by
  cases incomingFD with
  | mk valid targetConnected targetGenus saturated labelling det_ne_zero trivalent pathEnds =>
    cases labelling with
    | mk targetEdge row =>
      simp only [outgoingLabelling, initialLabelling, W2PCommonBalance.LimitColumns.labelling,
        W2PCommonBalance.LimitColumns.sourceCoordinates,
        W2PCommonBalance.LimitColumns.targetCoordinates]
      congr 1
      · ext column
        simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
      · ext path
        have hBetween : (between input shape 0 incoming).row =
            ((W2PLimitMatrix.limitColumns input shape).row 0).symm.trans
              ((W2PLimitMatrix.limitColumns input shape).row incoming) := by
          change (equivalence input shape 0).row.symm.trans
            (equivalence input shape incoming).row = _
          rw [equivalence_row input shape 0, equivalence_row input shape incoming]
        rw [hBetween]
        simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- The identified incoming member's own honest square matrix is nonsingular. -/
theorem incomingDet_ne_zero (input : W2SourceInput data star) (shape : Shape profile)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (W2PCommonBalance.members profile shape incoming).datum coordinate) :
    ((W2PLimitMatrix.limitColumns input shape).squareMatrix
      (initialLabelling input shape incoming incomingFD) incoming).det ≠ 0 := by
  change (GluingDatum.LengthMatrixPresentation.matrix
    (outgoingLabelling input shape incoming incomingFD incoming).presentation).det ≠ 0
  rw [outgoingLabelling_self input shape incoming incomingFD]
  exact incomingFD.det_ne_zero

end Exit

/-- **Non-vacuity.**  Every actual case-P datum carrying a `Shape` -- the same
bundle `W2PLimitMatrix.nonempty_limitColumns` runs on -- has all three stable
incidence dictionaries, with no further hypothesis. -/
theorem nonempty_equivalence (input : W2SourceInput data star) (shape : Shape profile)
    (position : Fin 3) :
    Nonempty (StableGraphIncidence.Equivalence data
      (W2PCommonBalance.members profile shape position).datum) :=
  ⟨equivalence input shape position⟩

end DraismaVargas.LocalCases.W2PArbitraryExit
