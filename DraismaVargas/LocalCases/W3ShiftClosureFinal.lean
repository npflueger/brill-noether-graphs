module

public import DraismaVargas.LocalCases.W3ShiftClosureUnconditional
public import DraismaVargas.LocalCases.W3ShiftStableIncidence
public import DraismaVargas.LocalCases.W3ShiftIncomingTransport

@[expose] public section

/-!
# The `w3Shift` case off the classifier's payload

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w3-r1-nd3-t2-(a>k₄)}`, Figure 29 and
Equation (3).

Everything the certified exit of this case needs -- Equation (3), the incoming
member, and the branch swaps of Position II.a -- is assembled here from the
payload of `W3IncomingClassification.Classification.shift` alone.  `CertifiedExit`
names the exit's conclusion; the exit itself, with graph and row tracking, is
`W3ShiftGraphTracking.exists_tracked_exit_of_shrinkPosition` (Position II.b),
`W3ShiftTrackedFinal.exists_tracked_exit_of_growPosition` (Position II.a) and
`W3ShiftTrackedFinal.trackedExit_of_classification` (both, from the classifier).

## The three inputs

* `W3ShiftClosureUnconditional.exists_shiftProfile_selectedCensus`: from the
  classifier's `Nd3Profile`, the two arithmetic fields, `hForest` and
  `hCompat`, an orientation whose moving direction is the incoming cover's own
  isolated one, `W3ShiftClosure.RetainedBelow`, and the selected-block census in
  one of Figure 29's two positions.
* `W3ShiftStableIncidence` and
  `W3ShiftGraphTracking.exists_tracked_exit_in_original_coordinates`: the exit
  itself, in the incoming cover's own coordinates, with `hOrder`, `hHonest` and
  `hContribution` all discharged.
* `W3ShiftIncomingTransport`: the Position II.a branch swap performed one level
  up, on the incoming datum before the contraction.

## The transferred sheet is data

`W3ShiftSourceCandidates.ShiftProfile` carries Position II.a's transferred
sheet as a field (`extra`), so `ShiftProfile.withExtra` installs the incoming
cover's own sheet `y ∈ A₀ ∖ e_α` and `exists_shiftProfile_census` below states
the Position II.a alternative with the census's classes **literally**
`shift.growPartition`; the equation `shift.extraSheet = y` holds by `rfl`.

## Positions

* **Position II.b** is completely unconditional: the census *produces* the
  `ShrinkData` over the incoming cover's own wall datum, so Equation (3)'s pair
  lives there and the exit applies directly.
* **Position II.a** needs the shrink member on the same direction, and the
  case's arithmetic does not supply Position II.b's sheet
  (`W3ShiftSourceCandidates.shift_arithmetic_does_not_force_shrinkSheet`).  Two
  DV branch swaps do, and they have to be performed on the **incoming** datum:
  `W3ShiftClosure.exists_gaugeCopy_shrinkSheet_endpoint` chooses both
  permutations inside blocks of the trivalent endpoint's own partition, which is
  exactly what `W3ShiftIncomingTransport.EndsCompatible` asks for, and
  `endpoint_inputs` below derives that finer arithmetic from
  `W3ShiftClosure.RetainedBelow` and the census's own second clause.

No FourStar theorem is applied to this ThreeStar case.
-/

namespace DraismaVargas.LocalCases.W3ShiftClosureFinal

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open TargetExpansion
open W3Nd2IncomingTargetPlacement (divalentOccurrence)
open W3ShiftSourceCandidates
open W3ShiftIncomingMatching (SelectedCensus shiftClasses)
open W3ShiftLimitRows (shiftMembers)

/-! ## §1  The `w3Shift` tag names Figure 29's payload -/

section Payload

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}

/-- **The `w3Shift` tag names the `shift` leaf, and the `shift` leaf is an
`Nd3Profile` with three distinct directions and the largest index below `|A₀|`.**
The two-le field is a theorem of those (`Nd3Profile.indices_two_le_of_largest_lt`)
and is not carried. -/
theorem exists_shift_payload
    (classification : W3IncomingClassification.Classification data star input)
    (hTag : classification.sourceCase = ClassifiedContinuation.SourceCase.w3Shift) :
    ∃ profile : Nd3Profile data input.distinguishedBlock,
      profile.first.1.1.1 ≠ profile.second.1.1.1 ∧
        data.sourceEdgeIndex profile.largest.1 <
          (data.vertexPartition wall).blockCard input.distinguishedBlock.1 := by
  cases classification with
  | four _ _ _ _ =>
      simp [W3IncomingClassification.Classification.sourceCase] at hTag
  | shift profile directions largest_lt _ => exact ⟨profile, directions, largest_lt⟩
  | nd3CoarseFine _ _ _ _ =>
      simp [W3IncomingClassification.Classification.sourceCase] at hTag
  | nd2CoarseFine _ =>
      simp [W3IncomingClassification.Classification.sourceCase] at hTag

end Payload

/-! ## §2  The orientation, the census, and the transferred sheet installed -/

section Census

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)

include fullDim hForest hCompat

/-- **Figure 29's orientation and census, with Position II.a's transferred sheet
already installed.**  `W3ShiftClosureUnconditional.exists_shiftProfile_selectedCensus`
returns the Position II.a census against `mergeBlocks e_α movingAnchor y`, which
matched Figure 29's grow member only on the extra equation `extraSheet = y`.
Since the sheet is a field of `ShiftProfile`, `withExtra` installs `y` itself and
the census's three classes are **literally** `shift.growPartition`, so the
dichotomy against `shiftClasses shrink 1` is `rfl`. -/
theorem exists_shiftProfile_census
    (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_lt : (contractDatum data hc hab hOne).sourceEdgeIndex profile.largest.1 <
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
        input.distinguishedBlock.1) :
    ∃ shift : ShiftProfile input,
      shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star ∧
      W3ShiftClosure.RetainedBelow shift ∧
      ((∃ shrink : ShrinkData shift,
          SelectedCensus data hc hab hOne star input (shiftClasses shrink 0).1
            (shiftClasses shrink 0).2.1 (shiftClasses shrink 0).2.2) ∨
        SelectedCensus data hc hab hOne star input shift.growPartition
          ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
          shift.growPartition) := by
  obtain ⟨shift, hMoving, hRetained, hCases⟩ :=
    W3ShiftClosureUnconditional.exists_shiftProfile_selectedCensus data hc hab hOne
      fullDim hForest hCompat star input profile directions largest_lt
  rcases hCases with hShrink | ⟨extra, hSep, hWall, hCensus⟩
  · exact ⟨shift, hMoving, hRetained, Or.inl hShrink⟩
  · exact ⟨shift.withExtra extra hWall hSep, hMoving, hRetained, Or.inr hCensus⟩

end Census

/-! ## §3  The certified exit, and Position II.b unconditionally -/

section Exit

universe u

variable {target : CFGraph.{u}} {degree : ℕ} {a b : target.V}
  {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The certified exit of the `w3Shift` case, as one named proposition.**  An outgoing gluing
datum carrying the incoming cover's stable incidence graph and a genuine
`FullDimensionalSourcePresentation` of strictly opposite determinant sign
against the incoming cover's own length matrix, reached along a segment that
stays in the positive cone, matches the incoming metric in the *original*
coordinates, and carries a cleared rank-one pencil at an explicit integral scale
on the outgoing datum's actual source subdivision at every point of it.

This is the conclusion of a certified exit with the outgoing member
existentially quantified -- over its own expanded target, as every Figure 29
member is -- which is what lets the case's two positions (one
over the incoming cover's own wall datum, one over a branch-swapped copy of it)
be stated as a single exit.  In both positions the witness is the *other* member
of Equation (3)'s `(k_α − 1, k_α + 1)` pair on the incoming cover's own moving
direction. -/
def CertifiedExit {data : GluingDatum target degree}
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (z incomingVelocity : coordinate → ℚ) : Prop :=
  ∃ (outgoingTarget : CFGraph.{u}) (outgoingDatum : GluingDatum outgoingTarget degree),
    outgoingDatum.Valid ∧
    Nonempty (StableGraphIncidence.Equivalence data outgoingDatum) ∧
    ∃ outgoingFD : FullDimensionalSourcePresentation outgoingDatum coordinate,
      (GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation).det *
          (GluingDatum.LengthMatrixPresentation.matrix
            outgoingFD.labelling.presentation).det < 0 ∧
      ∃ velocity : coordinate → ℚ, ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • velocity) i) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            outgoingFD.labelling.presentation).mulVec (z + t • velocity) =
          (GluingDatum.LengthMatrixPresentation.matrix
              fullDim.labelling.presentation).mulVec z +
            t • (GluingDatum.LengthMatrixPresentation.matrix
              fullDim.labelling.presentation).mulVec incomingVelocity ∧
        ∃ realization : outgoingDatum.IntegralRealization, ∃ scale : ℕ, 0 < scale ∧
          (∀ column,
            (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
              (scale : ℚ) * (z + t • velocity) column) ∧
          Utilities.BNExists realization.sourceSpec.graph 1 degree

variable (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (shift : ShiftProfile input)
  (hMoving : shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star)
  (shrink : ShrinkData shift)

include hForest hMoving

end Exit

/-! ## §4  Position II.a: the two branch swaps, performed on the incoming datum -/

section PositionTwoA

open W3ShiftIncomingTransport
open IncomingW2TargetPlacement (right_eq_true_iff right_eq_false_iff_of_incident
  right_eq_false_of_not_incident)

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-- Merging a prescribed sheet into a class is congruent in the partition and in
the class anchor; the two separation proofs are irrelevant. -/
theorem mergeBlocks_congr {d : ℕ} {P Q : SheetPartition d} (hPQ : P = Q)
    {x x' y : Fin d} (hx : x = x')
    (hP : ¬P.Rel x y) (hQ : ¬Q.Rel x' y) :
    P.mergeBlocks x y hP = Q.mergeBlocks x' y hQ := by
  subst hPQ
  subst hx
  rfl

/-- **The mirror of `W3ShiftIncomingTransport.endsCompatible_of_fixLeft_of_rightFixed`.**
If every wall occurrence lying over the `a` end of the wall edge is outside the
moved branch, then the moved branch never touches `a`, and only `b`'s own
partition is constrained.  This is the case in which Figure 29's divalent
original endpoint is `a`. -/
theorem endsCompatible_of_fixRight_of_leftFixed
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (root : (contract target hab hOne).V) (hRoot : root ≠ ⟨a, hab⟩)
    (hc : (contracted : target.V × target.V) = (a, b))
    (data : GluingDatum target degree) (permutation : Equiv.Perm (Fin degree))
    (hFixRight : ∀ sheet, (data.vertexPartition b).Rel (permutation sheet) sheet)
    (hLeftFixed : ∀ e : (contract target hab hOne).edges,
      e ∈ GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V) →
      IncomingTargetExpansion.right hc hab hOne e = false →
      TargetBranchRegion.edgeMoved (⟨a, hab⟩ : (contract target hab hOne).V) root hRoot
        e = false) :
    EndsCompatible hab hOne root hRoot data permutation := by
  refine endsCompatible_of_fixRight hab hOne root hRoot data permutation hFixRight
    fun f hIncident ↦ ?_
  by_cases hf : f = contracted
  · subst hf
    exact movedEdge_contracted hab hOne root hRoot hc
  · have hMem : foldEdge hc hab hOne ⟨f, hf⟩ ∈
        GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V) :=
      foldEdge_mem_incidentEdges_merge hc hab hOne hf
        (Finset.mem_union_left _ ((mem_incidentEdges_iff a f).mpr hIncident))
    rw [movedEdge_foldEdge hab hOne root hRoot hc ⟨f, hf⟩]
    refine hLeftFixed _ hMem ?_
    rw [right_eq_false_iff_of_incident hc hab hOne _ hMem, unfoldEdge_foldEdge]
    exact (mem_incidentEdges_iff a f).mpr hIncident

/-- Figure 29's **trivalent** original endpoint: the end of the wall occurrence
that is *not* the divalent one.  The two retained directions `t_β`, `t_γ` are
restored there, and it is its partition -- strictly finer than the merged `A₀` --
that an incoming-level relabelling has to preserve. -/
noncomputable def trivalentVertex (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (divalent : (contract target hab hOne).edges) : target.V :=
  if IncomingTargetExpansion.right hc hab hOne divalent then a else b

/-- **`EndsCompatible` at the trivalent endpoint.**  A permutation preserving the
blocks of the trivalent original endpoint's own partition is compatible with the
branch through any wall occurrence other than the divalent one: the only wall
occurrence over the *divalent* end is the divalent occurrence itself, and
`TargetSeparation.edgeMoved_eq_false` puts it outside that branch.

Nothing here mentions a cover, a profile or a presentation, so it applies
verbatim to a datum that has already been swapped once. -/
theorem endsCompatible_of_endpointFix
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (data : GluingDatum target degree)
    (divalent direction : (contract target hab hOne).edges)
    (hDivalentMem : divalent ∈
      GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V))
    (hDirMem : direction ∈
      GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V))
    (hDirNe : divalent ≠ direction)
    (hOnly : ∀ e ∈ GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V),
      IncomingTargetExpansion.right hc hab hOne e =
        IncomingTargetExpansion.right hc hab hOne divalent → e = divalent)
    (hConnected : graph_connected (contract target hab hOne))
    (hGenus : genus (contract target hab hOne) = 0)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet,
      (data.vertexPartition (trivalentVertex hc hab hOne divalent)).Rel
        (permutation sheet) sheet) :
    EndsCompatible hab hOne
      (TargetSeparation.farEndpoint (⟨a, hab⟩ : (contract target hab hOne).V) direction)
      (TargetSeparation.farEndpoint_ne
        (W3ShiftClosure.mem_incidentEdges_ends hDirMem)) data permutation := by
  have hFixed : TargetBranchRegion.edgeMoved
      (⟨a, hab⟩ : (contract target hab hOne).V)
      (TargetSeparation.farEndpoint (⟨a, hab⟩ : (contract target hab hOne).V) direction)
      (TargetSeparation.farEndpoint_ne (W3ShiftClosure.mem_incidentEdges_ends hDirMem))
      divalent = false :=
    TargetSeparation.edgeMoved_eq_false hConnected hGenus
      (W3ShiftClosure.mem_incidentEdges_ends hDirMem)
      (W3ShiftClosure.mem_incidentEdges_ends hDivalentMem) (Ne.symm hDirNe)
  unfold trivalentVertex at hFix
  cases hSide : IncomingTargetExpansion.right hc hab hOne divalent with
  | false =>
      rw [hSide] at hFix
      simp only [Bool.false_eq_true, ite_false] at hFix
      refine endsCompatible_of_fixRight_of_leftFixed hab hOne _ _ hc data permutation
        hFix fun e hMem hRight ↦ ?_
      rw [hOnly e hMem (hRight.trans hSide.symm)]
      exact hFixed
  | true =>
      rw [hSide] at hFix
      simp only [ite_true] at hFix
      refine endsCompatible_of_fixLeft_of_rightFixed hab hOne _ _ hc data permutation
        hFix fun e hRight ↦ ?_
      have hMem : e ∈
          GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V) := by
        by_contra hNot
        rw [right_eq_false_of_not_incident hc hab hOne e hNot] at hRight
        exact absurd hRight (by simp)
      rw [hOnly e hMem (hRight.trans hSide.symm)]
      exact hFixed

/-! ### The finer arithmetic, read off the Position II.a census -/

section Endpoint

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (shift : ShiftProfile input)

include fullDim

/-- **The trivalent endpoint carries the whole of `A₀`.**  Figure 29's Position
II.a census puts the merged wall block at the trivalent original endpoint
(`selectedRight = A₀`), so the endpoint partition -- in general strictly finer
than `A₀` -- agrees with it block for block there.  This is exactly what turns
`W3ShiftClosure.RetainedBelow` into the finer arithmetic
`W3ShiftClosure.exists_gaugeCopy_shrinkSheet_endpoint` consumes. -/
theorem trivalent_block_eq (selectedLeft selectedNew : SheetPartition degree)
    (hCensus : SelectedCensus data hc hab hOne star input selectedLeft
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) selectedNew)
    (sheet : Fin degree)
    (hSheet : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
      shift.movingAnchor sheet) :
    (data.vertexPartition (trivalentVertex hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star))).block sheet =
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block sheet := by
  have hRel : (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet :=
    (W3ShiftIncomingMatching.merged_rel_iff_movingAnchor data hc hab hOne star input
      shift sheet).mpr hSheet
  have hSpec := (W3Nd2IncomingTargetPlacement.divalentOccurrence_spec data hc hab hOne
    fullDim star).2
  unfold trivalentVertex
  rcases hSpec with ⟨hCard, hSide⟩ | ⟨hCard, hSide⟩
  · rw [hSide]
    simpa using (hCensus.divalentLeft hCard).2.1 sheet hRel
  · rw [hSide]
    simpa using (hCensus.divalentRight hCard).2.1 sheet hRel

/-- The trivalent endpoint's partition refines the merged wall partition. -/
theorem trivalent_refines :
    (data.vertexPartition (trivalentVertex hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star))).Refines
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) := by
  rw [contractDatum_vertexPartition_merge]
  unfold trivalentVertex
  cases IncomingTargetExpansion.right hc hab hOne
      (divalentOccurrence data hc hab hOne fullDim star) with
  | false =>
      simpa using vertexPartition_refines_mergedPartition_right data a b
  | true =>
      simpa using vertexPartition_refines_mergedPartition data a b

/-- A retained direction's own class refines the trivalent endpoint's partition:
the retained directions are restored at that endpoint
(`W3ShiftSelectedCensus.first_side_ne`). -/
theorem retained_refines_trivalent (retained : (contract target hab hOne).edges)
    (hMem : retained ∈
      GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V))
    (hSideNe : IncomingTargetExpansion.right hc hab hOne retained ≠
      IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star)) :
    ((contractDatum data hc hab hOne).edgePartition retained).Refines
      (data.vertexPartition (trivalentVertex hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star))) := by
  rw [contractDatum_edgePartition]
  unfold trivalentVertex
  cases hSide : IncomingTargetExpansion.right hc hab hOne
      (divalentOccurrence data hc hab hOne fullDim star) with
  | false =>
      rw [hSide] at hSideNe
      have hTrue : IncomingTargetExpansion.right hc hab hOne retained = true := by
        cases hR : IncomingTargetExpansion.right hc hab hOne retained
        · exact absurd hR hSideNe
        · rfl
      simp only [Bool.false_eq_true, ite_false]
      exact refines_of_mem_incidentEdges data
        ((right_eq_true_iff hc hab hOne retained).mp hTrue)
  | true =>
      rw [hSide] at hSideNe
      have hFalse : IncomingTargetExpansion.right hc hab hOne retained = false := by
        cases hR : IncomingTargetExpansion.right hc hab hOne retained
        · rfl
        · exact absurd hR hSideNe
      simp only [ite_true]
      exact refines_of_mem_incidentEdges data
        ((right_eq_false_iff_of_incident hc hab hOne retained hMem).mp hFalse)

end Endpoint

/-! ### Transporting the census, the block and the two swaps -/

section Transfer

variable (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)

/-- **The selected-block census sees only four partitions and the distinguished
block.**  It therefore transfers along any change of the incoming cover fixing
the two endpoint partitions and the contracted occurrence's partition -- which a
branch swap rooted away from the wall does, at either level. -/
theorem selectedCensus_transfer (first second : GluingDatum target degree)
    (hA : second.vertexPartition a = first.vertexPartition a)
    (hB : second.vertexPartition b = first.vertexPartition b)
    (hE : second.edgePartition contracted = first.edgePartition contracted)
    (inputOld : W3SourceInput (contractDatum first hc hab hOne) star)
    (inputNew : W3SourceInput (contractDatum second hc hab hOne) star)
    (hBlock : inputNew.distinguishedBlock.1 = inputOld.distinguishedBlock.1)
    (selectedLeft selectedRight selectedNew : SheetPartition degree)
    (hCensus : SelectedCensus first hc hab hOne star inputOld selectedLeft
      selectedRight selectedNew) :
    SelectedCensus second hc hab hOne star inputNew selectedLeft selectedRight
      selectedNew := by
  have hMerged : mergedPartition second a b = mergedPartition first a b := by
    show SheetPartition.join (second.vertexPartition a) (second.vertexPartition b) = _
    rw [hA, hB]
    rfl
  constructor
  · intro hDivalent
    obtain ⟨hL, hR, hN⟩ := hCensus.divalentLeft hDivalent
    refine ⟨fun sheet hRel ↦ ?_, fun sheet hRel ↦ ?_, fun sheet hRel ↦ ?_⟩ <;>
      rw [hMerged, hBlock] at hRel
    · rw [hA]; exact hL sheet hRel
    · rw [hB]; exact hR sheet hRel
    · rw [hE]; exact hN sheet hRel
  · intro hDivalent
    obtain ⟨hL, hR, hN⟩ := hCensus.divalentRight hDivalent
    refine ⟨fun sheet hRel ↦ ?_, fun sheet hRel ↦ ?_, fun sheet hRel ↦ ?_⟩ <;>
      rw [hMerged, hBlock] at hRel
    · rw [hB]; exact hL sheet hRel
    · rw [hA]; exact hR sheet hRel
    · rw [hE]; exact hN sheet hRel

end Transfer

/-- A relation between two sheets transports along an equality of partitions,
with no dependent rewriting. -/
theorem rel_of_eq_partition {d : ℕ} {P Q : SheetPartition d} (hPQ : P = Q)
    {x y : Fin d} (h : P.Rel x y) : Q.Rel x y := by
  subst hPQ
  exact h

/-- Two wall blocks of the same partition that share a sheet are the same
block: their values are canonical representatives. -/
theorem block_val_eq {d : ℕ} {P Q : SheetPartition d} (hPQ : P = Q)
    (x : P.Blocks) (y : Q.Blocks) (hRel : Q.Rel x.1 y.1) : x.1 = y.1 := by
  subst hPQ
  have hStep : P.repr x.1 = P.repr y.1 := hRel
  rw [x.2, y.2] at hStep
  exact hStep

/-! ### The endpoint-level inputs of `exists_gaugeCopy_shrinkSheet_endpoint` -/

section Inputs

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (shift : ShiftProfile input)
  (hMoving : shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star)

include fullDim hMoving

/-- **Everything `W3ShiftClosure.exists_gaugeCopy_shrinkSheet_endpoint` asks for
at the trivalent endpoint, from the Position II.a census and `RetainedBelow`.**
The two retained classes refine the endpoint partition because both retained
directions are restored there; the moving anchor is related to both retained
anchors and the endpoint's block cardinality at it is `|A₀|`, because the census
puts the whole merged wall block at that endpoint. -/
theorem endpoint_inputs (hRetained : W3ShiftClosure.RetainedBelow shift)
    (hCensus : SelectedCensus data hc hab hOne star input shift.growPartition
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) shift.growPartition) :
    ((contractDatum data hc hab hOne).edgePartition shift.firstTarget).Refines
        (data.vertexPartition (trivalentVertex hc hab hOne
          (divalentOccurrence data hc hab hOne fullDim star))) ∧
      ((contractDatum data hc hab hOne).edgePartition shift.secondTarget).Refines
        (data.vertexPartition (trivalentVertex hc hab hOne
          (divalentOccurrence data hc hab hOne fullDim star))) ∧
      (data.vertexPartition (trivalentVertex hc hab hOne
          (divalentOccurrence data hc hab hOne fullDim star))).Rel
        shift.movingAnchor shift.firstAnchor ∧
      (data.vertexPartition (trivalentVertex hc hab hOne
          (divalentOccurrence data hc hab hOne fullDim star))).Rel
        shift.movingAnchor shift.secondAnchor ∧
      (contractDatum data hc hab hOne).sourceEdgeIndex shift.firstRest.1 <
        (data.vertexPartition (trivalentVertex hc hab hOne
          (divalentOccurrence data hc hab hOne fullDim star))).blockCard
            shift.movingAnchor ∧
      (contractDatum data hc hab hOne).sourceEdgeIndex shift.secondRest.1 <
        (data.vertexPartition (trivalentVertex hc hab hOne
          (divalentOccurrence data hc hab hOne fullDim star))).blockCard
            shift.movingAnchor := by
  have hBlockEq := trivalent_block_eq data hc hab hOne fullDim star input shift
    shift.growPartition shift.growPartition hCensus
  have hCard : (data.vertexPartition (trivalentVertex hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star))).blockCard
          shift.movingAnchor =
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
        shift.movingAnchor :=
    congrArg Finset.card (hBlockEq shift.movingAnchor rfl)
  have hRel : ∀ other : Fin degree,
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
        shift.movingAnchor other →
      (data.vertexPartition (trivalentVertex hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star))).Rel
          shift.movingAnchor other := by
    intro other hOther
    have hMem := (SheetPartition.mem_block_iff _ shift.movingAnchor other).mpr hOther
    rw [← hBlockEq shift.movingAnchor rfl] at hMem
    exact (SheetPartition.mem_block_iff _ _ _).mp hMem
  refine ⟨retained_refines_trivalent data hc hab hOne fullDim star shift.firstTarget
      shift.firstTarget_mem
      (W3ShiftSelectedCensus.first_side_ne data hc hab hOne fullDim star input shift
        hMoving),
    retained_refines_trivalent data hc hab hOne fullDim star shift.secondTarget
      shift.secondTarget_mem
      (W3ShiftSelectedCensus.second_side_ne data hc hab hOne fullDim star input shift
        hMoving),
    hRel _ (shift.movingAnchor_wall_rel.symm.trans shift.firstAnchor_wall_rel),
    hRel _ (shift.movingAnchor_wall_rel.symm.trans shift.secondAnchor_wall_rel),
    ?_, ?_⟩
  · rw [hCard]; exact hRetained.1
  · rw [hCard]; exact hRetained.2


/-- **The divalent occurrence is the only wall occurrence over the divalent
original endpoint.**  The star is exactly the three surviving directions
(`ShiftProfile.incidentEdges_eq`), and both retained directions are restored at
the *other* endpoint (`W3ShiftSelectedCensus.first_side_ne`). -/
theorem only_divalent :
    ∀ e ∈ GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V),
      IncomingTargetExpansion.right hc hab hOne e =
        IncomingTargetExpansion.right hc hab hOne
          (divalentOccurrence data hc hab hOne fullDim star) →
      e = divalentOccurrence data hc hab hOne fullDim star := by
  intro e hMem hSide
  rw [shift.incidentEdges_eq] at hMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
  rcases hMem with rfl | rfl | rfl
  · exact hMoving
  · exact absurd hSide (W3ShiftSelectedCensus.first_side_ne data hc hab hOne fullDim star
      input shift hMoving)
  · exact absurd hSide (W3ShiftSelectedCensus.second_side_ne data hc hab hOne fullDim
      star input shift hMoving)

end Inputs

/-! ### One clearing swap, performed on the incoming datum -/

section Swap

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)

/-- **One of Figure 29's two clearing swaps, performed one level up.**  The
permutation `W3ShiftClosure.exists_branchSwapPerm_clearing_endpoint` chooses
inside a block of the trivalent endpoint's own partition, which is exactly
`W3ShiftIncomingTransport.EndsCompatible`, so the same swap can be performed on
the **incoming** datum before the contraction.  Everything the rest of the case reads
off the incoming cover survives: both endpoint partitions, the contracted
occurrence's partition, the contraction receipt, the stable incidence graph, the
length matrix, the column labelling and the divalent wall occurrence -- and the
contracted copy is literally `W3ShiftClosure.clearData`, i.e. the wall-level
gauge copy the pair is built over. -/
theorem exists_incoming_swap
    (divalent direction : (contract target hab hOne).edges)
    (hDivalent : divalentOccurrence data hc hab hOne fullDim star = divalent)
    (hDivalentMem : divalent ∈
      GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V))
    (hDirMem : direction ∈
      GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V))
    (hDirNe : divalent ≠ direction)
    (hOnly : ∀ e ∈ GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V),
      IncomingTargetExpansion.right hc hab hOne e =
        IncomingTargetExpansion.right hc hab hOne divalent → e = divalent)
    (hConnected : graph_connected (contract target hab hOne))
    (hGenus : genus (contract target hab hOne) = 0)
    (endpoint : SheetPartition degree)
    (hEndVertex : data.vertexPartition (trivalentVertex hc hab hOne divalent) = endpoint)
    (hEndRefines : endpoint.Refines
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩))
    (permutation : Equiv.Perm (Fin degree))
    (hFixEnd : ∀ sheet, endpoint.Rel (permutation sheet) sheet) :
    ∃ swapped : GluingDatum target degree,
      swapped.vertexPartition a = data.vertexPartition a ∧
      swapped.vertexPartition b = data.vertexPartition b ∧
      swapped.edgePartition contracted = data.edgePartition contracted ∧
      contractDatum swapped hc hab hOne =
        W3ShiftClosure.clearData (contractDatum data hc hab hOne) direction hDirMem
          endpoint hEndRefines permutation hFixEnd ∧
      (ContractionForest data a b contracted →
        ContractionForest swapped a b contracted) ∧
      Nonempty (StableGraphIncidence.Equivalence data swapped) ∧
      ∃ swappedFD : FullDimensionalSourcePresentation swapped coordinate,
        GluingDatum.LengthMatrixPresentation.matrix swappedFD.labelling.presentation =
            GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation ∧
          swappedFD.labelling.targetEdge = fullDim.labelling.targetEdge ∧
          divalentOccurrence swapped hc hab hOne swappedFD star = divalent := by
  have hEnds := endsCompatible_of_endpointFix hc hab hOne data divalent direction
    hDivalentMem hDirMem hDirNe hOnly hConnected hGenus permutation
    (by rw [hEndVertex]; exact hFixEnd)
  refine ⟨swappedDatum data hc hab hOne _ _ permutation hEnds,
    swappedDatum_vertexPartition_left data hc hab hOne _ _ permutation hEnds,
    swappedDatum_vertexPartition_right data hc hab hOne _ _ permutation hEnds,
    swappedDatum_edgePartition_contracted data hc hab hOne _ _ permutation hEnds,
    contract_swappedDatum data hc hab hOne _ _ permutation hEnds
      (fun sheet ↦ hEndRefines.rel (hFixEnd sheet)),
    contractionForest_swappedDatum data hc hab hOne _ _ permutation hEnds,
    ⟨swappedIncidence data hc hab hOne _ _ permutation hEnds fullDim⟩,
    swappedFullDim data hc hab hOne _ _ permutation hEnds fullDim,
    swappedFullDim_matrix data hc hab hOne _ _ permutation hEnds fullDim,
    swappedFullDim_targetEdge data hc hab hOne _ _ permutation hEnds fullDim, ?_⟩
  exact (divalentOccurrence_congr hc hab hOne data _ fullDim
    (swappedFullDim data hc hab hOne _ _ permutation hEnds fullDim) star).trans hDivalent

end Swap

end PositionTwoA

end DraismaVargas.LocalCases.W3ShiftClosureFinal
