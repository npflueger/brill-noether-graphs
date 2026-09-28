import DraismaVargas.LocalCases.ClosedEndpoint
import DraismaVargas.LocalCases.SemanticAtlasMarch

/-!
# The zero-free terminal face

This file treats the special case of a terminal face in which the terminal
coordinate vector of the rational march has **no vanishing coordinate**.  It
shows that the endpoint interfaces of `ClosedFaceRealization.lean` and
`ClosedEndpoint.lean` compose, and it isolates exactly what the general
(zero-carrying) case has to add.

Everything here is driven by one observation.  A source occurrence of a cleared
face lies in `face.realization.sourceZeroSet` exactly when the target edge under
it has coordinate `0` (`ClearedFace.mem_sourceZeroSet_iff`), so at a strictly
positive terminal point the zero set is empty.  Consequently:

* `SourceContractionTopology` degenerates to `IsForest core ∅` together with
  `¬ IsLoopy core ∅`, i.e. to looplessness of the unit-subdivision source core;
* the nonnegative realization of the face is already a strictly positive
  `IntegralRealization` — the *same* natural numbers, now known to be positive
  (`positiveRealization`), so nothing is contracted and the target is unchanged;
* the canonical contracted source is identified with that realization's source
  subdivision by `DegSpec.laplacianEquivToSpec`, which applies exactly because
  there is no zero slot.  That identification rests on a definitional equality
  checked below by `rfl` (`toSpec_eq_positiveRealization_sourceSpec`).

## The input refinement

`Candidate.ClearedFace.InputRefinement` is taken as a **hypothesis**, not proved
and not admitted.  It says that the canonical contracted source with its pendant
trees deleted, `PrunedContractedSpec.prunedSpec` (in the zero-free leafless case,
the contracted source itself), *is* the requested stable specification `spec`,
scaled by `face.scale` and subdivided at the block boundaries of the cover.  It
cannot be derived from a presentation alone, in this case or in any other,
because `GluingDatum.LengthMatrixPresentation` (`Infrastructure/LengthMatrix.lean`)
records only a bijection `coordinate ≃ target.edges` and, per row, a list of
source edges: it carries **no incidence, disjointness or exhaustiveness
condition** tying those paths to `candidate.datum.sourceGraph`.  Without such a
condition the relabeling `LaplacianEquiv refined.graph (prunedSpec ..).graph`
inside `RefinementPresentation` is not derivable, however positive the
coordinates are.  Supplying it needs further data alongside the presentation
plus the all-slots refinement combinator over `PackedSpec`; both lie outside
the zero-free case, and `OrientedTraversal.RowDictionary.inputRefinement`
supplies them.

The numerical input that combinator consumes is, by contrast, already proved
here: `ClearedFace.sourcePathLength_eq_scale_mul_of_matrixMap`.

## Candidate provenance

The candidate, presentation and face are taken as explicit arguments rather
than extracted from the `Prop`-valued `State.carriesPencil`.  Two reasons.
Extracting data from `carriesPencil` would have to go through `Nonempty` and
`Classical.choice`, which would force the hypotheses to hold for *every* valid
candidate realizing the chart matrix; and the `InputRefinement` hypothesis
above mentions the face, so it cannot even be stated before the candidate is
fixed.  The candidate is the one registered in the chart catalogue.
-/

namespace DraismaVargas.LocalCases.ZeroFreeTerminalFace

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal

/-! ## Contracting nothing -/

section EmptyContraction

variable {n p : ℕ} (core : ExplicitPotential.Core n p)

/-- Contracting the empty slot set merges no vertex class, so it is a forest
contraction.  Stated for an arbitrary core so that the general zero-carrying
case can reuse the shape. -/
theorem isForest_empty : IsForest core (∅ : Finset (Fin p)) := by
  simp [IsForest]

/-- Contracting the empty slot set creates no loop: a loop of the empty
contraction is literally a loop of the core. -/
theorem not_isLoopy_empty
    (hLoopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge) :
    ¬ IsLoopy core (∅ : Finset (Fin p)) := by
  intro hLoopy
  obtain ⟨edge, -, hEdge⟩ := hLoopy
  rw [compFold_empty] at hEdge
  exact hLoopless edge hEdge

end EmptyContraction

/-! ## The two topology receipts at a strictly positive face -/

section Face

variable {target : CFGraph.{0}} {degree : ℕ}
  {data : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree data wall}
  {coordinate : Type*}
  {presentation : candidate.datum.LengthMatrixPresentation coordinate}
  {coordinates : coordinate → ℚ}

/-- At a strictly positive coordinate vector no source occurrence of the
cleared face vanishes. -/
theorem sourceZeroSet_eq_empty_of_pos
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (hPositive : ∀ i, 0 < coordinates i) :
    face.realization.sourceZeroSet = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun slot hslot ↦ ?_
  have hColumn := (Candidate.ClearedFace.mem_sourceZeroSet_iff face slot).mp hslot
  exact (hPositive (presentation.targetEdge.symm
    (face.realization.sourceEdgeAt slot).1.1)).ne' hColumn

/-- With an empty zero set the genus-preservation receipt is the empty
contraction. -/
theorem isForest_of_sourceZeroSet_empty
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (hEmpty : face.realization.sourceZeroSet = ∅) :
    IsForest (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      face.realization.sourceZeroSet := by
  rw [hEmpty]
  exact isForest_empty _

/-- With an empty zero set the looplessness receipt is looplessness of the
unit-subdivision source core. -/
theorem not_isLoopy_of_sourceZeroSet_empty
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (hEmpty : face.realization.sourceZeroSet = ∅) :
    ¬ IsLoopy (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      face.realization.sourceZeroSet := by
  rw [hEmpty]
  exact not_isLoopy_empty _
    (UnitSubdivisionPresentation.spec candidate.datum.sourceGraph).core_loopless

/-- **The source-contraction topology at a zero-free face.**  A strictly positive terminal point has
a genus-preserving, loop-free zero-source contraction, namely the empty one. -/
theorem sourceContractionTopology
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (hPositive : ∀ i, 0 < coordinates i) :
    Candidate.ClearedFace.SourceContractionTopology face where
  forest := isForest_of_sourceZeroSet_empty face
    (sourceZeroSet_eq_empty_of_pos face hPositive)
  notLoopy := not_isLoopy_of_sourceZeroSet_empty face
    (sourceZeroSet_eq_empty_of_pos face hPositive)

/-! ## The cleared face is already a positive integral realization -/

/-- Every target occurrence of a zero-free cleared face has positive cleared
length. -/
theorem targetLength_pos_of_pos
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (hPositive : ∀ i, 0 < coordinates i)
    (edge : (TargetExpansion.graph target wall candidate.right).edges) :
    0 < face.realization.targetLength edge := by
  refine Nat.pos_of_ne_zero fun hZero ↦ ?_
  have hColumn : coordinates (presentation.targetEdge.symm edge) = 0 := by
    refine (Candidate.ClearedFace.targetLength_eq_zero_iff face
      (presentation.targetEdge.symm edge)).mp ?_
    simpa using hZero
  exact (hPositive (presentation.targetEdge.symm edge)).ne' hColumn

/-- Every source occurrence of a zero-free cleared face has positive cleared
length. -/
theorem sourceLength_pos_of_pos
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (hPositive : ∀ i, 0 < coordinates i)
    (edge : candidate.datum.SourceEdge) :
    0 < face.realization.sourceLength edge :=
  Nat.pos_of_ne_zero fun hZero ↦
    (hPositive (presentation.targetEdge.symm edge.1.1)).ne'
      ((Candidate.ClearedFace.sourceLength_eq_zero_iff face edge).mp hZero)

/-- The strictly positive integral realization carried by a zero-free cleared
face.  The lengths are *literally* those of `face.realization`; only the
positivity fields are new.  Building the record by hand rather than re-clearing
the rationals through `IntegralRealization.ofPositiveRational` is what keeps
`sourceSpec` definitionally equal to the canonical contracted source below. -/
noncomputable def positiveRealization
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (hPositive : ∀ i, 0 < coordinates i) :
    candidate.datum.IntegralRealization where
  targetLength := face.realization.targetLength
  targetLength_pos := targetLength_pos_of_pos face hPositive
  sourceLength := face.realization.sourceLength
  sourceLength_pos := sourceLength_pos_of_pos face hPositive
  dilation_length := face.realization.dilation_length

/-- The canonical degenerate quotient source of a zero-free face has strictly
positive slot lengths. -/
theorem degSpec_length_pos
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (hPositive : ∀ i, 0 < coordinates i)
    (slot : Fin candidate.datum.sourceGraph.edges.card) :
    0 < (sourceContractionTopology face hPositive).degSpec.length slot :=
  sourceLength_pos_of_pos face hPositive _

/-- **The definitional check.**  `DegSpec.toSpec` at the zero-free face and the
source subdivision of `positiveRealization` are the *same* term: both are the
unit-subdivision core of `candidate.datum.sourceGraph` carrying the slot length
`face.realization.sourceLength ∘ sourceEdgeAt`, and their remaining fields are
proofs.  This `rfl` is what makes `sourceEquiv` below typecheck. -/
theorem toSpec_eq_positiveRealization_sourceSpec
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (hPositive : ∀ i, 0 < coordinates i) :
    (sourceContractionTopology face hPositive).degSpec.toSpec
        (degSpec_length_pos face hPositive) =
      (positiveRealization face hPositive).sourceSpec := rfl

/-- `positiveIntegralNat` and `nonnegativeIntegralNat` are the same term applied
to the same integrality proof, so the canonically re-cleared positive
realization agrees with the face's nonnegative one, on the nose. -/
example
    (hNonnegative : ∀ i, 0 ≤ coordinates i)
    (hTargetPositive : ∀ edge : (TargetExpansion.graph target wall
        candidate.right).edges,
      0 < coordinates (presentation.targetEdge.symm edge))
    (hPositive : ∀ i, 0 < coordinates i) :
    positiveRealization
        (Candidate.clearedFace candidate presentation coordinates hNonnegative)
        hPositive =
      GluingDatum.IntegralRealization.ofPositiveRational candidate.datum
        (fun edge ↦ coordinates (presentation.targetEdge.symm edge))
        hTargetPositive := rfl

/-- The canonical positive contraction of a zero-free face is the source
subdivision of its own positive realization.  The second factor is available
exactly because the degenerate spec has no zero slot. -/
noncomputable def sourceEquiv
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (hPositive : ∀ i, 0 < coordinates i) :
    LaplacianEquiv (sourceContractionTopology face hPositive).contractedSpec.graph
      (positiveRealization face hPositive).sourceSpec.graph :=
  (sourceContractionTopology face hPositive).laplacianEquiv.trans
    ((sourceContractionTopology face hPositive).degSpec.laplacianEquivToSpec
      (degSpec_length_pos face hPositive)).symm

/-- **The contracted gluing at a zero-free face.**  Nothing is contracted: the contracted
target is the expanded target of the candidate, the contracted datum is the
candidate's own outgoing datum, and the positive realization is the cleared
face itself. -/
noncomputable def contractedGluing
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (hPositive : ∀ i, 0 < coordinates i)
    (hValid : data.Valid)
    (hConnected : graph_connected target)
    (hGenus : genus target = 0) :
    Candidate.ClearedFace.ContractedGluing
      (sourceContractionTopology face hPositive) where
  contractedTarget := TargetExpansion.graph target wall candidate.right
  contractedData := candidate.datum
  realization := positiveRealization face hPositive
  valid := candidate.datum_valid hValid
  targetConnected :=
    TargetExpansion.graph_connected target wall candidate.right hConnected
  targetGenus := by
    rw [TargetExpansion.graph_genus target wall candidate.right, hGenus]
  sourceEquiv := sourceEquiv face hPositive

/-- The zero-free endpoint already produces the rank-one pencil on the
canonical contracted source. -/
theorem bnExists_contractedSpec
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (hPositive : ∀ i, 0 < coordinates i)
    (hValid : data.Valid)
    (hConnected : graph_connected target)
    (hGenus : genus target = 0) :
    BNExists (sourceContractionTopology face hPositive).contractedSpec.graph
      1 degree :=
  (contractedGluing face hPositive hValid hConnected hGenus).bnExists

end Face

/-! ## The terminal state of the semantic march -/

section State

open Utilities.Certificate.SubdivisionGraph
open DraismaVargas.LocalCases.SemanticAtlasMarch

variable {coordinate chart : Type*}
  [Fintype coordinate] [DecidableEq coordinate]
  [Fintype chart] [DecidableEq chart]
  {degree : ℕ}
  {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}

omit [Fintype chart] [DecidableEq chart] in
/-- A strictly positive endpoint is in particular a terminal one. -/
theorem terminal_of_currentFinish_pos
    {state : State degree matrix baseStart baseFinish}
    (hPositive : ∀ i, 0 < state.toMatrixState.currentFinish i) :
    state.Terminal :=
  fun i ↦ (hPositive i).le

omit [Fintype chart] [DecidableEq chart] in
/-- Step 1 of the endpoint: the cleared face of a terminal state, at the
candidate and presentation supplied by the chart catalogue. -/
noncomputable def clearedFaceOfTerminal
    {state : State degree matrix baseStart baseFinish}
    (hTerminal : state.Terminal)
    {target : CFGraph.{0}} {data : GluingDatum target degree} {wall : target.V}
    (candidate : Candidate target degree data wall)
    (presentation : candidate.datum.LengthMatrixPresentation coordinate) :
    Candidate.ClearedFace candidate presentation
      state.toMatrixState.currentFinish :=
  Candidate.clearedFace candidate presentation
    state.toMatrixState.currentFinish hTerminal

end State

end DraismaVargas.LocalCases.ZeroFreeTerminalFace
