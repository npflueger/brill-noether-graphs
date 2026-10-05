module

public import DraismaVargas.Interface
public import DraismaVargas.LocalCases.ClosedFaceRealization
public import DraismaVargas.LocalCases.PrunedContractedSpecResidues

@[expose] public section

/-!
# The closed-face endpoint interface

Once a terminal DV cone face has been cleared to nonnegative integral lengths,
its zero source occurrences have a canonical positive contraction.  Two
source-dependent finite inputs are then needed:

* the contracted target/source partitions form a valid positive integral
  gluing realization over a connected genus-zero target; and
* the positive contracted source **with its pendant trees deleted** — the
  pruned contracted spec `SourceContractionTopology.prunedSpec` of
  `PrunedContractedSpec` — is a checked refinement presentation of the
  requested stable metric at the same common scale.

This file states those inputs as concrete data and proves that they imply the
regular-subdivision gonality bound.  In particular, no rank-one divisor is a
field: it is derived from the contracted gluing datum by the uniform target
tree theorem, and then **pushed forward across the deletion of the pendant
trees** (`SourceContractionTopology.bnExists_prunedSpec'`) before the
refinement presentation transports it to the scaled requested specification.

## Why the refinement targets the pruned source

`InputRefinement` targets `prunedSpec`, not the whole contracted source
`topology.contractedSpec.graph`: with its pendant trees included, the contracted
source admits no such refinement presentation as soon as some dangling
occurrence has positive length.  Targeting `prunedSpec` needs the kept classes
to be nonempty (`kept`), and `exists_subdivisionPencil` inserts the pendant
pushforward between `ContractedGluing.bnExists` and
`RefinementPresentation.bnExists_iff`.  The pushforward's own inputs — the
pendant separation and the class/slot count — are theorems of
`PrunedContractedSpecResidues`; the count needs connectivity of the quotient
source, which is `candidate.datum.Valid.1` and is threaded as `hConnected`.
-/

namespace DraismaVargas.LocalCases.BalancedGlobal.Candidate.ClearedFace

open Utilities
open Utilities.Certificate
open Utilities.Certificate.IteratedSplitRefinement
open DraismaVargas.Infrastructure

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree data wall}
  {coordinate : Type*}
  {presentation : candidate.datum.LengthMatrixPresentation coordinate}
  {coordinates : coordinate → ℚ}
  {face : ClearedFace candidate presentation coordinates}

/-- A genuine positive gluing realization obtained after contracting every
zero target/source occurrence of a terminal face.  The source equivalence
identifies it with the canonical positive contraction already constructed from
the face's zero-source forest. -/
structure ContractedGluing
    (topology : SourceContractionTopology face) where
  contractedTarget : CFGraph
  contractedData : GluingDatum contractedTarget degree
  realization : contractedData.IntegralRealization
  valid : contractedData.Valid
  targetConnected : graph_connected contractedTarget
  targetGenus : genus contractedTarget = 0
  sourceEquiv : LaplacianEquiv topology.contractedSpec.graph
    realization.sourceSpec.graph

namespace ContractedGluing

/-- The contracted gluing receipt produces rank one in the sheet degree on the
canonical positive source contraction. -/
theorem bnExists
    {topology : SourceContractionTopology face}
    (contracted : ContractedGluing topology) :
    BNExists topology.contractedSpec.graph 1 degree := by
  have hRealized :
      BNExists contracted.realization.sourceSpec.graph 1 degree :=
    (contracted.realization.bnExists_and_effective_of_connected_genus_zero_target
      contracted.valid.1 contracted.targetConnected contracted.targetGenus
      (Classical.choice
        (inferInstance : Nonempty contracted.contractedTarget.V))).1
  exact (contracted.sourceEquiv.bnExists_iff 1 degree).mpr hRealized

end ContractedGluing

/-- Identification of the **pruned** canonical contracted source — the
contracted quotient source with its pendant trees deleted,
`SourceContractionTopology.prunedSpec` — with a positive bivalent refinement
of the requested stable specification at the face's exact common scale.

`kept` says pruning leaves at least one class, which `prunedSpec` needs to be
a `Spec`; it is discharged by any placement of a stable core vertex on a
surviving occurrence (`StatementFromLink.keptClasses_nonempty_of_spanning`). -/
structure InputRefinement {n p : ℕ} (spec : SubdivisionGraph.Spec n p)
    (topology : SourceContractionTopology face) where
  /-- Pruning keeps at least one contraction class. -/
  kept : (SourceContractionTopology.keptClasses topology).Nonempty
  /-- The refinement presentation of the scaled input onto the pruned
  contracted source. -/
  refinement : RefinementPresentation
    ({ n := n
       p := p
       spec := spec.scale face.scale face.scale_pos } : PackedSpec)
    (SourceContractionTopology.prunedSpec topology kept).graph

/-- **The pendant pushforward, at the refinement.**  Rank one on the whole
contracted quotient source is rank one on its pruned contracted spec.  This is
`SourceContractionTopology.bnExists_prunedSpec'`, whose two inputs
(`pendantSeparated` and `classCard_add_keptSlots_card`) are theorems; the count
needs connectivity of the quotient source. -/
theorem InputRefinement.bnExists_prunedSpec
    {n p : ℕ} {spec : SubdivisionGraph.Spec n p}
    {topology : SourceContractionTopology face}
    (input : InputRefinement spec topology)
    (hConnected : candidate.datum.Connected)
    (hBN : BNExists topology.contractedSpec.graph 1 degree) :
    BNExists (SourceContractionTopology.prunedSpec topology input.kept).graph 1 degree :=
  SourceContractionTopology.bnExists_prunedSpec' topology input.kept hConnected hBN

/-- The closed endpoint retains the actual subdivision pencil and its exact
denominator-clearing scale, rather than only the resulting gonality
inequality.  The chain is `contracted.bnExists` (rank one on the contracted
quotient source), then the pendant pushforward, then the refinement
presentation. -/
theorem exists_subdivisionPencil
    {n p : ℕ} {spec : SubdivisionGraph.Spec n p}
    {topology : SourceContractionTopology face}
    (contracted : ContractedGluing topology)
    (input : InputRefinement spec topology)
    (hConnected : candidate.datum.Connected) :
    ∃ pencil : DraismaVargas.SubdivisionPencil spec degree,
      pencil.scale = face.scale := by
  apply DraismaVargas.SubdivisionPencil.exists_of_BNExists face.scale_pos
  exact (input.refinement.bnExists_iff 1 degree).mpr
    (input.bnExists_prunedSpec hConnected contracted.bnExists)

/-- **Closed endpoint composition.**  A genus-preserving zero-source
contraction, a contracted valid gluing realization, and a checked refinement
of the scaled input onto the pruned contracted source imply the desired
regular-subdivision gonality bound. -/
theorem regularSubdivisionGonality_le
    {n p : ℕ} {spec : SubdivisionGraph.Spec n p}
    {topology : SourceContractionTopology face}
    (contracted : ContractedGluing topology)
    (input : InputRefinement spec topology)
    (hConnected : candidate.datum.Connected) :
    spec.regularSubdivisionGonality ≤ degree := by
  obtain ⟨pencil, _⟩ := exists_subdivisionPencil contracted input hConnected
  exact pencil.gonality_le

end DraismaVargas.LocalCases.BalancedGlobal.Candidate.ClearedFace
