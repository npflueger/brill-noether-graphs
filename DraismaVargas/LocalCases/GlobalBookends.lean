module

public import DraismaVargas.LocalCases.BalancedGlobal
public import DraismaVargas.LocalCases.W4DeterminantContributions

@[expose] public section

/-!
# Global continuation wrappers for Equations (1) and (10)

These are Equations (1) and (10) of Draisma--Vargas Part I, in Cases {w4} and
{w2-r1}.  Unlike the distinguished-block cases, the four-valent and `w2-r1`
arguments balance contributions accumulated over all wall blocks.  What the
source must supply is therefore a whole function of occurrence-level
`Candidate`s.  This file proves that once those concrete candidates and the
source's summed determinant identity are supplied, global validity and the
positive exit follow.  No validity proposition is assumed: each member is a
`BalancedGlobal.Candidate`, so its outgoing datum is constructed by blockwise
global assembly.
-/

namespace DraismaVargas.LocalCases.GlobalBookends

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancingRemaining
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4TargetPairings
open DraismaVargas.LocalCases.W4DeterminantContributions

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree} {wall : target.V}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Forget the occurrence presentation of a finite family of blockwise
assembled candidates while retaining its derived validity theorem. -/
noncomputable def certify {n : ℕ}
    (candidate : Fin n → Candidate target degree data wall) :
    Fin n → CertifiedCandidate data := fun i ↦ (candidate i).certified

/-! ## Equation (1): four-valent wall vertex -/

/-- Equation (1) attached to the three actual blockwise-assembled resolutions
of a four-valent wall vertex. -/
noncomputable def w4BalancedFamily
    (candidate : Fin 3 → Candidate target degree data wall)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate)
    (hbalance : ∑ i, (matrix i).det = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn) :
    Family (coordinate := coordinate) 3 data where
  candidate := certify candidate
  matrix := matrix
  wallColumn := wallColumn
  weight := ![1, 1, 1]
  positiveBalance := balance_w4 hbalance
  agreeOffWall := hAgree

/-- Equation (1) assembled directly from the source's blockwise determinant
accounting.  The candidate determinant is decomposed over source wall blocks;
the three local contributions sum to the old wall contribution at each block;
and the old wall column sums to zero. -/
noncomputable def w4BalancedFamilyOfBlockContributions
    {block : Type*} [Fintype block]
    (candidate : Fin 3 → Candidate target degree data wall)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate)
    (candidateContribution : block → Fin 3 → ℚ)
    (wallContribution : block → ℚ)
    (hcandidate : ∀ i,
      (matrix i).det = ∑ sourceBlock,
        candidateContribution sourceBlock i)
    (hblock : ∀ sourceBlock,
      ∑ i, candidateContribution sourceBlock i =
        wallContribution sourceBlock)
    (hwall : ∑ sourceBlock, wallContribution sourceBlock = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn) :
    Family (coordinate := coordinate) 3 data :=
  w4BalancedFamily candidate matrix wallColumn
    (w4_sum_eq_zero_of_block_contributions
      (fun i ↦ (matrix i).det) candidateContribution wallContribution
      hcandidate hblock hwall)
    hAgree

/-- Equation (1) assembled from the typed nd2/nd3 contribution packages.
The finite pairing identities are discharged by
`W4DeterminantContributions`; only the candidate determinant decomposition
and old wall-column relation remain explicit. -/
noncomputable def w4BalancedFamilyOfContributions
    {block : Type*} [Fintype block]
    (candidate : Fin 3 → Candidate target degree data wall)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate)
    (pattern : block → BlockPattern)
    (contribution : ∀ sourceBlock, Contribution (pattern sourceBlock))
    (hcandidate : ∀ pairing,
      (matrix pairing).det =
        ∑ sourceBlock, (contribution sourceBlock).candidate pairing)
    (hwall : ∑ sourceBlock, (contribution sourceBlock).wall = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn) :
    Family (coordinate := coordinate) 3 data :=
  w4BalancedFamily candidate matrix wallColumn
    (sum_eq_zero_of_contributions pattern contribution
      (fun pairing ↦ (matrix pairing).det) hcandidate hwall)
    hAgree

/-- Equation (1) at the matrix level.  Cofactor expansion and grouping of the
wall-column rows provide each candidate determinant decomposition, so the
remaining determinant premises are only the local identification of typed
nd2/nd3 contributions with those row fibers and the old wall sum. -/
noncomputable def w4BalancedFamilyOfMatrixContributions
    {block : Type*} [Fintype block]
    (candidate : Fin 3 → Candidate target degree data wall)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (rowBlock : coordinate → block)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn)
    (pattern : block → BlockPattern)
    (contribution : ∀ sourceBlock, Contribution (pattern sourceBlock))
    (hcontribution : ∀ sourceBlock pairing,
      (contribution sourceBlock).candidate pairing =
        wallBlockContribution (matrix 0) (matrix pairing) wallColumn
          rowBlock sourceBlock)
    (hwall : ∑ sourceBlock, (contribution sourceBlock).wall = 0) :
    Family (coordinate := coordinate) 3 data :=
  w4BalancedFamily candidate matrix wallColumn
    (sum_det_eq_zero_of_matrix_contributions matrix wallColumn rowBlock
      hAgree pattern contribution hcontribution hwall)
    hAgree

/-- Row-grouped specialization of Equation (1): candidate and old-wall
contributions are identified block by block with cofactor-weighted matrix row
fibers.  This is convenient when every stable-path row belongs to one block;
the entry-summand wrapper below handles the general case. -/
noncomputable def w4BalancedFamilyOfOldColumnContributions
    {block : Type*} [Fintype block]
    (candidate : Fin 3 → Candidate target degree data wall)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (rowBlock : coordinate → block)
    (oldColumns : Finset coordinate)
    (hOld : ∀ column ∈ oldColumns, column ≠ wallColumn)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn)
    (pattern : block → BlockPattern)
    (contribution : ∀ sourceBlock, Contribution (pattern sourceBlock))
    (hcandidate : ∀ sourceBlock pairing,
      (contribution sourceBlock).candidate pairing =
        wallBlockContribution (matrix 0) (matrix pairing) wallColumn
          rowBlock sourceBlock)
    (hwall : ∀ sourceBlock,
      (contribution sourceBlock).wall =
        oldBlockContribution (matrix 0) wallColumn rowBlock oldColumns
          sourceBlock) :
    Family (coordinate := coordinate) 3 data :=
  w4BalancedFamily candidate matrix wallColumn
    (sum_det_eq_zero_of_oldColumn_contributions matrix wallColumn rowBlock
      oldColumns hOld hAgree pattern contribution hcandidate hwall)
    hAgree

/-- General Equation (1) wrapper with entry-level source-block summands.  It
allows one stable-path row to cross several wall blocks, matching the source's
literal sum over edges.  Only the blockwise matrix-entry identifications and
the validity receipts of Case {w4} remain outside this family. -/
noncomputable def w4BalancedFamilyOfEntrySummandContributions
    {block : Type*} [Fintype block]
    (candidate : Fin 3 → Candidate target degree data wall)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (oldColumns : Finset coordinate)
    (hOld : ∀ column ∈ oldColumns, column ≠ wallColumn)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn)
    (pattern : block → BlockPattern)
    (contribution : ∀ sourceBlock, Contribution (pattern sourceBlock))
    (candidateEntrySummand : Fin 3 → block → coordinate → ℚ)
    (hCandidateEntry : ∀ pairing sourceRow,
      matrix pairing sourceRow wallColumn = ∑ sourceBlock,
        candidateEntrySummand pairing sourceBlock sourceRow)
    (hcandidate : ∀ sourceBlock pairing,
      (contribution sourceBlock).candidate pairing =
        wallEntrySummandContribution (matrix 0) wallColumn
          (candidateEntrySummand pairing) sourceBlock)
    (oldEntrySummand : block → coordinate → coordinate → ℚ)
    (hOldEntry : ∀ column ∈ oldColumns, ∀ sourceRow,
      matrix 0 sourceRow column = ∑ sourceBlock,
        oldEntrySummand sourceBlock column sourceRow)
    (hwall : ∀ sourceBlock,
      (contribution sourceBlock).wall =
        oldEntrySummandContribution (matrix 0) wallColumn oldColumns
          oldEntrySummand sourceBlock) :
    Family (coordinate := coordinate) 3 data :=
  w4BalancedFamily candidate matrix wallColumn
    (sum_det_eq_zero_of_entrySummand_contributions matrix wallColumn
      oldColumns hOld hAgree pattern contribution candidateEntrySummand
      hCandidateEntry hcandidate oldEntrySummand hOldEntry hwall)
    hAgree

/-- Equation (1) for actual `LengthMatrixPresentation`s of the three globally
assembled candidates.  Matrix-entry decompositions are derived from their
source paths, so the only determinant receipts are the cofactor-weighted local
nd2/nd3 identifications. -/
noncomputable def w4BalancedFamilyOfLengthMatrixPresentations
    {block : Type*} [Fintype block]
    (candidate : Fin 3 → Candidate target degree data wall)
    (presentation : ∀ pairing,
      (certify candidate pairing).datum.LengthMatrixPresentation coordinate)
    (edgeBlock : ∀ pairing,
      (certify candidate pairing).datum.SourceEdge → block)
    (wallColumn : coordinate) (oldColumns : Finset coordinate)
    (hOld : ∀ column ∈ oldColumns, column ≠ wallColumn)
    (hAgree : ∀ i j,
      AgreeOffColumn
        (GluingDatum.LengthMatrixPresentation.matrix (presentation i))
        (GluingDatum.LengthMatrixPresentation.matrix (presentation j))
        wallColumn)
    (pattern : block → BlockPattern)
    (contribution : ∀ sourceBlock, Contribution (pattern sourceBlock))
    (hcandidate : ∀ sourceBlock pairing,
      (contribution sourceBlock).candidate pairing =
        GluingDatum.LengthMatrixPresentation.blockQuotientContribution
          (presentation pairing) (edgeBlock pairing) sourceBlock wallColumn
          (fun sourceRow ↦
            (GluingDatum.LengthMatrixPresentation.matrix
              (presentation 0)).adjugate wallColumn sourceRow))
    (hwall : ∀ sourceBlock,
      (contribution sourceBlock).wall =
        ∑ column ∈ oldColumns,
          GluingDatum.LengthMatrixPresentation.blockQuotientContribution
            (presentation 0) (edgeBlock 0) sourceBlock column
            (fun sourceRow ↦
              (GluingDatum.LengthMatrixPresentation.matrix
                (presentation 0)).adjugate wallColumn sourceRow)) :
    Family (coordinate := coordinate) 3 data :=
  w4BalancedFamily candidate
    (fun pairing ↦
      GluingDatum.LengthMatrixPresentation.matrix (presentation pairing))
    wallColumn
    (sum_det_eq_zero_of_lengthMatrixPresentations
      (fun pairing ↦ (certify candidate pairing).datum)
      presentation edgeBlock wallColumn oldColumns hOld hAgree pattern
      contribution hcandidate hwall)
    hAgree

/-- Source-facing Equation (1) wrapper for actual length-matrix
presentations.  The remaining determinant input is exactly one quotient
receipt per source wall block, recording the nd2/nd3 edge classification from
the paper. -/
noncomputable def w4BalancedFamilyOfLengthMatrixQuotientReceipts
    {block : Type*} [Fintype block]
    (candidate : Fin 3 → Candidate target degree data wall)
    (presentation : ∀ pairing,
      (certify candidate pairing).datum.LengthMatrixPresentation coordinate)
    (edgeBlock : ∀ pairing,
      (certify candidate pairing).datum.SourceEdge → block)
    (wallColumn : coordinate) (oldColumns : Finset coordinate)
    (hOld : ∀ column ∈ oldColumns, column ≠ wallColumn)
    (hAgree : ∀ i j,
      AgreeOffColumn
        (GluingDatum.LengthMatrixPresentation.matrix (presentation i))
        (GluingDatum.LengthMatrixPresentation.matrix (presentation j))
        wallColumn)
    (pattern : block → BlockPattern)
    (receipt : ∀ sourceBlock,
      QuotientReceipt
        (fun pairing ↦
          GluingDatum.LengthMatrixPresentation.blockQuotientContribution
            (presentation pairing) (edgeBlock pairing) sourceBlock wallColumn
            (fun sourceRow ↦
              (GluingDatum.LengthMatrixPresentation.matrix
                (presentation 0)).adjugate wallColumn sourceRow))
        (∑ column ∈ oldColumns,
          GluingDatum.LengthMatrixPresentation.blockQuotientContribution
            (presentation 0) (edgeBlock 0) sourceBlock column
            (fun sourceRow ↦
              (GluingDatum.LengthMatrixPresentation.matrix
                (presentation 0)).adjugate wallColumn sourceRow))
        (pattern sourceBlock)) :
    Family (coordinate := coordinate) 3 data :=
  w4BalancedFamily candidate
    (fun pairing ↦
      GluingDatum.LengthMatrixPresentation.matrix (presentation pairing))
    wallColumn
    (sum_det_eq_zero_of_lengthMatrixQuotientReceipts
      (fun pairing ↦ (certify candidate pairing).datum)
      presentation edgeBlock wallColumn oldColumns hOld hAgree pattern receipt)
    hAgree

/-- A common tagged type for path occurrences belonging to any of the three
candidate data of Case {w4}. -/
abbrev W4CandidatePathOccurrence
    (candidate : Fin 3 → Candidate target degree data wall)
    (coordinate : Type*) :=
  Σ pairing, coordinate × (certify candidate pairing).datum.SourceEdge

/-- Tag the literal path occurrences from one candidate so the three
candidate classifications can inhabit one common multiset type. -/
noncomputable def w4TaggedBlockColumnOccurrences
    {block : Type*} [Fintype block]
    (candidate : Fin 3 → Candidate target degree data wall)
    (presentation : ∀ pairing,
      (certify candidate pairing).datum.LengthMatrixPresentation coordinate)
    (edgeBlock : ∀ pairing,
      (certify candidate pairing).datum.SourceEdge → block)
    (sourceBlock : block) (wallColumn : coordinate) (pairing : Fin 3) :
    Multiset (W4CandidatePathOccurrence candidate coordinate) :=
  (GluingDatum.LengthMatrixPresentation.blockColumnOccurrences
    (presentation pairing) (edgeBlock pairing) sourceBlock wallColumn).map
      (fun occurrence ↦ ⟨pairing, occurrence⟩)

/-- Weight a tagged candidate occurrence by the common cofactor row and its
own candidate datum's source-edge dilation index. -/
noncomputable def w4CandidateOccurrenceWeight
    (candidate : Fin 3 → Candidate target degree data wall)
    (presentation : ∀ pairing,
      (certify candidate pairing).datum.LengthMatrixPresentation coordinate)
    (wallColumn : coordinate)
    (occurrence : W4CandidatePathOccurrence candidate coordinate) : ℚ :=
  (GluingDatum.LengthMatrixPresentation.matrix
      (presentation 0)).adjugate wallColumn occurrence.2.1 /
    (certify candidate occurrence.1).datum.sourceEdgeIndex occurrence.2.2

/-- Weight an old-column occurrence in candidate zero by the same common
cofactor row and its source-edge dilation index. -/
noncomputable def w4WallOccurrenceWeight
    (candidate : Fin 3 → Candidate target degree data wall)
    (presentation : ∀ pairing,
      (certify candidate pairing).datum.LengthMatrixPresentation coordinate)
    (wallColumn : coordinate)
    (occurrence : coordinate × (certify candidate 0).datum.SourceEdge) : ℚ :=
  (GluingDatum.LengthMatrixPresentation.matrix
      (presentation 0)).adjugate wallColumn occurrence.1 /
    (certify candidate 0).datum.sourceEdgeIndex occurrence.2

/-- Tagging candidate occurrences and then weighting them recovers exactly
the rational term multiset exposed by its length-matrix presentation. -/
theorem map_w4TaggedBlockColumnOccurrences
    {block : Type*} [Fintype block]
    (candidate : Fin 3 → Candidate target degree data wall)
    (presentation : ∀ pairing,
      (certify candidate pairing).datum.LengthMatrixPresentation coordinate)
    (edgeBlock : ∀ pairing,
      (certify candidate pairing).datum.SourceEdge → block)
    (sourceBlock : block) (wallColumn : coordinate) (pairing : Fin 3) :
    (w4TaggedBlockColumnOccurrences candidate presentation edgeBlock
      sourceBlock wallColumn pairing).map
        (w4CandidateOccurrenceWeight candidate presentation wallColumn) =
      GluingDatum.LengthMatrixPresentation.blockColumnTerms
        (presentation pairing) (edgeBlock pairing) sourceBlock wallColumn
        (fun sourceRow ↦
          (GluingDatum.LengthMatrixPresentation.matrix
            (presentation 0)).adjugate wallColumn sourceRow) := by
  rw [GluingDatum.LengthMatrixPresentation.blockColumnTerms_eq_occurrences_map]
  unfold w4TaggedBlockColumnOccurrences
  rw [Multiset.map_map]
  congr 1

/-- Weighting old-column occurrences recovers their combined rational term
multiset. -/
theorem map_blockColumnsOccurrences_w4WallOccurrenceWeight
    {block : Type*} [Fintype block]
    (candidate : Fin 3 → Candidate target degree data wall)
    (presentation : ∀ pairing,
      (certify candidate pairing).datum.LengthMatrixPresentation coordinate)
    (edgeBlock : ∀ pairing,
      (certify candidate pairing).datum.SourceEdge → block)
    (sourceBlock : block) (wallColumn : coordinate)
    (oldColumns : Finset coordinate) :
    (GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
      (presentation 0) (edgeBlock 0) sourceBlock oldColumns).map
        (w4WallOccurrenceWeight candidate presentation wallColumn) =
      GluingDatum.LengthMatrixPresentation.blockColumnsTerms
        (presentation 0) (edgeBlock 0) sourceBlock oldColumns
        (fun sourceRow ↦
          (GluingDatum.LengthMatrixPresentation.matrix
            (presentation 0)).adjugate wallColumn sourceRow) := by
  rw [GluingDatum.LengthMatrixPresentation.blockColumnsTerms_eq_occurrences_map]
  rfl

/-- Construct an nd2 occurrence receipt without rational arithmetic.  The
source supplies exact row/edge occurrence profiles and equality of the
corresponding rows and dilation indices; the cofactor quotient identities are
then definitional consequences. -/
noncomputable def w4OccurrenceReceiptNd2
    {blockType : Type*} [Fintype blockType]
    (candidate : Fin 3 → Candidate target degree data wall)
    (presentation : ∀ pairing,
      (certify candidate pairing).datum.LengthMatrixPresentation coordinate)
    (edgeBlock : ∀ pairing,
      (certify candidate pairing).datum.SourceEdge → blockType)
    (sourceBlock : blockType) (wallColumn : coordinate)
    (oldColumns : Finset coordinate) (block : Nd2Block)
    (newOccurrence : ∀ pairing,
      coordinate × (certify candidate pairing).datum.SourceEdge)
    (oldOccurrence : Fin 4 →
      coordinate × (certify candidate 0).datum.SourceEdge)
    (candidate_occurrences : ∀ pairing,
      (if Pairing.labelRight pairing block.first =
          Pairing.labelRight pairing block.second then 0
        else {⟨pairing, newOccurrence pairing⟩}) =
        w4TaggedBlockColumnOccurrences candidate presentation edgeBlock
          sourceBlock wallColumn pairing)
    (wall_occurrences :
      {oldOccurrence block.first, oldOccurrence block.second} =
        GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
          (presentation 0) (edgeBlock 0) sourceBlock oldColumns)
    (new_row : ∀ pairing,
      Pairing.labelRight pairing block.first ≠
        Pairing.labelRight pairing block.second →
      (newOccurrence pairing).1 = (oldOccurrence block.first).1)
    (new_index : ∀ pairing,
      Pairing.labelRight pairing block.first ≠
        Pairing.labelRight pairing block.second →
      (certify candidate pairing).datum.sourceEdgeIndex
          (newOccurrence pairing).2 =
        (certify candidate 0).datum.sourceEdgeIndex
          (oldOccurrence block.first).2)
    (old_row : (oldOccurrence block.first).1 =
      (oldOccurrence block.second).1)
    (old_index :
      (certify candidate 0).datum.sourceEdgeIndex
          (oldOccurrence block.first).2 =
        (certify candidate 0).datum.sourceEdgeIndex
          (oldOccurrence block.second).2) :
    OccurrenceReceipt
      (fun pairing ↦
        w4TaggedBlockColumnOccurrences candidate presentation edgeBlock
          sourceBlock wallColumn pairing)
      (GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
        (presentation 0) (edgeBlock 0) sourceBlock oldColumns)
      (w4CandidateOccurrenceWeight candidate presentation wallColumn)
      (w4WallOccurrenceWeight candidate presentation wallColumn)
      (.nd2 block) :=
  OccurrenceReceipt.nd2 block
    (fun pairing ↦ ⟨pairing, newOccurrence pairing⟩) oldOccurrence
    (by
      unfold w4WallOccurrenceWeight
      rw [old_row, old_index])
    candidate_occurrences
    (fun pairing h ↦ by
      unfold w4CandidateOccurrenceWeight w4WallOccurrenceWeight
      change
        (GluingDatum.LengthMatrixPresentation.matrix
            (presentation 0)).adjugate wallColumn
              (newOccurrence pairing).1 /
            (certify candidate pairing).datum.sourceEdgeIndex
              (newOccurrence pairing).2 =
          (GluingDatum.LengthMatrixPresentation.matrix
            (presentation 0)).adjugate wallColumn
              (oldOccurrence block.first).1 /
            (certify candidate 0).datum.sourceEdgeIndex
              (oldOccurrence block.first).2
      rw [new_row pairing h, new_index pairing h])
    wall_occurrences

/-- Construct an nd3 occurrence receipt from exact singleton row/edge
profiles and row/index identifications with the selected old branch. -/
noncomputable def w4OccurrenceReceiptNd3
    {blockType : Type*} [Fintype blockType]
    (candidate : Fin 3 → Candidate target degree data wall)
    (presentation : ∀ pairing,
      (certify candidate pairing).datum.LengthMatrixPresentation coordinate)
    (edgeBlock : ∀ pairing,
      (certify candidate pairing).datum.SourceEdge → blockType)
    (sourceBlock : blockType) (wallColumn : coordinate)
    (oldColumns : Finset coordinate) (block : Nd3Block)
    (newOccurrence : ∀ pairing,
      coordinate × (certify candidate pairing).datum.SourceEdge)
    (oldOccurrence : Fin 4 →
      coordinate × (certify candidate 0).datum.SourceEdge)
    (candidate_occurrences : ∀ pairing,
      {⟨pairing, newOccurrence pairing⟩} =
        w4TaggedBlockColumnOccurrences candidate presentation edgeBlock
          sourceBlock wallColumn pairing)
    (wall_occurrences :
      {oldOccurrence block.first, oldOccurrence block.second,
          oldOccurrence block.third} =
        GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
          (presentation 0) (edgeBlock 0) sourceBlock oldColumns)
    (new_row : ∀ pairing,
      (newOccurrence pairing).1 =
        (oldOccurrence (block.singletonLabel pairing)).1)
    (new_index : ∀ pairing,
      (certify candidate pairing).datum.sourceEdgeIndex
          (newOccurrence pairing).2 =
        (certify candidate 0).datum.sourceEdgeIndex
          (oldOccurrence (block.singletonLabel pairing)).2) :
    OccurrenceReceipt
      (fun pairing ↦
        w4TaggedBlockColumnOccurrences candidate presentation edgeBlock
          sourceBlock wallColumn pairing)
      (GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
        (presentation 0) (edgeBlock 0) sourceBlock oldColumns)
      (w4CandidateOccurrenceWeight candidate presentation wallColumn)
      (w4WallOccurrenceWeight candidate presentation wallColumn)
      (.nd3 block) :=
  OccurrenceReceipt.nd3 block
    (fun pairing ↦ ⟨pairing, newOccurrence pairing⟩) oldOccurrence
    candidate_occurrences
    (fun pairing ↦ by
      unfold w4CandidateOccurrenceWeight w4WallOccurrenceWeight
      change
        (GluingDatum.LengthMatrixPresentation.matrix
            (presentation 0)).adjugate wallColumn
              (newOccurrence pairing).1 /
            (certify candidate pairing).datum.sourceEdgeIndex
              (newOccurrence pairing).2 =
          (GluingDatum.LengthMatrixPresentation.matrix
            (presentation 0)).adjugate wallColumn
              (oldOccurrence (block.singletonLabel pairing)).1 /
            (certify candidate 0).datum.sourceEdgeIndex
              (oldOccurrence (block.singletonLabel pairing)).2
      rw [new_row pairing, new_index pairing])
    wall_occurrences

/-- Occurrence-safe source-facing Equation (1) wrapper.  Each local receipt
classifies exact multisets of displayed stable-path terms, so repeated source
edges cannot be lost and no numerical cancellation is used as evidence for
the case split of Case {w4}. -/
noncomputable def w4BalancedFamilyOfLengthMatrixTermReceipts
    {block : Type*} [Fintype block]
    (candidate : Fin 3 → Candidate target degree data wall)
    (presentation : ∀ pairing,
      (certify candidate pairing).datum.LengthMatrixPresentation coordinate)
    (edgeBlock : ∀ pairing,
      (certify candidate pairing).datum.SourceEdge → block)
    (wallColumn : coordinate) (oldColumns : Finset coordinate)
    (hOld : ∀ column ∈ oldColumns, column ≠ wallColumn)
    (hAgree : ∀ i j,
      AgreeOffColumn
        (GluingDatum.LengthMatrixPresentation.matrix (presentation i))
        (GluingDatum.LengthMatrixPresentation.matrix (presentation j))
        wallColumn)
    (pattern : block → BlockPattern)
    (receipt : ∀ sourceBlock,
      TermReceipt
        (fun pairing ↦
          GluingDatum.LengthMatrixPresentation.blockColumnTerms
            (presentation pairing) (edgeBlock pairing) sourceBlock wallColumn
            (fun sourceRow ↦
              (GluingDatum.LengthMatrixPresentation.matrix
                (presentation 0)).adjugate wallColumn sourceRow))
        (GluingDatum.LengthMatrixPresentation.blockColumnsTerms
          (presentation 0) (edgeBlock 0) sourceBlock oldColumns
          (fun sourceRow ↦
            (GluingDatum.LengthMatrixPresentation.matrix
              (presentation 0)).adjugate wallColumn sourceRow))
        (pattern sourceBlock)) :
    Family (coordinate := coordinate) 3 data :=
  w4BalancedFamily candidate
    (fun pairing ↦
      GluingDatum.LengthMatrixPresentation.matrix (presentation pairing))
    wallColumn
    (sum_det_eq_zero_of_lengthMatrixTermReceipts
      (fun pairing ↦ (certify candidate pairing).datum)
      presentation edgeBlock wallColumn oldColumns hOld hAgree pattern receipt)
    hAgree

/-- The lowest-level source-facing Equation (1) wrapper.  Receipts classify literal
`(stable row, source edge)` occurrences, with candidate occurrences tagged by
their pairing.  The generic occurrence receipt and the length-matrix weighting
identities derive the rational term receipts automatically. -/
noncomputable def w4BalancedFamilyOfLengthMatrixOccurrenceReceipts
    {block : Type*} [Fintype block]
    (candidate : Fin 3 → Candidate target degree data wall)
    (presentation : ∀ pairing,
      (certify candidate pairing).datum.LengthMatrixPresentation coordinate)
    (edgeBlock : ∀ pairing,
      (certify candidate pairing).datum.SourceEdge → block)
    (wallColumn : coordinate) (oldColumns : Finset coordinate)
    (hOld : ∀ column ∈ oldColumns, column ≠ wallColumn)
    (hAgree : ∀ i j,
      AgreeOffColumn
        (GluingDatum.LengthMatrixPresentation.matrix (presentation i))
        (GluingDatum.LengthMatrixPresentation.matrix (presentation j))
        wallColumn)
    (pattern : block → BlockPattern)
    (receipt : ∀ sourceBlock,
      OccurrenceReceipt
        (fun pairing ↦
          w4TaggedBlockColumnOccurrences candidate presentation edgeBlock
            sourceBlock wallColumn pairing)
        (GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
          (presentation 0) (edgeBlock 0) sourceBlock oldColumns)
        (w4CandidateOccurrenceWeight candidate presentation wallColumn)
        (w4WallOccurrenceWeight candidate presentation wallColumn)
        (pattern sourceBlock)) :
    Family (coordinate := coordinate) 3 data :=
  w4BalancedFamilyOfLengthMatrixTermReceipts candidate presentation edgeBlock
    wallColumn oldColumns hOld hAgree pattern (fun sourceBlock ↦ by
      have weighted := (receipt sourceBlock).toTermReceipt
      simpa only [map_w4TaggedBlockColumnOccurrences,
        map_blockColumnsOccurrences_w4WallOccurrenceWeight] using weighted)

/-- Semantic Equation (1) wrapper retaining the actual candidates and their
presentations, so the positive exit can be cleared to an explicit pencil. -/
noncomputable def w4PresentedFamilyOfLengthMatrixOccurrenceReceipts
    {block : Type*} [Fintype block]
    (candidate : Fin 3 → Candidate target degree data wall)
    (presentation : ∀ pairing,
      (certify candidate pairing).datum.LengthMatrixPresentation coordinate)
    (edgeBlock : ∀ pairing,
      (certify candidate pairing).datum.SourceEdge → block)
    (wallColumn : coordinate) (oldColumns : Finset coordinate)
    (hOld : ∀ column ∈ oldColumns, column ≠ wallColumn)
    (hAgree : ∀ i j,
      AgreeOffColumn
        (GluingDatum.LengthMatrixPresentation.matrix (presentation i))
        (GluingDatum.LengthMatrixPresentation.matrix (presentation j))
        wallColumn)
    (pattern : block → BlockPattern)
    (receipt : ∀ sourceBlock,
      OccurrenceReceipt
        (fun pairing ↦
          w4TaggedBlockColumnOccurrences candidate presentation edgeBlock
            sourceBlock wallColumn pairing)
        (GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
          (presentation 0) (edgeBlock 0) sourceBlock oldColumns)
        (w4CandidateOccurrenceWeight candidate presentation wallColumn)
        (w4WallOccurrenceWeight candidate presentation wallColumn)
        (pattern sourceBlock)) :
    PresentedFamily (coordinate := coordinate) 3 data wall := by
  let balanced := w4BalancedFamilyOfLengthMatrixOccurrenceReceipts candidate
    presentation edgeBlock wallColumn oldColumns hOld hAgree pattern receipt
  exact {
    candidate := candidate
    presentation := presentation
    wallColumn := wallColumn
    weight := ![1, 1, 1]
    positiveBalance := balanced.positiveBalance
    agreeOffWall := hAgree
  }

/-- Full global continuation for Equation (1), conditional only on the
source-classified occurrence-level candidate function and its summed
determinant identity. -/
theorem w4_exists_valid_positive_exit
    (candidate : Fin 3 → Candidate target degree data wall)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate)
    (hbalance : ∑ i, (matrix i).det = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn)
    (hValid : data.Valid) (incoming : Fin 3)
    (hincoming : (matrix incoming).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin 3 → coordinate → ℚ)
    (hz : z wallColumn = 0)
    (hzpos : ∀ i, i ≠ wallColumn → 0 < z i)
    (hSystems : ∀ outgoing,
      (matrix incoming).mulVec incomingVelocity =
        (matrix outgoing).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity wallColumn < 0) :
    ∃ outgoing,
      (certify candidate outgoing).datum.Valid ∧
      (matrix incoming).det * (matrix outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (matrix outgoing).mulVec
            (z + t • outgoingVelocity outgoing) =
          (matrix incoming).mulVec z +
            t • (matrix incoming).mulVec incomingVelocity := by
  exact (w4BalancedFamily candidate matrix wallColumn hbalance
    hAgree).exists_valid_positive_exit hValid incoming hincoming z
      incomingVelocity outgoingVelocity hz hzpos
      (fun outgoing _ ↦ hSystems outgoing) hIncomingDirection

/-- The continuation at a four-valent wall vertex, with Equation (1) supplied
in its source-local form,
rather than as a preassembled determinant-sum hypothesis. -/
theorem w4_exists_valid_positive_exit_of_block_contributions
    {block : Type*} [Fintype block]
    (candidate : Fin 3 → Candidate target degree data wall)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate)
    (candidateContribution : block → Fin 3 → ℚ)
    (wallContribution : block → ℚ)
    (hcandidate : ∀ i,
      (matrix i).det = ∑ sourceBlock,
        candidateContribution sourceBlock i)
    (hblock : ∀ sourceBlock,
      ∑ i, candidateContribution sourceBlock i =
        wallContribution sourceBlock)
    (hwall : ∑ sourceBlock, wallContribution sourceBlock = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn)
    (hValid : data.Valid) (incoming : Fin 3)
    (hincoming : (matrix incoming).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin 3 → coordinate → ℚ)
    (hz : z wallColumn = 0)
    (hzpos : ∀ i, i ≠ wallColumn → 0 < z i)
    (hSystems : ∀ outgoing,
      (matrix incoming).mulVec incomingVelocity =
        (matrix outgoing).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity wallColumn < 0) :
    ∃ outgoing,
      (certify candidate outgoing).datum.Valid ∧
      (matrix incoming).det * (matrix outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (matrix outgoing).mulVec
            (z + t • outgoingVelocity outgoing) =
          (matrix incoming).mulVec z +
            t • (matrix incoming).mulVec incomingVelocity := by
  exact (w4BalancedFamilyOfBlockContributions candidate matrix wallColumn
    candidateContribution wallContribution hcandidate hblock hwall
    hAgree).exists_valid_positive_exit hValid incoming hincoming z
      incomingVelocity outgoingVelocity hz hzpos
      (fun outgoing _ ↦ hSystems outgoing) hIncomingDirection

/-! ## Equation (10): two-valent wall vertex with ramification one -/

/-- Equation (10) attached to the two actual blockwise-assembled resolutions
of the `w2-r1` wall. -/
noncomputable def w2r1BalancedFamily
    (candidate : Fin 2 → Candidate target degree data wall)
    (matrix : Fin 2 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate)
    (hbalance : (matrix 0).det + (matrix 1).det = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn) :
    Family (coordinate := coordinate) 2 data where
  candidate := certify candidate
  matrix := matrix
  wallColumn := wallColumn
  weight := ![1, 1]
  positiveBalance := by
    convert balance_w2_r1 hbalance using 1
    ext i
    fin_cases i <;> rfl
  agreeOffWall := hAgree

/-- Full global continuation for Equation (10), conditional only on its two
source-classified occurrence-level candidates and summed determinant identity. -/
theorem w2r1_exists_valid_positive_exit
    (candidate : Fin 2 → Candidate target degree data wall)
    (matrix : Fin 2 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate)
    (hbalance : (matrix 0).det + (matrix 1).det = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn)
    (hValid : data.Valid) (incoming : Fin 2)
    (hincoming : (matrix incoming).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin 2 → coordinate → ℚ)
    (hz : z wallColumn = 0)
    (hzpos : ∀ i, i ≠ wallColumn → 0 < z i)
    (hSystems : ∀ outgoing,
      (matrix incoming).mulVec incomingVelocity =
        (matrix outgoing).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity wallColumn < 0) :
    ∃ outgoing,
      (certify candidate outgoing).datum.Valid ∧
      (matrix incoming).det * (matrix outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (matrix outgoing).mulVec
            (z + t • outgoingVelocity outgoing) =
          (matrix incoming).mulVec z +
            t • (matrix incoming).mulVec incomingVelocity := by
  exact (w2r1BalancedFamily candidate matrix wallColumn hbalance
    hAgree).exists_valid_positive_exit hValid incoming hincoming z
      incomingVelocity outgoingVelocity hz hzpos
      (fun outgoing _ ↦ hSystems outgoing) hIncomingDirection

end DraismaVargas.LocalCases.GlobalBookends
