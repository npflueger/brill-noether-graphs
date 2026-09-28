import DraismaVargas.LocalCases.BalancingRemaining
import DraismaVargas.LocalCases.W4Assembly
import Utilities.IntegralGeometry.WallColumnDeterminant
import DraismaVargas.Infrastructure.LengthMatrix
import Mathlib.Tactic

/-!
# Blockwise determinant contributions in the W4 case

The W4 case is Case {w4} of Draisma--Vargas Part I (a four-valent wall
vertex).  Its Equations `w4-nd2` and `w4-nd3` are finite identities over
the three target pairings.  For an nd2 source block, exactly two pairings put
its two external branches on opposite sides.  For an nd3 source block, each of
its three external branches is the singleton for exactly one pairing.

This file proves those two facts for the actual pairing and singleton
functions used by `W4Assembly`, then packages them in the block-contribution
form consumed by Equation (1).  The final quotient-receipt layer states the
remaining source classification directly in terms of the literal
adjugate-row quantities `c(h(e)) / m(e)` of a concrete length matrix.  Its
strongest form uses exact multisets of stable-path terms, retaining repeated
occurrences before any summation.  A lower-level `OccurrenceReceipt` boundary
classifies the literal row/edge pairs and applies rational weights only after
that finite classification has been checked.
-/

namespace DraismaVargas.LocalCases.W4DeterminantContributions

open DraismaVargas.LocalCases.BalancingRemaining
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4TargetPairings
open DraismaVargas.LocalCases.BalancingValencyTwo
open DraismaVargas.Infrastructure
open Finset

namespace Nd2Block

/-- The internal-edge contribution of an nd2 block in one pairing.  It is
present precisely when the two external branches lie on opposite sides. -/
def candidateContribution (block : Nd2Block) (value : ℚ)
    (pairing : Fin 3) : ℚ :=
  if Pairing.labelRight pairing block.first =
      Pairing.labelRight pairing block.second then 0 else value

/-- Exactly two representative pairings separate two distinct four-star
labels. -/
theorem card_separating (block : Nd2Block) :
    (Finset.univ.filter fun pairing : Fin 3 =>
      Pairing.labelRight pairing block.first ≠
        Pairing.labelRight pairing block.second).card = 2 := by
  rcases block with ⟨first, second, distinct⟩
  revert first second
  decide +kernel

/-- Source identity `w4-nd2`: among the three `2+2` target pairings, two
separate any fixed pair of distinct external branches. -/
theorem sum_candidateContribution (block : Nd2Block) (value : ℚ) :
    ∑ pairing, candidateContribution block value pairing = value + value := by
  classical
  calc
    ∑ pairing, candidateContribution block value pairing =
        ∑ pairing ∈ Finset.univ.filter (fun pairing : Fin 3 =>
          Pairing.labelRight pairing block.first ≠
            Pairing.labelRight pairing block.second), value := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro pairing _
              by_cases h : Pairing.labelRight pairing block.first =
                  Pairing.labelRight pairing block.second <;>
                simp [candidateContribution, h]
    _ = value + value := by
      rw [Finset.sum_const, card_separating]
      ring

/-- The nd2 identity with its right side written as the contributions of the
two old branches.  The equality hypothesis is the source fact that both old
branches and the regrown internal edge have the same stable-edge label and
sheet-block size. -/
theorem sum_candidateContribution_eq_branches (block : Nd2Block)
    (branchValue : Fin 4 → ℚ)
    (hEqual : branchValue block.first = branchValue block.second) :
    ∑ pairing,
        candidateContribution block (branchValue block.first) pairing =
      branchValue block.first + branchValue block.second := by
  rw [sum_candidateContribution, hEqual]

end Nd2Block

namespace Nd3Block

/-- The internal-edge contribution of an nd3 block is the old-branch value
selected by the pairing's singleton side. -/
def candidateContribution (block : Nd3Block) (branchValue : Fin 4 → ℚ)
    (pairing : Fin 3) : ℚ :=
  branchValue (block.singletonLabel pairing)

/-- The three singleton labels form a permutation of the block's three
external branches. -/
theorem singletonLabels_perm (block : Nd3Block) :
    [block.singletonLabel 0, block.singletonLabel 1,
        block.singletonLabel 2].Perm
      [block.first, block.second, block.third] := by
  rcases block with
    ⟨first, second, third, first_ne_second, first_ne_third,
      second_ne_third⟩
  revert first second third
  decide +kernel

/-- Source identity `w4-nd3`: as the three target pairings vary, each of the
three distinct external branches occurs exactly once as the singleton. -/
theorem sum_candidateContribution (block : Nd3Block)
    (branchValue : Fin 4 → ℚ) :
    ∑ pairing, candidateContribution block branchValue pairing =
      branchValue block.first + branchValue block.second +
        branchValue block.third := by
  have hsum := (singletonLabels_perm block).map branchValue |>.sum_eq
  simpa [candidateContribution, Fin.sum_univ_succ, add_assoc] using hsum

end Nd3Block

/-- One source wall block's three candidate contributions and its old
wall-column contribution, together with the appropriate local W4 identity. -/
structure Contribution (pattern : BlockPattern) where
  candidate : Fin 3 → ℚ
  wall : ℚ
  sum_candidate : ∑ pairing, candidate pairing = wall

namespace Contribution

/-- A dangling wall block contributes no stable source occurrence on either
side of the W4 balance, independently of the resolution pattern used to paste
its singleton sheets. -/
def zero (pattern : BlockPattern) : Contribution pattern where
  candidate := fun _ ↦ 0
  wall := 0
  sum_candidate := by simp

/-- Package an nd2 block from its two equal old-branch contributions. -/
def ofNd2 (block : Nd2Block) (branchValue : Fin 4 → ℚ)
    (hEqual : branchValue block.first = branchValue block.second) :
    Contribution (.nd2 block) where
  candidate := Nd2Block.candidateContribution block (branchValue block.first)
  wall := branchValue block.first + branchValue block.second
  sum_candidate := Nd2Block.sum_candidateContribution_eq_branches block
    branchValue hEqual

/-- Package an nd3 block from its three old-branch contributions. -/
def ofNd3 (block : Nd3Block) (branchValue : Fin 4 → ℚ) :
    Contribution (.nd3 block) where
  candidate := Nd3Block.candidateContribution block branchValue
  wall := branchValue block.first + branchValue block.second +
    branchValue block.third
  sum_candidate := Nd3Block.sum_candidateContribution block branchValue

end Contribution

/-! ## Source-edge quotient receipts -/

/-- A block-local receipt for the two source identities `w4-nd2` and
`w4-nd3`, stated directly against the quotient sums extracted from actual
stable paths.  Constructing one requires only the source-edge classification:
which regrown edge appears for each target pairing, and which old branches it
replaces. -/
inductive QuotientReceipt
    (candidateQuotient : Fin 3 → ℚ) (wallQuotient : ℚ) :
    BlockPattern → Type where
  /-- An entirely dangling wall block has zero candidate and old-wall
  quotients. -/
  | zero (pattern : BlockPattern)
      (candidate_eq : ∀ pairing, 0 = candidateQuotient pairing)
      (wall_eq : 0 = wallQuotient) :
      QuotientReceipt candidateQuotient wallQuotient pattern
  /-- An nd2 block has two equal old-branch values.  The regrown edge occurs
  exactly when the pairing separates those branches. -/
  | nd2 (block : Nd2Block) (branchValue : Fin 4 → ℚ)
      (branch_eq : branchValue block.first = branchValue block.second)
      (candidate_eq : ∀ pairing,
        Nd2Block.candidateContribution block (branchValue block.first)
          pairing = candidateQuotient pairing)
      (wall_eq : branchValue block.first + branchValue block.second =
        wallQuotient) :
      QuotientReceipt candidateQuotient wallQuotient (.nd2 block)
  /-- An nd3 block contributes the branch isolated by the target pairing;
  its old value is the sum of its three distinct branches. -/
  | nd3 (block : Nd3Block) (branchValue : Fin 4 → ℚ)
      (candidate_eq : ∀ pairing,
        Nd3Block.candidateContribution block branchValue pairing =
          candidateQuotient pairing)
      (wall_eq : branchValue block.first + branchValue block.second +
        branchValue block.third = wallQuotient) :
      QuotientReceipt candidateQuotient wallQuotient (.nd3 block)

namespace QuotientReceipt

/-- Forget a source-edge quotient classification to the typed contribution
used by the finite W4 pairing identities. -/
def contribution
    {candidateQuotient : Fin 3 → ℚ} {wallQuotient : ℚ}
    {pattern : BlockPattern}
  (receipt : QuotientReceipt candidateQuotient wallQuotient pattern) :
    Contribution pattern := by
  cases receipt with
  | zero pattern _ _ => exact Contribution.zero pattern
  | nd2 block branchValue branch_eq _ _ =>
      exact Contribution.ofNd2 block branchValue branch_eq
  | nd3 block branchValue _ _ =>
      exact Contribution.ofNd3 block branchValue

/-- The typed candidate contribution is the classified literal quotient sum. -/
theorem contribution_candidate
    {candidateQuotient : Fin 3 → ℚ} {wallQuotient : ℚ}
    {pattern : BlockPattern}
    (receipt : QuotientReceipt candidateQuotient wallQuotient pattern)
    (pairing : Fin 3) :
    receipt.contribution.candidate pairing = candidateQuotient pairing := by
  cases receipt with
  | zero pattern candidate_eq wall_eq => exact candidate_eq pairing
  | nd2 block branchValue branch_eq candidate_eq wall_eq =>
      exact candidate_eq pairing
  | nd3 block branchValue candidate_eq wall_eq =>
      exact candidate_eq pairing

/-- The typed old-wall contribution is the classified old-branch quotient
sum. -/
theorem contribution_wall
    {candidateQuotient : Fin 3 → ℚ} {wallQuotient : ℚ}
    {pattern : BlockPattern}
    (receipt : QuotientReceipt candidateQuotient wallQuotient pattern) :
    receipt.contribution.wall = wallQuotient := by
  cases receipt with
  | zero pattern candidate_eq wall_eq => exact wall_eq
  | nd2 block branchValue branch_eq candidate_eq wall_eq =>
      exact wall_eq
  | nd3 block branchValue candidate_eq wall_eq =>
      exact wall_eq

/-- Every source-edge quotient receipt proves its block-local instance of
`w4-nd2` or `w4-nd3`. -/
theorem sum_candidateQuotient_eq_wallQuotient
    {candidateQuotient : Fin 3 → ℚ} {wallQuotient : ℚ}
    {pattern : BlockPattern}
    (receipt : QuotientReceipt candidateQuotient wallQuotient pattern) :
    ∑ pairing, candidateQuotient pairing = wallQuotient := by
  calc
    ∑ pairing, candidateQuotient pairing =
        ∑ pairing, receipt.contribution.candidate pairing := by
      apply Finset.sum_congr rfl
      intro pairing _
      exact (receipt.contribution_candidate pairing).symm
    _ = receipt.contribution.wall := receipt.contribution.sum_candidate
    _ = wallQuotient := receipt.contribution_wall

end QuotientReceipt

/-! ## Multiplicity-preserving stable-path term receipts -/

namespace Nd2Block

/-- Expected occurrence multiset in one candidate wall column for an nd2
block.  Same-side pairings have no stable new edge; opposite-side pairings
have exactly one term. -/
def candidateTerms (block : Nd2Block) (value : ℚ)
    (pairing : Fin 3) : Multiset ℚ :=
  if Pairing.labelRight pairing block.first =
      Pairing.labelRight pairing block.second then 0 else {value}

@[simp] theorem sum_candidateTerms (block : Nd2Block) (value : ℚ)
    (pairing : Fin 3) :
    (candidateTerms block value pairing).sum =
      candidateContribution block value pairing := by
  by_cases h : Pairing.labelRight pairing block.first =
      Pairing.labelRight pairing block.second <;>
    simp [candidateTerms, candidateContribution, h]

/-- Expected old-column occurrence multiset for an nd2 block. -/
def wallTerms (block : Nd2Block) (branchValue : Fin 4 → ℚ) : Multiset ℚ :=
  {branchValue block.first, branchValue block.second}

@[simp] theorem sum_wallTerms (block : Nd2Block)
    (branchValue : Fin 4 → ℚ) :
    (wallTerms block branchValue).sum =
      branchValue block.first + branchValue block.second := by
  simp [wallTerms]

end Nd2Block

namespace Nd3Block

/-- Expected occurrence multiset in one candidate wall column for an nd3
block: the single regrown edge carries the singleton old branch's term. -/
def candidateTerms (block : Nd3Block) (branchValue : Fin 4 → ℚ)
    (pairing : Fin 3) : Multiset ℚ :=
  {branchValue (block.singletonLabel pairing)}

@[simp] theorem sum_candidateTerms (block : Nd3Block)
    (branchValue : Fin 4 → ℚ) (pairing : Fin 3) :
    (candidateTerms block branchValue pairing).sum =
      candidateContribution block branchValue pairing := by
  simp [candidateTerms, candidateContribution]

/-- Expected old-column occurrence multiset for an nd3 block. -/
def wallTerms (block : Nd3Block) (branchValue : Fin 4 → ℚ) : Multiset ℚ :=
  {branchValue block.first, branchValue block.second,
    branchValue block.third}

@[simp] theorem sum_wallTerms (block : Nd3Block)
    (branchValue : Fin 4 → ℚ) :
    (wallTerms block branchValue).sum =
      branchValue block.first + branchValue block.second +
        branchValue block.third := by
  simp [wallTerms, add_assoc]

end Nd3Block

/-- Exact finite stable-path classification for one W4 wall block.  Its
inputs are occurrence multisets, so duplicated path occurrences are retained
and numerical cancellation cannot conceal a misclassification. -/
inductive TermReceipt
    (candidateTerms : Fin 3 → Multiset ℚ) (wallTerms : Multiset ℚ) :
    BlockPattern → Type where
  /-- An entirely dangling block has no stable source terms. -/
  | zero (pattern : BlockPattern)
      (candidate_terms : ∀ pairing, 0 = candidateTerms pairing)
      (wall_terms : 0 = wallTerms) :
      TermReceipt candidateTerms wallTerms pattern
  | nd2 (block : Nd2Block) (branchValue : Fin 4 → ℚ)
      (branch_eq : branchValue block.first = branchValue block.second)
      (candidate_terms : ∀ pairing,
        Nd2Block.candidateTerms block (branchValue block.first) pairing =
          candidateTerms pairing)
      (wall_terms : Nd2Block.wallTerms block branchValue = wallTerms) :
      TermReceipt candidateTerms wallTerms (.nd2 block)
  | nd3 (block : Nd3Block) (branchValue : Fin 4 → ℚ)
      (candidate_terms : ∀ pairing,
        Nd3Block.candidateTerms block branchValue pairing =
          candidateTerms pairing)
      (wall_terms : Nd3Block.wallTerms block branchValue = wallTerms) :
      TermReceipt candidateTerms wallTerms (.nd3 block)

universe u v

/-- A W4 source classification before rational weights are applied.  The
candidate occurrence type may be a sigma type tagging the three candidate
data.  The receipt records exact empty/singleton occurrence profiles and then
separately identifies the weight of each literal occurrence. -/
inductive OccurrenceReceipt
    {candidateOccurrence : Type u} {wallOccurrence : Type v}
    (candidateOccurrences : Fin 3 → Multiset candidateOccurrence)
    (wallOccurrences : Multiset wallOccurrence)
    (candidateWeight : candidateOccurrence → ℚ)
    (wallWeight : wallOccurrence → ℚ) : BlockPattern → Type (max u v) where
  /-- An entirely dangling block has no literal stable-path occurrences. -/
  | zero (pattern : BlockPattern)
      (candidate_occurrences : ∀ pairing, 0 = candidateOccurrences pairing)
      (wall_occurrences : 0 = wallOccurrences) :
      OccurrenceReceipt candidateOccurrences wallOccurrences candidateWeight
        wallWeight pattern
  | nd2 (block : Nd2Block)
      (newOccurrence : Fin 3 → candidateOccurrence)
      (oldOccurrence : Fin 4 → wallOccurrence)
      (branch_eq :
        wallWeight (oldOccurrence block.first) =
          wallWeight (oldOccurrence block.second))
      (candidate_occurrences : ∀ pairing,
        (if Pairing.labelRight pairing block.first =
            Pairing.labelRight pairing block.second then 0
          else {newOccurrence pairing}) = candidateOccurrences pairing)
      (candidate_weight : ∀ pairing,
        Pairing.labelRight pairing block.first ≠
          Pairing.labelRight pairing block.second →
        candidateWeight (newOccurrence pairing) =
          wallWeight (oldOccurrence block.first))
      (wall_occurrences :
        {oldOccurrence block.first, oldOccurrence block.second} =
          wallOccurrences) :
      OccurrenceReceipt candidateOccurrences wallOccurrences candidateWeight
        wallWeight (.nd2 block)
  | nd3 (block : Nd3Block)
      (newOccurrence : Fin 3 → candidateOccurrence)
      (oldOccurrence : Fin 4 → wallOccurrence)
      (candidate_occurrences : ∀ pairing,
        {newOccurrence pairing} = candidateOccurrences pairing)
      (candidate_weight : ∀ pairing,
        candidateWeight (newOccurrence pairing) =
          wallWeight (oldOccurrence (block.singletonLabel pairing)))
      (wall_occurrences :
        {oldOccurrence block.first, oldOccurrence block.second,
            oldOccurrence block.third} = wallOccurrences) :
      OccurrenceReceipt candidateOccurrences wallOccurrences candidateWeight
        wallWeight (.nd3 block)

namespace TermReceipt

/-- Summing an exact occurrence receipt gives the numerical quotient receipt
used by the determinant theorem. -/
def toQuotientReceipt
    {candidateTerms : Fin 3 → Multiset ℚ} {wallTerms : Multiset ℚ}
    {pattern : BlockPattern}
  (receipt : TermReceipt candidateTerms wallTerms pattern) :
    QuotientReceipt (fun pairing ↦ (candidateTerms pairing).sum)
      wallTerms.sum pattern := by
  cases receipt with
  | zero pattern candidate_terms wall_terms =>
      exact QuotientReceipt.zero pattern
        (fun pairing ↦ by rw [← candidate_terms pairing]; simp)
        (by rw [← wall_terms]; simp)
  | nd2 block branchValue branch_eq candidate_terms wall_terms =>
      exact QuotientReceipt.nd2 block branchValue branch_eq
        (fun pairing ↦ by
          rw [← candidate_terms pairing]
          exact (Nd2Block.sum_candidateTerms block (branchValue block.first)
            pairing).symm)
        (by
          rw [← wall_terms]
          exact (Nd2Block.sum_wallTerms block branchValue).symm)
  | nd3 block branchValue candidate_terms wall_terms =>
      exact QuotientReceipt.nd3 block branchValue
        (fun pairing ↦ by
          rw [← candidate_terms pairing]
          exact (Nd3Block.sum_candidateTerms block branchValue pairing).symm)
        (by
          rw [← wall_terms]
          exact (Nd3Block.sum_wallTerms block branchValue).symm)

end TermReceipt

namespace OccurrenceReceipt

/-- Weighting an exact occurrence-level W4 classification produces the
multiplicity-preserving rational term receipt consumed by the determinant
identity. -/
def toTermReceipt
    {candidateOccurrence : Type u} {wallOccurrence : Type v}
    {candidateOccurrences : Fin 3 → Multiset candidateOccurrence}
    {wallOccurrences : Multiset wallOccurrence}
    {candidateWeight : candidateOccurrence → ℚ}
    {wallWeight : wallOccurrence → ℚ}
    {pattern : BlockPattern}
  (receipt : OccurrenceReceipt candidateOccurrences wallOccurrences
      candidateWeight wallWeight pattern) :
    TermReceipt
      (fun pairing ↦ (candidateOccurrences pairing).map candidateWeight)
      (wallOccurrences.map wallWeight) pattern := by
  cases receipt with
  | zero pattern candidate_occurrences wall_occurrences =>
      exact TermReceipt.zero pattern
        (fun pairing ↦ by rw [← candidate_occurrences pairing]; simp)
        (by rw [← wall_occurrences]; simp)
  | nd2 block newOccurrence oldOccurrence branch_eq candidate_occurrences
      candidate_weight wall_occurrences =>
      apply TermReceipt.nd2 block
        (fun branch ↦ wallWeight (oldOccurrence branch)) branch_eq
      · intro pairing
        rw [← candidate_occurrences pairing]
        by_cases h : Pairing.labelRight pairing block.first =
            Pairing.labelRight pairing block.second
        · simp [Nd2Block.candidateTerms, h]
        · simp [Nd2Block.candidateTerms, h, candidate_weight pairing h]
      · rw [← wall_occurrences]
        simp [Nd2Block.wallTerms]
  | nd3 block newOccurrence oldOccurrence candidate_occurrences
      candidate_weight wall_occurrences =>
      apply TermReceipt.nd3 block
        (fun branch ↦ wallWeight (oldOccurrence branch))
      · intro pairing
        rw [← candidate_occurrences pairing]
        simp [Nd3Block.candidateTerms, candidate_weight pairing]
      · rw [← wall_occurrences]
        simp [Nd3Block.wallTerms]

end OccurrenceReceipt

/-- A classified contribution for every source wall block reduces the raw
Equation (1) determinant sum to the determinant decomposition and the old
wall-column relation. -/
theorem sum_eq_zero_of_contributions
    {block : Type*} [Fintype block]
    (pattern : block → BlockPattern)
    (contribution : ∀ sourceBlock, Contribution (pattern sourceBlock))
    (candidateValue : Fin 3 → ℚ)
    (hcandidate : ∀ pairing,
      candidateValue pairing =
        ∑ sourceBlock, (contribution sourceBlock).candidate pairing)
    (hwall : ∑ sourceBlock, (contribution sourceBlock).wall = 0) :
    ∑ pairing, candidateValue pairing = 0 :=
  w4_sum_eq_zero_of_block_contributions candidateValue
    (fun sourceBlock pairing ↦
      (contribution sourceBlock).candidate pairing)
    (fun sourceBlock ↦ (contribution sourceBlock).wall)
    hcandidate (fun sourceBlock ↦
      (contribution sourceBlock).sum_candidate) hwall

/-- The same classified contributions give the positive unit-weight balance
used by the cone-exit argument. -/
theorem balance_of_contributions
    {block : Type*} [Fintype block]
    (pattern : block → BlockPattern)
    (contribution : ∀ sourceBlock, Contribution (pattern sourceBlock))
    (candidateValue : Fin 3 → ℚ)
    (hcandidate : ∀ pairing,
      candidateValue pairing =
        ∑ sourceBlock, (contribution sourceBlock).candidate pairing)
    (hwall : ∑ sourceBlock, (contribution sourceBlock).wall = 0) :
    PositiveBalance ![1, 1, 1] candidateValue :=
  balance_w4 (sum_eq_zero_of_contributions pattern contribution
    candidateValue hcandidate hwall)

/-- For actual candidate matrices, common off-wall columns make the candidate
determinant decomposition automatic.  The remaining local premise identifies
each typed nd2/nd3 contribution with the corresponding fiber of wall-column
entries times common cofactors. -/
theorem sum_det_eq_zero_of_matrix_contributions
    {coordinate block : Type*}
    [Fintype coordinate] [DecidableEq coordinate] [Fintype block]
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
    ∑ pairing, (matrix pairing).det = 0 := by
  apply sum_eq_zero_of_contributions pattern contribution
    (fun pairing ↦ (matrix pairing).det) _ hwall
  intro pairing
  calc
    (matrix pairing).det =
        ∑ sourceBlock,
          wallBlockContribution (matrix 0) (matrix pairing) wallColumn
            rowBlock sourceBlock :=
      det_eq_sum_wallBlockContribution rowBlock (hAgree pairing 0)
    _ = ∑ sourceBlock,
        (contribution sourceBlock).candidate pairing := by
      apply Finset.sum_congr rfl
      intro sourceBlock _
      exact (hcontribution sourceBlock pairing).symm

/-- The matrix-level W4 contribution data give the positive unit-weight
determinant balance. -/
theorem balance_of_matrix_contributions
    {coordinate block : Type*}
    [Fintype coordinate] [DecidableEq coordinate] [Fintype block]
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
    PositiveBalance ![1, 1, 1]
      (fun pairing ↦ (matrix pairing).det) :=
  balance_w4 (sum_det_eq_zero_of_matrix_contributions matrix wallColumn
    rowBlock hAgree pattern contribution hcontribution hwall)

/-- If the typed wall value of each source block is its contribution from a
finite set of old target columns, the old wall sum also follows automatically
from the adjugate identity.  The W4 determinant balance is then reduced to
block-local entry identifications only. -/
theorem sum_det_eq_zero_of_oldColumn_contributions
    {coordinate block : Type*}
    [Fintype coordinate] [DecidableEq coordinate] [Fintype block]
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
    ∑ pairing, (matrix pairing).det = 0 := by
  apply sum_det_eq_zero_of_matrix_contributions matrix wallColumn rowBlock
    hAgree pattern contribution hcandidate
  calc
    ∑ sourceBlock, (contribution sourceBlock).wall =
        ∑ sourceBlock,
          oldBlockContribution (matrix 0) wallColumn rowBlock oldColumns
            sourceBlock := by
              apply Finset.sum_congr rfl
              intro sourceBlock _
              exact hwall sourceBlock
    _ = 0 := sum_oldBlockContribution_eq_zero
      (matrix 0) wallColumn rowBlock oldColumns hOld

/-- Matrix and old-column contribution identifications give the positive W4
balance without any separate global determinant equation. -/
theorem balance_of_oldColumn_contributions
    {coordinate block : Type*}
    [Fintype coordinate] [DecidableEq coordinate] [Fintype block]
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
    PositiveBalance ![1, 1, 1]
      (fun pairing ↦ (matrix pairing).det) :=
  balance_w4 (sum_det_eq_zero_of_oldColumn_contributions matrix wallColumn
    rowBlock oldColumns hOld hAgree pattern contribution hcandidate hwall)

/-- The main W4 determinant theorem, with entry-level decomposition.  A
stable-path row may contain summands from several source wall blocks.  Once
the candidate wall entries and old-column entries are decomposed blockwise,
the typed nd2/nd3 identities, cofactor expansion, and both global sums close
Equation (1). -/
theorem sum_det_eq_zero_of_entrySummand_contributions
    {coordinate block : Type*}
    [Fintype coordinate] [DecidableEq coordinate] [Fintype block]
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
    ∑ pairing, (matrix pairing).det = 0 := by
  apply sum_eq_zero_of_contributions pattern contribution
    (fun pairing ↦ (matrix pairing).det)
  · intro pairing
    calc
      (matrix pairing).det = ∑ sourceBlock,
          wallEntrySummandContribution (matrix 0) wallColumn
            (candidateEntrySummand pairing) sourceBlock :=
        det_eq_sum_wallEntrySummandContribution
          (candidateEntrySummand pairing) (hCandidateEntry pairing)
          (hAgree pairing 0)
      _ = ∑ sourceBlock,
          (contribution sourceBlock).candidate pairing := by
            apply Finset.sum_congr rfl
            intro sourceBlock _
            exact (hcandidate sourceBlock pairing).symm
  · calc
      ∑ sourceBlock, (contribution sourceBlock).wall =
          ∑ sourceBlock,
            oldEntrySummandContribution (matrix 0) wallColumn oldColumns
              oldEntrySummand sourceBlock := by
                apply Finset.sum_congr rfl
                intro sourceBlock _
                exact hwall sourceBlock
      _ = 0 := sum_oldEntrySummandContribution_eq_zero
        (matrix 0) wallColumn oldColumns oldEntrySummand hOldEntry hOld

/-- Source-block summand of an actual presented length-matrix entry.  It is
the sum of `1 / m(e)` over the source edges in the displayed stable path that
carry the chosen block label and target column. -/
noncomputable def lengthMatrixEntrySummand
    {target : CFGraph} {degree : ℕ}
    {data : GluingDatum target degree}
    {coordinate block : Type*}
    [Fintype coordinate] [DecidableEq coordinate] [Fintype block]
    (presentation : data.LengthMatrixPresentation coordinate)
    (edgeBlock : data.SourceEdge → block) :
    block → coordinate → coordinate → ℚ :=
  fun sourceBlock column sourceRow ↦
    GluingDatum.LengthMatrixPresentation.blockCoefficient presentation
      edgeBlock sourceBlock sourceRow column

/-- In a presented length matrix, the abstract cofactor-weighted entry
summand is the literal nested sum over source-edge occurrences in the stable
paths. -/
theorem wallEntrySummandContribution_lengthMatrix_eq
    {target : CFGraph} {degree : ℕ}
    {data : GluingDatum target degree}
    {coordinate block : Type*}
    [Fintype coordinate] [DecidableEq coordinate] [Fintype block]
    (reference : Matrix coordinate coordinate ℚ) (wallColumn : coordinate)
    (presentation : data.LengthMatrixPresentation coordinate)
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (column : coordinate) :
    wallEntrySummandContribution reference wallColumn
        (fun blockLabel sourceRow ↦
          lengthMatrixEntrySummand presentation edgeBlock blockLabel column
            sourceRow)
        sourceBlock =
      GluingDatum.LengthMatrixPresentation.blockCofactorContribution
        presentation edgeBlock sourceBlock column
        (fun sourceRow ↦ reference.adjugate wallColumn sourceRow) := by
  unfold wallEntrySummandContribution lengthMatrixEntrySummand
  exact
    GluingDatum.LengthMatrixPresentation.sum_blockCoefficient_mul_eq_blockCofactorContribution
      presentation edgeBlock sourceBlock column
        (fun sourceRow ↦ reference.adjugate wallColumn sourceRow)

/-- The analogous identification for a finite family of old target columns. -/
theorem oldEntrySummandContribution_lengthMatrix_eq
    {target : CFGraph} {degree : ℕ}
    {data : GluingDatum target degree}
    {coordinate block : Type*}
    [Fintype coordinate] [DecidableEq coordinate] [Fintype block]
    (reference : Matrix coordinate coordinate ℚ) (wallColumn : coordinate)
    (presentation : data.LengthMatrixPresentation coordinate)
    (edgeBlock : data.SourceEdge → block) (sourceBlock : block)
    (oldColumns : Finset coordinate) :
    oldEntrySummandContribution reference wallColumn oldColumns
        (lengthMatrixEntrySummand presentation edgeBlock) sourceBlock =
      ∑ column ∈ oldColumns,
        GluingDatum.LengthMatrixPresentation.blockCofactorContribution
          presentation edgeBlock sourceBlock column
          (fun sourceRow ↦ reference.adjugate wallColumn sourceRow) := by
  classical
  unfold oldEntrySummandContribution lengthMatrixEntrySummand
  apply Finset.sum_congr rfl
  intro column _
  exact
    GluingDatum.LengthMatrixPresentation.sum_blockCoefficient_mul_eq_blockCofactorContribution
      presentation edgeBlock sourceBlock column
        (fun sourceRow ↦ reference.adjugate wallColumn sourceRow)

/-- Length-matrix specialization of the main W4 determinant theorem.
The decomposition of every matrix entry into source-edge block summands is
automatic from the presented stable paths.  Only the local
cofactor-weighted identifications with the typed nd2/nd3 branch values remain. -/
theorem sum_det_eq_zero_of_lengthMatrixPresentations
    {degree : ℕ} {candidateTarget : Fin 3 → CFGraph}
    (data : ∀ pairing, GluingDatum (candidateTarget pairing) degree)
    {coordinate block : Type*}
    [Fintype coordinate] [DecidableEq coordinate] [Fintype block]
    (presentation : ∀ pairing,
      (data pairing).LengthMatrixPresentation coordinate)
    (edgeBlock : ∀ pairing, (data pairing).SourceEdge → block)
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
    ∑ pairing,
      (GluingDatum.LengthMatrixPresentation.matrix
        (presentation pairing)).det = 0 := by
  apply sum_det_eq_zero_of_entrySummand_contributions
    (fun pairing ↦
      GluingDatum.LengthMatrixPresentation.matrix (presentation pairing))
    wallColumn oldColumns hOld hAgree pattern contribution
    (fun pairing sourceBlock sourceRow ↦
      lengthMatrixEntrySummand (presentation pairing) (edgeBlock pairing)
        sourceBlock wallColumn sourceRow) ?_ ?_
    (lengthMatrixEntrySummand (presentation 0) (edgeBlock 0)) ?_ ?_
  · intro pairing sourceRow
    exact GluingDatum.LengthMatrixPresentation.matrix_apply_eq_sum_blockCoefficient
      (presentation pairing) (edgeBlock pairing) sourceRow wallColumn
  · intro sourceBlock pairing
    rw [wallEntrySummandContribution_lengthMatrix_eq]
    rw [GluingDatum.LengthMatrixPresentation.blockCofactorContribution_eq_quotient]
    exact hcandidate sourceBlock pairing
  · intro column _ sourceRow
    exact GluingDatum.LengthMatrixPresentation.matrix_apply_eq_sum_blockCoefficient
      (presentation 0) (edgeBlock 0) sourceRow column
  · intro sourceBlock
    rw [oldEntrySummandContribution_lengthMatrix_eq]
    simp_rw [GluingDatum.LengthMatrixPresentation.blockCofactorContribution_eq_quotient]
    exact hwall sourceBlock

/-- The main source-classification form of Equation (1).  A receipt for
each wall block identifies the actual source-edge quotient sums with the nd2
or nd3 branch profile.  The finite pairing identities, length-matrix
expansion, cofactor algebra, and old-column cancellation are then automatic. -/
theorem sum_det_eq_zero_of_lengthMatrixQuotientReceipts
    {degree : ℕ} {candidateTarget : Fin 3 → CFGraph}
    (data : ∀ pairing, GluingDatum (candidateTarget pairing) degree)
    {coordinate block : Type*}
    [Fintype coordinate] [DecidableEq coordinate] [Fintype block]
    (presentation : ∀ pairing,
      (data pairing).LengthMatrixPresentation coordinate)
    (edgeBlock : ∀ pairing, (data pairing).SourceEdge → block)
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
    ∑ pairing,
      (GluingDatum.LengthMatrixPresentation.matrix
        (presentation pairing)).det = 0 := by
  apply sum_det_eq_zero_of_lengthMatrixPresentations data presentation
    edgeBlock wallColumn oldColumns hOld hAgree pattern
    (fun sourceBlock ↦ (receipt sourceBlock).contribution)
  · intro sourceBlock pairing
    exact (receipt sourceBlock).contribution_candidate pairing
  · intro sourceBlock
    exact (receipt sourceBlock).contribution_wall

/-- Strongest finite-classification form of Equation (1).  Callers classify
the multiplicity-preserving multisets of stable-path terms in the three new
wall columns and the old incident columns.  Summation produces the quotient
receipts, after which all determinant algebra is automatic. -/
theorem sum_det_eq_zero_of_lengthMatrixTermReceipts
    {degree : ℕ} {candidateTarget : Fin 3 → CFGraph}
    (data : ∀ pairing, GluingDatum (candidateTarget pairing) degree)
    {coordinate block : Type*}
    [Fintype coordinate] [DecidableEq coordinate] [Fintype block]
    (presentation : ∀ pairing,
      (data pairing).LengthMatrixPresentation coordinate)
    (edgeBlock : ∀ pairing, (data pairing).SourceEdge → block)
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
    ∑ pairing,
      (GluingDatum.LengthMatrixPresentation.matrix
        (presentation pairing)).det = 0 := by
  apply sum_det_eq_zero_of_lengthMatrixQuotientReceipts data presentation
    edgeBlock wallColumn oldColumns hOld hAgree pattern
  intro sourceBlock
  have hCandidate :
      (fun pairing ↦
        GluingDatum.LengthMatrixPresentation.blockQuotientContribution
          (presentation pairing) (edgeBlock pairing) sourceBlock wallColumn
          (fun sourceRow ↦
            (GluingDatum.LengthMatrixPresentation.matrix
              (presentation 0)).adjugate wallColumn sourceRow)) =
      (fun pairing ↦
        (GluingDatum.LengthMatrixPresentation.blockColumnTerms
          (presentation pairing) (edgeBlock pairing) sourceBlock wallColumn
          (fun sourceRow ↦
            (GluingDatum.LengthMatrixPresentation.matrix
              (presentation 0)).adjugate wallColumn sourceRow)).sum) := by
    funext pairing
    exact
      GluingDatum.LengthMatrixPresentation.blockQuotientContribution_eq_terms_sum
        (presentation pairing) (edgeBlock pairing) sourceBlock wallColumn _
  have hWall :
      (∑ column ∈ oldColumns,
        GluingDatum.LengthMatrixPresentation.blockQuotientContribution
          (presentation 0) (edgeBlock 0) sourceBlock column
          (fun sourceRow ↦
            (GluingDatum.LengthMatrixPresentation.matrix
              (presentation 0)).adjugate wallColumn sourceRow)) =
      (GluingDatum.LengthMatrixPresentation.blockColumnsTerms
        (presentation 0) (edgeBlock 0) sourceBlock oldColumns
        (fun sourceRow ↦
          (GluingDatum.LengthMatrixPresentation.matrix
            (presentation 0)).adjugate wallColumn sourceRow)).sum :=
    GluingDatum.LengthMatrixPresentation.sum_blockQuotientContribution_eq_terms_sum
      (presentation 0) (edgeBlock 0) sourceBlock oldColumns _
  rw [hCandidate, hWall]
  exact (receipt sourceBlock).toQuotientReceipt

end DraismaVargas.LocalCases.W4DeterminantContributions
