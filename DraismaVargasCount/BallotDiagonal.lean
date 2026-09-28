import DraismaVargasCount.BallotValency
import DraismaVargasCount.Multiplicity

/-!
# The diagonal of the ballot length matrix, at every slope sequence

**Source.**  Vargas, Part II (arXiv:2609.09109), the step of the proof of the main theorem
(`thm`) that computes the multiplicity of a morphism over the caterpillar of loops.  This
module computes the diagonal of the length matrix of every ballot member; the multiplicity
itself is computed from it in `Count.BallotMultiplicity`.

By `Count.BallotValency`, `ballotLabelling m s` is a `StableLengthMatrixLabelling` and
`ballotDiagonalPattern m s` a `SeedDeterminant.DiagonalPattern` for every `m`
and every `s : Slopes (2 * (m + 1))`.  On a diagonal pattern
`Count.signedMult_of_diagonalPattern` reduces the multiplicity to the
**numerators of the diagonal entries**, so this module computes that diagonal.

## The diagonal, for every `m` and every `s`

`bMatrix_diag` below is the entry-by-entry statement.  Its three cases, and
where each comes from:

| row `i` | survivors | source edges | entry | numerator |
|---|---|---|---|---|
| leaf (`i % 3 = 0` or `i = 6m+2`) | the bridge pair `{0, cum}` over a **discrete** occurrence partition | two, each of index `1` | `1 + 1 = 2` | `2` |
| stem (`i % 3 = 2`, `i ≠ 6m+2`) | the bridge pair, one block | one, of index `2` | `1/2` | `1` |
| spine (`i % 3 = 1`) | the block `SpineMem s ((i+2)/3)`, of size `s_i` | one, of index `s_i` | `1 / s_i` | `1` |

The survivor census is `BallotValency.bOccurrence_isDangling_iff`; the block sizes are
`BallotDatum.card_edgePred_spine` / `card_edgePred_stem` / `card_edgePred_leaf`, the last of
which is the leaf partition being discrete; that the two leaf flags are nevertheless distinct
source edges is `BallotFullDimensional.bLoopFirst_ne_bLoopSecond` (which is where
`ballotEdgePart_leaf` is used).

`Slopes.one_le_slope` is unconditional, so `1 / s_i` has numerator `1`
**whatever the slope is** -- that is what makes `bNum_matrix_diag` independent
of `s`, and hence `bProd_num_matrix_diag` equal to `2 ^ (2m+2)` for every slope
sequence.  Note `2m + 2 = leafCount (catTree m)`
(`Caterpillar.leafCount_catTree`), which is what cancels downstream.

## Two remarks on the entries

* **The spine entry is `1 / s_i` in general.**  It is `1` on a slope-one spine edge only
  because `1/1 = 1`, as on the zig-zag.  At `Slopes.six = [2,3,4,3,2]` the spine entries
  include `1/3` and `1/4`.  There is no numerical consequence: the numerator is `1` either
  way.
* **The leaf rows depend on pairs, not only on counts.**  The general slope costs
  nothing on the spine and the stems, where only the *count* of surviving
  source edges (one) matters and the block size passes through as an index.
  But the leaf rows contribute `2` precisely because the bridge pair is a
  **pair** sitting over a **discrete** partition, and it is that `2 ^ (2m+2)`
  which cancels `2 ^ leafCount`.  That structure is `s`-uniform, so it
  transfers to every slope sequence -- but the cancellation comes from pairs, not
  from blocks.

## What is proved

* `mem_bPath_iff` -- a source occurrence is displayed by the stable row `i`
  exactly when it survives pruning and lies over `occ m i`.
* `bMatrix_diag_eq_sum` -- the diagonal entry is the sum of the reciprocal
  dilation indices of the surviving occurrences over its own target
  occurrence.
* `toFinset_bPath_leaf`, `toFinset_bPath_notLeaf` -- which source edges those
  are: the two loop flags over a leaf edge, the spine-sheet block otherwise.
* `bSourceEdgeIndex_bLoopFirst`, `bSourceEdgeIndex_bLoopSecond`,
  `bSourceEdgeIndex_main_spine`, `bSourceEdgeIndex_main_stem` -- their indices.
* `bMatrix_diag`, `bNum_matrix_diag`, `bProd_num_matrix_diag` -- the diagonal,
  its numerators, and their product.

## What is not proved here

* **No multiplicity.**  `signedMult`, `absMult` and `fdAbsMult` do not occur
  below; they are `Count.BallotMultiplicity`.
* **No `FibreMember`, no `BallotFamily`, no count.**  `catCore`,
  `GeometricFibre` and `openOddCount` do not occur below.
  `Count.CaterpillarBallot.BallotFamily` is inhabited elsewhere, at every `m`
  and every positive request, by `BallotCoreIdentification.ballotFamily`, but
  no such member is built in this file.
* **No off-diagonal entry is computed.**  Only that they vanish, which is
  `BallotValency.ballotDiagonalPattern` and is not reproved here.
* **No genericity hypothesis is used or supplied.**  No statement below
  mentions a length; the matrix is the combinatorial one attached to the
  labelling.
-/

namespace DraismaVargas.Count.BallotDiagonal

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.CaterpillarPruning
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count
open DraismaVargas.Count.BallotDatum
open DraismaVargas.Count.BallotFullDimensional
open DraismaVargas.Count.BallotSpineCensus
open DraismaVargas.Count.BallotValency

variable {m : ℕ}

/-! ## 1.  The displayed occurrences of a stable row -/

theorem bPath_nodup (s : Slopes (2 * (m + 1))) (i : Fin (6 * m + 3)) :
    ((ballotLabelling m s).path i).Nodup := by
  classical
  unfold StableLengthMatrixLabelling.path
  exact List.Nodup.filter _ (Finset.nodup_toList _)

/-- **The stable row `i` displays exactly the surviving occurrences over the
target occurrence `occ m i`.**  This is `Caterpillar.mem_path_iff_cat` for the
ballot family; it holds because `ballotLabelling` is
`BallotFullDimensional.rowLabelling`, whose row map is "the target occurrence you lie
over". -/
theorem mem_bPath_iff (s : Slopes (2 * (m + 1))) (i : Fin (6 * m + 3))
    (edge : (ballotDatum m s).SourceEdge) :
    edge ∈ (ballotLabelling m s).path i ↔
      ¬ IsDangling (ballotDatum m s) edge ∧ edge.1.1 = occ m i := by
  rw [StableLengthMatrixLabelling.mem_path_iff]
  constructor
  · rintro ⟨hSurvives, hRow⟩
    refine ⟨hSurvives, ?_⟩
    have hsymm : (catEdgeEquiv m).symm edge.1.1 = i := hRow
    rw [← hsymm]
    exact ((catEdgeEquiv m).apply_symm_apply _).symm
  · rintro ⟨hSurvives, hTarget⟩
    refine ⟨hSurvives, ?_⟩
    show (catEdgeEquiv m).symm edge.1.1 = i
    rw [hTarget]
    exact (catEdgeEquiv m).symm_apply_apply i

theorem bCoefficient (s : Slopes (2 * (m + 1))) (i : Fin (6 * m + 3))
    (edge : (ballotDatum m s).SourceEdge) (hTarget : edge.1.1 = occ m i) :
    coefficient (ballotLabelling m s).presentation edge i =
      1 / ((ballotDatum m s).sourceEdgeIndex edge : ℚ) := by
  classical
  unfold coefficient
  rw [if_pos]
  show i = (catEdgeEquiv m).symm edge.1.1
  rw [hTarget]
  exact ((catEdgeEquiv m).symm_apply_apply i).symm

/-- **The diagonal entry is the sum of the reciprocal dilation indices of the
surviving occurrences above its own target occurrence.** -/
theorem bMatrix_diag_eq_sum (s : Slopes (2 * (m + 1))) (i : Fin (6 * m + 3)) :
    matrix (ballotLabelling m s).presentation i i =
      ∑ edge ∈ ((ballotLabelling m s).path i).toFinset,
        1 / ((ballotDatum m s).sourceEdgeIndex edge : ℚ) := by
  classical
  have hsum := List.sum_toFinset
    (fun edge ↦ (1 : ℚ) / ((ballotDatum m s).sourceEdgeIndex edge : ℚ))
    (bPath_nodup s i)
  rw [hsum]
  show ((ballotLabelling m s).path i |>.map
    (fun edge ↦ coefficient (ballotLabelling m s).presentation edge i)).sum = _
  congr 1
  refine List.map_congr_left fun edge hEdge ↦ ?_
  exact bCoefficient s i edge ((mem_bPath_iff s i edge).mp hEdge).2

/-! ## 2.  Which occurrences survive over which target occurrence -/

/-- **Off the leaf edges the surviving set is the occurrence-partition block.**
Over a spine edge both `bSurvives` and `EdgePred` are the spine block
`SpineMem s ((i+2)/3)`; over a stem both are the bridge pair, the two spellings
of its index agreeing by `lolli (i+1) = (i+4)/3`. -/
theorem bEdgePred_of_bSurvives (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hNotLeaf : ¬ IsLeafEdge m i) {k : ℕ} (h : bSurvives m s i.val k) :
    EdgePred m s i.val k := by
  have hi := i.isLt
  unfold IsLeafEdge at hNotLeaf
  rw [not_or] at hNotLeaf
  by_cases hspine : i.val % 3 = 1
  · rw [bSurvives_spine s hspine] at h
    rw [edgePred_spine s hspine]
    exact h
  · rw [bSurvives_of_not_spine s hspine] at h
    rw [edgePred_stem s (by omega) hNotLeaf.2]
    rwa [show lolli (i.val + 1) = (i.val + 4) / 3 from by unfold lolli; omega] at h

/-- **Off the leaf edges every survivor is the spine-sheet block.** -/
theorem bSourceEdge_eq_main (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hNotLeaf : ¬ IsLeafEdge m i) (σ : Fin (m + 2))
    (hSurvives : ¬ IsDangling (ballotDatum m s)
      ((ballotDatum m s).sourceEdge (occ m i) σ)) :
    (ballotDatum m s).sourceEdge (occ m i) σ =
      (ballotDatum m s).sourceEdge (occ m i) 0 := by
  have hb : bSurvives m s i.val σ.val := by
    by_contra hcon
    exact hSurvives ((bOccurrence_isDangling_iff s i σ).mpr hcon)
  have hE : EdgePred m s i.val σ.val := bEdgePred_of_bSurvives s hNotLeaf hb
  apply Subtype.ext
  apply Prod.ext
  · rfl
  change ((ballotDatum m s).edgePartition (occ m i)).Rel σ 0
  rw [ballotDatum_edgePart_occ, catStar_rel_iff _ (edgePred_zero s _)]
  exact Or.inl ⟨hE, by simp⟩

theorem toFinset_bPath_notLeaf (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hNotLeaf : ¬ IsLeafEdge m i) :
    ((ballotLabelling m s).path i).toFinset =
      ({(ballotDatum m s).sourceEdge (occ m i) 0} :
        Finset (ballotDatum m s).SourceEdge) := by
  classical
  ext edge
  rw [List.mem_toFinset, mem_bPath_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hSurvives, hTarget⟩
    have hself : (ballotDatum m s).sourceEdge (occ m i) edge.1.2 = edge := by
      have hs := GluingDatum.sourceEdge_self (ballotDatum m s) edge
      rw [hTarget] at hs
      exact hs
    rw [← hself]
    exact bSourceEdge_eq_main s hNotLeaf edge.1.2 (by rw [hself]; exact hSurvives)
  · rintro rfl
    exact ⟨ballot_mainSurvives s (occ m i), rfl⟩

theorem toFinset_bPath_leaf (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hLeaf : IsLeafEdge m i) :
    ((ballotLabelling m s).path i).toFinset =
      ({bLoopFirst m s i, bLoopSecond m s i} :
        Finset (ballotDatum m s).SourceEdge) := by
  classical
  ext edge
  rw [List.mem_toFinset, mem_bPath_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hSurvives, hTarget⟩
    have hself : (ballotDatum m s).sourceEdge (occ m i) edge.1.2 = edge := by
      have hs := GluingDatum.sourceEdge_self (ballotDatum m s) edge
      rw [hTarget] at hs
      exact hs
    have hDang : ¬ (edge.1.2.val ≠ 0 ∧ edge.1.2.val ≠ s.cum (lolli (i.val + 1))) := by
      intro hcon
      exact hSurvives
        (hself ▸ (bLeafOccurrence_isDangling_iff s hLeaf edge.1.2).mpr hcon)
    rw [not_and_or, not_not, not_not] at hDang
    rcases hDang with h | h
    · exact Or.inl (by rw [← hself, show edge.1.2 = 0 from Fin.ext h]; rfl)
    · refine Or.inr ?_
      rw [← hself, show edge.1.2 = cumSheet m s (i.val + 1) from
        Fin.ext (by rw [cumSheet_val]; exact h)]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨bLoopFirst_survives s hLeaf, rfl⟩
    · exact ⟨bLoopSecond_survives s hLeaf, rfl⟩

/-! ## 3.  The dilation indices -/

/-- Over a spine edge the surviving block has size `s_i`. -/
theorem bSourceEdgeIndex_main_spine (s : Slopes (2 * (m + 1)))
    {i : Fin (6 * m + 3)} (hspine : i.val % 3 = 1) :
    (ballotDatum m s).sourceEdgeIndex ((ballotDatum m s).sourceEdge (occ m i) 0)
      = s.slope ((i.val + 2) / 3) := by
  rw [GluingDatum.sourceEdgeIndex_sourceEdge, ballotDatum_edgePart_occ,
    catStar_blockCard_of_mem _ (edgePred_zero s _)
      (by simp),
    card_edgePred_spine s hspine]

/-- Over a stem the surviving block is the bridge pair, of size `2`. -/
theorem bSourceEdgeIndex_main_stem (s : Slopes (2 * (m + 1)))
    {i : Fin (6 * m + 3)} (hLeaf : ¬ IsLeafEdge m i) (hspine : i.val % 3 ≠ 1) :
    (ballotDatum m s).sourceEdgeIndex ((ballotDatum m s).sourceEdge (occ m i) 0)
      = 2 := by
  have hi := i.isLt
  unfold IsLeafEdge at hLeaf
  rw [not_or] at hLeaf
  rw [GluingDatum.sourceEdgeIndex_sourceEdge, ballotDatum_edgePart_occ,
    catStar_blockCard_of_mem _ (edgePred_zero s _)
      (by simp),
    card_edgePred_stem s (by omega) hLeaf.2]

/-- Over a leaf edge the occurrence partition is discrete, so the spine flag is
a block of size `1`. -/
theorem bSourceEdgeIndex_bLoopFirst (s : Slopes (2 * (m + 1)))
    {i : Fin (6 * m + 3)} (hLeaf : IsLeafEdge m i) :
    (ballotDatum m s).sourceEdgeIndex (bLoopFirst m s i) = 1 := by
  rw [bLoopFirst, GluingDatum.sourceEdgeIndex_sourceEdge, ballotDatum_edgePart_occ,
    catStar_blockCard_of_mem _ (edgePred_zero s _)
      (by simp),
    card_edgePred_leaf s hLeaf]

/-- The counter flag over a leaf edge is a block of size `1` too: its sheet is
not the spine sheet, and the leaf partition is discrete. -/
theorem bSourceEdgeIndex_bLoopSecond (s : Slopes (2 * (m + 1)))
    {i : Fin (6 * m + 3)} (hLeaf : IsLeafEdge m i) :
    (ballotDatum m s).sourceEdgeIndex (bLoopSecond m s i) = 1 := by
  have hcum : ¬ EdgePred m s i.val (cumSheet m s (i.val + 1)).val := by
    rw [cumSheet_val, edgePred_leaf s hLeaf]
    have := Slopes.one_le_cum s (lolli (i.val + 1))
    omega
  rw [bLoopSecond, GluingDatum.sourceEdgeIndex_sourceEdge, ballotDatum_edgePart_occ,
    catStar_blockCard_of_not _ (edgePred_zero s _) hcum]

/-! ## 4.  The diagonal, and the product of its numerators -/

/-- **The ballot length matrix on the diagonal, for every `m` and every slope
sequence**: `2` on a leaf row, `1 / s_i` on the spine row `h_i`, and `1/2` on a
stem.  At the zig-zag this is `Caterpillar.matrix_diag_cat`, whose `IsPairEdge`
split is exactly `s_i = 2` versus `s_i = 1`. -/
theorem bMatrix_diag (s : Slopes (2 * (m + 1))) (i : Fin (6 * m + 3)) :
    matrix (ballotLabelling m s).presentation i i =
      if IsLeafEdge m i then 2
      else if i.val % 3 = 1 then 1 / (s.slope ((i.val + 2) / 3) : ℚ)
      else 1 / 2 := by
  classical
  rw [bMatrix_diag_eq_sum]
  by_cases hLeaf : IsLeafEdge m i
  · rw [if_pos hLeaf, toFinset_bPath_leaf s hLeaf,
      Finset.sum_pair (bLoopFirst_ne_bLoopSecond s hLeaf),
      bSourceEdgeIndex_bLoopFirst s hLeaf, bSourceEdgeIndex_bLoopSecond s hLeaf]
    norm_num
  · rw [if_neg hLeaf, toFinset_bPath_notLeaf s hLeaf, Finset.sum_singleton]
    by_cases hspine : i.val % 3 = 1
    · rw [if_pos hspine, bSourceEdgeIndex_main_spine s hspine]
    · rw [if_neg hspine, bSourceEdgeIndex_main_stem s hLeaf hspine]
      norm_num

/-- **The numerator of a diagonal entry is `2` exactly on the leaf rows**, for
every slope sequence.  `Slopes.one_le_slope` is what makes the spine rows
contribute `1` whatever the slope is, so this statement does not mention `s`
at all. -/
theorem bNum_matrix_diag (s : Slopes (2 * (m + 1))) (i : Fin (6 * m + 3)) :
    ((matrix (ballotLabelling m s).presentation i i).num : ℚ) =
      if IsLeafEdge m i then 2 else 1 := by
  rw [bMatrix_diag]
  by_cases hLeaf : IsLeafEdge m i
  · rw [if_pos hLeaf, if_pos hLeaf]
    norm_num
  · rw [if_neg hLeaf, if_neg hLeaf]
    by_cases hspine : i.val % 3 = 1
    · rw [if_pos hspine, one_div,
        Rat.inv_natCast_num_of_pos (Slopes.one_le_slope s ((i.val + 2) / 3))]
      norm_num
    · rw [if_neg hspine]
      norm_num

/-- **The numerators of the ballot diagonal multiply to `2 ^ (2m+2)`**, which
is `2 ^ leafCount (catTree m)` -- for every `m` and every slope sequence. -/
theorem bProd_num_matrix_diag (s : Slopes (2 * (m + 1))) :
    ∏ i, ((matrix (ballotLabelling m s).presentation i i).num : ℚ)
      = 2 ^ (2 * m + 2) := by
  classical
  rw [Finset.prod_congr rfl fun i _ ↦ bNum_matrix_diag s i,
    ← Finset.prod_filter, Finset.prod_const, Caterpillar.card_leafEdges]

end DraismaVargas.Count.BallotDiagonal
