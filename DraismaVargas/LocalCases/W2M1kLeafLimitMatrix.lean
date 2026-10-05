module

public import DraismaVargas.LocalCases.W2M1kLeafRowDescent

@[expose] public section

/-!
# Figure 33's leaf member: the limit matrix

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w2-r2-nd3-M-1k}`, Figure 33 and
Equation (7).

`W2M1kLimitMatrix` evaluates **two** of Figure 33's three boxes, `M⁽²⁾` and
`M⁽³⁾`, out of `LimitChainCore`.  This module evaluates the third, the leaf
member `M⁽¹⁾` of Base I.a, which has no `LimitChainCore.WallCandidate`
(`W2M1kStableLift.leaf_not_wallCandidate`) and therefore none of the core's
matrix readers either.  The two statements are in the shape of
`W2M1kLimitMatrix.dividedMember_regrown` and `joinedMember_regrown`, so the
three-member balance of `W2M1kCommonBalance` can take all three as they stand:

* `leaf_matrix_retained` -- every retained column is literally the incoming
  wall column, read through the proved geometric row bijection
  `W2M1kLeafRowDescent.leafStablePathEquiv`.  Nothing about the retained
  *place* is assumed: `M⁽¹⁾` retains no wall direction at all, and the leaf's
  own regrown occurrences are excluded from a retained column by their target
  label alone (`BalancedGlobal.Candidate.newSourceEdge_target`), not by any
  side assignment;
* `leafMember_regrown` -- **`c⁽¹⁾ = 2c(e₁)`** (Figure 33's box for `M⁽¹⁾`), with
  **no** `s`.

## Why the leaf box has no background term

`M⁽²⁾` and `M⁽³⁾` carry Figure 33's `s`, the core's
`LimitChainCore.backgroundColumn data wall anchor path (star.edge 0)`, because
each of their background regrown occurrences is a *subdivision* of the old
block and survives exactly when the same-sheet old occurrence does
(`W2M1kStableGraph.divided_background_survives_iff`,
`joined_background_survives_iff`).  The leaf member's background endpoints on
the retained side are **source leaves**, so every one of its background regrown
occurrences is pruned (`W2M1kLeaves.leaf_new_background_dangling`, restated
here as `leaf_new_background_notMem`).  Its regrown column is therefore
supported entirely above `A₀`, on the retained pair's two arms
(`leaf_occurrences_new_first`), and Figure 33's box for that member reads
`σ¹(J₀,1) = σ¹(J₁,1) = 0` -- both arms are index-one singletons
(`leaf_newSourceEdge_index`) -- and `c⁽¹⁾ = 2c(e₁)`, the factor two being the
two arms' common row (`W2M1kLeafStableLift.leaf_new_stablePath_eq_first`).

That agrees with Figure 33's box: the evaluation below is `2 · [path = e₁'s
row]` on the nose, with no third term to reconcile.  Equation (7) itself is
used in the form of `BalancingValencyTwo.balance_M_1k`, whose second bracket
carries the factor two as well; this differs from the display of Equation (7)
in Part I, where the second bracket appears without it.  Both brackets vanish,
so the balance is unaffected.

## What is not here

Equation (7) itself and the common-balance receipt belong to
`W2M1kCommonBalance`, which this module deliberately does not import.
-/

namespace DraismaVargas.LocalCases.W2M1kLeafLimitMatrix

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StableSourceMatrix
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2M1kSourceCandidates W2M1kLeaves
open W2M1kStableGraph
open W2M1kLimitMatrix (firstRow secondRow thirdRow)
open W2M1kLeafStableLift W2M1kLeafRowDescent

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## §1  The retained columns -/

/-- Exact retained-column occurrence dictionary of `M⁽¹⁾`, including the actual
incoming stable class.  Injectivity of the geometric row map is essential
here. -/
theorem leaf_occurrences_retained (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (path : StablePath data) (place : target.edges) :
    occurrences (LeafPair.candidate input shape pair).datum
        (leafStablePathEquiv input shape pair path)
        (occurrenceEquiv target wall (LeafPair.candidate input shape pair).right (some place)) =
      (occurrences data path place).image (LeafPair.candidate input shape pair).oldSourceEdge := by
  classical
  ext edge
  constructor
  · intro hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases (LeafPair.candidate input shape pair) edge with
      ⟨old, rfl⟩ | ⟨sheet, rfl⟩
    · have hOld : ¬ IsDangling data old := fun hDangling ↦ hSurvives
        ((leaf_old_isDangling_iff input shape pair old).mpr hDangling)
      refine Finset.mem_image.mpr ⟨old, (mem_occurrences _ _ _).mpr ⟨⟨hOld, ?_⟩, ?_⟩, rfl⟩
      · exact (leafStablePathEquiv input shape pair).injective
          ((leafStablePathEquiv_mk input shape pair ⟨old, hOld⟩).trans hRow)
      · exact Option.some.inj ((occurrenceEquiv target wall
          (LeafPair.candidate input shape pair).right).injective hTarget)
    · have hLabels := (occurrenceEquiv target wall
        (LeafPair.candidate input shape pair).right).injective hTarget
      cases hLabels
  · intro hMem
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld
    refine (mem_occurrences _ _ _).mpr ⟨⟨ResolutionSurvival.not_isDangling_oldSourceEdge _
      input.valid.1 old hSurvives, ?_⟩, ?_⟩
    · exact (leafStablePathEquiv_mk input shape pair ⟨old, hSurvives⟩).symm.trans
        (congrArg (leafStablePathEquiv input shape pair) hRow)
    · exact congrArg (fun label ↦ occurrenceEquiv target wall
        (LeafPair.candidate input shape pair).right (some label)) hTarget

/-- **Every retained column of `M⁽¹⁾` is literally the incoming wall column**,
read through the proved geometric row bijection. -/
theorem leaf_matrix_retained (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (path : StablePath data) (place : target.edges) :
    matrix (LeafPair.candidate input shape pair).datum
        (leafStablePathEquiv input shape pair path)
        (occurrenceEquiv target wall (LeafPair.candidate input shape pair).right (some place)) =
      matrix data path place := by
  classical
  unfold matrix
  rw [leaf_occurrences_retained input shape pair path place, Finset.sum_image]
  · exact Finset.sum_congr rfl fun edge _ ↦ by
      rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]
  · intro first _ second _ hEqual
    exact ResolutionCut.oldSourceEdge_injective _ hEqual

/-! ## §2  `σ¹ = 0`: every regrown occurrence of `M⁽¹⁾` has index one

Above `A₀` the member's new edge is `SheetPartition.splitBlock` at the pinned
sheet, and off `A₀` it is `M11SourceCandidates.backgroundResolution`'s, again a
`splitBlock`.  So the new edge is discrete throughout, which is Base I.a's
`|e'| = |e''| = 1` and the vanishing of the two `σ`'s in Figure 33's box. -/

theorem leaf_newSourceEdge_index (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree) :
    (LeafPair.candidate input shape pair).datum.sourceEdgeIndex
        ((LeafPair.candidate input shape pair).newSourceEdge sheet) = 1 := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    LocalResolution.paste_newEdge_blockCard]
  by_cases hSelected : (data.vertexPartition wall).Rel (pinSheet profile 0)
      ((data.vertexPartition wall).repr sheet)
  · rw [leaf_resolution_selected input shape pair _ hSelected]
    exact firstResolution_newEdge_blockCard (data.vertexPartition wall) (pinSheet profile 0)
      pair.second sheet pair.ne_second pair.rel_second
      (hSelected.trans ((data.vertexPartition wall).rel_repr_left sheet))
  · rw [leaf_resolution_background input shape pair _ hSelected]
    exact (data.vertexPartition wall).splitBlock_blockCard_of_rel
      ((data.vertexPartition wall).repr sheet) sheet
      ((data.vertexPartition wall).rel_repr_left sheet)

/-! ## §3  The regrown column -/

/-- The image of `e₁`'s incoming row under `M⁽¹⁾`'s row bijection. -/
theorem leaf_firstRow_image (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    leafStablePathEquiv input shape pair (firstRow profile) =
      NonDanglingEdge.stablePath
        (⟨(LeafPair.candidate input shape pair).oldSourceEdge profile.first.1,
          leaf_first_survives input shape pair⟩ :
          NonDanglingEdge (LeafPair.candidate input shape pair).datum) := rfl

/-- **A surviving regrown occurrence of `M⁽¹⁾` sits in the regrown column
exactly in `e₁`'s row.**  Both arms of the retained pair do, which is the factor
two. -/
theorem leaf_new_mem_occurrences_iff (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).newSourceEdge sheet))
    (path : StablePath data) :
    (LeafPair.candidate input shape pair).newSourceEdge sheet ∈
        occurrences (LeafPair.candidate input shape pair).datum
          (leafStablePathEquiv input shape pair path)
          (occurrenceEquiv target wall (LeafPair.candidate input shape pair).right none) ↔
      path = firstRow profile := by
  classical
  rw [mem_occurrences]
  constructor
  · rintro ⟨⟨hOther, hRow⟩, -⟩
    apply (leafStablePathEquiv input shape pair).injective
    rw [← hRow, leaf_firstRow_image input shape pair]
    exact leaf_new_stablePath_eq_first input shape pair sheet hOther
  · rintro rfl
    exact ⟨⟨hSurvives, (leaf_new_stablePath_eq_first input shape pair sheet hSurvives).trans
      (leaf_firstRow_image input shape pair).symm⟩, rfl⟩

/-- **The leaf member contributes nothing off `A₀`.**  Every background regrown
occurrence is a pruned source leaf, so no `s` enters its box. -/
theorem leaf_new_background_notMem (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (path : StablePath data) :
    (LeafPair.candidate input shape pair).newSourceEdge sheet ∉
      occurrences (LeafPair.candidate input shape pair).datum
        (leafStablePathEquiv input shape pair path)
        (occurrenceEquiv target wall (LeafPair.candidate input shape pair).right none) := by
  classical
  rw [mem_occurrences]
  rintro ⟨⟨hSurvives, -⟩, -⟩
  exact hSurvives (leaf_new_background_dangling input shape pair sheet hBackground)

/-- **The whole support of `M⁽¹⁾`'s regrown column**: the retained pair's two
arms, in `e₁`'s row and nowhere else. -/
theorem leaf_occurrences_new_first (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    occurrences (LeafPair.candidate input shape pair).datum
        (leafStablePathEquiv input shape pair (firstRow profile))
        (occurrenceEquiv target wall (LeafPair.candidate input shape pair).right none) =
      {(LeafPair.candidate input shape pair).newSourceEdge (pinSheet profile 0),
        (LeafPair.candidate input shape pair).newSourceEdge pair.second} := by
  classical
  ext edge
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hMem
    obtain ⟨⟨hSurvives, -⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases (LeafPair.candidate input shape pair) edge with
      ⟨old, rfl⟩ | ⟨sheet, rfl⟩
    · have hLabels := (occurrenceEquiv target wall
        (LeafPair.candidate input shape pair).right).injective hTarget
      exact absurd hLabels (by simp)
    · rcases leaf_new_survives_cases input shape pair sheet hSurvives with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact (leaf_new_mem_occurrences_iff input shape pair (pinSheet profile 0)
        (leaf_new_pin_survives input shape pair) (firstRow profile)).mpr rfl
    · exact (leaf_new_mem_occurrences_iff input shape pair pair.second
        (leaf_new_second_survives input shape pair) (firstRow profile)).mpr rfl

/-- Off `e₁`'s row the regrown column is empty. -/
theorem leaf_occurrences_new_of_ne (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (path : StablePath data) (hPath : path ≠ firstRow profile) :
    occurrences (LeafPair.candidate input shape pair).datum
        (leafStablePathEquiv input shape pair path)
        (occurrenceEquiv target wall (LeafPair.candidate input shape pair).right none) = ∅ := by
  classical
  ext edge
  simp only [Finset.notMem_empty, iff_false]
  intro hMem
  obtain ⟨⟨hSurvives, -⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
  rcases ResolutionPruning.sourceEdge_cases (LeafPair.candidate input shape pair) edge with
    ⟨old, rfl⟩ | ⟨sheet, rfl⟩
  · have hLabels := (occurrenceEquiv target wall
      (LeafPair.candidate input shape pair).right).injective hTarget
    exact absurd hLabels (by simp)
  · exact hPath ((leaf_new_mem_occurrences_iff input shape pair sheet hSurvives path).mp hMem)

/-- **`c⁽¹⁾ = 2c(e₁)`** (Figure 33's box for `M⁽¹⁾`).  Base I.a: the two surviving regrown
occurrences are the index-one arms of the retained pair
(`leaf_newSourceEdge_index`), and both join `e₁`'s stable row.  Every other arm
-- the `k - 1` singletons over `A₀ ∖ {x, pair.second}` and every background one
-- is pruned at the target leaf, so there is **no** background term: Figure 33's
box for this member records exactly `σ¹(J₀,1) = σ¹(J₁,1) = 0` and no `s`.

Stated in the shape of `W2M1kLimitMatrix.dividedMember_regrown` and
`joinedMember_regrown`, whose right-hand sides do carry
`LimitChainCore.backgroundColumn`. -/
theorem leafMember_regrown (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (path : StablePath data) :
    matrix (LeafPair.candidate input shape pair).datum
        (leafStablePathEquiv input shape pair path)
        (occurrenceEquiv target wall (LeafPair.candidate input shape pair).right none) =
      2 * (if path = firstRow profile then (1 : ℚ) else 0) := by
  classical
  unfold matrix
  by_cases hPath : path = firstRow profile
  · subst hPath
    rw [leaf_occurrences_new_first input shape pair,
      Finset.sum_pair (leaf_newSourceEdge_ne input shape pair),
      leaf_newSourceEdge_index input shape pair (pinSheet profile 0),
      leaf_newSourceEdge_index input shape pair pair.second, ite_eq_left rfl]
    norm_num
  · rw [leaf_occurrences_new_of_ne input shape pair path hPath, Finset.sum_empty,
      ite_eq_right hPath]
    ring

/-- The same evaluation as a single conditional. -/
theorem leafMember_regrown_ite (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (path : StablePath data) :
    matrix (LeafPair.candidate input shape pair).datum
        (leafStablePathEquiv input shape pair path)
        (occurrenceEquiv target wall (LeafPair.candidate input shape pair).right none) =
      (if path = firstRow profile then (2 : ℚ) else 0) := by
  classical
  rw [leafMember_regrown input shape pair path]
  split_ifs <;> ring

end DraismaVargas.LocalCases.W2M1kLeafLimitMatrix
