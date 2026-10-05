module

public import DraismaVargas.LocalCases.FacetGenericity
public import DraismaVargas.LocalCases.MonovalentWall
public import DraismaVargas.LocalCases.ZeroForestBridge
public import DraismaVargas.LocalCases.WallDegeneration

@[expose] public section

/-!
# The setup shared by every non-trivalent wall

Every valency case of the non-trivalent wall analysis of Vargas, Part II
(Section 5) rests on four facts about the wall.  This module proves three of
them; the fourth, genericity of the march's endpoint on the facet, is
`FacetGenericity`.

## §1. The single vanishing stable row

The chart coordinates of a march are the target tree's edge lengths and the
base coordinates are the source's stable row lengths: `currentFinish_map` reads
`A ⬝ z = baseFinish`.  So a stable row vanishing is a *base* coordinate
vanishing, and along the segment the base point is
`segment baseStart baseFinish t` with `baseStart` positive and `baseFinish`
nonnegative.  For `t < 1` that is positive in every coordinate, so

* no stable row can vanish at an inner wall event of a march
  (`stableRow_pos_of_lt_one`, `eq_one_of_stableRow_eq_zero`), which is why a
  Part II wall is never an inner wall event and why
  `IncomingSourceCases.exists_classification`'s `hRows` holds there for free
  (`rows_ne_zero_of_lt_one`);
* at the endpoint the vanishing rows are exactly the vanishing coordinates of
  `baseFinish`, so a march whose endpoint is on the open facet `{h₁ = 0}` has
  exactly one vanishing stable row, namely `h₁`
  (`existsUnique_zero_stableRow_of_facet`).

## §2. `val w₀ ≠ 1` under the non-loop invariant

`MonovalentWall.card_incidentEdges_merge_ne_one` excludes a monovalent wall
from `ContractionForest`, and the live derivation of `ContractionForest`
(`SourceFibreForest.contractionForest_of_fullDimensional`) needs *every*
stable row to be nonzero, which is exactly what fails at a Part II wall.  The
replacement hypothesis here is `NoContractedCycle`: the zero source subgraph of
the wall metric is a census forest.  That is Part II's "no cycle contracts"
(`prop-rphi-under-contraction`: a limit is again a `DTmor` iff no cycle
contracts iff the genus is unchanged), and when exactly one stable row vanishes
it says precisely that the vanishing row is not a loop.  From it,
`contractionForest_of_noContractedCycle` supplies `ContractionForest` with no
condition on the rows at all, and hence `val w₀ ≠ 1` and
`val w₀ ∈ {2, 3, 4}`.

## §3. Rigidity above `w₀` (Part II `lemma-above-w0`)

`targetChange_contractDatum_merge` is `ch w₀ = ch u + ch v`, the sum over merged
blocks of `ContractionRamification.localRamificationAt_contractDatum_merge`;
with change-minimality at both endpoints it becomes
`ch w₀ = 4 - val w₀` (`targetChange_merge_eq_four_sub_valency`).  Since every
`r₀(B)` is nonnegative (Riemann--Hurwitz for the contracted datum) and they sum
to `ch w₀`:

* at `val w₀ = 4` *every* `r₀(B)` vanishes, with no further input
  (`forall_localRamification_eq_zero_of_valency_four`);
* in general, `r₀(A) = ch w₀` at the anchor forces `r₀(B) = 0` at every other
  block above `w₀` (`localRamification_eq_zero_of_ne_anchor`), which is the
  "one anchor, one `r = 0` background" census the identification stage wants.

Part II derives `r₀(A) = ch w₀` for `val w₀ ∈ {3, 2}` from the local properties
at `A₁^{(q)}` above the divalent endpoint; that derivation is *not* formalized
in this module (it is `NonTrivalentValencyThreeRigidity` and
`NonTrivalentValencyTwoRigidity`), so here it is a hypothesis.

## §4. The three identities

`StableLocalProperties.localRamification_eq_nonDangling_form` is
Draisma--Vargas `lem-rphi-nd`.  At a block of non-dangling valency four it reads
`r₀(A) = 2|A| + 2 - Σ kᵢ`, so `r₀(A) = 4 - val w₀` gives

```text
k₂ + k₃ + k₄ + k₅ = 2|A| + val w₀ - 2
```

which is `(□) = 2|A| + 2` at `val w₀ = 4`, `(⊞) = 2|A| + 1` at `val w₀ = 3`
and `= 2|A|` at `val w₀ = 2` (Part II configuration A), the identities of Part
II's three cases `{v4-nd4}`, `{v3-nd4}` and `{v2-nd4}`.

## What is *not* here

No candidate, no resolution type, no limit matrix, no exit: those are the
valency-specific modules (`NonTrivalentValencyFour*`, `NonTrivalentValencyThree*`,
`NonTrivalentValencyTwo*`).  Nothing in this module constructs a
`FullDimensionalSourcePresentation`;
every statement about one takes it as a hypothesis, so the standing vacuity
risk recorded in `ThirdEquation` is inherited, not introduced.  §5 exhibits the
`NoContractedCycle` datum-free half and the arithmetic of §3/§4 on literal
inputs, so none of the new definitions is vacuous by arithmetic accident.
-/

namespace DraismaVargas.LocalCases.NonTrivalentWallSetup

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.FiniteAtlasMarch
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral

/-! ## 1.  A stable row vanishes only at the end of a march -/

section March

variable {coordinate chart : Type*} [Fintype coordinate]
  {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}

/-- An affine segment from a positive point to a nonnegative one is positive
before it arrives. -/
theorem segment_pos {ι : Type*} (start finish : ι → ℚ)
    (hstart : ∀ i, 0 < start i) (hfinish : ∀ i, 0 ≤ finish i)
    {time : ℚ} (h0 : 0 ≤ time) (h1 : time < 1) (i : ι) :
    0 < RationalAffineWall.segment start finish time i := by
  have hs := hstart i
  have hf := hfinish i
  unfold RationalAffineWall.segment
  nlinarith

/-- The chart's own segment maps onto the global one: this is
`currentStart_map` and `currentFinish_map` composed with the rebasing of the
segment parameter. -/
theorem mulVec_segment_current (state : State matrix baseStart baseFinish)
    (time : ℚ) :
    (matrix state.label).mulVec
        (RationalAffineWall.segment state.currentStart state.currentFinish time)
      = RationalAffineWall.segment baseStart baseFinish
          (state.restartTime + (1 - state.restartTime) * time) := by
  rw [MarchContinuation.mulVec_segment, state.currentStart_map,
    state.currentFinish_map, MarchContinuation.segment_rebase_right]

/-- **No stable row vanishes strictly inside a march.**  Every stable row
length at an interior point of the march's segment is strictly positive,
because the base point is then strictly inside the positive orthant. -/
theorem stableRow_pos_of_lt_one (state : State matrix baseStart baseFinish)
    (hstart : ∀ i, 0 < baseStart i) (hfinish : ∀ i, 0 ≤ baseFinish i)
    (hrestart : 0 ≤ state.restartTime) {time : ℚ} (h0 : 0 ≤ time) (h1 : time < 1)
    (row : coordinate) :
    0 < (matrix state.label).mulVec
      (RationalAffineWall.segment state.currentStart state.currentFinish time) row := by
  have hlt : state.restartTime < 1 := state.restart_lt_one
  rw [mulVec_segment_current state time]
  refine segment_pos baseStart baseFinish hstart hfinish ?_ ?_ row
  · nlinarith
  · nlinarith

/-- The same fact as the hypothesis shape `hRows` of
`IncomingSourceCases.exists_classification`. -/
theorem stableRow_ne_zero_of_lt_one (state : State matrix baseStart baseFinish)
    (hstart : ∀ i, 0 < baseStart i) (hfinish : ∀ i, 0 ≤ baseFinish i)
    (hrestart : 0 ≤ state.restartTime) {time : ℚ} (h0 : 0 ≤ time) (h1 : time < 1)
    (row : coordinate) :
    (matrix state.label).mulVec
      (RationalAffineWall.segment state.currentStart state.currentFinish time) row ≠ 0 :=
  (stableRow_pos_of_lt_one state hstart hfinish hrestart h0 h1 row).ne'

/-- **A stable row can vanish along a march only at its terminal state.** -/
theorem eq_one_of_stableRow_eq_zero (state : State matrix baseStart baseFinish)
    (hstart : ∀ i, 0 < baseStart i) (hfinish : ∀ i, 0 ≤ baseFinish i)
    (hrestart : 0 ≤ state.restartTime) {time : ℚ} (h0 : 0 ≤ time) (h1 : time ≤ 1)
    {row : coordinate}
    (hzero : (matrix state.label).mulVec
      (RationalAffineWall.segment state.currentStart state.currentFinish time) row = 0) :
    time = 1 := by
  by_contra hne
  exact stableRow_ne_zero_of_lt_one state hstart hfinish hrestart h0
    (lt_of_le_of_ne h1 hne) row hzero

/-- At the endpoint the stable row lengths are the base coordinates. -/
theorem mulVec_currentFinish (state : State matrix baseStart baseFinish)
    (row : coordinate) :
    (matrix state.label).mulVec state.currentFinish row = baseFinish row :=
  congrFun state.currentFinish_map row

/-- **Exactly one stable row vanishes at a facet endpoint.**  If the march's
endpoint is a point of the open facet `{facet = 0}` -- which is what Lemma G
selects -- then `facet` is the unique vanishing stable row of the terminal
state. -/
theorem existsUnique_zero_stableRow_of_facet
    (state : State matrix baseStart baseFinish) (facet : coordinate)
    (hfacet : baseFinish facet = 0) (hother : ∀ t, t ≠ facet → 0 < baseFinish t) :
    ∃! row : coordinate,
      (matrix state.label).mulVec state.currentFinish row = 0 := by
  refine ⟨facet, ?_, ?_⟩
  · show (matrix state.label).mulVec state.currentFinish facet = 0
    rw [mulVec_currentFinish state facet]
    exact hfacet
  · intro row hrow
    by_contra hne
    rw [mulVec_currentFinish state row] at hrow
    exact (hother row hne).ne' hrow

end March

/-! ### The row hypothesis in the presented form -/

section PresentedRows

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate chart : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}

/-- **`hRows` for free at an inner wall event.**  The hypothesis
`∀ row, (A_fullDim).mulVec coordinates row ≠ 0` of
`IncomingSourceCases.exists_classification` holds automatically at every
interior point of a march whose registered chart matrix is the honest stable
length matrix of `fullDim`. -/
theorem rows_ne_zero_of_lt_one
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (state : State matrix baseStart baseFinish)
    (hmatrix : GluingDatum.LengthMatrixPresentation.matrix
      fullDim.labelling.presentation = matrix state.label)
    (hstart : ∀ i, 0 < baseStart i) (hfinish : ∀ i, 0 ≤ baseFinish i)
    (hrestart : 0 ≤ state.restartTime) {time : ℚ} (h0 : 0 ≤ time) (h1 : time < 1) :
    ∀ row, (GluingDatum.LengthMatrixPresentation.matrix
        fullDim.labelling.presentation).mulVec
      (RationalAffineWall.segment state.currentStart state.currentFinish time) row ≠ 0 := by
  intro row
  rw [hmatrix]
  exact stableRow_ne_zero_of_lt_one state hstart hfinish hrestart h0 h1 row

end PresentedRows

/-! ## 2.  The wall valency under the non-loop invariant -/

section Valency

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- The nonnegative integral realization of a nonnegative chart-coordinate
vector, read through a presentation's target labelling. -/
noncomputable def wallRealization
    (presentation : data.LengthMatrixPresentation coordinate)
    (coordinates : coordinate → ℚ) (hNonnegative : ∀ column, 0 ≤ coordinates column) :
    data.NonnegativeIntegralRealization :=
  GluingDatum.NonnegativeIntegralRealization.ofNonnegativeRational data
    (fun edge ↦ coordinates (presentation.targetEdge.symm edge))
    (fun edge ↦ hNonnegative (presentation.targetEdge.symm edge))

/-- **The non-loop invariant.**  The zero subgraph of the wall metric contains
no cycle.

This is Part II's "no cycle contracts" condition
(`prop-rphi-under-contraction`): the limit is again a `DTmor` exactly when the
source genus is unchanged.  When exactly one stable row vanishes at the wall --
the Part II situation -- the zero subgraph is that row together with dangling
occurrences, so the condition says precisely that the vanishing row is **not a
loop** of the stable graph.

The live march derives the same conclusion from *all* rows being nonzero
(`SourceFibreForest.isForest_of_nonzero_rows`), which is exactly the hypothesis
a Part II wall violates. -/
def NoContractedCycle (presentation : data.LengthMatrixPresentation coordinate)
    (coordinates : coordinate → ℚ) (hNonnegative : ∀ column, 0 ≤ coordinates column) :
    Prop :=
  IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
    (wallRealization presentation coordinates hNonnegative).sourceZeroSet

variable {a b : target.V} {contracted : target.edges}

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- **The contraction fibre is a forest under the non-loop invariant.**  This
replaces `SourceFibreForest.contractionForest_of_fullDimensional` at a wall
where one stable row vanishes: no condition on the rows is used. -/
theorem contractionForest_of_noContractedCycle
    (presentation : data.LengthMatrixPresentation coordinate)
    (coordinates : coordinate → ℚ) (hNonnegative : ∀ column, 0 ≤ coordinates column)
    (hCycle : NoContractedCycle presentation coordinates hNonnegative)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hZero : coordinates (presentation.targetEdge.symm contracted) = 0) :
    ContractionForest data a b contracted := by
  refine ZeroForestBridge.contractionForest_of_isForest_of_targetLength_eq_zero data
    (wallRealization presentation coordinates hNonnegative) hc ?_ hCycle
  exact (GluingDatum.NonnegativeIntegralRealization.ofNonnegativeRational_targetLength_eq_zero_iff
    data _ _ contracted).mpr hZero

/-- **Excluding `val w₀ = 1` in Part II's `lemma-above-w0`.**  The merged
target vertex of a wall whose vanishing stable row is not a loop is not a leaf.

`lemma-above-w0` lists `val w₀ ∈ {4, 3, 2}` without excluding `1`; the
exclusion is `MonovalentWall`'s contraction-forest form of `lemma-loop-12`, and
the non-loop invariant is what supplies its forest hypothesis here. -/
theorem card_incidentEdges_merge_ne_one_of_noContractedCycle
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (coordinates : coordinate → ℚ) (hNonnegative : ∀ column, 0 ≤ coordinates column)
    (hCycle : NoContractedCycle fullDim.labelling.presentation coordinates hNonnegative)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hZero : coordinates (fullDim.labelling.presentation.targetEdge.symm contracted) = 0) :
    (GluingDatum.incidentEdges
      (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card ≠ 1 :=
  MonovalentWall.card_incidentEdges_merge_ne_one data hc hab hOne fullDim
    (contractionForest_of_noContractedCycle fullDim.labelling.presentation coordinates
      hNonnegative hCycle hc hZero)

/-- **`val w₀ ∈ {2, 3, 4}`** at a wall whose vanishing stable row
is not a loop. -/
theorem card_incidentEdges_merge_eq_two_three_or_four_of_noContractedCycle
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (coordinates : coordinate → ℚ) (hNonnegative : ∀ column, 0 ≤ coordinates column)
    (hCycle : NoContractedCycle fullDim.labelling.presentation coordinates hNonnegative)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hZero : coordinates (fullDim.labelling.presentation.targetEdge.symm contracted) = 0) :
    (GluingDatum.incidentEdges
        (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 2 ∨
      (GluingDatum.incidentEdges
          (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 3 ∨
        (GluingDatum.incidentEdges
          (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 4 :=
  MonovalentWall.card_incidentEdges_merge_eq_two_three_or_four data hc hab hOne fullDim
    (contractionForest_of_noContractedCycle fullDim.labelling.presentation coordinates
      hNonnegative hCycle hc hZero)

end Valency

/-! ## 3.  Rigidity above `w₀` -/

section Rigidity

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-- Two equal sheet partitions have the same block-indexed sums. -/
theorem sum_blocks_congr {P Q : SheetPartition degree} (hPQ : P = Q)
    (f : Fin degree → ℤ) :
    (∑ block : P.Blocks, f block.1) = ∑ block : Q.Blocks, f block.1 := by
  subst hPQ; rfl

/-- Summing over the fine blocks inside each coarse block is summing over all
fine blocks. -/
theorem sum_blocksWithin_sum (data : GluingDatum target degree) (vertex : target.V)
    (merged : SheetPartition degree)
    (f : (data.vertexPartition vertex).Blocks → ℤ) :
    (∑ mergedBlock : merged.Blocks,
        ∑ block ∈ SheetPartition.blocksWithin (data.vertexPartition vertex) merged
          mergedBlock, f block)
      = ∑ block : (data.vertexPartition vertex).Blocks, f block := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ
    (SheetPartition.fineBlockToCoarseBlock (data.vertexPartition vertex) merged) f]
  refine Finset.sum_congr rfl ?_
  intro mergedBlock _
  refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
  ext block
  simp

/-- **`ch w₀ = ch u + ch v`.**  The change at the merged target vertex is the
sum of the changes at the two endpoints of the contracted occurrence: the
block-by-block statement is
`ContractionRamification.localRamificationAt_contractDatum_merge`, and the
merged blocks partition both endpoint fibres. -/
theorem targetChange_contractDatum_merge (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted) :
    (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩
      = data.targetChange a + data.targetChange b := by
  classical
  have hmerge : (contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩
      = mergedPartition data a b :=
    contractDatum_vertexPartition_merge data hc hab hOne
  have hstep : (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩
      = ∑ block : (mergedPartition data a b).Blocks,
          localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 := by
    unfold GluingDatum.targetChange
    exact sum_blocks_congr hmerge
      (localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩)
  rw [hstep, Finset.sum_congr rfl (fun block _ ↦
      localRamificationAt_contractDatum_merge data hc hab hOne hForest block),
    Finset.sum_add_distrib, sum_blocksWithin_sum data a (mergedPartition data a b),
    sum_blocksWithin_sum data b (mergedPartition data a b)]
  rfl

/-- **`ch w₀ = 4 - val w₀`.**  Change-minimality at both endpoints of the
contracted occurrence turns the additivity into the valency form used
throughout Part II §5. -/
theorem targetChange_merge_eq_four_sub_valency (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hValid : data.Valid) (hMinimal : data.ChangeMinimal) :
    (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩
      = 4 - ((GluingDatum.incidentEdges
          (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card : ℤ) := by
  obtain ⟨hSum, -, -, -, -, hLeft, hRight⟩ :=
    WallProgress.endpoints_of_contraction data hc hab hOne hValid hMinimal
  have hcast : ((GluingDatum.incidentEdges
      (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card : ℤ) + 2
      = ((GluingDatum.incidentEdges a).card : ℤ)
        + ((GluingDatum.incidentEdges b).card : ℤ) := by
    exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℤ)) hSum
  rw [targetChange_contractDatum_merge data hc hab hOne hForest]
  linarith

/-- Every block above the merged vertex has nonnegative local ramification:
Riemann--Hurwitz for the contracted datum. -/
theorem localRamification_merge_nonneg (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted) (hValid : data.Valid)
    (block : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Blocks) :
    0 ≤ (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ block := by
  have hRH := (valid_contractDatum data hc hab hOne hForest hValid).2
  exact ((riemannHurwitzAtTargetVertex_iff _ _).mp (fun sheet ↦ hRH _ sheet)) block.1

/-- **Rigidity above `w₀` (Part II `lemma-above-w0`).**  If one block above the
merged vertex carries the whole change `ch w₀`, every other block above `w₀`
has `r₀ = 0`, so the deformation is localized at that block.

Part II derives the hypothesis `r₀(A) = ch w₀` from the local properties at
`A₁^{(q)}`; it is taken as a hypothesis here, and is *free* in the four-valent
case below. -/
theorem localRamification_eq_zero_of_ne_anchor (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted) (hValid : data.Valid)
    (anchor : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Blocks)
    (hanchor : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ anchor
      = (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩)
    (block : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Blocks)
    (hne : block ≠ anchor) :
    (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ block = 0 := by
  classical
  have htotal : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ anchor
      + ∑ other ∈ (Finset.univ.erase anchor),
          (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other
      = (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩ :=
    Finset.add_sum_erase _ _ (Finset.mem_univ anchor)
  have hrest : ∑ other ∈ (Finset.univ.erase anchor),
      (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0 := by
    rw [hanchor] at htotal
    linarith
  refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hrest block
    (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ block⟩)
  intro other _
  exact localRamification_merge_nonneg data hc hab hOne hForest hValid other

/-- **The four-valent case of rigidity is unconditional.**  At `val w₀ = 4` the
change vanishes, so every block above `w₀` has `r₀ = 0` -- in particular the
anchor, which is Part II's `r₀(A) = 0` for case `{v4-nd4}`. -/
theorem forall_localRamification_eq_zero_of_valency_four
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hValid : data.Valid) (hMinimal : data.ChangeMinimal)
    (hvalency : (GluingDatum.incidentEdges
      (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 4)
    (block : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Blocks) :
    (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ block = 0 := by
  classical
  have hchange : (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩ = 0 := by
    rw [targetChange_merge_eq_four_sub_valency data hc hab hOne hForest hValid hMinimal,
      hvalency]
    norm_num
  have hsum : ∑ other : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Blocks,
      (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0 := hchange
  refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hsum block (Finset.mem_univ block)
  intro other _
  exact localRamification_merge_nonneg data hc hab hOne hForest hValid other

end Rigidity

/-! ## 4.  The three identities -/

section Identities

variable {target : CFGraph} {degree : ℕ}

/-- The local ramification of a wall block, read at the quotient-source vertex
the block names. -/
theorem localRamification_sourceVertex (data : GluingDatum target degree)
    (wall : target.V) (block : (data.vertexPartition wall).Blocks) :
    data.localRamification (WallBlock.sourceVertex data wall block).1.1
        ⟨(WallBlock.sourceVertex data wall block).1.2,
          (WallBlock.sourceVertex data wall block).2⟩
      = data.localRamification wall block := by
  unfold WallBlock.sourceVertex GluingDatum.sourceEndpoint
  congr 1
  exact Subtype.ext block.2

/-- **`lem-rphi-nd` at a block of non-dangling valency four.**  The sum of the
dilation indices of the four surviving occurrences at the block is
`2|A| + 2 - r(A)`. -/
theorem sum_sourceEdgeIndex_of_nonDanglingValency_four
    (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (wall : target.V) (block : (data.vertexPartition wall).Blocks)
    (hnd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 4) :
    (∑ edge ∈ (Finset.univ :
        Finset (IncidentSourceEdge data (WallBlock.sourceVertex data wall block))).filter
          (fun edge ↦ ¬ IsDangling data edge.1),
        (data.sourceEdgeIndex edge.1 : ℤ))
      = 2 * ((data.vertexPartition wall).blockCard block.1 : ℤ) + 2
          - data.localRamification wall block := by
  have hform := StableLocalProperties.localRamification_eq_nonDangling_form data hNoGlue
    (WallBlock.sourceVertex data wall block)
  rw [localRamification_sourceVertex data wall block, hnd] at hform
  have hcard : ((data.vertexPartition
      (WallBlock.sourceVertex data wall block).1.1).blockCard
        (WallBlock.sourceVertex data wall block).1.2 : ℤ)
      = ((data.vertexPartition wall).blockCard block.1 : ℤ) := by
    have hrepr : (data.vertexPartition wall).repr block.1 = block.1 := block.2
    show (((data.vertexPartition wall).blockCard
        ((data.vertexPartition wall).repr block.1) : ℕ) : ℤ)
      = (((data.vertexPartition wall).blockCard block.1 : ℕ) : ℤ)
    rw [hrepr]
  rw [hcard] at hform
  push_cast at hform ⊢
  linarith

/-- **The anchor identity, uniformly in the wall valency.**  At the anchor
block `A` of non-dangling valency four above `w₀`, with `r₀(A) = ch w₀`,

```text
k₂ + k₃ + k₄ + k₅ = 2|A| + val w₀ - 2.
```
-/
theorem sum_sourceEdgeIndex_eq_of_anchor
    {a b : target.V} {contracted : target.edges}
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hValid : data.Valid) (hMinimal : data.ChangeMinimal)
    (hReflected : WallDegeneration.DanglingReflected data hc hab hOne)
    (hNoGlue : DanglingEdgeNoGlue data)
    (anchor : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Blocks)
    (hnd : nonDanglingValency (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor) = 4)
    (hanchor : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ anchor
      = (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩) :
    (∑ edge ∈ (Finset.univ :
        Finset (IncidentSourceEdge (contractDatum data hc hab hOne)
          (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor))).filter
          (fun edge ↦ ¬ IsDangling (contractDatum data hc hab hOne) edge.1),
        ((contractDatum data hc hab hOne).sourceEdgeIndex edge.1 : ℤ))
      = 2 * (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
              anchor.1 : ℤ)
          + ((GluingDatum.incidentEdges
              (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card : ℤ)
          - 2 := by
  have hwall := sum_sourceEdgeIndex_of_nonDanglingValency_four
    (contractDatum data hc hab hOne)
    (WallDegeneration.danglingEdgeNoGlue_contractDatum data hReflected hNoGlue)
    ⟨a, hab⟩ anchor hnd
  rw [hwall, hanchor,
    targetChange_merge_eq_four_sub_valency data hc hab hOne hForest hValid hMinimal]
  ring

/-- **Identity (□) of Part II.**  `val w₀ = 4`, case `{v4-nd4}`:
`k₂ + k₃ + k₄ + k₅ = 2|A| + 2`.  The anchor hypothesis is discharged by
`forall_localRamification_eq_zero_of_valency_four`, so this case needs no
input beyond the standing receipts. -/
theorem sum_sourceEdgeIndex_eq_valency_four
    {a b : target.V} {contracted : target.edges}
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hValid : data.Valid) (hMinimal : data.ChangeMinimal)
    (hReflected : WallDegeneration.DanglingReflected data hc hab hOne)
    (hNoGlue : DanglingEdgeNoGlue data)
    (hvalency : (GluingDatum.incidentEdges
      (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 4)
    (anchor : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Blocks)
    (hnd : nonDanglingValency (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor) = 4) :
    (∑ edge ∈ (Finset.univ :
        Finset (IncidentSourceEdge (contractDatum data hc hab hOne)
          (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor))).filter
          (fun edge ↦ ¬ IsDangling (contractDatum data hc hab hOne) edge.1),
        ((contractDatum data hc hab hOne).sourceEdgeIndex edge.1 : ℤ))
      = 2 * (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
          anchor.1 : ℤ) + 2 := by
  have hanchor : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ anchor
      = (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩ := by
    rw [forall_localRamification_eq_zero_of_valency_four data hc hab hOne hForest
        hValid hMinimal hvalency anchor,
      targetChange_merge_eq_four_sub_valency data hc hab hOne hForest hValid hMinimal,
      hvalency]
    norm_num
  rw [sum_sourceEdgeIndex_eq_of_anchor data hc hab hOne hForest hValid hMinimal
    hReflected hNoGlue anchor hnd hanchor, hvalency]
  ring

/-- **Identity (⊞) of Part II.**  `val w₀ = 3`, case `{v3-nd4}`:
`k₂ + k₃ + k₄ + k₅ = 2|A| + 1`. -/
theorem sum_sourceEdgeIndex_eq_valency_three
    {a b : target.V} {contracted : target.edges}
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hValid : data.Valid) (hMinimal : data.ChangeMinimal)
    (hReflected : WallDegeneration.DanglingReflected data hc hab hOne)
    (hNoGlue : DanglingEdgeNoGlue data)
    (hvalency : (GluingDatum.incidentEdges
      (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 3)
    (anchor : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Blocks)
    (hnd : nonDanglingValency (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor) = 4)
    (hanchor : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ anchor
      = (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩) :
    (∑ edge ∈ (Finset.univ :
        Finset (IncidentSourceEdge (contractDatum data hc hab hOne)
          (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor))).filter
          (fun edge ↦ ¬ IsDangling (contractDatum data hc hab hOne) edge.1),
        ((contractDatum data hc hab hOne).sourceEdgeIndex edge.1 : ℤ))
      = 2 * (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
          anchor.1 : ℤ) + 1 := by
  rw [sum_sourceEdgeIndex_eq_of_anchor data hc hab hOne hForest hValid hMinimal
    hReflected hNoGlue anchor hnd hanchor, hvalency]
  ring

/-- **The valency-two identity of Part II.**  `val w₀ = 2`,
configuration A of case `{v2-nd4}`: `k₂ + k₃ + k₄ + k₅ = 2|A|`. -/
theorem sum_sourceEdgeIndex_eq_valency_two
    {a b : target.V} {contracted : target.edges}
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hValid : data.Valid) (hMinimal : data.ChangeMinimal)
    (hReflected : WallDegeneration.DanglingReflected data hc hab hOne)
    (hNoGlue : DanglingEdgeNoGlue data)
    (hvalency : (GluingDatum.incidentEdges
      (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 2)
    (anchor : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Blocks)
    (hnd : nonDanglingValency (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor) = 4)
    (hanchor : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ anchor
      = (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩) :
    (∑ edge ∈ (Finset.univ :
        Finset (IncidentSourceEdge (contractDatum data hc hab hOne)
          (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor))).filter
          (fun edge ↦ ¬ IsDangling (contractDatum data hc hab hOne) edge.1),
        ((contractDatum data hc hab hOne).sourceEdgeIndex edge.1 : ℤ))
      = 2 * (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
          anchor.1 : ℤ) := by
  rw [sum_sourceEdgeIndex_eq_of_anchor data hc hab hOne hForest hValid hMinimal
    hReflected hNoGlue anchor hnd hanchor, hvalency]
  ring

end Identities

/-! ## 5.  The terminal state of a facet march -/

section TerminalState

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {baseStart baseFinish : coordinate → ℚ}

/-- **One vanishing coordinate at a terminal state of the universal atlas march.**
At the terminal state of a march whose endpoint is facet-generic and lies on
the facet `{facet = 0}`, exactly one chart coordinate -- i.e. exactly one
target edge length -- vanishes.

This is the object the valency-specific wall analysis starts from: the
contracted occurrence `t₁` is the unique zero, and every other occurrence is
positive. -/
theorem existsUnique_zero_currentFinish_of_facetGeneric
    (state : State (WallProgress.atlasChartMatrix coordinate degree)
      baseStart baseFinish)
    (hgeneric : FacetGenericity.FacetGeneric degree baseFinish)
    (facet : coordinate) (hfacet : baseFinish facet = 0)
    (hTerminal : State.Terminal state) :
    ∃! t : coordinate, state.currentFinish t = 0 :=
  FacetGenericity.existsUnique_zero_of_facetGeneric_atlas degree state.label facet
    baseFinish state.currentFinish hgeneric state.currentFinish_map hfacet hTerminal

/-- The two halves together: **exactly one stable source row and
exactly one target occurrence vanish** at the terminal state of a facet
march. -/
theorem existsUnique_zero_pair_of_facetGeneric
    (state : State (WallProgress.atlasChartMatrix coordinate degree)
      baseStart baseFinish)
    (hgeneric : FacetGenericity.FacetGeneric degree baseFinish)
    (facet : coordinate) (hfacet : baseFinish facet = 0)
    (hother : ∀ t, t ≠ facet → 0 < baseFinish t)
    (hTerminal : State.Terminal state) :
    (∃! row : coordinate, (WallProgress.atlasChartMatrix coordinate degree
        state.label).mulVec state.currentFinish row = 0) ∧
      ∃! t : coordinate, state.currentFinish t = 0 :=
  ⟨existsUnique_zero_stableRow_of_facet state facet hfacet hother,
    existsUnique_zero_currentFinish_of_facetGeneric state hgeneric facet hfacet
      hTerminal⟩

end TerminalState

/-! ## 6.  Non-vacuity -/

section NonVacuity

/-- A metric with no zero source occurrence has an empty zero set. -/
theorem sourceZeroSet_eq_empty_of_pos {target : CFGraph} {degree : ℕ}
    {data : GluingDatum target degree} {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate]
    (presentation : data.LengthMatrixPresentation coordinate)
    (coordinates : coordinate → ℚ) (hpos : ∀ column, 0 < coordinates column) :
    (wallRealization presentation coordinates (fun column ↦ (hpos column).le)).sourceZeroSet
      = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  intro slot hslot
  rw [GluingDatum.NonnegativeIntegralRealization.mem_sourceZeroSet] at hslot
  have hiff := GluingDatum.NonnegativeIntegralRealization.ofNonnegativeRational_sourceLength_eq_zero_iff
    data (fun edge ↦ coordinates (presentation.targetEdge.symm edge))
    (fun edge ↦ (hpos (presentation.targetEdge.symm edge)).le)
    ((wallRealization presentation coordinates (fun column ↦ (hpos column).le)).sourceEdgeAt slot)
  have hzero := hiff.mp hslot
  exact (hpos _).ne' hzero

/-- Contracting nothing is a forest contraction. -/
theorem isForest_empty {n p : ℕ} (core : ExplicitPotential.Core n p) :
    IsForest core (∅ : Finset (Fin p)) := by
  classical
  unfold IsForest
  rw [compFold_empty]
  simp

/-- **`NoContractedCycle` is not vacuous.**  Every strictly positive metric
satisfies it, for every gluing datum and every presentation: nothing vanishes,
so nothing contracts.  The Part II wall is the boundary case of exactly one
vanishing row, which the invariant still allows as long as that row is not a
loop. -/
theorem noContractedCycle_of_pos {target : CFGraph} {degree : ℕ}
    {data : GluingDatum target degree} {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate]
    (presentation : data.LengthMatrixPresentation coordinate)
    (coordinates : coordinate → ℚ) (hpos : ∀ column, 0 < coordinates column) :
    NoContractedCycle presentation coordinates (fun column ↦ (hpos column).le) := by
  unfold NoContractedCycle
  rw [sourceZeroSet_eq_empty_of_pos presentation coordinates hpos]
  exact isForest_empty _

/-- A two-coordinate march state in the identity chart, with a positive start
and a facet endpoint.  It exhibits the hypotheses of §1 as jointly
satisfiable. -/
noncomputable def exampleState :
    State (fun _ : Unit ↦ (1 : Matrix (Fin 2) (Fin 2) ℚ)) ![1, 1] ![0, 1] :=
  State.initial () ![1, 1] ![0, 1]
    (by intro i; fin_cases i <;> norm_num)
    (Matrix.one_mulVec _) (Matrix.one_mulVec _)

/-- **§1 is not vacuous**: the example state has exactly one vanishing stable
row. -/
theorem existsUnique_zero_stableRow_exampleState :
    ∃! row : Fin 2,
      (1 : Matrix (Fin 2) (Fin 2) ℚ).mulVec exampleState.currentFinish row = 0 := by
  refine existsUnique_zero_stableRow_of_facet exampleState 0 (by norm_num) ?_
  intro t ht
  fin_cases t
  · exact absurd rfl ht
  · norm_num

/-- **§1's interior positivity is not vacuous**: every stable row of the
example state is strictly positive before the endpoint. -/
theorem stableRow_pos_exampleState (row : Fin 2) :
    0 < (1 : Matrix (Fin 2) (Fin 2) ℚ).mulVec
      (RationalAffineWall.segment exampleState.currentStart
        exampleState.currentFinish (1 / 2)) row := by
  refine stableRow_pos_of_lt_one exampleState ?_ ?_ le_rfl (by norm_num)
    (by norm_num) row
  · intro i; fin_cases i <;> norm_num
  · intro i; fin_cases i <;> norm_num

end NonVacuity

end DraismaVargas.LocalCases.NonTrivalentWallSetup
