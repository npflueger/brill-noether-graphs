module

public import DraismaVargas.LocalCases.W3Nd2IncomingBackground
public import DraismaVargas.LocalCases.TargetPartitionNormalization

@[expose] public section

/-!
# Whole-block census at the selected incoming W3 nd2 wall, and sheet normalization

Source: Draisma--Vargas Part I, case `w3-r1-nd2` and Figure 31 (whose reference
back to an earlier case is read here as case `{w3-r1-nd3-t2}`), and case
`{w3-r0}`.  The inputs are
`W3Nd2IncomingSelectedCensus.selected_fibre_census`,
`W3Nd2IncomingSheetClasses.selected_sheet_classes` and
`W3Nd2IncomingBackground.background_localRamification_endpoints_eq_zero`.

## The whole-block census, at the granularity that actually holds

`W3Nd2IncomingBackground` classifies the r0 background at *vertex*
granularity.  The M11 whole-block census does not carry over to a `(2,3)` wall
in its M11 shape, but a whole-block statement of a different shape does hold,
and this file proves it.

M11 (`M11IncomingBackground`) classifies each of `vertexPartition a`,
`edgePartition contracted` and `vertexPartition b` on a background block as
`JoinedOnBlock` or `DiscreteOnBlock`.  That trichotomy is *not* reproduced here
and no part of it is proved for the divalent side: the vertex-level dichotomy
`W3Nd2IncomingBackground.background_divalent_dichotomy` leaves each source
vertex above the divalent endpoint free to be either a dangling singleton or a
non-dangling valency-two vertex, and nothing below separates the two inside one
block.  The census proved here does not need such a flag.

What *is* unconditionally true, and is proved here, is a whole-block statement
covering both endpoints and the contracted occurrence at once
(`background_whole_block_census`).  Writing `u` for the divalent original
endpoint and `v` for the trivalent one:

* every occurrence incident to `u` -- the contracted occurrence and both
  retained ones -- has exactly `vertexPartition u`'s own sheet relation on the
  whole background block.  This is `{w3-r0}`'s vanishing ramification at `u` fed
  through `StableLocalProperties.edgePartition_rel_iff_of_divalent_localRamification_zero`,
  which needs only the divalent endpoint and so never needs a trivalent
  analogue;
* hence the contracted occurrence and `vertexPartition u` induce the same block
  count there, and `ContractionForest` forces `vertexPartition v` to induce
  exactly one: **the trivalent endpoint partition is `JoinedOnBlock` on every
  background block.**

`selected_endpoint_joined` is the complementary statement on the distinguished
block: Figure 31's ramified endpoint carries the entire merged class `A_0`, so
there too one of the two endpoint partitions is joined.  Which of the two it is
is the `M^{(1)}`/`M^{(2)}` dichotomy and is left as a disjunction, so the pair
of statements says: on every wall block at least one endpoint partition is
joined, and on a background block it is the trivalent one.

`background_relations_of_left_divalent` and its mirror restate the background
half at sheets rather than at blocks, which is the form a later blockwise
resolution comparison consumes.

## Stored-representative normalization

`exists_normalized_presentation` is the normalization step: equality of block relations
does not identify stored representative maps, so the within-block transpositions
of `Infrastructure.PartitionNormalization` are applied and the honest
full-dimensional presentation is transported through
`TargetPartitionNormalization`.  It is stated for an arbitrary target
isomorphism and comparison datum -- the two available here are
`W3Nd2IncomingDirection.coarseTargetIso` and `fineTargetIso` -- with the
pointwise `SameBlocks` families as explicit hypotheses.  Supplying those
families for a named Figure 31 member is **not** done here (see
`W3Nd2IncomingMemberMatching`); nor is any incoming classification or
count-based stable-row bijection used, which the recorded occurrence and matrix
clauses make explicit.

## The `AnyBlock` forms

The whole background group below depends on `background ≠
input.distinguishedBlock` only through
`W3Nd2IncomingBackground.background_localRamification_endpoints_eq_zero`, whose
single use of it is to obtain vanishing local ramification of the block.  Each
of them is therefore also available in the `AnyBlock` namespace with
`(contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0` as
the hypothesis, free of the `ThreeStar` and the `W3SourceInput`; the originals
are one-line wrappers around those.

## The `(1, 3)` `AnyBlock` forms

Every lemma of that group hypothesises one restored endpoint **divalent**.  At a
`T_∅` wall -- Base I.a of Figure 33, `w2M1k`'s `M⁽¹⁾` -- the valencies are
`(1, 3)` and neither endpoint is, so none of them applies.  The `AnyBlock`
namespace therefore also carries a `_of_left_leaf` / `_of_right_leaf` group,
`(GluingDatum.incidentEdges a).card = 1` (resp. `b`) in place of the divalence,
proving that the leaf's partition and the contracted occurrence's are discrete
on the block and that the trivalent endpoint is joined there.  It is
independent of the divalent group, shares its hypotheses and its
contraction-forest step, and its source is the change-minimal-leaf remark
`rem-leaves-min-change` of Part I.
-/

namespace DraismaVargas.LocalCases.W3Nd2IncomingNormalization

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties NonDanglingValency
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open M11IncomingPartitions
open W3Nd2IncomingTargetPlacement

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-! ## A counting lemma for two partitions that agree on one coarse block -/

/-- If two sheet partitions have the same relation at every sheet of a chosen
coarse block, they induce the same number of blocks on it.  The representative
maps themselves are *not* identified: only the induced count is. -/
theorem blockCountWithin_congr_of_rel_on_block_local {d : ℕ}
    (first second coarse : SheetPartition d) (root : Fin d)
    (hRefines : first.Refines coarse)
    (hAgree : ∀ i j, coarse.Rel root i → (first.Rel i j ↔ second.Rel i j)) :
    first.blockCountWithin coarse root = second.blockCountWithin coarse root := by
  classical
  have hMem : ∀ x ∈ (coarse.block root).image first.repr, coarse.Rel root x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact ((coarse.mem_block_iff root i).mp hi).trans
      (hRefines.rel (first.rel_repr_right i))
  refine Finset.card_bij (fun x _ ↦ second.repr x) ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, (coarse.mem_block_iff root x).mpr (hMem x hx), rfl⟩
  · intro x hx y hy hEq
    have hRoot := hMem x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    have hFirstRel : first.Rel (first.repr i) (first.repr j) :=
      (hAgree _ _ hRoot).mpr hEq
    have hLeft : first.repr (first.repr i) = first.repr i := first.repr_idem i
    have hRight : first.repr (first.repr j) = first.repr j := first.repr_idem j
    exact hLeft.symm.trans (hFirstRel.trans hRight)
  · intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨first.repr j, Finset.mem_image.mpr ⟨j, hj, rfl⟩, ?_⟩
    exact ((hAgree j (first.repr j) ((coarse.mem_block_iff root j).mp hj)).mp
      (first.rel_repr_right j)).symm

/-- A fine block that already fills a whole coarse block joins it. -/
theorem joinedOnBlock_of_block_eq_local {d : ℕ} (fine coarse : SheetPartition d)
    (root sheet : Fin d) (hBlock : fine.block sheet = coarse.block root) :
    JoinedOnBlock fine coarse root := by
  intro i j hi hj
  have hi' : fine.Rel sheet i := by
    apply (fine.mem_block_iff sheet i).mp
    rw [hBlock]
    exact (coarse.mem_block_iff root i).mpr hi
  have hj' : fine.Rel sheet j := by
    apply (fine.mem_block_iff sheet j).mp
    rw [hBlock]
    exact (coarse.mem_block_iff root j).mpr hj
  exact hi'.symm.trans hj'

/-! ## The whole-block census of an r0 background block -/

section AnyBlockBackground

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)

/-! ### The background group at *any* wall block of vanishing local ramification

Every statement of the `Background` section below is proved from
`W3Nd2IncomingBackground.background_localRamification_endpoints_eq_zero`, whose
only use of `input.distinguishedBlock` was to obtain vanishing local
ramification of the block.  Taking that vanishing as the hypothesis removes the
`ThreeStar` and the `W3SourceInput` from the entire group, which is the form
the two `r = 1` blocks of case `{w2-r1}` need: there the background condition
is `background ∉ {A, B}`, not `background ≠ input.distinguishedBlock`.

The original statements are one-line wrappers around these, obtaining `hZero`
by
`ThirdEquation.W3SourceInput.localRamification_eq_zero_of_ne`. -/
namespace AnyBlock

include fullDim hForest

/-- **Left-divalent orientation.**  On a wall block of vanishing local
ramification, *every* occurrence at the divalent original endpoint carries
exactly the endpoint's own sheet relation. -/
theorem background_edge_rel_iff_of_left_divalent
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges a)
    (first second : Fin degree)
    (hFirst : (mergedPartition data a b).Rel background.1 first) :
    (data.edgePartition edge).Rel first second ↔
      (data.vertexPartition a).Rel first second :=
  edgePartition_rel_iff_of_divalent_localRamification_zero data a hLeftDivalent first
    (W3Nd2IncomingBackground.AnyBlock.background_localRamification_endpoints_eq_zero
      data hc hab hOne fullDim hForest hZero first hFirst).1 edge hEdge second

/-- The induced block counts therefore agree. -/
theorem background_blockCountWithin_eq_of_left_divalent
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges a) :
    (data.edgePartition edge).blockCountWithin (mergedPartition data a b) background.1 =
      (data.vertexPartition a).blockCountWithin (mergedPartition data a b) background.1 :=
  blockCountWithin_congr_of_rel_on_block_local _ _ _ _
    ((refines_of_mem_incidentEdges data hEdge).trans
      (vertexPartition_refines_mergedPartition data a b))
    (fun i j hi ↦ background_edge_rel_iff_of_left_divalent data hc hab hOne fullDim hForest
      hLeftDivalent hZero edge hEdge i j hi)

/-- **The whole-block census, left-divalent orientation.**  The forest identity
turns the count equality into a *single* block of the trivalent endpoint
partition on the whole block. -/
theorem background_trivalent_joined_of_left_divalent
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0) :
    (data.vertexPartition b).blockCountWithin (mergedPartition data a b) background.1 = 1 ∧
      JoinedOnBlock (data.vertexPartition b) (mergedPartition data a b) background.1 := by
  have hTree := contractionForest_count data hc hForest
    (selectedMergedBlock data hc hab hOne background)
  have hEdgeCount := background_blockCountWithin_eq_of_left_divalent data hc hab hOne fullDim
    hForest hLeftDivalent hZero contracted (contracted_mem_incidentEdges_left hc)
  have hCount : (data.vertexPartition b).blockCountWithin
      (mergedPartition data a b) background.1 = 1 := by
    have hTree' : ((data.edgePartition contracted).blockCountWithin
          (mergedPartition data a b) background.1 : ℤ) + 1 =
        ((data.vertexPartition a).blockCountWithin
            (mergedPartition data a b) background.1 : ℤ) +
          ((data.vertexPartition b).blockCountWithin
            (mergedPartition data a b) background.1 : ℤ) := hTree
    rw [hEdgeCount] at hTree'
    have : ((data.vertexPartition b).blockCountWithin
        (mergedPartition data a b) background.1 : ℤ) = 1 := by linarith
    exact_mod_cast this
  exact ⟨hCount, joinedOnBlock_of_blockCountWithin_eq_one _ _ _
    (vertexPartition_refines_mergedPartition_right data a b) hCount⟩

/-- **Right-divalent orientation.**  The mirror of
`background_edge_rel_iff_of_left_divalent`. -/
theorem background_edge_rel_iff_of_right_divalent
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges b)
    (first second : Fin degree)
    (hFirst : (mergedPartition data a b).Rel background.1 first) :
    (data.edgePartition edge).Rel first second ↔
      (data.vertexPartition b).Rel first second :=
  edgePartition_rel_iff_of_divalent_localRamification_zero data b hRightDivalent first
    (W3Nd2IncomingBackground.AnyBlock.background_localRamification_endpoints_eq_zero
      data hc hab hOne fullDim hForest hZero first hFirst).2 edge hEdge second

/-- The induced block counts therefore agree. -/
theorem background_blockCountWithin_eq_of_right_divalent
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges b) :
    (data.edgePartition edge).blockCountWithin (mergedPartition data a b) background.1 =
      (data.vertexPartition b).blockCountWithin (mergedPartition data a b) background.1 :=
  blockCountWithin_congr_of_rel_on_block_local _ _ _ _
    ((refines_of_mem_incidentEdges data hEdge).trans
      (vertexPartition_refines_mergedPartition_right data a b))
    (fun i j hi ↦ background_edge_rel_iff_of_right_divalent data hc hab hOne fullDim hForest
      hRightDivalent hZero edge hEdge i j hi)

/-- **The whole-block census, right-divalent orientation.** -/
theorem background_trivalent_joined_of_right_divalent
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0) :
    (data.vertexPartition a).blockCountWithin (mergedPartition data a b) background.1 = 1 ∧
      JoinedOnBlock (data.vertexPartition a) (mergedPartition data a b) background.1 := by
  have hTree := contractionForest_count data hc hForest
    (selectedMergedBlock data hc hab hOne background)
  have hEdgeCount := background_blockCountWithin_eq_of_right_divalent data hc hab hOne fullDim
    hForest hRightDivalent hZero contracted (contracted_mem_incidentEdges_right hc)
  have hCount : (data.vertexPartition a).blockCountWithin
      (mergedPartition data a b) background.1 = 1 := by
    have hTree' : ((data.edgePartition contracted).blockCountWithin
          (mergedPartition data a b) background.1 : ℤ) + 1 =
        ((data.vertexPartition a).blockCountWithin
            (mergedPartition data a b) background.1 : ℤ) +
          ((data.vertexPartition b).blockCountWithin
            (mergedPartition data a b) background.1 : ℤ) := hTree
    rw [hEdgeCount] at hTree'
    have : ((data.vertexPartition a).blockCountWithin
        (mergedPartition data a b) background.1 : ℤ) = 1 := by linarith
    exact_mod_cast this
  exact ⟨hCount, joinedOnBlock_of_blockCountWithin_eq_one _ _ _
    (vertexPartition_refines_mergedPartition data a b) hCount⟩

/-- **The `r = 0` whole-block census at a `(2,3)` incoming W3 wall**, at any
wall block of vanishing local ramification.  The wall star enters only through
`W3Nd2IncomingTargetPlacement.endpoint_valencies`, which decides which original
endpoint is the divalent one; it is an explicit argument here and no source
input is used. -/
theorem background_whole_block_census
    (wallStar : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0) :
    ((GluingDatum.incidentEdges a).card = 2 ∧ (GluingDatum.incidentEdges b).card = 3 ∧
        (∀ edge ∈ GluingDatum.incidentEdges a, ∀ first second : Fin degree,
            (mergedPartition data a b).Rel background.1 first →
            ((data.edgePartition edge).Rel first second ↔
              (data.vertexPartition a).Rel first second)) ∧
        JoinedOnBlock (data.vertexPartition b) (mergedPartition data a b) background.1 ∧
        (data.vertexPartition b).blockCountWithin
          (mergedPartition data a b) background.1 = 1) ∨
      ((GluingDatum.incidentEdges a).card = 3 ∧ (GluingDatum.incidentEdges b).card = 2 ∧
        (∀ edge ∈ GluingDatum.incidentEdges b, ∀ first second : Fin degree,
            (mergedPartition data a b).Rel background.1 first →
            ((data.edgePartition edge).Rel first second ↔
              (data.vertexPartition b).Rel first second)) ∧
        JoinedOnBlock (data.vertexPartition a) (mergedPartition data a b) background.1 ∧
        (data.vertexPartition a).blockCountWithin
          (mergedPartition data a b) background.1 = 1) := by
  rcases W3Nd2IncomingTargetPlacement.endpoint_valencies data hc hab hOne fullDim wallStar with
    ⟨hLeft, hRight, _, _⟩ | ⟨hLeft, hRight, _, _⟩
  · refine Or.inl ⟨hLeft, hRight, ?_, ?_, ?_⟩
    · exact fun edge hEdge first second hFirst ↦
        background_edge_rel_iff_of_left_divalent data hc hab hOne fullDim hForest
          hLeft hZero edge hEdge first second hFirst
    · exact (background_trivalent_joined_of_left_divalent data hc hab hOne fullDim hForest
        hLeft hZero).2
    · exact (background_trivalent_joined_of_left_divalent data hc hab hOne fullDim hForest
        hLeft hZero).1
  · refine Or.inr ⟨hLeft, hRight, ?_, ?_, ?_⟩
    · exact fun edge hEdge first second hFirst ↦
        background_edge_rel_iff_of_right_divalent data hc hab hOne fullDim hForest
          hRight hZero edge hEdge first second hFirst
    · exact (background_trivalent_joined_of_right_divalent data hc hab hOne fullDim hForest
        hRight hZero).2
    · exact (background_trivalent_joined_of_right_divalent data hc hab hOne fullDim hForest
        hRight hZero).1

/-- **Left-divalent orientation, read at sheets rather than at blocks**, from
the vanishing local ramification of the sheet's own wall block. -/
theorem background_relations_of_left_divalent
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    (first second : Fin degree)
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩
      (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ first) = 0)
    (hMerged : (mergedPartition data a b).Rel first second) :
    ((data.edgePartition contracted).Rel first second ↔
        (data.vertexPartition a).Rel first second) ∧
      (data.vertexPartition b).Rel first second := by
  have hRoot : (mergedPartition data a b).Rel
      (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ first).1 first := by
    rw [← contractDatum_vertexPartition_merge data hc hab hOne]
    exact ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).rel_repr_left first
  refine ⟨background_edge_rel_iff_of_left_divalent data hc hab hOne fullDim hForest
      hLeftDivalent hZero contracted (contracted_mem_incidentEdges_left hc)
      first second hRoot, ?_⟩
  exact (background_trivalent_joined_of_left_divalent data hc hab hOne fullDim hForest
    hLeftDivalent hZero).2 first second hRoot (hRoot.trans hMerged)

/-- **Right-divalent orientation, read at sheets.**  The mirror of
`background_relations_of_left_divalent`. -/
theorem background_relations_of_right_divalent
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2)
    (first second : Fin degree)
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩
      (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ first) = 0)
    (hMerged : (mergedPartition data a b).Rel first second) :
    ((data.edgePartition contracted).Rel first second ↔
        (data.vertexPartition b).Rel first second) ∧
      (data.vertexPartition a).Rel first second := by
  have hRoot : (mergedPartition data a b).Rel
      (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ first).1 first := by
    rw [← contractDatum_vertexPartition_merge data hc hab hOne]
    exact ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).rel_repr_left first
  refine ⟨background_edge_rel_iff_of_right_divalent data hc hab hOne fullDim hForest
      hRightDivalent hZero contracted (contracted_mem_incidentEdges_right hc)
      first second hRoot, ?_⟩
  exact (background_trivalent_joined_of_right_divalent data hc hab hOne fullDim hForest
    hRightDivalent hZero).2 first second hRoot (hRoot.trans hMerged)

/-! ### The `(1, 3)` forms: a monovalent restored endpoint

Every statement above needs one restored endpoint **divalent**, and at a `T_∅`
wall -- Base I.a of Figure 33, `w2M1k`'s `M⁽¹⁾` -- the valencies are `(1, 3)`
and neither endpoint is.  The group below is the `(1, 3)` replacement, on the
same bundle and with the same `hZero` hypothesis.

The source is Draisma--Vargas's change-minimal-leaf remark
(`rem-leaves-min-change`), formalized as
`StableLocalProperties.leaf_block_dichotomy`: above a change-minimal leaf a
source block is either a dangling single sheet of vanishing local ramification,
or *the* block of local degree two and local ramification two.  On a wall block
of vanishing local ramification the second alternative is excluded at every
sheet -- `W3Nd2IncomingBackground.AnyBlock.background_localRamification_endpoints_eq_zero`
descends the vanishing to the leaf -- so the leaf partition is **discrete**
there, and so is the contracted occurrence's, which refines it
(`background_edge_discrete_of_left_leaf` and its mirror).

The trivalent endpoint is then joined for exactly the reason the divalent group
gives: the contracted occurrence and the leaf partition induce the same count on
the block (both discrete), so the contraction-forest identity `e + 1 = p + q`
forces `q = 1` (`background_trivalent_joined_of_left_leaf` and its mirror).  No
`ThreeStar`, no source input, and no divalence hypothesis occurs. -/

/-- **Left-leaf orientation.**  On a wall block of vanishing local ramification
whose left restored endpoint is a leaf, both the leaf's vertex partition and the
contracted occurrence's partition are discrete: every sheet of the block is its
own block.  `rem-leaves-min-change` through
`StableLocalProperties.leaf_block_dichotomy`. -/
theorem background_edge_discrete_of_left_leaf
    (hLeafLeft : (GluingDatum.incidentEdges a).card = 1)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0)
    (sheet : Fin degree) (hSheet : (mergedPartition data a b).Rel background.1 sheet) :
    (data.vertexPartition a).block sheet = {sheet} ∧
      (data.edgePartition contracted).block sheet = {sheet} := by
  classical
  have hRam : data.localRamification a ((data.vertexPartition a).toBlock sheet) = 0 :=
    (W3Nd2IncomingBackground.AnyBlock.background_localRamification_endpoints_eq_zero
      data hc hab hOne fullDim hForest hZero sheet hSheet).1
  have hLeft : (data.vertexPartition a).block sheet = {sheet} := by
    rcases leaf_block_dichotomy data fullDim.valid fullDim.noDanglingTargetFibres a
        hLeafLeft (fullDim.changeMinimal a) ((data.vertexPartition a).toBlock sheet) with
      ⟨_, hCard, _⟩ | ⟨_, _, hTwo, _⟩
    · refine (data.vertexPartition a).block_eq_singleton_of_blockCard_eq_one sheet ?_
      simp only [SheetPartition.toBlock_val, SheetPartition.blockCard,
        (data.vertexPartition a).block_eq_of_rel
          ((data.vertexPartition a).rel_repr_left sheet)] at hCard
      exact hCard
    · rw [hTwo] at hRam
      exact absurd hRam (by norm_num)
  refine ⟨hLeft, ?_⟩
  have hRefines : (data.edgePartition contracted).Refines (data.vertexPartition a) :=
    refines_of_mem_incidentEdges data (contracted_mem_incidentEdges_left hc)
  refine Finset.Subset.antisymm ?_ ?_
  · rw [← hLeft]
    intro j hj
    exact ((data.vertexPartition a).mem_block_iff _ _).mpr
      (hRefines.rel (((data.edgePartition contracted).mem_block_iff _ _).mp hj))
  · intro j hj
    rw [Finset.mem_singleton.mp hj]
    exact (data.edgePartition contracted).self_mem_block sheet

/-- The induced block counts of the contracted occurrence and of the leaf agree:
both are discrete on the block. -/
theorem background_blockCountWithin_eq_of_left_leaf
    (hLeafLeft : (GluingDatum.incidentEdges a).card = 1)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0) :
    (data.edgePartition contracted).blockCountWithin (mergedPartition data a b) background.1 =
      (data.vertexPartition a).blockCountWithin (mergedPartition data a b) background.1 := by
  refine blockCountWithin_congr_of_rel_on_block_local _ _ _ _
    ((refines_of_mem_incidentEdges data (contracted_mem_incidentEdges_left hc)).trans
      (vertexPartition_refines_mergedPartition data a b)) ?_
  intro i j hi
  refine ⟨fun h ↦ (refines_of_mem_incidentEdges data
    (contracted_mem_incidentEdges_left hc)).rel h, fun h ↦ ?_⟩
  have hBlock := (background_edge_discrete_of_left_leaf data hc hab hOne fullDim hForest
    hLeafLeft hZero i hi).1
  have hMem : j ∈ ({i} : Finset (Fin degree)) := by
    rw [← hBlock]
    exact ((data.vertexPartition a).mem_block_iff i j).mpr h
  rw [Finset.mem_singleton.mp hMem]
  rfl

/-- **The whole-block census, left-leaf orientation.**  The forest identity
turns the count equality into a *single* block of the trivalent endpoint
partition on the whole block -- the `(1, 3)` analogue of
`background_trivalent_joined_of_left_divalent`, with the leaf in the divalent
endpoint's place. -/
theorem background_trivalent_joined_of_left_leaf
    (hLeafLeft : (GluingDatum.incidentEdges a).card = 1)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0) :
    (data.vertexPartition b).blockCountWithin (mergedPartition data a b) background.1 = 1 ∧
      JoinedOnBlock (data.vertexPartition b) (mergedPartition data a b) background.1 := by
  have hTree := contractionForest_count data hc hForest
    (selectedMergedBlock data hc hab hOne background)
  have hEdgeCount := background_blockCountWithin_eq_of_left_leaf data hc hab hOne fullDim
    hForest hLeafLeft hZero
  have hCount : (data.vertexPartition b).blockCountWithin
      (mergedPartition data a b) background.1 = 1 := by
    have hTree' : ((data.edgePartition contracted).blockCountWithin
          (mergedPartition data a b) background.1 : ℤ) + 1 =
        ((data.vertexPartition a).blockCountWithin
            (mergedPartition data a b) background.1 : ℤ) +
          ((data.vertexPartition b).blockCountWithin
            (mergedPartition data a b) background.1 : ℤ) := hTree
    rw [hEdgeCount] at hTree'
    have : ((data.vertexPartition b).blockCountWithin
        (mergedPartition data a b) background.1 : ℤ) = 1 := by linarith
    exact_mod_cast this
  exact ⟨hCount, joinedOnBlock_of_blockCountWithin_eq_one _ _ _
    (vertexPartition_refines_mergedPartition_right data a b) hCount⟩

/-- **Right-leaf orientation.**  The mirror of
`background_edge_discrete_of_left_leaf`. -/
theorem background_edge_discrete_of_right_leaf
    (hLeafRight : (GluingDatum.incidentEdges b).card = 1)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0)
    (sheet : Fin degree) (hSheet : (mergedPartition data a b).Rel background.1 sheet) :
    (data.vertexPartition b).block sheet = {sheet} ∧
      (data.edgePartition contracted).block sheet = {sheet} := by
  classical
  have hRam : data.localRamification b ((data.vertexPartition b).toBlock sheet) = 0 :=
    (W3Nd2IncomingBackground.AnyBlock.background_localRamification_endpoints_eq_zero
      data hc hab hOne fullDim hForest hZero sheet hSheet).2
  have hRight : (data.vertexPartition b).block sheet = {sheet} := by
    rcases leaf_block_dichotomy data fullDim.valid fullDim.noDanglingTargetFibres b
        hLeafRight (fullDim.changeMinimal b) ((data.vertexPartition b).toBlock sheet) with
      ⟨_, hCard, _⟩ | ⟨_, _, hTwo, _⟩
    · refine (data.vertexPartition b).block_eq_singleton_of_blockCard_eq_one sheet ?_
      simp only [SheetPartition.toBlock_val, SheetPartition.blockCard,
        (data.vertexPartition b).block_eq_of_rel
          ((data.vertexPartition b).rel_repr_left sheet)] at hCard
      exact hCard
    · rw [hTwo] at hRam
      exact absurd hRam (by norm_num)
  refine ⟨hRight, ?_⟩
  have hRefines : (data.edgePartition contracted).Refines (data.vertexPartition b) :=
    refines_of_mem_incidentEdges data (contracted_mem_incidentEdges_right hc)
  refine Finset.Subset.antisymm ?_ ?_
  · rw [← hRight]
    intro j hj
    exact ((data.vertexPartition b).mem_block_iff _ _).mpr
      (hRefines.rel (((data.edgePartition contracted).mem_block_iff _ _).mp hj))
  · intro j hj
    rw [Finset.mem_singleton.mp hj]
    exact (data.edgePartition contracted).self_mem_block sheet

/-- The induced block counts therefore agree, right-leaf orientation. -/
theorem background_blockCountWithin_eq_of_right_leaf
    (hLeafRight : (GluingDatum.incidentEdges b).card = 1)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0) :
    (data.edgePartition contracted).blockCountWithin (mergedPartition data a b) background.1 =
      (data.vertexPartition b).blockCountWithin (mergedPartition data a b) background.1 := by
  refine blockCountWithin_congr_of_rel_on_block_local _ _ _ _
    ((refines_of_mem_incidentEdges data (contracted_mem_incidentEdges_right hc)).trans
      (vertexPartition_refines_mergedPartition_right data a b)) ?_
  intro i j hi
  refine ⟨fun h ↦ (refines_of_mem_incidentEdges data
    (contracted_mem_incidentEdges_right hc)).rel h, fun h ↦ ?_⟩
  have hBlock := (background_edge_discrete_of_right_leaf data hc hab hOne fullDim hForest
    hLeafRight hZero i hi).1
  have hMem : j ∈ ({i} : Finset (Fin degree)) := by
    rw [← hBlock]
    exact ((data.vertexPartition b).mem_block_iff i j).mpr h
  rw [Finset.mem_singleton.mp hMem]
  rfl

/-- **The whole-block census, right-leaf orientation.**  The mirror of
`background_trivalent_joined_of_left_leaf`. -/
theorem background_trivalent_joined_of_right_leaf
    (hLeafRight : (GluingDatum.incidentEdges b).card = 1)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0) :
    (data.vertexPartition a).blockCountWithin (mergedPartition data a b) background.1 = 1 ∧
      JoinedOnBlock (data.vertexPartition a) (mergedPartition data a b) background.1 := by
  have hTree := contractionForest_count data hc hForest
    (selectedMergedBlock data hc hab hOne background)
  have hEdgeCount := background_blockCountWithin_eq_of_right_leaf data hc hab hOne fullDim
    hForest hLeafRight hZero
  have hCount : (data.vertexPartition a).blockCountWithin
      (mergedPartition data a b) background.1 = 1 := by
    have hTree' : ((data.edgePartition contracted).blockCountWithin
          (mergedPartition data a b) background.1 : ℤ) + 1 =
        ((data.vertexPartition a).blockCountWithin
            (mergedPartition data a b) background.1 : ℤ) +
          ((data.vertexPartition b).blockCountWithin
            (mergedPartition data a b) background.1 : ℤ) := hTree
    rw [hEdgeCount] at hTree'
    have : ((data.vertexPartition a).blockCountWithin
        (mergedPartition data a b) background.1 : ℤ) = 1 := by linarith
    exact_mod_cast this
  exact ⟨hCount, joinedOnBlock_of_blockCountWithin_eq_one _ _ _
    (vertexPartition_refines_mergedPartition data a b) hCount⟩

end AnyBlock

end AnyBlockBackground

section Background

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  {star : ThreeStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W3SourceInput (contractDatum data hc hab hOne) star)

include fullDim hForest input

/-- **Left-divalent orientation.**  On a background wall block, *every*
occurrence at the divalent original endpoint carries exactly the endpoint's own
sheet relation.  In particular the contracted occurrence does. -/
theorem background_edge_rel_iff_of_left_divalent
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hBackground : background ≠ input.distinguishedBlock)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges a)
    (first second : Fin degree)
    (hFirst : (mergedPartition data a b).Rel background.1 first) :
    (data.edgePartition edge).Rel first second ↔
      (data.vertexPartition a).Rel first second :=
  AnyBlock.background_edge_rel_iff_of_left_divalent data hc hab hOne fullDim hForest
    hLeftDivalent (input.localRamification_eq_zero_of_ne hBackground) edge hEdge first second
    hFirst

/-- The induced block counts therefore agree. -/
theorem background_blockCountWithin_eq_of_left_divalent
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hBackground : background ≠ input.distinguishedBlock)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges a) :
    (data.edgePartition edge).blockCountWithin (mergedPartition data a b) background.1 =
      (data.vertexPartition a).blockCountWithin (mergedPartition data a b) background.1 :=
  AnyBlock.background_blockCountWithin_eq_of_left_divalent data hc hab hOne fullDim hForest
    hLeftDivalent (input.localRamification_eq_zero_of_ne hBackground) edge hEdge

/-- **The whole-block census of a background block, left-divalent
orientation.**  The forest identity turns the previous count equality into a
*single* block of the trivalent endpoint partition on the whole background
block: `vertexPartition b` is joined there. -/
theorem background_trivalent_joined_of_left_divalent
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hBackground : background ≠ input.distinguishedBlock) :
    (data.vertexPartition b).blockCountWithin (mergedPartition data a b) background.1 = 1 ∧
      JoinedOnBlock (data.vertexPartition b) (mergedPartition data a b) background.1 :=
  AnyBlock.background_trivalent_joined_of_left_divalent data hc hab hOne fullDim hForest
    hLeftDivalent (input.localRamification_eq_zero_of_ne hBackground)

/-- **Right-divalent orientation.**  The mirror of
`background_edge_rel_iff_of_left_divalent`. -/
theorem background_edge_rel_iff_of_right_divalent
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hBackground : background ≠ input.distinguishedBlock)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges b)
    (first second : Fin degree)
    (hFirst : (mergedPartition data a b).Rel background.1 first) :
    (data.edgePartition edge).Rel first second ↔
      (data.vertexPartition b).Rel first second :=
  AnyBlock.background_edge_rel_iff_of_right_divalent data hc hab hOne fullDim hForest
    hRightDivalent (input.localRamification_eq_zero_of_ne hBackground) edge hEdge first second
    hFirst

/-- The induced block counts therefore agree. -/
theorem background_blockCountWithin_eq_of_right_divalent
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hBackground : background ≠ input.distinguishedBlock)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges b) :
    (data.edgePartition edge).blockCountWithin (mergedPartition data a b) background.1 =
      (data.vertexPartition b).blockCountWithin (mergedPartition data a b) background.1 :=
  AnyBlock.background_blockCountWithin_eq_of_right_divalent data hc hab hOne fullDim hForest
    hRightDivalent (input.localRamification_eq_zero_of_ne hBackground) edge hEdge

/-- **The whole-block census of a background block, right-divalent
orientation.** -/
theorem background_trivalent_joined_of_right_divalent
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hBackground : background ≠ input.distinguishedBlock) :
    (data.vertexPartition a).blockCountWithin (mergedPartition data a b) background.1 = 1 ∧
      JoinedOnBlock (data.vertexPartition a) (mergedPartition data a b) background.1 :=
  AnyBlock.background_trivalent_joined_of_right_divalent data hc hab hOne fullDim hForest
    hRightDivalent (input.localRamification_eq_zero_of_ne hBackground)

/-- **The r0 background whole-block census at a `(2,3)` incoming W3 nd2 wall.**

For an arbitrary background wall block, in whichever of the two literal
orientations `W3Nd2IncomingTargetPlacement.endpoint_valencies` supplies:

* at the **divalent** original endpoint every incident occurrence -- the
  contracted one and both retained ones -- carries exactly that endpoint's own
  sheet relation on the whole block;
* the **trivalent** original endpoint partition is `JoinedOnBlock`: the entire
  background block is one sheet class there.

This is the whole-block statement the vertex-level dichotomy of
`W3Nd2IncomingBackground` deliberately stopped short of, and it is *not* the
M11 shape.  `M11IncomingBackground` classifies each of the three partitions as
`JoinedOnBlock` or `DiscreteOnBlock`; no such flag is proved here for the
divalent side, whose source vertices may be the dangling singletons and the
non-dangling valency-two vertices of
`W3Nd2IncomingBackground.background_divalent_dichotomy` in any mixture.  What
is proved -- and what a representative-matching step actually consumes -- is the
pair above: an *equality of relations* on the divalent side and a *join* on the
trivalent side.  No singleton-background hypothesis is
used, and the divalent-side clause is an equality of relations rather than a
classification, so nothing here presumes a block shape. -/
theorem background_whole_block_census
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hBackground : background ≠ input.distinguishedBlock) :
    ((GluingDatum.incidentEdges a).card = 2 ∧ (GluingDatum.incidentEdges b).card = 3 ∧
        (∀ edge ∈ GluingDatum.incidentEdges a, ∀ first second : Fin degree,
            (mergedPartition data a b).Rel background.1 first →
            ((data.edgePartition edge).Rel first second ↔
              (data.vertexPartition a).Rel first second)) ∧
        JoinedOnBlock (data.vertexPartition b) (mergedPartition data a b) background.1 ∧
        (data.vertexPartition b).blockCountWithin
          (mergedPartition data a b) background.1 = 1) ∨
      ((GluingDatum.incidentEdges a).card = 3 ∧ (GluingDatum.incidentEdges b).card = 2 ∧
        (∀ edge ∈ GluingDatum.incidentEdges b, ∀ first second : Fin degree,
            (mergedPartition data a b).Rel background.1 first →
            ((data.edgePartition edge).Rel first second ↔
              (data.vertexPartition b).Rel first second)) ∧
        JoinedOnBlock (data.vertexPartition a) (mergedPartition data a b) background.1 ∧
        (data.vertexPartition a).blockCountWithin
          (mergedPartition data a b) background.1 = 1) :=
  AnyBlock.background_whole_block_census data hc hab hOne fullDim hForest star
    (input.localRamification_eq_zero_of_ne hBackground)

/-! ### Sheet-level form, as a later paste comparison consumes it -/

/-- **Left-divalent orientation, read at sheets rather than at blocks.**  Away
from the distinguished wall class, the divalent endpoint partition and the
contracted-occurrence partition have the same relation, and the trivalent
endpoint partition relates every pair of the merged class.  This is exactly the
local comparison a blockwise resolution asks for off the selected block. -/
theorem background_relations_of_left_divalent
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    (first second : Fin degree)
    (hOff : ¬ (mergedPartition data a b).Rel input.distinguishedBlock.1 first)
    (hMerged : (mergedPartition data a b).Rel first second) :
    ((data.edgePartition contracted).Rel first second ↔
        (data.vertexPartition a).Rel first second) ∧
      (data.vertexPartition b).Rel first second := by
  have hBackground : WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ first ≠
      input.distinguishedBlock := by
    intro hEq
    apply hOff
    rw [← contractDatum_vertexPartition_merge data hc hab hOne]
    exact (WallBlock.ofSheet_eq_iff_rel (contractDatum data hc hab hOne) ⟨a, hab⟩ _ first).mp hEq
  exact AnyBlock.background_relations_of_left_divalent data hc hab hOne fullDim hForest
    hLeftDivalent first second (input.localRamification_eq_zero_of_ne hBackground) hMerged

/-- **Right-divalent orientation, read at sheets.**  The mirror of
`background_relations_of_left_divalent`. -/
theorem background_relations_of_right_divalent
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2)
    (first second : Fin degree)
    (hOff : ¬ (mergedPartition data a b).Rel input.distinguishedBlock.1 first)
    (hMerged : (mergedPartition data a b).Rel first second) :
    ((data.edgePartition contracted).Rel first second ↔
        (data.vertexPartition b).Rel first second) ∧
      (data.vertexPartition a).Rel first second := by
  have hBackground : WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ first ≠
      input.distinguishedBlock := by
    intro hEq
    apply hOff
    rw [← contractDatum_vertexPartition_merge data hc hab hOne]
    exact (WallBlock.ofSheet_eq_iff_rel (contractDatum data hc hab hOne) ⟨a, hab⟩ _ first).mp hEq
  exact AnyBlock.background_relations_of_right_divalent data hc hab hOne fullDim hForest
    hRightDivalent first second (input.localRamification_eq_zero_of_ne hBackground) hMerged

end Background

/-! ## The selected block, complementing the background census -/

section Selected

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd2Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

include fullDim hForest hCompat profile

/-- **The selected block is the exact mirror of a background block.**  Figure
31's ramified endpoint carries the entire merged wall class `A_0`, so one of the
two original endpoint partitions is `JoinedOnBlock` on the *distinguished*
block.  Together with `background_whole_block_census` this gives the whole-block
picture at a `(2,3)` incoming wall: on every wall block at least one endpoint
partition is joined, and on a background block it is the trivalent one.  Which
endpoint is the ramified one here is the `M^{(1)}`/`M^{(2)}` dichotomy, so it is
reported as a disjunction rather than fixed. -/
theorem selected_endpoint_joined :
    JoinedOnBlock (data.vertexPartition a) (mergedPartition data a b)
        (W3Nd2IncomingSelectedCensus.selectedBlock data hc hab hOne star input).1 ∨
      JoinedOnBlock (data.vertexPartition b) (mergedPartition data a b)
        (W3Nd2IncomingSelectedCensus.selectedBlock data hc hab hOne star input).1 := by
  classical
  obtain ⟨_, ramified, unramified, _, _, _, hPair, _, _, _, _, _, _, hRamClass⟩ :=
    W3Nd2IncomingSheetClasses.selected_sheet_classes data hc hab hOne fullDim hForest hCompat
      star input profile
  have hCases : ramified =
        W3Nd2IncomingSelectedCensus.smallEndpoint data hc hab hOne star input profile ∨
      ramified =
        W3Nd2IncomingSelectedCensus.largeEndpoint data hc hab hOne star input profile := by
    have hMem : ramified ∈
        ({W3Nd2IncomingSelectedCensus.smallEndpoint data hc hab hOne star input profile,
          W3Nd2IncomingSelectedCensus.largeEndpoint data hc hab hOne star input profile} :
            Finset data.SourceVertex) := by
      rw [← hPair]
      exact Finset.mem_insert_self ramified {unramified}
    rcases Finset.mem_insert.mp hMem with hEq | hEq
    · exact Or.inl hEq
    · exact Or.inr (Finset.mem_singleton.mp hEq)
  have hSide : ∀ edge : (contractDatum data hc hab hOne).SourceEdge,
      (W4IncomingRetainedFlags.endpoint data hc hab hOne edge).1.1 = a ∨
        (W4IncomingRetainedFlags.endpoint data hc hab hOne edge).1.1 = b := by
    intro edge
    cases hValue : IncomingTargetExpansion.right hc hab hOne edge.1.1
    · exact Or.inl
        (W3Nd2IncomingSheetClasses.endpoint_target_of_false data hc hab hOne edge hValue)
    · exact Or.inr
        (W3Nd2IncomingSheetClasses.endpoint_target_of_true data hc hab hOne edge hValue)
  have hTarget : ramified.1.1 = a ∨ ramified.1.1 = b := by
    rcases hCases with hEq | hEq
    · rw [hEq]
      exact hSide profile.small.1
    · rw [hEq]
      exact hSide profile.large.1
  rcases hTarget with hEq | hEq
  · exact Or.inl (joinedOnBlock_of_block_eq_local _ _ _ ramified.1.2
      ((congrArg (fun place : target.V ↦
        (data.vertexPartition place).block ramified.1.2) hEq).symm.trans hRamClass))
  · exact Or.inr (joinedOnBlock_of_block_eq_local _ _ _ ramified.1.2
      ((congrArg (fun place : target.V ↦
        (data.vertexPartition place).block ramified.1.2) hEq).symm.trans hRamClass))

end Selected

/-! ## Stored-representative normalization -/

section Normalization

open Utilities GluingTransport

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {outgoing : CFGraph}
  (data : GluingDatum target degree)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (iso : CFGraphIso target outgoing) (other : GluingDatum outgoing degree)
  (hVertices : ∀ vertex, ((transport iso data).vertexPartition vertex).SameBlocks
    (other.vertexPartition vertex))
  (hEdges : ∀ edge, ((transport iso data).edgePartition edge).SameBlocks
    (other.edgePartition edge))

include fullDim hVertices hEdges

/-- **Relations to stored data.**  Once every transported vertex and occurrence
partition of the incoming datum has the same *blocks* as the comparison datum,
the within-block representative transpositions of
`Infrastructure.PartitionNormalization` turn that into literal equality of the
stored representative tables, and carry the honest full-dimensional
presentation across in the original coordinates.

The three recorded clauses are exactly what forbids a hidden identification:
the target-edge labelling is the original one composed with the actual
occurrence map, every entry of the length matrix is unchanged (not merely its
determinant or its sign), and each surviving source occurrence is sent to the
occurrence with the *same* target occurrence and the *same* sheet, taken with
the comparison datum's own representative.  No stable-row bijection is chosen
from a cardinality, and no incoming classification is used: the two `SameBlocks`
families are the only inputs beyond the original presentation. -/
theorem exists_normalized_presentation :
    ∃ relabeling : (transport iso data).SheetRelabeling,
      relabeling.apply = other ∧
      ∃ presentation : FullDimensionalSourcePresentation other coordinate,
        presentation.labelling.targetEdge =
            fullDim.labelling.targetEdge.trans (edgeEquiv iso) ∧
          GluingDatum.LengthMatrixPresentation.matrix presentation.labelling.presentation =
            GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation ∧
          (∀ edge : NonDanglingEdge data,
            (TargetPartitionNormalization.nonDanglingEdgeEquiv iso data other hVertices hEdges
              fullDim.valid.1 edge).1.1 =
              (edgeEquiv iso edge.1.1.1,
                (other.edgePartition (edgeEquiv iso edge.1.1.1)).repr edge.1.1.2)) ∧
          ∀ (path : StablePath data) (edge : target.edges),
            StableSourceMatrix.matrix other
                (TargetPartitionNormalization.stablePathEquiv iso data other hVertices hEdges
                  fullDim.valid.1 path) (edgeEquiv iso edge) =
              StableSourceMatrix.matrix data path edge :=
  ⟨PartitionNormalization.sheetRelabeling (transport iso data) other hVertices hEdges,
    PartitionNormalization.sheetRelabeling_apply (transport iso data) other hVertices hEdges,
    TargetPartitionNormalization.presentation iso data other hVertices hEdges fullDim,
    TargetPartitionNormalization.presentation_targetEdge iso data other hVertices hEdges fullDim,
    TargetPartitionNormalization.presentation_matrix_eq iso data other hVertices hEdges fullDim,
    TargetPartitionNormalization.nonDanglingEdgeEquiv_val iso data other hVertices hEdges
      fullDim.valid.1,
    TargetPartitionNormalization.matrix_map iso data other hVertices hEdges fullDim.valid.1⟩

end Normalization

end DraismaVargas.LocalCases.W3Nd2IncomingNormalization
