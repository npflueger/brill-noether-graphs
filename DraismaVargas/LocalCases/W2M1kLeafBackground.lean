module

public import DraismaVargas.LocalCases.W2M1kIncomingMatching

@[expose] public section

/-!
# The `r = 0` background census at a `(1, 3)` incoming `w2M1k` wall

Source: Draisma--Vargas Part I, remark *change-minimal leaves*
(`rem-leaves-min-change`), read at Base I.a of Figure 33 exactly as
`W2M1kIncomingCensus` §6 reads `{w3-r0}` at the two `T_2` members.

## What this module proves

`W2M1kIncomingMatching` carries two named hypotheses.  The first,
`SelectedCensus`, is the irreducibly per-case selected-block analysis
(`W2M1kSelectedCensus`).  The second, `LeafBackgroundCensus`, is **not**
per-case: it is the `r = 0` background census at a wall whose two restored
endpoints have valencies `(1, 3)`.  The `AnyBlock` background lemmas of
`W3Nd2IncomingNormalization` cover that case through their `_of_left_leaf` /
`_of_right_leaf` group, beside the `_of_divalent` one, and this module uses
them: `leafBackgroundCensus` inhabits `W2M1kIncomingMatching.LeafBackgroundCensus`
at `leafEnd` / `branchEnd` from the standing bundle alone (`fullDim`,
`hForest`, the wall input and its profile, and the leaf disjunction
`(GluingDatum.incidentEdges a).card = 1 ∨ (GluingDatum.incidentEdges b).card
= 1`).

Nothing here is a new assumption, and no background clause is assumed: the
vanishing of local ramification off the distinguished block is
`W2RankObstructions.other_localRamification_eq_zero` at the profile's own
`ramification` field, so the wall input and profile already in the bundle
supply it.

## The argument, in one paragraph

At a change-minimal leaf `v` every source block above `v` is either a dangling
single sheet of vanishing local ramification, or *the* block of local degree two
and local ramification two (`StableLocalProperties.leaf_block_dichotomy`, the
formal form of Part I's remark).  A background wall block has vanishing local
ramification at the merged wall, and forest additivity descends that to both
original endpoints at every sheet of the block
(`W3Nd2IncomingBackground.AnyBlock.background_localRamification_endpoints_eq_zero`),
so the second alternative never occurs there: the leaf partition is discrete off
`A₀`, and so is the contracted occurrence's, which refines it.  Those are the
`left` and `new` clauses.  The `right` clause is then a *consequence*, not an
input: the contracted occurrence and the leaf induce the same count on the
block, so the contraction-forest identity `e + 1 = p + q` forces `q = 1` at the
trivalent endpoint, which is therefore joined there
(`W3Nd2IncomingNormalization.AnyBlock.background_trivalent_joined_of_left_leaf`).

## Orientation

`W2M1kIncomingCensus.leafEnd` is the monovalent restored endpoint and
`branchEnd` the trivalent one, in whichever of the two orders `(a, b)` happens
to realise them; `leafEnd_card_one` and `leaf_ends_cases` turn the disjunction
into the named orientation, and §1 below proves the census in each of the two
concrete orientations.
-/

namespace DraismaVargas.LocalCases.W2M1kLeafBackground

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open FullDimensionalSource WallDegeneration
open TargetExpansion
open W2M1kSourceCandidates
open W2M1kIncomingCensus
open W2M1kIncomingMatching (LeafBackgroundCensus SelectedCensus leafSelected)

/-! ## §1  The census in each concrete orientation -/

section Orientations

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  {block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}

include fullDim hForest

/-- **Left-leaf orientation, `left` and `new`.**  Off the distinguished class the
target leaf's partition and the contracted occurrence's are both discrete. -/
theorem background_leaf_discrete_left
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeafLeft : (GluingDatum.incidentEdges a).card = 1)
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel block.1 sheet) :
    (data.vertexPartition a).block sheet = {sheet} ∧
      (data.edgePartition contracted).block sheet = {sheet} :=
  W3Nd2IncomingNormalization.AnyBlock.background_edge_discrete_of_left_leaf
    data hc hab hOne fullDim hForest hLeafLeft
    (hBackground _ (ofSheet_ne_block data hc hab hOne hOff)) sheet
    (merged_rel_ofSheet data hc hab hOne sheet)

/-- **Right-leaf orientation, `left` and `new`.**  The mirror of
`background_leaf_discrete_left`. -/
theorem background_leaf_discrete_right
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeafRight : (GluingDatum.incidentEdges b).card = 1)
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel block.1 sheet) :
    (data.vertexPartition b).block sheet = {sheet} ∧
      (data.edgePartition contracted).block sheet = {sheet} :=
  W3Nd2IncomingNormalization.AnyBlock.background_edge_discrete_of_right_leaf
    data hc hab hOne fullDim hForest hLeafRight
    (hBackground _ (ofSheet_ne_block data hc hab hOne hOff)) sheet
    (merged_rel_ofSheet data hc hab hOne sheet)

/-- **Left-leaf orientation, `right`.**  The trivalent endpoint carries the whole
wall block off the distinguished class.  This is a consequence of the two
discreteness statements through the contraction-forest identity, not a further
input. -/
theorem background_branch_joined_of_left_leaf
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeafLeft : (GluingDatum.incidentEdges a).card = 1)
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel block.1 sheet) :
    (data.vertexPartition b).block sheet = (mergedPartition data a b).block sheet := by
  have hJoined := (W3Nd2IncomingNormalization.AnyBlock.background_trivalent_joined_of_left_leaf
    data hc hab hOne fullDim hForest hLeafLeft
    (hBackground _ (ofSheet_ne_block data hc hab hOne hOff))).2
  have hRel := merged_rel_ofSheet data hc hab hOne sheet
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact ⟨fun h ↦ (vertexPartition_refines_mergedPartition_right data a b).rel h,
    fun h ↦ hJoined sheet other hRel (hRel.trans h)⟩

/-- **Right-leaf orientation, `right`.**  The mirror of
`background_branch_joined_of_left_leaf`. -/
theorem background_branch_joined_of_right_leaf
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeafRight : (GluingDatum.incidentEdges b).card = 1)
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel block.1 sheet) :
    (data.vertexPartition a).block sheet = (mergedPartition data a b).block sheet := by
  have hJoined := (W3Nd2IncomingNormalization.AnyBlock.background_trivalent_joined_of_right_leaf
    data hc hab hOne fullDim hForest hLeafRight
    (hBackground _ (ofSheet_ne_block data hc hab hOne hOff))).2
  have hRel := merged_rel_ofSheet data hc hab hOne sheet
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact ⟨fun h ↦ (vertexPartition_refines_mergedPartition data a b).rel h,
    fun h ↦ hJoined sheet other hRel (hRel.trans h)⟩

/-- The census in the `leafEnd = a` orientation. -/
theorem leafBackgroundCensus_left
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeafLeft : (GluingDatum.incidentEdges a).card = 1) :
    LeafBackgroundCensus data hc hab hOne block a b where
  left sheet hOff :=
    (background_leaf_discrete_left data hc hab hOne fullDim hForest hBackground
      hLeafLeft sheet hOff).1
  right sheet hOff :=
    background_branch_joined_of_left_leaf data hc hab hOne fullDim hForest hBackground
      hLeafLeft sheet hOff
  new sheet hOff :=
    (background_leaf_discrete_left data hc hab hOne fullDim hForest hBackground
      hLeafLeft sheet hOff).2

/-- The census in the `leafEnd = b` orientation. -/
theorem leafBackgroundCensus_right
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeafRight : (GluingDatum.incidentEdges b).card = 1) :
    LeafBackgroundCensus data hc hab hOne block b a where
  left sheet hOff :=
    (background_leaf_discrete_right data hc hab hOne fullDim hForest hBackground
      hLeafRight sheet hOff).1
  right sheet hOff :=
    background_branch_joined_of_right_leaf data hc hab hOne fullDim hForest hBackground
      hLeafRight sheet hOff
  new sheet hOff :=
    (background_leaf_discrete_right data hc hab hOne fullDim hForest hBackground
      hLeafRight sheet hOff).2

end Orientations


/-! ## §2  The census at `leafEnd` and `branchEnd`, from the standing bundle -/

section Census

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W2SourceInput (contractDatum data hc hab hOne) star)
  {block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (profile : W2R2SourceProfile.SourceProfile (contractDatum data hc hab hOne) star block)

include fullDim hForest input profile

/-- **`W2M1kIncomingMatching.LeafBackgroundCensus`, proved.**  The second of the
two named hypotheses of `W2M1kIncomingMatching` is discharged from the standing
bundle: the
wall input and its ramification-two profile give the background blocks vanishing
local ramification, and the `(1, 3)` `AnyBlock` group does the rest. -/
theorem leafBackgroundCensus
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1) :
    LeafBackgroundCensus data hc hab hOne block (leafEnd hc hab hOne star)
      (branchEnd hc hab hOne star) := by
  have hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0 :=
    fun other hNe ↦ W2RankObstructions.other_localRamification_eq_zero input block
      profile.ramification other hNe
  have hCard := leafEnd_card_one hc hab hOne star hLeaf
  rcases leaf_ends_cases hc hab hOne star with ⟨hLeafE, hBranchE⟩ | ⟨hLeafE, hBranchE⟩
  · rw [hLeafE] at hCard
    rw [hLeafE, hBranchE]
    exact leafBackgroundCensus_left data hc hab hOne fullDim hForest hBackground hCard
  · rw [hLeafE] at hCard
    rw [hLeafE, hBranchE]
    exact leafBackgroundCensus_right data hc hab hOne fullDim hForest hBackground hCard

end Census


end DraismaVargas.LocalCases.W2M1kLeafBackground
