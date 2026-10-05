module

public import DraismaVargas.LocalCases.NonTrivalentValencyFourKZero

@[expose] public section

/-!
# The general-`K` local wall resolution at a four-valent wall

Vargas, Part II (arXiv:2609.09109), case `{v4-nd4}` of the section on changing combinatorial
type (`subsec-case-v4`): for a prescribed `2+2` resolution of the four target branches at a
four-valent wall vertex `A`, the outgoing members are indexed by an integer `K` in the range
`0 ≤ K ≤ min(k₂-1, |A|-k₅)`, with

    |A₊| = |A| - K,   |A₋| = k_α + k_β - 1 - K,   k₁ = k_α + k_β - 1 - 2K.

Part I's construction
`NonTrivalentValencyFourKZero.PrescribedPairing.selectedResolution` builds only
the `K = 0` member.  Two things are special to `K = 0` there and stop being
available for `K > 0`:

1. **Only one endpoint is refined.**  At `K = 0` we have `|A₊| = |A|`, so
   `endpointForSide` can hand the non-smaller side the untouched wall
   partition.  For `K > 0` *both* endpoints are proper refinements of the wall
   partition on the anchor block.
2. **`newEdge = left` stops being possible.**  At `K = 0` the new edge is the
   finer endpoint itself, so `blockCountWithin newEdge left = 1` holds by
   `blockCountWithin_self`.  For `K > 0` the new edge must be *strictly* finer
   than both endpoints on the selected blocks, with `K+1` blocks inside `A₋`.

`ResolutionCoarseFine.fineResolution` only builds the "new edge = the finer
endpoint" shape, so this file supplies the missing `LocalResolution`
constructor together with its two `Refines` receipts, its contraction receipt
and its two selected-block Riemann--Hurwitz inequalities.

## The construction

`SplitData coarse anchor` is the combinatorial input: the two endpoint sheet
sets `A₋` and `A₊` inside one block of the wall partition, a sheet `bridge`
common to both, and the receipt `A₋ ∪ A₊ = A`.  From it,

* `left`   refines the anchor block to `A₋`, singletons elsewhere in it;
* `right`  refines the anchor block to `A₊`, singletons elsewhere in it;
* `newEdge` refines it to `A₋ ∩ A₊`, singletons elsewhere in it.

All three are `PrescribedPairing.withSelectedBlock` at the same representative,
which is why the two `Refines` receipts are available and why the join of the
two endpoints is again the wall partition.

`K` is `(A₋ \ A₊).card` and `coK` is `(A₊ \ A₋).card`; the paper's `k₁` is
`(A₋ ∩ A₊).card`.  At `K = 0` the construction degenerates to Part I's:
`A₊ = A` (`plusSheets_eq_block_of_K_eq_zero`) and the new edge is `left`.

## Two traps, both recorded because they are easy to walk into

* **`K + 1` counts *all* new-edge blocks inside `A₋`, dangling ones included.**
  `newEdge_blockCountWithin_left_eq` below is a statement about
  `blockCountWithin`, i.e. about induced blocks of a sheet partition.  It is
  *not* a count of non-dangling occurrences of the regrown edge `e₁`, and it is
  not the uniqueness statement for `e₁` at the start of Part II's case `{v4-nd4}`: the
  block count can be `2` while `k₁ = 1` and the non-dangling occurrence at `A₋` is
  unique.  Nothing in this file says anything about dangling occurrences.
* **`K` is not sheet-independent.**  `blockCountWithin newEdge left sheet` takes
  different values at different sheets of the *same* wall block (the `K` it reads off can
  be `1` at two sheets of a block and `0` at a third; see
  `newEdge_blockCountWithin_left_eq_one`).  Every
  statement about `K` below is therefore anchored at the field `SplitData.bridge`, which
  is the sheet witness, and transported to other sheets only along
  `left.Rel bridge sheet` (equivalently `sheet ∈ A₋`).  There is no
  unquantified-sheet form of `K` in this file, deliberately.

## The gauge hypothesis

This file takes the gauge as a hypothesis, spelled out here as `OverlapGauge`:

    OverlapGauge whole first second overlap :=
      ∃ σ : Equiv.Perm (Fin degree),
        (σ preserves `whole`) ∧ (σ fixes everything outside `whole`) ∧
        (first ∩ second.image σ).card = overlap

which is `PrescribedPairing.exists_overlap_gauge` with the literal `1` replaced by
`overlap`.  What is needed is, for the two branch blocks on one side of the
prescribed pairing, `OverlapGauge (wall block) e_α e_β (K+1)` under the
feasibility conditions `K+1 ≤ min(k_α,k_β)` and `k_α+k_β ≤ |A| + (K+1)`.

Two further inputs are hypotheses of `exists_splitData_of_gauged_sides`:

* the two per-side cardinalities `|A₋| + coK = |A|` and `|A₊| + K = |A|`
  (the paper's `|A₊| = |A| - K` and its mirror), and
* the **joint** condition `|A₋ ∩ A₊| + K + coK = |A|`.  No single-side branch
  swap can see this one: it is the statement that the two independently gauged
  sides together exhaust the wall block.  The two swaps themselves commute,
  being supported on disjoint components of `T \ wall` (the branch swaps of Part I,
  `subsection-isomorphism-classes-of-dtmors`), so gauging the two sides simultaneously is
  bookkeeping; making their *union* the whole block is not.

`SplitData.ofCards` shows that `A₋ ∪ A₊ = A` is then *derived*, not assumed.

All of these inputs are proved in `Count/GeneralKReceipts.lean`.  The overlap gauge is
`BlockPreservingOverlap.exists_perm_image_inter_card_eq`, and the per-side cardinalities and
the joint condition come from gauging the first class and moving the other three by
block-preserving permutations at once (`GeneralKReceipts.exists_joint_gauge`,
`exists_splitData_of_joint_gauge`, `exists_gauged_splitData`).  Gauging only each side's
second class cannot reach the joint condition in general
(`GeneralKReceipts.fy_pairingII_single_side_fails`).
-/

namespace DraismaVargas.LocalCases.GeneralKResolution

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing

variable {degree : ℕ}

/-! ## 1.  The combinatorial input -/

/-- The two endpoint sheet sets of a general-`K` resolution inside one block of
the wall partition, together with a common sheet naming their intersection.
`minusSheets` is the paper's `A₋` (retained endpoint) and `plusSheets` is `A₊`
(fresh endpoint). -/
structure SplitData (coarse : SheetPartition degree) (anchor : Fin degree) where
  /-- A sheet lying in both endpoint blocks.  It is the *sheet witness* every
  statement about `K` is anchored at; see the module docstring. -/
  bridge : Fin degree
  /-- The paper's `A₋`. -/
  minusSheets : Finset (Fin degree)
  /-- The paper's `A₊`. -/
  plusSheets : Finset (Fin degree)
  bridge_mem_minus : bridge ∈ minusSheets
  bridge_mem_plus : bridge ∈ plusSheets
  /-- The two endpoint blocks exhaust the wall block. -/
  union_eq : minusSheets ∪ plusSheets = coarse.block anchor

namespace SplitData

variable {coarse : SheetPartition degree} {anchor : Fin degree}
  (split : SplitData coarse anchor)

theorem minus_subset : split.minusSheets ⊆ coarse.block anchor := by
  rw [← split.union_eq]
  exact Finset.subset_union_left

theorem plus_subset : split.plusSheets ⊆ coarse.block anchor := by
  rw [← split.union_eq]
  exact Finset.subset_union_right

/-- The new edge's distinguished class, `A₋ ∩ A₊`.  Its cardinality is the
paper's `k₁`. -/
def bridgeSheets : Finset (Fin degree) := split.minusSheets ∩ split.plusSheets

theorem bridge_mem_bridgeSheets : split.bridge ∈ split.bridgeSheets :=
  Finset.mem_inter.mpr ⟨split.bridge_mem_minus, split.bridge_mem_plus⟩

theorem bridgeSheets_subset_minus : split.bridgeSheets ⊆ split.minusSheets :=
  Finset.inter_subset_left

theorem bridgeSheets_subset_plus : split.bridgeSheets ⊆ split.plusSheets :=
  Finset.inter_subset_right

theorem bridgeSheets_subset : split.bridgeSheets ⊆ coarse.block anchor :=
  split.bridgeSheets_subset_minus.trans split.minus_subset

/-- The paper's `K`, as a function of the split **and its anchor**.  It is the
number of sheets of `A₋` that the fresh endpoint does not retain. -/
def K : ℕ := (split.minusSheets \ split.plusSheets).card

/-- The mirror of `K` at the fresh endpoint: `|A| - |A₋|`. -/
def coK : ℕ := (split.plusSheets \ split.minusSheets).card

theorem bridgeSheets_card_add_K :
    split.bridgeSheets.card + split.K = split.minusSheets.card :=
  Finset.card_inter_add_card_sdiff _ _

theorem bridgeSheets_card_add_coK :
    split.bridgeSheets.card + split.coK = split.plusSheets.card := by
  have h := Finset.card_inter_add_card_sdiff split.plusSheets split.minusSheets
  rw [Finset.inter_comm] at h
  exact h

theorem card_minus_add_card_plus :
    split.minusSheets.card + split.plusSheets.card
      = coarse.blockCard anchor + split.bridgeSheets.card := by
  have h := Finset.card_union_add_card_inter split.minusSheets split.plusSheets
  rw [split.union_eq] at h
  exact h.symm

/-- The paper's `|A₊| = |A| - K`. -/
theorem card_plus_add_K : split.plusSheets.card + split.K = coarse.blockCard anchor := by
  have hUnion := split.card_minus_add_card_plus
  have hK := split.bridgeSheets_card_add_K
  omega

/-- The mirror `|A₋| = |A| - K'`. -/
theorem card_minus_add_coK : split.minusSheets.card + split.coK = coarse.blockCard anchor := by
  have hUnion := split.card_minus_add_card_plus
  have hcoK := split.bridgeSheets_card_add_coK
  omega

/-- `k₁ + K + K' = |A|`. -/
theorem card_bridgeSheets_add :
    split.bridgeSheets.card + split.K + split.coK = coarse.blockCard anchor := by
  have hK := split.bridgeSheets_card_add_K
  have hMinus := split.card_minus_add_coK
  omega

/-! ## 2.  The three partitions -/

/-- The retained endpoint: the wall partition refined on the anchor block to
`A₋`, with singleton classes on the rest of that block. -/
def left : SheetPartition degree :=
  withSelectedBlock coarse anchor split.bridge split.minusSheets
    split.bridge_mem_minus split.minus_subset

/-- The fresh endpoint: the wall partition refined on the anchor block to
`A₊`. -/
def right : SheetPartition degree :=
  withSelectedBlock coarse anchor split.bridge split.plusSheets
    split.bridge_mem_plus split.plus_subset

/-- The new edge: the wall partition refined on the anchor block to `A₋ ∩ A₊`.
For `K > 0` this is strictly finer than both endpoints. -/
def newEdge : SheetPartition degree :=
  withSelectedBlock coarse anchor split.bridge split.bridgeSheets
    split.bridge_mem_bridgeSheets split.bridgeSheets_subset

theorem left_block_bridge : split.left.block split.bridge = split.minusSheets :=
  withSelectedBlock.block_representative coarse anchor split.bridge split.minusSheets
    split.bridge_mem_minus split.minus_subset

theorem right_block_bridge : split.right.block split.bridge = split.plusSheets :=
  withSelectedBlock.block_representative coarse anchor split.bridge split.plusSheets
    split.bridge_mem_plus split.plus_subset

theorem newEdge_block_bridge : split.newEdge.block split.bridge = split.bridgeSheets :=
  withSelectedBlock.block_representative coarse anchor split.bridge split.bridgeSheets
    split.bridge_mem_bridgeSheets split.bridgeSheets_subset

theorem left_blockCard_bridge :
    split.left.blockCard split.bridge = split.minusSheets.card := by
  unfold SheetPartition.blockCard
  rw [split.left_block_bridge]

theorem right_blockCard_bridge :
    split.right.blockCard split.bridge = split.plusSheets.card := by
  unfold SheetPartition.blockCard
  rw [split.right_block_bridge]

theorem newEdge_blockCard_bridge :
    split.newEdge.blockCard split.bridge = split.bridgeSheets.card := by
  unfold SheetPartition.blockCard
  rw [split.newEdge_block_bridge]

theorem left_rel_bridge_iff (sheet : Fin degree) :
    split.left.Rel split.bridge sheet ↔ sheet ∈ split.minusSheets := by
  rw [← SheetPartition.mem_block_iff, split.left_block_bridge]

theorem right_rel_bridge_iff (sheet : Fin degree) :
    split.right.Rel split.bridge sheet ↔ sheet ∈ split.plusSheets := by
  rw [← SheetPartition.mem_block_iff, split.right_block_bridge]

theorem newEdge_rel_bridge_iff (sheet : Fin degree) :
    split.newEdge.Rel split.bridge sheet ↔ sheet ∈ split.bridgeSheets := by
  rw [← SheetPartition.mem_block_iff, split.newEdge_block_bridge]

theorem left_refines_coarse : split.left.Refines coarse :=
  withSelectedBlock.refines coarse anchor split.bridge split.minusSheets
    split.bridge_mem_minus split.minus_subset

theorem right_refines_coarse : split.right.Refines coarse :=
  withSelectedBlock.refines coarse anchor split.bridge split.plusSheets
    split.bridge_mem_plus split.plus_subset

theorem newEdge_refines_coarse : split.newEdge.Refines coarse :=
  withSelectedBlock.refines coarse anchor split.bridge split.bridgeSheets
    split.bridge_mem_bridgeSheets split.bridgeSheets_subset

/-- Off the anchor block all three partitions agree with the wall partition. -/
theorem left_repr_of_not_rel {sheet : Fin degree} (hSheet : ¬coarse.Rel anchor sheet) :
    split.left.repr sheet = coarse.repr sheet :=
  withSelectedBlock.repr_of_not_rel coarse anchor split.bridge split.minusSheets
    split.bridge_mem_minus split.minus_subset hSheet

theorem left_block_of_not_mem {sheet : Fin degree}
    (hSheet : sheet ∉ split.minusSheets) (hWall : coarse.Rel anchor sheet) :
    split.left.block sheet = {sheet} :=
  withSelectedBlock.block_of_not_mem_of_rel coarse anchor split.bridge split.minusSheets
    split.bridge_mem_minus split.minus_subset hSheet hWall

theorem right_block_of_not_mem {sheet : Fin degree}
    (hSheet : sheet ∉ split.plusSheets) (hWall : coarse.Rel anchor sheet) :
    split.right.block sheet = {sheet} :=
  withSelectedBlock.block_of_not_mem_of_rel coarse anchor split.bridge split.plusSheets
    split.bridge_mem_plus split.plus_subset hSheet hWall

theorem newEdge_block_of_not_mem {sheet : Fin degree}
    (hSheet : sheet ∉ split.bridgeSheets) (hWall : coarse.Rel anchor sheet) :
    split.newEdge.block sheet = {sheet} :=
  withSelectedBlock.block_of_not_mem_of_rel coarse anchor split.bridge split.bridgeSheets
    split.bridge_mem_bridgeSheets split.bridgeSheets_subset hSheet hWall

/-- The new edge's classes inside the anchor block: the distinguished one, and
singletons. -/
theorem newEdge_shape (sheet : Fin degree) (hSheet : coarse.Rel anchor sheet) :
    sheet ∈ split.bridgeSheets ∨ split.newEdge.block sheet = {sheet} := by
  by_cases hMem : sheet ∈ split.bridgeSheets
  · exact Or.inl hMem
  · exact Or.inr (split.newEdge_block_of_not_mem hMem hSheet)

theorem bridgeSheets_closed {first second : Fin degree}
    (hFirst : first ∈ split.bridgeSheets) (hRel : split.newEdge.Rel first second) :
    second ∈ split.bridgeSheets := by
  rw [← split.newEdge_rel_bridge_iff] at hFirst ⊢
  exact hFirst.trans hRel

/-! ### The two `Refines` receipts -/

/-- **First receipt.**  The new edge refines the retained endpoint. -/
theorem newEdge_refines_left : split.newEdge.Refines split.left :=
  refines_withSelectedBlock_of_one_class coarse split.newEdge anchor split.bridge
    split.minusSheets split.bridgeSheets split.bridge_mem_minus split.minus_subset
    split.newEdge_refines_coarse split.bridgeSheets_subset_minus
    (fun _ hFirst _ hRel => split.bridgeSheets_closed hFirst hRel)
    split.newEdge_shape

/-- **Second receipt.**  The new edge refines the fresh endpoint. -/
theorem newEdge_refines_right : split.newEdge.Refines split.right :=
  refines_withSelectedBlock_of_one_class coarse split.newEdge anchor split.bridge
    split.plusSheets split.bridgeSheets split.bridge_mem_plus split.plus_subset
    split.newEdge_refines_coarse split.bridgeSheets_subset_plus
    (fun _ hFirst _ hRel => split.bridgeSheets_closed hFirst hRel)
    split.newEdge_shape

/-- **The general-`K` local resolution.**  Unlike
`ResolutionCoarseFine.fineResolution`, the new edge is a third partition,
strictly finer than both endpoints as soon as `K > 0`. -/
def resolution : LocalResolution degree where
  left := split.left
  right := split.right
  newEdge := split.newEdge
  edge_refines_left := split.newEdge_refines_left
  edge_refines_right := split.newEdge_refines_right

@[simp] theorem resolution_left : split.resolution.left = split.left := rfl

@[simp] theorem resolution_right : split.resolution.right = split.right := rfl

@[simp] theorem resolution_newEdge : split.resolution.newEdge = split.newEdge := rfl

/-! ### The contraction receipt -/

theorem eqvGen_bridge (sheet : Fin degree) (hSheet : coarse.Rel anchor sheet) :
    Relation.EqvGen (fun a b => split.left.Rel a b ∨ split.right.Rel a b)
      sheet split.bridge := by
  have hMem : sheet ∈ split.minusSheets ∪ split.plusSheets := by
    rw [split.union_eq]
    exact (coarse.mem_block_iff anchor sheet).mpr hSheet
  rcases Finset.mem_union.mp hMem with hMinus | hPlus
  · refine Relation.EqvGen.rel sheet split.bridge (Or.inl ?_)
    exact ((split.left_rel_bridge_iff sheet).mpr hMinus).symm
  · refine Relation.EqvGen.rel sheet split.bridge (Or.inr ?_)
    exact ((split.right_rel_bridge_iff sheet).mpr hPlus).symm

/-- The wall partition is the join of the two endpoint partitions.  Off the
anchor block either endpoint already is the wall partition; on it, every sheet
is joined to `bridge` through `A₋` or through `A₊`, and the two exhaust the
block. -/
theorem left_right_isJoin : SheetPartition.IsJoin split.left split.right coarse := by
  intro first second
  constructor
  · intro hRel
    by_cases hFirst : coarse.Rel anchor first
    · have hSecond : coarse.Rel anchor second := hFirst.trans hRel
      exact Relation.EqvGen.trans first split.bridge second
        (split.eqvGen_bridge first hFirst)
        (Relation.EqvGen.symm second split.bridge (split.eqvGen_bridge second hSecond))
    · have hSecond : ¬coarse.Rel anchor second := fun h => hFirst (h.trans hRel.symm)
      refine Relation.EqvGen.rel first second (Or.inl ?_)
      show split.left.Rel first second
      rw [SheetPartition.rel_iff, split.left_repr_of_not_rel hFirst,
        split.left_repr_of_not_rel hSecond]
      exact hRel
  · intro hGen
    induction hGen with
    | rel _ _ hStep =>
        exact hStep.elim split.left_refines_coarse.rel split.right_refines_coarse.rel
    | refl => rfl
    | symm => apply Eq.symm; assumption
    | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- Contracting the new edge recovers the wall partition. -/
theorem resolution_contracts : split.resolution.ContractsTo coarse :=
  split.left_right_isJoin

/-! ## 3.  The bridge counts: this is where `K` enters -/

/-- **The `K`-count at the retained endpoint.**  The new edge induces `K + 1`
classes inside `A₋`: the distinguished class `A₋ ∩ A₊`, plus one singleton for
each sheet of `A₋ \ A₊`.

Read the module docstring before consuming this: `K + 1` counts *all* induced
new-edge classes inside `A₋`, dangling occurrences included. -/
theorem newEdge_blockCountWithin_left_add :
    split.newEdge.blockCountWithin split.left split.bridge
        + split.bridgeSheets.card
      = split.minusSheets.card + 1 := by
  have hCount := blockCountWithin_add_blockCard_eq split.newEdge split.left
    split.bridge split.bridge rfl split.newEdge_refines_left
    (by
      intro sheet hSheet
      have hMinus : sheet ∈ split.minusSheets := (split.left_rel_bridge_iff sheet).mp hSheet
      have hWall : coarse.Rel anchor sheet :=
        (coarse.mem_block_iff anchor sheet).mp (split.minus_subset hMinus)
      rcases split.newEdge_shape sheet hWall with hBridge | hSingleton
      · exact Or.inl ((split.newEdge_rel_bridge_iff sheet).mpr hBridge)
      · exact Or.inr hSingleton)
  rw [split.newEdge_blockCard_bridge, split.left_blockCard_bridge] at hCount
  exact hCount

theorem newEdge_blockCountWithin_left_eq :
    split.newEdge.blockCountWithin split.left split.bridge = split.K + 1 := by
  have hCount := split.newEdge_blockCountWithin_left_add
  have hK := split.bridgeSheets_card_add_K
  omega

/-- **The `K`-count at the fresh endpoint**, the mirror across the new edge. -/
theorem newEdge_blockCountWithin_right_add :
    split.newEdge.blockCountWithin split.right split.bridge
        + split.bridgeSheets.card
      = split.plusSheets.card + 1 := by
  have hCount := blockCountWithin_add_blockCard_eq split.newEdge split.right
    split.bridge split.bridge rfl split.newEdge_refines_right
    (by
      intro sheet hSheet
      have hPlus : sheet ∈ split.plusSheets := (split.right_rel_bridge_iff sheet).mp hSheet
      have hWall : coarse.Rel anchor sheet :=
        (coarse.mem_block_iff anchor sheet).mp (split.plus_subset hPlus)
      rcases split.newEdge_shape sheet hWall with hBridge | hSingleton
      · exact Or.inl ((split.newEdge_rel_bridge_iff sheet).mpr hBridge)
      · exact Or.inr hSingleton)
  rw [split.newEdge_blockCard_bridge, split.right_blockCard_bridge] at hCount
  exact hCount

theorem newEdge_blockCountWithin_right_eq :
    split.newEdge.blockCountWithin split.right split.bridge = split.coK + 1 := by
  have hCount := split.newEdge_blockCountWithin_right_add
  have hcoK := split.bridgeSheets_card_add_coK
  omega

/-- The `K`-count transported to any sheet of `A₋`.  This is the exact
`hSub`-relative form: `K` is well defined at the sheets where the anchor's
branches attach, and only there. -/
theorem newEdge_blockCountWithin_left_eq_of_rel {sheet : Fin degree}
    (hRel : split.left.Rel split.bridge sheet) :
    split.newEdge.blockCountWithin split.left sheet = split.K + 1 := by
  rw [ContractionRamification.blockCountWithin_congr split.newEdge split.left hRel.symm]
  exact split.newEdge_blockCountWithin_left_eq

/-- The mirror at the fresh endpoint. -/
theorem newEdge_blockCountWithin_right_eq_of_rel {sheet : Fin degree}
    (hRel : split.right.Rel split.bridge sheet) :
    split.newEdge.blockCountWithin split.right sheet = split.coK + 1 := by
  rw [ContractionRamification.blockCountWithin_congr split.newEdge split.right hRel.symm]
  exact split.newEdge_blockCountWithin_right_eq

/-- **`K` is not sheet-independent.**  At a sheet of the anchor block outside
`A₋` the very same count collapses to `1`, whatever `K` is.  This is why every
statement about `K` above is anchored at `bridge` or guarded by
`left.Rel bridge sheet`. -/
theorem newEdge_blockCountWithin_left_eq_one {sheet : Fin degree}
    (hSheet : sheet ∉ split.minusSheets) (hWall : coarse.Rel anchor sheet) :
    split.newEdge.blockCountWithin split.left sheet = 1 :=
  SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton split.newEdge split.left
    sheet (split.left_block_of_not_mem hSheet hWall)

/-- The mirror outside `A₊`. -/
theorem newEdge_blockCountWithin_right_eq_one {sheet : Fin degree}
    (hSheet : sheet ∉ split.plusSheets) (hWall : coarse.Rel anchor sheet) :
    split.newEdge.blockCountWithin split.right sheet = 1 :=
  SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton split.newEdge split.right
    sheet (split.right_block_of_not_mem hSheet hWall)

/-! ### Strict refinement, and the degeneration to Part I's `K = 0` shape -/

/-- For `K > 0` the new edge is strictly finer than the retained endpoint on
the selected block. -/
theorem newEdge_blockCard_lt_left (hK : 0 < split.K) :
    split.newEdge.blockCard split.bridge < split.left.blockCard split.bridge := by
  have hCard := split.bridgeSheets_card_add_K
  rw [split.newEdge_blockCard_bridge, split.left_blockCard_bridge]
  omega

/-- For `K' > 0` the new edge is strictly finer than the fresh endpoint on the
selected block. -/
theorem newEdge_blockCard_lt_right (hcoK : 0 < split.coK) :
    split.newEdge.blockCard split.bridge < split.right.blockCard split.bridge := by
  have hCard := split.bridgeSheets_card_add_coK
  rw [split.newEdge_blockCard_bridge, split.right_blockCard_bridge]
  omega

/-- For `K > 0` the fresh endpoint is a *proper* refinement of the wall
partition on the anchor block -- this is what fails at `K = 0`, where the
construction of Part I hands that side the untouched wall partition. -/
theorem right_blockCard_lt_coarse (hK : 0 < split.K) :
    split.right.blockCard split.bridge < coarse.blockCard anchor := by
  have hCard := split.card_plus_add_K
  rw [split.right_blockCard_bridge]
  omega

/-- The retained endpoint is a proper refinement exactly when `K' > 0`. -/
theorem left_blockCard_lt_coarse (hcoK : 0 < split.coK) :
    split.left.blockCard split.bridge < coarse.blockCard anchor := by
  have hCard := split.card_minus_add_coK
  rw [split.left_blockCard_bridge]
  omega

/-- At `K = 0` the fresh endpoint retains the whole wall block, which is the
shape Part I's `K = 0` construction builds. -/
theorem plusSheets_eq_block_of_K_eq_zero (hK : split.K = 0) :
    split.plusSheets = coarse.block anchor := by
  have hCard := split.card_plus_add_K
  refine Finset.eq_of_subset_of_card_le split.plus_subset ?_
  unfold SheetPartition.blockCard at hCard
  omega

end SplitData

/-! ## 4.  The two selected-block Riemann--Hurwitz inequalities -/

/-- A sheet whose endpoint class is a singleton satisfies the Riemann--Hurwitz
inequality for free, whatever the incident occurrences are: every induced count
is `1` and the endpoint block has one sheet. -/
theorem sum_blockCountWithin_eq_length_of_block_eq_singleton
    (endpoint : SheetPartition degree) (incident : List (SheetPartition degree))
    {sheet : Fin degree} (hSingleton : endpoint.block sheet = {sheet}) :
    (incident.map fun edge => (edge.blockCountWithin endpoint sheet : ℤ)).sum
      = (incident.length : ℤ) := by
  induction incident with
  | nil => simp
  | cons head tail ih =>
      rw [List.map_cons, List.sum_cons, ih,
        SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton head endpoint
          sheet hSingleton]
      push_cast [List.length_cons]
      ring

theorem riemannHurwitz_of_block_eq_singleton
    (endpoint : SheetPartition degree) (incident : List (SheetPartition degree))
    {sheet : Fin degree} (hSingleton : endpoint.block sheet = {sheet}) :
    (incident.map fun edge => (edge.blockCountWithin endpoint sheet : ℤ)).sum - 2
      ≥ (endpoint.blockCard sheet : ℤ) * ((incident.length : ℤ) - 2) := by
  have hCard : endpoint.blockCard sheet = 1 := by
    unfold SheetPartition.blockCard
    rw [hSingleton]
    simp
  rw [sum_blockCountWithin_eq_length_of_block_eq_singleton endpoint incident hSingleton,
    hCard]
  simp

namespace SplitData

variable {coarse : SheetPartition degree} {anchor : Fin degree}
  (split : SplitData coarse anchor)

/-- **The selected-block Riemann--Hurwitz inequality at the retained
endpoint.**  The new target vertex is trivalent (a `2+2` pairing leaves two old
occurrences on each side), so the condition is that the two old occurrence
counts dominate `k₁ + 1`, where `k₁ = |A₋ ∩ A₊|` is the new edge's index.

Sheets of the anchor block outside `A₋` are handled for free: their endpoint
class is a singleton.  Only sheets of `A₋` -- exactly the sheets at which the
`K`-count is the paper's `K` -- consume the hypothesis. -/
theorem left_riemannHurwitzAtBlock
    (oldEdges : List (SheetPartition degree)) (hLength : oldEdges.length = 2)
    (hOld : ∀ sheet, split.left.Rel split.bridge sheet →
      (split.bridgeSheets.card : ℤ) + 1
        ≤ (oldEdges.map fun edge => (edge.blockCountWithin split.left sheet : ℤ)).sum)
    (block : Fin degree) (hBlock : coarse.Rel anchor block) :
    LocalResolution.RiemannHurwitzAtBlock coarse split.left
      (split.newEdge :: oldEdges) block := by
  intro sheet hSheet
  have hWall : coarse.Rel anchor sheet := hBlock.trans hSheet
  by_cases hMinus : sheet ∈ split.minusSheets
  · have hRel : split.left.Rel split.bridge sheet :=
      (split.left_rel_bridge_iff sheet).mpr hMinus
    have hCount : split.newEdge.blockCountWithin split.left sheet = split.K + 1 :=
      split.newEdge_blockCountWithin_left_eq_of_rel hRel
    have hCard : split.left.blockCard sheet = split.minusSheets.card := by
      rw [← ContractionRamification.blockCard_congr split.left hRel]
      exact split.left_blockCard_bridge
    have hSum := hOld sheet hRel
    have hK := split.bridgeSheets_card_add_K
    simp only [List.map_cons, List.sum_cons, List.length_cons, hLength, hCount, hCard]
    push_cast
    omega
  · exact riemannHurwitz_of_block_eq_singleton split.left (split.newEdge :: oldEdges)
      (split.left_block_of_not_mem hMinus hWall)

/-- **The selected-block Riemann--Hurwitz inequality at the fresh endpoint.**
The mirror of `left_riemannHurwitzAtBlock`; the bound on the old occurrence
counts is the same `k₁ + 1`. -/
theorem right_riemannHurwitzAtBlock
    (oldEdges : List (SheetPartition degree)) (hLength : oldEdges.length = 2)
    (hOld : ∀ sheet, split.right.Rel split.bridge sheet →
      (split.bridgeSheets.card : ℤ) + 1
        ≤ (oldEdges.map fun edge => (edge.blockCountWithin split.right sheet : ℤ)).sum)
    (block : Fin degree) (hBlock : coarse.Rel anchor block) :
    LocalResolution.RiemannHurwitzAtBlock coarse split.right
      (split.newEdge :: oldEdges) block := by
  intro sheet hSheet
  have hWall : coarse.Rel anchor sheet := hBlock.trans hSheet
  by_cases hPlus : sheet ∈ split.plusSheets
  · have hRel : split.right.Rel split.bridge sheet :=
      (split.right_rel_bridge_iff sheet).mpr hPlus
    have hCount : split.newEdge.blockCountWithin split.right sheet = split.coK + 1 :=
      split.newEdge_blockCountWithin_right_eq_of_rel hRel
    have hCard : split.right.blockCard sheet = split.plusSheets.card := by
      rw [← ContractionRamification.blockCard_congr split.right hRel]
      exact split.right_blockCard_bridge
    have hSum := hOld sheet hRel
    have hcoK := split.bridgeSheets_card_add_coK
    simp only [List.map_cons, List.sum_cons, List.length_cons, hLength, hCount, hCard]
    push_cast
    omega
  · exact riemannHurwitz_of_block_eq_singleton split.right (split.newEdge :: oldEdges)
      (split.right_block_of_not_mem hPlus hWall)

/-- The retained-endpoint inequality in the paper's bookkeeping: the two old
branch counts and the side index `k_α + k_β` add to `2(|A₋| + 1)` (hypothesis `hSide`),
and the side index is `|A₋| + 1 + K` (the `K`-equation; `hIndex` is its upper
bound).  Those two together give the
hypothesis of `left_riemannHurwitzAtBlock`; with `hIndex` an equality the
resulting Riemann--Hurwitz inequality holds with equality, as it must at an
unramified trivalent endpoint. -/
theorem left_riemannHurwitzAtBlock_of_sideIndex
    (oldEdges : List (SheetPartition degree)) (hLength : oldEdges.length = 2)
    (sideIndex : ℕ)
    (hSide : ∀ sheet, split.left.Rel split.bridge sheet →
      (oldEdges.map fun edge => (edge.blockCountWithin split.left sheet : ℤ)).sum
          + sideIndex
        = 2 * ((split.left.blockCard sheet : ℤ) + 1))
    (hIndex : sideIndex ≤ split.minusSheets.card + 1 + split.K)
    (block : Fin degree) (hBlock : coarse.Rel anchor block) :
    LocalResolution.RiemannHurwitzAtBlock coarse split.left
      (split.newEdge :: oldEdges) block := by
  refine split.left_riemannHurwitzAtBlock oldEdges hLength ?_ block hBlock
  intro sheet hRel
  have hCard : split.left.blockCard sheet = split.minusSheets.card := by
    rw [← ContractionRamification.blockCard_congr split.left hRel]
    exact split.left_blockCard_bridge
  have hSum := hSide sheet hRel
  rw [hCard] at hSum
  have hK := split.bridgeSheets_card_add_K
  have hIndexCast : (sideIndex : ℤ) ≤ (split.minusSheets.card : ℤ) + 1 + split.K := by
    exact_mod_cast hIndex
  omega

/-- **The layer-3 deliverable in one statement.**  The general-`K` local
resolution, its contraction receipt, its two `Refines` receipts, its two
selected-block Riemann--Hurwitz inequalities, and the two bridge counts that
identify the paper's `K` and its mirror.

For `K > 0` this is genuinely outside the reach of
`ResolutionCoarseFine.fineResolution`: the new edge is a third partition,
strictly finer than both endpoints on the selected block
(`newEdge_blockCard_lt_left`, `newEdge_blockCard_lt_right`), and both endpoints
are proper refinements of the wall partition there
(`left_blockCard_lt_coarse`, `right_blockCard_lt_coarse`). -/
theorem resolution_receipts
    (leftOld rightOld : List (SheetPartition degree))
    (hLeftLength : leftOld.length = 2) (hRightLength : rightOld.length = 2)
    (hLeftOld : ∀ sheet, split.left.Rel split.bridge sheet →
      (split.bridgeSheets.card : ℤ) + 1
        ≤ (leftOld.map fun edge => (edge.blockCountWithin split.left sheet : ℤ)).sum)
    (hRightOld : ∀ sheet, split.right.Rel split.bridge sheet →
      (split.bridgeSheets.card : ℤ) + 1
        ≤ (rightOld.map fun edge => (edge.blockCountWithin split.right sheet : ℤ)).sum)
    (block : Fin degree) (hBlock : coarse.Rel anchor block) :
    split.resolution.ContractsTo coarse ∧
      split.resolution.newEdge.Refines split.resolution.left ∧
      split.resolution.newEdge.Refines split.resolution.right ∧
      LocalResolution.RiemannHurwitzAtBlock coarse split.resolution.left
        (split.resolution.newEdge :: leftOld) block ∧
      LocalResolution.RiemannHurwitzAtBlock coarse split.resolution.right
        (split.resolution.newEdge :: rightOld) block ∧
      split.resolution.newEdge.blockCountWithin split.resolution.left split.bridge
          = split.K + 1 ∧
      split.resolution.newEdge.blockCountWithin split.resolution.right split.bridge
          = split.coK + 1 :=
  ⟨split.resolution_contracts, split.newEdge_refines_left, split.newEdge_refines_right,
    split.left_riemannHurwitzAtBlock leftOld hLeftLength hLeftOld block hBlock,
    split.right_riemannHurwitzAtBlock rightOld hRightLength hRightOld block hBlock,
    split.newEdge_blockCountWithin_left_eq, split.newEdge_blockCountWithin_right_eq⟩

end SplitData

/-! ## 5.  Building the split from a gauge -/

/-- The union receipt is **derived**, not assumed, once the two endpoint sets
sit inside the wall block with the right total cardinality. -/
def SplitData.ofCards (coarse : SheetPartition degree) (anchor bridge : Fin degree)
    (minusSheets plusSheets : Finset (Fin degree))
    (hMinus : minusSheets ⊆ coarse.block anchor)
    (hPlus : plusSheets ⊆ coarse.block anchor)
    (hBridgeMinus : bridge ∈ minusSheets) (hBridgePlus : bridge ∈ plusSheets)
    (hCards : minusSheets.card + plusSheets.card
      = coarse.blockCard anchor + (minusSheets ∩ plusSheets).card) :
    SplitData coarse anchor where
  bridge := bridge
  minusSheets := minusSheets
  plusSheets := plusSheets
  bridge_mem_minus := hBridgeMinus
  bridge_mem_plus := hBridgePlus
  union_eq := by
    have hUnion := Finset.card_union_add_card_inter minusSheets plusSheets
    refine Finset.eq_of_subset_of_card_le (Finset.union_subset hMinus hPlus) ?_
    unfold SheetPartition.blockCard at hCards
    omega

/-- The conclusion shape of the widened overlap gauge: a permutation
supported on one wall block which puts the two branch classes in overlap
exactly `overlap`.  At `overlap = 1` this is
`PrescribedPairing.exists_overlap_gauge` verbatim. -/
def OverlapGauge (whole first second : Finset (Fin degree)) (overlap : ℕ) : Prop :=
  ∃ permutation : Equiv.Perm (Fin degree),
    (∀ sheet ∈ whole, permutation sheet ∈ whole) ∧
    (∀ sheet, sheet ∉ whole → permutation sheet = sheet) ∧
    (first ∩ second.image permutation).card = overlap

/-- What one side of the pairing contributes, given PW1's gauge: a sheet set
inside the wall block, containing the whole first branch class, whose
cardinality is `k_α + k_β - overlap`.  At `overlap = K + 1` this is the paper's
`|A₋| = k_α + k_β - 1 - K`. -/
theorem exists_gauged_side {whole first second : Finset (Fin degree)} {overlap : ℕ}
    (hFirst : first ⊆ whole) (hSecond : second ⊆ whole)
    (hGauge : OverlapGauge whole first second overlap) :
    ∃ gauged : Finset (Fin degree),
      first ⊆ gauged ∧ gauged ⊆ whole ∧
        gauged.card + overlap = first.card + second.card := by
  obtain ⟨permutation, hInside, _, hOverlap⟩ := hGauge
  refine ⟨first ∪ second.image permutation, Finset.subset_union_left, ?_, ?_⟩
  · refine Finset.union_subset hFirst ?_
    intro sheet hSheet
    obtain ⟨original, hOriginal, rfl⟩ := Finset.mem_image.mp hSheet
    exact hInside original (hSecond hOriginal)
  · have hImage : (second.image permutation).card = second.card :=
      Finset.card_image_of_injective _ permutation.injective
    have hUnion := Finset.card_union_add_card_inter first (second.image permutation)
    rw [hOverlap, hImage] at hUnion
    exact hUnion

/-- **The assembly.**  Given the two gauged endpoint sheet sets, the two
per-side cardinalities `|A₋| + K' = |A|` and `|A₊| + K = |A|`, and the joint
condition `k₁ + K + K' = |A|`, the split exists with exactly the prescribed
`K` and `K'`.

The first two hypotheses are the paper's `|A₊| = |A| - K` and its mirror; the
third is the joint obligation described in the module docstring.  The union
receipt `A₋ ∪ A₊ = A` is derived. -/
theorem exists_splitData_of_gauged_sides {coarse : SheetPartition degree}
    {anchor bridge : Fin degree} {K coK : ℕ}
    {minusSheets plusSheets : Finset (Fin degree)}
    (hMinus : minusSheets ⊆ coarse.block anchor)
    (hPlus : plusSheets ⊆ coarse.block anchor)
    (hBridgeMinus : bridge ∈ minusSheets) (hBridgePlus : bridge ∈ plusSheets)
    (hMinusCard : minusSheets.card + coK = coarse.blockCard anchor)
    (hPlusCard : plusSheets.card + K = coarse.blockCard anchor)
    (hJointCard : (minusSheets ∩ plusSheets).card + K + coK = coarse.blockCard anchor) :
    ∃ split : SplitData coarse anchor,
      split.bridge = bridge ∧ split.minusSheets = minusSheets ∧
        split.plusSheets = plusSheets ∧ split.K = K ∧ split.coK = coK := by
  refine ⟨SplitData.ofCards coarse anchor bridge minusSheets plusSheets hMinus hPlus
    hBridgeMinus hBridgePlus (by omega), rfl, rfl, rfl, ?_, ?_⟩
  · have hK := Finset.card_inter_add_card_sdiff minusSheets plusSheets
    show (minusSheets \ plusSheets).card = K
    omega
  · have hcoK := Finset.card_inter_add_card_sdiff plusSheets minusSheets
    rw [Finset.inter_comm] at hcoK
    show (plusSheets \ minusSheets).card = coK
    omega

end DraismaVargas.LocalCases.GeneralKResolution
