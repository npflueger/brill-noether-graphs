import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Sheet partitions for Draisma--Vargas gluing data

A gluing datum records, above every target vertex and edge, a partition of
the finite sheet set.  This file gives that object a small extensional API.
The representation is a canonical-representative map: its fibres are the
blocks, and idempotence says that every representative names its own block.

The wall operation joins the partitions at the two endpoints of a contracted
target edge.  `IsJoin` states that operation without choosing an algorithm for
transitive closure.  This is the exact relation used in Part I, Definition 15.
-/

namespace DraismaVargas.Infrastructure

open Finset

/-- A partition of `Fin d`, represented by an idempotent choice of one
representative in every block. -/
structure SheetPartition (d : ℕ) where
  repr : Fin d → Fin d
  repr_idem : ∀ i, repr (repr i) = repr i

namespace SheetPartition

variable {d : ℕ}

/-- Sheet partitions are equal when their representative maps are equal;
the idempotence fields are propositions. -/
@[ext] theorem ext_repr (first second : SheetPartition d)
    (h : first.repr = second.repr) : first = second := by
  cases first
  cases second
  cases h
  rfl

/-- Two sheets lie in the same block. -/
def Rel (partition : SheetPartition d) (i j : Fin d) : Prop :=
  partition.repr i = partition.repr j

instance (partition : SheetPartition d) : DecidableRel partition.Rel :=
  fun i j ↦ inferInstanceAs (Decidable (partition.repr i = partition.repr j))

@[simp] theorem rel_iff (partition : SheetPartition d) (i j : Fin d) :
    partition.Rel i j ↔ partition.repr i = partition.repr j := Iff.rfl

@[simp] theorem rel_repr_left (partition : SheetPartition d) (i : Fin d) :
    partition.Rel (partition.repr i) i := by
  simp [Rel, partition.repr_idem]

@[simp] theorem rel_repr_right (partition : SheetPartition d) (i : Fin d) :
    partition.Rel i (partition.repr i) := by
  simp [Rel, partition.repr_idem]

/-- The block containing a sheet. -/
def block (partition : SheetPartition d) (i : Fin d) : Finset (Fin d) :=
  Finset.univ.filter fun j ↦ partition.Rel i j

@[simp] theorem mem_block_iff (partition : SheetPartition d) (i j : Fin d) :
    j ∈ partition.block i ↔ partition.Rel i j := by
  simp [block]

theorem self_mem_block (partition : SheetPartition d) (i : Fin d) :
    i ∈ partition.block i := by simp

theorem block_eq_of_rel (partition : SheetPartition d) {i j : Fin d}
    (h : partition.Rel i j) : partition.block i = partition.block j := by
  ext k
  rw [mem_block_iff, mem_block_iff, rel_iff, rel_iff, h]

/-- The cardinality of the block containing a sheet. -/
def blockCard (partition : SheetPartition d) (i : Fin d) : ℕ :=
  (partition.block i).card

theorem blockCard_pos (partition : SheetPartition d) (i : Fin d) :
    0 < partition.blockCard i :=
  Finset.card_pos.mpr ⟨i, partition.self_mem_block i⟩

/-- Every block of cardinality greater than one contains another sheet. -/
theorem exists_other_of_one_lt_blockCard (partition : SheetPartition d)
    (i : Fin d) (hCard : 1 < partition.blockCard i) :
    ∃ j, partition.Rel i j ∧ i ≠ j := by
  by_contra hExists
  push Not at hExists
  have hSubset : partition.block i ⊆ {i} := by
    intro j hj
    have hRel := (partition.mem_block_iff i j).mp hj
    have hij : i = j := hExists j hRel
    exact Finset.mem_singleton.mpr hij.symm
  have hLe := Finset.card_le_card hSubset
  change partition.blockCard i ≤ 1 at hLe
  omega

/-- A block of cardinality `k + 1` with `k > 1` contains a third sheet besides
any chosen distinct pair in that block. -/
theorem exists_third_of_blockCard_eq_add_one
    (partition : SheetPartition d) (first second : Fin d)
    (hne : first ≠ second) (_hTogether : partition.Rel first second)
    (k : ℕ) (hk : 1 < k) (hCard : partition.blockCard first = k + 1) :
    ∃ third, partition.Rel first third ∧ first ≠ third ∧ second ≠ third := by
  by_contra hExists
  push Not at hExists
  have hSubset : partition.block first ⊆ {first, second} := by
    intro sheet hSheet
    have hRel := (partition.mem_block_iff first sheet).mp hSheet
    by_cases hFirst : first = sheet
    · simp [hFirst]
    · have hSecond : second = sheet := hExists sheet hRel hFirst
      simp [hSecond]
  have hLe := Finset.card_le_card hSubset
  have hPairCard : ({first, second} : Finset (Fin d)).card = 2 := by
    simp [hne]
  rw [hPairCard] at hLe
  change partition.blockCard first ≤ 2 at hLe
  rw [hCard] at hLe
  omega

/-! ## Splitting one block -/

private def splitBlockRepr (partition : SheetPartition d) (anchor i : Fin d) :
    Fin d :=
  if partition.Rel anchor i then i else partition.repr i

private theorem splitBlockRepr_idem (partition : SheetPartition d)
    (anchor i : Fin d) :
    splitBlockRepr partition anchor (splitBlockRepr partition anchor i) =
      splitBlockRepr partition anchor i := by
  unfold splitBlockRepr
  by_cases hi : partition.Rel anchor i
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi]
    have hrepr : ¬partition.Rel anchor (partition.repr i) := by
      intro h
      apply hi
      unfold Rel at h ⊢
      simpa only [partition.repr_idem i] using h
    rw [if_neg hrepr, partition.repr_idem i]

/-- Refine one selected block into singleton sheets, leaving every other block
unchanged.  This is the partition operation used when a DV wall class splits
at one endpoint of an outgoing target edge. -/
def splitBlock (partition : SheetPartition d) (anchor : Fin d) :
    SheetPartition d where
  repr := splitBlockRepr partition anchor
  repr_idem := splitBlockRepr_idem partition anchor

@[simp] theorem splitBlock_repr_of_rel (partition : SheetPartition d)
    (anchor i : Fin d) (hi : partition.Rel anchor i) :
    (partition.splitBlock anchor).repr i = i := by
  change splitBlockRepr partition anchor i = i
  exact if_pos hi

@[simp] theorem splitBlock_repr_of_not_rel (partition : SheetPartition d)
    (anchor i : Fin d) (hi : ¬partition.Rel anchor i) :
    (partition.splitBlock anchor).repr i = partition.repr i := by
  change splitBlockRepr partition anchor i = partition.repr i
  exact if_neg hi

/-- Every new singleton block remains inside its original block. -/
theorem splitBlock_repr_rel (partition : SheetPartition d)
    (anchor i : Fin d) :
    partition.Rel ((partition.splitBlock anchor).repr i) i := by
  by_cases hi : partition.Rel anchor i
  · rw [partition.splitBlock_repr_of_rel anchor i hi]
    exact rfl
  · rw [partition.splitBlock_repr_of_not_rel anchor i hi]
    exact partition.rel_repr_left i

/-- The anchor is a singleton in the split partition. -/
@[simp] theorem splitBlock_rel_anchor_iff (partition : SheetPartition d)
    (anchor i : Fin d) :
    (partition.splitBlock anchor).Rel anchor i ↔ anchor = i := by
  have hAnchor : partition.Rel anchor anchor := rfl
  rw [rel_iff]
  rw [partition.splitBlock_repr_of_rel anchor anchor hAnchor]
  by_cases hi : partition.Rel anchor i
  · rw [partition.splitBlock_repr_of_rel anchor i hi]
  · rw [partition.splitBlock_repr_of_not_rel anchor i hi]
    constructor
    · intro hrepr
      exfalso
      apply hi
      unfold Rel
      rw [hrepr]
      exact partition.repr_idem i
    · intro hai
      subst i
      exact (hi hAnchor).elim

/-- Every sheet of the selected original block becomes a singleton in the
split partition. -/
theorem splitBlock_rel_of_rel_anchor_iff (partition : SheetPartition d)
    (anchor i : Fin d) (hi : partition.Rel anchor i) (j : Fin d) :
    (partition.splitBlock anchor).Rel i j ↔ i = j := by
  rw [rel_iff]
  rw [partition.splitBlock_repr_of_rel anchor i hi]
  by_cases hj : partition.Rel anchor j
  · rw [partition.splitBlock_repr_of_rel anchor j hj]
  · rw [partition.splitBlock_repr_of_not_rel anchor j hj]
    constructor
    · intro hij
      exfalso
      apply hj
      unfold Rel at hi ⊢
      calc
        partition.repr anchor = partition.repr i := hi
        _ = partition.repr (partition.repr j) := congrArg partition.repr hij
        _ = partition.repr j := partition.repr_idem j
    · intro hij
      subst j
      exact (hj hi).elim

theorem splitBlock_block_of_rel (partition : SheetPartition d)
    (anchor i : Fin d) (hi : partition.Rel anchor i) :
    (partition.splitBlock anchor).block i = {i} := by
  ext j
  rw [mem_block_iff, partition.splitBlock_rel_of_rel_anchor_iff anchor i hi]
  simp only [Finset.mem_singleton]
  exact eq_comm

theorem splitBlock_blockCard_of_rel (partition : SheetPartition d)
    (anchor i : Fin d) (hi : partition.Rel anchor i) :
    (partition.splitBlock anchor).blockCard i = 1 := by
  simp [blockCard, partition.splitBlock_block_of_rel anchor i hi]

@[simp] theorem splitBlock_block_anchor (partition : SheetPartition d)
    (anchor : Fin d) :
    (partition.splitBlock anchor).block anchor = {anchor} := by
  ext i
  rw [mem_block_iff, splitBlock_rel_anchor_iff]
  simp only [Finset.mem_singleton]
  exact eq_comm

@[simp] theorem splitBlock_blockCard_anchor (partition : SheetPartition d)
    (anchor : Fin d) :
    (partition.splitBlock anchor).blockCard anchor = 1 := by
  simp [blockCard]

/-! ## Detaching one sheet from a block -/

private def detachSheetRepr (partition : SheetPartition d)
    (single remainder : Fin d) (i : Fin d) : Fin d :=
  if i = single then single
  else if partition.Rel single i then remainder
  else partition.repr i

private theorem detachSheetRepr_idem (partition : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder) (i : Fin d) :
    detachSheetRepr partition single remainder
        (detachSheetRepr partition single remainder i) =
      detachSheetRepr partition single remainder i := by
  unfold detachSheetRepr
  by_cases hiSingle : i = single
  · rw [if_pos hiSingle, if_pos rfl]
  · rw [if_neg hiSingle]
    by_cases hiBlock : partition.Rel single i
    · rw [if_pos hiBlock, if_neg hne.symm, if_pos hTogether]
    · rw [if_neg hiBlock]
      have hReprSingle : partition.repr i ≠ single := by
        intro h
        apply hiBlock
        unfold Rel
        rw [← h]
        exact partition.repr_idem i
      have hReprBlock : ¬partition.Rel single (partition.repr i) := by
        intro h
        apply hiBlock
        unfold Rel at h ⊢
        simpa only [partition.repr_idem i] using h
      rw [if_neg hReprSingle, if_neg hReprBlock, partition.repr_idem i]

/-- Detach `single` from its original block, using `remainder` as the
representative of the nonempty residual block and leaving all other blocks
unchanged. -/
def detachSheet (partition : SheetPartition d) (single remainder : Fin d)
    (hne : single ≠ remainder) (hTogether : partition.Rel single remainder) :
    SheetPartition d where
  repr := detachSheetRepr partition single remainder
  repr_idem := partition.detachSheetRepr_idem single remainder hne hTogether

@[simp] theorem detachSheet_repr_single (partition : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder) :
    (partition.detachSheet single remainder hne hTogether).repr single = single := by
  change detachSheetRepr partition single remainder single = single
  exact if_pos rfl

theorem detachSheet_repr_of_rel_of_ne (partition : SheetPartition d)
    (single remainder i : Fin d) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder)
    (hiSingle : i ≠ single) (hiBlock : partition.Rel single i) :
    (partition.detachSheet single remainder hne hTogether).repr i = remainder := by
  change detachSheetRepr partition single remainder i = remainder
  rw [detachSheetRepr, if_neg hiSingle, if_pos hiBlock]

theorem detachSheet_repr_of_not_rel (partition : SheetPartition d)
    (single remainder i : Fin d) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder)
    (hiBlock : ¬partition.Rel single i) :
    (partition.detachSheet single remainder hne hTogether).repr i =
      partition.repr i := by
  have hiSingle : i ≠ single := by
    intro hi
    subst i
    exact hiBlock rfl
  change detachSheetRepr partition single remainder i = partition.repr i
  rw [detachSheetRepr, if_neg hiSingle, if_neg hiBlock]

/-- The detached sheet is a singleton. -/
theorem detachSheet_rel_single_iff (partition : SheetPartition d)
    (single remainder i : Fin d) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder) :
    (partition.detachSheet single remainder hne hTogether).Rel single i ↔
      single = i := by
  rw [rel_iff, partition.detachSheet_repr_single single remainder hne hTogether]
  by_cases hiSingle : i = single
  · subst i
    simp
  · by_cases hiBlock : partition.Rel single i
    · rw [partition.detachSheet_repr_of_rel_of_ne single remainder i hne
        hTogether hiSingle hiBlock]
      exact ⟨fun h ↦ (hne h).elim, fun h ↦ (hiSingle h.symm).elim⟩
    · rw [partition.detachSheet_repr_of_not_rel single remainder i hne
        hTogether hiBlock]
      constructor
      · intro hRepr
        exfalso
        apply hiBlock
        unfold Rel
        rw [hRepr]
        exact partition.repr_idem i
      · intro h
        exact (hiSingle h.symm).elim

theorem detachSheet_block_single (partition : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder) :
    (partition.detachSheet single remainder hne hTogether).block single =
      {single} := by
  ext i
  rw [mem_block_iff,
    partition.detachSheet_rel_single_iff single remainder i hne hTogether]
  simp only [Finset.mem_singleton]
  exact eq_comm

@[simp] theorem detachSheet_blockCard_single (partition : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder) :
    (partition.detachSheet single remainder hne hTogether).blockCard single = 1 := by
  simp [blockCard, partition.detachSheet_block_single single remainder hne hTogether]

/-- The residual block is the original block with the detached sheet erased. -/
theorem detachSheet_block_remainder (partition : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder) :
    (partition.detachSheet single remainder hne hTogether).block remainder =
      (partition.block single).erase single := by
  ext i
  rw [mem_block_iff]
  have hRemainderNe : remainder ≠ single := hne.symm
  have hRemainderRepr := partition.detachSheet_repr_of_rel_of_ne
    single remainder remainder hne hTogether hRemainderNe hTogether
  rw [rel_iff, hRemainderRepr]
  rw [Finset.mem_erase, mem_block_iff]
  by_cases hiSingle : i = single
  · subst i
    rw [partition.detachSheet_repr_single single remainder hne hTogether]
    simp [hRemainderNe]
  · by_cases hiBlock : partition.Rel single i
    · rw [partition.detachSheet_repr_of_rel_of_ne single remainder i hne
        hTogether hiSingle hiBlock]
      constructor
      · intro _
        exact ⟨hiSingle, hiBlock⟩
      · intro _
        rfl
    · rw [partition.detachSheet_repr_of_not_rel single remainder i hne
        hTogether hiBlock]
      have hReprNe : remainder ≠ partition.repr i := by
        intro hRepr
        apply hiBlock
        unfold Rel at hTogether ⊢
        calc
          partition.repr single = partition.repr remainder := hTogether
          _ = partition.repr (partition.repr i) := congrArg partition.repr hRepr
          _ = partition.repr i := partition.repr_idem i
      constructor
      · intro h
        exact (hReprNe h).elim
      · rintro ⟨_, h⟩
        exact (hiBlock h).elim

/-- Detaching one sheet decreases the residual block cardinality by exactly
one. -/
theorem detachSheet_blockCard_remainder (partition : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder) :
    (partition.detachSheet single remainder hne hTogether).blockCard remainder =
      partition.blockCard single - 1 := by
  unfold blockCard
  rw [partition.detachSheet_block_remainder single remainder hne hTogether,
    Finset.card_erase_of_mem (partition.self_mem_block single)]

theorem detachSheet_repr_rel (partition : SheetPartition d)
    (single remainder i : Fin d) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder) :
    partition.Rel
      ((partition.detachSheet single remainder hne hTogether).repr i) i := by
  by_cases hiSingle : i = single
  · subst i
    rw [partition.detachSheet_repr_single single remainder hne hTogether]
    exact rfl
  · by_cases hiBlock : partition.Rel single i
    · rw [partition.detachSheet_repr_of_rel_of_ne single remainder i hne
        hTogether hiSingle hiBlock]
      unfold Rel at hTogether hiBlock ⊢
      exact hTogether.symm.trans hiBlock
    · rw [partition.detachSheet_repr_of_not_rel single remainder i hne
        hTogether hiBlock]
      exact partition.rel_repr_left i

/-! ## Retaining exactly one pair inside a wall block -/

private def pairBlockRepr (partition : SheetPartition d)
    (first second : Fin d) (i : Fin d) : Fin d :=
  if partition.Rel first i then
    if i = second then first else i
  else partition.repr i

private theorem pairBlockRepr_idem (partition : SheetPartition d)
    (first second : Fin d) (hne : first ≠ second) (i : Fin d) :
    pairBlockRepr partition first second
        (pairBlockRepr partition first second i) =
      pairBlockRepr partition first second i := by
  unfold pairBlockRepr
  by_cases hiBlock : partition.Rel first i
  · rw [if_pos hiBlock]
    by_cases hiSecond : i = second
    · rw [if_pos hiSecond]
      have hFirstBlock : partition.Rel first first := rfl
      rw [if_pos hFirstBlock, if_neg hne]
    · rw [if_neg hiSecond, if_pos hiBlock, if_neg hiSecond]
  · rw [if_neg hiBlock]
    have hReprBlock : ¬partition.Rel first (partition.repr i) := by
      intro h
      apply hiBlock
      unfold Rel at h ⊢
      simpa only [partition.repr_idem i] using h
    rw [if_neg hReprBlock, partition.repr_idem i]

/-- Inside the block containing `first` and `second`, retain exactly their
two-sheet block and split every other sheet into a singleton. Outside that
original block, leave the partition unchanged. -/
def pairBlock (partition : SheetPartition d) (first second : Fin d)
    (hne : first ≠ second) : SheetPartition d where
  repr := pairBlockRepr partition first second
  repr_idem := partition.pairBlockRepr_idem first second hne

@[simp] theorem pairBlock_repr_first (partition : SheetPartition d)
    (first second : Fin d) (hne : first ≠ second) :
    (partition.pairBlock first second hne).repr first = first := by
  change pairBlockRepr partition first second first = first
  rw [pairBlockRepr, if_pos (show partition.Rel first first from rfl), if_neg hne]

@[simp] theorem pairBlock_repr_second (partition : SheetPartition d)
    (first second : Fin d) (hne : first ≠ second)
    (hTogether : partition.Rel first second) :
    (partition.pairBlock first second hne).repr second = first := by
  change pairBlockRepr partition first second second = first
  rw [pairBlockRepr, if_pos hTogether, if_pos rfl]

theorem pairBlock_repr_of_rel_of_ne_second (partition : SheetPartition d)
    (first second i : Fin d) (hne : first ≠ second)
    (hiBlock : partition.Rel first i) (hiSecond : i ≠ second) :
    (partition.pairBlock first second hne).repr i = i := by
  change pairBlockRepr partition first second i = i
  rw [pairBlockRepr, if_pos hiBlock, if_neg hiSecond]

theorem pairBlock_repr_of_not_rel (partition : SheetPartition d)
    (first second i : Fin d) (hne : first ≠ second)
    (hiBlock : ¬partition.Rel first i) :
    (partition.pairBlock first second hne).repr i = partition.repr i := by
  change pairBlockRepr partition first second i = partition.repr i
  rw [pairBlockRepr, if_neg hiBlock]

theorem pairBlock_repr_rel (partition : SheetPartition d)
    (first second i : Fin d) (hne : first ≠ second)
    (hTogether : partition.Rel first second) :
    partition.Rel ((partition.pairBlock first second hne).repr i) i := by
  by_cases hiBlock : partition.Rel first i
  · by_cases hiSecond : i = second
    · subst i
      rw [partition.pairBlock_repr_second first second hne hTogether]
      exact hTogether
    · rw [partition.pairBlock_repr_of_rel_of_ne_second first second i hne
        hiBlock hiSecond]
      exact rfl
  · rw [partition.pairBlock_repr_of_not_rel first second i hne hiBlock]
    exact partition.rel_repr_left i

theorem pairBlock_rel_first_iff (partition : SheetPartition d)
    (first second i : Fin d) (hne : first ≠ second)
    (hTogether : partition.Rel first second) :
    (partition.pairBlock first second hne).Rel first i ↔
      i = first ∨ i = second := by
  rw [rel_iff, partition.pairBlock_repr_first first second hne]
  by_cases hiBlock : partition.Rel first i
  · by_cases hiSecond : i = second
    · subst i
      rw [partition.pairBlock_repr_second first second hne hTogether]
      simp
    · rw [partition.pairBlock_repr_of_rel_of_ne_second first second i hne
        hiBlock hiSecond]
      constructor
      · intro h
        exact Or.inl h.symm
      · rintro (h | h)
        · exact h.symm
        · exact (hiSecond h).elim
  · rw [partition.pairBlock_repr_of_not_rel first second i hne hiBlock]
    have hReprNe : first ≠ partition.repr i := by
      intro hRepr
      apply hiBlock
      unfold Rel
      rw [hRepr]
      exact partition.repr_idem i
    constructor
    · exact fun h ↦ (hReprNe h).elim
    · rintro (h | h)
      · subst i
        exact (hiBlock rfl).elim
      · subst i
        exact (hiBlock hTogether).elim

/-- Detaching a sheet leaves every disjoint block unchanged. -/
theorem detachSheet_block_of_not_rel (partition : SheetPartition d)
    (single remainder i : Fin d) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder)
    (hiBlock : ¬partition.Rel single i) :
    (partition.detachSheet single remainder hne hTogether).block i =
      partition.block i := by
  ext j
  rw [mem_block_iff, mem_block_iff]
  constructor
  · intro hij
    have hi := partition.detachSheet_repr_rel single remainder i hne hTogether
    have hj := partition.detachSheet_repr_rel single remainder j hne hTogether
    unfold Rel at hij hi hj ⊢
    exact hi.symm.trans ((congrArg partition.repr hij).trans hj)
  · intro hij
    have hjBlock : ¬partition.Rel single j := by
      intro hj
      exact hiBlock (hj.trans hij.symm)
    unfold Rel
    rw [partition.detachSheet_repr_of_not_rel single remainder i hne hTogether
        hiBlock,
      partition.detachSheet_repr_of_not_rel single remainder j hne hTogether
        hjBlock]
    exact hij

theorem detachSheet_blockCard_of_not_rel (partition : SheetPartition d)
    (single remainder i : Fin d) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder)
    (hiBlock : ¬partition.Rel single i) :
    (partition.detachSheet single remainder hne hTogether).blockCard i =
      partition.blockCard i := by
  unfold blockCard
  rw [partition.detachSheet_block_of_not_rel single remainder i hne hTogether
    hiBlock]

theorem pairBlock_block_first (partition : SheetPartition d)
    (first second : Fin d) (hne : first ≠ second)
    (hTogether : partition.Rel first second) :
    (partition.pairBlock first second hne).block first = {first, second} := by
  ext i
  rw [mem_block_iff,
    partition.pairBlock_rel_first_iff first second i hne hTogether]
  simp [eq_comm]

@[simp] theorem pairBlock_blockCard_first (partition : SheetPartition d)
    (first second : Fin d) (hne : first ≠ second)
    (hTogether : partition.Rel first second) :
    (partition.pairBlock first second hne).blockCard first = 2 := by
  unfold blockCard
  rw [partition.pairBlock_block_first first second hne hTogether]
  simp [hne]

/-! ## Joining two existing blocks -/

private def mergeBlocksRepr (partition : SheetPartition d)
    (first extra i : Fin d) : Fin d :=
  if partition.Rel extra i then partition.repr first else partition.repr i

private theorem mergeBlocksRepr_idem (partition : SheetPartition d)
    (first extra : Fin d) (hSeparate : ¬partition.Rel first extra)
    (i : Fin d) :
    mergeBlocksRepr partition first extra
        (mergeBlocksRepr partition first extra i) =
      mergeBlocksRepr partition first extra i := by
  unfold mergeBlocksRepr
  by_cases hiExtra : partition.Rel extra i
  · rw [if_pos hiExtra]
    have hFirstOutside : ¬partition.Rel extra (partition.repr first) := by
      intro h
      apply hSeparate
      unfold Rel at h ⊢
      simpa only [partition.repr_idem first] using h.symm
    rw [if_neg hFirstOutside, partition.repr_idem first]
  · rw [if_neg hiExtra]
    have hReprOutside : ¬partition.Rel extra (partition.repr i) := by
      intro h
      apply hiExtra
      unfold Rel at h ⊢
      simpa only [partition.repr_idem i] using h
    rw [if_neg hReprOutside, partition.repr_idem i]

/-- Join the blocks containing `first` and `extra`, leaving every other block
unchanged. -/
def mergeBlocks (partition : SheetPartition d) (first extra : Fin d)
    (hSeparate : ¬partition.Rel first extra) : SheetPartition d where
  repr := mergeBlocksRepr partition first extra
  repr_idem := partition.mergeBlocksRepr_idem first extra hSeparate

theorem mergeBlocks_rel_first_iff (partition : SheetPartition d)
    (first extra i : Fin d) (hSeparate : ¬partition.Rel first extra) :
    (partition.mergeBlocks first extra hSeparate).Rel first i ↔
      partition.Rel first i ∨ partition.Rel extra i := by
  rw [rel_iff]
  change mergeBlocksRepr partition first extra first =
      mergeBlocksRepr partition first extra i ↔ _
  unfold mergeBlocksRepr
  have hExtraFirst : ¬partition.Rel extra first :=
    fun h ↦ hSeparate h.symm
  rw [if_neg hExtraFirst]
  by_cases hiExtra : partition.Rel extra i
  · rw [if_pos hiExtra]
    exact iff_of_true rfl (Or.inr hiExtra)
  · rw [if_neg hiExtra]
    exact ⟨Or.inl, fun h ↦ h.elim id (fun hExtra ↦ (hiExtra hExtra).elim)⟩

theorem mergeBlocks_block_first (partition : SheetPartition d)
    (first extra : Fin d) (hSeparate : ¬partition.Rel first extra) :
    (partition.mergeBlocks first extra hSeparate).block first =
      partition.block first ∪ partition.block extra := by
  ext i
  rw [mem_block_iff,
    partition.mergeBlocks_rel_first_iff first extra i hSeparate]
  simp only [Finset.mem_union, mem_block_iff]

theorem mergeBlocks_blockCard_first_of_singleton
    (partition : SheetPartition d) (first extra : Fin d)
    (hSeparate : ¬partition.Rel first extra)
    (hExtraSingleton : partition.block extra = {extra}) :
    (partition.mergeBlocks first extra hSeparate).blockCard first =
      partition.blockCard first + 1 := by
  unfold blockCard
  rw [partition.mergeBlocks_block_first first extra hSeparate,
    hExtraSingleton]
  have hExtraNotMem : extra ∉ partition.block first := by
    simpa using hSeparate
  simp [hExtraNotMem]

theorem mergeBlocks_block_of_separate (partition : SheetPartition d)
    (first extra other : Fin d) (hSeparate : ¬partition.Rel first extra)
    (hOtherFirst : ¬partition.Rel other first)
    (hOtherExtra : ¬partition.Rel other extra) :
    (partition.mergeBlocks first extra hSeparate).block other =
      partition.block other := by
  ext i
  rw [mem_block_iff, mem_block_iff]
  rw [rel_iff, rel_iff]
  change mergeBlocksRepr partition first extra other =
      mergeBlocksRepr partition first extra i ↔ _
  unfold mergeBlocksRepr
  have hExtraOther : ¬partition.Rel extra other :=
    fun h ↦ hOtherExtra h.symm
  rw [if_neg hExtraOther]
  by_cases hiExtra : partition.Rel extra i
  · rw [if_pos hiExtra]
    constructor
    · intro h
      exact (hOtherFirst h).elim
    · intro h
      exact (hOtherExtra (h.trans hiExtra.symm)).elim
  · rw [if_neg hiExtra]

theorem mergeBlocks_blockCard_of_separate (partition : SheetPartition d)
    (first extra other : Fin d) (hSeparate : ¬partition.Rel first extra)
    (hOtherFirst : ¬partition.Rel other first)
    (hOtherExtra : ¬partition.Rel other extra) :
    (partition.mergeBlocks first extra hSeparate).blockCard other =
      partition.blockCard other := by
  unfold blockCard
  rw [partition.mergeBlocks_block_of_separate first extra other hSeparate
    hOtherFirst hOtherExtra]

/-- Block cardinality as an integer-valued indicator sum over sheets. -/
theorem blockCard_cast_eq_sum_rel (partition : SheetPartition d) (i : Fin d) :
    (partition.blockCard i : ℤ) =
      ∑ k : Fin d, if partition.Rel i k then 1 else 0 := by
  calc
    (partition.blockCard i : ℤ) =
        ∑ _k ∈ partition.block i, (1 : ℤ) := by
      simp [blockCard]
    _ = ∑ k : Fin d, if partition.Rel i k then 1 else 0 := by
      unfold block
      rw [Finset.sum_filter]

/-- `fine` refines `coarse`: every fine block lies in one coarse block. -/
def Refines (fine coarse : SheetPartition d) : Prop :=
  ∀ i j, fine.Rel i j → coarse.Rel i j

instance (fine coarse : SheetPartition d) : Decidable (fine.Refines coarse) := by
  unfold Refines
  infer_instance

theorem Refines.rel {fine coarse : SheetPartition d}
    (h : fine.Refines coarse) {i j : Fin d} (hij : fine.Rel i j) :
    coarse.Rel i j := h i j hij

theorem Refines.refl (partition : SheetPartition d) : partition.Refines partition :=
  fun _ _ h ↦ h

theorem Refines.trans {first second third : SheetPartition d}
    (hFirst : first.Refines second) (hSecond : second.Refines third) :
    first.Refines third :=
  fun _ _ h ↦ hSecond.rel (hFirst.rel h)

/-- `fine` refines `endpoint` on the one block of `wall` named by `anchor`.
This is the exact compatibility condition needed when endpoint partitions are
pasted independently across the blocks of a contracted wall partition. -/
def RefinesOnBlock (fine endpoint wall : SheetPartition d)
    (anchor : Fin d) : Prop :=
  ∀ first second, wall.Rel anchor first → fine.Rel first second →
    endpoint.Rel first second

theorem RefinesOnBlock.rel {fine endpoint wall : SheetPartition d}
    {anchor first second : Fin d}
    (h : fine.RefinesOnBlock endpoint wall anchor)
    (hFirst : wall.Rel anchor first) (hFine : fine.Rel first second) :
    endpoint.Rel first second :=
  h first second hFirst hFine

/-- A global refinement is, in particular, a refinement on every wall
block. -/
theorem Refines.refinesOnBlock {fine endpoint wall : SheetPartition d}
    (h : fine.Refines endpoint) (anchor : Fin d) :
    fine.RefinesOnBlock endpoint wall anchor :=
  fun _ _ _ hFine ↦ h.rel hFine

/-- A partition which is singleton-refined on one wall block refines every
endpoint partition on that block. -/
theorem RefinesOnBlock.refinesAny_of_splitBlock
    {fine wall : SheetPartition d} {anchor : Fin d}
    (h : fine.RefinesOnBlock (wall.splitBlock anchor) wall anchor)
    (endpoint : SheetPartition d) :
    fine.RefinesOnBlock endpoint wall anchor := by
  intro first second hFirst hFine
  have hSplit := h.rel hFirst hFine
  have hEq :=
    (wall.splitBlock_rel_of_rel_anchor_iff anchor first hFirst second).mp hSplit
  subst second
  exact rfl

/-! ## Pasting refinements block by block -/

/-- Paste independently chosen refinements across the blocks of `coarse`.
The refinement used at a sheet is selected by the canonical representative
of its coarse block. Refinement guarantees that taking a representative does
not leave that block, which makes the pasted representative idempotent. -/
def paste (coarse : SheetPartition d) (fine : Fin d → SheetPartition d)
    (hFine : ∀ anchor, (fine anchor).Refines coarse) : SheetPartition d where
  repr := fun sheet ↦ (fine (coarse.repr sheet)).repr sheet
  repr_idem := by
    intro sheet
    have hSameBlock :
        coarse.repr ((fine (coarse.repr sheet)).repr sheet) =
          coarse.repr sheet := by
      exact (hFine (coarse.repr sheet)).rel
        ((fine (coarse.repr sheet)).rel_repr_left sheet)
    change (fine (coarse.repr
        ((fine (coarse.repr sheet)).repr sheet))).repr
          ((fine (coarse.repr sheet)).repr sheet) =
      (fine (coarse.repr sheet)).repr sheet
    rw [hSameBlock]
    exact (fine (coarse.repr sheet)).repr_idem sheet

@[simp] theorem paste_repr (coarse : SheetPartition d)
    (fine : Fin d → SheetPartition d)
    (hFine : ∀ anchor, (fine anchor).Refines coarse) (sheet : Fin d) :
    (coarse.paste fine hFine).repr sheet =
      (fine (coarse.repr sheet)).repr sheet := rfl

/-- Every block of a pasted partition remains in its original coarse block. -/
theorem paste_refines (coarse : SheetPartition d)
    (fine : Fin d → SheetPartition d)
    (hFine : ∀ anchor, (fine anchor).Refines coarse) :
    (coarse.paste fine hFine).Refines coarse := by
  intro first second hPasted
  have hFirst :
      coarse.repr ((fine (coarse.repr first)).repr first) =
        coarse.repr first := by
    exact (hFine (coarse.repr first)).rel
      ((fine (coarse.repr first)).rel_repr_left first)
  have hSecond :
      coarse.repr ((fine (coarse.repr second)).repr second) =
        coarse.repr second := by
    exact (hFine (coarse.repr second)).rel
      ((fine (coarse.repr second)).rel_repr_left second)
  unfold Rel at hPasted ⊢
  exact hFirst.symm.trans ((congrArg coarse.repr hPasted).trans hSecond)

/-- On a given coarse block, the pasted relation is exactly the relation
selected for that block. -/
theorem paste_rel_iff (coarse : SheetPartition d)
    (fine : Fin d → SheetPartition d)
    (hFine : ∀ anchor, (fine anchor).Refines coarse) (first second : Fin d) :
    (coarse.paste fine hFine).Rel first second ↔
      (fine (coarse.repr first)).Rel first second := by
  constructor
  · intro hPasted
    have hCoarse : coarse.Rel first second :=
      (coarse.paste_refines fine hFine).rel hPasted
    unfold Rel at hPasted hCoarse ⊢
    change (fine (coarse.repr first)).repr first =
      (fine (coarse.repr second)).repr second at hPasted
    rw [← hCoarse] at hPasted
    exact hPasted
  · intro hLocal
    have hCoarse : coarse.Rel first second :=
      (hFine (coarse.repr first)).rel hLocal
    unfold Rel at hLocal hCoarse ⊢
    change (fine (coarse.repr first)).repr first =
      (fine (coarse.repr second)).repr second
    rw [← hCoarse]
    exact hLocal

/-- The block of a sheet in a pasted partition is literally its block in the
refinement selected by the containing coarse block. -/
theorem paste_block (coarse : SheetPartition d)
    (fine : Fin d → SheetPartition d)
    (hFine : ∀ anchor, (fine anchor).Refines coarse) (sheet : Fin d) :
    (coarse.paste fine hFine).block sheet =
      (fine (coarse.repr sheet)).block sheet := by
  ext other
  rw [mem_block_iff, mem_block_iff,
    coarse.paste_rel_iff fine hFine sheet other]

theorem paste_blockCard (coarse : SheetPartition d)
    (fine : Fin d → SheetPartition d)
    (hFine : ∀ anchor, (fine anchor).Refines coarse) (sheet : Fin d) :
    (coarse.paste fine hFine).blockCard sheet =
      (fine (coarse.repr sheet)).blockCard sheet := by
  simp [blockCard, coarse.paste_block fine hFine sheet]

/-- A partition refines the result of joining two of its blocks. -/
theorem refines_mergeBlocks (partition : SheetPartition d)
    (first extra : Fin d) (hSeparate : ¬partition.Rel first extra) :
    partition.Refines (partition.mergeBlocks first extra hSeparate) := by
  intro i j hij
  unfold Rel at hij
  change mergeBlocksRepr partition first extra i =
    mergeBlocksRepr partition first extra j
  unfold mergeBlocksRepr
  have hExtraIff : partition.Rel extra i ↔ partition.Rel extra j := by
    unfold Rel
    rw [hij]
  by_cases hi : partition.Rel extra i
  · rw [if_pos hi, if_pos (hExtraIff.mp hi)]
  · rw [if_neg hi, if_neg (fun hj ↦ hi (hExtraIff.mpr hj))]
    exact hij

/-- Joining two endpoint blocks that lie in one coarse block still refines
the coarse partition. -/
theorem mergeBlocks_refines_coarse
    (partition coarse : SheetPartition d) (first extra : Fin d)
    (hSeparate : ¬partition.Rel first extra)
    (hRefines : partition.Refines coarse)
    (hTogether : coarse.Rel first extra) :
    (partition.mergeBlocks first extra hSeparate).Refines coarse := by
  intro i j hij
  change mergeBlocksRepr partition first extra i =
    mergeBlocksRepr partition first extra j at hij
  unfold mergeBlocksRepr at hij
  by_cases hiExtra : partition.Rel extra i <;>
      by_cases hjExtra : partition.Rel extra j
  · exact (hRefines.rel hiExtra).symm.trans (hRefines.rel hjExtra)
  · rw [if_pos hiExtra, if_neg hjExtra] at hij
    have hFirstJ : partition.Rel first j := hij
    exact (hRefines.rel hiExtra).symm.trans
      (hTogether.symm.trans (hRefines.rel hFirstJ))
  · rw [if_neg hiExtra, if_pos hjExtra] at hij
    have hIFirst : partition.Rel i first := hij
    exact (hRefines.rel hIFirst).trans
      (hTogether.trans (hRefines.rel hjExtra))
  · rw [if_neg hiExtra, if_neg hjExtra] at hij
    exact hRefines.rel hij

/-- A refinement of a singleton coarse block has the same singleton block. -/
theorem block_eq_singleton_of_refines {fine coarse : SheetPartition d}
    (hRefines : fine.Refines coarse) (i : Fin d)
    (hCoarse : coarse.block i = {i}) :
    fine.block i = {i} := by
  ext j
  constructor
  · intro hj
    have hCoarseRel := hRefines.rel ((fine.mem_block_iff i j).mp hj)
    have : j ∈ ({i} : Finset (Fin d)) := by
      rw [← hCoarse]
      exact (coarse.mem_block_iff i j).mpr hCoarseRel
    simpa [eq_comm] using this
  · intro hj
    have : j = i := by simpa using hj
    subst j
    exact fine.self_mem_block i

theorem blockCard_eq_one_of_refines_singleton {fine coarse : SheetPartition d}
    (hRefines : fine.Refines coarse) (i : Fin d)
    (hCoarse : coarse.block i = {i}) :
    fine.blockCard i = 1 := by
  simp [blockCard, block_eq_singleton_of_refines hRefines i hCoarse]

/-- A block of cardinality one is the singleton containing its anchor. -/
theorem block_eq_singleton_of_blockCard_eq_one (partition : SheetPartition d)
    (i : Fin d) (hCard : partition.blockCard i = 1) :
    partition.block i = {i} := by
  obtain ⟨only, hOnly⟩ := Finset.card_eq_one.mp hCard
  have hi : i ∈ ({only} : Finset (Fin d)) := by
    rw [← hOnly]
    exact partition.self_mem_block i
  have hEq : i = only := Finset.mem_singleton.mp hi
  simpa [hEq] using hOnly

/-- Transfer one sheet from a block disjoint from `recipient` into the
recipient block. The donor singleton case is handled by merging directly; a
larger donor block first detaches the chosen donor sheet. -/
theorem exists_merge_one_from_separate_block
    (partition coarse : SheetPartition d) (recipient donor : Fin d)
    (hRefines : partition.Refines coarse)
    (hSeparate : ¬partition.Rel recipient donor)
    (hTogether : coarse.Rel recipient donor)
    (hDonorPos : 0 < partition.blockCard donor) :
    ∃ moved : SheetPartition d,
      moved.Refines coarse ∧
        moved.blockCard recipient = partition.blockCard recipient + 1 := by
  by_cases hDonorOne : partition.blockCard donor = 1
  · let moved := partition.mergeBlocks recipient donor hSeparate
    refine ⟨moved,
      partition.mergeBlocks_refines_coarse coarse recipient donor hSeparate
        hRefines hTogether, ?_⟩
    exact partition.mergeBlocks_blockCard_first_of_singleton recipient donor
      hSeparate (partition.block_eq_singleton_of_blockCard_eq_one donor hDonorOne)
  · have hDonorLarge : 1 < partition.blockCard donor := by omega
    obtain ⟨remainder, hDonorRemainder, hne⟩ :=
      partition.exists_other_of_one_lt_blockCard donor hDonorLarge
    let detached := partition.detachSheet donor remainder hne hDonorRemainder
    have hDetachedRefines : detached.Refines partition := by
      intro i j hij
      have hi := partition.detachSheet_repr_rel donor remainder i hne
        hDonorRemainder
      have hj := partition.detachSheet_repr_rel donor remainder j hne
        hDonorRemainder
      unfold detached at hij
      unfold Rel at hij hi hj ⊢
      exact hi.symm.trans ((congrArg partition.repr hij).trans hj)
    have hDetachedSeparate : ¬detached.Rel recipient donor := by
      intro h
      exact hSeparate (hDetachedRefines.rel h)
    let moved := detached.mergeBlocks recipient donor hDetachedSeparate
    refine ⟨moved,
      detached.mergeBlocks_refines_coarse coarse recipient donor
        hDetachedSeparate (hDetachedRefines.trans hRefines) hTogether, ?_⟩
    rw [detached.mergeBlocks_blockCard_first_of_singleton recipient donor
      hDetachedSeparate
      (partition.detachSheet_block_single donor remainder hne hDonorRemainder)]
    congr 1
    unfold detached
    exact congrArg Finset.card
      (partition.detachSheet_block_of_not_rel donor remainder recipient hne
        hDonorRemainder (fun h ↦ hSeparate h.symm))

/-- Splitting a block is a refinement of the original partition. -/
theorem splitBlock_refines (partition : SheetPartition d) (anchor : Fin d) :
    (partition.splitBlock anchor).Refines partition := by
  intro i j hij
  have hi := partition.splitBlock_repr_rel anchor i
  have hj := partition.splitBlock_repr_rel anchor j
  unfold Rel at hij hi hj ⊢
  exact hi.symm.trans ((congrArg partition.repr hij).trans hj)

/-- Detaching one sheet refines the original partition. -/
theorem detachSheet_refines (partition : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder) :
    (partition.detachSheet single remainder hne hTogether).Refines partition := by
  intro i j hij
  have hi := partition.detachSheet_repr_rel single remainder i hne hTogether
  have hj := partition.detachSheet_repr_rel single remainder j hne hTogether
  unfold Rel at hij hi hj ⊢
  exact hi.symm.trans ((congrArg partition.repr hij).trans hj)

/-- A refinement of `partition` in which `single` is already a singleton also
refines the partition obtained by detaching `single`. -/
theorem refines_detachSheet_of_block_singleton
    (fine partition : SheetPartition d) (single remainder : Fin d)
    (hne : single ≠ remainder) (hTogether : partition.Rel single remainder)
    (hRefines : fine.Refines partition)
    (hSingleton : fine.block single = {single}) :
    fine.Refines (partition.detachSheet single remainder hne hTogether) := by
  intro i j hij
  have hWall := hRefines.rel hij
  by_cases hiSingle : i = single
  · subst i
    have hj : j ∈ fine.block single := (fine.mem_block_iff single j).mpr hij
    rw [hSingleton] at hj
    have : j = single := by simpa using hj
    subst j
    exact rfl
  · have hjSingle : j ≠ single := by
      intro hj
      subst j
      have hi : i ∈ fine.block single :=
        (fine.mem_block_iff single i).mpr hij.symm
      rw [hSingleton] at hi
      exact hiSingle (by simpa using hi)
    by_cases hiBlock : partition.Rel single i
    · have hjBlock : partition.Rel single j := hiBlock.trans hWall
      unfold Rel
      rw [partition.detachSheet_repr_of_rel_of_ne single remainder i hne
          hTogether hiSingle hiBlock,
        partition.detachSheet_repr_of_rel_of_ne single remainder j hne
          hTogether hjSingle hjBlock]
    · have hjBlock : ¬partition.Rel single j := by
        intro hj
        exact hiBlock (hj.trans hWall.symm)
      unfold Rel
      rw [partition.detachSheet_repr_of_not_rel single remainder i hne
          hTogether hiBlock,
        partition.detachSheet_repr_of_not_rel single remainder j hne
          hTogether hjBlock]
      exact hWall

/-- Retaining one pair inside a block refines the original partition. -/
theorem pairBlock_refines (partition : SheetPartition d)
    (first second : Fin d) (hne : first ≠ second)
    (hTogether : partition.Rel first second) :
    (partition.pairBlock first second hne).Refines partition := by
  intro i j hij
  have hi := partition.pairBlock_repr_rel first second i hne hTogether
  have hj := partition.pairBlock_repr_rel first second j hne hTogether
  unfold Rel at hij hi hj ⊢
  exact hi.symm.trans ((congrArg partition.repr hij).trans hj)

/-- Splitting the whole selected block into singletons refines the partition
that retains only one pair in that block. -/
theorem splitBlock_refines_pairBlock (partition : SheetPartition d)
    (first second : Fin d) (hne : first ≠ second) :
    (partition.splitBlock first).Refines
      (partition.pairBlock first second hne) := by
  intro i j hij
  by_cases hiBlock : partition.Rel first i
  · have hijEq :=
      (partition.splitBlock_rel_of_rel_anchor_iff first i hiBlock j).mp hij
    subst j
    exact rfl
  · have hWall := (partition.splitBlock_refines first).rel hij
    have hjBlock : ¬partition.Rel first j := by
      intro hj
      apply hiBlock
      unfold Rel at hj hWall ⊢
      exact hj.trans hWall.symm
    unfold Rel
    rw [partition.pairBlock_repr_of_not_rel first second i hne hiBlock,
      partition.pairBlock_repr_of_not_rel first second j hne hjBlock]
    exact hWall

/-- The same full split refines a one-sheet detachment of the selected block. -/
theorem splitBlock_refines_detachSheet (partition : SheetPartition d)
    (single remainder : Fin d) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder) :
    (partition.splitBlock single).Refines
      (partition.detachSheet single remainder hne hTogether) := by
  intro i j hij
  by_cases hiBlock : partition.Rel single i
  · have hijEq :=
      (partition.splitBlock_rel_of_rel_anchor_iff single i hiBlock j).mp hij
    subst j
    exact rfl
  · have hWall := (partition.splitBlock_refines single).rel hij
    have hjBlock : ¬partition.Rel single j := by
      intro hj
      apply hiBlock
      unfold Rel at hj hWall ⊢
      exact hj.trans hWall.symm
    unfold Rel
    rw [partition.detachSheet_repr_of_not_rel single remainder i hne hTogether
        hiBlock,
      partition.detachSheet_repr_of_not_rel single remainder j hne hTogether
        hjBlock]
    exact hWall

/-- A coarse block is the disjoint union of the fine blocks refining it:
summing the cardinalities at their canonical representatives recovers the
coarse block cardinality.  This is the sheet-counting identity behind the
local degree equation of a gluing datum. -/
theorem sum_blockCard_representatives_eq_blockCard
    (fine coarse : SheetPartition d) (hRefines : fine.Refines coarse)
    (i : Fin d) :
    (∑ j : Fin d,
      if fine.repr j = j ∧ coarse.Rel i j then
        (fine.blockCard j : ℤ)
      else 0) = (coarse.blockCard i : ℤ) := by
  simp_rw [fine.blockCard_cast_eq_sum_rel]
  have hDistribute :
      (∑ j : Fin d,
        if fine.repr j = j ∧ coarse.Rel i j then
          ∑ k : Fin d, if fine.Rel j k then (1 : ℤ) else 0
        else 0) =
      ∑ j : Fin d, ∑ k : Fin d,
        if fine.repr j = j ∧ coarse.Rel i j then
          if fine.Rel j k then (1 : ℤ) else 0
        else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : fine.repr j = j ∧ coarse.Rel i j <;> simp [hj]
  rw [hDistribute, Finset.sum_comm, coarse.blockCard_cast_eq_sum_rel]
  apply Finset.sum_congr rfl
  intro k _
  let representative : Fin d := fine.repr k
  have hRepresentative : fine.repr representative = representative :=
    fine.repr_idem k
  have hFineRepresentative : fine.Rel representative k :=
    fine.rel_repr_left k
  have hCoarseRepresentative : coarse.Rel representative k :=
    hRefines.rel hFineRepresentative
  have hCoarseIff : coarse.Rel i representative ↔ coarse.Rel i k := by
    unfold Rel at hCoarseRepresentative ⊢
    rw [hCoarseRepresentative]
  refine (Fintype.sum_eq_single representative ?_).trans ?_
  · intro j hne
    by_cases hOuter : fine.repr j = j ∧ coarse.Rel i j
    · rw [if_pos hOuter]
      by_cases hjFine : fine.Rel j k
      · exfalso
        apply hne
        unfold Rel at hjFine
        exact hOuter.1.symm.trans hjFine
      · rw [if_neg hjFine]
    · rw [if_neg hOuter]
  · by_cases hk : coarse.Rel i k
    · have hOuter : fine.repr representative = representative ∧
          coarse.Rel i representative :=
        ⟨hRepresentative, hCoarseIff.mpr hk⟩
      rw [if_pos hOuter, if_pos hFineRepresentative, if_pos hk]
    · have hOuter : ¬(fine.repr representative = representative ∧
          coarse.Rel i representative) :=
        fun h ↦ hk (hCoarseIff.mp h.2)
      rw [if_neg hOuter, if_neg hk]

/-- The block-decomposition identity with a common integer coefficient. -/
theorem sum_blockCard_representatives_mul_eq_blockCard_mul
    (fine coarse : SheetPartition d) (hRefines : fine.Refines coarse)
    (i : Fin d) (coefficient : ℤ) :
    (∑ j : Fin d,
      if fine.repr j = j ∧ coarse.Rel i j then
        (fine.blockCard j : ℤ) * coefficient
      else 0) = (coarse.blockCard i : ℤ) * coefficient := by
  rw [← fine.sum_blockCard_representatives_eq_blockCard coarse hRefines i,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : fine.repr j = j ∧ coarse.Rel i j <;> simp [h]

/-- Number of blocks of `fine` induced on the block of `coarse` containing
`i`.  When `fine.Refines coarse`, this is the `k_q` in the gluing-datum
Riemann--Hurwitz condition. -/
def blockCountWithin (fine coarse : SheetPartition d) (i : Fin d) : ℕ :=
  ((coarse.block i).image fine.repr).card

/-- If a refinement induces only one fine block inside a coarse block, then
the two blocks containing the chosen sheet coincide. -/
theorem block_eq_of_refines_of_blockCountWithin_eq_one
    (fine coarse : SheetPartition d) (hRefines : fine.Refines coarse)
    (i : Fin d) (hCount : fine.blockCountWithin coarse i = 1) :
    fine.block i = coarse.block i := by
  have hImageCard : ((coarse.block i).image fine.repr).card = 1 := hCount
  obtain ⟨only, hOnly⟩ := Finset.card_eq_one.mp hImageCard
  apply Finset.Subset.antisymm
  · intro sheet hFine
    exact (coarse.mem_block_iff i sheet).mpr
      (hRefines.rel ((fine.mem_block_iff i sheet).mp hFine))
  · intro sheet hCoarse
    apply (fine.mem_block_iff i sheet).mpr
    have hIImage : fine.repr i ∈ (coarse.block i).image fine.repr :=
      Finset.mem_image.mpr ⟨i, coarse.self_mem_block i, rfl⟩
    have hSheetImage : fine.repr sheet ∈ (coarse.block i).image fine.repr :=
      Finset.mem_image.mpr ⟨sheet, hCoarse, rfl⟩
    have hIOnly : fine.repr i = only := by
      simpa [hOnly] using hIImage
    have hSheetOnly : fine.repr sheet = only := by
      simpa [hOnly] using hSheetImage
    exact hIOnly.trans hSheetOnly.symm

/-- Cardinality form of `block_eq_of_refines_of_blockCountWithin_eq_one`. -/
theorem blockCard_eq_of_refines_of_blockCountWithin_eq_one
    (fine coarse : SheetPartition d) (hRefines : fine.Refines coarse)
    (i : Fin d) (hCount : fine.blockCountWithin coarse i = 1) :
    fine.blockCard i = coarse.blockCard i := by
  unfold blockCard
  rw [fine.block_eq_of_refines_of_blockCountWithin_eq_one coarse hRefines i
    hCount]

/-- Every coarse block contains at least one induced fine block. -/
theorem blockCountWithin_pos (fine coarse : SheetPartition d) (i : Fin d) :
    0 < fine.blockCountWithin coarse i := by
  unfold blockCountWithin
  apply Finset.card_pos.mpr
  exact ⟨fine.repr i, Finset.mem_image.mpr
    ⟨i, coarse.self_mem_block i, rfl⟩⟩

/-- Counting the pasted fine blocks inside a pasted coarse block is exactly
the corresponding local block count selected by the original wall block. -/
theorem paste_blockCountWithin (wall : SheetPartition d)
    (fine coarse : Fin d → SheetPartition d)
    (hFine : ∀ anchor, (fine anchor).Refines wall)
    (hCoarse : ∀ anchor, (coarse anchor).Refines wall) (sheet : Fin d) :
    (wall.paste fine hFine).blockCountWithin
        (wall.paste coarse hCoarse) sheet =
      (fine (wall.repr sheet)).blockCountWithin
        (coarse (wall.repr sheet)) sheet := by
  unfold blockCountWithin
  rw [wall.paste_block coarse hCoarse sheet]
  congr 1
  ext image
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨source, hSource, hImage⟩
    have hLocal : (coarse (wall.repr sheet)).Rel sheet source :=
      (mem_block_iff _ _ _).mp hSource
    have hWall : wall.Rel sheet source :=
      (hCoarse (wall.repr sheet)).rel hLocal
    have hRepr :
        (wall.paste fine hFine).repr source =
          (fine (wall.repr sheet)).repr source := by
      rw [paste_repr]
      unfold Rel at hWall
      rw [← hWall]
    exact ⟨source, hSource, hRepr.symm.trans hImage⟩
  · rintro ⟨source, hSource, hImage⟩
    have hLocal : (coarse (wall.repr sheet)).Rel sheet source :=
      (mem_block_iff _ _ _).mp hSource
    have hWall : wall.Rel sheet source :=
      (hCoarse (wall.repr sheet)).rel hLocal
    have hRepr :
        (wall.paste fine hFine).repr source =
          (fine (wall.repr sheet)).repr source := by
      rw [paste_repr]
      unfold Rel at hWall
      rw [← hWall]
    exact ⟨source, hSource, hRepr.trans hImage⟩

/-- A fixed fine partition counts the same blocks inside a pasted coarse
block as inside the local coarse block selected there. -/
theorem blockCountWithin_paste (wall fine : SheetPartition d)
    (coarse : Fin d → SheetPartition d)
    (hCoarse : ∀ anchor, (coarse anchor).Refines wall) (sheet : Fin d) :
    fine.blockCountWithin (wall.paste coarse hCoarse) sheet =
      fine.blockCountWithin (coarse (wall.repr sheet)) sheet := by
  unfold blockCountWithin
  rw [wall.paste_block coarse hCoarse sheet]

/-- A partition induces one of its own blocks inside that block. -/
@[simp] theorem blockCountWithin_self (partition : SheetPartition d)
    (i : Fin d) :
    partition.blockCountWithin partition i = 1 := by
  unfold blockCountWithin
  have himage : (partition.block i).image partition.repr = {partition.repr i} := by
    ext representative
    constructor
    · intro hRepresentative
      obtain ⟨sheet, hSheet, rfl⟩ := Finset.mem_image.mp hRepresentative
      exact Finset.mem_singleton.mpr
        ((partition.mem_block_iff i sheet).mp hSheet).symm
    · intro hRepresentative
      have hRepresentativeEq := Finset.mem_singleton.mp hRepresentative
      subst representative
      exact Finset.mem_image.mpr
        ⟨i, partition.self_mem_block i, rfl⟩
  rw [himage]
  simp

/-- Any refinement induces exactly one block inside a singleton coarse block. -/
theorem blockCountWithin_eq_one_of_block_eq_singleton
    (fine coarse : SheetPartition d) (i : Fin d)
    (hBlock : coarse.block i = {i}) :
    fine.blockCountWithin coarse i = 1 := by
  unfold blockCountWithin
  rw [hBlock]
  simp

/-- On the selected original block, `splitBlock` induces one singleton block
for each sheet. -/
theorem splitBlock_blockCountWithin_of_rel (partition : SheetPartition d)
    (anchor i : Fin d) (hi : partition.Rel anchor i) :
    (partition.splitBlock anchor).blockCountWithin partition i =
      partition.blockCard i := by
  unfold blockCountWithin blockCard
  rw [← partition.block_eq_of_rel hi]
  have himage :
      (partition.block anchor).image (partition.splitBlock anchor).repr =
        partition.block anchor := by
    ext sheet
    constructor
    · intro hSheet
      obtain ⟨original, hOriginal, hRepr⟩ := Finset.mem_image.mp hSheet
      have hOriginalRel :=
        (partition.mem_block_iff anchor original).mp hOriginal
      rw [partition.splitBlock_repr_of_rel anchor original hOriginalRel] at hRepr
      simpa [← hRepr] using hOriginal
    · intro hSheet
      have hSheetRel := (partition.mem_block_iff anchor sheet).mp hSheet
      exact Finset.mem_image.mpr
        ⟨sheet, hSheet,
          partition.splitBlock_repr_of_rel anchor sheet hSheetRel⟩
  rw [himage]

/-- If `endpoint` refines `wall`, then splitting the selected wall block into
singletons induces one block for every sheet of each endpoint block inside
that wall block. -/
theorem splitBlock_blockCountWithin_of_refines
    (wall endpoint : SheetPartition d) (anchor i : Fin d)
    (hRefines : endpoint.Refines wall) (hi : wall.Rel anchor i) :
    (wall.splitBlock anchor).blockCountWithin endpoint i =
      endpoint.blockCard i := by
  unfold blockCountWithin blockCard
  have himage :
      (endpoint.block i).image (wall.splitBlock anchor).repr =
        endpoint.block i := by
    ext sheet
    constructor
    · intro hSheet
      obtain ⟨original, hOriginal, hRepr⟩ := Finset.mem_image.mp hSheet
      have hEndpoint := (endpoint.mem_block_iff i original).mp hOriginal
      have hWall : wall.Rel anchor original :=
        hi.trans (hRefines.rel hEndpoint)
      rw [wall.splitBlock_repr_of_rel anchor original hWall] at hRepr
      simpa [← hRepr] using hOriginal
    · intro hSheet
      have hEndpoint := (endpoint.mem_block_iff i sheet).mp hSheet
      have hWall : wall.Rel anchor sheet :=
        hi.trans (hRefines.rel hEndpoint)
      exact Finset.mem_image.mpr
        ⟨sheet, hSheet, wall.splitBlock_repr_of_rel anchor sheet hWall⟩
  rw [himage]

/-- Any further refinement of `splitBlock` still has one singleton block per
sheet of the selected original block. -/
theorem blockCountWithin_eq_blockCard_of_refines_splitBlock
    (fine partition : SheetPartition d) (anchor i : Fin d)
    (hRefines : fine.Refines (partition.splitBlock anchor))
    (hi : partition.Rel anchor i) :
    fine.blockCountWithin partition i = partition.blockCard i := by
  unfold blockCountWithin blockCard
  rw [← partition.block_eq_of_rel hi]
  have himage :
      (partition.block anchor).image fine.repr = partition.block anchor := by
    ext sheet
    constructor
    · intro hSheet
      obtain ⟨original, hOriginal, rfl⟩ := Finset.mem_image.mp hSheet
      have hOriginalRel :=
        (partition.mem_block_iff anchor original).mp hOriginal
      have hFineRel : fine.Rel original (fine.repr original) :=
        fine.rel_repr_right original
      have hSplitRel := hRefines.rel hFineRel
      have hEq :=
        (partition.splitBlock_rel_of_rel_anchor_iff anchor original
          hOriginalRel (fine.repr original)).mp hSplitRel
      simpa [← hEq] using hOriginal
    · intro hSheet
      have hSheetRel := (partition.mem_block_iff anchor sheet).mp hSheet
      have hFineRel : fine.Rel sheet (fine.repr sheet) := fine.rel_repr_right sheet
      have hSplitRel := hRefines.rel hFineRel
      have hEq :=
        (partition.splitBlock_rel_of_rel_anchor_iff anchor sheet hSheetRel
          (fine.repr sheet)).mp hSplitRel
      exact Finset.mem_image.mpr ⟨sheet, hSheet, hEq.symm⟩
  rw [himage]

/-- The same singleton-count conclusion from the block-local refinement used
by pasted wall resolutions. -/
theorem blockCountWithin_eq_blockCard_of_refinesOnBlock_splitBlock
    (fine endpoint wall : SheetPartition d) (anchor i : Fin d)
    (hFine : fine.RefinesOnBlock (wall.splitBlock anchor) wall anchor)
    (hEndpoint : endpoint.Refines wall) (hi : wall.Rel anchor i) :
    fine.blockCountWithin endpoint i = endpoint.blockCard i := by
  unfold blockCountWithin blockCard
  have himage : (endpoint.block i).image fine.repr = endpoint.block i := by
    ext sheet
    constructor
    · intro hSheet
      obtain ⟨original, hOriginal, rfl⟩ := Finset.mem_image.mp hSheet
      have hEndpointRel := (endpoint.mem_block_iff i original).mp hOriginal
      have hWall : wall.Rel anchor original :=
        hi.trans (hEndpoint.rel hEndpointRel)
      have hFineRel : fine.Rel original (fine.repr original) :=
        fine.rel_repr_right original
      have hSplitRel := hFine.rel hWall hFineRel
      have hEq :=
        (wall.splitBlock_rel_of_rel_anchor_iff anchor original hWall
          (fine.repr original)).mp hSplitRel
      simpa [← hEq] using hOriginal
    · intro hSheet
      have hEndpointRel := (endpoint.mem_block_iff i sheet).mp hSheet
      have hWall : wall.Rel anchor sheet :=
        hi.trans (hEndpoint.rel hEndpointRel)
      have hFineRel : fine.Rel sheet (fine.repr sheet) :=
        fine.rel_repr_right sheet
      have hSplitRel := hFine.rel hWall hFineRel
      have hEq :=
        (wall.splitBlock_rel_of_rel_anchor_iff anchor sheet hWall
          (fine.repr sheet)).mp hSplitRel
      exact Finset.mem_image.mpr ⟨sheet, hSheet, hEq.symm⟩
  rw [himage]

/-- Two representative maps present the same underlying partition. -/
def SameBlocks (first second : SheetPartition d) : Prop :=
  ∀ i j, first.Rel i j ↔ second.Rel i j

theorem SameBlocks.refl (partition : SheetPartition d) :
    partition.SameBlocks partition := fun _ _ ↦ Iff.rfl

theorem SameBlocks.symm {first second : SheetPartition d}
    (h : first.SameBlocks second) : second.SameBlocks first :=
  fun i j ↦ (h i j).symm

theorem SameBlocks.trans {first second third : SheetPartition d}
    (hFirst : first.SameBlocks second) (hSecond : second.SameBlocks third) :
    first.SameBlocks third :=
  fun i j ↦ (hFirst i j).trans (hSecond i j)

theorem SameBlocks.block_eq {first second : SheetPartition d}
    (h : first.SameBlocks second) (i : Fin d) :
    first.block i = second.block i := by
  ext j
  rw [mem_block_iff, mem_block_iff, h i j]

theorem SameBlocks.blockCard_eq {first second : SheetPartition d}
    (h : first.SameBlocks second) (i : Fin d) :
    first.blockCard i = second.blockCard i := by
  simp [blockCard, h.block_eq i]

theorem SameBlocks.blockCountWithin_eq_coarse
    (fine : SheetPartition d) {first second : SheetPartition d}
    (h : first.SameBlocks second) (i : Fin d) :
    fine.blockCountWithin first i = fine.blockCountWithin second i := by
  simp [blockCountWithin, h.block_eq i]

theorem SameBlocks.refines_iff_left {first second coarse : SheetPartition d}
    (h : first.SameBlocks second) :
    first.Refines coarse ↔ second.Refines coarse := by
  constructor
  · intro hrefine i j hij
    exact hrefine.rel ((h i j).mpr hij)
  · intro hrefine i j hij
    exact hrefine.rel ((h i j).mp hij)

theorem SameBlocks.refines_iff_right {fine first second : SheetPartition d}
    (h : first.SameBlocks second) :
    fine.Refines first ↔ fine.Refines second := by
  constructor
  · intro hrefine i j hij
    exact (h i j).mp (hrefine.rel hij)
  · intro hrefine i j hij
    exact (h i j).mpr (hrefine.rel hij)

/-! ## Sheet relabelling -/

/-- Transport a sheet partition along a permutation. -/
def relabel (partition : SheetPartition d) (permutation : Equiv.Perm (Fin d)) :
    SheetPartition d where
  repr := fun i ↦ permutation (partition.repr (permutation.symm i))
  repr_idem := by
    intro i
    simp only [Equiv.symm_apply_apply]
    rw [partition.repr_idem]

/-- Relabelling twice is relabelling by the composite permutation. -/
theorem relabel_relabel (partition : SheetPartition d)
    (first second : Equiv.Perm (Fin d)) :
    (partition.relabel first).relabel second =
      partition.relabel (first.trans second) := by
  cases partition
  rfl

@[simp] theorem relabel_rel_iff (partition : SheetPartition d)
    (permutation : Equiv.Perm (Fin d)) (i j : Fin d) :
    (partition.relabel permutation).Rel (permutation i) (permutation j) ↔
      partition.Rel i j := by
  simp [Rel, relabel]

theorem relabel_block (partition : SheetPartition d)
    (permutation : Equiv.Perm (Fin d)) (i : Fin d) :
    (partition.relabel permutation).block (permutation i) =
      (partition.block i).image permutation := by
  ext j
  constructor
  · intro hj
    have hrel : partition.Rel i (permutation.symm j) := by
      apply (partition.relabel_rel_iff permutation i (permutation.symm j)).mp
      simpa using (mem_block_iff _ _ _).mp hj
    exact Finset.mem_image.mpr
      ⟨permutation.symm j, (mem_block_iff _ _ _).mpr hrel, by simp⟩
  · intro hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact (mem_block_iff _ _ _).mpr
      ((partition.relabel_rel_iff permutation i k).mpr
        ((mem_block_iff _ _ _).mp hk))

theorem relabel_blockCard (partition : SheetPartition d)
    (permutation : Equiv.Perm (Fin d)) (i : Fin d) :
    (partition.relabel permutation).blockCard (permutation i) =
      partition.blockCard i := by
  rw [blockCard, partition.relabel_block permutation i, blockCard]
  exact Finset.card_image_iff.mpr permutation.injective.injOn

theorem relabel_blockCountWithin (fine coarse : SheetPartition d)
    (permutation : Equiv.Perm (Fin d)) (i : Fin d) :
    (fine.relabel permutation).blockCountWithin
        (coarse.relabel permutation) (permutation i) =
      fine.blockCountWithin coarse i := by
  unfold blockCountWithin
  rw [coarse.relabel_block permutation i]
  have himage :
      (((coarse.block i).image permutation).image
          (fine.relabel permutation).repr) =
        ((coarse.block i).image fine.repr).image permutation := by
    ext j
    simp [relabel]
  rw [himage]
  exact Finset.card_image_iff.mpr permutation.injective.injOn

theorem relabel_refines {fine coarse : SheetPartition d}
    (h : fine.Refines coarse) (permutation : Equiv.Perm (Fin d)) :
    (fine.relabel permutation).Refines (coarse.relabel permutation) := by
  intro i j hij
  have hfine : fine.repr (permutation.symm i) =
      fine.repr (permutation.symm j) := permutation.injective hij
  exact congrArg permutation (h.rel hfine)

theorem relabel_sameBlocks_of_pointwise (partition : SheetPartition d)
    (permutation : Equiv.Perm (Fin d))
    (hpoint : ∀ i, partition.Rel (permutation i) i) :
    (partition.relabel permutation).SameBlocks partition := by
  intro i j
  have hi : partition.Rel i (permutation.symm i) := by
    simpa using hpoint (permutation.symm i)
  have hj : partition.Rel j (permutation.symm j) := by
    simpa using hpoint (permutation.symm j)
  constructor
  · intro hij
    exact hi.trans ((permutation.injective hij).trans hj.symm)
  · intro hij
    exact congrArg permutation (hi.symm.trans (hij.trans hj))

/-- A transposition of two sheets in one block preserves every block
setwise. -/
theorem swap_apply_rel_self_of_rel (partition : SheetPartition d)
    {first second : Fin d} (hrel : partition.Rel first second) :
    ∀ i, partition.Rel ((Equiv.swap first second) i) i := by
  intro i
  rw [Equiv.swap_apply_def]
  split_ifs with hiFirst hiSecond
  · subst i
    exact hrel.symm
  · subst i
    exact hrel
  · rfl

/-- Swapping two sheets already in the same block leaves the underlying
partition unchanged.  This is the cut-vertex fact used by a DV branch-swap. -/
theorem relabel_swap_sameBlocks_of_rel (partition : SheetPartition d)
    {first second : Fin d} (hrel : partition.Rel first second) :
    (partition.relabel (Equiv.swap first second)).SameBlocks partition :=
  partition.relabel_sameBlocks_of_pointwise _
    (partition.swap_apply_rel_self_of_rel hrel)

/-- A relabelled edge partition still refines an unchanged cut-vertex
partition when the permutation preserves each cut-vertex block. -/
theorem relabel_refines_fixed_of_pointwise {fine coarse : SheetPartition d}
    (hrefine : fine.Refines coarse) (permutation : Equiv.Perm (Fin d))
    (hpoint : ∀ i, coarse.Rel (permutation i) i) :
    (fine.relabel permutation).Refines coarse := by
  have hBoth := relabel_refines hrefine permutation
  have hSame := coarse.relabel_sameBlocks_of_pointwise permutation hpoint
  exact (hSame.refines_iff_right).mp hBoth

/-- A branch relabelling does not change the number of fine blocks incident
to any unchanged cut-vertex block. -/
theorem relabel_blockCountWithin_fixed_of_pointwise
    (fine coarse : SheetPartition d) (permutation : Equiv.Perm (Fin d))
    (hpoint : ∀ i, coarse.Rel (permutation i) i) (i : Fin d) :
    (fine.relabel permutation).blockCountWithin coarse i =
      fine.blockCountWithin coarse i := by
  have hSame := coarse.relabel_sameBlocks_of_pointwise permutation hpoint
  calc
    (fine.relabel permutation).blockCountWithin coarse i =
        (fine.relabel permutation).blockCountWithin
          (coarse.relabel permutation) i :=
      (hSame.blockCountWithin_eq_coarse (fine.relabel permutation) i).symm
    _ = fine.blockCountWithin coarse (permutation.symm i) := by
      simpa using fine.relabel_blockCountWithin coarse permutation
        (permutation.symm i)
    _ = fine.blockCountWithin coarse i := by
      have hrel : coarse.Rel i (permutation.symm i) := by
        simpa using hpoint (permutation.symm i)
      simp [blockCountWithin, coarse.block_eq_of_rel hrel]

/-- Edge and vertex relations may use different sheet permutations provided
their relative permutation stays inside every coarse vertex block. -/
theorem relabel_refines_of_relative_pointwise
    {fine coarse : SheetPartition d} (hrefine : fine.Refines coarse)
    (finePermutation coarsePermutation : Equiv.Perm (Fin d))
    (hpoint : ∀ i,
      coarse.Rel (coarsePermutation.symm (finePermutation i)) i) :
    (fine.relabel finePermutation).Refines
      (coarse.relabel coarsePermutation) := by
  let relative := finePermutation.trans coarsePermutation.symm
  have hRelative : ∀ i, coarse.Rel (relative i) i := hpoint
  have hComposite : relative.trans coarsePermutation = finePermutation := by
    ext i
    simp [relative]
  have hFixed := relabel_refines_fixed_of_pointwise
    hrefine relative hRelative
  have hBoth := relabel_refines hFixed coarsePermutation
  simpa [relabel_relabel, hComposite] using hBoth

/-- Under the same relative compatibility, the induced fine-block count in
the corresponding relabelled coarse block is unchanged. -/
theorem relabel_blockCountWithin_of_relative_pointwise
    (fine coarse : SheetPartition d)
    (finePermutation coarsePermutation : Equiv.Perm (Fin d))
    (hpoint : ∀ i,
      coarse.Rel (coarsePermutation.symm (finePermutation i)) i)
    (i : Fin d) :
    (fine.relabel finePermutation).blockCountWithin
        (coarse.relabel coarsePermutation) (coarsePermutation i) =
      fine.blockCountWithin coarse i := by
  let relative := finePermutation.trans coarsePermutation.symm
  have hRelative : ∀ j, coarse.Rel (relative j) j := hpoint
  have hComposite : relative.trans coarsePermutation = finePermutation := by
    ext j
    simp [relative]
  calc
    (fine.relabel finePermutation).blockCountWithin
        (coarse.relabel coarsePermutation) (coarsePermutation i) =
      ((fine.relabel relative).relabel coarsePermutation).blockCountWithin
        (coarse.relabel coarsePermutation) (coarsePermutation i) := by
          rw [relabel_relabel, hComposite]
    _ = (fine.relabel relative).blockCountWithin coarse i := by
      exact (fine.relabel relative).relabel_blockCountWithin
        coarse coarsePermutation i
    _ = fine.blockCountWithin coarse i :=
      relabel_blockCountWithin_fixed_of_pointwise
        fine coarse relative hRelative i

/-- The local Riemann--Hurwitz condition at a target vertex.  The incident
edge partitions are required separately to refine `vertex`; the formula here
is exactly
`(sum k_q) - 2 ≥ |A| * (valency - 2)`, interpreted in `ℤ`. -/
def RiemannHurwitzAt (vertex : SheetPartition d)
    (incident : List (SheetPartition d)) : Prop :=
  ∀ i,
    (incident.map (fun edge => (edge.blockCountWithin vertex i : ℤ))).sum - 2 ≥
      (vertex.blockCard i : ℤ) * ((incident.length : ℤ) - 2)

/-- Local Riemann--Hurwitz depends only on the multiset of incident edge
partitions, not on the order chosen to display them. -/
theorem riemannHurwitzAt_iff_of_perm (vertex : SheetPartition d)
    {first second : List (SheetPartition d)} (hPerm : first.Perm second) :
    RiemannHurwitzAt vertex first ↔ RiemannHurwitzAt vertex second := by
  have hLength : first.length = second.length := hPerm.length_eq
  have hCoe : (first : Multiset (SheetPartition d)) = second :=
    Multiset.coe_eq_coe.mpr hPerm
  constructor
  · intro hFirst sheet
    have hSum :
        (first.map (fun edge ↦
          (edge.blockCountWithin vertex sheet : ℤ))).sum =
        (second.map (fun edge ↦
          (edge.blockCountWithin vertex sheet : ℤ))).sum := by
      have hMapped := congrArg
        (fun incident : Multiset (SheetPartition d) ↦
          (incident.map (fun edge ↦
            (edge.blockCountWithin vertex sheet : ℤ))).sum) hCoe
      simpa using hMapped
    unfold RiemannHurwitzAt at hFirst
    rw [← hSum, ← hLength]
    exact hFirst sheet
  · intro hSecond sheet
    have hSum :
        (first.map (fun edge ↦
          (edge.blockCountWithin vertex sheet : ℤ))).sum =
        (second.map (fun edge ↦
          (edge.blockCountWithin vertex sheet : ℤ))).sum := by
      have hMapped := congrArg
        (fun incident : Multiset (SheetPartition d) ↦
          (incident.map (fun edge ↦
            (edge.blockCountWithin vertex sheet : ℤ))).sum) hCoe
      simpa using hMapped
    unfold RiemannHurwitzAt at hSecond
    rw [hSum, hLength]
    exact hSecond sheet

/-- The discrete sheet partition. -/
def discrete (d : ℕ) : SheetPartition d where
  repr := id
  repr_idem := fun _ ↦ rfl

/-- Relabelling singleton blocks leaves the discrete partition literally
unchanged, including its chosen representatives. -/
@[simp] theorem discrete_relabel (permutation : Equiv.Perm (Fin d)) :
    (discrete d).relabel permutation = discrete d := by
  apply SheetPartition.ext_repr
  funext i
  simp [relabel, discrete]

@[simp] theorem discrete_rel_iff (i j : Fin d) :
    (discrete d).Rel i j ↔ i = j := by
  simp [Rel, discrete]

theorem discrete_refines (partition : SheetPartition d) :
    (discrete d).Refines partition := by
  intro i j hij
  exact congrArg partition.repr (discrete_rel_iff i j |>.mp hij)

/-- The one-block partition of a nonempty sheet set. -/
def indiscrete (d : ℕ) [NeZero d] : SheetPartition d where
  repr := fun _ ↦ 0
  repr_idem := fun _ ↦ rfl

@[simp] theorem indiscrete_rel (i j : Fin d) [NeZero d] :
    (indiscrete d).Rel i j := by
  simp [Rel, indiscrete]

theorem refines_indiscrete (partition : SheetPartition d) [NeZero d] :
    partition.Refines (indiscrete d) := by
  intro i j _
  exact indiscrete_rel i j

/-- The cardinalities of all distinct blocks add up to the number of sheets.
Canonical representatives ensure that every block is counted exactly once. -/
theorem sum_blockCard_representatives_eq_degree
    (partition : SheetPartition d) (hDegree : 0 < d) :
    (∑ representative : Fin d,
      if partition.repr representative = representative then
        (partition.blockCard representative : ℤ)
      else 0) = d := by
  let _ : NeZero d := ⟨Nat.ne_of_gt hDegree⟩
  let sheet : Fin d := ⟨0, hDegree⟩
  have hBlocks := partition.sum_blockCard_representatives_eq_blockCard
    (indiscrete d) (refines_indiscrete partition) sheet
  simpa [indiscrete, blockCard, block] using hBlocks

/-- `wall` is the join of the two endpoint partitions: its equivalence
relation is generated by equivalences at either endpoint. -/
def IsJoin (left right wall : SheetPartition d) : Prop :=
  ∀ i j, wall.Rel i j ↔ Relation.EqvGen
    (fun a b ↦ left.Rel a b ∨ right.Rel a b) i j

/-- Either endpoint partition refines its join. -/
theorem IsJoin.left_refines {left right wall : SheetPartition d}
    (h : IsJoin left right wall) : left.Refines wall := by
  intro i j hij
  exact (h i j).mpr (Relation.EqvGen.rel i j (Or.inl hij))

/-- The second endpoint partition also refines its join. -/
theorem IsJoin.right_refines {left right wall : SheetPartition d}
    (h : IsJoin left right wall) : right.Refines wall := by
  intro i j hij
  exact (h i j).mpr (Relation.EqvGen.rel i j (Or.inr hij))

theorem isJoin_comm {left right wall : SheetPartition d}
    (h : IsJoin left right wall) : IsJoin right left wall := by
  intro i j
  rw [h i j]
  constructor
  · exact Relation.EqvGen.mono
      (r := fun a b => left.Rel a b ∨ right.Rel a b)
      (p := fun a b => right.Rel a b ∨ left.Rel a b)
      (fun _ _ hxy => Or.elim hxy Or.inr Or.inl) i j
  · exact Relation.EqvGen.mono
      (r := fun a b => right.Rel a b ∨ left.Rel a b)
      (p := fun a b => left.Rel a b ∨ right.Rel a b)
      (fun _ _ hxy => Or.elim hxy Or.inr Or.inl) i j

/-- Joining a partition with any refinement of it recovers the coarser
partition. -/
theorem isJoin_left_of_refines {coarse fine : SheetPartition d}
    (hRefines : fine.Refines coarse) :
    IsJoin coarse fine coarse := by
  intro i j
  constructor
  · intro hij
    exact Relation.EqvGen.rel i j (Or.inl hij)
  · intro hij
    induction hij with
    | rel x y hxy => exact hxy.elim id hRefines.rel
    | refl => rfl
    | symm => apply Eq.symm; assumption
    | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

theorem isJoin_right_of_refines {coarse fine : SheetPartition d}
    (hRefines : fine.Refines coarse) :
    IsJoin fine coarse coarse :=
  isJoin_comm (isJoin_left_of_refines hRefines)

/-- The two-sheet leaf block and the complementary one-sheet detachment join
back to the original wall partition.  This is the contraction pattern shared
by the first M-11 and M-1k candidates. -/
theorem isJoin_pairBlock_detachSheet (partition : SheetPartition d)
    (first second : Fin d) (hne : first ≠ second)
    (hTogether : partition.Rel first second) :
    IsJoin (partition.pairBlock first second hne)
      (partition.detachSheet first second hne hTogether) partition := by
  let pair := partition.pairBlock first second hne
  let detached := partition.detachSheet first second hne hTogether
  have hPairRefines : pair.Refines partition :=
    partition.pairBlock_refines first second hne hTogether
  have hDetachedRefines : detached.Refines partition :=
    partition.detachSheet_refines first second hne hTogether
  intro i j
  constructor
  · intro hij
    by_cases hiBlock : partition.Rel first i
    · have hjBlock : partition.Rel first j := by
        unfold Rel at hiBlock hij ⊢
        exact hiBlock.trans hij
      have connect : ∀ x, partition.Rel first x →
          Relation.EqvGen (fun a b ↦ pair.Rel a b ∨ detached.Rel a b)
            x second := by
        intro x hxBlock
        by_cases hxFirst : x = first
        · subst x
          apply Relation.EqvGen.rel
          left
          unfold pair Rel
          rw [partition.pairBlock_repr_first first second hne,
            partition.pairBlock_repr_second first second hne hTogether]
        · apply Relation.EqvGen.rel
          right
          unfold detached Rel
          rw [partition.detachSheet_repr_of_rel_of_ne first second x hne
              hTogether hxFirst hxBlock,
            partition.detachSheet_repr_of_rel_of_ne first second second hne
              hTogether hne.symm hTogether]
      exact Relation.EqvGen.trans i second j (connect i hiBlock)
        (Relation.EqvGen.symm j second (connect j hjBlock))
    · have hjBlock : ¬partition.Rel first j := by
        intro hj
        apply hiBlock
        unfold Rel at hj hij ⊢
        exact hj.trans hij.symm
      apply Relation.EqvGen.rel
      left
      unfold Rel
      rw [partition.pairBlock_repr_of_not_rel first second i hne hiBlock,
        partition.pairBlock_repr_of_not_rel first second j hne hjBlock]
      exact hij
  · intro hGenerated
    induction hGenerated with
    | rel x y hxy => exact hxy.elim hPairRefines.rel hDetachedRefines.rel
    | refl => rfl
    | symm => apply Eq.symm; assumption
    | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- Joining the discrete partition with itself changes nothing. -/
theorem isJoin_discrete_discrete :
    IsJoin (discrete d) (discrete d) (discrete d) := by
  intro i j
  constructor
  · intro hij
    exact Relation.EqvGen.rel i j (Or.inl hij)
  · intro hij
    apply discrete_rel_iff i j |>.mpr
    exact Relation.EqvGen.eqvGen_le
      (fun x y hxy => hxy.elim
        (fun hxy => discrete_rel_iff x y |>.mp hxy)
        (fun hxy => discrete_rel_iff x y |>.mp hxy)) i j hij

/-- Joining any partition with the one-block partition gives the one-block
partition. -/
theorem isJoin_indiscrete_right (partition : SheetPartition d) [NeZero d] :
    IsJoin partition (indiscrete d) (indiscrete d) := by
  intro i j
  constructor
  · intro _
    exact Relation.EqvGen.rel i j (Or.inr (indiscrete_rel i j))
  · intro _
    exact indiscrete_rel i j

theorem isJoin_indiscrete_left (partition : SheetPartition d) [NeZero d] :
    IsJoin (indiscrete d) partition (indiscrete d) :=
  isJoin_comm (isJoin_indiscrete_right partition)

end SheetPartition

end DraismaVargas.Infrastructure
