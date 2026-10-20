module

public import DraismaVargasMarkedCount.MarkedCount.Regrowth
public import DraismaVargasMarkedCount.MarkedCountGeneral.Sheets

@[expose] public section

/-!
# Regrowth, part 1: two sheet-partition operations

The partitions of the regrowth. Two operations on sheet partitions, with the facts the caterpillar
regrowth needs:

* `liftPart e P`: a partition of `Fin d'` lifted along `e : Fin d' ⊕ N ≃ Fin d`, the sheets
  `e (inr n)` being **new singletons**. This is the partition level of "adding singleton sheets"
  (going from degree `d - shed J` to degree `d`), and it is **literally**
  `Sheets.extendPartition P e.symm` (module `Sheets`), so that the regrowth over the old target
  is `Sheets.extendSheets ψ e.symm`. The lemmas here are its facts in the
  orientation `e` that the regrowth uses.
* `blockPart B b`: the partition with the one block `B` (named by `b ∈ B`) and singletons
  elsewhere; `blockPart ∅ b` is discrete. Every partition over the caterpillar tail is of this
  form ("`P_i` and singletons" over `t_i`, "`S_i` and singletons" at `x_i`, ...).

Proved here: the relations, blocks, block counts, refinements, block counts within, and the
relabellings of both.
-/

namespace DraismaVargas.Count.MarkedCountGeneral.CatRegrow

open DraismaVargas.Infrastructure

variable {d d' : ℕ} {N : Type}

/-! ## 1.  One-block partitions -/

section BlockPart

/-- **The partition with one block `B`, named by `b`, and singletons elsewhere.** -/
def blockPart (B : Finset (Fin d)) (b : Fin d) : SheetPartition d where
  repr i := if i ∈ B then b else i
  repr_idem i := by
    by_cases h : i ∈ B
    · simp only [h, ite_true]; split_ifs <;> rfl
    · simp [h]

/-- The name of a one-block partition lies in its block (or the block is empty). -/
def Anchored (B : Finset (Fin d)) (b : Fin d) : Prop := B = ∅ ∨ b ∈ B

theorem anchored_of_mem {B : Finset (Fin d)} {b : Fin d} (h : b ∈ B) : Anchored B b := Or.inr h

theorem anchored_empty (b : Fin d) : Anchored (∅ : Finset (Fin d)) b := Or.inl rfl

variable {B B' : Finset (Fin d)} {b b' : Fin d}

theorem blockPart_repr (i : Fin d) : (blockPart B b).repr i = if i ∈ B then b else i := rfl

theorem blockPart_repr_of_mem {i : Fin d} (h : i ∈ B) : (blockPart B b).repr i = b := by
  simp [blockPart_repr, h]

theorem blockPart_repr_of_not_mem {i : Fin d} (h : i ∉ B) : (blockPart B b).repr i = i := by
  simp [blockPart_repr, h]

@[simp] theorem blockPart_empty (b : Fin d) : blockPart (∅ : Finset (Fin d)) b =
    SheetPartition.discrete d := by
  apply SheetPartition.ext_repr
  funext i
  simp [blockPart_repr, SheetPartition.discrete]

/-- **The relation of a one-block partition.** -/
theorem blockPart_rel_iff (hb : Anchored B b) (i j : Fin d) :
    (blockPart B b).Rel i j ↔ i = j ∨ (i ∈ B ∧ j ∈ B) := by
  unfold SheetPartition.Rel
  rw [blockPart_repr, blockPart_repr]
  rcases hb with rfl | hb
  · simp
  by_cases hi : i ∈ B <;> by_cases hj : j ∈ B
  · simp [hi, hj]
  · rw [ite_eq_left hi, ite_eq_right hj]
    constructor
    · rintro rfl; exact absurd hb hj
    · rintro (rfl | ⟨-, h⟩)
      · exact absurd hi hj
      · exact absurd h hj
  · rw [ite_eq_right hi, ite_eq_left hj]
    constructor
    · rintro rfl; exact absurd hb hi
    · rintro (rfl | ⟨h, -⟩)
      · exact absurd hj hi
      · exact absurd h hi
  · rw [ite_eq_right hi, ite_eq_right hj]
    simp [hi]

theorem blockPart_rel_of_mem {i j : Fin d} (hi : i ∈ B) (hj : j ∈ B) :
    (blockPart B b).Rel i j := by
  unfold SheetPartition.Rel
  rw [blockPart_repr_of_mem hi, blockPart_repr_of_mem hj]

theorem blockPart_rel_iff_of_not_mem (hb : Anchored B b) {i : Fin d} (hi : i ∉ B) (j : Fin d) :
    (blockPart B b).Rel i j ↔ i = j := by
  rw [blockPart_rel_iff hb]
  exact ⟨fun h ↦ h.resolve_right fun h' ↦ hi h'.1, Or.inl⟩

/-- The blocks of a one-block partition. -/
theorem blockPart_block_of_mem (hb : Anchored B b) {i : Fin d} (hi : i ∈ B) :
    (blockPart B b).block i = B := by
  ext j
  rw [SheetPartition.mem_block_iff, blockPart_rel_iff hb]
  constructor
  · rintro (rfl | ⟨-, h⟩)
    · exact hi
    · exact h
  · intro h; exact Or.inr ⟨hi, h⟩

theorem blockPart_block_of_not_mem (hb : Anchored B b) {i : Fin d} (hi : i ∉ B) :
    (blockPart B b).block i = {i} := by
  ext j
  rw [SheetPartition.mem_block_iff, blockPart_rel_iff_of_not_mem hb hi, Finset.mem_singleton,
    eq_comm]

theorem blockPart_blockCard_of_mem (hb : Anchored B b) {i : Fin d} (hi : i ∈ B) :
    (blockPart B b).blockCard i = B.card := by
  unfold SheetPartition.blockCard
  rw [blockPart_block_of_mem hb hi]

theorem blockPart_blockCard_of_not_mem (hb : Anchored B b) {i : Fin d} (hi : i ∉ B) :
    (blockPart B b).blockCard i = 1 := by
  unfold SheetPartition.blockCard
  rw [blockPart_block_of_not_mem hb hi, Finset.card_singleton]

/-- **A one-block partition refines a partition in which its block is one block.** -/
theorem blockPart_refines {P : SheetPartition d} (hb : Anchored B b)
    (h : ∀ i ∈ B, ∀ j ∈ B, P.Rel i j) : (blockPart B b).Refines P := by
  intro i j hij
  rcases (blockPart_rel_iff hb i j).mp hij with rfl | ⟨hi, hj⟩
  · rfl
  · exact h i hi j hj

theorem blockPart_refines_blockPart (hb : Anchored B b) (hBB : B ⊆ B') :
    (blockPart B b).Refines (blockPart B' b') :=
  blockPart_refines hb fun _ hi _ hj ↦ blockPart_rel_of_mem (hBB hi) (hBB hj)

/-- The block of a one-block partition is the image of the representative. -/
theorem image_repr_blockPart (hb : Anchored B b) (C : Finset (Fin d)) (hBC : B ⊆ C) :
    (C.image (blockPart B b).repr) = (C \ B) ∪ (if B.Nonempty then {b} else ∅) := by
  ext i
  simp only [Finset.mem_image, Finset.mem_union, Finset.mem_sdiff]
  rcases hb with rfl | hb
  · simp [SheetPartition.discrete]
  rw [ite_eq_left ⟨b, hb⟩, Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases hjB : j ∈ B
    · rw [blockPart_repr_of_mem hjB]; exact Or.inr rfl
    · rw [blockPart_repr_of_not_mem hjB]; exact Or.inl ⟨hj, hjB⟩
  · rintro (⟨hi, hiB⟩ | h)
    · exact ⟨i, hi, blockPart_repr_of_not_mem hiB⟩
    · rw [h]; exact ⟨b, hBC hb, blockPart_repr_of_mem hb⟩

/-- **Block count of a one-block partition inside a block containing its block.** -/
theorem blockCountWithin_blockPart (hb : Anchored B b) {P : SheetPartition d} {s : Fin d}
    (hBs : B ⊆ P.block s) :
    (blockPart B b).blockCountWithin P s + B.card =
      P.blockCard s + (if B.Nonempty then 1 else 0) := by
  classical
  unfold SheetPartition.blockCountWithin SheetPartition.blockCard
  rw [image_repr_blockPart hb _ hBs]
  have hdisj : Disjoint (P.block s \ B) (if B.Nonempty then {b} else ∅) := by
    split_ifs with hne
    · rw [Finset.disjoint_singleton_right, Finset.mem_sdiff, not_and, not_not]
      intro _
      rcases hb with rfl | hb
      · exact absurd hne (by simp)
      · exact hb
    · exact Finset.disjoint_empty_right _
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hBs]
  have hle := Finset.card_le_card hBs
  split_ifs <;> simp <;> omega

/-- Block count of a one-block partition inside a block disjoint from its block. -/
theorem blockCountWithin_blockPart_of_disjoint {P : SheetPartition d}
    {s : Fin d} (hBs : Disjoint B (P.block s)) :
    (blockPart B b).blockCountWithin P s = P.blockCard s := by
  classical
  unfold SheetPartition.blockCountWithin SheetPartition.blockCard
  congr 1
  ext i
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [blockPart_repr_of_not_mem (Finset.disjoint_right.mp hBs hj)]
    exact hj
  · intro hi
    exact ⟨i, hi, blockPart_repr_of_not_mem (Finset.disjoint_right.mp hBs hi)⟩

/-- **Block count within a one-block partition**, of a one-block partition inside it. -/
theorem blockCountWithin_blockPart_blockPart (hb : Anchored B b) (hb' : Anchored B' b')
    (hBB : B ⊆ B') {s : Fin d} (hs : s ∈ B') :
    (blockPart B b).blockCountWithin (blockPart B' b') s + B.card =
      B'.card + (if B.Nonempty then 1 else 0) := by
  have h := blockCountWithin_blockPart hb (P := blockPart B' b') (s := s)
    (by rw [blockPart_block_of_mem hb' hs]; exact hBB)
  rwa [blockPart_blockCard_of_mem hb' hs] at h

/-- Inside a singleton block, any finer partition has one block. -/
theorem blockCountWithin_of_blockCard_eq_one (fine : SheetPartition d) {P : SheetPartition d}
    {s : Fin d} (h : P.blockCard s = 1) : fine.blockCountWithin P s = 1 := by
  classical
  unfold SheetPartition.blockCountWithin
  have hblock : P.block s = {s} := by
    have hs : s ∈ P.block s := P.self_mem_block s
    unfold SheetPartition.blockCard at h
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp h
    rw [ht] at hs ⊢
    rw [Finset.mem_singleton] at hs
    rw [hs]
  rw [hblock, Finset.image_singleton, Finset.card_singleton]

/-- **Relabelling a one-block partition.** -/
theorem blockPart_relabel (π : Equiv.Perm (Fin d)) :
    (blockPart B b).relabel π = blockPart (B.map π.toEmbedding) (π b) := by
  apply SheetPartition.ext_repr
  funext i
  change π ((blockPart B b).repr (π.symm i)) = (blockPart (B.map π.toEmbedding) (π b)).repr i
  rw [blockPart_repr, blockPart_repr]
  have hmem : i ∈ B.map π.toEmbedding ↔ π.symm i ∈ B := by
    rw [Finset.mem_map_equiv]
  by_cases h : π.symm i ∈ B
  · rw [ite_eq_left h, ite_eq_left (hmem.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h (hmem.mp h')), Equiv.apply_symm_apply]

/-- The number of blocks of a one-block partition. -/
theorem card_blocks_blockPart (hb : Anchored B b) :
    Fintype.card (blockPart B b).Blocks + B.card = d + (if B.Nonempty then 1 else 0) := by
  classical
  change Fintype.card {i : Fin d // (blockPart B b).repr i = i} + B.card = _
  rw [Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun i ↦ (blockPart B b).repr i = i) =
      (Finset.univ \ B) ∪ (if B.Nonempty then {b} else ∅) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
    simp only [Finset.mem_univ, true_and]
    rcases hb with rfl | hb
    · simp [SheetPartition.discrete]
    rw [ite_eq_left ⟨b, hb⟩, Finset.mem_singleton]
    by_cases hi : i ∈ B
    · rw [blockPart_repr_of_mem hi]
      constructor
      · intro h; exact Or.inr h.symm
      · rintro (h | h)
        · exact absurd hi h
        · exact h.symm
    · rw [blockPart_repr_of_not_mem hi]
      simp [hi]
  rw [hfilter]
  have hdisj : Disjoint (Finset.univ \ B) (if B.Nonempty then {b} else ∅) := by
    split_ifs with hne
    · rw [Finset.disjoint_singleton_right, Finset.mem_sdiff, not_and, not_not]
      intro _
      rcases hb with rfl | hb
      · exact absurd hne (by simp)
      · exact hb
    · exact Finset.disjoint_empty_right _
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin]
  have hle : B.card ≤ d := by simpa using Finset.card_le_univ B
  split_ifs <;> simp <;> omega

end BlockPart

/-! ## 2.  Lifting a partition by new singleton sheets -/

section Lift

variable (e : Fin d' ⊕ N ≃ Fin d)

/-- **A partition of `Fin d'`, with the new sheets `e (inr n)` as singletons**: the
`extendPartition` along `e.symm`. -/
def liftPart (P : SheetPartition d') : SheetPartition d := Sheets.extendPartition P e.symm

variable {e}

/-- An old sheet. -/
abbrev old (e : Fin d' ⊕ N ≃ Fin d) (i : Fin d') : Fin d := e (Sum.inl i)

/-- A new sheet. -/
abbrev new (e : Fin d' ⊕ N ≃ Fin d) (n : N) : Fin d := e (Sum.inr n)

theorem old_injective : Function.Injective (old e) := fun _ _ h ↦
  Sum.inl_injective (e.injective h)

theorem new_injective : Function.Injective (new e) := fun _ _ h ↦
  Sum.inr_injective (e.injective h)

@[simp] theorem old_inj {i i' : Fin d'} : old e i = old e i' ↔ i = i' := old_injective.eq_iff
@[simp] theorem new_inj {n n' : N} : new e n = new e n' ↔ n = n' := new_injective.eq_iff
@[simp] theorem old_ne_new (i : Fin d') (n : N) : old e i ≠ new e n := fun h ↦ by
  simpa using e.injective h
@[simp] theorem new_ne_old (i : Fin d') (n : N) : new e n ≠ old e i := fun h ↦ by
  simpa using e.injective h

/-- Every sheet is old or new. -/
theorem sheet_cases (q : Fin d) : (∃ i, q = old e i) ∨ ∃ n, q = new e n := by
  rcases h : e.symm q with i | n
  · exact Or.inl ⟨i, by rw [old, ← h, Equiv.apply_symm_apply]⟩
  · exact Or.inr ⟨n, by rw [new, ← h, Equiv.apply_symm_apply]⟩

variable (P P' : SheetPartition d')

@[simp] theorem liftPart_repr_old (i : Fin d') :
    (liftPart e P).repr (old e i) = old e (P.repr i) :=
  Sheets.extendPartition_repr_inl P e.symm i

@[simp] theorem liftPart_repr_new (n : N) : (liftPart e P).repr (new e n) = new e n :=
  Sheets.extendPartition_repr_inr P e.symm n

@[simp] theorem liftPart_rel_old_old (i i' : Fin d') :
    (liftPart e P).Rel (old e i) (old e i') ↔ P.Rel i i' := by
  unfold SheetPartition.Rel
  rw [liftPart_repr_old, liftPart_repr_old, old_inj]

@[simp] theorem liftPart_rel_old_new (i : Fin d') (n : N) :
    ¬ (liftPart e P).Rel (old e i) (new e n) := by
  unfold SheetPartition.Rel
  rw [liftPart_repr_old, liftPart_repr_new]
  exact old_ne_new _ _

@[simp] theorem liftPart_rel_new_old (i : Fin d') (n : N) :
    ¬ (liftPart e P).Rel (new e n) (old e i) := by
  unfold SheetPartition.Rel
  rw [liftPart_repr_old, liftPart_repr_new]
  exact new_ne_old _ _

theorem liftPart_rel_new_iff (n : N) (q : Fin d) : (liftPart e P).Rel (new e n) q ↔ q = new e n := by
  rcases sheet_cases (e := e) q with ⟨i, rfl⟩ | ⟨n', rfl⟩
  · simp
  · unfold SheetPartition.Rel
    rw [liftPart_repr_new, liftPart_repr_new, new_inj, new_inj, eq_comm]

theorem liftPart_block_old (i : Fin d') :
    (liftPart e P).block (old e i) = (P.block i).map ⟨old e, old_injective⟩ := by
  ext q
  rw [SheetPartition.mem_block_iff, Finset.mem_map]
  rcases sheet_cases (e := e) q with ⟨i', rfl⟩ | ⟨n, rfl⟩
  · rw [liftPart_rel_old_old]
    constructor
    · intro h; exact ⟨i', (P.mem_block_iff i i').mpr h, rfl⟩
    · rintro ⟨i'', hi'', h⟩
      rw [Function.Embedding.coeFn_mk, old_inj] at h
      subst h
      exact (P.mem_block_iff i _).mp hi''
  · simp only [liftPart_rel_old_new, false_iff, not_exists, not_and]
    intro i' _ h
    exact old_ne_new _ _ h

theorem liftPart_block_new (n : N) : (liftPart e P).block (new e n) = {new e n} := by
  ext q
  rw [SheetPartition.mem_block_iff, liftPart_rel_new_iff, Finset.mem_singleton]

@[simp] theorem liftPart_blockCard_old (i : Fin d') :
    (liftPart e P).blockCard (old e i) = P.blockCard i := by
  unfold SheetPartition.blockCard
  rw [liftPart_block_old, Finset.card_map]

@[simp] theorem liftPart_blockCard_new (n : N) : (liftPart e P).blockCard (new e n) = 1 := by
  unfold SheetPartition.blockCard
  rw [liftPart_block_new, Finset.card_singleton]

theorem liftPart_refines {P P' : SheetPartition d'} (h : P.Refines P') :
    (liftPart e P).Refines (liftPart e P') := by
  intro q q' hqq'
  rcases sheet_cases (e := e) q with ⟨i, rfl⟩ | ⟨n, rfl⟩
  · rcases sheet_cases (e := e) q' with ⟨i', rfl⟩ | ⟨n', rfl⟩
    · exact (liftPart_rel_old_old P' i i').mpr (h i i' ((liftPart_rel_old_old P i i').mp hqq'))
    · exact absurd hqq' (liftPart_rel_old_new P i n')
  · rw [(liftPart_rel_new_iff P n q').mp hqq']
    rfl

@[simp] theorem liftPart_blockCountWithin_old (i : Fin d') :
    (liftPart e P).blockCountWithin (liftPart e P') (old e i) = P.blockCountWithin P' i := by
  classical
  unfold SheetPartition.blockCountWithin
  rw [liftPart_block_old, Finset.map_eq_image, Finset.image_image]
  have : ((liftPart e P).repr ∘ ⇑(⟨old e, old_injective⟩ : Fin d' ↪ Fin d)) =
      (fun i ↦ old e i) ∘ P.repr := by
    funext i; simp
  rw [this, ← Finset.image_image, Finset.card_image_of_injective _ old_injective]

@[simp] theorem liftPart_blockCountWithin_new (n : N) :
    (liftPart e P).blockCountWithin (liftPart e P') (new e n) = 1 :=
  blockCountWithin_of_blockCard_eq_one _ (liftPart_blockCard_new P' n)

/-- The sheet permutation acting by `σ` on the old sheets and fixing the new ones. -/
def liftPerm (e : Fin d' ⊕ N ≃ Fin d) (σ : Equiv.Perm (Fin d')) : Equiv.Perm (Fin d) :=
  e.symm.trans ((Equiv.sumCongr σ (Equiv.refl N)).trans e)

@[simp] theorem liftPerm_old (σ : Equiv.Perm (Fin d')) (i : Fin d') :
    liftPerm e σ (old e i) = old e (σ i) := by
  simp [liftPerm]

@[simp] theorem liftPerm_new (σ : Equiv.Perm (Fin d')) (n : N) :
    liftPerm e σ (new e n) = new e n := by
  simp [liftPerm]

@[simp] theorem liftPerm_symm_old (σ : Equiv.Perm (Fin d')) (i : Fin d') :
    (liftPerm e σ).symm (old e i) = old e (σ.symm i) := by
  rw [Equiv.symm_apply_eq, liftPerm_old, Equiv.apply_symm_apply]

@[simp] theorem liftPerm_symm_new (σ : Equiv.Perm (Fin d')) (n : N) :
    (liftPerm e σ).symm (new e n) = new e n := by
  rw [Equiv.symm_apply_eq, liftPerm_new]

/-- **Relabelling commutes with the lift.** -/
theorem liftPart_relabel (σ : Equiv.Perm (Fin d')) :
    (liftPart e P).relabel (liftPerm e σ) = liftPart e (P.relabel σ) := by
  apply SheetPartition.ext_repr
  funext q
  change liftPerm e σ ((liftPart e P).repr ((liftPerm e σ).symm q)) = (liftPart e (P.relabel σ)).repr q
  rcases sheet_cases (e := e) q with ⟨i, rfl⟩ | ⟨n, rfl⟩
  · rw [liftPerm_symm_old, liftPart_repr_old, liftPerm_old, liftPart_repr_old]
    rfl
  · rw [liftPerm_symm_new, liftPart_repr_new, liftPerm_new, liftPart_repr_new]

/-- The number of blocks of a lifted partition: the old blocks and the new singletons. -/
theorem card_blocks_liftPart [Fintype N] :
    Fintype.card (liftPart e P).Blocks = Fintype.card P.Blocks + Fintype.card N := by
  classical
  let f : P.Blocks ⊕ N → (liftPart e P).Blocks
    | .inl b => ⟨old e b.1, by rw [liftPart_repr_old, b.2]⟩
    | .inr n => ⟨new e n, liftPart_repr_new P n⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro (b | n) (b' | n') h <;> have h' := congrArg Subtype.val h <;>
        simp only [f, old_inj, new_inj, old_ne_new, new_ne_old] at h'
      · exact congrArg Sum.inl (Subtype.ext h')
      · exact congrArg Sum.inr h'
    · rintro ⟨q, hq⟩
      rcases sheet_cases (e := e) q with ⟨i, rfl⟩ | ⟨n, rfl⟩
      · rw [liftPart_repr_old, old_inj] at hq
        exact ⟨.inl ⟨i, hq⟩, rfl⟩
      · exact ⟨.inr n, rfl⟩
  rw [← Fintype.card_sum]
  exact (Fintype.card_of_bijective hf).symm

end Lift

end DraismaVargas.Count.MarkedCountGeneral.CatRegrow
