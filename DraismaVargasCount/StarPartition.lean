import DraismaVargas.Infrastructure.GluingDatum

/-!
# Star partitions: one distinguished block through sheet `0`, singletons elsewhere

Every partition appearing in the caterpillar-of-loops gluing data -- the pair partitions
`LocalCases.CaterpillarDatum.pairPart` and the ballot-parametrized blocks of
`Count.BallotDatum` alike -- has the same shape: one block, containing the
spine sheet `0`, and singletons everywhere else.  This module gives that shape
a name and the five facts the gluing datum needs about it, once and for all and
for an **abstract** predicate and an abstract degree, so that no downstream
proof ever unfolds a concrete membership test inside a `simp` or a `convert`
(on concrete partitions such unfolding makes elaboration very slow).

## What is proved

* `sheetStar n P` -- the partition of `Fin (n+1)` whose non-singleton block is
  `{k | P k}`, defined for every decidable `P` and idempotent whether or not
  `P 0` holds.
* `sheetStar_rel_iff`, `sheetStar_refines` -- two sheets are related exactly
  when both lie in the block or they are equal, so one star partition refines
  another exactly when the blocks are nested.  Both need `P 0`.
* `sheetStar_blockCard_of_mem`/`_of_not`, `sheetStar_blockCountWithin_of_mem`/`_of_not`
  -- the block through a
  sheet has `|P|` elements inside the block and one outside; a finer star
  partition induces `1 + (|Q| - |P|)` blocks inside the coarse block and one
  outside.
* `card_blocks_sheetStar` -- the source-vertex count `n + 2 - |P|`.
* `sheetStar_discrete`, `sheetStar_eq_discrete` -- the degenerate block `{0}`
  *is* the discrete partition, literally, so a slope-one spine edge needs no
  special case.
* `card_star_eq_card_range` -- counting inside `Fin (n+1)` is counting inside
  `range (n+1)`, which is how `Count.SlopeStack`'s interval counts are used.

## What is NOT proved here (every surviving hypothesis, explicitly)

* `sheetStar_rel_iff`, `sheetStar_refines`, `sheetStar_block_of_mem`,
  `sheetStar_blockCard_of_mem`, `sheetStar_blockCountWithin_of_mem` and
  `card_blocks_sheetStar` all carry `P 0` (and, where two partitions appear,
  `Q 0` and `P ⊆ Q`) as an explicit hypothesis.  Without `P 0` the relation is
  still an equivalence but `0` is no longer its representative and every
  formula below changes; nothing here silently assumes it.
* Nothing here mentions a graph, a target tree, a slope sequence or a gluing
  datum: this is pure `SheetPartition` algebra.
-/

namespace DraismaVargas.Infrastructure

namespace SheetPartition

variable {n : ℕ}

/-- The partition of `Fin (n+1)` whose only non-singleton block is `{k | P k}`.
Idempotence holds whether or not `P 0`: if `P k` then the representative is `0`
and `0` is its own representative either way. -/
def sheetStar (n : ℕ) (P : ℕ → Prop) [DecidablePred P] : SheetPartition (n + 1) where
  repr := fun k => if P k.val then 0 else k
  repr_idem := by
    intro k
    by_cases h : P k.val
    · rw [if_pos h]
      by_cases h0 : P ((0 : Fin (n + 1)) : ℕ)
      · rw [if_pos h0]
      · rw [if_neg h0]
    · rw [if_neg h, if_neg h]

@[simp] theorem sheetStar_repr (P : ℕ → Prop) [DecidablePred P] (k : Fin (n + 1)) :
    (sheetStar n P).repr k = if P k.val then 0 else k := rfl

theorem sheetStar_repr_of_not (P : ℕ → Prop) [DecidablePred P] {k : Fin (n + 1)}
    (h : ¬ P k.val) : (sheetStar n P).repr k = k := by simp [h]

theorem sheetStar_repr_of_mem (P : ℕ → Prop) [DecidablePred P] {k : Fin (n + 1)}
    (h : P k.val) : (sheetStar n P).repr k = 0 := by simp [h]

/-- **The relation of a star partition.**  Two sheets are related exactly when
both lie in the block, or they are equal. -/
theorem sheetStar_rel_iff (P : ℕ → Prop) [DecidablePred P] (hP0 : P 0)
    (i j : Fin (n + 1)) :
    (sheetStar n P).Rel i j ↔ ((P i.val ∧ P j.val) ∨ i = j) := by
  have hzero : ((0 : Fin (n + 1)) : ℕ) = 0 := rfl
  rw [rel_iff, sheetStar_repr, sheetStar_repr]
  by_cases hi : P i.val <;> by_cases hj : P j.val
  · rw [if_pos hi, if_pos hj]; exact ⟨fun _ => Or.inl ⟨hi, hj⟩, fun _ => rfl⟩
  · rw [if_pos hi, if_neg hj]
    constructor
    · intro h
      exact absurd (by rw [← h, hzero]; exact hP0) hj
    · rintro (⟨-, h⟩ | rfl)
      · exact absurd h hj
      · exact absurd hi hj
  · rw [if_neg hi, if_pos hj]
    constructor
    · intro h
      exact absurd (by rw [h, hzero]; exact hP0) hi
    · rintro (⟨h, -⟩ | rfl)
      · exact absurd h hi
      · exact absurd hj hi
  · rw [if_neg hi, if_neg hj]
    exact ⟨fun h => Or.inr h, fun h => h.resolve_left (fun hh => hi hh.1)⟩

/-- **Nested blocks refine.** -/
theorem sheetStar_refines (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hP0 : P 0) (hQ0 : Q 0) (hsub : ∀ k, P k → Q k) :
    (sheetStar n P).Refines (sheetStar n Q) := by
  intro i j hij
  rw [sheetStar_rel_iff P hP0] at hij
  rw [sheetStar_rel_iff Q hQ0]
  rcases hij with ⟨hi, hj⟩ | rfl
  · exact Or.inl ⟨hsub _ hi, hsub _ hj⟩
  · exact Or.inr rfl

/-- The block through a sheet of the distinguished block. -/
theorem sheetStar_block_of_mem (P : ℕ → Prop) [DecidablePred P] (hP0 : P 0)
    {σ : Fin (n + 1)} (hσ : P σ.val) :
    (sheetStar n P).block σ = Finset.univ.filter (fun k : Fin (n + 1) => P k.val) := by
  ext k
  rw [mem_block_iff, sheetStar_rel_iff P hP0, Finset.mem_filter]
  constructor
  · rintro (⟨-, h⟩ | rfl)
    · exact ⟨Finset.mem_univ _, h⟩
    · exact ⟨Finset.mem_univ _, hσ⟩
  · intro h; exact Or.inl ⟨hσ, h.2⟩

/-- The block through a sheet outside the distinguished block is a singleton. -/
theorem sheetStar_block_of_not (P : ℕ → Prop) [DecidablePred P] (hP0 : P 0)
    {σ : Fin (n + 1)} (hσ : ¬ P σ.val) : (sheetStar n P).block σ = {σ} := by
  ext k
  rw [mem_block_iff, sheetStar_rel_iff P hP0, Finset.mem_singleton]
  constructor
  · rintro (⟨h, -⟩ | rfl)
    · exact absurd h hσ
    · rfl
  · rintro rfl; exact Or.inr rfl

/-- **Counting inside `Fin (n+1)` is counting inside `range (n+1)`.** -/
theorem card_star_eq_card_range (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun k : Fin (n + 1) => P k.val)).card
      = ((Finset.range (n + 1)).filter P).card := by
  classical
  rw [Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun k => if P k then 1 else 0) (n + 1)]

theorem sheetStar_blockCard_of_mem (P : ℕ → Prop) [DecidablePred P] (hP0 : P 0)
    {σ : Fin (n + 1)} (hσ : P σ.val) :
    (sheetStar n P).blockCard σ = ((Finset.range (n + 1)).filter P).card := by
  rw [blockCard, sheetStar_block_of_mem P hP0 hσ, card_star_eq_card_range]

theorem sheetStar_blockCard_of_not (P : ℕ → Prop) [DecidablePred P] (hP0 : P 0)
    {σ : Fin (n + 1)} (hσ : ¬ P σ.val) : (sheetStar n P).blockCard σ = 1 := by
  rw [blockCard, sheetStar_block_of_not P hP0 hσ, Finset.card_singleton]

/-- **A finer star partition induces `1 + (|Q| - |P|)` blocks inside the coarse
block**: the block `P` itself, and one singleton for each sheet of `Q` outside
`P`. -/
theorem sheetStar_blockCountWithin_of_mem (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (hP0 : P 0) (hQ0 : Q 0)
    (hsub : ∀ k, P k → Q k) {σ : Fin (n + 1)} (hσ : Q σ.val) :
    (sheetStar n P).blockCountWithin (sheetStar n Q) σ
      = 1 + (((Finset.range (n + 1)).filter Q).card
          - ((Finset.range (n + 1)).filter P).card) := by
  classical
  have hzeroval : ((0 : Fin (n + 1)) : ℕ) = 0 := rfl
  have himage : ((sheetStar n Q).block σ).image (sheetStar n P).repr
      = insert 0 (Finset.univ.filter (fun k : Fin (n + 1) => Q k.val ∧ ¬ P k.val)) := by
    rw [sheetStar_block_of_mem Q hQ0 hσ]
    ext r
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · rintro ⟨k, hk, rfl⟩
      by_cases hPk : P k.val
      · exact Or.inl (sheetStar_repr_of_mem P hPk)
      · refine Or.inr ?_
        rw [sheetStar_repr_of_not P hPk]
        exact ⟨hk, hPk⟩
    · rintro (rfl | ⟨hQr, hPr⟩)
      · exact ⟨0, by rw [hzeroval]; exact hQ0, sheetStar_repr_of_mem P (by
          rw [hzeroval]; exact hP0)⟩
      · exact ⟨r, hQr, sheetStar_repr_of_not P hPr⟩
  have hnot : (0 : Fin (n + 1)) ∉
      Finset.univ.filter (fun k : Fin (n + 1) => Q k.val ∧ ¬ P k.val) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hzeroval]
    exact fun h => h.2 hP0
  have hsplit : (Finset.univ.filter (fun k : Fin (n + 1) => Q k.val ∧ ¬ P k.val)).card
      = ((Finset.range (n + 1)).filter Q).card
        - ((Finset.range (n + 1)).filter P).card := by
    have hPQ : (Finset.univ.filter (fun k : Fin (n + 1) => P k.val))
        ⊆ (Finset.univ.filter (fun k : Fin (n + 1) => Q k.val)) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hsub _ hk
    have hsdiff : (Finset.univ.filter (fun k : Fin (n + 1) => Q k.val ∧ ¬ P k.val))
        = (Finset.univ.filter (fun k : Fin (n + 1) => Q k.val))
          \ (Finset.univ.filter (fun k : Fin (n + 1) => P k.val)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    rw [hsdiff, Finset.card_sdiff_of_subset hPQ, card_star_eq_card_range,
      card_star_eq_card_range]
  rw [blockCountWithin, himage, Finset.card_insert_of_notMem hnot, hsplit]
  omega

/-- Outside the coarse block every refinement induces exactly one block. -/
theorem sheetStar_blockCountWithin_of_not (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (hQ0 : Q 0) {σ : Fin (n + 1)}
    (hσ : ¬ Q σ.val) :
    (sheetStar n P).blockCountWithin (sheetStar n Q) σ = 1 :=
  blockCountWithin_eq_one_of_block_eq_singleton _ _ _
    (sheetStar_block_of_not Q hQ0 hσ)

/-- The discrete partition is the star partition of the singleton `{0}`. -/
theorem sheetStar_discrete : sheetStar n (fun k => k = 0) = discrete (n + 1) := by
  apply SheetPartition.ext_repr
  funext k
  show (if k.val = 0 then (0 : Fin (n + 1)) else k) = k
  by_cases h : k.val = 0
  · rw [if_pos h]; exact (Fin.ext h).symm
  · rw [if_neg h]

/-- Any predicate cutting out exactly `{0}` gives the discrete partition. -/
theorem sheetStar_eq_discrete (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ k, P k ↔ k = 0) : sheetStar n P = discrete (n + 1) := by
  rw [show (sheetStar n P) = sheetStar n (fun k => k = 0) by
    apply SheetPartition.ext_repr
    funext k
    show (if P k.val then (0 : Fin (n + 1)) else k)
      = (if k.val = 0 then (0 : Fin (n + 1)) else k)
    by_cases h : k.val = 0
    · rw [if_pos h, if_pos ((hP _).mpr h)]
    · rw [if_neg h, if_neg (fun hh => h ((hP _).mp hh))]]
  exact sheetStar_discrete

/-- **The number of blocks of a star partition**: one for the block itself and
one for every sheet outside it. -/
theorem card_blocks_sheetStar (P : ℕ → Prop) [DecidablePred P] (hP0 : P 0) :
    Fintype.card (sheetStar n P).Blocks
      = (n + 1) + 1 - ((Finset.range (n + 1)).filter P).card := by
  classical
  have hzeroval : ((0 : Fin (n + 1)) : ℕ) = 0 := rfl
  have hle : ((Finset.range (n + 1)).filter P).card ≤ n + 1 := by
    have := Finset.card_filter_le (Finset.range (n + 1)) P
    rwa [Finset.card_range] at this
  have hpos : 1 ≤ ((Finset.range (n + 1)).filter P).card := by
    rw [← card_star_eq_card_range]
    refine Finset.card_pos.mpr ⟨0, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hzeroval]
    exact hP0
  have hEquiv : (sheetStar n P).Blocks ≃ {k : Fin (n + 1) // k = 0 ∨ ¬ P k.val} :=
    Equiv.subtypeEquivRight (fun k => by
      show (sheetStar n P).repr k = k ↔ (k = 0 ∨ ¬ P k.val)
      by_cases h : P k.val
      · rw [sheetStar_repr_of_mem P h]
        constructor
        · intro hk; exact Or.inl hk.symm
        · rintro (rfl | hk)
          · rfl
          · exact absurd h hk
      · rw [sheetStar_repr_of_not P h]
        exact ⟨fun _ => Or.inr h, fun _ => rfl⟩)
  rw [Fintype.card_congr hEquiv, Fintype.card_subtype]
  have hset : (Finset.univ.filter (fun k : Fin (n + 1) => k = 0 ∨ ¬ P k.val))
      = insert 0 (Finset.univ.filter (fun k : Fin (n + 1) => ¬ P k.val)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  have hnot : (0 : Fin (n + 1)) ∉ Finset.univ.filter (fun k : Fin (n + 1) => ¬ P k.val) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hzeroval]
    exact fun h => h hP0
  have hcompl : (Finset.univ.filter (fun k : Fin (n + 1) => ¬ P k.val)).card
      = (n + 1) - ((Finset.range (n + 1)).filter P).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (n + 1)))) (p := fun k : Fin (n + 1) => P k.val)
    rw [Finset.card_univ, Fintype.card_fin, card_star_eq_card_range] at hsplit
    omega
  rw [hset, Finset.card_insert_of_notMem hnot, hcompl]
  omega

end SheetPartition

end DraismaVargas.Infrastructure
