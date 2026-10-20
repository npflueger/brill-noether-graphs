module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RegrowTarget

@[expose] public section

/-!
# Regrowth, part 3: tail chains

A `TailChain d c` records the blocks of the regrowth over one target tail of genus
`a = c + 1`, 0-indexed:

* `P i` (`i : Fin (c + 1)`): the block over the path slot `path i` (`P_{i+1}`; `P c = P_a` lies
  over the last branch bridge `h_a`), with `|P i| = s_{i+1}`;
* `Q i` (`i : Fin c`): the 2-subset over the bridge of the branch at `x_{i+1}`;
* the names `vA`, `eA` of the blocks (any sheets of the blocks: a datum stores a representative).

The derived blocks are `S i = P i ∪ P (i + 1)` at the spine vertex `x_{i+1}`, `R i` (the block of
the bridge entering the bulb `i`: `Q i`, or `P c` for the last bulb) at the bulb and the tip, and
the empty block (the discrete partition) over the leaf edges.

`TailChain.Valid` collects the conditions on these blocks: `|P c| = 2`, `|Q i| = 2`, every
`P i` nonempty, consecutive blocks nested with sizes differing by one (an ascent adds a sheet, a
descent drops one), `Q i ⊆ S i`, the names in their blocks, and **convexity**: a sheet that leaves
the chain never returns (`P_{i+1}` is `P_i` with one sheet added or removed, and an added sheet is
a new one).

Proved here: the refinement facts (`eB_sub_vB_head`, `eB_sub_vB_tail`), the cardinalities, and the
sizes of the blocks at the spine vertices.
-/

namespace DraismaVargas.Count.MarkedCountGeneral.CatRegrow

open DraismaVargas.Infrastructure CatSlot TailV

/-- **The blocks of one tail**. -/
structure TailChain (d c : ℕ) where
  /-- The block over the path slot `path i`. -/
  P : Fin (c + 1) → Finset (Fin d)
  /-- The block over the bridge of the branch at `x_{i+1}`. -/
  Q : Fin c → Finset (Fin d)
  /-- The names of the blocks at the tail vertices. -/
  vA : TailV c → Fin d
  /-- The names of the blocks over the tail slots. -/
  eA : CatSlot c → Fin d

namespace TailChain

variable {d c : ℕ} (ch : TailChain d c)

/-- The block `S_{i+1} = P_{i+1} ∪ P_{i+2}` at the spine vertex `x_{i+1}`. -/
def S (i : Fin c) : Finset (Fin d) := ch.P i.castSucc ∪ ch.P i.succ

/-- The block over a slot (empty over a leaf edge). -/
def eB : CatSlot c → Finset (Fin d)
  | Sum.inl i => ch.P i
  | Sum.inr (Sum.inl i) => ch.Q i
  | Sum.inr (Sum.inr _) => ∅

/-- The block of the bridge entering the bulb `i`. -/
def R (i : Fin (c + 1)) : Finset (Fin d) := ch.eB (inBridge i)

/-- The block at a tail vertex. -/
def vB : TailV c → Finset (Fin d)
  | Sum.inl (Sum.inl i) => ch.S i
  | Sum.inl (Sum.inr i) => ch.R i
  | Sum.inr i => ch.R i

/-- **The surviving sheets over a slot**: its block, or for a leaf edge the block of its branch
(the two loop edges). -/
def rowSet : CatSlot c → Finset (Fin d)
  | Sum.inr (Sum.inr i) => ch.R i
  | s => ch.eB s

@[simp] theorem eB_path (i : Fin (c + 1)) : ch.eB (path i) = ch.P i := rfl
@[simp] theorem eB_bridge (i : Fin c) : ch.eB (bridge i) = ch.Q i := rfl
@[simp] theorem eB_loop (i : Fin (c + 1)) : ch.eB (loop i) = ∅ := rfl
@[simp] theorem vB_spine (i : Fin c) : ch.vB (spine i) = ch.S i := rfl
@[simp] theorem vB_bulb (i : Fin (c + 1)) : ch.vB (bulb i) = ch.R i := rfl
@[simp] theorem vB_tip (i : Fin (c + 1)) : ch.vB (tip i) = ch.R i := rfl
@[simp] theorem rowSet_path (i : Fin (c + 1)) : ch.rowSet (path i) = ch.P i := rfl
@[simp] theorem rowSet_bridge (i : Fin c) : ch.rowSet (bridge i) = ch.Q i := rfl
@[simp] theorem rowSet_loop (i : Fin (c + 1)) : ch.rowSet (loop i) = ch.R i := rfl
@[simp] theorem R_last : ch.R (Fin.last c) = ch.P (Fin.last c) := by simp [R]
@[simp] theorem R_castSucc (i : Fin c) : ch.R i.castSucc = ch.Q i := by simp [R]

theorem rowSet_of_not_loop {s : CatSlot c} (hs : ∀ i, s ≠ loop i) : ch.rowSet s = ch.eB s := by
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rfl
  · rfl
  · exact absurd rfl (hs i)

/-- **The conditions on the blocks.** -/
structure Valid : Prop where
  card_P_last : (ch.P (Fin.last c)).card = 2
  card_Q : ∀ i, (ch.Q i).card = 2
  P_nonempty : ∀ i, (ch.P i).Nonempty
  step : ∀ i : Fin c,
    (ch.P i.castSucc ⊆ ch.P i.succ ∧ (ch.P i.succ).card = (ch.P i.castSucc).card + 1) ∨
      (ch.P i.succ ⊆ ch.P i.castSucc ∧ (ch.P i.castSucc).card = (ch.P i.succ).card + 1)
  Q_sub : ∀ i, ch.Q i ⊆ ch.S i
  vA_mem : ∀ w, ch.vA w ∈ ch.vB w
  eA_anchored : ∀ s, Anchored (ch.eB s) (ch.eA s)
  convex : ∀ (q : Fin d) (i₁ i₂ i₃ : Fin (c + 1)), i₁ ≤ i₂ → i₂ ≤ i₃ → q ∈ ch.P i₁ →
    q ∈ ch.P i₃ → q ∈ ch.P i₂

variable {ch}

theorem Valid.card_R (h : ch.Valid) (i : Fin (c + 1)) : (ch.R i).card = 2 := by
  induction i using Fin.lastCases with
  | last => rw [R_last]; exact h.card_P_last
  | cast i => rw [R_castSucc]; exact h.card_Q i

theorem Valid.R_nonempty (h : ch.Valid) (i : Fin (c + 1)) : (ch.R i).Nonempty := by
  rw [← Finset.card_pos, h.card_R]; omega

theorem Valid.vA_anchored (h : ch.Valid) (w : TailV c) : Anchored (ch.vB w) (ch.vA w) :=
  anchored_of_mem (h.vA_mem w)

theorem Valid.eB_nonempty (h : ch.Valid) {s : CatSlot c} (hs : ∀ i, s ≠ loop i) :
    (ch.eB s).Nonempty := by
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact h.P_nonempty i
  · rw [eB_bridge, ← Finset.card_pos, h.card_Q]; omega
  · exact absurd rfl (hs i)

theorem Valid.eA_mem (h : ch.Valid) {s : CatSlot c} (hs : ∀ i, s ≠ loop i) : ch.eA s ∈ ch.eB s :=
  (h.eA_anchored s).resolve_left (h.eB_nonempty hs).ne_empty

theorem Valid.R_sub_S (h : ch.Valid) (i : Fin c) : ch.R i.castSucc ⊆ ch.S i := by
  rw [R_castSucc]; exact h.Q_sub i

theorem P_castSucc_sub_S (i : Fin c) : ch.P i.castSucc ⊆ ch.S i := Finset.subset_union_left
theorem P_succ_sub_S (i : Fin c) : ch.P i.succ ⊆ ch.S i := Finset.subset_union_right

/-- **A slot's block lies in the block at its head.** -/
theorem Valid.eB_sub_vB_head (_h : ch.Valid) (s : CatSlot c) : ch.eB s ⊆ ch.vB (lHead s) := by
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · induction i using Fin.lastCases with
    | last => simp
    | cast i => rw [lHead_path_castSucc, vB_spine, eB_path]; exact P_castSucc_sub_S i
  · simp
  · simp

/-- **A slot's block lies in the block at its tail**, when the tail is a tail vertex. -/
theorem Valid.eB_sub_vB_tail (h : ch.Valid) {s : CatSlot c} {w : TailV c}
    (hw : lTail s = some w) : ch.eB s ⊆ ch.vB w := by
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · obtain ⟨i', rfl, rfl⟩ := (lTail_path_eq_some_iff _ _).mp hw
    rw [vB_spine, eB_path]
    exact P_succ_sub_S i'
  · rw [lTail_bridge, Option.some_inj] at hw
    subst hw
    exact h.Q_sub i
  · simp

/-- **The size of the spine block**: `|S_i| = max(s_i, s_{i+1})`, the larger of two consecutive
blocks. -/
theorem Valid.card_S (h : ch.Valid) (i : Fin c) :
    2 * (ch.S i).card = (ch.P i.castSucc).card + (ch.P i.succ).card + 1 := by
  unfold S
  rcases h.step i with ⟨hsub, hcard⟩ | ⟨hsub, hcard⟩
  · rw [Finset.union_eq_right.mpr hsub]; omega
  · rw [Finset.union_eq_left.mpr hsub]; omega

theorem Valid.S_nonempty (h : ch.Valid) (i : Fin c) : (ch.S i).Nonempty :=
  (h.P_nonempty i.castSucc).mono (P_castSucc_sub_S i)

theorem Valid.vB_nonempty (h : ch.Valid) (w : TailV c) : (ch.vB w).Nonempty :=
  ⟨ch.vA w, h.vA_mem w⟩

/-- The surviving sheets over a slot lie in the block at its head. -/
theorem Valid.rowSet_sub_vB_head (h : ch.Valid) (s : CatSlot c) :
    ch.rowSet s ⊆ ch.vB (lHead s) := by
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact h.eB_sub_vB_head _
  · exact h.eB_sub_vB_head _
  · simp

theorem Valid.card_rowSet_loop (h : ch.Valid) (i : Fin (c + 1)) :
    (ch.rowSet (loop i)).card = 2 := h.card_R i

variable (ch) in
/-- **The genus a tail adds** (before the new sheets are counted): blocks over the slots minus
blocks at the tail vertices, after cancelling the `d` sheets on each side. -/
def genusContribution : ℤ :=
  (∑ s : CatSlot c, ((if (ch.eB s).Nonempty then 1 else 0 : ℤ) - (ch.eB s).card)) +
    ∑ w : TailV c, (((ch.vB w).card : ℤ) - 1)

/-- **The genus of a tail**: `2 · contribution = 3c + 4 - |P_1|`; with `|P_1| = c + 2 - 2J` it is
`c + 1 + J` (the tail genus `a`, and one for every shed sheet, which `- |N|` removes). -/
theorem Valid.two_mul_genusContribution (h : ch.Valid) :
    2 * ch.genusContribution = 3 * c + 4 - (ch.P 0).card := by
  classical
  have hsplitS : ∀ f : CatSlot c → ℤ,
      ∑ s, f s = ∑ i, f (path i) + ∑ i, f (bridge i) + ∑ i, f (loop i) := by
    intro f; rw [Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]; rfl
  have hsplitV : ∀ g : TailV c → ℤ,
      ∑ w, g w = ∑ i, g (spine i) + ∑ i, g (bulb i) + ∑ i, g (tip i) := by
    intro g; rw [Fintype.sum_sum_type, Fintype.sum_sum_type]; rfl
  have hP : ∀ i, (if (ch.eB (path i)).Nonempty then (1 : ℤ) else 0) = 1 := fun i ↦
    ite_eq_left (h.P_nonempty i)
  have hQ : ∀ i, (if (ch.eB (bridge i)).Nonempty then (1 : ℤ) else 0) = 1 := fun i ↦
    ite_eq_left (by change (ch.Q i).Nonempty; rw [← Finset.card_pos, h.card_Q]; omega)
  have hL : ∀ i, (if (ch.eB (loop i)).Nonempty then (1 : ℤ) else 0) = 0 := fun i ↦
    ite_eq_right (by change ¬ (∅ : Finset (Fin d)).Nonempty; simp)
  unfold genusContribution
  rw [hsplitS, hsplitV]
  simp only [hP, hQ, hL]
  simp only [eB_path, eB_bridge, eB_loop, vB_spine, vB_bulb, vB_tip, Finset.card_empty,
    h.card_Q, h.card_R]
  have hSsum : 2 * ∑ i : Fin c, ((ch.S i).card : ℤ) =
      ∑ i : Fin c, (((ch.P i.castSucc).card : ℤ) + (ch.P i.succ).card + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by have := h.card_S i; omega
  have h1 : ∑ i : Fin (c + 1), ((ch.P i).card : ℤ) =
      ∑ i : Fin c, ((ch.P i.castSucc).card : ℤ) + (ch.P (Fin.last c)).card :=
    Fin.sum_univ_castSucc _
  have h2 : ∑ i : Fin (c + 1), ((ch.P i).card : ℤ) =
      (ch.P 0).card + ∑ i : Fin c, ((ch.P i.succ).card : ℤ) := Fin.sum_univ_succ _
  have hlast := h.card_P_last
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hSsum h1 h2 ⊢
  push_cast at hSsum h1 h2 hlast ⊢
  linarith

end TailChain

end DraismaVargas.Count.MarkedCountGeneral.CatRegrow
