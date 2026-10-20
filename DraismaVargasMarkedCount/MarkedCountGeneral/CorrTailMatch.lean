module

public import DraismaVargasMarkedCount.MarkedCountGeneral.CorrAlloc

@[expose] public section

/-!
# The inverse laws, part 3: matching two tail chains with the same slopes

Two valid tail chains `ch₁, ch₂`
with the same slopes (`|P¹_i| = |P²_i|`), whose `P_1` lie in blocks `B₁, B₂` at the attaching
vertex, are matched by sheet permutations, one per tail vertex and tail slot, built **level by
level up the spine** (as for the independence of the regrowth from its choices: each choice is a
permutation of sheets inside one block at one target vertex, extended along the far side of that
vertex):

* `lv m`: the permutation at level `m` (`lv 0 = θ` at the attaching vertex, then the spine);
* `pathP i`: `lv i`, corrected inside the block below `path i` so that `P¹_i ↦ P²_i`;
* `spineP i`: `pathP i`, corrected inside `S²_i` so that the names match;
* `bridgeP`, `bulbP`, `tipP`: the branches, corrected inside their blocks.

The input `θ` (`TailMatch`) carries `B₁` onto `B₂` and every sheet entering `ch₁` at an ascent to the
sheet entering `ch₂` at that ascent (the matching of the new sheets, `CorrAlloc`).

Proved here: every block goes to the corresponding block, every name to the corresponding name
(`vP_map`, `vP_anchor`, `eP_map`, `eP_anchor`), and the permutations are compatible along every
incidence of the tail (`compat_tail`) and at the attaching vertex (`compat_attach`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral.CatRegrow

noncomputable section

open DraismaVargas.Infrastructure CatSlot TailV

/-- **The data matching two tail chains.** -/
structure TailMatch (d c : ℕ) where
  ch₁ : TailChain d c
  ch₂ : TailChain d c
  B₁ : Finset (Fin d)
  B₂ : Finset (Fin d)
  θ : Equiv.Perm (Fin d)
  valid₁ : ch₁.Valid
  valid₂ : ch₂.Valid
  card : ∀ i, (ch₁.P i).card = (ch₂.P i).card
  P0₁ : ch₁.P 0 ⊆ B₁
  P0₂ : ch₂.P 0 ⊆ B₂
  θB : B₁.map θ.toEmbedding = B₂
  θenter : ∀ q i, ch₁.Enters q i → ch₂.Enters (θ q) i
  enter_notB : ∀ q i, ch₁.Enters q i → q ∉ B₁

namespace TailMatch

variable {d c : ℕ} (M : TailMatch d c)

/-- The block below the path slot `path i`: at the attaching vertex, or at `x_i`. -/
def low₁ (i : Fin (c + 1)) : Finset (Fin d) := Fin.cases M.B₁ M.ch₁.S i
/-- The block below the path slot `path i`, second chain. -/
def low₂ (i : Fin (c + 1)) : Finset (Fin d) := Fin.cases M.B₂ M.ch₂.S i

@[simp] theorem low₁_zero : M.low₁ 0 = M.B₁ := rfl
@[simp] theorem low₂_zero : M.low₂ 0 = M.B₂ := rfl
@[simp] theorem low₁_succ (i : Fin c) : M.low₁ i.succ = M.ch₁.S i := rfl
@[simp] theorem low₂_succ (i : Fin c) : M.low₂ i.succ = M.ch₂.S i := rfl

/-- **The permutation at level `m`.** -/
def lv : ℕ → Equiv.Perm (Fin d)
  | 0 => M.θ
  | m + 1 => if h : m < c then
      adjust (adjust (lv m) (M.low₂ ⟨m, by omega⟩) (M.ch₁.P ⟨m, by omega⟩) (M.ch₂.P ⟨m, by omega⟩)
          (M.ch₁.eA (path ⟨m, by omega⟩)) (M.ch₂.eA (path ⟨m, by omega⟩)))
        (M.ch₂.S ⟨m, h⟩) (M.ch₁.S ⟨m, h⟩) (M.ch₂.S ⟨m, h⟩) (M.ch₁.vA (spine ⟨m, h⟩))
        (M.ch₂.vA (spine ⟨m, h⟩))
    else lv m

/-- **The permutation over the path slot `path i`.** -/
def pathP (i : Fin (c + 1)) : Equiv.Perm (Fin d) :=
  adjust (M.lv i.val) (M.low₂ i) (M.ch₁.P i) (M.ch₂.P i) (M.ch₁.eA (path i)) (M.ch₂.eA (path i))

/-- **The permutation at the spine vertex `x_{i+1}`.** -/
def spineP (i : Fin c) : Equiv.Perm (Fin d) :=
  adjust (M.pathP i.castSucc) (M.ch₂.S i) (M.ch₁.S i) (M.ch₂.S i) (M.ch₁.vA (spine i))
    (M.ch₂.vA (spine i))

theorem lv_zero : M.lv 0 = M.θ := rfl

theorem lv_succ (i : Fin c) : M.lv (i.val + 1) = M.spineP i := by
  simp only [lv, dite_eq_left i.2]
  rfl

/-- The permutation over the bridge of the branch at `x_{i+1}`. -/
def bridgeP (i : Fin c) : Equiv.Perm (Fin d) :=
  adjust (M.spineP i) (M.ch₂.S i) (M.ch₁.Q i) (M.ch₂.Q i) (M.ch₁.eA (bridge i))
    (M.ch₂.eA (bridge i))

/-- The permutation over the bridge entering the bulb `i`. -/
def inP (i : Fin (c + 1)) : Equiv.Perm (Fin d) :=
  Fin.lastCases (motive := fun _ ↦ Equiv.Perm (Fin d)) (M.pathP (Fin.last c)) M.bridgeP i

/-- The permutation at the bulb `i` (and over its leaf edge). -/
def bulbP (i : Fin (c + 1)) : Equiv.Perm (Fin d) :=
  adjust (M.inP i) (M.ch₂.R i) (M.ch₁.R i) (M.ch₂.R i) (M.ch₁.vA (bulb i)) (M.ch₂.vA (bulb i))

/-- The permutation at the tip `i`. -/
def tipP (i : Fin (c + 1)) : Equiv.Perm (Fin d) :=
  adjust (M.bulbP i) (M.ch₂.R i) (M.ch₁.R i) (M.ch₂.R i) (M.ch₁.vA (tip i)) (M.ch₂.vA (tip i))

/-- **The permutation at a tail vertex.** -/
def vP : TailV c → Equiv.Perm (Fin d)
  | Sum.inl (Sum.inl i) => M.spineP i
  | Sum.inl (Sum.inr i) => M.bulbP i
  | Sum.inr i => M.tipP i

/-- **The permutation over a tail slot.** -/
def eP : CatSlot c → Equiv.Perm (Fin d)
  | Sum.inl i => M.pathP i
  | Sum.inr (Sum.inl i) => M.bridgeP i
  | Sum.inr (Sum.inr i) => M.bulbP i

@[simp] theorem inP_last : M.inP (Fin.last c) = M.pathP (Fin.last c) := by simp [inP]
@[simp] theorem inP_castSucc (i : Fin c) : M.inP i.castSucc = M.bridgeP i := by simp [inP]

/-! ## 1.  The spine, by induction -/

theorem P_sub_low₁ (i : Fin (c + 1)) : M.ch₁.P i ⊆ M.low₁ i := by
  induction i using Fin.cases with
  | zero => exact M.P0₁
  | succ i => exact TailChain.P_succ_sub_S i

theorem P_sub_low₂ (i : Fin (c + 1)) : M.ch₂.P i ⊆ M.low₂ i := by
  induction i using Fin.cases with
  | zero => exact M.P0₂
  | succ i => exact TailChain.P_succ_sub_S i

theorem card_S (i : Fin c) : (M.ch₁.S i).card = (M.ch₂.S i).card := by
  have h1 := M.valid₁.card_S i
  have h2 := M.valid₂.card_S i
  rw [M.card, M.card] at h1
  omega

/-- The sheets entering at the step `i` agree with `θ` up to level `i`. -/
theorem lv_enter {q : Fin d} {i : Fin c} (hq : M.ch₁.Enters q i) :
    ∀ m, m ≤ i.val → M.lv m q = M.θ q ∧
      (∀ hm : m < c + 1, M.pathP ⟨m, hm⟩ q = M.θ q) := by
  have hθ := M.θenter q i hq
  -- `θ q` is in no block of the second chain below level `i + 1`
  have hP : ∀ m : Fin (c + 1), m.val ≤ i.val → M.θ q ∉ M.ch₂.P m := by
    intro m hm h
    exact hθ.2 (M.valid₂.convex _ m i.castSucc i.succ (Fin.le_def.mpr (by simpa using hm))
      (Fin.le_def.mpr (by simp)) h hθ.1)
  have hB : M.θ q ∉ M.B₂ := by
    rw [mem_iff_of_map M.θB]
    exact M.enter_notB q i hq
  have hS : ∀ m : Fin c, m.val < i.val → M.θ q ∉ M.ch₂.S m := by
    intro m hm h
    rcases Finset.mem_union.mp h with h | h
    · exact hP m.castSucc (by simp; omega) h
    · exact hP m.succ (by simp; omega) h
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨rfl, fun hm ↦ ?_⟩
    unfold pathP
    exact adjust_out' (by rw [show M.lv (⟨0, hm⟩ : Fin (c + 1)).val = M.θ from rfl]; exact hB)
  | succ m ih =>
    intro hmi
    have hmc : m < c := by omega
    obtain ⟨-, ih2⟩ := ih (by omega)
    have hpm : M.pathP ⟨m, by omega⟩ q = M.θ q := ih2 _
    have hlv : M.lv (m + 1) q = M.θ q := by
      rw [show m + 1 = (⟨m, hmc⟩ : Fin c).val + 1 from rfl, M.lv_succ]
      unfold spineP
      rw [show (⟨m, hmc⟩ : Fin c).castSucc = ⟨m, by omega⟩ from rfl,
        adjust_out' (by rw [hpm]; exact hS ⟨m, hmc⟩ (by simp; omega)), hpm]
    refine ⟨hlv, fun hm ↦ ?_⟩
    unfold pathP
    rw [show (⟨m + 1, hm⟩ : Fin (c + 1)).val = m + 1 from rfl]
    rw [adjust_out' (by rw [hlv]; exact hS ⟨m, hmc⟩ (by simp; omega)), hlv]

theorem pathOK_of (i : Fin (c + 1)) (h : (M.low₁ i).map (M.lv i.val).toEmbedding = M.low₂ i) :
    AdjustOK (M.lv i.val) (M.low₂ i) (M.ch₁.P i) (M.ch₂.P i) (M.ch₁.eA (path i))
      (M.ch₂.eA (path i)) :=
  ⟨fun q hq ↦ (mem_iff_of_map h q).mpr (M.P_sub_low₁ i hq), M.P_sub_low₂ i, M.card i,
    M.valid₁.eA_mem (fun _ ↦ path_ne_loop _ _), M.valid₂.eA_mem (fun _ ↦ path_ne_loop _ _)⟩

theorem spineOK_of (i : Fin c) (h : AdjustOK (M.lv i.castSucc.val) (M.low₂ i.castSucc)
    (M.ch₁.P i.castSucc) (M.ch₂.P i.castSucc) (M.ch₁.eA (path i.castSucc))
    (M.ch₂.eA (path i.castSucc))) :
    AdjustOK (M.pathP i.castSucc) (M.ch₂.S i) (M.ch₁.S i) (M.ch₂.S i) (M.ch₁.vA (spine i))
      (M.ch₂.vA (spine i)) := by
  refine ⟨fun q hq ↦ ?_, subset_rfl, M.card_S i, M.valid₁.vA_mem (spine i),
    M.valid₂.vA_mem (spine i)⟩
  by_cases hq' : q ∈ M.ch₁.P i.castSucc
  · exact TailChain.P_castSucc_sub_S i (adjust_mem h hq')
  · have hP : q ∈ M.ch₁.P i.succ := by
      rcases Finset.mem_union.mp hq with h' | h'
      · exact absurd h' hq'
      · exact h'
    have hen : M.ch₁.Enters q i := ⟨hP, hq'⟩
    have := (M.lv_enter hen i.val le_rfl).2 (by omega)
    rw [show (⟨i.val, by omega⟩ : Fin (c + 1)) = i.castSucc from rfl] at this
    rw [this]
    exact TailChain.P_succ_sub_S i (M.θenter q i hen).1

/-- **Every level carries the block below it onto the corresponding block.** -/
theorem low_map : ∀ i : Fin (c + 1), (M.low₁ i).map (M.lv i.val).toEmbedding = M.low₂ i := by
  suffices H : ∀ (m : ℕ) (hm : m < c + 1),
      (M.low₁ ⟨m, hm⟩).map (M.lv m).toEmbedding = M.low₂ ⟨m, hm⟩ from fun i ↦ H i.val i.2
  intro m
  induction m with
  | zero => intro _; exact M.θB
  | succ m ih =>
    intro hm
    have hmc : m < c := by omega
    have h0 := M.spineOK_of ⟨m, hmc⟩ (M.pathOK_of ⟨m, by omega⟩ (ih (by omega)))
    have e1 : M.lv (m + 1) = M.spineP ⟨m, hmc⟩ := M.lv_succ ⟨m, hmc⟩
    have e2 : (⟨m + 1, hm⟩ : Fin (c + 1)) = (⟨m, hmc⟩ : Fin c).succ := rfl
    rw [e1, e2, low₁_succ, low₂_succ]
    exact adjust_map h0

theorem pathOK (i : Fin (c + 1)) :
    AdjustOK (M.lv i.val) (M.low₂ i) (M.ch₁.P i) (M.ch₂.P i) (M.ch₁.eA (path i))
      (M.ch₂.eA (path i)) := M.pathOK_of i (M.low_map i)

theorem spineOK (i : Fin c) :
    AdjustOK (M.pathP i.castSucc) (M.ch₂.S i) (M.ch₁.S i) (M.ch₂.S i) (M.ch₁.vA (spine i))
      (M.ch₂.vA (spine i)) := M.spineOK_of i (M.pathOK i.castSucc)

theorem pathP_map (i : Fin (c + 1)) :
    (M.ch₁.P i).map (M.pathP i).toEmbedding = M.ch₂.P i := adjust_map (M.pathOK i)

theorem pathP_anchor (i : Fin (c + 1)) :
    M.pathP i (M.ch₁.eA (path i)) = M.ch₂.eA (path i) := adjust_anchor (M.pathOK i)

theorem spineP_map (i : Fin c) :
    (M.ch₁.S i).map (M.spineP i).toEmbedding = M.ch₂.S i := adjust_map (M.spineOK i)

theorem spineP_anchor (i : Fin c) :
    M.spineP i (M.ch₁.vA (spine i)) = M.ch₂.vA (spine i) := adjust_anchor (M.spineOK i)

/-! ## 2.  The branches -/

theorem bridgeOK (i : Fin c) :
    AdjustOK (M.spineP i) (M.ch₂.S i) (M.ch₁.Q i) (M.ch₂.Q i) (M.ch₁.eA (bridge i))
      (M.ch₂.eA (bridge i)) :=
  ⟨fun q hq ↦ (mem_iff_of_map (M.spineP_map i) q).mpr (M.valid₁.Q_sub i hq), M.valid₂.Q_sub i,
    by rw [M.valid₁.card_Q, M.valid₂.card_Q], M.valid₁.eA_mem (fun _ ↦ bridge_ne_loop _ _),
    M.valid₂.eA_mem (fun _ ↦ bridge_ne_loop _ _)⟩

theorem bridgeP_map (i : Fin c) :
    (M.ch₁.Q i).map (M.bridgeP i).toEmbedding = M.ch₂.Q i := adjust_map (M.bridgeOK i)

theorem bridgeP_anchor (i : Fin c) :
    M.bridgeP i (M.ch₁.eA (bridge i)) = M.ch₂.eA (bridge i) := adjust_anchor (M.bridgeOK i)

theorem inP_map (i : Fin (c + 1)) :
    (M.ch₁.R i).map (M.inP i).toEmbedding = M.ch₂.R i := by
  induction i using Fin.lastCases with
  | last => rw [inP_last, TailChain.R_last, TailChain.R_last]; exact M.pathP_map _
  | cast i => rw [inP_castSucc, TailChain.R_castSucc, TailChain.R_castSucc]; exact M.bridgeP_map i

theorem bulbOK (i : Fin (c + 1)) :
    AdjustOK (M.inP i) (M.ch₂.R i) (M.ch₁.R i) (M.ch₂.R i) (M.ch₁.vA (bulb i))
      (M.ch₂.vA (bulb i)) :=
  ⟨fun q hq ↦ (mem_iff_of_map (M.inP_map i) q).mpr hq, subset_rfl,
    by rw [M.valid₁.card_R, M.valid₂.card_R], M.valid₁.vA_mem (bulb i), M.valid₂.vA_mem (bulb i)⟩

theorem bulbP_map (i : Fin (c + 1)) :
    (M.ch₁.R i).map (M.bulbP i).toEmbedding = M.ch₂.R i := adjust_map (M.bulbOK i)

theorem tipOK (i : Fin (c + 1)) :
    AdjustOK (M.bulbP i) (M.ch₂.R i) (M.ch₁.R i) (M.ch₂.R i) (M.ch₁.vA (tip i))
      (M.ch₂.vA (tip i)) :=
  ⟨fun q hq ↦ (mem_iff_of_map (M.bulbP_map i) q).mpr hq, subset_rfl,
    by rw [M.valid₁.card_R, M.valid₂.card_R], M.valid₁.vA_mem (tip i), M.valid₂.vA_mem (tip i)⟩

theorem tipP_map (i : Fin (c + 1)) :
    (M.ch₁.R i).map (M.tipP i).toEmbedding = M.ch₂.R i := adjust_map (M.tipOK i)

/-! ## 3.  Blocks, names and compatibility -/

theorem vP_map (w : TailV c) : (M.ch₁.vB w).map (M.vP w).toEmbedding = M.ch₂.vB w := by
  rcases TailV.cases w with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact M.spineP_map i
  · exact M.bulbP_map i
  · exact M.tipP_map i

theorem vP_anchor (w : TailV c) : M.vP w (M.ch₁.vA w) = M.ch₂.vA w := by
  rcases TailV.cases w with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact M.spineP_anchor i
  · exact adjust_anchor (M.bulbOK i)
  · exact adjust_anchor (M.tipOK i)

theorem eP_map (s : CatSlot c) : (M.ch₁.eB s).map (M.eP s).toEmbedding = M.ch₂.eB s := by
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact M.pathP_map i
  · exact M.bridgeP_map i
  · rfl

theorem eP_anchor {s : CatSlot c} (hs : ∀ i, s ≠ loop i) : M.eP s (M.ch₁.eA s) = M.ch₂.eA s := by
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact M.pathP_anchor i
  · exact M.bridgeP_anchor i
  · exact absurd rfl (hs i)

theorem eP_rowSet (s : CatSlot c) :
    (M.ch₁.rowSet s).map (M.eP s).toEmbedding = M.ch₂.rowSet s := by
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact M.pathP_map i
  · exact M.bridgeP_map i
  · exact M.bulbP_map i

theorem eP_inBridge (i : Fin (c + 1)) : M.eP (inBridge i) = M.inP i := by
  induction i using Fin.lastCases with
  | last => rw [inBridge_last, inP_last]; rfl
  | cast i => rw [inBridge_castSucc, inP_castSucc]; rfl

/-- **Compatibility along every incidence of the tail.** -/
theorem compat_tail (w : TailV c) {s : CatSlot c} (hs : s ∈ incSlots w) (q : Fin d) :
    (blockPart (M.ch₁.vB w) (M.ch₁.vA w)).Rel ((M.vP w).symm (M.eP s q)) q := by
  have hb := M.valid₁.vA_anchored w
  rcases TailV.cases w with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [incSlots_spine] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact compat_head hb (M.spineOK i) q
    · change (blockPart (M.ch₁.S i) _).Rel ((M.spineP i).symm (M.pathP i.succ q)) q
      unfold pathP
      rw [show M.lv i.succ.val = M.spineP i from M.lv_succ i, low₂_succ]
      exact compat_tailEnd hb (M.spineP_map i) q
    · exact compat_tailEnd hb (M.spineP_map i) q
  · rw [incSlots_bulb] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · change (blockPart (M.ch₁.R i) _).Rel ((M.bulbP i).symm (M.eP (inBridge i) q)) q
      rw [eP_inBridge]
      exact compat_head hb (M.bulbOK i) q
    · change (blockPart (M.ch₁.R i) _).Rel ((M.bulbP i).symm (M.bulbP i q)) q
      rw [Equiv.symm_apply_apply]
      rfl
  · rw [incSlots_tip, Finset.mem_singleton] at hs
    subst hs
    exact compat_head hb (M.tipOK i) q

/-- **Compatibility at the attaching vertex**, for any partition in which `B₁` is a block. -/
theorem compat_attach (Px : SheetPartition d) (hblock : ∀ q ∈ M.B₁, ∀ q', Px.Rel q q' ↔ q' ∈ M.B₁)
    (q : Fin d) : Px.Rel (M.θ.symm (M.pathP 0 q)) q := by
  by_cases hq : q ∈ M.B₁
  · have h1 : M.θ q ∈ M.B₂ := (mem_iff_of_map M.θB q).mpr hq
    have h2 : M.pathP 0 q ∈ M.B₂ := adjust_mem_B (M.pathOK 0) h1
    have h3 : M.θ.symm (M.pathP 0 q) ∈ M.B₁ := by
      rw [← mem_iff_of_map M.θB, Equiv.apply_symm_apply]; exact h2
    exact ((hblock q hq _).mpr h3).symm
  · have h1 : M.θ q ∉ M.B₂ := by rw [mem_iff_of_map M.θB]; exact hq
    unfold pathP
    rw [adjust_out' (show M.lv (0 : Fin (c + 1)).val q ∉ M.low₂ 0 from h1),
      show M.lv (0 : Fin (c + 1)).val = M.θ from rfl, Equiv.symm_apply_apply]
    rfl

end TailMatch

end

end DraismaVargas.Count.MarkedCountGeneral.CatRegrow
