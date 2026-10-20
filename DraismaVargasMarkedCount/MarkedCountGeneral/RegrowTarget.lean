module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RegrowSheets
public import DraismaVargasMarkedCount.MarkedCountGeneral.Caterpillar

@[expose] public section

/-!
# Regrowth, part 2: the regrown target

Given a target `T` and target vertices `x : Fin k → T.V` (the images of the marks),
`catTarget T c x` attaches at every `x j` the **target tail** of the regrowth: the path
`x —t_1— x_1 — ⋯ — x_{a-1}` with a two-edge leaf branch `β_i` at every `x_i` (and `β_a` at
`x_{a-1}`; at `x` when `a = 1`), `a = c j + 1`.

The target tail is the image of the caterpillar of `Caterpillar.lean`: its edges are named by
the caterpillar slots `CatSlot c` (a path edge `t_i` over `h_i`, a branch bridge over each bridge
and over `h_a`, a branch leaf edge over each loop), and its vertices by `TailV c`, the caterpillar
vertices `CatVertex c` (`spine i` = `x_{i+1}`, `bulb i` = the middle vertex of the branch at
`A_{i+1}`) together with the tips `tip i` of the branches. The tail end of a slot is `lTail s`
(`none` is the attaching vertex `x`), its head `lHead s`; for the path and bridge slots these are
the caterpillar's `catTail` and `catHead`, and a loop slot ends at its tip.

Vertices are `T.V ⊕ Σ j, TailV (c j)` and occurrences `T.edges ⊕ Σ j, CatSlot (c j)`
(`occEquiv`), all marks at once with no recursion on `k`.

Proved here: the incident slots of every tail vertex (`incSlots`), sums over incident target edges,
connectedness, genus, and the counts.
-/

namespace DraismaVargas.Count.MarkedCountGeneral.CatRegrow

noncomputable section

open DraismaVargas.Infrastructure

/-! ## 1.  One tail -/

/-- **The new target vertices of one tail**: the caterpillar vertices (spine, bulbs), then the
tips. -/
abbrev TailV (c : ℕ) : Type := CatVertex c ⊕ Fin (c + 1)

namespace TailV

variable {c : ℕ}

/-- The spine vertex `x_{i+1}`, under `B_{i+1}`. -/
def spine (i : Fin c) : TailV c := Sum.inl (Sum.inl i)
/-- The middle vertex of the branch at `A_{i+1}` (under the bulb). -/
def bulb (i : Fin (c + 1)) : TailV c := Sum.inl (Sum.inr i)
/-- The tip of the branch at `A_{i+1}`. -/
def tip (i : Fin (c + 1)) : TailV c := Sum.inr i

theorem cases (w : TailV c) : (∃ i, w = spine i) ∨ (∃ i, w = bulb i) ∨ ∃ i, w = tip i := by
  rcases w with (i | i) | i
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr (Or.inl ⟨i, rfl⟩)
  · exact Or.inr (Or.inr ⟨i, rfl⟩)

@[simp] theorem spine_inj {i i' : Fin c} : spine i = spine i' ↔ i = i' := by simp [spine]
@[simp] theorem bulb_inj {i i' : Fin (c + 1)} : bulb (c := c) i = bulb i' ↔ i = i' := by
  simp [bulb]
@[simp] theorem tip_inj {i i' : Fin (c + 1)} : tip (c := c) i = tip i' ↔ i = i' := by simp [tip]
@[simp] theorem spine_ne_bulb (i : Fin c) (i' : Fin (c + 1)) : spine i ≠ bulb i' := by
  simp [spine, bulb]
@[simp] theorem bulb_ne_spine (i : Fin c) (i' : Fin (c + 1)) : bulb i' ≠ spine i := by
  simp [spine, bulb]
@[simp] theorem spine_ne_tip (i : Fin c) (i' : Fin (c + 1)) : spine i ≠ tip i' := by
  simp [spine, tip]
@[simp] theorem tip_ne_spine (i : Fin c) (i' : Fin (c + 1)) : tip i' ≠ spine i := by
  simp [spine, tip]
@[simp] theorem bulb_ne_tip (i i' : Fin (c + 1)) : bulb (c := c) i ≠ tip i' := by
  simp [bulb, tip]
@[simp] theorem tip_ne_bulb (i i' : Fin (c + 1)) : tip (c := c) i' ≠ bulb i := by
  simp [bulb, tip]

theorem card (c : ℕ) : Fintype.card (TailV c) = 3 * c + 2 := by
  simp only [Fintype.card_sum, Fintype.card_fin]; ring

end TailV

theorem card_catSlot (c : ℕ) : Fintype.card (CatSlot c) = 3 * c + 2 := by
  simp only [Fintype.card_sum, Fintype.card_fin]; ring

section Local

variable {c : ℕ}

open CatSlot TailV

/-- **The tail end of a slot**: `none` is the attaching vertex. -/
def lTail : CatSlot c → Option (TailV c) := catTail none fun v ↦ some (Sum.inl v)

/-- **The head end of a slot**: the caterpillar's head for a path or bridge slot, the tip for a
loop slot. -/
def lHead : CatSlot c → TailV c
  | Sum.inl i => Fin.lastCases (motive := fun _ ↦ TailV c) (bulb (Fin.last c)) spine i
  | Sum.inr (Sum.inl i) => bulb i.castSucc
  | Sum.inr (Sum.inr i) => tip i

/-- The slot entering the bulb `i`: the bridge `b_{i+1}`, or `h_{c+1}` for the last bulb. -/
def inBridge (i : Fin (c + 1)) : CatSlot c :=
  Fin.lastCases (motive := fun _ ↦ CatSlot c) (path (Fin.last c)) bridge i

@[simp] theorem inBridge_last : inBridge (Fin.last c) = path (Fin.last c) := by
  simp [inBridge]
@[simp] theorem inBridge_castSucc (i : Fin c) : inBridge i.castSucc = bridge i := by
  simp [inBridge]

@[simp] theorem lTail_path_zero : lTail (path (0 : Fin (c + 1))) = none := by
  simp [lTail, catTail, path]
@[simp] theorem lTail_path_succ (i : Fin c) : lTail (path i.succ) = some (spine i) := by
  simp [lTail, catTail, path, spine]
@[simp] theorem lTail_bridge (i : Fin c) : lTail (bridge i) = some (spine i) := by
  simp [lTail, catTail, bridge, spine]
@[simp] theorem lTail_loop (i : Fin (c + 1)) : lTail (loop i) = some (bulb i) := by
  simp [lTail, catTail, loop, bulb]
@[simp] theorem lHead_path_castSucc (i : Fin c) : lHead (path i.castSucc) = spine i := by
  simp [lHead, path]
@[simp] theorem lHead_path_last : lHead (path (Fin.last c)) = bulb (Fin.last c) := by
  simp [lHead, path]
@[simp] theorem lHead_bridge (i : Fin c) : lHead (bridge i) = bulb i.castSucc := by
  simp [lHead, bridge]
@[simp] theorem lHead_loop (i : Fin (c + 1)) : lHead (loop i) = tip i := by
  simp [lHead, loop]
@[simp] theorem lHead_inBridge (i : Fin (c + 1)) : lHead (inBridge i) = bulb i := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp

/-- Every slot is a path slot, a bridge or a loop. -/
theorem slot_cases (s : CatSlot c) :
    (∃ i, s = path i) ∨ (∃ i, s = bridge i) ∨ ∃ i, s = loop i := by
  rcases s with i | i | i
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr (Or.inl ⟨i, rfl⟩)
  · exact Or.inr (Or.inr ⟨i, rfl⟩)

@[simp] theorem path_inj {i i' : Fin (c + 1)} : path (c := c) i = path i' ↔ i = i' := by
  simp [path]
@[simp] theorem bridge_inj {i i' : Fin c} : bridge i = bridge i' ↔ i = i' := by simp [bridge]
@[simp] theorem loop_inj {i i' : Fin (c + 1)} : loop (c := c) i = loop i' ↔ i = i' := by
  simp [loop]
@[simp] theorem path_ne_bridge (i : Fin (c + 1)) (i' : Fin c) : path i ≠ bridge i' := by
  simp [path, bridge]
@[simp] theorem bridge_ne_path (i : Fin (c + 1)) (i' : Fin c) : bridge i' ≠ path i := by
  simp [path, bridge]
@[simp] theorem path_ne_loop (i i' : Fin (c + 1)) : path (c := c) i ≠ loop i' := by
  simp [path, loop]
@[simp] theorem loop_ne_path (i i' : Fin (c + 1)) : loop (c := c) i' ≠ path i := by
  simp [path, loop]
@[simp] theorem bridge_ne_loop (i : Fin c) (i' : Fin (c + 1)) : bridge i ≠ loop i' := by
  simp [bridge, loop]
@[simp] theorem loop_ne_bridge (i : Fin c) (i' : Fin (c + 1)) : loop i' ≠ bridge i := by
  simp [bridge, loop]

theorem inBridge_ne_loop (i i' : Fin (c + 1)) : inBridge i ≠ loop i' := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp

theorem inBridge_injective : Function.Injective (inBridge (c := c)) := by
  intro i i' h
  induction i using Fin.lastCases <;> induction i' using Fin.lastCases <;>
    simp_all [Fin.ext_iff]

/-- The tail end of a path slot is the attaching vertex or a spine vertex. -/
theorem lTail_path_eq_some_iff (i : Fin (c + 1)) (w : TailV c) :
    lTail (path i) = some w ↔ ∃ i', i = i'.succ ∧ w = spine i' := by
  induction i using Fin.cases with
  | zero => simp [Fin.succ_ne_zero, eq_comm]
  | succ i =>
    rw [lTail_path_succ, Option.some_inj]
    constructor
    · rintro rfl; exact ⟨i, rfl, rfl⟩
    · rintro ⟨i', h, rfl⟩; rw [Fin.succ_inj.mp h]

theorem lTail_path_eq_none_iff (i : Fin (c + 1)) : lTail (path i) = none ↔ i = 0 := by
  induction i using Fin.cases with
  | zero => simp
  | succ i => simp [Fin.succ_ne_zero]

theorem lHead_path_eq_spine_iff (i : Fin (c + 1)) (i' : Fin c) :
    lHead (path i) = spine i' ↔ i = i'.castSucc := by
  induction i using Fin.lastCases with
  | last => simp [(Fin.castSucc_ne_last i').symm]
  | cast i => simp

theorem lHead_path_eq_bulb_iff (i i' : Fin (c + 1)) :
    lHead (path i) = bulb i' ↔ i = Fin.last c ∧ i' = Fin.last c := by
  induction i using Fin.lastCases with
  | last => simp [eq_comm]
  | cast i => simp [Fin.castSucc_ne_last]

/-- **The head of a slot is never its tail.** -/
theorem lTail_ne_lHead (s : CatSlot c) : lTail s ≠ some (lHead s) := by
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · intro h
    obtain ⟨i', rfl, h'⟩ := (lTail_path_eq_some_iff _ _).mp h
    have := (lHead_path_eq_spine_iff _ _).mp h'
    have hv := congrArg Fin.val this
    simp at hv
  · simp
  · simp

/-- **The slots at a tail vertex**: three at a spine vertex (`t_i`, `t_{i+1}`
and the branch bridge), two at a bulb (its bridge and its leaf edge), one at a tip. -/
def incSlots : TailV c → Finset (CatSlot c)
  | Sum.inl (Sum.inl i) => {path i.castSucc, path i.succ, bridge i}
  | Sum.inl (Sum.inr i) => {inBridge i, loop i}
  | Sum.inr i => {loop i}

theorem incSlots_spine (i : Fin c) :
    incSlots (spine i) = {path i.castSucc, path i.succ, bridge i} := rfl
theorem incSlots_bulb (i : Fin (c + 1)) : incSlots (bulb i) = {inBridge i, loop i} := rfl
theorem incSlots_tip (i : Fin (c + 1)) : incSlots (tip i) = {loop i} := rfl

/-- **The incident slots of a tail vertex.** -/
theorem mem_incSlots (w : TailV c) (s : CatSlot c) :
    s ∈ incSlots w ↔ (lTail s = some w ∨ lHead s = w) := by
  rcases TailV.cases w with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [incSlots_spine]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases slot_cases s with ⟨i', rfl⟩ | ⟨i', rfl⟩ | ⟨i', rfl⟩
    · rw [lTail_path_eq_some_iff, lHead_path_eq_spine_iff]
      simp only [path_inj, path_ne_bridge, or_false, spine_inj]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl ⟨i, h, rfl⟩
      · rintro (⟨i'', h, rfl⟩ | h)
        · exact Or.inr h
        · exact Or.inl h
    · simp [eq_comm]
    · simp
  · rw [incSlots_bulb]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases slot_cases s with ⟨i', rfl⟩ | ⟨i', rfl⟩ | ⟨i', rfl⟩
    · rw [lTail_path_eq_some_iff, lHead_path_eq_bulb_iff]
      simp only [path_ne_loop, or_false, bulb_ne_spine, and_false, exists_false, false_or]
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simp [Fin.castSucc_ne_last]
    · simp only [lTail_bridge, lHead_bridge, bridge_ne_loop, or_false, Option.some_inj,
        spine_ne_bulb, false_or, bulb_inj]
      induction i using Fin.lastCases with
      | last => simp [Fin.castSucc_ne_last]
      | cast i => simp
    · simp [inBridge_ne_loop, eq_comm]
  · rw [incSlots_tip]
    simp only [Finset.mem_singleton]
    rcases slot_cases s with ⟨i', rfl⟩ | ⟨i', rfl⟩ | ⟨i', rfl⟩
    · constructor
      · intro h; exact absurd h (path_ne_loop _ _)
      · rintro (h | h)
        · obtain ⟨_, _, h'⟩ := (lTail_path_eq_some_iff _ _).mp h
          exact absurd h' (tip_ne_spine _ _)
        · induction i' using Fin.lastCases <;> simp [lHead, path] at h
    · simp
    · simp [eq_comm]

theorem lTail_eq_none_iff (s : CatSlot c) : lTail s = none ↔ s = path 0 := by
  rcases slot_cases s with ⟨i', rfl⟩ | ⟨i', rfl⟩ | ⟨i', rfl⟩
  · rw [lTail_path_eq_none_iff, path_inj]
  · simp
  · simp

theorem card_incSlots_spine (i : Fin c) : (incSlots (spine i)).card = 3 := by
  rw [incSlots_spine, Finset.card_insert_of_notMem, Finset.card_pair (path_ne_bridge _ _)]
  simp only [Finset.mem_insert, Finset.mem_singleton, path_inj, path_ne_bridge, or_false]
  intro h
  have := congrArg Fin.val h
  simp at this

theorem card_incSlots_bulb (i : Fin (c + 1)) : (incSlots (bulb i)).card = 2 := by
  rw [incSlots_bulb, Finset.card_pair (inBridge_ne_loop _ _)]

theorem card_incSlots_tip (i : Fin (c + 1)) : (incSlots (tip i)).card = 1 := by
  rw [incSlots_tip, Finset.card_singleton]

end Local

/-! ## 2.  All tails at once -/

variable {k : ℕ} (c : Fin k → ℕ)

/-- The tail vertices of all marks. -/
abbrev TV : Type := Σ j, TailV (c j)

/-- The tail slots of all marks (the tail slots of the tailed core). -/
abbrev TE : Type := Σ j, CatSlot (c j)

variable {T : CFGraph.{0}}

/-- The vertices of the regrown target: old ones, then the tail vertices. -/
abbrev Vtx (T : CFGraph.{0}) : Type := T.V ⊕ TV c

/-- The occurrences of the regrown target: old ones, then the tail slots. -/
abbrev Occ (T : CFGraph.{0}) : Type := T.edges ⊕ TE c

instance instDecidableEqOcc : DecidableEq (Occ c T) := Classical.decEq _

instance instDecidableEqVtx : DecidableEq (Vtx c T) := inferInstance

variable (x : Fin k → T.V)

/-- The target vertex of a local tail name at mark `j` (`none` is `x j`). -/
def attach (j : Fin k) : Option (TailV (c j)) → Vtx c T
  | none => Sum.inl (x j)
  | some w => Sum.inr ⟨j, w⟩

/-- The endpoints of an occurrence. -/
def occEnds : Occ c T → Vtx c T × Vtx c T
  | .inl e => (.inl (e : T.V × T.V).1, .inl (e : T.V × T.V).2)
  | .inr te => (attach c x te.1 (lTail te.2), .inr ⟨te.1, lHead te.2⟩)

theorem attach_ne_inr (j : Fin k) (s : CatSlot (c j)) :
    attach c x j (lTail s) ≠ Sum.inr ⟨j, lHead s⟩ := by
  cases h : lTail s with
  | none => simp [attach]
  | some w =>
    simp only [attach, ne_eq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    rintro rfl
    exact lTail_ne_lHead s h

theorem occEnds_ne (o : Occ c T) : (occEnds c x o).1 ≠ (occEnds c x o).2 := by
  rcases o with e | ⟨j, s⟩
  · simp only [occEnds, ne_eq, Sum.inl.injEq]
    exact GenusSixExistence.Tripod.Gluing.fst_ne_snd e
  · exact attach_ne_inr c x j s

/-- **The regrown target**: the target tail at every `x j`. -/
def catTarget (T : CFGraph.{0}) (x : Fin k → T.V) : CFGraph.{0} where
  V := Vtx c T
  instNonempty := ⟨.inl (Classical.choice T.instNonempty)⟩
  edges := (Finset.univ : Finset (Occ c T)).val.map (occEnds c x)
  loopless := by
    intro v hmem
    obtain ⟨o, -, ho⟩ := Multiset.mem_map.mp hmem
    exact occEnds_ne c x o ((congrArg Prod.fst ho).trans (congrArg Prod.snd ho).symm)

/-- **The occurrence dictionary** of the regrown target. -/
def occEquiv : Occ c T ≃ (catTarget c T x).edges :=
  (MarkedCount.Regrow.univEnumeration (Occ c T)).symm.trans
    (Multiset.mapEquiv (Finset.univ : Finset (Occ c T)).val (occEnds c x))

@[simp] theorem occEquiv_ends (o : Occ c T) :
    ((occEquiv c x o : (catTarget c T x).edges) :
      (catTarget c T x).V × (catTarget c T x).V) = occEnds c x o := by
  unfold occEquiv
  exact Multiset.mapEquiv_apply _ _ _

/-! ### Names -/

/-- An old vertex. -/
def oldV (v : T.V) : (catTarget c T x).V := Sum.inl v

/-- A tail vertex. -/
def tailV (w : TV c) : (catTarget c T x).V := Sum.inr w

/-- An old edge. -/
def oldE (e : T.edges) : (catTarget c T x).edges := occEquiv c x (.inl e)

/-- A tail edge. -/
def tailE (t : TE c) : (catTarget c T x).edges := occEquiv c x (.inr t)

/-- The tail end of a tail edge. -/
def tailEnd (t : TE c) : (catTarget c T x).V := attach c x t.1 (lTail t.2)

/-- The head end of a tail edge. -/
def headEnd (t : TE c) : (catTarget c T x).V := tailV c x ⟨t.1, lHead t.2⟩

@[simp] theorem oldE_ends (e : T.edges) :
    ((oldE c x e : (catTarget c T x).edges) : (catTarget c T x).V × (catTarget c T x).V) =
      (oldV c x (e : T.V × T.V).1, oldV c x (e : T.V × T.V).2) := occEquiv_ends c x _

@[simp] theorem tailE_ends (t : TE c) :
    ((tailE c x t : (catTarget c T x).edges) : (catTarget c T x).V × (catTarget c T x).V) =
      (tailEnd c x t, headEnd c x t) := occEquiv_ends c x _

theorem tailEnd_eq_attach (j : Fin k) (s : CatSlot (c j)) :
    tailEnd c x ⟨j, s⟩ = attach c x j (lTail s) := rfl

theorem oldV_injective : Function.Injective (oldV c x) := Sum.inl_injective
theorem tailV_injective : Function.Injective (tailV c x) := Sum.inr_injective

@[simp] theorem oldV_inj {v w : T.V} : oldV c x v = oldV c x w ↔ v = w := (oldV_injective c x).eq_iff
@[simp] theorem tailV_inj {v w : TV c} : tailV c x v = tailV c x w ↔ v = w :=
  (tailV_injective c x).eq_iff
@[simp] theorem oldV_ne_tailV (v : T.V) (w : TV c) : oldV c x v ≠ tailV c x w := Sum.inl_ne_inr
@[simp] theorem tailV_ne_oldV (v : T.V) (w : TV c) : tailV c x w ≠ oldV c x v := Sum.inr_ne_inl

@[simp] theorem tailV_mk_inj {j : Fin k} {w w' : TailV (c j)} :
    tailV c x ⟨j, w⟩ = tailV c x ⟨j, w'⟩ ↔ w = w' := by
  rw [tailV_inj]; simp

@[simp] theorem attach_none (j : Fin k) : attach c x j none = oldV c x (x j) := rfl
@[simp] theorem attach_some (j : Fin k) (w : TailV (c j)) :
    attach c x j (some w) = tailV c x ⟨j, w⟩ := rfl

theorem vertex_cases (v : (catTarget c T x).V) : (∃ w, v = oldV c x w) ∨ ∃ w, v = tailV c x w := by
  rcases v with w | w
  · exact Or.inl ⟨w, rfl⟩
  · exact Or.inr ⟨w, rfl⟩

theorem edge_cases (e : (catTarget c T x).edges) : (∃ f, e = oldE c x f) ∨ ∃ t, e = tailE c x t := by
  obtain ⟨o, rfl⟩ := (occEquiv c x).surjective e
  rcases o with f | t
  · exact Or.inl ⟨f, rfl⟩
  · exact Or.inr ⟨t, rfl⟩

theorem oldE_injective : Function.Injective (oldE c x) := fun _ _ h ↦ by
  simpa [oldE] using (occEquiv c x).injective h
theorem tailE_injective : Function.Injective (tailE c x) := fun _ _ h ↦ by
  simpa [tailE] using (occEquiv c x).injective h

@[simp] theorem oldE_inj {e f : T.edges} : oldE c x e = oldE c x f ↔ e = f :=
  (oldE_injective c x).eq_iff
@[simp] theorem tailE_inj {t t' : TE c} : tailE c x t = tailE c x t' ↔ t = t' :=
  (tailE_injective c x).eq_iff
@[simp] theorem oldE_ne_tailE (e : T.edges) (t : TE c) : oldE c x e ≠ tailE c x t := fun h ↦ by
  simpa [oldE, tailE] using (occEquiv c x).injective h
@[simp] theorem tailE_ne_oldE (e : T.edges) (t : TE c) : tailE c x t ≠ oldE c x e :=
  fun h ↦ oldE_ne_tailE c x e t h.symm

theorem occEquiv_symm_oldE (e : T.edges) : (occEquiv c x).symm (oldE c x e) = .inl e :=
  (occEquiv c x).symm_apply_apply _
theorem occEquiv_symm_tailE (t : TE c) : (occEquiv c x).symm (tailE c x t) = .inr t :=
  (occEquiv c x).symm_apply_apply _

/-! ### Incident target edges -/

/-- Sums over the occurrences split into old edges and tail edges. -/
theorem sum_edges {M : Type*} [AddCommMonoid M] (f : (catTarget c T x).edges → M) :
    ∑ e, f e = ∑ e, f (oldE c x e) + ∑ t, f (tailE c x t) := by
  rw [← (occEquiv c x).sum_comp, Fintype.sum_sum_type]
  rfl

theorem tailEnd_eq_oldV_iff (t : TE c) (v : T.V) :
    tailEnd c x t = oldV c x v ↔ lTail t.2 = none ∧ x t.1 = v := by
  obtain ⟨j, s⟩ := t
  rw [tailEnd_eq_attach]
  cases lTail s with
  | none => exact ⟨fun h ↦ ⟨rfl, Sum.inl_injective h⟩, fun h ↦ by rw [← h.2]; rfl⟩
  | some w => simp

theorem tailEnd_eq_tailV_iff (t : TE c) (j : Fin k) (w : TailV (c j)) :
    tailEnd c x t = tailV c x ⟨j, w⟩ ↔ ∃ h : t.1 = j, lTail t.2 = some (h ▸ w) := by
  obtain ⟨j', s⟩ := t
  rw [tailEnd_eq_attach]
  cases hs : lTail s with
  | none => simp
  | some w' =>
    simp only [attach_some, tailV_inj, Sigma.mk.inj_iff, Option.some.injEq]
    constructor
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, (eq_of_heq h)⟩
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, heq_of_eq h⟩

theorem headEnd_eq_tailV_iff (t : TE c) (j : Fin k) (w : TailV (c j)) :
    headEnd c x t = tailV c x ⟨j, w⟩ ↔ ∃ h : t.1 = j, lHead t.2 = (h ▸ w) := by
  obtain ⟨j', s⟩ := t
  simp only [headEnd, tailV_inj, Sigma.mk.inj_iff]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, eq_of_heq h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, heq_of_eq h⟩

/-- Incidence of a tail edge at a tail vertex of the same mark. -/
theorem tail_incident_iff (j : Fin k) (s : CatSlot (c j)) (w : TailV (c j)) :
    (tailEnd c x ⟨j, s⟩ = tailV c x ⟨j, w⟩ ∨ headEnd c x ⟨j, s⟩ = tailV c x ⟨j, w⟩) ↔
      s ∈ incSlots w := by
  rw [mem_incSlots, tailEnd_eq_tailV_iff, headEnd_eq_tailV_iff]
  simp

/-- A tail edge is incident to a tail vertex only of its own mark. -/
theorem tail_incident_mark {t : TE c} {j : Fin k} {w : TailV (c j)}
    (h : tailEnd c x t = tailV c x ⟨j, w⟩ ∨ headEnd c x t = tailV c x ⟨j, w⟩) : t.1 = j := by
  rcases h with h | h
  · exact ((tailEnd_eq_tailV_iff c x t j w).mp h).1
  · exact ((headEnd_eq_tailV_iff c x t j w).mp h).1

theorem headEnd_ne_oldV (t : TE c) (v : T.V) : headEnd c x t ≠ oldV c x v :=
  tailV_ne_oldV c x v _

/-- **Sums over the incident target edges at an old vertex**: old incident edges, and the first
path edge of every mark over it. -/
theorem sum_incidentEdges_oldV {M : Type*} [AddCommMonoid M] (v : T.V)
    (f : (catTarget c T x).edges → M) :
    ∑ e ∈ GluingDatum.incidentEdges (oldV c x v), f e =
      ∑ e ∈ GluingDatum.incidentEdges v, f (oldE c x e) +
        ∑ j ∈ Finset.univ.filter (fun j ↦ x j = v), f (tailE c x ⟨j, CatSlot.path 0⟩) := by
  classical
  unfold GluingDatum.incidentEdges
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, sum_edges]
  congr 1
  · refine Finset.sum_congr rfl fun e _ ↦ ?_
    simp only [oldE_ends, oldV_inj]
  · rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [tailE_ends, headEnd_ne_oldV, or_false, tailEnd_eq_oldV_iff, lTail_eq_none_iff]
    rw [Finset.sum_eq_single (CatSlot.path 0)]
    · simp
    · intro s _ hs; simp [hs]
    · simp

theorem card_incidentEdges_oldV (v : T.V) :
    (GluingDatum.incidentEdges (oldV c x v)).card =
      (GluingDatum.incidentEdges v).card + (Finset.univ.filter (fun j ↦ x j = v)).card := by
  have h := sum_incidentEdges_oldV c x v (fun _ ↦ (1 : ℕ))
  simpa using h

/-- **The incident target edges at a tail vertex** are its incident slots. -/
theorem incidentEdges_tailV (j : Fin k) (w : TailV (c j)) :
    GluingDatum.incidentEdges (tailV c x ⟨j, w⟩) =
      (incSlots w).map ⟨fun s ↦ tailE c x ⟨j, s⟩, fun _ _ h ↦ by
        simpa using (tailE_injective c x h)⟩ := by
  classical
  ext e
  rw [Finset.mem_map]
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases edge_cases c x e with ⟨f, rfl⟩ | ⟨t, rfl⟩
  · rw [oldE_ends]
    simp only [oldV_ne_tailV, or_self, false_iff, not_exists, not_and]
    intro s _ h
    exact tailE_ne_oldE c x f _ h
  · rw [tailE_ends]
    constructor
    · intro h
      obtain ⟨j', s⟩ := t
      obtain rfl := tail_incident_mark c x h
      exact ⟨s, (tail_incident_iff c x j' s w).mp h, rfl⟩
    · rintro ⟨s, hs, h⟩
      have h' : tailE c x ⟨j, s⟩ = tailE c x t := h
      rw [tailE_inj] at h'
      subst h'
      exact (tail_incident_iff c x j s w).mpr hs

theorem sum_incidentEdges_tailV {M : Type*} [AddCommMonoid M] (j : Fin k) (w : TailV (c j))
    (f : (catTarget c T x).edges → M) :
    ∑ e ∈ GluingDatum.incidentEdges (tailV c x ⟨j, w⟩), f e =
      ∑ s ∈ incSlots w, f (tailE c x ⟨j, s⟩) := by
  rw [incidentEdges_tailV, Finset.sum_map]
  rfl

theorem card_incidentEdges_tailV (j : Fin k) (w : TailV (c j)) :
    (GluingDatum.incidentEdges (tailV c x ⟨j, w⟩)).card = (incSlots w).card := by
  rw [incidentEdges_tailV, Finset.card_map]

/-! ### Connectedness, genus, edge count -/

theorem adj_of_occ (o : Occ c T) :
    (Utilities.underlyingSimpleGraph (catTarget c T x)).Adj (occEnds c x o).1
      (occEnds c x o).2 := by
  have hmem : occEnds c x o ∈ (catTarget c T x).edges :=
    Multiset.mem_map_of_mem _ (Finset.mem_val.mpr (Finset.mem_univ o))
  exact GraphContraction.num_edges_pos_of_mem_edges _ _ _ hmem

theorem reachable_tailE (t : TE c) :
    (Utilities.underlyingSimpleGraph (catTarget c T x)).Reachable (tailEnd c x t)
      (headEnd c x t) :=
  (adj_of_occ c x (.inr t)).reachable

open GenusSixExistence.Tripod.Gluing in
/-- **The regrown target is connected** when `T` is: walk up each spine. -/
theorem catTarget_connected (hT : graph_connected T) : graph_connected (catTarget c T x) := by
  let H := Utilities.underlyingSimpleGraph (catTarget c T x)
  have hOld : ∀ a b : T.V, H.Reachable (oldV c x a) (oldV c x b) :=
    reachable_of_targetEdges H (oldV c x)
      (fun e ↦ (adj_of_occ c x (.inl e)).reachable) hT
  obtain ⟨v₀⟩ := T.instNonempty
  -- every spine vertex is reachable
  have hSpine : ∀ (j : Fin k) (m : ℕ) (i : Fin (c j)), i.val = m →
      H.Reachable (oldV c x v₀) (tailV c x ⟨j, TailV.spine i⟩) := by
    intro j m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hi
      have hEdge := reachable_tailE c x ⟨j, CatSlot.path i.castSucc⟩
      simp only [headEnd, lHead_path_castSucc] at hEdge
      refine SimpleGraph.Reachable.trans ?_ hEdge
      rw [tailEnd_eq_attach]
      rcases Fin.eq_zero_or_eq_succ i.castSucc with h0 | ⟨i', hi'⟩
      · rw [h0, lTail_path_zero, attach_none]
        exact hOld v₀ (x j)
      · rw [hi', lTail_path_succ, attach_some]
        have : i'.val < m := by
          have := congrArg Fin.val hi'
          simp at this
          omega
        exact ih i'.val this i' rfl
  have hNotLoop : ∀ (j : Fin k) (s : CatSlot (c j)), (∀ i, s ≠ CatSlot.loop i) →
      H.Reachable (oldV c x v₀) (tailEnd c x ⟨j, s⟩) := by
    intro j s hs
    rw [tailEnd_eq_attach]
    cases h : lTail s with
    | none => exact hOld v₀ (x j)
    | some w =>
      rw [attach_some]
      rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
      · obtain ⟨i', -, rfl⟩ := (lTail_path_eq_some_iff i w).mp h
        exact hSpine j _ i' rfl
      · rw [lTail_bridge, Option.some_inj] at h
        rw [← h]
        exact hSpine j _ i rfl
      · exact absurd rfl (hs i)
  have hBulb : ∀ (j : Fin k) (i : Fin (c j + 1)),
      H.Reachable (oldV c x v₀) (tailV c x ⟨j, TailV.bulb i⟩) := by
    intro j i
    have hB := reachable_tailE c x ⟨j, inBridge i⟩
    simp only [headEnd, lHead_inBridge] at hB
    exact (hNotLoop j _ (fun i' ↦ inBridge_ne_loop i i')).trans hB
  have hTip : ∀ (j : Fin k) (i : Fin (c j + 1)),
      H.Reachable (oldV c x v₀) (tailV c x ⟨j, TailV.tip i⟩) := by
    intro j i
    have hL := reachable_tailE c x ⟨j, CatSlot.loop i⟩
    simp only [headEnd, lHead_loop, tailEnd_eq_attach, lTail_loop, attach_some] at hL
    exact (hBulb j i).trans hL
  rw [Utilities.graph_connected_iff_underlyingSimpleGraph_connected,
    SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨oldV c x v₀, fun v ↦ ?_⟩
  rcases vertex_cases c x v with ⟨w, rfl⟩ | ⟨⟨j, w⟩, rfl⟩
  · exact hOld v₀ w
  · rcases TailV.cases w with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact hSpine j _ i rfl
    · exact hBulb j i
    · exact hTip j i

theorem card_edges_catTarget :
    Multiset.card (catTarget c T x).edges = Multiset.card T.edges + ∑ j, (3 * c j + 2) := by
  change Multiset.card ((Finset.univ : Finset (Occ c T)).val.map (occEnds c x)) = _
  rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_sum,
    Fintype.card_sigma]
  simp only [card_catSlot, Multiset.card_coe]

theorem card_V_catTarget :
    Fintype.card (catTarget c T x).V = Fintype.card T.V + ∑ j, (3 * c j + 2) := by
  change Fintype.card (T.V ⊕ TV c) = _
  rw [Fintype.card_sum, Fintype.card_sigma]
  simp only [TailV.card]

/-- **The regrown target has the genus of `T`.** -/
theorem genus_catTarget : genus (catTarget c T x) = genus T := by
  unfold genus
  rw [card_edges_catTarget, card_V_catTarget]
  push_cast
  ring

end

end DraismaVargas.Count.MarkedCountGeneral.CatRegrow
