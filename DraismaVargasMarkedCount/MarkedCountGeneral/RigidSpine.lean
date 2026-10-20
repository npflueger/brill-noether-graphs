module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RigidStep
public import DraismaVargasMarkedCount.MarkedCountGeneral.Caterpillar

@[expose] public section

/-!
# The spine of a caterpillar tail (rigidity (1)--(4), module `Rigidity`)

For a caterpillar tail `C : CaterpillarAt H w c` in a cubic core `H` and a member `M` over `H`:

* §1 the incidences of the tail inside `H` (`CaterpillarAt.exists_slot_of_incident`: a slot of `H`
  at a new vertex of the tail is a slot of the tail; `coreIncidence_bulb_pos`,
  `coreIncidence_spine_pos`);
* §2 the lollipop at every bulb (module `MarkedCount.LoopAt`): its bridge row is the slot
  `bulbBridge i` (the bridge `b_{i+1}`, or the last path edge for the last bulb), and its far end
  is the branch vertex of the other end of that slot;
* §3 **the downward induction** (`lone_path`): every path row `h_{i+1}` is a single survivor which
  is the only survivor over its target edge, joining the branch vertices of the two ends of the
  slot. The step is `SpineStep` at the spine vertex, with the lollipop bridge and the upper path
  edge as the two lone survivors;
* §4 the spine facts (`spineHyp`, from which `SpineStep` gives trivalence, `r = 0`, uniqueness of
  the spine vertex over its image, and the index relation).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open Utilities.Certificate.ExplicitPotential (Core)
open scoped DraismaVargas.Infrastructure.GluingContraction

noncomputable section

/-! ## 1.  The tail inside the core -/

namespace CatSlot

variable {c : ℕ}

/-- The canonical tail end of a slot, with `none` for the attaching vertex. -/
abbrev cTail (s : CatSlot c) : Option (CatVertex c) := catTail none some s

/-- The canonical head end of a slot. -/
abbrev cHead (s : CatSlot c) : Option (CatVertex c) := catHead none some s

/-- The bridge of the lollipop at bulb `i`: `b_{i+1}` for `i < c`, the last path edge for
`i = c`. -/
def bulbBridge (i : Fin (c + 1)) : CatSlot c :=
  Fin.lastCases (motive := fun _ ↦ CatSlot c) (Sum.inl (Fin.last c)) (fun i' ↦ Sum.inr (Sum.inl i')) i

@[simp] theorem bulbBridge_last : bulbBridge (Fin.last c) = (Sum.inl (Fin.last c) : CatSlot c) := by
  simp [bulbBridge]

@[simp] theorem bulbBridge_castSucc (i : Fin c) :
    bulbBridge i.castSucc = (Sum.inr (Sum.inl i) : CatSlot c) := by
  simp [bulbBridge]

theorem cTail_path_zero : cTail (Sum.inl 0 : CatSlot c) = none := by
  simp [cTail, catTail]

theorem cTail_path_succ (i : Fin c) :
    cTail (Sum.inl i.succ : CatSlot c) = some (Sum.inl i) := by
  simp [cTail, catTail]

theorem cHead_path_castSucc (i : Fin c) :
    cHead (Sum.inl i.castSucc : CatSlot c) = some (Sum.inl i) := by
  simp [cHead, catHead]

theorem cHead_path_last : cHead (Sum.inl (Fin.last c) : CatSlot c) = some (Sum.inr (Fin.last c)) := by
  simp [cHead, catHead]

theorem cTail_bridge (i : Fin c) : cTail (Sum.inr (Sum.inl i) : CatSlot c) = some (Sum.inl i) :=
  rfl

theorem cHead_bridge (i : Fin c) :
    cHead (Sum.inr (Sum.inl i) : CatSlot c) = some (Sum.inr i.castSucc) := rfl

theorem cTail_loop (i : Fin (c + 1)) : cTail (Sum.inr (Sum.inr i) : CatSlot c) = some (Sum.inr i) :=
  rfl

theorem cHead_loop (i : Fin (c + 1)) : cHead (Sum.inr (Sum.inr i) : CatSlot c) = some (Sum.inr i) :=
  rfl

theorem cHead_bulbBridge (i : Fin (c + 1)) : cHead (bulbBridge i) = some (Sum.inr i) := by
  refine Fin.lastCases ?_ (fun i' ↦ ?_) i
  · rw [bulbBridge_last, cHead_path_last]
  · rw [bulbBridge_castSucc, cHead_bridge]

/-- The slots at a bulb: its loop and its bridge. -/
theorem eq_of_at_bulb {s : CatSlot c} {i : Fin (c + 1)}
    (h : cTail s = some (Sum.inr i) ∨ cHead s = some (Sum.inr i)) :
    s = Sum.inr (Sum.inr i) ∨ s = bulbBridge i := by
  rcases s with j | j | j
  · rcases h with h | h
    · exfalso
      refine Fin.cases ?_ (fun j' ↦ ?_) j h
      · simp [cTail, catTail]
      · simp [cTail, catTail]
    · right
      revert h
      refine Fin.lastCases ?_ (fun j' ↦ ?_) j
      · intro h
        rw [cHead_path_last] at h
        obtain rfl : Fin.last c = i := by simpa using h
        rw [bulbBridge_last]
      · intro h
        rw [cHead_path_castSucc] at h
        simp at h
  · rcases h with h | h
    · simp [cTail, catTail] at h
    · right
      rw [cHead_bridge] at h
      obtain rfl : j.castSucc = i := by simpa using h
      rw [bulbBridge_castSucc]
  · rcases h with h | h <;>
    · left
      obtain rfl : j = i := by simpa [cTail, cHead, catTail, catHead] using h
      rfl

/-- The slots at a spine vertex: the two path edges and the bridge. -/
theorem eq_of_at_spine {s : CatSlot c} {i : Fin c}
    (h : cTail s = some (Sum.inl i) ∨ cHead s = some (Sum.inl i)) :
    s = Sum.inl i.castSucc ∨ s = Sum.inl i.succ ∨ s = Sum.inr (Sum.inl i) := by
  rcases s with j | j | j
  · rcases h with h | h
    · right; left
      revert h
      refine Fin.cases ?_ (fun j' ↦ ?_) j
      · intro h; simp [cTail, catTail] at h
      · intro h
        rw [cTail_path_succ] at h
        obtain rfl : j' = i := by simpa using h
        rfl
    · left
      revert h
      refine Fin.lastCases ?_ (fun j' ↦ ?_) j
      · intro h; rw [cHead_path_last] at h; simp at h
      · intro h
        rw [cHead_path_castSucc] at h
        obtain rfl : j' = i := by simpa using h
        rfl
  · rcases h with h | h
    · right; right
      obtain rfl : j = i := by simpa [cTail, catTail] using h
      rfl
    · simp [cHead, catHead] at h
  · rcases h with h | h <;> simp [cTail, cHead, catTail, catHead] at h

/-- The slot at the attaching vertex: the first path edge. -/
theorem eq_of_at_root {s : CatSlot c} (h : cTail s = none ∨ cHead s = none) :
    s = Sum.inl 0 := by
  rcases s with j | j | j
  · rcases h with h | h
    · revert h
      refine Fin.cases (fun _ ↦ rfl) (fun j' h ↦ ?_) j
      simp [cTail, catTail] at h
    · revert h
      refine Fin.lastCases ?_ (fun j' ↦ ?_) j
      · intro h; simp [cHead, catHead] at h
      · intro h; simp [cHead, catHead] at h
  · rcases h with h | h <;> simp [cTail, cHead, catTail, catHead] at h
  · rcases h with h | h <;> simp [cTail, cHead, catTail, catHead] at h

end CatSlot

namespace CaterpillarAt

variable {N P : ℕ} {H : Core N P} {w : Fin N} {c : ℕ} (C : CaterpillarAt H w c)

open CatSlot

/-- The names of the tail's vertices, `w` for `none`. -/
def vname : Option (CatVertex c) → Fin N := fun o ↦ o.elim w C.vertex

@[simp] theorem vname_none : C.vname none = w := rfl
@[simp] theorem vname_some (x : CatVertex c) : C.vname (some x) = C.vertex x := rfl

theorem vname_injective : Function.Injective C.vname := by
  rintro (_ | x) (_ | y) h
  · rfl
  · exact absurd h.symm (C.vertex_ne y)
  · exact absurd h (C.vertex_ne x)
  · exact congrArg some (C.vertex_injective h)

theorem tail_slot (s : CatSlot c) : H.tail (C.slot s) = C.vname (cTail s) := by
  rw [C.tail_eq, catTail_map C.vname none some s]
  rfl

theorem head_slot (s : CatSlot c) : H.head (C.slot s) = C.vname (cHead s) := by
  rw [C.head_eq, catHead_map C.vname none some s]
  rfl

theorem tail_slot_eq_iff (s : CatSlot c) (o : Option (CatVertex c)) :
    H.tail (C.slot s) = C.vname o ↔ cTail s = o := by
  rw [tail_slot]; exact C.vname_injective.eq_iff

theorem head_slot_eq_iff (s : CatSlot c) (o : Option (CatVertex c)) :
    H.head (C.slot s) = C.vname o ↔ cHead s = o := by
  rw [head_slot]; exact C.vname_injective.eq_iff

/-- The tail contributes three slot ends at each of its vertices. -/
theorem sum_slot_incidence (x : CatVertex c) :
    ∑ s : CatSlot c, ((if H.tail (C.slot s) = C.vertex x then 1 else 0) +
      (if H.head (C.slot s) = C.vertex x then 1 else 0)) = 3 := by
  have h := Tailed.catDegree_some (c' := c) x
  rw [← h]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [← C.vname_some x]
  simp only [C.tail_slot_eq_iff, C.head_slot_eq_iff]

/-- **A slot of `H` at a new vertex of the tail is a slot of the tail** (`H` cubic). -/
theorem exists_slot_of_incident (hH : H.Cubic) (x : CatVertex c) {e : Fin P}
    (he : H.tail e = C.vertex x ∨ H.head e = C.vertex x) : ∃ s, C.slot s = e := by
  classical
  by_contra hNo
  push Not at hNo
  have hDeg := hH (C.vertex x)
  unfold Core.incidenceDegree at hDeg
  set g : Fin P → ℕ := fun e ↦ (if H.tail e = C.vertex x then 1 else 0) +
    (if H.head e = C.vertex x then 1 else 0)
  have hSplit := Finset.sum_add_sum_compl (Finset.univ.image C.slot) g
  rw [Finset.sum_image (fun s _ t _ h ↦ C.slot_injective h)] at hSplit
  change ∑ s, g (C.slot s) + _ = ∑ e, g e at hSplit
  have hTail : ∑ s, g (C.slot s) = 3 := C.sum_slot_incidence x
  have hePos : 0 < g e := by
    rcases he with h | h <;> simp [g, h]
  have heMem : e ∈ (Finset.univ.image C.slot)ᶜ := by
    rw [Finset.mem_compl, Finset.mem_image]
    rintro ⟨s, -, hs⟩
    exact hNo s hs
  have hLe := Finset.single_le_sum (f := g) (fun _ _ ↦ Nat.zero_le _) heMem
  change ∑ e, g e = 3 at hDeg
  omega

theorem coreIncidence_slot (x : Option (CatVertex c)) (s : CatSlot c) :
    Count.coreIncidence H (C.vname x) (C.slot s) =
      (if cTail s = x then 1 else 0) + (if cHead s = x then 1 else 0) := by
  unfold Count.coreIncidence
  simp only [C.tail_slot_eq_iff, C.head_slot_eq_iff]

/-- **The slots at a bulb**: its loop and its bridge. -/
theorem coreIncidence_bulb_pos (hH : H.Cubic) (i : Fin (c + 1)) {e : Fin P}
    (h : 0 < Count.coreIncidence H (C.vertex (Sum.inr i)) e) :
    e = C.slot (Sum.inr (Sum.inr i)) ∨ e = C.slot (bulbBridge i) := by
  have he : H.tail e = C.vertex (Sum.inr i) ∨ H.head e = C.vertex (Sum.inr i) := by
    unfold Count.coreIncidence at h
    by_contra hNo
    push Not at hNo
    simp [hNo.1, hNo.2] at h
  obtain ⟨s, rfl⟩ := C.exists_slot_of_incident hH _ he
  rw [← C.vname_some, C.tail_slot_eq_iff, C.head_slot_eq_iff] at he
  rcases eq_of_at_bulb he with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **The slots at a spine vertex**: the two path edges and the bridge. -/
theorem coreIncidence_spine_pos (hH : H.Cubic) (i : Fin c) {e : Fin P}
    (h : 0 < Count.coreIncidence H (C.vertex (Sum.inl i)) e) :
    e = C.slot (Sum.inl i.castSucc) ∨ e = C.slot (Sum.inl i.succ) ∨
      e = C.slot (Sum.inr (Sum.inl i)) := by
  have he : H.tail e = C.vertex (Sum.inl i) ∨ H.head e = C.vertex (Sum.inl i) := by
    unfold Count.coreIncidence at h
    by_contra hNo
    push Not at hNo
    simp [hNo.1, hNo.2] at h
  obtain ⟨s, rfl⟩ := C.exists_slot_of_incident hH _ he
  rw [← C.vname_some, C.tail_slot_eq_iff, C.head_slot_eq_iff] at he
  rcases eq_of_at_spine he with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- A vertex at a slot is one of its two ends. -/
theorem eq_end_of_coreIncidence_pos {v : Fin N} {e : Fin P}
    (h : 0 < Count.coreIncidence H v e) : v = H.tail e ∨ v = H.head e := by
  unfold Count.coreIncidence at h
  by_contra hNo
  push Not at hNo
  simp [Ne.symm hNo.1, Ne.symm hNo.2] at h

theorem head_bulbBridge (i : Fin (c + 1)) :
    H.head (C.slot (bulbBridge i)) = C.vertex (Sum.inr i) := by
  rw [C.head_slot, cHead_bulbBridge]; rfl

theorem tail_loop (i : Fin (c + 1)) :
    H.tail (C.slot (Sum.inr (Sum.inr i))) = C.vertex (Sum.inr i) := by
  rw [C.tail_slot]; rfl

theorem isLoop (i : Fin (c + 1)) :
    H.tail (C.slot (Sum.inr (Sum.inr i))) = H.head (C.slot (Sum.inr (Sum.inr i))) := by
  rw [C.tail_slot, C.head_slot]; rfl

theorem tail_bulbBridge_ne_head (i : Fin (c + 1)) :
    H.tail (C.slot (bulbBridge i)) ≠ H.head (C.slot (bulbBridge i)) := by
  rw [C.tail_slot, C.head_slot, C.vname_injective.ne_iff]
  refine Fin.lastCases ?_ (fun i' ↦ ?_) i
  · rw [bulbBridge_last, cHead_path_last]
    revert i
    intro _
    rcases Nat.eq_zero_or_pos c with hc | hc
    · subst hc
      simp [cTail, catTail]
    · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      rw [show (Fin.last (c' + 1)) = (Fin.last c').succ from rfl, cTail_path_succ]
      simp
  · rw [bulbBridge_castSucc, cTail_bridge, cHead_bridge]
    simp

theorem tail_path_succ (i : Fin c) :
    H.tail (C.slot (Sum.inl i.succ)) = C.vertex (Sum.inl i) := by
  rw [C.tail_slot, cTail_path_succ]; rfl

theorem head_path_castSucc (i : Fin c) :
    H.head (C.slot (Sum.inl i.castSucc)) = C.vertex (Sum.inl i) := by
  rw [C.head_slot, cHead_path_castSucc]; rfl

theorem tail_bridge (i : Fin c) : H.tail (C.slot (Sum.inr (Sum.inl i))) = C.vertex (Sum.inl i) := by
  rw [C.tail_slot]; rfl

theorem tail_path_zero : H.tail (C.slot (Sum.inl 0)) = w := by
  rw [C.tail_slot, cTail_path_zero]; rfl

theorem head_path_last : H.head (C.slot (Sum.inl (Fin.last c))) = C.vertex (Sum.inr (Fin.last c)) := by
  rw [C.head_slot, cHead_path_last]; rfl

theorem tail_path_ne_head (i : Fin (c + 1)) :
    H.tail (C.slot (Sum.inl i)) ≠ H.head (C.slot (Sum.inl i)) := by
  rw [C.tail_slot, C.head_slot, C.vname_injective.ne_iff]
  revert i
  intro i
  refine Fin.lastCases ?_ (fun i' ↦ ?_) i
  · rw [cHead_path_last]
    rcases Nat.eq_zero_or_pos c with hc | hc
    · subst hc; simp [cTail, catTail]
    · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      rw [show (Fin.last (c' + 1)) = (Fin.last c').succ from rfl, cTail_path_succ]
      simp
  · rw [cHead_path_castSucc]
    rcases Fin.eq_zero_or_eq_succ i'.castSucc with h0 | ⟨j, hj⟩
    · rw [h0, cTail_path_zero]; simp
    · rw [hj, cTail_path_succ]
      have hv : j.val + 1 = i'.val := by
        have := congrArg Fin.val hj
        simp at this
        omega
      simp only [ne_eq, Option.some.injEq, Sum.inl.injEq]
      intro h
      rw [h] at hv
      omega

end CaterpillarAt

/-! ## 2.  Generic: the other end of a source edge -/

section OtherEnd

variable {target : CFGraph} {d : ℕ} {data : GluingDatum target d}

/-- The end of `E` other than `B`. -/
def otherEnd (data : GluingDatum target d) (E : data.SourceEdge) (B : data.SourceVertex) :
    data.SourceVertex :=
  if (data.sourceEnds E).1 = B then (data.sourceEnds E).2 else (data.sourceEnds E).1

theorem otherEnd_incident (E : data.SourceEdge) (B : data.SourceVertex) :
    Incident data E (otherEnd data E B) := by
  unfold otherEnd
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem otherEnd_ne {E : data.SourceEdge} {B : data.SourceVertex} (hB : Incident data E B) :
    otherEnd data E B ≠ B := by
  unfold otherEnd
  split_ifs with h
  · intro h'
    exact data.sourceEnds_ne _ (h.trans h'.symm)
  · rcases hB with hB | hB
    · exact absurd hB h
    · intro h'; exact data.sourceEnds_ne _ (h'.trans hB.symm)

theorem eq_or_eq_otherEnd {E : data.SourceEdge} {B X : data.SourceVertex} (hB : Incident data E B)
    (hX : Incident data E X) : X = B ∨ X = otherEnd data E B := by
  unfold otherEnd
  split_ifs with h
  · rcases hX with hX | hX
    · exact Or.inl (hX.symm.trans h)
    · exact Or.inr hX.symm
  · rcases hX with hX | hX
    · exact Or.inr hX.symm
    · rcases hB with hB | hB
      · exact absurd hB h
      · exact Or.inl (hX.symm.trans hB)

end OtherEnd

/-! ## 3.  The tail at a member -/

namespace TailAt

open CatSlot

variable {N P degree : ℕ} {H : Core N P} {w : Fin N} {c : ℕ} {y : Fin P → ℚ}
  (C : CaterpillarAt H w c) (M : FibreMember H y degree)

/-- The branch vertex of a core vertex. -/
def vSource (v : Fin N) : M.data.SourceVertex := (M.ident.vertex.symm v).1

theorem three_le_vSource (v : Fin N) : 3 ≤ nonDanglingValency M.data (vSource M v) :=
  (M.ident.vertex.symm v).2

theorem nonDanglingValency_vSource (v : Fin N) : nonDanglingValency M.data (vSource M v) = 3 :=
  le_antisymm (M.fullDim.trivalent _) (three_le_vSource M v)

theorem ident_vSource (v : Fin N) : M.ident.vertex ⟨vSource M v, three_le_vSource M v⟩ = v := by
  change M.ident.vertex (M.ident.vertex.symm v) = v
  exact Equiv.apply_symm_apply _ _

theorem vSource_injective : Function.Injective (vSource M) := by
  intro v v' h
  have : M.ident.vertex.symm v = M.ident.vertex.symm v' := Subtype.ext h
  exact M.ident.vertex.symm.injective this

theorem eq_vSource_of_ident {X : StableGraphIncidence.BranchVertex M.data} {v : Fin N}
    (h : M.ident.vertex X = v) : X.1 = vSource M v := by
  unfold vSource; rw [← h, Equiv.symm_apply_apply]

/-- The row of a tail slot. -/
def row (s : CatSlot c) : StablePath M.data := M.ident.row.symm (C.slot s)

theorem row_injective : Function.Injective (row C M) :=
  fun _ _ h ↦ C.slot_injective (M.ident.row.symm.injective h)

theorem ident_row (s : CatSlot c) : M.ident.row (row C M s) = C.slot s := by
  unfold row; exact Equiv.apply_symm_apply _ _

/-- **A lone row**: one survivor, alone over its target edge (rigidity (1), (2)). -/
def Lone (E : NonDanglingEdge M.data) (r : StablePath M.data) : Prop :=
  (∀ F : NonDanglingEdge M.data, F.stablePath = r ↔ F = E) ∧
    ∀ F : M.data.SourceEdge, ¬ IsDangling M.data F → F.1.1 = E.1.1.1 → F = E.1

variable {C M} in
theorem Lone.unique {E E' : NonDanglingEdge M.data} {r : StablePath M.data} (h : Lone M E r)
    (h' : Lone M E' r) : E' = E := (h.1 E').mp ((h'.1 E').mpr rfl)

variable {C M} in
theorem Lone.stablePath {E : NonDanglingEdge M.data} {r : StablePath M.data} (h : Lone M E r) :
    E.stablePath = r := (h.1 E).mpr rfl

/-! ### The lollipop at each bulb -/

/-- The bridge occurrence of the lollipop at bulb `i`. -/
def bridgeAt (i : Fin (c + 1)) : NonDanglingEdge M.data :=
  ⟨MarkedCount.LoopAt.bridgeE M (C.isLoop i), MarkedCount.LoopAt.bridgeE_survives M (C.isLoop i)⟩

theorem ident_row_bridgePath (hH : H.Cubic) (i : Fin (c + 1)) :
    M.ident.row (MarkedCount.LoopAt.bridgePath M (C.isLoop i)) = C.slot (bulbBridge i) := by
  have h := MarkedCount.LoopAt.coreIncidence_bridgePath_loopVertex M (C.isLoop i)
  rw [C.tail_loop] at h
  rcases C.coreIncidence_bulb_pos hH i h with h' | h'
  · exact absurd h' (MarkedCount.LoopAt.ident_row_bridgePath_ne M (C.isLoop i))
  · exact h'

theorem bridgeAt_stablePath (hH : H.Cubic) (i : Fin (c + 1)) :
    (bridgeAt C M i).stablePath = row C M (bulbBridge i) := by
  unfold row
  rw [← ident_row_bridgePath C M hH i, Equiv.symm_apply_apply]
  rfl

theorem lone_bridgeAt (hH : H.Cubic) (i : Fin (c + 1)) :
    Lone M (bridgeAt C M i) (row C M (bulbBridge i)) := by
  refine ⟨fun F ↦ ⟨fun hF ↦ ?_, fun hF ↦ hF ▸ bridgeAt_stablePath C M hH i⟩, fun F hF hT ↦
    MarkedCount.LoopAt.eq_bridgeE M (C.isLoop i) hF hT⟩
  rw [← bridgeAt_stablePath C M hH i] at hF
  exact MarkedCount.LoopAt.eq_bridgeE_of_stablePath_eq M (C.isLoop i) F hF

theorem loopV_eq (i : Fin (c + 1)) :
    MarkedCount.LoopAt.loopV M (C.isLoop i) = vSource M (C.vertex (Sum.inr i)) := by
  unfold MarkedCount.LoopAt.loopV LollipopDivalent.loopBranch vSource
  rw [C.tail_loop]

theorem farEnd_eq (hH : H.Cubic) (i : Fin (c + 1)) :
    MarkedCount.LoopAt.farEnd M (C.isLoop i) = vSource M (H.tail (C.slot (bulbBridge i))) := by
  refine eq_vSource_of_ident M (X := ⟨_, MarkedCount.LoopAt.three_le_farEnd M (C.isLoop i)⟩) ?_
  have h := MarkedCount.LoopAt.coreIncidence_bridgePath_farEnd M (C.isLoop i)
  rw [ident_row_bridgePath C M hH i] at h
  rcases CaterpillarAt.eq_end_of_coreIncidence_pos h with h' | h'
  · exact h'
  · exfalso
    apply MarkedCount.LoopAt.ident_farEnd_ne_loopVertex M (C.isLoop i)
    rw [h', C.head_bulbBridge, C.tail_loop]

theorem bridgeAt_incident_head (i : Fin (c + 1)) :
    Incident M.data (bridgeAt C M i).1 (vSource M (C.vertex (Sum.inr i))) := by
  rw [← loopV_eq]; exact MarkedCount.LoopAt.bridgeE_incident_loopV M (C.isLoop i)

theorem bridgeAt_incident_tail (hH : H.Cubic) (i : Fin (c + 1)) :
    Incident M.data (bridgeAt C M i).1 (vSource M (H.tail (C.slot (bulbBridge i)))) := by
  rw [← farEnd_eq C M hH]; exact MarkedCount.LoopAt.farEnd_incident M (C.isLoop i)

theorem bridgeAt_index (i : Fin (c + 1)) : M.data.sourceEdgeIndex (bridgeAt C M i).1 = 2 :=
  MarkedCount.LoopAt.bridgeE_index M (C.isLoop i)

/-! ### The downward induction -/

/-- The statement of the induction at the path edge `h_{i+1}`. -/
def LonePath (i : Fin (c + 1)) : Prop :=
  ∃ E : NonDanglingEdge M.data, Lone M E (row C M (Sum.inl i)) ∧
    Incident M.data E.1 (vSource M (H.tail (C.slot (Sum.inl i)))) ∧
    Incident M.data E.1 (vSource M (H.head (C.slot (Sum.inl i))))

/-- The spine vertex `B_{i+1}`. -/
abbrev spineV (i : Fin c) : M.data.SourceVertex := vSource M (C.vertex (Sum.inl i))

/-- **The hypotheses of the step at a spine vertex**: its lollipop bridge and the upper path
edge are lone. -/
theorem spineHyp_of (hH : H.Cubic) (i : Fin c) {Eup : NonDanglingEdge M.data}
    (hUp : Lone M Eup (row C M (Sum.inl i.succ)))
    (hUpInc : Incident M.data Eup.1 (spineV C M i)) :
    SpineStep.Hyp M.data (spineV C M i) (bridgeAt C M i.castSucc).1 Eup.1 where
  valency := nonDanglingValency_vSource M _
  surv₁ := (bridgeAt C M i.castSucc).2
  surv₂ := Eup.2
  ne h := by
    have h1 := bridgeAt_stablePath C M hH i.castSucc
    have h2 := hUp.stablePath
    have hE : bridgeAt C M i.castSucc = Eup := Subtype.ext h
    rw [hE, h2, bulbBridge_castSucc] at h1
    exact absurd (row_injective C M h1) (by simp)
  inc₁ := by
    have := bridgeAt_incident_tail C M hH i.castSucc
    rwa [bulbBridge_castSucc, C.tail_bridge] at this
  inc₂ := hUpInc
  unique₁ F hF hT := MarkedCount.LoopAt.eq_bridgeE M (C.isLoop i.castSucc) hF hT
  unique₂ F hF hT := hUp.2 F hF hT

/-- **The step**: the third survivor at `B_{i+1}` is the lone survivor of the lower path edge,
and its far end is the branch vertex of the lower end of that slot. -/
theorem step (hH : H.Cubic) (i : Fin c) {Eup : NonDanglingEdge M.data}
    (hUp : Lone M Eup (row C M (Sum.inl i.succ)))
    (hUpInc : Incident M.data Eup.1 (spineV C M i)) :
    Lone M ⟨SpineStep.third (spineHyp_of C M hH i hUp hUpInc),
        SpineStep.third_survives (spineHyp_of C M hH i hUp hUpInc)⟩
        (row C M (Sum.inl i.castSucc)) ∧
      Incident M.data (SpineStep.third (spineHyp_of C M hH i hUp hUpInc))
        (vSource M (H.tail (C.slot (Sum.inl i.castSucc)))) := by
  set h := spineHyp_of C M hH i hUp hUpInc
  set E₃ : NonDanglingEdge M.data := ⟨SpineStep.third h, SpineStep.third_survives h⟩
  have hI : Incident M.data E₃.1 (spineV C M i) := SpineStep.third_incident h
  -- the row of `E₃`
  have hRow : E₃.stablePath = row C M (Sum.inl i.castSucc) := by
    have hc := MarkedCount.LoopAt.coreIncidence_pos_of_incident M
      ⟨spineV C M i, three_le_vSource M _⟩ E₃.2 hI
    rw [ident_vSource] at hc
    rcases C.coreIncidence_spine_pos hH i hc with h' | h' | h'
    · unfold row; rw [← h', Equiv.symm_apply_apply]
    · exfalso
      have hR : E₃.stablePath = row C M (Sum.inl i.succ) := by
        unfold row; rw [← h', Equiv.symm_apply_apply]
      have := (hUp.1 E₃).mp hR
      exact SpineStep.third_ne₂ h (congrArg Subtype.val this)
    · exfalso
      have hR : E₃.stablePath = row C M (bulbBridge i.castSucc) := by
        rw [bulbBridge_castSucc]; unfold row; rw [← h', Equiv.symm_apply_apply]
      have := ((lone_bridgeAt C M hH i.castSucc).1 E₃).mp hR
      exact SpineStep.third_ne₁ h (congrArg Subtype.val this)
  -- the far end of `E₃`
  set Y := otherEnd M.data E₃.1 (spineV C M i)
  have hY : Incident M.data E₃.1 Y := otherEnd_incident _ _
  have hY3 : nonDanglingValency M.data Y = 3 := SpineStep.third_farEnd_valency M.fullDim h hY
  have hYeq : Y = vSource M (H.tail (C.slot (Sum.inl i.castSucc))) := by
    apply eq_vSource_of_ident (X := ⟨Y, hY3.ge⟩)
    have hc := MarkedCount.LoopAt.coreIncidence_pos_of_incident M ⟨Y, hY3.ge⟩ E₃.2 hY
    rw [hRow, ident_row] at hc
    rcases CaterpillarAt.eq_end_of_coreIncidence_pos hc with h' | h'
    · exact h'
    · exfalso
      rw [C.head_path_castSucc] at h'
      have := eq_vSource_of_ident M h'
      exact otherEnd_ne hI this
  refine ⟨⟨fun F ↦ ⟨fun hF ↦ ?_, fun hF ↦ hF ▸ hRow⟩, fun F hF hT ↦
    SpineStep.spineStep_unique_edge M.fullDim h hF hT⟩, hYeq ▸ hY⟩
  rw [← hRow] at hF
  refine MarkedCount.LoopAt.eq_of_stablePath_eq_of_ends (fun X hX ↦ ?_) hF
  rcases eq_or_eq_otherEnd hI hX with rfl | rfl
  · rw [nonDanglingValency_vSource]; omega
  · rw [hY3]; omega

/-- **Rigidity (2), by downward induction**: every path row is lone. -/
theorem lonePath (hH : H.Cubic) (i : Fin (c + 1)) : LonePath C M i := by
  suffices H' : ∀ m (i : Fin (c + 1)), i.val + m = c → LonePath C M i from
    H' (c - i.val) i (by have := i.isLt; omega)
  intro m
  induction m with
  | zero =>
    intro i hi
    obtain rfl : i = Fin.last c := Fin.ext (by simpa using hi)
    refine ⟨bridgeAt C M (Fin.last c), ?_, ?_, ?_⟩
    · have := lone_bridgeAt C M hH (Fin.last c)
      rwa [bulbBridge_last] at this
    · have := bridgeAt_incident_tail C M hH (Fin.last c)
      rwa [bulbBridge_last] at this
    · rw [C.head_path_last]; exact bridgeAt_incident_head C M (Fin.last c)
  | succ m ih =>
    intro i hi
    have hlt : i.val < c := by omega
    obtain ⟨i', rfl⟩ : ∃ i' : Fin c, i'.castSucc = i := ⟨⟨i.val, hlt⟩, rfl⟩
    obtain ⟨Eup, hUp, hUpT, -⟩ := ih i'.succ (by simp at hi ⊢; omega)
    rw [C.tail_path_succ] at hUpT
    obtain ⟨hLone, hTail⟩ := step C M hH i' hUp hUpT
    refine ⟨_, hLone, hTail, ?_⟩
    rw [C.head_path_castSucc]
    exact SpineStep.third_incident (spineHyp_of C M hH i' hUp hUpT)

/-- The lone survivor of the path edge `h_{i+1}`. -/
def pathE (hH : H.Cubic) (i : Fin (c + 1)) : NonDanglingEdge M.data :=
  (lonePath C M hH i).choose

theorem lone_pathE (hH : H.Cubic) (i : Fin (c + 1)) : Lone M (pathE C M hH i) (row C M (Sum.inl i)) :=
  (lonePath C M hH i).choose_spec.1

theorem pathE_incident_tail (hH : H.Cubic) (i : Fin (c + 1)) :
    Incident M.data (pathE C M hH i).1 (vSource M (H.tail (C.slot (Sum.inl i)))) :=
  (lonePath C M hH i).choose_spec.2.1

theorem pathE_incident_head (hH : H.Cubic) (i : Fin (c + 1)) :
    Incident M.data (pathE C M hH i).1 (vSource M (H.head (C.slot (Sum.inl i)))) :=
  (lonePath C M hH i).choose_spec.2.2

theorem pathE_last (hH : H.Cubic) : pathE C M hH (Fin.last c) = bridgeAt C M (Fin.last c) := by
  have h := lone_bridgeAt C M hH (Fin.last c)
  rw [bulbBridge_last] at h
  exact ((lone_pathE C M hH (Fin.last c)).unique h).symm

/-- **The spine hypotheses** at `B_{i+1}`. -/
theorem spineHyp (hH : H.Cubic) (i : Fin c) :
    SpineStep.Hyp M.data (spineV C M i) (bridgeAt C M i.castSucc).1 (pathE C M hH i.succ).1 := by
  have h := pathE_incident_tail C M hH i.succ
  rw [C.tail_path_succ] at h
  exact spineHyp_of C M hH i (lone_pathE C M hH i.succ) h

theorem third_spineHyp (hH : H.Cubic) (i : Fin c) :
    SpineStep.third (spineHyp C M hH i) = (pathE C M hH i.castSucc).1 := by
  have h := pathE_incident_tail C M hH i.succ
  rw [C.tail_path_succ] at h
  have hs := (step C M hH i (lone_pathE C M hH i.succ) h).1
  exact congrArg Subtype.val ((lone_pathE C M hH i.castSucc).unique hs)

theorem pathE_incident_spine_lower (hH : H.Cubic) (i : Fin c) :
    Incident M.data (pathE C M hH i.castSucc).1 (spineV C M i) := by
  have h := pathE_incident_head C M hH i.castSucc
  rwa [C.head_path_castSucc] at h

theorem pathE_incident_spine_upper (hH : H.Cubic) (i : Fin c) :
    Incident M.data (pathE C M hH i.succ).1 (spineV C M i) := by
  have h := pathE_incident_tail C M hH i.succ
  rwa [C.tail_path_succ] at h

end TailAt

end

end DraismaVargas.Count.MarkedCountGeneral
