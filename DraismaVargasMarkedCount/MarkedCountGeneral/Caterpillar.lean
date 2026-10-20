module

public import DraismaVargasMarkedCount.MarkedCount.Core

@[expose] public section

/-!
# The caterpillar tail and the tailed core

**The caterpillar tail** `CT_a` of genus `a = c + 1` at a vertex `w` (Part II's caterpillar of
loops): a path `w = B_0 —h_1— B_1 — ⋯ — B_c —h_{c+1}— A_{c+1}` with a lollipop (bridge `b_i`,
loop at `A_i`) at every `B_i`, `1 ≤ i ≤ c`, and a loop at `A_{c+1}`. It has `3c + 2 = 3a - 1`
edges and `2c + 1` new vertices. For `c = 0` it is the lollipop of the marked count at
ramification one (the path edge `h_1` is the bridge).

In Lean, 0-indexed (`CatSlot c`, `CatVertex c`):

* `path i`, `i : Fin (c + 1)`: the path edge `h_{i+1}`, from `B_i` (`w` for `i = 0`) to `B_{i+1}`
  (`A_{c+1}` for `i = c`);
* `bridge i`, `i : Fin c`: the bridge `b_{i+1}`, from `B_{i+1}` to `A_{i+1}`;
* `loop i`, `i : Fin (c + 1)`: the loop at `A_{i+1}`;
* `spine i`, `i : Fin c`: the vertex `B_{i+1}`; `bulb i`, `i : Fin (c + 1)`: the vertex `A_{i+1}`.

`CaterpillarAt H w c` says that the core `H` contains such a tail at `w` (named slots and
vertices with these incidences). `Tailed core mark c` is the graph `H` of the decomposition theorem
(module `Correspondence`) for any number of marks: `core` with a caterpillar of genus `c j + 1` at
every mark `j`, all at once, described by a decomposition of its vertices and slots.
`Tailed.canonical` constructs one; any two are isomorphic, and the theorems below hold for every
`Tailed`.

## Proved here

`catTail_map`, `catHead_map`, `Tailed.canonical`, `Tailed.caterpillarAt`, `Tailed.cubic`, `Tailed.connected`, the counts
`Tailed.card_vertices`, `Tailed.card_slots`, the genus `Tailed.genus_eq`, the request
`Tailed.request` and its positivity. `Tailed.cubic` rests on `catDegree_some` and
`catDegree_none`, `Tailed.connected` on `mem_of_closed`.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Count.MarkedCount
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  Slots and vertices of a caterpillar tail -/

/-- The slots of a caterpillar tail of genus `c + 1`: path edges, bridges, loops. -/
abbrev CatSlot (c : ℕ) : Type := Fin (c + 1) ⊕ (Fin c ⊕ Fin (c + 1))

/-- The new vertices of a caterpillar tail of genus `c + 1`: spine vertices `B_i`, bulbs `A_i`. -/
abbrev CatVertex (c : ℕ) : Type := Fin c ⊕ Fin (c + 1)

namespace CatSlot

variable {c : ℕ}

/-- The path edge `h_{i+1}`. -/
def path (i : Fin (c + 1)) : CatSlot c := Sum.inl i
/-- The bridge `b_{i+1}`. -/
def bridge (i : Fin c) : CatSlot c := Sum.inr (Sum.inl i)
/-- The loop at `A_{i+1}`. -/
def loop (i : Fin (c + 1)) : CatSlot c := Sum.inr (Sum.inr i)

end CatSlot

namespace CatVertex

variable {c : ℕ}

/-- The spine vertex `B_{i+1}`. -/
def spine (i : Fin c) : CatVertex c := Sum.inl i
/-- The bulb `A_{i+1}` (the vertex carrying a loop). -/
def bulb (i : Fin (c + 1)) : CatVertex c := Sum.inr i

end CatVertex

section Ends

variable {V : Type*} {c : ℕ}

/-- **The tail end of a caterpillar slot**, given the attaching vertex `w` and the names `vtx` of
the new vertices: `h_{i+1}` starts at `B_i` (`w` if `i = 0`), a bridge at its spine vertex, a loop
at its bulb. -/
def catTail (w : V) (vtx : CatVertex c → V) : CatSlot c → V
  | Sum.inl i => Fin.cases (motive := fun _ ↦ V) w (fun i' ↦ vtx (Sum.inl i')) i
  | Sum.inr (Sum.inl i) => vtx (Sum.inl i)
  | Sum.inr (Sum.inr i) => vtx (Sum.inr i)

/-- **The head end of a caterpillar slot**: `h_{i+1}` ends at `B_{i+1}` (`A_{c+1}` if `i = c`), a
bridge at the bulb `A_{i+1}`, a loop at its bulb. -/
def catHead (_w : V) (vtx : CatVertex c → V) : CatSlot c → V
  | Sum.inl i => Fin.lastCases (motive := fun _ ↦ V) (vtx (Sum.inr (Fin.last c)))
      (fun i' ↦ vtx (Sum.inl i')) i
  | Sum.inr (Sum.inl i) => vtx (Sum.inr i.castSucc)
  | Sum.inr (Sum.inr i) => vtx (Sum.inr i)

theorem catTail_map {W : Type*} (g : V → W) (w : V) (vtx : CatVertex c → V) (s : CatSlot c) :
    g (catTail w vtx s) = catTail (g w) (g ∘ vtx) s := by
  rcases s with i | i | i
  · refine Fin.cases ?_ (fun i' ↦ ?_) i <;> simp [catTail]
  · rfl
  · rfl

theorem catHead_map {W : Type*} (g : V → W) (w : V) (vtx : CatVertex c → V) (s : CatSlot c) :
    g (catHead w vtx s) = catHead (g w) (g ∘ vtx) s := by
  rcases s with i | i | i
  · refine Fin.lastCases ?_ (fun i' ↦ ?_) i <;> simp [catHead]
  · rfl
  · rfl

end Ends

/-! ## 2.  A caterpillar inside a core -/

/-- **A caterpillar tail of genus `c + 1` at the vertex `w` of the core `H`**:
injective names for its `3c + 2` slots and `2c + 1` new vertices, with the incidences of the
caterpillar. In a cubic `H` the new vertices then have no other incidences. -/
structure CaterpillarAt {N P : ℕ} (H : Core N P) (w : Fin N) (c : ℕ) where
  /-- The slots of the tail. -/
  slot : CatSlot c → Fin P
  /-- The new vertices of the tail. -/
  vertex : CatVertex c → Fin N
  slot_injective : Function.Injective slot
  vertex_injective : Function.Injective vertex
  vertex_ne : ∀ x, vertex x ≠ w
  tail_eq : ∀ s, H.tail (slot s) = catTail w vertex s
  head_eq : ∀ s, H.head (slot s) = catHead w vertex s

/-! ## 3.  The tailed core -/

variable {n p k : ℕ}

/-- **The tailed core** `H` of the decomposition theorem: `core` with a caterpillar tail of genus
`c j + 1` attached at every mark `j` (all marks of positive type, all tails at once). Its vertices
are the old ones and the tail vertices, its slots the old ones and the tail slots, through the two
decompositions `vertexEquiv` and `slotEquiv`; the old slots keep their ends, and the tail slots
have the caterpillar's. -/
structure Tailed (core : Core n p) (mark : Fin k → Fin n) (c : Fin k → ℕ) where
  /-- The number of vertices of `H`. -/
  N : ℕ
  /-- The number of slots of `H`. -/
  P : ℕ
  /-- The core `H`. -/
  H : Core N P
  /-- Vertices: old ones, then the tail vertices of each mark. -/
  vertexEquiv : Fin n ⊕ (Σ j, CatVertex (c j)) ≃ Fin N
  /-- Slots: old ones, then the tail slots of each mark. -/
  slotEquiv : Fin p ⊕ (Σ j, CatSlot (c j)) ≃ Fin P
  tail_core : ∀ i, H.tail (slotEquiv (Sum.inl i)) = vertexEquiv (Sum.inl (core.tail i))
  head_core : ∀ i, H.head (slotEquiv (Sum.inl i)) = vertexEquiv (Sum.inl (core.head i))
  tail_tail : ∀ j s, H.tail (slotEquiv (Sum.inr ⟨j, s⟩)) =
    catTail (vertexEquiv (Sum.inl (mark j))) (fun x ↦ vertexEquiv (Sum.inr ⟨j, x⟩)) s
  head_tail : ∀ j s, H.head (slotEquiv (Sum.inr ⟨j, s⟩)) =
    catHead (vertexEquiv (Sum.inl (mark j))) (fun x ↦ vertexEquiv (Sum.inr ⟨j, x⟩)) s

namespace Tailed

variable {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}

/-- An old vertex of `H`. -/
def oldVertex (T : Tailed core mark c) (v : Fin n) : Fin T.N := T.vertexEquiv (Sum.inl v)

/-- A core slot of `H`. -/
def coreSlot (T : Tailed core mark c) (i : Fin p) : Fin T.P := T.slotEquiv (Sum.inl i)

/-- A tail slot of `H`. -/
def tailSlot (T : Tailed core mark c) (j : Fin k) (s : CatSlot (c j)) : Fin T.P :=
  T.slotEquiv (Sum.inr ⟨j, s⟩)

theorem coreSlot_injective (T : Tailed core mark c) : Function.Injective T.coreSlot :=
  fun _ _ h ↦ Sum.inl_injective (T.slotEquiv.injective h)

/-- **The tail at mark `j`** is a caterpillar at the old vertex `mark j`. -/
def caterpillarAt (T : Tailed core mark c) (j : Fin k) :
    CaterpillarAt T.H (T.oldVertex (mark j)) (c j) where
  slot s := T.tailSlot j s
  vertex x := T.vertexEquiv (Sum.inr ⟨j, x⟩)
  slot_injective _ _ h := by simpa [tailSlot] using T.slotEquiv.injective h
  vertex_injective _ _ h := by simpa using T.vertexEquiv.injective h
  vertex_ne x h := by
    have := T.vertexEquiv.injective h
    simp at this
  tail_eq s := T.tail_tail j s
  head_eq s := T.head_tail j s

/-- Every slot is a core slot or a tail slot. -/
theorem slot_cases (T : Tailed core mark c) (e : Fin T.P) :
    (∃ i, T.coreSlot i = e) ∨ ∃ j s, T.tailSlot j s = e := by
  rcases h : T.slotEquiv.symm e with i | ⟨j, s⟩
  · exact Or.inl ⟨i, by rw [coreSlot, ← h, Equiv.apply_symm_apply]⟩
  · exact Or.inr ⟨j, s, by rw [tailSlot, ← h, Equiv.apply_symm_apply]⟩

theorem coreSlot_ne_tailSlot (T : Tailed core mark c) (i : Fin p) (j : Fin k)
    (s : CatSlot (c j)) : T.coreSlot i ≠ T.tailSlot j s := by
  intro h
  have := T.slotEquiv.injective h
  simp at this

/-! ### The counts and the genus -/

theorem card_vertices (T : Tailed core mark c) : T.N = n + ∑ j, (2 * c j + 1) := by
  have h := Fintype.card_congr T.vertexEquiv
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma] at h
  rw [← h]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by ring

theorem card_slots (T : Tailed core mark c) : T.P = p + ∑ j, (3 * c j + 2) := by
  have h := Fintype.card_congr T.slotEquiv
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma] at h
  rw [← h]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **The genus of `H`** is that of the marked core plus the total type `Σⱼ (c j + 1)`
(`g_H = g + a (+ b)`). -/
theorem genus_eq (T : Tailed core mark c) (h : n ≤ p + 1) :
    T.P + 1 - T.N = (p + 1 - n) + ∑ j, (c j + 1) := by
  rw [T.card_vertices, T.card_slots]
  have h3 : ∑ j, (3 * c j + 2) = ∑ j, (2 * c j + 1) + ∑ j, (c j + 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [h3]
  omega

/-! ### The canonical tailed core -/

/-- The vertex type of the canonical tailed core. -/
abbrev CanonicalVertex (n : ℕ) (c : Fin k → ℕ) : Type := Fin n ⊕ (Σ j, CatVertex (c j))

/-- The slot type of the canonical tailed core. -/
abbrev CanonicalSlot (p : ℕ) (c : Fin k → ℕ) : Type := Fin p ⊕ (Σ j, CatSlot (c j))

/-- Ends of the slots of the canonical tailed core, on the vertex type. -/
def canonicalTail (core : Core n p) (mark : Fin k → Fin n) (c : Fin k → ℕ) :
    CanonicalSlot p c → CanonicalVertex n c
  | Sum.inl i => Sum.inl (core.tail i)
  | Sum.inr ⟨j, s⟩ => catTail (Sum.inl (mark j)) (fun x ↦ Sum.inr ⟨j, x⟩) s

/-- Ends of the slots of the canonical tailed core, on the vertex type. -/
def canonicalHead (core : Core n p) (mark : Fin k → Fin n) (c : Fin k → ℕ) :
    CanonicalSlot p c → CanonicalVertex n c
  | Sum.inl i => Sum.inl (core.head i)
  | Sum.inr ⟨j, s⟩ => catHead (Sum.inl (mark j)) (fun x ↦ Sum.inr ⟨j, x⟩) s

/-- **The canonical tailed core**: vertices and slots are the decompositions themselves,
numbered by `Fintype.equivFin`. -/
noncomputable def canonical (core : Core n p) (mark : Fin k → Fin n) (c : Fin k → ℕ) :
    Tailed core mark c where
  N := Fintype.card (CanonicalVertex n c)
  P := Fintype.card (CanonicalSlot p c)
  H :=
    { tail := fun e ↦ (Fintype.equivFin _) (canonicalTail core mark c
        ((Fintype.equivFin _).symm e))
      head := fun e ↦ (Fintype.equivFin _) (canonicalHead core mark c
        ((Fintype.equivFin _).symm e)) }
  vertexEquiv := Fintype.equivFin _
  slotEquiv := Fintype.equivFin _
  tail_core i := by simp [canonicalTail]
  head_core i := by simp [canonicalHead]
  tail_tail j s := by
    simp only [Equiv.symm_apply_apply, canonicalTail]
    exact catTail_map _ _ _ s
  head_tail j s := by
    simp only [Equiv.symm_apply_apply, canonicalHead]
    exact catHead_map _ _ _ s

instance : Nonempty (Tailed core mark c) := ⟨canonical core mark c⟩

/-! ### Cubic (proved) -/

section Degree

variable {c' : ℕ}

/-- At a new vertex of a caterpillar, three slot ends (the tail is trivalent). -/
theorem catDegree_some (x : CatVertex c') :
    ∑ s : CatSlot c', ((if catTail (none : Option (CatVertex c')) some s = some x then 1 else 0) +
      (if catHead (none : Option (CatVertex c')) some s = some x then 1 else 0)) = 3 := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Finset.sum_add_distrib]
  rw [Fin.sum_univ_succ (fun k ↦ if catTail (none : Option (CatVertex c')) some (Sum.inl k) =
    some x then 1 else 0), Fin.sum_univ_castSucc (fun k ↦ if catHead (none : Option (CatVertex c'))
      some (Sum.inl k) = some x then 1 else 0)]
  rcases x with i | i
  · simp [catTail, catHead]
  · refine Fin.lastCases ?_ (fun i' ↦ ?_) i
    · simp [catTail, catHead, Fin.castSucc_ne_last]
    · simp only [catTail, catHead]
      simp
      exact fun h ↦ Fin.castSucc_ne_last i' h.symm

/-- At the attaching vertex, one slot end (the tail of `path 0`). -/
theorem catDegree_none :
    ∑ s : CatSlot c', ((if catTail (none : Option (CatVertex c')) some s = none then 1 else 0) +
      (if catHead (none : Option (CatVertex c')) some s = none then 1 else 0)) = 1 := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Finset.sum_add_distrib]
  rw [Fin.sum_univ_succ (fun k ↦ if catTail (none : Option (CatVertex c')) some (Sum.inl k) = none
    then 1 else 0), Fin.sum_univ_castSucc (fun k ↦ if catHead (none : Option (CatVertex c')) some
      (Sum.inl k) = none then 1 else 0)]
  simp [catTail, catHead]

end Degree

/-- The ends of a slot of `H`, read in the decomposition. -/
theorem tail_slotEquiv (T : Tailed core mark c) (x : CanonicalSlot p c) :
    T.H.tail (T.slotEquiv x) = T.vertexEquiv (canonicalTail core mark c x) := by
  rcases x with i | ⟨j, s⟩
  · exact T.tail_core i
  · rw [T.tail_tail]
    exact (catTail_map T.vertexEquiv _ _ s).symm

theorem head_slotEquiv (T : Tailed core mark c) (x : CanonicalSlot p c) :
    T.H.head (T.slotEquiv x) = T.vertexEquiv (canonicalHead core mark c x) := by
  rcases x with i | ⟨j, s⟩
  · exact T.head_core i
  · rw [T.head_tail]
    exact (catHead_map T.vertexEquiv _ _ s).symm

/-- The new vertices of the tail at `j`, and its attaching vertex, in the decomposition. -/
def tailName (mark : Fin k → Fin n) (c : Fin k → ℕ) (j : Fin k) :
    Option (CatVertex (c j)) → CanonicalVertex n c :=
  fun o ↦ o.elim (Sum.inl (mark j)) fun x ↦ Sum.inr ⟨j, x⟩

theorem canonicalTail_inr (j : Fin k) (s : CatSlot (c j)) :
    canonicalTail core mark c (Sum.inr ⟨j, s⟩) = tailName mark c j (catTail none some s) :=
  (catTail_map (tailName mark c j) none some s).symm

theorem canonicalHead_inr (j : Fin k) (s : CatSlot (c j)) :
    canonicalHead core mark c (Sum.inr ⟨j, s⟩) = tailName mark c j (catHead none some s) :=
  (catHead_map (tailName mark c j) none some s).symm

/-- **The incidence degree of `H`, in the decomposition.** -/
theorem incidenceDegree_vertexEquiv (T : Tailed core mark c) (w : CanonicalVertex n c) :
    T.H.incidenceDegree (T.vertexEquiv w) =
      ∑ x : CanonicalSlot p c, ((if canonicalTail core mark c x = w then 1 else 0) +
        (if canonicalHead core mark c x = w then 1 else 0)) := by
  unfold Core.incidenceDegree
  refine Fintype.sum_equiv T.slotEquiv.symm _ _ fun e ↦ ?_
  obtain ⟨x, rfl⟩ := T.slotEquiv.surjective e
  rw [Equiv.symm_apply_apply, T.tail_slotEquiv, T.head_slotEquiv]
  exact congrArg₂ (· + ·) (if_congr (Equiv.apply_eq_iff_eq _) rfl rfl)
    (if_congr (Equiv.apply_eq_iff_eq _) rfl rfl)

/-- **`H` is cubic** when the marked core is marked-cubic (the tail is trivalent): at an
old vertex the old slots give `core.incidenceDegree v` and the tails `#{j | mark j = v}`
(`catDegree_none`); at a tail vertex its own tail gives `3` (`catDegree_some`). -/
theorem cubic (T : Tailed core mark c) (hc : IsMarkedCubic core mark) : T.H.Cubic := by
  classical
  intro v
  obtain ⟨w, rfl⟩ := T.vertexEquiv.surjective v
  rw [T.incidenceDegree_vertexEquiv, Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [canonicalTail_inr, canonicalHead_inr]
  rcases w with v | ⟨j₀, x⟩
  · -- an old vertex
    have hTail : ∀ j (o : Option (CatVertex (c j))),
        (if tailName mark c j o = Sum.inl v then 1 else 0) =
          (if mark j = v then 1 else 0) * (if o = none then 1 else 0) := by
      intro j o
      rcases o with _ | x <;> simp [tailName]
    simp only [hTail, ← mul_add, ← Finset.mul_sum, catDegree_none, mul_one]
    have key : core.incidenceDegree v + ∑ j : Fin k, (if mark j = v then 1 else 0) = 3 := by
      by_cases hv : v ∈ Set.range mark
      · obtain ⟨j, rfl⟩ := hv
        have hone : (∑ i : Fin k, if mark i = mark j then 1 else 0) = 1 := by
          simp_rw [hc.injective.eq_iff]
          simp
        rw [hc.mark_degree j, hone]
      · have hzero : (∑ i : Fin k, if mark i = v then 1 else 0) = 0 :=
          Finset.sum_eq_zero fun i _ ↦ by
            simp only [ite_eq_right_iff]
            exact fun hi ↦ (hv ⟨i, hi⟩).elim
        rw [hc.other_degree v hv, hzero]
    convert key using 2
    unfold Core.incidenceDegree
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [canonicalTail, canonicalHead]
  · -- a tail vertex
    have hOther : ∀ j, j ≠ j₀ → ∀ o : Option (CatVertex (c j)),
        (if tailName mark c j o = Sum.inr ⟨j₀, x⟩ then 1 else 0) = 0 := by
      intro j hj o
      rcases o with _ | x' <;> simp [tailName, hj]
    have hSame : ∀ o : Option (CatVertex (c j₀)),
        (if tailName mark c j₀ o = Sum.inr ⟨j₀, x⟩ then 1 else 0) =
          if o = some x then 1 else 0 := by
      intro o
      rcases o with _ | x' <;> simp [tailName]
    rw [Finset.sum_eq_single j₀ (fun j _ hj ↦ Finset.sum_eq_zero fun s _ ↦ by
      rw [hOther j hj, hOther j hj, add_zero]) (by simp)]
    simp only [hSame, catDegree_some]
    simp [canonicalTail, canonicalHead]

/-- **A set of vertices closed under the slots contains a whole tail once it contains its
attaching vertex**: walk up the spine along the path edges, then out along the bridges and the
last path edge. -/
theorem mem_of_closed (T : Tailed core mark c) {S : Finset (Fin T.N)}
    (hClosed : ∀ e, T.H.tail e ∈ S ↔ T.H.head e ∈ S) (j : Fin k)
    (hj : T.oldVertex (mark j) ∈ S) (x : CatVertex (c j)) :
    T.vertexEquiv (Sum.inr ⟨j, x⟩) ∈ S := by
  set V : CatVertex (c j) → Fin T.N := fun x ↦ T.vertexEquiv (Sum.inr ⟨j, x⟩) with hV
  have hTail : ∀ s, T.H.tail (T.tailSlot j s) = catTail (T.oldVertex (mark j)) V s :=
    T.tail_tail j
  have hHead : ∀ s, T.H.head (T.tailSlot j s) = catHead (T.oldVertex (mark j)) V s :=
    T.head_tail j
  -- the tail end of a path edge is in `S` once the earlier spine vertices are
  have hPathTail : ∀ y : Fin (c j + 1), (∀ i : Fin (c j), i.val < y.val → V (Sum.inl i) ∈ S) →
      catTail (T.oldVertex (mark j)) V (Sum.inl y) ∈ S := by
    intro y hy
    rcases Fin.eq_zero_or_eq_succ y with rfl | ⟨i, rfl⟩
    · simpa [catTail] using hj
    · simp only [catTail, Fin.cases_succ]
      exact hy i (by simp)
  have hSpine : ∀ m (i : Fin (c j)), i.val = m → V (Sum.inl i) ∈ S := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro i hi
    have h := (hClosed (T.tailSlot j (Sum.inl i.castSucc))).mp (by
      rw [hTail]
      exact hPathTail _ fun i' hi' ↦ ih i'.val (by simp at hi'; omega) i' rfl)
    rw [hHead] at h
    simpa [catHead] using h
  rcases x with i | i
  · exact hSpine i.val i rfl
  · refine Fin.lastCases ?_ (fun i' ↦ ?_) i
    · have h := (hClosed (T.tailSlot j (Sum.inl (Fin.last (c j))))).mp (by
        rw [hTail]
        exact hPathTail _ fun i' _ ↦ hSpine i'.val i' rfl)
      rw [hHead] at h
      simpa [catHead] using h
    · have h := (hClosed (T.tailSlot j (Sum.inr (Sum.inl i')))).mp (by
        rw [hTail]
        exact hSpine i'.val i' rfl)
      rw [hHead] at h
      simpa [catHead] using h

/-- **`H` is connected** when the core is: a cut either splits the old vertices (then an old
slot crosses it) or contains all of them or none of them, and then it contains every tail or
none (`mem_of_closed`, for the cut or its complement). -/
theorem connected (T : Tailed core mark c) (hConnected : core.Connected) : T.H.Connected := by
  classical
  intro S hS
  obtain ⟨v, w, hv, hw⟩ := hS
  by_contra hNo
  push Not at hNo
  have hClosed : ∀ e, T.H.tail e ∈ S ↔ T.H.head e ∈ S := fun e ↦ ⟨(hNo e).1, (hNo e).2⟩
  have hAll : ∀ S' : Finset (Fin T.N), (∀ e, T.H.tail e ∈ S' ↔ T.H.head e ∈ S') →
      (∀ u, T.oldVertex u ∈ S') → ∀ z, z ∈ S' := by
    intro S' hC hOld z
    obtain ⟨z, rfl⟩ := T.vertexEquiv.surjective z
    rcases z with u | ⟨j, x⟩
    · exact hOld u
    · exact T.mem_of_closed hC j (hOld _) x
  by_cases hsplit : ∃ u u' : Fin n, T.oldVertex u ∈ S ∧ T.oldVertex u' ∉ S
  · obtain ⟨u, u', hu, hu'⟩ := hsplit
    obtain ⟨i, hi⟩ := hConnected (Finset.univ.filter fun u ↦ T.oldVertex u ∈ S)
      ⟨u, u', by simpa using hu, by simpa using hu'⟩
    have hT := T.tail_core i
    have hH := T.head_core i
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      have h3 := (hClosed (T.slotEquiv (Sum.inl i))).mp (by rw [hT]; exact h1)
      rw [hH] at h3
      exact h2 h3
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      have h3 := (hClosed (T.slotEquiv (Sum.inl i))).mpr (by rw [hH]; exact h1)
      rw [hT] at h3
      exact h2 h3
  · push Not at hsplit
    by_cases hIn : ∀ u, T.oldVertex u ∈ S
    · exact hw (hAll S hClosed hIn w)
    · push Not at hIn
      obtain ⟨u₀, hu₀⟩ := hIn
      have hOut : ∀ u, T.oldVertex u ∈ Sᶜ := fun u ↦ by
        rw [Finset.mem_compl]
        exact fun hu ↦ hu₀ (hsplit u u₀ hu)
      have hC : ∀ e, T.H.tail e ∈ Sᶜ ↔ T.H.head e ∈ Sᶜ := fun e ↦ by
        simp only [Finset.mem_compl, hClosed e]
      exact (Finset.mem_compl.mp (hAll Sᶜ hC hOut v)) hv

/-! ### Requests on the tailed core -/

/-- **The request on `H`**: `y` on the core slots and the length `1` on every tail slot (any
positive tail lengths would do: no tail needs to be long). -/
def request (T : Tailed core mark c) (y : Fin p → ℚ) : Fin T.P → ℚ :=
  fun e ↦ Sum.elim y (fun _ ↦ 1) (T.slotEquiv.symm e)

@[simp] theorem request_coreSlot (T : Tailed core mark c) (y : Fin p → ℚ) (i : Fin p) :
    T.request y (T.coreSlot i) = y i := by
  simp [request, coreSlot]

@[simp] theorem request_tailSlot (T : Tailed core mark c) (y : Fin p → ℚ) (j : Fin k)
    (s : CatSlot (c j)) : T.request y (T.tailSlot j s) = 1 := by
  simp [request, tailSlot]

theorem request_pos (T : Tailed core mark c) {y : Fin p → ℚ} (hy : ∀ i, 0 < y i) (e : Fin T.P) :
    0 < T.request y e := by
  rcases T.slot_cases e with ⟨i, rfl⟩ | ⟨j, s, rfl⟩
  · rw [request_coreSlot]; exact hy i
  · rw [request_tailSlot]; exact one_pos

end Tailed

end DraismaVargas.Count.MarkedCountGeneral
