module

public import GenusSixExistence.BrillNoetherRank.Tripod.Gadget

@[expose] public section

/-!
# Marked cores and the lollipop core

The combinatorial objects of the marked Draisma--Vargas count at ramification one
(`MarkedCount.markedCount_eq_catalan`).

A **marked core** is a `Core n p` together with `k` distinct vertices `mark : Fin k → Fin n`, the
marks, of incidence degree two, every other vertex having incidence degree three (`IsMarkedCubic`).
It is the marked model `H_{u,v}` (the essential model `H_Γ` of the metric graph `Γ`, with the marks
added as divalent vertices) with only the **ramified** marks declared: an unramified mark is never
put into the core, because the lollipop lemma (`Correspondence.lollipopClassEquiv`) is a statement
about `Γ` marked at its ramified marks only. A request `y : Fin p → ℚ` on it records `Γ` together
with the positions of the marks, as the lengths of the pieces of the split edges.

The marked cores of the two headline cases are subdivisions of a cubic core (`subdivide` from
the public tripod gadget): one mark (`onceMark`, the case `(a, b) = (1, 0)`) or two
(`twiceMark`, the case `(1, 1)`; the second mark may sit on either piece of the first split
slot, so both marks may lie on one edge of `Γ`).

`attachLollipops core mark : Core (n + k) (p + (k + k))` is the graph `H` obtained by attaching a
lollipop (a bridge to a new vertex, and a loop there) at every mark: at every mark `j` a new vertex
`lollipopVertex j`, a bridge slot `bridgeSlot j : mark j → w_j` and a loop slot
`loopSlot j : w_j → w_j`. Core loops are allowed, as in `FibreCaterpillar.catCore`.

## What is proved here

* `incidenceDegree_attachLollipops_old`, `incidenceDegree_attachLollipops_new`,
  `attachLollipops_cubic`: the lollipop core is cubic when the marked core is marked-cubic;
* `attachLollipops_connected`;
* `isMarkedCubic_onceMarked`, `isMarkedCubic_twiceMarked`: the one- and two-mark subdivisions of
  a cubic core are marked-cubic;
* the request bookkeeping `lollipopRequest` and its values on the three kinds of slot.
-/

namespace DraismaVargas.Count.MarkedCount

open Utilities.Certificate.ExplicitPotential (Core)
open GenusSixExistence.Tripod.Gadget (subdivide incidenceDegree_subdivide_castSucc
  incidenceDegree_subdivide_last subdivide_connected)
open Finset

variable {n p k : ℕ}

/-! ## 1.  Marked cores -/

/-- **A marked cubic core**: the marks are distinct vertices of incidence degree two, and every
other vertex has incidence degree three (the genericity of the marked graph: `H_Γ` trivalent, the
marks interior to edges). -/
structure IsMarkedCubic (core : Core n p) (mark : Fin k → Fin n) : Prop where
  injective : Function.Injective mark
  mark_degree : ∀ j, core.incidenceDegree (mark j) = 2
  other_degree : ∀ v, v ∉ Set.range mark → core.incidenceDegree v = 3

/-! ## 2.  The lollipop core -/

/-- **The lollipop core** `H`: a lollipop at every mark. Vertices: `Fin.castAdd k` of the
old ones, then `lollipopVertex j = Fin.natAdd n j`. Slots: `Fin.castAdd (k + k)` of the old ones
(the **core slots**), then the bridges `bridgeSlot j` from `mark j` to `w_j`, then the loops
`loopSlot j` at `w_j`. -/
def attachLollipops (core : Core n p) (mark : Fin k → Fin n) : Core (n + k) (p + (k + k)) where
  tail := Fin.addCases (fun i ↦ Fin.castAdd k (core.tail i))
    (Fin.addCases (fun j ↦ Fin.castAdd k (mark j)) fun j ↦ Fin.natAdd n j)
  head := Fin.addCases (fun i ↦ Fin.castAdd k (core.head i))
    (Fin.addCases (fun j ↦ Fin.natAdd n j) fun j ↦ Fin.natAdd n j)

/-- An old vertex of the lollipop core. -/
def oldVertex (k : ℕ) (v : Fin n) : Fin (n + k) := Fin.castAdd k v

/-- The new vertex `w_j` of the lollipop at mark `j`. -/
def lollipopVertex (n : ℕ) (j : Fin k) : Fin (n + k) := Fin.natAdd n j

/-- A core slot of the lollipop core. -/
def coreSlot (k : ℕ) (i : Fin p) : Fin (p + (k + k)) := Fin.castAdd (k + k) i

/-- The bridge of the lollipop at mark `j`. -/
def bridgeSlot (p : ℕ) (j : Fin k) : Fin (p + (k + k)) := Fin.natAdd p (Fin.castAdd k j)

/-- The loop of the lollipop at mark `j`. -/
def loopSlot (p : ℕ) (j : Fin k) : Fin (p + (k + k)) := Fin.natAdd p (Fin.natAdd k j)

section Simp

variable (core : Core n p) (mark : Fin k → Fin n)

@[simp] theorem attachLollipops_tail_core (i : Fin p) :
    (attachLollipops core mark).tail (coreSlot k i) = oldVertex k (core.tail i) := by
  simp [attachLollipops, coreSlot, oldVertex]

@[simp] theorem attachLollipops_head_core (i : Fin p) :
    (attachLollipops core mark).head (coreSlot k i) = oldVertex k (core.head i) := by
  simp [attachLollipops, coreSlot, oldVertex]

@[simp] theorem attachLollipops_tail_bridge (j : Fin k) :
    (attachLollipops core mark).tail (bridgeSlot p j) = oldVertex k (mark j) := by
  simp only [attachLollipops, bridgeSlot, oldVertex, Fin.addCases_right, Fin.addCases_left]

@[simp] theorem attachLollipops_head_bridge (j : Fin k) :
    (attachLollipops core mark).head (bridgeSlot p j) = lollipopVertex n j := by
  simp only [attachLollipops, bridgeSlot, lollipopVertex, Fin.addCases_right, Fin.addCases_left]

@[simp] theorem attachLollipops_tail_loop (j : Fin k) :
    (attachLollipops core mark).tail (loopSlot p j) = lollipopVertex n j := by
  simp only [attachLollipops, loopSlot, lollipopVertex, Fin.addCases_right]

@[simp] theorem attachLollipops_head_loop (j : Fin k) :
    (attachLollipops core mark).head (loopSlot p j) = lollipopVertex n j := by
  simp only [attachLollipops, loopSlot, lollipopVertex, Fin.addCases_right]

end Simp

theorem lollipopVertex_ne_oldVertex (j : Fin k) (v : Fin n) :
    lollipopVertex n j ≠ oldVertex k v := by
  intro h
  have := congrArg Fin.val h
  simp only [lollipopVertex, oldVertex, Fin.val_natAdd, Fin.val_castAdd] at this
  omega

@[simp] theorem oldVertex_inj {v w : Fin n} : oldVertex k v = oldVertex k w ↔ v = w :=
  ⟨fun h ↦ Fin.castAdd_injective n k h, fun h ↦ h ▸ rfl⟩

@[simp] theorem lollipopVertex_inj {i j : Fin k} :
    lollipopVertex n i = lollipopVertex n j ↔ i = j :=
  ⟨fun h ↦ Fin.natAdd_injective k n h, fun h ↦ h ▸ rfl⟩

/-- The loop of the lollipop at mark `j` is a core loop (`tail = head`), the hypothesis of the
public lollipop package (`LollipopLeafRow.exists_leafRow_of_core_loop` and its siblings). -/
theorem attachLollipops_loop_isLoop (core : Core n p) (mark : Fin k → Fin n) (j : Fin k) :
    (attachLollipops core mark).tail (loopSlot p j) =
      (attachLollipops core mark).head (loopSlot p j) := by
  simp

/-- An old vertex gains one incidence per lollipop attached at it. -/
theorem incidenceDegree_attachLollipops_old (core : Core n p) (mark : Fin k → Fin n)
    (v : Fin n) :
    (attachLollipops core mark).incidenceDegree (oldVertex k v) =
      core.incidenceDegree v + ∑ j : Fin k, if mark j = v then 1 else 0 := by
  unfold Core.incidenceDegree
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  have hne : ∀ j : Fin k, (lollipopVertex n j = oldVertex k v) ↔ False :=
    fun j ↦ iff_false_intro (lollipopVertex_ne_oldVertex j v)
  have h1 := attachLollipops_tail_core core mark
  have h2 := attachLollipops_head_core core mark
  have h3 := attachLollipops_tail_bridge core mark
  have h4 := attachLollipops_head_bridge core mark
  have h5 := attachLollipops_tail_loop core mark
  have h6 := attachLollipops_head_loop core mark
  simp only [coreSlot, bridgeSlot, loopSlot] at h1 h2 h3 h4 h5 h6
  simp only [h1, h2, h3, h4, h5, h6, hne, oldVertex_inj, ite_false, add_zero,
    Finset.sum_const_zero]

/-- The new vertex of a lollipop has incidence degree three: one for the bridge, two for the
loop. -/
theorem incidenceDegree_attachLollipops_new (core : Core n p) (mark : Fin k → Fin n)
    (j : Fin k) :
    (attachLollipops core mark).incidenceDegree (lollipopVertex n j) = 3 := by
  unfold Core.incidenceDegree
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  have hne : ∀ v : Fin n, (oldVertex k v = lollipopVertex n j) ↔ False :=
    fun v ↦ iff_false_intro fun h ↦ lollipopVertex_ne_oldVertex j v h.symm
  have h1 := attachLollipops_tail_core core mark
  have h2 := attachLollipops_head_core core mark
  have h3 := attachLollipops_tail_bridge core mark
  have h4 := attachLollipops_head_bridge core mark
  have h5 := attachLollipops_tail_loop core mark
  have h6 := attachLollipops_head_loop core mark
  simp only [coreSlot, bridgeSlot, loopSlot] at h1 h2 h3 h4 h5 h6
  simp only [h1, h2, h3, h4, h5, h6, hne, lollipopVertex_inj, ite_false, add_zero, zero_add,
    Finset.sum_const_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Nat.reduceAdd]

/-- **The lollipop core is cubic** when the marked core is marked-cubic: the essential model
`H^c` of `H` is trivalent. -/
theorem attachLollipops_cubic {core : Core n p} {mark : Fin k → Fin n}
    (h : IsMarkedCubic core mark) : (attachLollipops core mark).Cubic := by
  intro w
  refine Fin.addCases (fun v ↦ ?_) (fun j ↦ ?_) w
  · change (attachLollipops core mark).incidenceDegree (oldVertex k v) = 3
    rw [incidenceDegree_attachLollipops_old]
    by_cases hv : v ∈ Set.range mark
    · obtain ⟨j, rfl⟩ := hv
      have hone : (∑ i : Fin k, if mark i = mark j then 1 else 0) = 1 := by
        simp_rw [h.injective.eq_iff]
        simp
      rw [h.mark_degree j, hone]
    · have hzero : (∑ i : Fin k, if mark i = v then 1 else 0) = 0 :=
        Finset.sum_eq_zero fun i _ ↦ by
          simp only [ite_eq_right_iff]
          exact fun hi ↦ (hv ⟨i, hi⟩).elim
      rw [h.other_degree v hv, hzero]
  · exact incidenceDegree_attachLollipops_new core mark j

/-- **The lollipop core is connected** when the marked core is. -/
theorem attachLollipops_connected (core : Core n p) (mark : Fin k → Fin n)
    (h : core.Connected) : (attachLollipops core mark).Connected := by
  classical
  intro S hS
  set S' : Finset (Fin n) := univ.filter fun u ↦ oldVertex k u ∈ S with hS'
  have hmem : ∀ u : Fin n, u ∈ S' ↔ oldVertex k u ∈ S := by intro u; simp [hS']
  by_cases hsplit : ∃ v w : Fin n, v ∈ S' ∧ w ∉ S'
  · obtain ⟨i, hi⟩ := h S' hsplit
    refine ⟨coreSlot k i, ?_⟩
    simp only [attachLollipops_tail_core, attachLollipops_head_core]
    simpa [hmem] using hi
  · push Not at hsplit
    obtain ⟨v, w, hv, hw⟩ := hS
    by_cases hall : ∀ u : Fin n, oldVertex k u ∈ S
    · revert hw
      refine Fin.addCases (fun u hw ↦ ?_) (fun j hw ↦ ?_) w
      · exact absurd (hall u) hw
      · refine ⟨bridgeSlot p j, Or.inl ⟨?_, ?_⟩⟩
        · simpa using hall (mark j)
        · simpa [lollipopVertex] using hw
    · push Not at hall
      obtain ⟨u₀, hu₀⟩ := hall
      have hnone : ∀ u : Fin n, oldVertex k u ∉ S := by
        intro u hu
        exact hu₀ ((hmem u₀).mp (hsplit u u₀ ((hmem u).mpr hu)))
      revert hv
      refine Fin.addCases (fun u hv ↦ ?_) (fun j hv ↦ ?_) v
      · exact absurd hv (hnone u)
      · refine ⟨bridgeSlot p j, Or.inr ⟨?_, ?_⟩⟩
        · simpa [lollipopVertex] using hv
        · simpa using hnone (mark j)

/-- **The genus of the lollipop core** is that of the marked core plus the number of marks:
`g_H = g + a + b`. Truncated subtraction is harmless in this form. -/
theorem attachLollipops_genus (n p k : ℕ) :
    (p + (k + k)) + 1 - (n + k) = p + k + 1 - n := by
  omega

/-! ## 3.  The headline marked cores -/

/-- The mark of the once-marked core `subdivide core s`: the new vertex. -/
def onceMark (n : ℕ) : Fin 1 → Fin (n + 1) := fun _ ↦ Fin.last n

/-- The twice-marked core: subdivide slot `s₁`, then slot `s₂` of the result (which may be a
piece of `s₁`, so both marks may lie on one edge of `Γ`). -/
def twiceMarked (core : Core n p) (s₁ : Fin p) (s₂ : Fin (p + 1)) : Core (n + 1 + 1) (p + 1 + 1) :=
  subdivide (subdivide core s₁) s₂

/-- The two marks of `twiceMarked core s₁ s₂`: the vertices created by the two subdivisions. -/
def twiceMark (n : ℕ) : Fin 2 → Fin (n + 1 + 1) := ![(Fin.last n).castSucc, Fin.last (n + 1)]

/-- **The once-marked core is marked-cubic** (the genericity of `(Γ, u)`). -/
theorem isMarkedCubic_onceMarked {core : Core n p} (hCubic : core.Cubic) (s : Fin p) :
    IsMarkedCubic (subdivide core s) (onceMark n) where
  injective i j _ := Subsingleton.elim i j
  mark_degree _ := incidenceDegree_subdivide_last core s
  other_degree v hv := by
    revert hv
    refine Fin.lastCases (fun hv ↦ ?_) (fun u _ ↦ ?_) v
    · exact absurd ⟨0, rfl⟩ hv
    · rw [incidenceDegree_subdivide_castSucc, hCubic u]

/-- **The twice-marked core is marked-cubic** (the genericity of `(Γ, u, v)`). -/
theorem isMarkedCubic_twiceMarked {core : Core n p} (hCubic : core.Cubic) (s₁ : Fin p)
    (s₂ : Fin (p + 1)) : IsMarkedCubic (twiceMarked core s₁ s₂) (twiceMark n) where
  injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [twiceMark, Fin.ext_iff]
  mark_degree j := by
    fin_cases j
    · change (subdivide (subdivide core s₁) s₂).incidenceDegree (Fin.last n).castSucc = 2
      rw [incidenceDegree_subdivide_castSucc, incidenceDegree_subdivide_last]
    · exact incidenceDegree_subdivide_last _ s₂
  other_degree v hv := by
    unfold twiceMarked
    revert hv
    refine Fin.lastCases (fun hv ↦ ?_) (fun v hv ↦ ?_) v
    · exact absurd ⟨1, rfl⟩ hv
    · rw [incidenceDegree_subdivide_castSucc]
      revert hv
      refine Fin.lastCases (fun hv ↦ ?_) (fun u _ ↦ ?_) v
      · exact absurd ⟨0, rfl⟩ hv
      · rw [incidenceDegree_subdivide_castSucc, hCubic u]

theorem twiceMarked_connected {core : Core n p} (h : core.Connected) (s₁ : Fin p)
    (s₂ : Fin (p + 1)) : (twiceMarked core s₁ s₂).Connected :=
  subdivide_connected _ _ (subdivide_connected _ _ h)

/-! ## 4.  Requests on the lollipop core -/

/-- **The request on the lollipop core**: `y` on the core slots, `bridge j = β_j` on the bridge
slots and `loop j = λ_j` on the loop slots (`y_H = (y_{u,v}, β, λ, …)`). -/
def lollipopRequest (y : Fin p → ℚ) (bridge loop : Fin k → ℚ) : Fin (p + (k + k)) → ℚ :=
  Fin.append y (Fin.append bridge loop)

@[simp] theorem lollipopRequest_core (y : Fin p → ℚ) (bridge loop : Fin k → ℚ) (i : Fin p) :
    lollipopRequest y bridge loop (coreSlot k i) = y i := by
  simp [lollipopRequest, coreSlot]

@[simp] theorem lollipopRequest_bridge (y : Fin p → ℚ) (bridge loop : Fin k → ℚ) (j : Fin k) :
    lollipopRequest y bridge loop (bridgeSlot p j) = bridge j := by
  simp only [lollipopRequest, bridgeSlot, Fin.append_right, Fin.append_left]

@[simp] theorem lollipopRequest_loop (y : Fin p → ℚ) (bridge loop : Fin k → ℚ) (j : Fin k) :
    lollipopRequest y bridge loop (loopSlot p j) = loop j := by
  simp only [lollipopRequest, loopSlot, Fin.append_right]

/-- A positive request with positive tails is positive. -/
theorem lollipopRequest_pos {y : Fin p → ℚ} {bridge loop : Fin k → ℚ} (hy : ∀ i, 0 < y i)
    (hb : ∀ j, 0 < bridge j) (hl : ∀ j, 0 < loop j) :
    ∀ i, 0 < lollipopRequest y bridge loop i := by
  intro i
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
  · simpa only [lollipopRequest, Fin.append_left] using hy i
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa only [lollipopRequest, Fin.append_right, Fin.append_left] using hb j
    · simpa only [lollipopRequest, Fin.append_right] using hl j

end DraismaVargas.Count.MarkedCount
