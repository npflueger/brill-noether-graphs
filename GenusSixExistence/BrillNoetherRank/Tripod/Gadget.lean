import Utilities.Subdivision.CubicCore
import Utilities.Subdivision.SubdivisionConnectivity

/-!
# The tripod gadget as a core

Tripod subtraction attaches a tripod `Y` to a genus-six graph `G` at the three points `p, q, r`
of a degree-three divisor `E`. The cubic core `Γ̃` of the gadget is built **by hand** from a cubic
core `G̃` of `G`:

* each mark sits on a slot of `G̃`; subdivide that slot at the mark, one mark at a time, so that
  several marks may share a slot in a fixed order (`subdivide`, `markedCore`);
* add a centre `c̃` joined to the three marks by three leg slots (`attachTripod`, `tripodCore`).

It must not be requested from `exists_expansionModel` applied to the gadget's own specification:
that may join two legs at a forest vertex when two marks coincide, and then the attached part
has a cycle.

Prose: `Research/genus-six-brill-noether-rank.md`, §3.1 (The gadget) and §6.2 (The tripod model);
section and statement numbers in this file refer to that note.

## Layout of `tripodCore core s : Core (n + 1 + 1 + 1 + 1) (p + 1 + 1 + 1 + 3)`

* vertices: `castSucc` of the vertices of `markedCore core s`, a
  `Core (n + 1 + 1 + 1) (p + 1 + 1 + 1)`, then the centre `centre n`, the last vertex. In
  `markedCore`, the vertices `< n` are those of `core` and `markVertex n k` (value `n + k`) is
  the `k`-th mark;
* slots: the `p + 3` slots of `markedCore` (`Fin.castAdd 3`; these are the **G-slots**: the
  slots of `G̃` split at the marks), then the three legs `legSlot p k` (`Fin.natAdd`), each
  from the centre to mark `k`.

A request on the gadget is a vector `y : Fin (p + 1 + 1 + 1 + 3) → ℚ`. `baseRequest s y` merges the
pieces of every split slot back into a request on `G̃`; `legLength y k` is the length of leg `k`.

## What is proved

All the cheap facts: the genus count (`tripodCore_genus`), cubicity (`tripodCore_cubic`),
connectedness (`tripodCore_connected`) and looplessness (`markedCore_loopless`,
`tripodCore_loopless`); that merging keeps total length and positivity (`sum_baseRequest`,
`baseRequest_pos`).
-/

namespace GenusSixExistence.Tripod

open Utilities.Certificate.ExplicitPotential (Core)
open Finset

namespace Gadget

variable {n p : ℕ}

/-! ## 1.  Subdividing one slot -/

/-- **Subdivide slot `e`** at a new vertex `Fin.last n`. Slot `e` keeps its tail and ends at
the new vertex; the new slot `Fin.last p` runs from the new vertex to the old head of `e`. -/
def subdivide (core : Core n p) (e : Fin p) : Core (n + 1) (p + 1) where
  tail := Fin.lastCases (Fin.last n) fun i ↦ (core.tail i).castSucc
  head := Fin.lastCases (core.head e).castSucc fun i ↦
    if i = e then Fin.last n else (core.head i).castSucc

@[simp] theorem subdivide_tail_castSucc (core : Core n p) (e i : Fin p) :
    (subdivide core e).tail i.castSucc = (core.tail i).castSucc := by
  simp [subdivide]

@[simp] theorem subdivide_tail_last (core : Core n p) (e : Fin p) :
    (subdivide core e).tail (Fin.last p) = Fin.last n := by
  simp [subdivide]

@[simp] theorem subdivide_head_castSucc (core : Core n p) (e i : Fin p) :
    (subdivide core e).head i.castSucc =
      if i = e then Fin.last n else (core.head i).castSucc := by
  simp [subdivide]

@[simp] theorem subdivide_head_last (core : Core n p) (e : Fin p) :
    (subdivide core e).head (Fin.last p) = (core.head e).castSucc := by
  simp [subdivide]

/-- Old vertices keep their incidence degree. -/
theorem incidenceDegree_subdivide_castSucc (core : Core n p) (e : Fin p) (v : Fin n) :
    (subdivide core e).incidenceDegree v.castSucc = core.incidenceDegree v := by
  unfold Core.incidenceDegree
  rw [Fin.sum_univ_castSucc]
  have hlast : Fin.last n ≠ v.castSucc := (Fin.castSucc_lt_last v).ne'
  have hpoint : ∀ i : Fin p,
      ((if (subdivide core e).tail i.castSucc = v.castSucc then 1 else 0) +
          (if (subdivide core e).head i.castSucc = v.castSucc then 1 else 0)) +
        (if i = e then (if core.head e = v then 1 else 0) else 0) =
      (if core.tail i = v then 1 else 0) + (if core.head i = v then 1 else 0) := by
    intro i
    by_cases hie : i = e
    · subst hie
      simp [hlast]
    · simp [hie]
  have hsum := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin p))) ↦ hpoint i)
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  rw [← hsum]
  congr 1
  simp [hlast]

/-- The new vertex has incidence degree two. -/
theorem incidenceDegree_subdivide_last (core : Core n p) (e : Fin p) :
    (subdivide core e).incidenceDegree (Fin.last n) = 2 := by
  unfold Core.incidenceDegree
  rw [Fin.sum_univ_castSucc]
  simp only [subdivide_tail_castSucc, subdivide_head_castSucc, subdivide_tail_last,
    subdivide_head_last]
  have hcs : ∀ v : Fin n, v.castSucc ≠ Fin.last n := fun v ↦ (Fin.castSucc_lt_last v).ne
  have hpoint : ∀ i : Fin p,
      ((if (core.tail i).castSucc = Fin.last n then 1 else 0) +
          (if (if i = e then Fin.last n else (core.head i).castSucc) = Fin.last n
            then 1 else 0)) = if i = e then 1 else 0 := by
    intro i
    by_cases hie : i = e
    · simp [hie, hcs]
    · simp [hie, hcs]
  rw [Finset.sum_congr rfl (fun i _ ↦ hpoint i), Finset.sum_ite_eq']
  simp [hcs]

theorem subdivide_loopless (core : Core n p) (e : Fin p)
    (h : ∀ i, core.tail i ≠ core.head i) :
    ∀ i, (subdivide core e).tail i ≠ (subdivide core e).head i := by
  intro i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simp only [subdivide_tail_last, subdivide_head_last]
    exact (Fin.castSucc_lt_last _).ne'
  · simp only [subdivide_tail_castSucc, subdivide_head_castSucc]
    split_ifs with hie
    · exact (Fin.castSucc_lt_last _).ne
    · intro hh
      exact h i (Fin.castSucc_injective _ hh)

/-- Subdividing a slot keeps the core connected. -/
theorem subdivide_connected (core : Core n p) (e : Fin p) (h : core.Connected) :
    (subdivide core e).Connected := by
  classical
  intro S hS
  set S' : Finset (Fin n) := univ.filter fun u ↦ u.castSucc ∈ S with hS'
  have hmem : ∀ u : Fin n, u ∈ S' ↔ u.castSucc ∈ S := by intro u; simp [hS']
  by_cases hsplit : ∃ v w : Fin n, v ∈ S' ∧ w ∉ S'
  · obtain ⟨i, hi⟩ := h S' hsplit
    by_cases hie : i = e
    · subst hie
      by_cases hx : Fin.last n ∈ S
      · rcases hi with ⟨ht, hh⟩ | ⟨hh, ht⟩
        · refine ⟨Fin.last p, Or.inl ⟨by simpa using hx, ?_⟩⟩
          simpa [hmem] using hh
        · refine ⟨i.castSucc, Or.inr ⟨by simpa using hx, ?_⟩⟩
          simpa [hmem] using ht
      · rcases hi with ⟨ht, hh⟩ | ⟨hh, ht⟩
        · refine ⟨i.castSucc, Or.inl ⟨by simpa [hmem] using ht, by simpa using hx⟩⟩
        · refine ⟨Fin.last p, Or.inr ⟨by simpa [hmem] using hh, by simpa using hx⟩⟩
    · refine ⟨i.castSucc, ?_⟩
      simp only [subdivide_tail_castSucc, subdivide_head_castSucc, if_neg hie]
      simpa [hmem] using hi
  · push Not at hsplit
    obtain ⟨v, w, hv, hw⟩ := hS
    by_cases hall : ∀ u : Fin n, u.castSucc ∈ S
    · -- every old vertex is in `S`, so the new vertex is not
      have hx : Fin.last n ∉ S := by
        intro hx
        apply hw
        refine Fin.lastCases hx (fun u ↦ hall u) w
      refine ⟨e.castSucc, Or.inl ⟨?_, ?_⟩⟩
      · simpa using hall (core.tail e)
      · simpa using hx
    · push Not at hall
      obtain ⟨u₀, hu₀⟩ := hall
      have hnone : ∀ u : Fin n, u.castSucc ∉ S := by
        intro u hu
        exact hu₀ ((hmem u₀).mp (hsplit u u₀ ((hmem u).mpr hu)))
      have hx : Fin.last n ∈ S := by
        by_contra hx
        apply hw
        exfalso
        revert hv
        refine Fin.lastCases (fun h ↦ hx h) (fun u h ↦ hnone u h) v
      refine ⟨e.castSucc, Or.inr ⟨?_, ?_⟩⟩
      · simpa using hx
      · simpa using hnone (core.tail e)

/-! ## 2.  Attaching a tripod -/

/-- **Attach a tripod** at three vertices: a new centre `Fin.last n` and three leg slots, leg
`k` running from the centre to `mark k`. -/
def attachTripod (core : Core n p) (mark : Fin 3 → Fin n) : Core (n + 1) (p + 3) where
  tail := Fin.addCases (fun i ↦ (core.tail i).castSucc) fun _ ↦ Fin.last n
  head := Fin.addCases (fun i ↦ (core.head i).castSucc) fun k ↦ (mark k).castSucc

@[simp] theorem attachTripod_tail_castAdd (core : Core n p) (mark : Fin 3 → Fin n) (i : Fin p) :
    (attachTripod core mark).tail (Fin.castAdd 3 i) = (core.tail i).castSucc := by
  simp [attachTripod]

@[simp] theorem attachTripod_head_castAdd (core : Core n p) (mark : Fin 3 → Fin n) (i : Fin p) :
    (attachTripod core mark).head (Fin.castAdd 3 i) = (core.head i).castSucc := by
  simp [attachTripod]

@[simp] theorem attachTripod_tail_natAdd (core : Core n p) (mark : Fin 3 → Fin n) (k : Fin 3) :
    (attachTripod core mark).tail (Fin.natAdd p k) = Fin.last n := by
  simp [attachTripod]

@[simp] theorem attachTripod_head_natAdd (core : Core n p) (mark : Fin 3 → Fin n) (k : Fin 3) :
    (attachTripod core mark).head (Fin.natAdd p k) = (mark k).castSucc := by
  simp [attachTripod]

theorem castSucc_ne_last' (v : Fin n) : v.castSucc ≠ Fin.last n :=
  (Fin.castSucc_lt_last v).ne

/-- An old vertex gains one incidence per leg ending there. -/
theorem incidenceDegree_attachTripod_castSucc (core : Core n p) (mark : Fin 3 → Fin n)
    (v : Fin n) :
    (attachTripod core mark).incidenceDegree v.castSucc =
      core.incidenceDegree v + ∑ k : Fin 3, if mark k = v then 1 else 0 := by
  unfold Core.incidenceDegree
  rw [Fin.sum_univ_add]
  simp only [attachTripod_tail_castAdd, attachTripod_head_castAdd, attachTripod_tail_natAdd,
    attachTripod_head_natAdd, Fin.castSucc_inj]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have : Fin.last n ≠ v.castSucc := fun h ↦ castSucc_ne_last' v h.symm
  simp [this]

/-- The centre has incidence degree three. -/
theorem incidenceDegree_attachTripod_last (core : Core n p) (mark : Fin 3 → Fin n) :
    (attachTripod core mark).incidenceDegree (Fin.last n) = 3 := by
  unfold Core.incidenceDegree
  rw [Fin.sum_univ_add]
  simp only [attachTripod_tail_castAdd, attachTripod_head_castAdd, attachTripod_tail_natAdd,
    attachTripod_head_natAdd]
  have h1 : ∀ v : Fin n, v.castSucc ≠ Fin.last n := castSucc_ne_last'
  simp [h1]

theorem attachTripod_loopless (core : Core n p) (mark : Fin 3 → Fin n)
    (h : ∀ i, core.tail i ≠ core.head i) :
    ∀ i, (attachTripod core mark).tail i ≠ (attachTripod core mark).head i := by
  intro i
  refine Fin.addCases (fun i ↦ ?_) (fun k ↦ ?_) i
  · simp only [attachTripod_tail_castAdd, attachTripod_head_castAdd]
    intro hh
    exact h i (Fin.castSucc_injective _ hh)
  · simp only [attachTripod_tail_natAdd, attachTripod_head_natAdd]
    exact fun hh ↦ castSucc_ne_last' _ hh.symm

/-- Attaching a tripod keeps the core connected. -/
theorem attachTripod_connected (core : Core n p) (mark : Fin 3 → Fin n) (h : core.Connected) :
    (attachTripod core mark).Connected := by
  classical
  intro S hS
  set S' : Finset (Fin n) := univ.filter fun u ↦ u.castSucc ∈ S with hS'
  have hmem : ∀ u : Fin n, u ∈ S' ↔ u.castSucc ∈ S := by intro u; simp [hS']
  by_cases hsplit : ∃ v w : Fin n, v ∈ S' ∧ w ∉ S'
  · obtain ⟨i, hi⟩ := h S' hsplit
    refine ⟨Fin.castAdd 3 i, ?_⟩
    simp only [attachTripod_tail_castAdd, attachTripod_head_castAdd]
    simpa [hmem] using hi
  · push Not at hsplit
    obtain ⟨v, w, hv, hw⟩ := hS
    by_cases hall : ∀ u : Fin n, u.castSucc ∈ S
    · have hx : Fin.last n ∉ S := by
        intro hx
        apply hw
        refine Fin.lastCases hx (fun u ↦ hall u) w
      refine ⟨Fin.natAdd p 0, Or.inr ⟨?_, ?_⟩⟩
      · simpa using hall (mark 0)
      · simpa using hx
    · push Not at hall
      obtain ⟨u₀, hu₀⟩ := hall
      have hnone : ∀ u : Fin n, u.castSucc ∉ S := by
        intro u hu
        exact hu₀ ((hmem u₀).mp (hsplit u u₀ ((hmem u).mpr hu)))
      have hx : Fin.last n ∈ S := by
        by_contra hx
        apply hw
        exfalso
        revert hv
        refine Fin.lastCases (fun h ↦ hx h) (fun u h ↦ hnone u h) v
      refine ⟨Fin.natAdd p 0, Or.inl ⟨?_, ?_⟩⟩
      · simpa using hx
      · simpa using hnone (mark 0)

/-! ## 3.  The gadget -/

/-- **Where the three marks sit.** Mark `0` on a slot of `G̃`; mark `1` on a slot of `G̃`
subdivided once (possibly a piece of the slot of mark `0`); mark `2` on a slot of `G̃` subdivided
twice. -/
structure MarkSlots (p : ℕ) where
  /-- The slot of `G̃` carrying mark `0`. -/
  first : Fin p
  /-- The slot, after the first subdivision, carrying mark `1`. -/
  second : Fin (p + 1)
  /-- The slot, after the second subdivision, carrying mark `2`. -/
  third : Fin (p + 1 + 1)

/-- **The marked core**: `G̃` with its slots subdivided at the three marks. Its first `n`
vertices are those of `G̃`, and `markVertex n k` is mark `k`. These are the G-slots of the
gadget. -/
def markedCore (core : Core n p) (s : MarkSlots p) : Core (n + 1 + 1 + 1) (p + 1 + 1 + 1) :=
  subdivide (subdivide (subdivide core s.first) s.second) s.third

/-- Mark `k` of the marked core: the vertex created by the `k`-th subdivision. -/
def markVertex (n : ℕ) (k : Fin 3) : Fin (n + 1 + 1 + 1) := ⟨n + k, by omega⟩

theorem markVertex_injective (n : ℕ) : Function.Injective (markVertex n) := by
  intro a b h
  have := congrArg Fin.val h
  simp only [markVertex] at this
  exact Fin.ext (by omega)

/-- **The tripod core** `Γ̃`: the marked core with a centre joined to the three marks. -/
def tripodCore (core : Core n p) (s : MarkSlots p) : Core (n + 1 + 1 + 1 + 1) (p + 1 + 1 + 1 + 3) :=
  attachTripod (markedCore core s) (markVertex n)

/-- The centre of the tripod. -/
def centre (n : ℕ) : Fin (n + 1 + 1 + 1 + 1) := Fin.last (n + 1 + 1 + 1)

/-- Mark `k` as a vertex of the tripod core. -/
def tripodMark (n : ℕ) (k : Fin 3) : Fin (n + 1 + 1 + 1 + 1) := (markVertex n k).castSucc

/-- Leg `k`, from the centre to mark `k`. -/
def legSlot (p : ℕ) (k : Fin 3) : Fin (p + 1 + 1 + 1 + 3) := Fin.natAdd (p + 1 + 1 + 1) k

/-- The G-slots of the gadget are the slots of the marked core. -/
def IsGSlot (j : Fin (p + 1 + 1 + 1 + 3)) : Prop := j.val < p + 1 + 1 + 1

theorem legSlot_not_isGSlot (k : Fin 3) : ¬ IsGSlot (legSlot p k) := by
  intro h
  simp only [IsGSlot, legSlot, Fin.val_natAdd] at h
  omega

/-! ## 4.  Cheap facts -/

theorem markedCore_incidenceDegree_old (core : Core n p) (s : MarkSlots p) (v : Fin n) :
    (markedCore core s).incidenceDegree v.castSucc.castSucc.castSucc =
      core.incidenceDegree v := by
  unfold markedCore
  rw [incidenceDegree_subdivide_castSucc, incidenceDegree_subdivide_castSucc,
    incidenceDegree_subdivide_castSucc]

theorem markedCore_incidenceDegree_mark (core : Core n p) (s : MarkSlots p) (k : Fin 3) :
    (markedCore core s).incidenceDegree (markVertex n k) = 2 := by
  unfold markedCore
  obtain ⟨k, hk⟩ := k
  interval_cases k
  · have : markVertex n ⟨0, hk⟩ = (Fin.last n).castSucc.castSucc :=
      Fin.ext (by simp [markVertex])
    rw [this, incidenceDegree_subdivide_castSucc, incidenceDegree_subdivide_castSucc,
      incidenceDegree_subdivide_last]
  · have : markVertex n ⟨1, hk⟩ = (Fin.last (n + 1)).castSucc :=
      Fin.ext (by simp [markVertex])
    rw [this, incidenceDegree_subdivide_castSucc, incidenceDegree_subdivide_last]
  · have : markVertex n ⟨2, hk⟩ = Fin.last (n + 1 + 1) :=
      Fin.ext (by simp [markVertex])
    rw [this, incidenceDegree_subdivide_last]

/-- **The gadget is cubic** when `G̃` is. -/
theorem tripodCore_cubic (core : Core n p) (s : MarkSlots p) (h : core.Cubic) :
    (tripodCore core s).Cubic := by
  intro w
  unfold tripodCore
  refine Fin.lastCases ?_ (fun w ↦ ?_) w
  · exact incidenceDegree_attachTripod_last _ _
  · rw [incidenceDegree_attachTripod_castSucc]
    by_cases hw : w.val < n
    · have hw' : w = (⟨w.val, hw⟩ : Fin n).castSucc.castSucc.castSucc := Fin.ext rfl
      have hzero : (∑ k : Fin 3, if markVertex n k = w then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        rw [if_neg]
        intro hk
        have := congrArg Fin.val hk
        simp only [markVertex] at this
        omega
      rw [hzero, hw', markedCore_incidenceDegree_old, h]
    · have hk : w = markVertex n ⟨w.val - n, by omega⟩ :=
        Fin.ext (by simp only [markVertex]; omega)
      rw [hk, markedCore_incidenceDegree_mark]
      have hone : (∑ k : Fin 3, if markVertex n k = markVertex n ⟨w.val - n, by omega⟩
          then 1 else 0) = 1 := by
        simp_rw [(markVertex_injective n).eq_iff]
        simp
      rw [hone]

/-- **The gadget is connected** when `G̃` is. -/
theorem tripodCore_connected (core : Core n p) (s : MarkSlots p) (h : core.Connected) :
    (tripodCore core s).Connected :=
  attachTripod_connected _ _ (subdivide_connected _ _ (subdivide_connected _ _
    (subdivide_connected _ _ h)))

theorem markedCore_loopless (core : Core n p) (s : MarkSlots p)
    (h : ∀ i, core.tail i ≠ core.head i) :
    ∀ i, (markedCore core s).tail i ≠ (markedCore core s).head i :=
  subdivide_loopless _ _ (subdivide_loopless _ _ (subdivide_loopless _ _ h))

theorem tripodCore_loopless (core : Core n p) (s : MarkSlots p)
    (h : ∀ i, core.tail i ≠ core.head i) :
    ∀ i, (tripodCore core s).tail i ≠ (tripodCore core s).head i :=
  attachTripod_loopless _ _ (markedCore_loopless core s h)

/-- **The gadget has genus eight** when `G̃` has genus six. -/
theorem tripodCore_genus (h : p + 1 - n = 6) :
    (p + 1 + 1 + 1 + 3) + 1 - (n + 1 + 1 + 1 + 1) = 8 := by
  omega

/-! ## 5.  Requests -/

/-- Merge the two pieces of a subdivided slot `e` back into one. -/
def mergeRequest (e : Fin p) (y : Fin (p + 1) → ℚ) : Fin p → ℚ :=
  fun i ↦ if i = e then y i.castSucc + y (Fin.last p) else y i.castSucc

theorem sum_mergeRequest (e : Fin p) (y : Fin (p + 1) → ℚ) :
    ∑ i, mergeRequest e y i = ∑ j, y j := by
  rw [Fin.sum_univ_castSucc]
  have hpoint : ∀ i : Fin p, mergeRequest e y i =
      y i.castSucc + (if i = e then y (Fin.last p) else 0) := by
    intro i
    unfold mergeRequest
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun i _ ↦ hpoint i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- The G-part of a gadget request: the lengths of the slots of the marked core. -/
def gPart (y : Fin (p + 1 + 1 + 1 + 3) → ℚ) : Fin (p + 1 + 1 + 1) → ℚ :=
  fun i ↦ y (Fin.castAdd 3 i)

/-- **The base request** on `G̃`: the G-part with every split slot merged. -/
def baseRequest (s : MarkSlots p) (y : Fin (p + 1 + 1 + 1 + 3) → ℚ) : Fin p → ℚ :=
  mergeRequest s.first (mergeRequest s.second (mergeRequest s.third (gPart y)))

/-- The length of leg `k`. -/
def legLength (y : Fin (p + 1 + 1 + 1 + 3) → ℚ) (k : Fin 3) : ℚ := y (legSlot p k)

/-- Merging does not change total length. -/
theorem sum_baseRequest (s : MarkSlots p) (y : Fin (p + 1 + 1 + 1 + 3) → ℚ) :
    ∑ i, baseRequest s y i = ∑ i, gPart y i := by
  unfold baseRequest
  rw [sum_mergeRequest, sum_mergeRequest, sum_mergeRequest]

theorem mergeRequest_pos (e : Fin p) {y : Fin (p + 1) → ℚ} (h : ∀ j, 0 < y j) :
    ∀ i, 0 < mergeRequest e y i := by
  intro i
  unfold mergeRequest
  split_ifs
  · exact add_pos (h _) (h _)
  · exact h _

/-- A positive gadget request has a positive base request. -/
theorem baseRequest_pos (s : MarkSlots p) {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
    (h : ∀ j, 0 < y j) : ∀ i, 0 < baseRequest s y i :=
  mergeRequest_pos _ (mergeRequest_pos _ (mergeRequest_pos _ fun _ ↦ h _))

/-- **Long legs** at degree `4 = 6/2 + 1`: every leg is longer than four times the total length
of `G̃` (Lemma 4.6, Theorem 5.1; §6.3 (v)). -/
def LongLegs (s : MarkSlots p) (y : Fin (p + 1 + 1 + 1 + 3) → ℚ) : Prop :=
  ∀ k : Fin 3, 4 * ∑ i, baseRequest s y i < legLength y k

end Gadget

end GenusSixExistence.Tripod
