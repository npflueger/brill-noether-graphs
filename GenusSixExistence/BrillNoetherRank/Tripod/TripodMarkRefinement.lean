module

public import GenusSixExistence.BrillNoetherRank.Tripod.Gadget
public import Utilities.Subdivision.CoreExpansion
public import Utilities.Subdivision.OneEdgeSplitRefinement

@[expose] public section

/-!
# Refining an expansion datum at one mark

A step of the construction of tripod models (`TripodModelProof.lean`). Prose:
`Research/genus-six-brill-noether-rank.md`, §6.2 (The tripod model), the placement of the marks;
section numbers in this file refer to that note.

Given an expansion datum `D` from a big core onto a small specification `small`, and a vertex
`x` of the subdivided graph `small.graph`, `exists_markStep` subdivides one big slot `e` at a new
big vertex (`Gadget.subdivide`) and produces an expansion datum `D'` from the subdivided big core
onto a small specification `small'`, in which the new big vertex lies over a small core vertex
`w'` that the Laplacian equivalence `small'.graph ≃ small.graph` sends to `x`. Iterated three
times it places the three marks.

The cases are those of the mark placement of §6.2, by where `x` sits in `small`:

* **A** (`x` is a core vertex in the image of the fibre map, valence at least three in `G`):
  `small' = small`; the mark is put at offset `0` of a big slot `e` at a vertex `b` of the fibre,
  and the piece between `b` and the mark is **contracted** (a zero mark piece). `A1` if `b` is the
  tail of `e`, `A2` if it is the head.
* **B** (`x` is a core vertex outside the image: a bivalent marker of a `double`): `small' =
  small`; the double is split at its marker into two `single`s.
* **C** (`x` is an interior vertex of a small slot `j`, a bivalent vertex of `G`): `small'` is
  `small` with `j` split at `x` (`OneEdgeSplitRefinement.splitSpec`), and the owner of `j` is
  split at the same point. `C1`, `C2`, `C3`: the owner is `single j`, `double j _`, `double _ j`.

`refine_conditions` checks `ExpansionData.Conditions` once for the general refinement, from
facts about the two new pieces; each case then supplies those facts.
-/

namespace GenusSixExistence.Tripod.MarkRefinement

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ExplicitPotential (Core)
open Utilities.Subdivision.CoreExpansion
open Gadget

variable {n p N Q n' p' : ℕ}

/-! ## 1.  Kinds, and the slot conditions read off a kind -/

/-- Relabel the small slots carried by a kind. -/
def mapKind (f : Fin p → Fin p') : SlotKind p → SlotKind p'
  | .contracted => .contracted
  | .single j => .single (f j)
  | .double j₁ j₂ => .double (f j₁) (f j₂)

@[simp] theorem mapKind_contracted (f : Fin p → Fin p') :
    mapKind f (SlotKind.contracted : SlotKind p) = .contracted := rfl
@[simp] theorem mapKind_single (f : Fin p → Fin p') (j : Fin p) :
    mapKind f (SlotKind.single j) = .single (f j) := rfl
@[simp] theorem mapKind_double (f : Fin p → Fin p') (j₁ j₂ : Fin p) :
    mapKind f (SlotKind.double j₁ j₂) = .double (f j₁) (f j₂) := rfl

/-- `ExpansionData.SlotCompatible`, for a kind with given end fibres. -/
abbrev KindCompat (C : Core n p) (a b : Fin n) (κ : SlotKind p) : Prop :=
  (κ = .contracted → a = b) ∧
  (∀ j, κ = .single j → a = C.tail j ∧ b = C.head j) ∧
  (∀ j₁ j₂, κ = .double j₁ j₂ → a = C.tail j₁ ∧ C.head j₁ = C.tail j₂ ∧ b = C.head j₂)

/-- `ExpansionData.SlotIndexed`, for a kind at a given big slot. -/
abbrev KindIndexed (owner : Fin p → Fin Q) (side : Fin p → Bool) (e : Fin Q) (κ : SlotKind p) :
    Prop :=
  (∀ j, κ = .single j → owner j = e ∧ side j = false) ∧
  (∀ j₁ j₂, κ = .double j₁ j₂ → owner j₁ = e ∧ side j₁ = false ∧ owner j₂ = e ∧ side j₂ = true)

/-- `ExpansionData.SlotClaimed`, for the kind of the owner. -/
abbrev KindClaims (side : Fin p → Bool) (j : Fin p) (κ : SlotKind p) : Prop :=
  κ ≠ .contracted ∧
  (∀ j', κ = .single j' → side j = false ∧ j' = j) ∧
  (∀ j₁ j₂, κ = .double j₁ j₂ → (side j = false ∧ j₁ = j) ∨ (side j = true ∧ j₂ = j))

theorem compat_iff (D : ExpansionData n p N Q) (C : Core n p) (e : Fin Q) :
    D.SlotCompatible C e ↔
      KindCompat C (D.fib (D.bigCore.tail e)) (D.fib (D.bigCore.head e)) (D.kind e) := Iff.rfl

theorem indexed_iff (D : ExpansionData n p N Q) (e : Fin Q) :
    D.SlotIndexed e ↔ KindIndexed D.owner D.side e (D.kind e) := Iff.rfl

theorem claimed_iff (D : ExpansionData n p N Q) (j : Fin p) :
    D.SlotClaimed j ↔ KindClaims D.side j (D.kind (D.owner j)) := Iff.rfl

/-- The two small slots of a `double` are distinct. -/
theorem double_ne {D : ExpansionData n p N Q} {C : Core n p} (hD : D.Conditions C) {e : Fin Q}
    {j₁ j₂ : Fin p} (hk : D.kind e = .double j₁ j₂) : j₁ ≠ j₂ := by
  intro h
  subst h
  have := (ExpansionData.indexed_of_conditions hD e).2 j₁ j₁ hk
  rw [this.2.1] at this
  exact Bool.false_ne_true this.2.2.2

/-- A small slot carried by a big slot has that big slot as owner. -/
theorem owner_of_single {D : ExpansionData n p N Q} {C : Core n p} (hD : D.Conditions C)
    {i : Fin Q} {j : Fin p} (hk : D.kind i = .single j) : D.owner j = i :=
  ((ExpansionData.indexed_of_conditions hD i).1 j hk).1

theorem owner_of_double₁ {D : ExpansionData n p N Q} {C : Core n p} (hD : D.Conditions C)
    {i : Fin Q} {j₁ j₂ : Fin p} (hk : D.kind i = .double j₁ j₂) : D.owner j₁ = i :=
  ((ExpansionData.indexed_of_conditions hD i).2 j₁ j₂ hk).1

theorem owner_of_double₂ {D : ExpansionData n p N Q} {C : Core n p} (hD : D.Conditions C)
    {i : Fin Q} {j₁ j₂ : Fin p} (hk : D.kind i = .double j₁ j₂) : D.owner j₂ = i :=
  ((ExpansionData.indexed_of_conditions hD i).2 j₁ j₂ hk).2.2.1

/-- The slots carried by the owner of `j`, read off `exists_carrier`. -/
theorem owner_carries {D : ExpansionData n p N Q} {C : Core n p} (hD : D.Conditions C)
    (j j₀ : Fin p) (h : D.owner j₀ = D.owner j) :
    (D.kind (D.owner j) = .single j ∧ j₀ = j) ∨
      (∃ j₂, D.kind (D.owner j) = .double j j₂ ∧ (j₀ = j ∨ j₀ = j₂)) ∨
      (∃ j₁, D.kind (D.owner j) = .double j₁ j ∧ (j₀ = j₁ ∨ j₀ = j)) := by
  have hc := (claimed_iff D j₀).mp (ExpansionData.claimed_of_conditions hD j₀)
  unfold KindClaims at hc
  rw [h] at hc
  rcases ExpansionData.exists_carrier hD j with ⟨hk, -⟩ | ⟨j₂, hk, -⟩ | ⟨j₁, hk, -⟩
  · exact Or.inl ⟨hk, ((hc.2.1 j hk).2).symm⟩
  · refine Or.inr (Or.inl ⟨j₂, hk, ?_⟩)
    rcases hc.2.2 j j₂ hk with ⟨-, h1⟩ | ⟨-, h2⟩
    · exact Or.inl h1.symm
    · exact Or.inr h2.symm
  · refine Or.inr (Or.inr ⟨j₁, hk, ?_⟩)
    rcases hc.2.2 j₁ j hk with ⟨-, h1⟩ | ⟨-, h2⟩
    · exact Or.inl h1.symm
    · exact Or.inr h2.symm


/-! ### Building the slot conditions of a kind -/

section KindLemmas

variable {C : Core n p} {a b : Fin n} {owner : Fin p → Fin Q} {side : Fin p → Bool} {e : Fin Q}

theorem compat_contracted (h : a = b) : KindCompat C a b .contracted :=
  ⟨fun _ ↦ h, fun _ h ↦ (by cases h), fun _ _ h ↦ (by cases h)⟩

theorem compat_single {j : Fin p} (h1 : a = C.tail j) (h2 : b = C.head j) :
    KindCompat C a b (.single j) := by
  refine ⟨fun h ↦ (by cases h), fun j' h ↦ ?_, fun _ _ h ↦ (by cases h)⟩
  cases h
  exact ⟨h1, h2⟩

theorem compat_double {j₁ j₂ : Fin p} (h1 : a = C.tail j₁) (h2 : C.head j₁ = C.tail j₂)
    (h3 : b = C.head j₂) : KindCompat C a b (.double j₁ j₂) := by
  refine ⟨fun h ↦ (by cases h), fun _ h ↦ (by cases h), fun j₁' j₂' h ↦ ?_⟩
  cases h
  exact ⟨h1, h2, h3⟩

theorem indexed_contracted : KindIndexed owner side e .contracted :=
  ⟨fun _ h ↦ (by cases h), fun _ _ h ↦ (by cases h)⟩

theorem indexed_single {j : Fin p} (h1 : owner j = e) (h2 : side j = false) :
    KindIndexed owner side e (.single j) := by
  refine ⟨fun j' h ↦ ?_, fun _ _ h ↦ (by cases h)⟩
  cases h
  exact ⟨h1, h2⟩

theorem indexed_double {j₁ j₂ : Fin p} (h1 : owner j₁ = e) (h2 : side j₁ = false)
    (h3 : owner j₂ = e) (h4 : side j₂ = true) : KindIndexed owner side e (.double j₁ j₂) := by
  refine ⟨fun _ h ↦ (by cases h), fun j₁' j₂' h ↦ ?_⟩
  cases h
  exact ⟨h1, h2, h3, h4⟩

theorem claims_single {j : Fin p} (h : side j = false) : KindClaims side j (.single j) := by
  refine ⟨fun h ↦ (by cases h), fun j' h' ↦ ?_, fun _ _ h ↦ (by cases h)⟩
  cases h'
  exact ⟨h, rfl⟩

theorem claims_double₁ {j₁ j₂ : Fin p} (h : side j₁ = false) :
    KindClaims side j₁ (.double j₁ j₂) := by
  refine ⟨fun h ↦ (by cases h), fun _ h ↦ (by cases h), fun j₁' j₂' h' ↦ ?_⟩
  cases h'
  exact Or.inl ⟨h, rfl⟩

theorem claims_double₂ {j₁ j₂ : Fin p} (h : side j₂ = true) :
    KindClaims side j₂ (.double j₁ j₂) := by
  refine ⟨fun h ↦ (by cases h), fun _ h ↦ (by cases h), fun j₁' j₂' h' ↦ ?_⟩
  cases h'
  exact Or.inr ⟨h, rfl⟩

end KindLemmas

/-! ## 2.  The refined datum -/

/-- **The refinement of `D` at big slot `e`.** The big core is `subdivide D.bigCore e`; the new
big vertex lies over `μ`, the old ones over `ι ∘ D.fib`; the two pieces of `e` have kinds `κ₁`
(the old slot, which ends at the new vertex) and `κ₂` (the new last slot), and every other slot
keeps its kind, relabelled by `ιs`. -/
def refine (D : ExpansionData n p N Q) (e : Fin Q) (ι : Fin n → Fin n') (ιs : Fin p → Fin p')
    (μ : Fin n') (κ₁ κ₂ : SlotKind p') (owner' : Fin p' → Fin (Q + 1))
    (side' : Fin p' → Bool) : ExpansionData n' p' (N + 1) (Q + 1) where
  bigCore := subdivide D.bigCore e
  fib := Fin.lastCases μ fun v ↦ ι (D.fib v)
  kind := Fin.lastCases κ₂ fun i ↦ if i = e then κ₁ else mapKind ιs (D.kind i)
  owner := owner'
  side := side'

section Refine

variable (D : ExpansionData n p N Q) (e : Fin Q) (ι : Fin n → Fin n') (ιs : Fin p → Fin p')
  (μ : Fin n') (κ₁ κ₂ : SlotKind p') (owner' : Fin p' → Fin (Q + 1)) (side' : Fin p' → Bool)

@[simp] theorem refine_bigCore : (refine D e ι ιs μ κ₁ κ₂ owner' side').bigCore =
    subdivide D.bigCore e := rfl
@[simp] theorem refine_fib_last : (refine D e ι ιs μ κ₁ κ₂ owner' side').fib (Fin.last N) = μ := by
  simp [refine]
@[simp] theorem refine_fib_castSucc (v : Fin N) :
    (refine D e ι ιs μ κ₁ κ₂ owner' side').fib v.castSucc = ι (D.fib v) := by
  simp [refine]
@[simp] theorem refine_kind_last :
    (refine D e ι ιs μ κ₁ κ₂ owner' side').kind (Fin.last Q) = κ₂ := by
  simp [refine]
@[simp] theorem refine_kind_e :
    (refine D e ι ιs μ κ₁ κ₂ owner' side').kind e.castSucc = κ₁ := by
  simp [refine]
theorem refine_kind_ne {i : Fin Q} (hi : i ≠ e) :
    (refine D e ι ιs μ κ₁ κ₂ owner' side').kind i.castSucc = mapKind ιs (D.kind i) := by
  simp [refine, hi]
@[simp] theorem refine_owner : (refine D e ι ιs μ κ₁ κ₂ owner' side').owner = owner' := rfl
@[simp] theorem refine_side : (refine D e ι ιs μ κ₁ κ₂ owner' side').side = side' := rfl

/-- Every big vertex of the refinement still has an incident slot. -/
theorem refine_incident (hInc : ∀ v : Fin N, ∃ i, D.bigCore.tail i = v ∨ D.bigCore.head i = v) :
    ∀ v : Fin (N + 1), ∃ i, (subdivide D.bigCore e).tail i = v ∨
      (subdivide D.bigCore e).head i = v := by
  intro v
  refine Fin.lastCases ⟨Fin.last Q, Or.inl (by simp)⟩ (fun v ↦ ?_) v
  obtain ⟨i, hi⟩ := hInc v
  rcases hi with hi | hi
  · exact ⟨i.castSucc, Or.inl (by simp [hi])⟩
  · by_cases hie : i = e
    · subst hie
      exact ⟨Fin.last Q, Or.inr (by simp [hi])⟩
    · exact ⟨i.castSucc, Or.inr (by simp [hie, hi])⟩

end Refine

/-! ## 3.  The conditions, once -/

section Conditions

variable {D : ExpansionData n p N Q} {C : Core n p} {C' : Core n' p'} {e : Fin Q}
  {ι : Fin n → Fin n'} {ιs : Fin p → Fin p'} {μ : Fin n'} {κ₁ κ₂ : SlotKind p'}
  {owner' : Fin p' → Fin (Q + 1)} {side' : Fin p' → Bool}

/-- **The marker condition for a new piece**: the middle vertex of a `double` is outside the image
of the refined fibre map, and only one small slot ends there. -/
abbrev KindMarker (C' : Core n' p') (ι : Fin n → Fin n') (fib : Fin N → Fin n) (μ : Fin n')
    (κ : SlotKind p') : Prop :=
  ∀ j₁ j₂, κ = .double j₁ j₂ →
    (∀ v, ι (fib v) ≠ C'.head j₁) ∧ μ ≠ C'.head j₁ ∧ (∀ j, C'.head j = C'.head j₁ → j = j₁)


theorem marker_contracted {C' : Core n' p'} {ι : Fin n → Fin n'} {fib : Fin N → Fin n}
    {μ : Fin n'} : KindMarker C' ι fib μ .contracted := fun _ _ h ↦ by cases h

theorem marker_single {C' : Core n' p'} {ι : Fin n → Fin n'} {fib : Fin N → Fin n}
    {μ : Fin n'} {j : Fin p'} : KindMarker C' ι fib μ (.single j) := fun _ _ h ↦ by cases h

theorem marker_double {C' : Core n' p'} {ι : Fin n → Fin n'} {fib : Fin N → Fin n}
    {μ : Fin n'} {j₁ j₂ : Fin p'} (h1 : ∀ v, ι (fib v) ≠ C'.head j₁) (h2 : μ ≠ C'.head j₁)
    (h3 : ∀ j, C'.head j = C'.head j₁ → j = j₁) : KindMarker C' ι fib μ (.double j₁ j₂) := by
  intro j₁' j₂' h
  cases h
  exact ⟨h1, h2, h3⟩

/-- The fibre condition, for a refinement: if some old vertex lies over `w'` on each side of `T`,
there is a crossing contracted slot. -/
theorem refine_fibre_old (hD : D.Conditions C) (hι : Function.Injective ι)
    (hcon : D.kind e = .contracted →
      κ₁ = .contracted ∧ κ₂ = .contracted ∧ μ = ι (D.fib (D.bigCore.tail e)))
    (w' : Fin n') (T : Finset (Fin (N + 1)))
    (ha : ∃ a : Fin N, a.castSucc ∈ T ∧ ι (D.fib a) = w')
    (hb : ∃ b : Fin N, b.castSucc ∉ T ∧ ι (D.fib b) = w') :
    ∃ i : Fin (Q + 1), (refine D e ι ιs μ κ₁ κ₂ owner' side').kind i = .contracted ∧
      (refine D e ι ιs μ κ₁ κ₂ owner' side').fib
          ((refine D e ι ιs μ κ₁ κ₂ owner' side').bigCore.tail i) = w' ∧
      (((refine D e ι ιs μ κ₁ κ₂ owner' side').bigCore.tail i ∈ T ∧
          (refine D e ι ιs μ κ₁ κ₂ owner' side').bigCore.head i ∉ T) ∨
        ((refine D e ι ιs μ κ₁ κ₂ owner' side').bigCore.head i ∈ T ∧
          (refine D e ι ιs μ κ₁ κ₂ owner' side').bigCore.tail i ∉ T)) := by
  classical
  obtain ⟨a, haT, haw⟩ := ha
  obtain ⟨b, hbT, hbw⟩ := hb
  have hab : D.fib a = D.fib b := hι (haw.trans hbw.symm)
  set T₀ : Finset (Fin N) := Finset.univ.filter fun v ↦ v.castSucc ∈ T with hT₀
  have hmem : ∀ v, v ∈ T₀ ↔ v.castSucc ∈ T := by intro v; simp [hT₀]
  obtain ⟨e₀, hk₀, hf₀, hcross⟩ := ExpansionData.fibre_of_conditions hD (D.fib a) T₀
    ⟨a, (hmem a).mpr haT, rfl⟩ ⟨b, fun h ↦ hbT ((hmem b).mp h), hab.symm⟩
  by_cases he : e₀ = e
  · subst he
    obtain ⟨h1, h2, hμ⟩ := hcon hk₀
    have hμw : μ = w' := by rw [hμ, hf₀, haw]
    by_cases hlast : Fin.last N ∈ T
    · rcases hcross with ⟨ht, hh⟩ | ⟨hh, ht⟩
      · refine ⟨Fin.last Q, by simp [h2], by simp [hμw], Or.inl ⟨by simpa using hlast, ?_⟩⟩
        simpa [hmem] using hh
      · refine ⟨e₀.castSucc, by simp [h1], by simp [hf₀, haw], Or.inr ⟨by simpa using hlast, ?_⟩⟩
        simpa [hmem] using ht
    · rcases hcross with ⟨ht, hh⟩ | ⟨hh, ht⟩
      · refine ⟨e₀.castSucc, by simp [h1], by simp [hf₀, haw], Or.inl ⟨?_, by simpa using hlast⟩⟩
        simpa [hmem] using ht
      · refine ⟨Fin.last Q, by simp [h2], by simp [hμw], Or.inr ⟨?_, by simpa using hlast⟩⟩
        simpa [hmem] using hh
  · refine ⟨e₀.castSucc, ?_, ?_, ?_⟩
    · rw [refine_kind_ne D e ι ιs μ κ₁ κ₂ owner' side' he, hk₀]
      rfl
    · simp [hf₀, haw]
    · simp only [refine_bigCore, subdivide_tail_castSucc, subdivide_head_castSucc, ite_eq_right he]
      simpa [hmem] using hcross

/-- **`Conditions` for a refinement**, from facts about its two new pieces. -/
theorem refine_conditions (hD : D.Conditions C)
    (hι : Function.Injective ι)
    (hmor : ∀ j, D.owner j ≠ e → C'.tail (ιs j) = ι (C.tail j) ∧ C'.head (ιs j) = ι (C.head j))
    (hown : ∀ j, D.owner j ≠ e → owner' (ιs j) = (D.owner j).castSucc ∧ side' (ιs j) = D.side j)
    (hc₁ : KindCompat C' (ι (D.fib (D.bigCore.tail e))) μ κ₁)
    (hc₂ : KindCompat C' μ (ι (D.fib (D.bigCore.head e))) κ₂)
    (hi₁ : KindIndexed owner' side' e.castSucc κ₁)
    (hi₂ : KindIndexed owner' side' (Fin.last Q) κ₂)
    (hnew : ∀ j', (∀ j, D.owner j ≠ e → j' ≠ ιs j) →
      (owner' j' = e.castSucc ∧ KindClaims side' j' κ₁) ∨
        (owner' j' = Fin.last Q ∧ KindClaims side' j' κ₂))
    (hμold : ∀ i j₁ j₂, i ≠ e → D.kind i = .double j₁ j₂ → μ ≠ ι (C.head j₁))
    (hhead : ∀ i j₁ j₂, i ≠ e → D.kind i = .double j₁ j₂ →
      ∀ j', C'.head j' = ι (C.head j₁) → j' = ιs j₁)
    (hm₁ : KindMarker C' ι D.fib μ κ₁) (hm₂ : KindMarker C' ι D.fib μ κ₂)
    (hinc : ∀ w', ∃ j', C'.tail j' = w' ∨ C'.head j' = w')
    (hcon : D.kind e = .contracted →
      κ₁ = .contracted ∧ κ₂ = .contracted ∧ μ = ι (D.fib (D.bigCore.tail e)))
    (hμ : ∀ v, ι (D.fib v) = μ →
      (κ₁ = .contracted ∧ ι (D.fib (D.bigCore.tail e)) = μ) ∨
        (κ₂ = .contracted ∧ ι (D.fib (D.bigCore.head e)) = μ)) :
    (refine D e ι ιs μ κ₁ κ₂ owner' side').Conditions C' := by
  classical
  set D' := refine D e ι ιs μ κ₁ κ₂ owner' side' with hD'
  refine ⟨?_, ?_, ?_, ?_, ?_, hinc, ?_⟩
  · -- loopless
    exact subdivide_loopless _ _ (ExpansionData.loopless_of_conditions hD)
  · -- compatibility
    intro i'
    refine Fin.lastCases ?_ (fun i ↦ ?_) i'
    · rw [compat_iff]
      simpa [hD'] using hc₂
    · by_cases hie : i = e
      · subst hie
        rw [compat_iff]
        simpa [hD'] using hc₁
      · rw [compat_iff, hD', refine_kind_ne D e ι ιs μ κ₁ κ₂ owner' side' hie]
        simp only [refine_bigCore, subdivide_tail_castSucc, subdivide_head_castSucc, ite_eq_right hie,
          refine_fib_castSucc]
        have hc := (compat_iff D C i).mp (ExpansionData.compatible_of_conditions hD i)
        refine ⟨?_, ?_, ?_⟩
        · intro hk
          cases hki : D.kind i with
          | contracted => rw [hki] at hc; rw [hc.1 rfl]
          | single j => rw [hki] at hk; cases hk
          | double j₁ j₂ => rw [hki] at hk; cases hk
        · intro j' hk
          cases hki : D.kind i with
          | contracted => rw [hki] at hk; cases hk
          | single j =>
            rw [hki] at hk hc
            simp only [mapKind_single, SlotKind.single.injEq] at hk
            subst hk
            have hoj : D.owner j ≠ e := by rw [owner_of_single hD hki]; exact hie
            obtain ⟨h1, h2⟩ := hc.2.1 j rfl
            rw [(hmor j hoj).1, (hmor j hoj).2, h1, h2]
            exact ⟨rfl, rfl⟩
          | double j₁ j₂ => rw [hki] at hk; cases hk
        · intro j₁' j₂' hk
          cases hki : D.kind i with
          | contracted => rw [hki] at hk; cases hk
          | single j => rw [hki] at hk; cases hk
          | double j₁ j₂ =>
            rw [hki] at hk hc
            simp only [mapKind_double, SlotKind.double.injEq] at hk
            obtain ⟨rfl, rfl⟩ := hk
            have ho1 : D.owner j₁ ≠ e := by rw [owner_of_double₁ hD hki]; exact hie
            have ho2 : D.owner j₂ ≠ e := by rw [owner_of_double₂ hD hki]; exact hie
            obtain ⟨h1, h2, h3⟩ := hc.2.2 j₁ j₂ rfl
            rw [(hmor j₁ ho1).1, (hmor j₁ ho1).2, (hmor j₂ ho2).1, (hmor j₂ ho2).2, h1, h2, h3]
            exact ⟨rfl, rfl, rfl⟩
  · -- indexing
    intro i'
    refine Fin.lastCases ?_ (fun i ↦ ?_) i'
    · rw [indexed_iff]
      simpa [hD'] using hi₂
    · by_cases hie : i = e
      · subst hie
        rw [indexed_iff]
        simpa [hD'] using hi₁
      · rw [indexed_iff, hD', refine_kind_ne D e ι ιs μ κ₁ κ₂ owner' side' hie]
        simp only [refine_owner, refine_side]
        refine ⟨?_, ?_⟩
        · intro j' hk
          cases hki : D.kind i with
          | contracted => rw [hki] at hk; cases hk
          | single j =>
            rw [hki] at hk
            simp only [mapKind_single, SlotKind.single.injEq] at hk
            subst hk
            have hoj := owner_of_single hD hki
            have hside := ((ExpansionData.indexed_of_conditions hD i).1 j hki).2
            obtain ⟨h1, h2⟩ := hown j (by rw [hoj]; exact hie)
            rw [h1, h2, hoj, hside]
            exact ⟨rfl, rfl⟩
          | double j₁ j₂ => rw [hki] at hk; cases hk
        · intro j₁' j₂' hk
          cases hki : D.kind i with
          | contracted => rw [hki] at hk; cases hk
          | single j => rw [hki] at hk; cases hk
          | double j₁ j₂ =>
            rw [hki] at hk
            simp only [mapKind_double, SlotKind.double.injEq] at hk
            obtain ⟨rfl, rfl⟩ := hk
            obtain ⟨ho1, hs1, ho2, hs2⟩ := (ExpansionData.indexed_of_conditions hD i).2 j₁ j₂ hki
            obtain ⟨h1, h2⟩ := hown j₁ (by rw [ho1]; exact hie)
            obtain ⟨h3, h4⟩ := hown j₂ (by rw [ho2]; exact hie)
            rw [h1, h2, h3, h4, ho1, ho2, hs1, hs2]
            exact ⟨rfl, rfl, rfl, rfl⟩
  · -- claims
    intro j'
    rw [claimed_iff]
    simp only [hD', refine_owner, refine_side]
    by_cases hold : ∃ j, D.owner j ≠ e ∧ j' = ιs j
    · obtain ⟨j, hoj, rfl⟩ := hold
      rw [(hown j hoj).1, refine_kind_ne D e ι ιs μ κ₁ κ₂ owner' side' hoj]
      unfold KindClaims
      rw [(hown j hoj).2]
      have hc := (claimed_iff D j).mp (ExpansionData.claimed_of_conditions hD j)
      refine ⟨?_, ?_, ?_⟩
      · intro hk
        cases hki : D.kind (D.owner j) with
        | contracted => exact hc.1 hki
        | single j₀ => rw [hki] at hk; cases hk
        | double j₁ j₂ => rw [hki] at hk; cases hk
      · intro j₀' hk
        cases hki : D.kind (D.owner j) with
        | contracted => rw [hki] at hk; cases hk
        | single j₀ =>
          rw [hki] at hk hc
          simp only [mapKind_single, SlotKind.single.injEq] at hk
          subst hk
          obtain ⟨h1, h2⟩ := hc.2.1 j₀ rfl
          rw [h2]
          exact ⟨h1, rfl⟩
        | double j₁ j₂ => rw [hki] at hk; cases hk
      · intro j₁' j₂' hk
        cases hki : D.kind (D.owner j) with
        | contracted => rw [hki] at hk; cases hk
        | single j₀ => rw [hki] at hk; cases hk
        | double j₁ j₂ =>
          rw [hki] at hk hc
          simp only [mapKind_double, SlotKind.double.injEq] at hk
          obtain ⟨rfl, rfl⟩ := hk
          rcases hc.2.2 j₁ j₂ rfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, by rw [h2]⟩
          · exact Or.inr ⟨h1, by rw [h2]⟩
    · push Not at hold
      rcases hnew j' (fun j hj h ↦ hold j hj h) with ⟨ho, hcl⟩ | ⟨ho, hcl⟩
      · rw [ho, refine_kind_e]
        exact hcl
      · rw [ho, refine_kind_last]
        exact hcl
  · -- markers
    intro i'
    refine Fin.lastCases ?_ (fun i ↦ ?_) i'
    · intro j₁ j₂ hk
      rw [refine_kind_last] at hk
      obtain ⟨h1, h2, h3⟩ := hm₂ j₁ j₂ hk
      refine ⟨fun v ↦ ?_, h3⟩
      refine Fin.lastCases ?_ (fun v ↦ ?_) v
      · rw [refine_fib_last]; exact h2
      · rw [refine_fib_castSucc]; exact h1 v
    · by_cases hie : i = e
      · subst hie
        intro j₁ j₂ hk
        rw [refine_kind_e] at hk
        obtain ⟨h1, h2, h3⟩ := hm₁ j₁ j₂ hk
        refine ⟨fun v ↦ ?_, h3⟩
        refine Fin.lastCases ?_ (fun v ↦ ?_) v
        · rw [refine_fib_last]; exact h2
        · rw [refine_fib_castSucc]; exact h1 v
      · intro j₁' j₂' hk
        rw [refine_kind_ne D e ι ιs μ κ₁ κ₂ owner' side' hie] at hk
        cases hki : D.kind i with
        | contracted => rw [hki] at hk; cases hk
        | single j => rw [hki] at hk; cases hk
        | double j₁ j₂ =>
          rw [hki] at hk
          simp only [mapKind_double, SlotKind.double.injEq] at hk
          obtain ⟨rfl, rfl⟩ := hk
          have ho1 : D.owner j₁ ≠ e := by rw [owner_of_double₁ hD hki]; exact hie
          have hmk := ExpansionData.marker_of_conditions hD i j₁ j₂ hki
          rw [(hmor j₁ ho1).2]
          refine ⟨fun v ↦ ?_, hhead i j₁ j₂ hie hki⟩
          refine Fin.lastCases ?_ (fun v ↦ ?_) v
          · rw [refine_fib_last]; exact hμold i j₁ j₂ hie hki
          · rw [refine_fib_castSucc]
            exact fun h ↦ hmk.1 v (hι h)
  · -- fibres
    intro w' T ha hb
    obtain ⟨a, haT, haw⟩ := ha
    obtain ⟨b, hbT, hbw⟩ := hb
    have hold := refine_fibre_old (ιs := ιs) (owner' := owner') (side' := side') hD hι hcon w' T
    revert haT haw hbT hbw
    refine Fin.lastCases ?_ (fun a ↦ ?_) a <;> refine Fin.lastCases ?_ (fun b ↦ ?_) b
    · intro haT _ hbT _
      exact absurd haT hbT
    · intro haT haw hbT hbw
      rw [refine_fib_last] at haw
      rw [refine_fib_castSucc] at hbw
      rcases hμ b (hbw.trans haw.symm) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · by_cases ht : (D.bigCore.tail e).castSucc ∈ T
        · exact hold ⟨_, ht, h2.trans haw⟩ ⟨b, hbT, hbw⟩
        · refine ⟨e.castSucc, by simp [hD', h1], by simp [hD', h2, haw], Or.inr ⟨?_, ?_⟩⟩
          · simpa [hD'] using haT
          · simpa [hD'] using ht
      · by_cases hh : (D.bigCore.head e).castSucc ∈ T
        · exact hold ⟨_, hh, h2.trans haw⟩ ⟨b, hbT, hbw⟩
        · refine ⟨Fin.last Q, by simp [hD', h1], by simp [hD', haw], Or.inl ⟨?_, ?_⟩⟩
          · simpa [hD'] using haT
          · simpa [hD'] using hh
    · intro haT haw hbT hbw
      rw [refine_fib_castSucc] at haw
      rw [refine_fib_last] at hbw
      rcases hμ a (haw.trans hbw.symm) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · by_cases ht : (D.bigCore.tail e).castSucc ∈ T
        · refine ⟨e.castSucc, by simp [hD', h1], by simp [hD', h2, hbw], Or.inl ⟨?_, ?_⟩⟩
          · simpa [hD'] using ht
          · simpa [hD'] using hbT
        · exact hold ⟨a, haT, haw⟩ ⟨_, ht, h2.trans hbw⟩
      · by_cases hh : (D.bigCore.head e).castSucc ∈ T
        · refine ⟨Fin.last Q, by simp [hD', h1], by simp [hD', hbw], Or.inr ⟨?_, ?_⟩⟩
          · simpa [hD'] using hh
          · simpa [hD'] using hbT
        · exact hold ⟨a, haT, haw⟩ ⟨_, hh, h2.trans hbw⟩
    · intro haT haw hbT hbw
      rw [refine_fib_castSucc] at haw hbw
      exact hold ⟨a, haT, haw⟩ ⟨b, hbT, hbw⟩

end Conditions


/-! ## 4.  Case A: a mark at a vertex of the fibre image (a zero mark piece) -/

section CaseA

variable {D : ExpansionData n p N Q} {C : Core n p}

/-- **Case A** (§6.2, valence at least three). A small core vertex `w` over which some
big vertex `b` lies: subdivide a big slot at `b`, with a contracted piece from `b` to the mark. -/
theorem caseA (hD : D.Conditions C)
    (hInc : ∀ v : Fin N, ∃ i, D.bigCore.tail i = v ∨ D.bigCore.head i = v)
    (w : Fin n) (b : Fin N) (hb : D.fib b = w) :
    ∃ (D' : ExpansionData n p (N + 1) (Q + 1)) (e : Fin Q),
      D'.Conditions C ∧ D'.bigCore = subdivide D.bigCore e ∧ D'.fib (Fin.last N) = w ∧
        ∀ v, D'.fib v.castSucc = D.fib v := by
  classical
  obtain ⟨e, he⟩ := hInc b
  have hce := (compat_iff D C e).mp (ExpansionData.compatible_of_conditions hD e)
  have hie := (indexed_iff D e).mp (ExpansionData.indexed_of_conditions hD e)
  have hme := ExpansionData.marker_of_conditions hD e
  have hμold : ∀ i j₁ j₂, i ≠ e → D.kind i = .double j₁ j₂ → w ≠ id (C.head j₁) := by
    intro i j₁ j₂ _ hk h
    exact (ExpansionData.marker_of_conditions hD i j₁ j₂ hk).1 b (hb.trans h)
  have hhead : ∀ i j₁ j₂, i ≠ e → D.kind i = .double j₁ j₂ →
      ∀ j', C.head j' = id (C.head j₁) → j' = id j₁ :=
    fun i j₁ j₂ _ hk ↦ (ExpansionData.marker_of_conditions hD i j₁ j₂ hk).2
  have hmk : KindMarker C id D.fib w (D.kind e) := by
    intro j₁ j₂ hk
    obtain ⟨h1, h2⟩ := hme j₁ j₂ hk
    exact ⟨h1, fun h ↦ h1 b (hb.trans h), h2⟩
  have hnoneOwned : ∀ j' : Fin p, (∀ j, D.owner j ≠ e → j' ≠ id j) → D.owner j' = e := by
    intro j' h
    by_contra hne
    exact h j' hne rfl
  rcases he with ht | hh
  · -- A1: `b` is the tail of `e`; the old slot becomes the zero piece.
    have hcond : (refine D e id id w .contracted (D.kind e)
        (fun j ↦ if D.owner j = e then Fin.last Q else (D.owner j).castSucc) D.side).Conditions
          C := by
      refine refine_conditions hD Function.injective_id (fun _ _ ↦ ⟨rfl, rfl⟩)
        (fun j hj ↦ ⟨by simp [hj], rfl⟩) ?_ ?_ ?_ ?_ ?_ hμold hhead ?_ hmk
        (ExpansionData.incident_of_conditions hD) ?_ ?_
      · exact compat_contracted (by simp [ht, hb])
      · rw [ht, hb] at hce; exact hce
      · exact indexed_contracted
      · refine ⟨fun j hk ↦ ?_, fun j₁ j₂ hk ↦ ?_⟩
        · obtain ⟨h1, h2⟩ := hie.1 j hk
          exact ⟨by simp [h1], h2⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hie.2 j₁ j₂ hk
          exact ⟨by simp [h1], h2, by simp [h3], h4⟩
      · intro j' h
        have ho := hnoneOwned j' h
        refine Or.inr ⟨by simp [ho], ?_⟩
        have hc := (claimed_iff D j').mp (ExpansionData.claimed_of_conditions hD j')
        rw [ho] at hc
        exact hc
      · exact marker_contracted
      · intro hk; exact ⟨rfl, hk, by simp [ht, hb]⟩
      · intro v _; exact Or.inl ⟨rfl, by simp [ht, hb]⟩
    exact ⟨_, e, hcond, rfl, by simp, by simp⟩
  · -- A2: `b` is the head of `e`; the new slot is the zero piece.
    have hcond : (refine D e id id w (D.kind e) .contracted (fun j ↦ (D.owner j).castSucc)
        D.side).Conditions C := by
      refine refine_conditions hD Function.injective_id (fun _ _ ↦ ⟨rfl, rfl⟩)
        (fun j _ ↦ ⟨rfl, rfl⟩) ?_ ?_ ?_ ?_ ?_ hμold hhead hmk ?_
        (ExpansionData.incident_of_conditions hD) ?_ ?_
      · rw [hh, hb] at hce; exact hce
      · exact compat_contracted (by simp [hh, hb])
      · refine ⟨fun j hk ↦ ?_, fun j₁ j₂ hk ↦ ?_⟩
        · obtain ⟨h1, h2⟩ := hie.1 j hk
          exact ⟨by simp [h1], h2⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hie.2 j₁ j₂ hk
          exact ⟨by simp [h1], h2, by simp [h3], h4⟩
      · exact indexed_contracted
      · intro j' h
        have ho := hnoneOwned j' h
        refine Or.inl ⟨by simp [ho], ?_⟩
        have hc := (claimed_iff D j').mp (ExpansionData.claimed_of_conditions hD j')
        rw [ho] at hc
        exact hc
      · exact marker_contracted
      · intro hk
        refine ⟨hk, rfl, ?_⟩
        have := hce.1 hk
        simp only [id]
        rw [this, hh, hb]
      · intro v _; exact Or.inr ⟨rfl, by simp [hh, hb]⟩
    exact ⟨_, e, hcond, rfl, by simp, by simp⟩

end CaseA

/-! ## 5.  Case B: a mark at a bivalent marker -/

section CaseB

variable {D : ExpansionData n p N Q} {C : Core n p}

/-- A small core vertex over which no big vertex lies is the marker of a `double`. -/
theorem exists_double_of_not_mem (hD : D.Conditions C) (w : Fin n) (hw : ∀ v, D.fib v ≠ w) :
    ∃ (e : Fin Q) (j₁ j₂ : Fin p), D.kind e = .double j₁ j₂ ∧ C.head j₁ = w := by
  obtain ⟨j, hj⟩ := ExpansionData.incident_of_conditions hD w
  have hc := (compat_iff D C (D.owner j)).mp
    (ExpansionData.compatible_of_conditions hD (D.owner j))
  rcases ExpansionData.exists_carrier hD j with ⟨hk, -⟩ | ⟨j₂, hk, -⟩ | ⟨j₁, hk, -⟩
  · obtain ⟨h1, h2⟩ := hc.2.1 j hk
    rcases hj with hj | hj
    · exact absurd (h1.trans hj) (hw _)
    · exact absurd (h2.trans hj) (hw _)
  · obtain ⟨h1, -, -⟩ := hc.2.2 j j₂ hk
    rcases hj with hj | hj
    · exact absurd (h1.trans hj) (hw _)
    · exact ⟨D.owner j, j, j₂, hk, hj⟩
  · obtain ⟨-, h2, h3⟩ := hc.2.2 j₁ j hk
    rcases hj with hj | hj
    · exact ⟨D.owner j, j₁, j, hk, h2.trans hj⟩
    · exact absurd (h3.trans hj) (hw _)

/-- **Case B** (§6.2, a mark at a loop marker). The `double` through the marker is split
there into two `single`s. -/
theorem caseB (hD : D.Conditions C) (w : Fin n) (hw : ∀ v, D.fib v ≠ w) :
    ∃ (D' : ExpansionData n p (N + 1) (Q + 1)) (e : Fin Q),
      D'.Conditions C ∧ D'.bigCore = subdivide D.bigCore e ∧ D'.fib (Fin.last N) = w ∧
        ∀ v, D'.fib v.castSucc = D.fib v := by
  classical
  obtain ⟨e, j₁, j₂, hk, hw₁⟩ := exists_double_of_not_mem hD w hw
  have hce := (compat_iff D C e).mp (ExpansionData.compatible_of_conditions hD e)
  obtain ⟨hc1, hc2, hc3⟩ := hce.2.2 j₁ j₂ hk
  obtain ⟨ho1, hs1, ho2, hs2⟩ := (ExpansionData.indexed_of_conditions hD e).2 j₁ j₂ hk
  have hne := double_ne hD hk
  have hme := ExpansionData.marker_of_conditions hD e j₁ j₂ hk
  let owner' : Fin p → Fin (Q + 1) :=
    fun j ↦ if j = j₂ then Fin.last Q else (D.owner j).castSucc
  let side' : Fin p → Bool := fun j ↦ if j = j₂ then false else D.side j
  have hown : ∀ j, D.owner j ≠ e → owner' (id j) = (D.owner j).castSucc ∧
      side' (id j) = D.side j := by
    intro j hj
    have hj2 : j ≠ j₂ := by rintro rfl; exact hj ho2
    simp [owner', side', hj2]
  have hcond : (refine D e id id w (.single j₁) (.single j₂) owner' side').Conditions C := by
    refine refine_conditions hD Function.injective_id (fun _ _ ↦ ⟨rfl, rfl⟩) hown ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ (ExpansionData.incident_of_conditions hD) ?_ ?_
    · exact compat_single hc1 hw₁.symm
    · exact compat_single (hw₁.symm.trans hc2) hc3
    · exact indexed_single (by simp [owner', hne, ho1]) (by simp [side', hne, hs1])
    · exact indexed_single (by simp [owner']) (by simp [side'])
    · intro j' h
      have ho : D.owner j' = e := by
        by_contra hne'
        exact h j' hne' rfl
      have hc := (claimed_iff D j').mp (ExpansionData.claimed_of_conditions hD j')
      rw [ho, hk] at hc
      rcases hc.2.2 j₁ j₂ rfl with ⟨-, h1⟩ | ⟨-, h2⟩
      · subst h1
        exact Or.inl ⟨by simp [owner', hne, ho1], claims_single (by simp [side', hne, hs1])⟩
      · subst h2
        exact Or.inr ⟨by simp [owner'], claims_single (by simp [side'])⟩
    · intro i a b' hi hka h
      have : a = j₁ := hme.2 a (h.symm.trans hw₁.symm)
      subst this
      exact hi ((owner_of_double₁ hD hka).symm.trans ho1)
    · exact fun i a b' _ hka ↦ (ExpansionData.marker_of_conditions hD i a b' hka).2
    · exact marker_single
    · exact marker_single
    · intro hk'; rw [hk] at hk'; cases hk'
    · intro v hv; exact absurd hv (hw v)
  exact ⟨_, e, hcond, rfl, by simp, by simp⟩

end CaseB


/-! ## 6.  Case C: a mark at an interior vertex of a small slot -/

section CaseC

open OneEdgeSplitRefinement (splitCore)

variable {D : ExpansionData n p N Q} (small : Spec n p)

theorem sc_tail_cs (j j₀ : Fin p) :
    (splitCore small j).tail j₀.castSucc = (small.core.tail j₀).castSucc := by
  simp [splitCore, OneEdgeSplitRefinement.oldVertex]

theorem sc_tail_last (j : Fin p) : (splitCore small j).tail (Fin.last p) = Fin.last n := by
  simp [splitCore, OneEdgeSplitRefinement.splitVertex]

theorem sc_head_cs (j j₀ : Fin p) :
    (splitCore small j).head j₀.castSucc =
      if j₀ = j then Fin.last n else (small.core.head j₀).castSucc := by
  simp [splitCore, OneEdgeSplitRefinement.oldVertex, OneEdgeSplitRefinement.splitVertex]

theorem sc_head_last (j : Fin p) :
    (splitCore small j).head (Fin.last p) = (small.core.head j).castSucc := by
  simp [splitCore, OneEdgeSplitRefinement.oldVertex]

theorem castSucc_ne_last {m : ℕ} (v : Fin m) : v.castSucc ≠ Fin.last m :=
  (Fin.castSucc_lt_last v).ne

/-- **Case C** (§6.2, a mark at a bivalent vertex of `G`).
The small slot `j` is split at the mark, and so is the big slot that owns it. -/
theorem caseC (hD : D.Conditions small.core) (j : Fin p) :
    ∃ (D' : ExpansionData (n + 1) (p + 1) (N + 1) (Q + 1)) (e : Fin Q),
      D'.Conditions (splitCore small j) ∧ D'.bigCore = subdivide D.bigCore e ∧
        D'.fib (Fin.last N) = Fin.last n ∧ ∀ v, D'.fib v.castSucc = (D.fib v).castSucc := by
  classical
  set C := small.core with hC
  set e := D.owner j with he
  have hι : Function.Injective (Fin.castSucc : Fin n → Fin (n + 1)) := Fin.castSucc_injective n
  have hmor : ∀ j₀, D.owner j₀ ≠ e →
      (splitCore small j).tail j₀.castSucc = (C.tail j₀).castSucc ∧
        (splitCore small j).head j₀.castSucc = (C.head j₀).castSucc := by
    intro j₀ hj₀
    have hne : j₀ ≠ j := by rintro rfl; exact hj₀ rfl
    rw [sc_tail_cs, sc_head_cs, ite_eq_right hne]
    exact ⟨rfl, rfl⟩
  have hμold : ∀ i j₁ j₂, i ≠ e → D.kind i = .double j₁ j₂ →
      Fin.last n ≠ (C.head j₁).castSucc := fun _ _ _ _ _ h ↦ castSucc_ne_last _ h.symm
  have hhead : ∀ i j₁ j₂, i ≠ e → D.kind i = .double j₁ j₂ →
      ∀ j', (splitCore small j).head j' = (C.head j₁).castSucc → j' = j₁.castSucc := by
    intro i j₁ j₂ hi hk j'
    have hmk := ExpansionData.marker_of_conditions hD i j₁ j₂ hk
    refine Fin.lastCases ?_ (fun j₀ ↦ ?_) j'
    · intro h
      rw [sc_head_last] at h
      have hj := hmk.2 j (Fin.castSucc_injective n h)
      exact absurd ((owner_of_double₁ hD hk).symm.trans (by rw [← hj])) hi
    · intro h
      rw [sc_head_cs] at h
      split_ifs at h with hj₀
      · exact absurd h.symm (castSucc_ne_last _)
      · rw [hmk.2 j₀ (Fin.castSucc_injective n h)]
  have hinc : ∀ w', ∃ j', (splitCore small j).tail j' = w' ∨ (splitCore small j).head j' = w' := by
    intro w'
    refine Fin.lastCases ⟨j.castSucc, Or.inr (by rw [sc_head_cs, ite_eq_left rfl])⟩
      (fun w ↦ ?_) w'
    obtain ⟨j₀, hj₀⟩ := ExpansionData.incident_of_conditions hD w
    by_cases hjj : j₀ = j
    · subst hjj
      rcases hj₀ with h | h
      · exact ⟨j₀.castSucc, Or.inl (by rw [sc_tail_cs, h])⟩
      · exact ⟨Fin.last p, Or.inr (by rw [sc_head_last, h])⟩
    · rcases hj₀ with h | h
      · exact ⟨j₀.castSucc, Or.inl (by rw [sc_tail_cs, h])⟩
      · exact ⟨j₀.castSucc, Or.inr (by rw [sc_head_cs, ite_eq_right hjj, h])⟩
  have hnc : D.kind e ≠ .contracted := (ExpansionData.claimed_of_conditions hD j).1
  have hμ : ∀ v, (D.fib v).castSucc ≠ Fin.last n := fun v ↦ castSucc_ne_last _
  have hce := (compat_iff D C e).mp (ExpansionData.compatible_of_conditions hD e)
  have howned : ∀ j₀ : Fin p, (∀ j₁, D.owner j₁ ≠ e → j₀.castSucc ≠ j₁.castSucc) →
      D.owner j₀ = e := by
    intro j₀ h
    by_contra hne
    exact h j₀ hne rfl
  rcases ExpansionData.exists_carrier hD j with ⟨hk, hs⟩ | ⟨j₂, hk, hs⟩ | ⟨j₁, hk, hs⟩
  · -- C1: the owner is `single j`.
    obtain ⟨h1, h2⟩ := hce.2.1 j hk
    have hcond : (refine D e Fin.castSucc Fin.castSucc (Fin.last n) (.single j.castSucc)
        (.single (Fin.last p)) (Fin.lastCases (Fin.last Q) fun j₀ ↦ (D.owner j₀).castSucc)
        (Fin.lastCases false D.side)).Conditions (splitCore small j) := by
      refine refine_conditions hD hι hmor (fun j₀ _ ↦ ⟨by simp, by simp⟩) ?_ ?_ ?_ ?_ ?_ hμold
        hhead marker_single marker_single hinc (fun h ↦ absurd h hnc)
        (fun v hv ↦ absurd hv (hμ v))
      · exact compat_single (by rw [sc_tail_cs, h1]) (by rw [sc_head_cs, ite_eq_left rfl])
      · exact compat_single (by rw [sc_tail_last]) (by rw [sc_head_last, h2])
      · exact indexed_single (by simp [he]) (by simpa using hs)
      · exact indexed_single (by simp) (by simp)
      · intro j'
        refine Fin.lastCases (fun _ ↦ Or.inr ⟨by simp, claims_single (by simp)⟩)
          (fun j₀ h ↦ ?_) j'
        rcases owner_carries hD j j₀ (howned j₀ h) with ⟨-, rfl⟩ | ⟨j₂, hk', -⟩ | ⟨j₁, hk', -⟩
        · exact Or.inl ⟨by simp [he], claims_single (by simpa using hs)⟩
        · rw [hk] at hk'; cases hk'
        · rw [hk] at hk'; cases hk'
    exact ⟨_, e, hcond, rfl, by simp, by simp⟩
  · -- C2: the owner is `double j j₂`; the mark is inside the first half.
    obtain ⟨h1, h2, h3⟩ := hce.2.2 j j₂ hk
    have hne := double_ne hD hk
    have hs2 := ((ExpansionData.indexed_of_conditions hD e).2 j j₂ hk).2.2.2
    have ho2 := owner_of_double₂ hD hk
    have hmk := ExpansionData.marker_of_conditions hD e j j₂ hk
    have hcond : (refine D e Fin.castSucc Fin.castSucc (Fin.last n) (.single j.castSucc)
        (.double (Fin.last p) j₂.castSucc)
        (Fin.lastCases (Fin.last Q) fun j₀ ↦
          if j₀ = j₂ then Fin.last Q else (D.owner j₀).castSucc)
        (Fin.lastCases false D.side)).Conditions (splitCore small j) := by
      refine refine_conditions hD hι hmor ?_ ?_ ?_ ?_ ?_ ?_ hμold hhead marker_single ?_ hinc
        (fun h ↦ absurd h hnc) (fun v hv ↦ absurd hv (hμ v))
      · intro j₀ hj₀
        have : j₀ ≠ j₂ := by rintro rfl; exact hj₀ ho2
        exact ⟨by simp [this], by simp⟩
      · exact compat_single (by rw [sc_tail_cs, h1]) (by rw [sc_head_cs, ite_eq_left rfl])
      · exact compat_double (by rw [sc_tail_last]) (by rw [sc_head_last, sc_tail_cs, h2])
          (by rw [sc_head_cs, ite_eq_right hne.symm, h3])
      · exact indexed_single (by simp [he, hne]) (by simpa using hs)
      · exact indexed_double (by simp) (by simp) (by simp) (by simpa using hs2)
      · intro j'
        refine Fin.lastCases (fun _ ↦ Or.inr ⟨by simp, claims_double₁ (by simp)⟩)
          (fun j₀ h ↦ ?_) j'
        rcases owner_carries hD j j₀ (howned j₀ h) with ⟨hk', -⟩ | ⟨j₂', hk', hj₀⟩ |
            ⟨j₁', hk', -⟩
        · rw [hk] at hk'; cases hk'
        · rw [hk] at hk'
          cases hk'
          rcases hj₀ with rfl | rfl
          · exact Or.inl ⟨by simp [he, hne], claims_single (by simpa using hs)⟩
          · exact Or.inr ⟨by simp, claims_double₂ (by simpa using hs2)⟩
        · rw [hk] at hk'
          obtain ⟨-, rfl⟩ := SlotKind.double.inj hk'
          exact absurd rfl hne
      · refine marker_double (fun v h ↦ ?_) (fun h ↦ ?_) (fun j' ↦ ?_)
        · rw [sc_head_last] at h
          exact hmk.1 v (Fin.castSucc_injective n h)
        · rw [sc_head_last] at h
          exact castSucc_ne_last _ h.symm
        · refine Fin.lastCases (fun _ ↦ rfl) (fun j₀ h ↦ ?_) j'
          rw [sc_head_cs, sc_head_last] at h
          split_ifs at h with hj₀
          · exact absurd h (castSucc_ne_last _).symm
          · exact absurd (hmk.2 j₀ (Fin.castSucc_injective n h)) hj₀
    exact ⟨_, e, hcond, rfl, by simp, by simp⟩
  · -- C3: the owner is `double j₁ j`; the mark is inside the second half.
    obtain ⟨h1, h2, h3⟩ := hce.2.2 j₁ j hk
    have hne := double_ne hD hk
    have hs1 := ((ExpansionData.indexed_of_conditions hD e).2 j₁ j hk).2.1
    have ho1 := owner_of_double₁ hD hk
    have hmk := ExpansionData.marker_of_conditions hD e j₁ j hk
    have hcond : (refine D e Fin.castSucc Fin.castSucc (Fin.last n)
        (.double j₁.castSucc j.castSucc) (.single (Fin.last p))
        (Fin.lastCases (Fin.last Q) fun j₀ ↦ (D.owner j₀).castSucc)
        (Fin.lastCases false D.side)).Conditions (splitCore small j) := by
      refine refine_conditions hD hι hmor (fun j₀ _ ↦ ⟨by simp, by simp⟩) ?_ ?_ ?_ ?_ ?_ hμold
        hhead ?_ marker_single hinc (fun h ↦ absurd h hnc) (fun v hv ↦ absurd hv (hμ v))
      · exact compat_double (by rw [sc_tail_cs, h1]) (by rw [sc_head_cs, ite_eq_right hne, sc_tail_cs, h2])
          (by rw [sc_head_cs, ite_eq_left rfl])
      · exact compat_single (by rw [sc_tail_last]) (by rw [sc_head_last, h3])
      · exact indexed_double (by simp [ho1, he]) (by simpa using hs1) (by simp [he])
          (by simpa using hs)
      · exact indexed_single (by simp) (by simp)
      · intro j'
        refine Fin.lastCases (fun _ ↦ Or.inr ⟨by simp, claims_single (by simp)⟩)
          (fun j₀ h ↦ ?_) j'
        rcases owner_carries hD j j₀ (howned j₀ h) with ⟨hk', -⟩ | ⟨j₂', hk', -⟩ |
            ⟨j₁', hk', hj₀⟩
        · rw [hk] at hk'; cases hk'
        · rw [hk] at hk'
          obtain ⟨rfl, -⟩ := SlotKind.double.inj hk'
          exact absurd rfl hne
        · rw [hk] at hk'
          cases hk'
          rcases hj₀ with rfl | rfl
          · exact Or.inl ⟨by simp [ho1, he], claims_double₁ (by simpa using hs1)⟩
          · exact Or.inl ⟨by simp [he], claims_double₂ (by simpa using hs)⟩
      · refine marker_double (fun v h ↦ ?_) (fun h ↦ ?_) (fun j' ↦ ?_)
        · rw [sc_head_cs, ite_eq_right hne] at h
          exact hmk.1 v (Fin.castSucc_injective n h)
        · rw [sc_head_cs, ite_eq_right hne] at h
          exact castSucc_ne_last _ h.symm
        · refine Fin.lastCases (fun h ↦ ?_) (fun j₀ h ↦ ?_) j'
          · rw [sc_head_last, sc_head_cs, ite_eq_right hne] at h
            exact absurd (hmk.2 j (Fin.castSucc_injective n h)).symm hne
          · rw [sc_head_cs, sc_head_cs, ite_eq_right hne] at h
            split_ifs at h with hj₀
            · exact absurd h (castSucc_ne_last _).symm
            · rw [hmk.2 j₀ (Fin.castSucc_injective n h)]
    exact ⟨_, e, hcond, rfl, by simp, by simp⟩

end CaseC


/-! ## 7.  One mark -/

/-- **One mark.** For every vertex `x` of the subdivided small graph, the big core can be
subdivided at one slot, and the small specification split if `x` is an interior vertex, so that
the new big vertex lies over a small core vertex `w'` which the Laplacian equivalence `χ` sends to
`x`. Old small core vertices are carried along `ι`, and `χ` fixes them. -/
theorem exists_markStep (small : Spec n p) (D : ExpansionData n p N Q)
    (hD : D.Conditions small.core)
    (hInc : ∀ v : Fin N, ∃ i, D.bigCore.tail i = v ∨ D.bigCore.head i = v)
    (x : small.Vertex) :
    ∃ (n' p' : ℕ) (small' : Spec n' p') (D' : ExpansionData n' p' (N + 1) (Q + 1))
      (e : Fin Q) (ι : Fin n → Fin n') (w' : Fin n')
      (χ : LaplacianEquiv small'.graph small.graph),
      D'.Conditions small'.core ∧ D'.bigCore = subdivide D.bigCore e ∧
        (∀ v : Fin (N + 1), ∃ i, D'.bigCore.tail i = v ∨ D'.bigCore.head i = v) ∧
        D'.fib (Fin.last N) = w' ∧ (∀ v, D'.fib v.castSucc = ι (D.fib v)) ∧
        χ (small'.coreVertex w') = x ∧
        ∀ v, χ (small'.coreVertex (ι v)) = small.coreVertex v := by
  classical
  rcases x with w | ⟨j, o⟩
  · by_cases hw : ∃ b, D.fib b = w
    · obtain ⟨b, hb⟩ := hw
      obtain ⟨D', e, h1, h2, h3, h4⟩ := caseA hD hInc w b hb
      refine ⟨n, p, small, D', e, id, w, ⟨Equiv.refl _, fun _ _ ↦ rfl⟩, h1, h2, ?_, h3, h4, rfl,
        fun _ ↦ rfl⟩
      rw [h2]
      exact refine_incident D e hInc
    · push Not at hw
      obtain ⟨D', e, h1, h2, h3, h4⟩ := caseB hD w hw
      refine ⟨n, p, small, D', e, id, w, ⟨Equiv.refl _, fun _ _ ↦ rfl⟩, h1, h2, ?_, h3, h4, rfl,
        fun _ ↦ rfl⟩
      rw [h2]
      exact refine_incident D e hInc
  · obtain ⟨D', e, h1, h2, h3, h4⟩ := caseC small hD j
    have hlt := o.isLt
    have ha : 0 < o.val + 1 := Nat.succ_pos _
    have hb : 0 < small.length j - (o.val + 1) := by omega
    have hL : small.length j = (o.val + 1) + (small.length j - (o.val + 1)) := by omega
    refine ⟨n + 1, p + 1, OneEdgeSplitRefinement.splitSpec small j _ _ ha hb, D', e,
      Fin.castSucc, Fin.last n,
      (OneEdgeSplitRefinement.canonicalSplitLaplacianEquiv small j _ _ ha hb hL).symm,
      h1, h2, ?_, h3, h4, ?_, ?_⟩
    · rw [h2]
      exact refine_incident D e hInc
    · show (OneEdgeSplitRefinement.canonicalSplitVertexEquiv small j _ _ ha hb hL).symm _ = _
      rw [Equiv.symm_apply_eq]
      exact (OneEdgeSplitRefinement.canonicalSplitVertexEquiv_splitInterior_at small j _ _ ha hb
        hL o rfl).symm
    · intro v
      show (OneEdgeSplitRefinement.canonicalSplitVertexEquiv small j _ _ ha hb hL).symm _ = _
      rw [Equiv.symm_apply_eq]
      exact (OneEdgeSplitRefinement.canonicalSplitVertexEquiv_core small j _ _ ha hb hL v).symm

end GenusSixExistence.Tripod.MarkRefinement
