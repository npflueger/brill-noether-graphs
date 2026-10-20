module

public import DraismaVargasMarkedCount.MarkedCountGeneral.Agreement
public import DraismaVargasMarkedCount.MarkedCountGeneral.DropRelabel
public import DraismaVargasMarkedCount.MarkedCountGeneral.DropFrame
public import DraismaVargasCount.CoreRelabelInvariance

@[expose] public section

/-!
# Unramified marks (type 0): the drop lemma

The drop lemma extends to marks of every type the fact, used in the marked count at ramification
one, that an unramified mark is no condition.

**Unramified marks are kept in the core.** A mark of type `0` is an unramified mark kept in the
core: restriction at `j = a/2` leaves `u` in the core as an unramified mark (its image is a
divalent change-0 vertex, and `r = 0`), so typed frames allow type `0` (module `TypedFrame`) and the
decomposition (module `Correspondence`) lands in them directly. The count of a core with a type-`0`
mark is related to the count without it by **one** lemma, the drop of the last mark
(`typedCount_dropLast`): the core is `subdivide core s`, the dropped mark is the new
vertex, and the request is merged across it (`mergeRequest`). The other drops are corollaries:
the first mark of a twice-marked core by relabelling (`exists_twiceMarked_swap`,
`typedCount_relabel`, giving `typedCount_dropFirst`), and the last mark of a once-marked core by
`k = 0` (then `Agreement.typedCount_nil_eq_openMultCount` reaches the integer count).

**When `a` and `b` are both odd, nothing here is used**: every lower type `a - 2j`, `b - 2k` is
odd, hence positive (module `MarkedCountGeneral.MarkedCount`).

## The structure of the proof

`typedCount_dropLast` is proved from the six frame-level statements I1–I6 of
module `DropFrame` (the drop, its compatibility with isomorphisms, openness, the multiplicity, the
lift and its uniqueness), which rest on the denominator step
`DropSmooth.rowDenominator_split` (module `DenomDrop`) and the loop case
`DropSmooth.exists_loop_reversal` (module `DropUnique`) (module `LoopHairpin`). The bookkeeping (`snocMark`, `snocType`,
`mergeRequest`) is in module `DropBase`.

The other ingredients are `typeZero_image` (module `DropTypeZero`, the summand count),
`typedCount_relabel` (module `DropRelabel`) and `exists_twiceMarked_swap` (here, by the explicit
swap relabelling `swapRelabel`). `typedCount_dropFirst`, `typedCount_dropSecond` and
`typedCount_dropOnce` are proved from them and `typedCount_dropLast`.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.CoreRelabel (Relabel)
open GenusSixExistence.Tripod.Gadget (subdivide)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ}

/-! ## 2.  The image of an unramified mark -/

/-- **The image of a type-`0` mark is a divalent change-0 vertex** (the summand count of the
dimension formula with marks of types `aⱼ`, `Σ_x (ch(x) + val(x) - 3) = Σⱼ (aⱼ - 1)`). Every
summand is `≥ 0` except at a divalent change-0 vertex, which has two equal columns unless a mark
lies over it; a mark of type `aⱼ ≥ 1` contributes at least `aⱼ - 1` at its image; so each
type-`0` mark sits over its own summand `-1`. Hence every source vertex over `x_v` has `r = 0`
(and surviving valency two). Used only by the drop lemma.

*Proof.* The dimension formula for a marked frame, from `MarkedFullDim.saturated` and Part I's
dimension count, with the marked rows in place of the stable paths; then a case analysis of the
summands, vertex by vertex: module `DropTypeZero`, `typeZero_image'` (which also shows that no other
mark lies over the image). -/
theorem typeZero_image {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
    (hc : IsMarkedCubic core mark) (κ : TypedFrame core mark types degree) (j : Fin k)
    (hj : types j = 0) :
    (GluingDatum.incidentEdges (κ.markSource j).1.1).card = 2 ∧
      ∀ X : κ.data.SourceVertex, X.1.1 = (κ.markSource j).1.1 → markRamification κ.data X = 0 := by
  obtain ⟨hDivalent, -, hZero, -⟩ := typeZero_image' hc κ j hj
  exact ⟨hDivalent, hZero⟩

/-! ## 3.  The drop of the last mark -/

/-- **The drop lemma**: dropping an unramified mark. On `subdivide core s`,
whose last mark (the new vertex `v`) has type `0`, the typed count equals the count on `core` at
the merged request, the other marks and types unchanged.

*Proof sketch.* *Drop* (members over `(core, v)` to members over `core`): the image
`x_v` is a divalent change-0 vertex (`typeZero_image`), so every source vertex over it is a
valency-two `r = 0` vertex with one edge of equal index on each side; smooth `x_v` (contract one of
its two target edges, `GluingContraction.contractDatum`, whose join is the old partition), and
join the two marked rows through `v`. Coordinates: `z_{t'} + z_{t''}`, so openness is kept. The
determinant identity is a row-and-column operation on the marked matrix; the denominator `D` of
the joined row is the product of the two (Part II `proposition-at-most-two-weights`, read on the
regrowth `ψ^+` of `Regrowth` for `a ≥ 2`, the lollipop regrowth for `a = 1`). *Lift* (inverse): put
`v` back at its position on the row, inside a target edge, and subdivide that edge. `hGeneral` (no
frame of the subdivided core has a zero coordinate at `y`) gives the proviso of the drop lemma: if
`v` sat over a target vertex of a member over `core`, the lift with `v` on an adjacent edge would be
a frame with a zero coordinate. Positivity: `hPositive`.

*Proof.* An equivalence of the two fibres preserving `typedAbsMult`
(`finsum_comp_equiv`): a class over `sub` goes to the class of its drop (`dropFrame`, well
defined by `dropFrame_iso`, open by `openAt_dropFrame`, same multiplicity by
`typedAbsMult_dropFrame`); it is injective by `lift_unique` (through
`TypedFrameClass.mk_eq_mk_iff`) and surjective by `exists_lift`, which is where `hPositive` and
`hGeneral` enter. Two subtle points are inside those statements: the
denominator step (`D_κ = m · D_{drop κ}`, read on an unmarked caterpillar regrowth) is in
`typedAbsMult_dropFrame`, and the loop case (a loop slot gives two lifts, one per direction round
the loop, isomorphic through the hairpin's sheet swap) is in `lift_unique`. -/
theorem typedCount_dropLast {core : Core n p} {mark : Fin k → Fin n}
    (hc : IsMarkedCubic core mark) (types : Fin k → ℕ) (s : Fin p) {y : Fin (p + 1) → ℚ}
    (hPositive : ∀ i, 0 < y i)
    (hGeneral : ∀ (κ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree)
      (col : Fin (p + 1)), κ.coordsAt y col ≠ 0) :
    typedCount (subdivide core s) (snocMark mark) (snocType types 0) y degree =
      typedCount core mark types (mergeRequest s y) degree := by
  -- the drop on classes
  let G : TypedFrameClass (subdivide core s) (snocMark mark) (snocType types 0) degree →
      TypedFrameClass core mark types degree :=
    Quot.lift (fun κ ↦ TypedFrameClass.mk (dropFrame hc s κ)) fun _ _ h ↦
      h.elim fun iso ↦ TypedFrameClass.mk_eq_mk_of_iso (dropFrame_iso hc s iso)
  have hG : ∀ x : TypedFrameClass (subdivide core s) (snocMark mark) (snocType types 0) degree,
      x.OpenAt y → (G x).OpenAt (mergeRequest s y) := by
    intro x
    induction x using Quot.ind with
    | mk κ => exact openAt_dropFrame hc s κ
  have hMult : ∀ x : TypedFrameClass (subdivide core s) (snocMark mark) (snocType types 0) degree,
      (G x).typedAbsMult = x.typedAbsMult := by
    intro x
    induction x using Quot.ind with
    | mk κ => exact typedAbsMult_dropFrame hc s κ
  -- on fibres
  let F : TypedFibre (subdivide core s) (snocMark mark) (snocType types 0) y degree →
      TypedFibre core mark types (mergeRequest s y) degree := fun x ↦ ⟨G x.1, hG x.1 x.2⟩
  have hInjective : Function.Injective F := by
    rintro ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ hEq
    induction x₁ using Quot.ind with
    | mk κ₁ =>
      induction x₂ using Quot.ind with
      | mk κ₂ =>
        have hDrop : TypedFrameClass.mk (dropFrame hc s κ₁) =
            TypedFrameClass.mk (dropFrame hc s κ₂) := congrArg Subtype.val hEq
        obtain ⟨iso⟩ := TypedFrameClass.mk_eq_mk_iff.mp hDrop
        obtain ⟨iso'⟩ := lift_unique hc s h₁ h₂ iso
        exact Subtype.ext (TypedFrameClass.mk_eq_mk_of_iso ⟨iso'⟩)
  have hSurjective : Function.Surjective F := by
    rintro ⟨x, hx⟩
    induction x using Quot.ind with
    | mk κ =>
      obtain ⟨κ', hOpen', hIso⟩ := exists_lift hc s hPositive hGeneral κ hx
      exact ⟨⟨TypedFrameClass.mk κ', hOpen'⟩,
        Subtype.ext (TypedFrameClass.mk_eq_mk_of_iso hIso)⟩
  let e := Equiv.ofBijective F ⟨hInjective, hSurjective⟩
  unfold typedCount
  rw [← finsum_comp_equiv e]
  exact finsum_congr fun x ↦ (hMult x.1).symm

/-! ## 4.  Relabelling -/

/-- **Typed counts and genericity are relabelling invariants**: a relabelling of the core
carrying marks to marks (up to a permutation `σ` of the marks, with the types permuted along) and
requests to requests. *Proof sketch.* Compose `ident.vertex`, `ident.row` with
`r.vtx`, `r.slot` (`r.incidence` matches the incidences), keep the datum; the marked matrix is
unchanged, the slots are permuted (`coordsAt` is permuted accordingly), `(D4′)` is read at the same
source vertices. As `IntegerCount.openMultCount_relabel` / `CoreRelabel.relabelEquiv`.

*Proof.* `DropRelabel.typedCount_relabel'` (module `DropRelabel`). -/
theorem typedCount_relabel {c c' : Core n p} (r : Relabel c c') {mark mark' : Fin k → Fin n}
    (σ : Fin k ≃ Fin k) (hMark : ∀ j, r.vtx (mark j) = mark' (σ j)) {types types' : Fin k → ℕ}
    (hTypes : ∀ j, types' (σ j) = types j) {y y' : Fin p → ℚ} (hy : ∀ e, y' (r.slot e) = y e) :
    typedCount c mark types y degree = typedCount c' mark' types' y' degree ∧
      ((∀ (κ : TypedFrame c mark types degree) (col : Fin p), κ.coordsAt y col ≠ 0) →
        ∀ (κ' : TypedFrame c' mark' types' degree) (col : Fin p), κ'.coordsAt y' col ≠ 0) :=
  typedCount_relabel' r σ hMark hTypes hy

/-! ## 5.  The drop of the first mark of a twice-marked core -/

/-- The slot of `core` carrying `v` once `u` is dropped: `s₁` when `v` is on a piece of `s₁`,
otherwise `s₂` read in `core`. -/
def dropFirstSlot (s₁ : Fin p) (s₂ : Fin (p + 1)) : Fin p :=
  Fin.lastCases (motive := fun _ ↦ Fin p) s₁ (fun s ↦ s) s₂

/-- **The request on `subdivide core (dropFirstSlot s₁ s₂)`** once `u` is dropped: the two pieces
at `u` are joined. If `v` is on the piece `tail(s₁) → u` (`s₂ = s₁.castSucc`), they are the
pieces `v → u` and `u → head(s₁)`, i.e. the new second piece of `v`; otherwise they are
`tail(s₁) → u` and `u → head(s₁)` (or `u → v`), i.e. the slot `s₁` of `core`. -/
def dropFirstRequest (s₁ : Fin p) (s₂ : Fin (p + 1)) (y : Fin (p + 1 + 1) → ℚ) :
    Fin (p + 1) → ℚ :=
  Fin.lastCases (motive := fun _ ↦ ℚ)
    (y (Fin.last (p + 1)) + if s₂ = s₁.castSucc then y (Fin.last p).castSucc else 0)
    (fun i ↦ y i.castSucc.castSucc +
      if s₂ ≠ s₁.castSucc ∧ i = s₁ then y (Fin.last p).castSucc else 0)

theorem dropFirstRequest_pos {s₁ : Fin p} {s₂ : Fin (p + 1)} {y : Fin (p + 1 + 1) → ℚ}
    (hy : ∀ i, 0 < y i) (i : Fin (p + 1)) : 0 < dropFirstRequest s₁ s₂ y i := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simp only [dropFirstRequest, Fin.lastCases_last]
    split_ifs <;> linarith [hy (Fin.last (p + 1)), hy (Fin.last p).castSucc]
  · simp only [dropFirstRequest, Fin.lastCases_castSucc]
    split_ifs <;> linarith [hy i.castSucc.castSucc, hy (Fin.last p).castSucc]

/-- The slot of the swapped core carrying `u`: `last p` when `v`
is on the piece `tail(s₁) → u`, otherwise the piece `s₁.castSucc` of `subdivide core s₁'`. -/
def swapSecondSlot (s₁ : Fin p) (s₂ : Fin (p + 1)) : Fin (p + 1) :=
  if s₂ = s₁.castSucc then Fin.last p else s₁.castSucc

/-- The slot map of the swap: the two new slots `cs(last p)` and `last (p + 1)` are exchanged,
the others fixed. -/
def swapSlot (p : ℕ) : Fin (p + 1 + 1) ≃ Fin (p + 1 + 1) :=
  Equiv.swap (Fin.last p).castSucc (Fin.last (p + 1))

/-- The vertex map of the swap: the two new vertices are exchanged. -/
def swapVtx (n : ℕ) : Fin (n + 1 + 1) ≃ Fin (n + 1 + 1) :=
  Equiv.swap (Fin.last n).castSucc (Fin.last (n + 1))

theorem swapSlot_castSucc_castSucc (i : Fin p) :
    swapSlot p i.castSucc.castSucc = i.castSucc.castSucc :=
  Equiv.swap_apply_of_ne_of_ne
    (fun h ↦ (Fin.castSucc_lt_last i).ne (Fin.castSucc_injective _ h))
    (Fin.castSucc_lt_last _).ne

theorem swapSlot_castSucc_last : swapSlot p (Fin.last p).castSucc = Fin.last (p + 1) :=
  Equiv.swap_apply_left _ _

theorem swapSlot_last : swapSlot p (Fin.last (p + 1)) = (Fin.last p).castSucc :=
  Equiv.swap_apply_right _ _

theorem swapVtx_castSucc_castSucc (v : Fin n) :
    swapVtx n v.castSucc.castSucc = v.castSucc.castSucc :=
  Equiv.swap_apply_of_ne_of_ne
    (fun h ↦ (Fin.castSucc_lt_last v).ne (Fin.castSucc_injective _ h))
    (Fin.castSucc_lt_last _).ne

theorem swapVtx_castSucc_last : swapVtx n (Fin.last n).castSucc = Fin.last (n + 1) :=
  Equiv.swap_apply_left _ _

theorem swapVtx_last : swapVtx n (Fin.last (n + 1)) = (Fin.last n).castSucc :=
  Equiv.swap_apply_right _ _

/-- **The swap preserves tails and heads** (orientation included), in each of the three
placements of `v`. -/
theorem swap_tail_head (core : Core n p) (s₁ : Fin p) (s₂ : Fin (p + 1)) (e : Fin (p + 1 + 1)) :
    (twiceMarked core (dropFirstSlot s₁ s₂) (swapSecondSlot s₁ s₂)).tail (swapSlot p e) =
        swapVtx n ((twiceMarked core s₁ s₂).tail e) ∧
      (twiceMarked core (dropFirstSlot s₁ s₂) (swapSecondSlot s₁ s₂)).head (swapSlot p e) =
        swapVtx n ((twiceMarked core s₁ s₂).head e) := by
  have hne : ∀ i : Fin p, i.castSucc ≠ Fin.last p := fun i ↦ (Fin.castSucc_lt_last i).ne
  have hne' : ∀ i : Fin p, Fin.last p ≠ i.castSucc := fun i ↦ (hne i).symm
  induction e using Fin.lastCases with
  | last =>
    rw [swapSlot_last]
    induction s₂ using Fin.lastCases with
    | last =>
      simp [twiceMarked, dropFirstSlot, swapSecondSlot, hne', swapVtx_last,
        swapVtx_castSucc_castSucc]
    | cast s =>
      by_cases hs : s = s₁
      · subst hs
        simp [twiceMarked, dropFirstSlot, swapSecondSlot, swapVtx_last,
          swapVtx_castSucc_last]
      · simp [twiceMarked, dropFirstSlot, swapSecondSlot, hne', hs,
          swapVtx_last, swapVtx_castSucc_castSucc]
  | cast e =>
    induction e using Fin.lastCases with
    | last =>
      rw [swapSlot_castSucc_last]
      induction s₂ using Fin.lastCases with
      | last =>
        simp [twiceMarked, dropFirstSlot, swapSecondSlot, hne', swapVtx_last,
          swapVtx_castSucc_last]
      | cast s =>
        by_cases hs : s = s₁
        · subst hs
          simp [twiceMarked, dropFirstSlot, swapSecondSlot, hne',
            swapVtx_castSucc_last, swapVtx_castSucc_castSucc]
        · simp [twiceMarked, dropFirstSlot, swapSecondSlot, hne', hs, Ne.symm hs,
            swapVtx_castSucc_last, swapVtx_castSucc_castSucc]
    | cast i =>
      rw [swapSlot_castSucc_castSucc]
      induction s₂ using Fin.lastCases with
      | last =>
        by_cases hi : i = s₁
        · subst hi
          simp [twiceMarked, dropFirstSlot, swapSecondSlot, hne, hne',
            swapVtx_castSucc_last, swapVtx_castSucc_castSucc]
        · simp [twiceMarked, dropFirstSlot, swapSecondSlot, hne, hne', hi,
            swapVtx_castSucc_castSucc]
      | cast s =>
        by_cases hs : s = s₁
        · subst hs
          by_cases hi : i = s
          · subst hi
            simp [twiceMarked, dropFirstSlot, swapSecondSlot, hne, swapVtx_last,
              swapVtx_castSucc_castSucc]
          · simp [twiceMarked, dropFirstSlot, swapSecondSlot, hne, hi,
              swapVtx_castSucc_castSucc]
        · by_cases hi : i = s₁
          · subst hi
            simp [twiceMarked, dropFirstSlot, swapSecondSlot, hs, Ne.symm hs,
              swapVtx_castSucc_last, swapVtx_castSucc_castSucc]
          · by_cases his : i = s
            · subst his
              simp [twiceMarked, dropFirstSlot, swapSecondSlot, hs,
                swapVtx_last, swapVtx_castSucc_castSucc]
            · simp [twiceMarked, dropFirstSlot, swapSecondSlot, hs, hi, his,
                swapVtx_castSucc_castSucc]

/-- **The swap relabelling.** -/
def swapRelabel (core : Core n p) (s₁ : Fin p) (s₂ : Fin (p + 1)) :
    Relabel (twiceMarked core s₁ s₂)
      (twiceMarked core (dropFirstSlot s₁ s₂) (swapSecondSlot s₁ s₂)) where
  slot := swapSlot p
  vtx := swapVtx n
  incidence v e := by
    obtain ⟨hTail, hHead⟩ := swap_tail_head core s₁ s₂ e
    rw [coreIncidence, coreIncidence, hTail, hHead]
    simp only [Equiv.apply_eq_iff_eq]

/-- **The two subdivisions commute**: `twiceMarked core s₁ s₂` is `twiceMarked core s₁' s₂'` with
the marks swapped, where `s₁' = dropFirstSlot s₁ s₂` carries `v`, and merging the pieces of the
new last mark (`u`) is `dropFirstRequest`. *Proof* (`swapRelabel`, `swap_tail_head`). Three
cases: `s₂ = s.castSucc` with `s ≠ s₁` (then `s₂' = s₁.castSucc`), `s₂ = s₁.castSucc` (then
`s₂' = last p`), `s₂ = last p` (then `s₂' = s₁.castSucc`). In each, the relabelling swaps the two
new vertices and the two new slots `(last p).castSucc` and `last (p + 1)`; this is checked
here case by case against `subdivide`'s convention. -/
theorem exists_twiceMarked_swap (core : Core n p) (s₁ : Fin p) (s₂ : Fin (p + 1)) :
    ∃ (s₂' : Fin (p + 1))
      (r : Relabel (twiceMarked core s₁ s₂) (twiceMarked core (dropFirstSlot s₁ s₂) s₂')),
      (∀ j, r.vtx (twiceMark n j) = twiceMark n (Equiv.swap 0 1 j)) ∧
        ∀ y : Fin (p + 1 + 1) → ℚ,
          mergeRequest s₂' (fun e ↦ y (r.slot.symm e)) = dropFirstRequest s₁ s₂ y := by
  have hne : ∀ i : Fin p, i.castSucc ≠ Fin.last p := fun i ↦ (Fin.castSucc_lt_last i).ne
  have hne' : ∀ i : Fin p, Fin.last p ≠ i.castSucc := fun i ↦ (hne i).symm
  have hSymm : (swapSlot p).symm = swapSlot p := Equiv.symm_swap _ _
  refine ⟨swapSecondSlot s₁ s₂, swapRelabel core s₁ s₂, fun j ↦ ?_, fun y ↦ ?_⟩
  · fin_cases j
    · exact swapVtx_castSucc_last
    · exact swapVtx_last
  · change mergeRequest _ (fun e ↦ y ((swapSlot p).symm e)) = _
    rw [hSymm]
    funext i
    induction i using Fin.lastCases with
    | last =>
      induction s₂ using Fin.lastCases with
      | last => simp [mergeRequest, dropFirstRequest, swapSecondSlot, hne', swapSlot_castSucc_last]
      | cast s =>
        by_cases hs : s = s₁
        · subst hs
          simp [mergeRequest, dropFirstRequest, swapSecondSlot, swapSlot_castSucc_last,
            swapSlot_last]
        · simp [mergeRequest, dropFirstRequest, swapSecondSlot, hs, hne', swapSlot_castSucc_last]
    | cast i =>
      induction s₂ using Fin.lastCases with
      | last =>
        simp [mergeRequest, dropFirstRequest, swapSecondSlot, hne', swapSlot_castSucc_castSucc,
          swapSlot_last]
      | cast s =>
        by_cases hs : s = s₁
        · subst hs
          simp [mergeRequest, dropFirstRequest, swapSecondSlot, hne, swapSlot_castSucc_castSucc]
        · simp [mergeRequest, dropFirstRequest, swapSecondSlot, hs, swapSlot_castSucc_castSucc,
            swapSlot_last]

/-- **Dropping the first mark of a twice-marked core** (the drop lemma at `u`): by the swap, the
relabelling invariance and `typedCount_dropLast`. -/
theorem typedCount_dropFirst {core : Core n p} (hCubic : core.Cubic) (s₁ : Fin p)
    (s₂ : Fin (p + 1)) (b : ℕ) {y : Fin (p + 1 + 1) → ℚ} (hPositive : ∀ i, 0 < y i)
    (hGeneral : ∀ (κ : TypedFrame (twiceMarked core s₁ s₂) (twiceMark n) ![0, b] degree)
      (col : Fin (p + 1 + 1)), κ.coordsAt y col ≠ 0) :
    typedCount (twiceMarked core s₁ s₂) (twiceMark n) ![0, b] y degree =
      typedCount (subdivide core (dropFirstSlot s₁ s₂)) (onceMark n) ![b]
        (dropFirstRequest s₁ s₂ y) degree := by
  obtain ⟨s₂', r, hMark, hReq⟩ := exists_twiceMarked_swap core s₁ s₂
  have hTypes : ∀ j, (![b, 0] : Fin 2 → ℕ) (Equiv.swap 0 1 j) = (![0, b] : Fin 2 → ℕ) j := by
    intro j; fin_cases j <;> rfl
  have hy : ∀ e, (fun e ↦ y (r.slot.symm e)) (r.slot e) = y e := fun e ↦ by simp
  obtain ⟨hCount, hGen⟩ := typedCount_relabel (degree := degree) (y := y)
    (y' := fun e ↦ y (r.slot.symm e)) r (Equiv.swap 0 1) hMark hTypes hy
  rw [hCount, ← hReq]
  have hPos' : ∀ i, 0 < (fun e ↦ y (r.slot.symm e)) i := fun i ↦ hPositive _
  have hc := isMarkedCubic_onceMarked hCubic (dropFirstSlot s₁ s₂)
  have h := typedCount_dropLast (degree := degree) hc ![b] s₂' hPos'
  rw [← twiceMark_eq_snocMark, ← vecTwo_eq_snocType] at h
  exact h (hGen hGeneral)

/-- **Dropping the last mark of a twice-marked core**: `typedCount_dropLast` at `onceMark`. -/
theorem typedCount_dropSecond {core : Core n p} (hCubic : core.Cubic) (s₁ : Fin p)
    (s₂ : Fin (p + 1)) (a : ℕ) {y : Fin (p + 1 + 1) → ℚ} (hPositive : ∀ i, 0 < y i)
    (hGeneral : ∀ (κ : TypedFrame (twiceMarked core s₁ s₂) (twiceMark n) ![a, 0] degree)
      (col : Fin (p + 1 + 1)), κ.coordsAt y col ≠ 0) :
    typedCount (twiceMarked core s₁ s₂) (twiceMark n) ![a, 0] y degree =
      typedCount (subdivide core s₁) (onceMark n) ![a] (mergeRequest s₂ y) degree := by
  have hc := isMarkedCubic_onceMarked hCubic s₁
  have h := typedCount_dropLast (degree := degree) hc ![a] s₂ hPositive
  rw [← twiceMark_eq_snocMark, ← vecTwo_eq_snocType] at h
  exact h hGeneral

/-- **Dropping the only mark of a once-marked core** reaches the weighted count of the integer
count: `typedCount_dropLast` at `k = 0`, then `typedCount_nil_eq_openMultCount`. -/
theorem typedCount_dropOnce {core : Core n p} (hCubic : core.Cubic) (s : Fin p)
    {y : Fin (p + 1) → ℚ} (hPositive : ∀ i, 0 < y i)
    (hGeneral : ∀ (κ : TypedFrame (subdivide core s) (onceMark n) ![0] degree)
      (col : Fin (p + 1)), κ.coordsAt y col ≠ 0) :
    typedCount (subdivide core s) (onceMark n) ![0] y degree =
      (IntegerCount.openMultCount core (mergeRequest s y) degree : ℚ) := by
  have hc : IsMarkedCubic core (Fin.elim0 : Fin 0 → Fin n) :=
    ⟨fun i ↦ i.elim0, fun j ↦ j.elim0, fun v _ ↦ hCubic v⟩
  have h := typedCount_dropLast (degree := degree) hc (Fin.elim0 : Fin 0 → ℕ) s hPositive
  rw [← onceMark_eq_snocMark, ← vecOne_eq_snocType] at h
  rw [h hGeneral, typedCount_nil_eq_openMultCount]

end DraismaVargas.Count.MarkedCountGeneral
