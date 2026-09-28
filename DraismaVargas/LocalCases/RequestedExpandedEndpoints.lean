import DraismaVargas.LocalCases.StableModelPackaging

/-!
# The requested metric on the expanded cubic model, with zero expansion rows

**Source.**  Draisma--Vargas Part I, the subsection *Proof of main result*: the
requested metric graph is written as `(H, y₁)` for a trivalent combinatorial
type `H` and a point `y₁` of the closed cone `\overline C_H`, a pair `(M, ℓ_T)`
being read as `(M₀, ℓ|T₀)`.  A non-trivalent requested type is thus presented
as a point of the **closed** cone of a trivalent type, i.e. with **zero** lengths
on exactly the edges that the contraction collapses.  Part I's convention for
the closed cone `\overline C_G` (subsection *Moduli space of metric graphs*)
says nothing about rational, integral or scaled lengths, and Part I contains no
proof of the exact integral-scale transport used here, so the integral
statements below are original to this formalization, adapted from the
closed-cone description.  The interface has the shape
`InputInterface (spec' : Spec n' p') (F : Finset (Fin p'))` with
`slot : Fin p' ≃ coordinate` and `matrixMap : mulVec coordinates = fun row ↦
if slot.symm row ∈ F then 0 else spec'.length (slot.symm row)`; the positive
interface `InputInterface spec` is the case `F = ∅`.

## What is proved

For an arbitrary connected requested specification — **not** only a cubic core —
the reduction to a cubic model (`exists_expansionModel` below) produces a small
representative `spec₀` and an
`Utilities.Subdivision.CoreExpansion.ExpansionData` whose `bigSpec` is the cubic
model.  This file builds the finish vector on that model's stable slots and
proves its four required properties.

1. **Slot by slot**:
   `expandedLength_slot_of_not_mem` on a retained slot, `expansionLength_single`
   and `expansionLength_double` naming which original integral lengths a
   retained cubic slot carries (one, or two in series through a marker), and
   `expandedLength_slot_of_mem` / `expansionLength_contracted` giving `0` on the
   expansion forest.  `le_expansionLength_owner` says every requested slot is
   carried by a retained row.
2. **Sign**: `expandedFinish_nonneg`, and positivity **exactly** off the
   expansion forest, `expandedFinish_pos_iff` and `expandedFinish_eq_zero_iff`.
3. **Scaling**:
   `expandedFinish_scale` in the abstract form, and `expansionLength_scale` /
   `expandedFinish_bigSpec_scale` in the form the expansion datum needs, where refining
   the **requested** specification `k`-fold multiplies the vector by `k` even
   though the cubic model's own contracted slots keep length one under
   `CoreExpansion.kindLength`.
4. **The interface**: `ExpandedInterface`, with `eq_zero_iff` proving its zero
   rows are precisely the expansion forest, `terminalExpandedInterface` the
   interface at a terminal state of the march, and — at a cleared face —
   `sourceLength_eq_zero_of_mem`:
   **every source occurrence displayed by an expansion-forest row is contracted
   by the face**, while `exists_sourceLength_ne_zero_of_not_mem` shows no
   retained row is.  So the terminal face's zero-row contraction is that forest
   and nothing more.

`exists_expansionModel` re-runs the composite reduction of
`StableModelPackaging.exists_cubicModel` so that the expansion **datum itself**
is returned, not only the contraction certificate (`exists_cubicModel` binds it
existentially, so the expansion forest is not visible through it).
`exists_expandedFinish` packages the whole deliverable in one sentence for an
arbitrary connected request.

## Relation to `InputRefinementData.InputInterface`

`InputRefinementData.InputInterface` carries the forest as a fourth parameter
`(F : Finset (Fin p) := ∅)`, with `matrixMap : mulVec coordinates = fun row ↦
if slot.symm row ∈ F then 0 else spec.length (slot.symm row)`; its positive
instance `InputInterface spec presentation coordinates` is `F = ∅`.
Consequently `ofInputInterface` and `toInputInterface` below are **two-way maps
at every `F`**, `terminalForestInterface` supplies the terminal identification
with the general interface at the forest, and `inputInterface_pos` /
`eq_empty_of_inputInterface` are the statements *at the empty forest*,
recorded as the reason the positive interface has no zero row.

`ExpandedInterface` is kept as a separate structure — and not replaced by
`InputInterface` — because it is stated at a bare matrix, with no gluing datum
in sight, which is what lets `bananaInterface` inhabit it at a nonempty forest
with no candidate at all.

## What is not proved here, and stays an explicit hypothesis

* **No face, refinement or pencil is built from an `ExpandedInterface`.**  The
  general-`F` users `InputRefinementData.Retained.segmentData`,
  `Retained.refinedSpec` and `Retained.inputRefinement` take a
  `RetainedIndex` — a presentation of the retained slots as a specification in
  its own right — and `RetainedIndexProducer` produces one from the expansion
  datum.
* **The expansion forest is not proved acyclic here.**  `expansionForest` is
  the contracted-slot set of the datum; that it is a forest is the genus
  bookkeeping of `ExpansionData.certificate_topologicalValid` (see
  `ForestReceiptGeneral.exists_expansionModel_isForest`).
* The positive sublists of `OrientedTraversal` handle zero occurrences
  **within** positive-total rows, not whole zero rows.  Whole zero rows are what
  this file supplies, for the contraction at the terminal face and the terminal
  identification to use.

## Used by

The contraction of the zero forest at the terminal face, preserving the common
scale, followed by the transport back through the reduction
(`RetainedRelabeling`, `StatementFromLink`), and the terminal identification
(`TerminalIdentification.carriesCertifiedPencil_of_tracked_expanded`).  The
positive interface is the `F = ∅` instance.

## Non-vacuity

`bananaExpansion` is an explicit `ExpansionData 2 4 4 6`: the four-fold banana
expanded to a cubic core, with a **two-slot** expansion forest, all conditions
checked by evaluation.  `banana_expandedLength` computes the finish vector as
`![0, 0, 2, 3, 5, 7]` and `bananaInterface` inhabits `ExpandedInterface` at a
nonempty forest.
-/

namespace DraismaVargas.LocalCases.RequestedExpandedEndpoints

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion
open ExplicitPotential
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData

/-! ## 1.  The expanded endpoint vector -/

section Vector

variable {coordinate : Type*} {n p : ℕ}

/-- **The requested endpoint vector with zero expansion rows, integral form.**  The requested
length on a retained slot of the cubic model, and exactly `0` on every slot of
the expansion forest `F`.  This is `baseFinish`; it is not the target-edge
vector. -/
def expandedLength (spec : Spec n p) (F : Finset (Fin p))
    (slot : Fin p ≃ coordinate) : coordinate → ℕ :=
  fun row ↦ if slot.symm row ∈ F then 0 else spec.length (slot.symm row)

/-- The same vector over `ℚ`, the shape `FiniteAtlasMarch.State` consumes. -/
def expandedFinish (spec : Spec n p) (F : Finset (Fin p))
    (slot : Fin p ≃ coordinate) : coordinate → ℚ :=
  fun row ↦ ((expandedLength spec F slot row : ℕ) : ℚ)

theorem expandedFinish_apply (spec : Spec n p) (F : Finset (Fin p))
    (slot : Fin p ≃ coordinate) (row : coordinate) :
    expandedFinish spec F slot row = ((expandedLength spec F slot row : ℕ) : ℚ) := rfl

theorem expandedFinish_eq (spec : Spec n p) (F : Finset (Fin p))
    (slot : Fin p ≃ coordinate) :
    expandedFinish spec F slot = fun row ↦ ((expandedLength spec F slot row : ℕ) : ℚ) :=
  rfl

/-- **(i) Slot by slot on a retained slot.**  A slot outside the expansion forest
carries its own requested length. -/
@[simp] theorem expandedLength_slot_of_not_mem (spec : Spec n p)
    (F : Finset (Fin p)) (slot : Fin p ≃ coordinate) {i : Fin p} (hi : i ∉ F) :
    expandedLength spec F slot (slot i) = spec.length i := by
  simp [expandedLength, hi]

/-- **(i) Slot by slot on the expansion forest**: exactly zero. -/
@[simp] theorem expandedLength_slot_of_mem (spec : Spec n p)
    (F : Finset (Fin p)) (slot : Fin p ≃ coordinate) {i : Fin p} (hi : i ∈ F) :
    expandedLength spec F slot (slot i) = 0 := by
  simp [expandedLength, hi]

@[simp] theorem expandedFinish_slot_of_not_mem (spec : Spec n p)
    (F : Finset (Fin p)) (slot : Fin p ≃ coordinate) {i : Fin p} (hi : i ∉ F) :
    expandedFinish spec F slot (slot i) = (spec.length i : ℚ) := by
  rw [expandedFinish_apply, expandedLength_slot_of_not_mem spec F slot hi]

@[simp] theorem expandedFinish_slot_of_mem (spec : Spec n p)
    (F : Finset (Fin p)) (slot : Fin p ≃ coordinate) {i : Fin p} (hi : i ∈ F) :
    expandedFinish spec F slot (slot i) = 0 := by
  rw [expandedFinish_apply, expandedLength_slot_of_mem spec F slot hi]
  exact Nat.cast_zero

/-- The value on a retained row, read through the inverse labelling. -/
theorem expandedLength_of_not_mem (spec : Spec n p) (F : Finset (Fin p))
    (slot : Fin p ≃ coordinate) {row : coordinate} (hrow : slot.symm row ∉ F) :
    expandedLength spec F slot row = spec.length (slot.symm row) :=
  if_neg hrow

theorem expandedLength_of_mem (spec : Spec n p) (F : Finset (Fin p))
    (slot : Fin p ≃ coordinate) {row : coordinate} (hrow : slot.symm row ∈ F) :
    expandedLength spec F slot row = 0 :=
  if_pos hrow

/-- **(ii) The zero set is the expansion forest, on the nose.** -/
theorem expandedLength_eq_zero_iff (spec : Spec n p) (F : Finset (Fin p))
    (slot : Fin p ≃ coordinate) (row : coordinate) :
    expandedLength spec F slot row = 0 ↔ slot.symm row ∈ F := by
  by_cases hrow : slot.symm row ∈ F
  · simp [expandedLength_of_mem spec F slot hrow, hrow]
  · have hpos := spec.length_pos (slot.symm row)
    rw [expandedLength_of_not_mem spec F slot hrow]
    exact ⟨fun h ↦ absurd h (by omega), fun h ↦ absurd h hrow⟩

/-- **(ii) Positivity holds exactly off the expansion forest.** -/
theorem expandedLength_pos_iff (spec : Spec n p) (F : Finset (Fin p))
    (slot : Fin p ≃ coordinate) (row : coordinate) :
    0 < expandedLength spec F slot row ↔ slot.symm row ∉ F := by
  rw [Nat.pos_iff_ne_zero, ne_eq, expandedLength_eq_zero_iff]

/-- **(ii) Nonnegativity.** -/
theorem expandedFinish_nonneg (spec : Spec n p) (F : Finset (Fin p))
    (slot : Fin p ≃ coordinate) (row : coordinate) :
    0 ≤ expandedFinish spec F slot row := by
  rw [expandedFinish_apply]
  exact Nat.cast_nonneg _

theorem expandedFinish_eq_zero_iff (spec : Spec n p) (F : Finset (Fin p))
    (slot : Fin p ≃ coordinate) (row : coordinate) :
    expandedFinish spec F slot row = 0 ↔ slot.symm row ∈ F := by
  rw [expandedFinish_apply, Nat.cast_eq_zero, expandedLength_eq_zero_iff]

theorem expandedFinish_pos_iff (spec : Spec n p) (F : Finset (Fin p))
    (slot : Fin p ≃ coordinate) (row : coordinate) :
    0 < expandedFinish spec F slot row ↔ slot.symm row ∉ F := by
  rw [expandedFinish_apply]
  constructor
  · intro hpos
    have : 0 < expandedLength spec F slot row := by exact_mod_cast hpos
    exact (expandedLength_pos_iff spec F slot row).mp this
  · intro hrow
    have : 0 < expandedLength spec F slot row :=
      (expandedLength_pos_iff spec F slot row).mpr hrow
    exact_mod_cast this

/-- **(iii) Scaling, integral form.**  Refining every slot `k`-fold multiplies
the vector by `k`; the forest entries stay zero. -/
theorem expandedLength_scale (spec : Spec n p) (F : Finset (Fin p))
    (slot : Fin p ≃ coordinate) (k : ℕ) (hk : 0 < k) :
    expandedLength (spec.scale k hk) F slot =
      fun row ↦ k * expandedLength spec F slot row := by
  funext row
  unfold expandedLength
  by_cases hrow : slot.symm row ∈ F <;> simp [hrow]

/-- **(iii) Scaling**, over `ℚ`. -/
theorem expandedFinish_scale (spec : Spec n p) (F : Finset (Fin p))
    (slot : Fin p ≃ coordinate) (k : ℕ) (hk : 0 < k) :
    expandedFinish (spec.scale k hk) F slot =
      fun row ↦ (k : ℚ) * expandedFinish spec F slot row := by
  funext row
  rw [expandedFinish_apply, expandedFinish_apply,
    show expandedLength (spec.scale k hk) F slot row
        = k * expandedLength spec F slot row from
      congrFun (expandedLength_scale spec F slot k hk) row]
  push_cast
  ring

end Vector

/-! ## 2.  The interface, with the forest as its zero set

An `InputInterface (spec' : Spec n' p') (F : Finset (Fin p'))`, stated at the
level of the chart matrix so that it is inhabited independently of a gluing
datum.  At a presentation it is exactly the positive interface's shape with
the forest rows zeroed. -/

section Interface

variable {coordinate : Type*} [Fintype coordinate] {n p : ℕ}

/-- **(iv) The interface at the forest.**  A labelling of the cubic model's
slots by matrix rows under which the realized rational metric is the expanded
endpoint vector: the requested length on every retained slot, `0` on every slot
of the expansion forest `F`. -/
structure ExpandedInterface (spec : Spec n p) (F : Finset (Fin p))
    (M : Matrix coordinate coordinate ℚ) (coordinates : coordinate → ℚ) where
  /-- Which matrix row displays the stable path of a given cubic slot. -/
  slot : Fin p ≃ coordinate
  /-- The realized rational metric is the expanded endpoint vector. -/
  matrixMap : M.mulVec coordinates = expandedFinish spec F slot

namespace ExpandedInterface

variable {spec : Spec n p} {F : Finset (Fin p)}
  {M : Matrix coordinate coordinate ℚ} {coordinates : coordinate → ℚ}

/-- Build the interface from a nonnegative length function on rows, the shape in
which a certificate actually presents it. -/
def ofStableLength (slot : Fin p ≃ coordinate) (stableLength : coordinate → ℕ)
    (hMap : ∀ row, M.mulVec coordinates row = (stableLength row : ℚ))
    (length_eq : ∀ i : Fin p, i ∉ F → stableLength (slot i) = spec.length i)
    (zero_eq : ∀ i : Fin p, i ∈ F → stableLength (slot i) = 0) :
    ExpandedInterface spec F M coordinates where
  slot := slot
  matrixMap := by
    funext row
    have key : stableLength row = expandedLength spec F slot row := by
      by_cases hmem : slot.symm row ∈ F
      · have h1 : stableLength row = 0 := by
          have h := zero_eq _ hmem
          rwa [slot.apply_symm_apply] at h
        rw [h1, expandedLength_of_mem spec F slot hmem]
      · have h1 : stableLength row = spec.length (slot.symm row) := by
          have h := length_eq _ hmem
          rwa [slot.apply_symm_apply] at h
        rw [h1, expandedLength_of_not_mem spec F slot hmem]
    rw [hMap row, expandedFinish_apply, key]

@[simp] theorem ofStableLength_slot (slot : Fin p ≃ coordinate)
    (stableLength : coordinate → ℕ)
    (hMap : ∀ row, M.mulVec coordinates row = (stableLength row : ℚ))
    (length_eq : ∀ i : Fin p, i ∉ F → stableLength (slot i) = spec.length i)
    (zero_eq : ∀ i : Fin p, i ∈ F → stableLength (slot i) = 0) :
    (ofStableLength (spec := spec) (F := F) slot stableLength hMap length_eq
      zero_eq).slot = slot := rfl

theorem apply_eq (iface : ExpandedInterface spec F M coordinates) (row : coordinate) :
    M.mulVec coordinates row = expandedFinish spec F iface.slot row :=
  congrFun iface.matrixMap row

/-- **(ii) at the interface**: every row total is nonnegative. -/
theorem nonneg (iface : ExpandedInterface spec F M coordinates) (row : coordinate) :
    0 ≤ M.mulVec coordinates row := by
  rw [iface.apply_eq row]; exact expandedFinish_nonneg _ _ _ _

/-- **(iv) the zero rows are precisely the expansion forest.**  This is the
clause the terminal contraction needs: the rows the terminal face contracts are
the forest rows and no others. -/
theorem eq_zero_iff (iface : ExpandedInterface spec F M coordinates)
    (row : coordinate) :
    M.mulVec coordinates row = 0 ↔ iface.slot.symm row ∈ F := by
  rw [iface.apply_eq row]; exact expandedFinish_eq_zero_iff _ _ _ _

theorem pos_iff (iface : ExpandedInterface spec F M coordinates)
    (row : coordinate) :
    0 < M.mulVec coordinates row ↔ iface.slot.symm row ∉ F := by
  rw [iface.apply_eq row]; exact expandedFinish_pos_iff _ _ _ _

theorem apply_slot_of_not_mem (iface : ExpandedInterface spec F M coordinates)
    {i : Fin p} (hi : i ∉ F) :
    M.mulVec coordinates (iface.slot i) = (spec.length i : ℚ) := by
  rw [iface.apply_eq (iface.slot i)]
  exact expandedFinish_slot_of_not_mem spec F iface.slot hi

theorem apply_slot_of_mem (iface : ExpandedInterface spec F M coordinates)
    {i : Fin p} (hi : i ∈ F) :
    M.mulVec coordinates (iface.slot i) = 0 := by
  rw [iface.apply_eq (iface.slot i)]
  exact expandedFinish_slot_of_mem spec F iface.slot hi

/-- The coordinate type of the march has exactly as many elements as the cubic
model has slots (the expanded model, not the requested one). -/
theorem card_coordinate (iface : ExpandedInterface spec F M coordinates) :
    Fintype.card coordinate = p := by
  rw [← Fintype.card_fin p]
  exact (Fintype.card_congr iface.slot).symm

end ExpandedInterface

end Interface

/-! ### Relation to the positive interface, and why this is a separate structure -/

section Compare

variable {target : CFGraph} {degree : ℕ}
  {gluing : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree gluing wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {presentation : candidate.datum.LengthMatrixPresentation coordinate}
  {coordinates : coordinate → ℚ}
  {n p : ℕ} {spec : Spec n p} {F : Finset (Fin p)}

/-- **At an empty forest the interface has no zero row.**  Its `matrixMap` ties
each row total to `Spec.length`, which `Spec.length_pos` keeps strictly
positive.  This is the exact reason a nonempty expansion forest forces the
fourth parameter: without it the requested metric on a contracted slot would
have to be both `0` and `spec.length`. -/
theorem inputInterface_pos (iface : InputInterface spec presentation coordinates)
    (row : coordinate) :
    0 < (GluingDatum.LengthMatrixPresentation.matrix presentation).mulVec
      coordinates row := by
  rw [congrFun iface.matrixMap_empty row]
  exact_mod_cast spec.length_pos (iface.slot.symm row)

/-- The same at a general forest, on a retained row. -/
theorem inputInterface_pos_of_not_mem
    (iface : InputInterface spec presentation coordinates F) {row : coordinate}
    (hrow : iface.slot.symm row ∉ F) :
    0 < (GluingDatum.LengthMatrixPresentation.matrix presentation).mulVec
      coordinates row := by
  rw [congrFun iface.matrixMap row, if_neg hrow]
  exact_mod_cast spec.length_pos (iface.slot.symm row)

/-- and zero exactly on the forest. -/
theorem inputInterface_eq_zero_of_mem
    (iface : InputInterface spec presentation coordinates F) {row : coordinate}
    (hrow : iface.slot.symm row ∈ F) :
    (GluingDatum.LengthMatrixPresentation.matrix presentation).mulVec
      coordinates row = 0 := by
  rw [congrFun iface.matrixMap row, if_pos hrow]

/-- **Consequently an interface at the empty forest pins the forest down.** -/
theorem eq_empty_of_inputInterface
    (iface : ExpandedInterface spec F
      (GluingDatum.LengthMatrixPresentation.matrix presentation) coordinates)
    (base : InputInterface spec presentation coordinates) : F = ∅ := by
  by_contra hne
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hzero := iface.apply_slot_of_mem hi
  have hpos := inputInterface_pos base (iface.slot i)
  rw [hzero] at hpos
  exact lt_irrefl _ hpos

/-- **Every interface is an expanded interface at the same forest.** -/
def ofInputInterface (iface : InputInterface spec presentation coordinates F) :
    ExpandedInterface spec F
      (GluingDatum.LengthMatrixPresentation.matrix presentation) coordinates where
  slot := iface.slot
  matrixMap := by
    rw [iface.matrixMap]
    funext row
    by_cases hrow : iface.slot.symm row ∈ F <;>
      simp [expandedFinish, expandedLength, hrow]

/-- **and conversely, at every forest**, so `ExpandedInterface` and the
generalised `InputInterface` are the same data over a length-matrix
presentation; the positive interface is the `F = ∅` instance of both. -/
def toInputInterface
    (iface : ExpandedInterface spec F
      (GluingDatum.LengthMatrixPresentation.matrix presentation) coordinates) :
    InputInterface spec presentation coordinates F where
  slot := iface.slot
  matrixMap := by
    rw [iface.matrixMap]
    funext row
    by_cases hrow : iface.slot.symm row ∈ F <;>
      simp [expandedFinish, expandedLength, hrow]

@[simp] theorem ofInputInterface_slot
    (iface : InputInterface spec presentation coordinates F) :
    (ofInputInterface iface).slot = iface.slot := rfl

@[simp] theorem toInputInterface_slot
    (iface : ExpandedInterface spec F
      (GluingDatum.LengthMatrixPresentation.matrix presentation) coordinates) :
    (toInputInterface iface).slot = iface.slot := rfl

end Compare

/-! ### The terminal interface -/

section Terminal

variable {coordinate chart : Type} [Fintype coordinate] [DecidableEq coordinate]
  {n p degree : ℕ} {spec : Spec n p}
  {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}
  {target : CFGraph} {gluing : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree gluing wall}

/-- **(iv) The terminal interface, with zero expansion rows.**  Once
`baseFinish` is the expanded endpoint vector, the face-level interface at the
state's own coordinate vector is one rewrite — the strong presentation's matrix
is the chart matrix and `currentFinish_map` is the chart system.  Its zero rows
are the expansion forest by `ExpandedInterface.eq_zero_iff`. -/
def terminalExpandedInterface (F : Finset (Fin p))
    (state : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (strong : TraversalPresentation.StrongPresentation candidate.datum coordinate)
    (hStrongMatrix : GluingDatum.LengthMatrixPresentation.matrix
      strong.toPresentation = matrix state.label)
    (slot : Fin p ≃ coordinate)
    (hBase : baseFinish = expandedFinish spec F slot) :
    ExpandedInterface spec F
      (GluingDatum.LengthMatrixPresentation.matrix strong.toPresentation)
      state.currentFinish where
  slot := slot
  matrixMap := by rw [hStrongMatrix, state.currentFinish_map, hBase]

/-- **The general interface at the forest.**  The same data read as an
`InputRefinementData.InputInterface` at the forest `F`, the form the terminal
identification consumes; at `F = ∅` it is the positive terminal interface. -/
def terminalForestInterface (F : Finset (Fin p))
    (state : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (strong : TraversalPresentation.StrongPresentation candidate.datum coordinate)
    (hStrongMatrix : GluingDatum.LengthMatrixPresentation.matrix
      strong.toPresentation = matrix state.label)
    (slot : Fin p ≃ coordinate)
    (hBase : baseFinish = expandedFinish spec F slot) :
    InputInterface spec strong.toPresentation state.currentFinish F :=
  toInputInterface
    (terminalExpandedInterface (spec := spec) F state strong hStrongMatrix slot hBase)

@[simp] theorem terminalForestInterface_slot (F : Finset (Fin p))
    (state : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (strong : TraversalPresentation.StrongPresentation candidate.datum coordinate)
    (hStrongMatrix : GluingDatum.LengthMatrixPresentation.matrix
      strong.toPresentation = matrix state.label)
    (slot : Fin p ≃ coordinate)
    (hBase : baseFinish = expandedFinish spec F slot) :
    (terminalForestInterface (spec := spec) F state strong hStrongMatrix slot
      hBase).slot = slot := rfl

@[simp] theorem terminalExpandedInterface_slot (F : Finset (Fin p))
    (state : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (strong : TraversalPresentation.StrongPresentation candidate.datum coordinate)
    (hStrongMatrix : GluingDatum.LengthMatrixPresentation.matrix
      strong.toPresentation = matrix state.label)
    (slot : Fin p ≃ coordinate)
    (hBase : baseFinish = expandedFinish spec F slot) :
    (terminalExpandedInterface (spec := spec) F state strong hStrongMatrix slot
      hBase).slot = slot := rfl

end Terminal

/-! ## 3.  At a cleared face: the zero rows are contracted, occurrence by
occurrence -/

section Face

variable {target : CFGraph} {degree : ℕ}
  {gluing : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree gluing wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {presentation : candidate.datum.LengthMatrixPresentation coordinate}
  {coordinates : coordinate → ℚ}
  {n p : ℕ} {spec : Spec n p} {F : Finset (Fin p)}

/-- The ordered list of cleared source-occurrence lengths along the stable path
displaying cubic slot `i`. -/
def expandedRowSegments
    (iface : ExpandedInterface spec F
      (GluingDatum.LengthMatrixPresentation.matrix presentation) coordinates)
    (face : ClearedFace candidate presentation coordinates) (i : Fin p) : List ℕ :=
  (presentation.path (iface.slot i)).map face.realization.sourceLength

/-- The one arithmetic fact the interface exists to provide, with zero totals
allowed. -/
theorem expandedRowSegments_sum
    (iface : ExpandedInterface spec F
      (GluingDatum.LengthMatrixPresentation.matrix presentation) coordinates)
    (face : ClearedFace candidate presentation coordinates) (i : Fin p) :
    (expandedRowSegments iface face i).sum =
      face.scale * expandedLength spec F iface.slot (iface.slot i) := by
  have h := face.sourcePathLength_eq_scale_mul_of_matrixMap
    (expandedLength spec F iface.slot) iface.matrixMap (iface.slot i)
  simpa [expandedRowSegments] using h

/-- On a retained slot the row realizes the requested scaled length on the
nose. -/
theorem expandedRowSegments_sum_of_not_mem
    (iface : ExpandedInterface spec F
      (GluingDatum.LengthMatrixPresentation.matrix presentation) coordinates)
    (face : ClearedFace candidate presentation coordinates) {i : Fin p}
    (hi : i ∉ F) :
    (expandedRowSegments iface face i).sum = face.scale * spec.length i := by
  rw [expandedRowSegments_sum iface face i,
    expandedLength_slot_of_not_mem spec F iface.slot hi]

/-- On an expansion-forest slot the row has total zero. -/
theorem expandedRowSegments_sum_of_mem
    (iface : ExpandedInterface spec F
      (GluingDatum.LengthMatrixPresentation.matrix presentation) coordinates)
    (face : ClearedFace candidate presentation coordinates) {i : Fin p}
    (hi : i ∈ F) : (expandedRowSegments iface face i).sum = 0 := by
  rw [expandedRowSegments_sum iface face i,
    expandedLength_slot_of_mem spec F iface.slot hi, Nat.mul_zero]

/-- **(iv) the terminal face's zero-row contraction is the expansion forest.**
Every source occurrence displayed by a forest row has cleared length zero, so
the face contracts the whole row. -/
theorem sourceLength_eq_zero_of_mem
    (iface : ExpandedInterface spec F
      (GluingDatum.LengthMatrixPresentation.matrix presentation) coordinates)
    (face : ClearedFace candidate presentation coordinates) {i : Fin p}
    (hi : i ∈ F) :
    ∀ edge ∈ presentation.path (iface.slot i),
      face.realization.sourceLength edge = 0 := by
  intro edge hedge
  have hsum := expandedRowSegments_sum_of_mem iface face hi
  have hmem : face.realization.sourceLength edge ∈ expandedRowSegments iface face i :=
    List.mem_map_of_mem hedge
  have hle : face.realization.sourceLength edge ≤
      (expandedRowSegments iface face i).sum := List.le_sum_of_mem hmem
  rw [hsum] at hle
  omega

/-- and no retained row is contracted whole: it carries an occurrence of
positive cleared length. -/
theorem exists_sourceLength_ne_zero_of_not_mem
    (iface : ExpandedInterface spec F
      (GluingDatum.LengthMatrixPresentation.matrix presentation) coordinates)
    (face : ClearedFace candidate presentation coordinates) {i : Fin p}
    (hi : i ∉ F) :
    ∃ edge ∈ presentation.path (iface.slot i),
      face.realization.sourceLength edge ≠ 0 := by
  by_contra hcontra
  have hall : ∀ edge ∈ presentation.path (iface.slot i),
      face.realization.sourceLength edge = 0 := by
    intro edge hedge
    by_contra hne
    exact hcontra ⟨edge, hedge, hne⟩
  have hsum := expandedRowSegments_sum_of_not_mem iface face hi
  have hzero : (expandedRowSegments iface face i).sum = 0 := by
    refine List.sum_eq_zero_iff.mpr ?_
    intro x hx
    obtain ⟨edge, hedge, hx'⟩ := List.mem_map.mp hx
    rw [← hx']
    exact hall edge hedge
  rw [hzero] at hsum
  have hscale := face.scale_pos
  have hlen := spec.length_pos i
  have hpos : 0 < face.scale * spec.length i := Nat.mul_pos hscale hlen
  omega

end Face

/-! ## 4.  The expansion datum: which slots are retained, which are the forest

`Utilities.Subdivision.CoreExpansion.ExpansionData` already carries the split:
`kind e = .contracted` is an expansion-forest slot, `kind e = .single j` carries
the requested slot `j`, and `kind e = .double j₁ j₂` carries two requested slots
in series through a marker (a loop of the underlying metric graph). -/

section Expansion

variable {n p N Q : ℕ}

/-- The expansion forest of a datum: its contracted slots. -/
def expansionForest (D : ExpansionData n p N Q) : Finset (Fin Q) :=
  Finset.univ.filter fun e ↦ D.kind e = SlotKind.contracted

@[simp] theorem mem_expansionForest (D : ExpansionData n p N Q) (e : Fin Q) :
    e ∈ expansionForest D ↔ D.kind e = SlotKind.contracted := by
  simp [expansionForest]

/-- The requested length a big slot carries, by its role: nothing on a
contracted slot, one requested length on a `single`, two in series on a
`double`.  This is `CoreExpansion.kindLength` with the contracted slot's
placeholder length `1` replaced by `0`. -/
def slotFinishLength (small : Spec n p) : SlotKind p → ℕ
  | SlotKind.contracted => 0
  | SlotKind.single j => small.length j
  | SlotKind.double j₁ j₂ => small.length j₁ + small.length j₂

/-- Off the forest it is the cubic model's own slot length. -/
theorem slotFinishLength_eq_kindLength (small : Spec n p) {k : SlotKind p}
    (hk : k ≠ SlotKind.contracted) :
    slotFinishLength small k = kindLength small k := by
  cases k with
  | contracted => exact absurd rfl hk
  | single j => rfl
  | double j₁ j₂ => rfl

theorem slotFinishLength_pos_iff (small : Spec n p) (k : SlotKind p) :
    0 < slotFinishLength small k ↔ k ≠ SlotKind.contracted := by
  cases k with
  | contracted =>
      have h0 : slotFinishLength small (SlotKind.contracted : SlotKind p) = 0 := rfl
      rw [h0]
      simp
  | single j =>
      constructor
      · intro _ h
        simp at h
      · intro _
        exact small.length_pos j
  | double j₁ j₂ =>
      constructor
      · intro _ h
        simp at h
      · intro _
        have h1 := small.length_pos j₁
        show 0 < small.length j₁ + small.length j₂
        omega

theorem slotFinishLength_scale (small : Spec n p) (k : SlotKind p) (m : ℕ)
    (hm : 0 < m) :
    slotFinishLength (small.scale m hm) k = m * slotFinishLength small k := by
  cases k with
  | contracted => rfl
  | single j => rfl
  | double j₁ j₂ =>
      show (small.scale m hm).length j₁ + (small.scale m hm).length j₂
        = m * (small.length j₁ + small.length j₂)
      rw [Spec.scale_length, Spec.scale_length, Nat.mul_add]

/-- The expanded endpoint vector read off the expansion datum. -/
def expansionLength (D : ExpansionData n p N Q) (small : Spec n p) (e : Fin Q) : ℕ :=
  slotFinishLength small (D.kind e)

/-- **(i) A retained `single` slot carries exactly its requested length.** -/
theorem expansionLength_single (D : ExpansionData n p N Q) (small : Spec n p)
    {e : Fin Q} {j : Fin p} (hk : D.kind e = SlotKind.single j) :
    expansionLength D small e = small.length j := by
  show slotFinishLength small (D.kind e) = small.length j
  rw [hk]
  rfl

/-- **(i) A retained `double` slot carries the two requested lengths it joins
through a marker.** -/
theorem expansionLength_double (D : ExpansionData n p N Q) (small : Spec n p)
    {e : Fin Q} {j₁ j₂ : Fin p} (hk : D.kind e = SlotKind.double j₁ j₂) :
    expansionLength D small e = small.length j₁ + small.length j₂ := by
  show slotFinishLength small (D.kind e) = small.length j₁ + small.length j₂
  rw [hk]
  rfl

/-- **(i) An expansion-forest slot carries exactly zero.** -/
theorem expansionLength_contracted (D : ExpansionData n p N Q) (small : Spec n p)
    {e : Fin Q} (hk : D.kind e = SlotKind.contracted) :
    expansionLength D small e = 0 := by
  show slotFinishLength small (D.kind e) = 0
  rw [hk]
  rfl

theorem expansionLength_pos_iff (D : ExpansionData n p N Q) (small : Spec n p)
    (e : Fin Q) : 0 < expansionLength D small e ↔ e ∉ expansionForest D := by
  constructor
  · intro h
    simp only [mem_expansionForest]
    exact (slotFinishLength_pos_iff small (D.kind e)).mp h
  · intro h
    refine (slotFinishLength_pos_iff small (D.kind e)).mpr ?_
    simpa only [mem_expansionForest] using h

/-- **(iii) Scaling in the requested specification.**  Refining the small
specification `k`-fold multiplies the finish vector by `k` — even though the
cubic model's own contracted slots keep length one under
`CoreExpansion.kindLength`, so this is not `Spec.scale` of the big model. -/
theorem expansionLength_scale (D : ExpansionData n p N Q) (small : Spec n p)
    (m : ℕ) (hm : 0 < m) :
    expansionLength D (small.scale m hm) = fun e ↦ m * expansionLength D small e := by
  funext e
  show slotFinishLength (small.scale m hm) (D.kind e)
      = m * slotFinishLength small (D.kind e)
  exact slotFinishLength_scale small (D.kind e) m hm

/-- **The tie between §1 and the expansion datum.**  On the cubic model `D.bigSpec`, the
abstract expanded vector at the forest `expansionForest D` is exactly the
role-by-role vector `expansionLength`. -/
theorem expandedLength_bigSpec {coordinate : Type*} (D : ExpansionData n p N Q)
    (small : Spec n p) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (slot : Fin Q ≃ coordinate) (e : Fin Q) :
    expandedLength (D.bigSpec small hN hL) (expansionForest D) slot (slot e) =
      expansionLength D small e := by
  by_cases hmem : e ∈ expansionForest D
  · rw [expandedLength_slot_of_mem _ _ _ hmem,
      expansionLength_contracted D small ((mem_expansionForest D e).mp hmem)]
  · have hk : D.kind e ≠ SlotKind.contracted := by
      simpa only [mem_expansionForest] using hmem
    rw [expandedLength_slot_of_not_mem _ _ _ hmem]
    show kindLength small (D.kind e) = slotFinishLength small (D.kind e)
    exact (slotFinishLength_eq_kindLength small hk).symm

/-- **(iii) Scaling on the cubic model.**  Refining the *requested*
specification `m`-fold multiplies the finish vector on the cubic model by `m`;
the forest entries stay zero, so this is not `Spec.scale` of the cubic model
itself (whose contracted slots keep length one). -/
theorem expandedLength_bigSpec_scale {coordinate : Type*} (D : ExpansionData n p N Q)
    (small : Spec n p) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (slot : Fin Q ≃ coordinate) (m : ℕ) (hm : 0 < m) (row : coordinate) :
    expandedLength (D.bigSpec (small.scale m hm) hN hL) (expansionForest D) slot row
      = m * expandedLength (D.bigSpec small hN hL) (expansionForest D) slot row := by
  have h1 := expandedLength_bigSpec D (small.scale m hm) hN hL slot (slot.symm row)
  have h2 := expandedLength_bigSpec D small hN hL slot (slot.symm row)
  rw [slot.apply_symm_apply] at h1 h2
  rw [h1, h2, congrFun (expansionLength_scale D small m hm) (slot.symm row)]

theorem expandedFinish_bigSpec_scale {coordinate : Type*} (D : ExpansionData n p N Q)
    (small : Spec n p) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (slot : Fin Q ≃ coordinate) (m : ℕ) (hm : 0 < m) (row : coordinate) :
    expandedFinish (D.bigSpec (small.scale m hm) hN hL) (expansionForest D) slot row
      = (m : ℚ) *
        expandedFinish (D.bigSpec small hN hL) (expansionForest D) slot row := by
  rw [expandedFinish_apply, expandedFinish_apply,
    expandedLength_bigSpec_scale D small hN hL slot m hm row]
  push_cast
  ring

/-- Every requested slot is claimed by a retained big slot: its owner is never
in the expansion forest. -/
theorem owner_not_mem_expansionForest {D : ExpansionData n p N Q} {C : Core n p}
    (hCond : D.Conditions C) (j : Fin p) : D.owner j ∉ expansionForest D := by
  rw [mem_expansionForest]
  exact (ExpansionData.claimed_of_conditions hCond j).1

/-- and therefore carries at least its own requested length. -/
theorem le_expansionLength_owner {D : ExpansionData n p N Q} {small : Spec n p}
    (hCond : D.Conditions small.core) (j : Fin p) :
    small.length j ≤ expansionLength D small (D.owner j) := by
  rcases ExpansionData.exists_carrier hCond j with
    ⟨hk, -⟩ | ⟨j₂, hk, -⟩ | ⟨j₁, hk, -⟩
  · rw [expansionLength_single D small hk]
  · rw [expansionLength_double D small hk]; omega
  · rw [expansionLength_double D small hk]; omega

theorem expansionLength_owner_pos {D : ExpansionData n p N Q} {small : Spec n p}
    (hCond : D.Conditions small.core) (j : Fin p) :
    0 < expansionLength D small (D.owner j) :=
  lt_of_lt_of_le (small.length_pos j) (le_expansionLength_owner hCond j)

end Expansion

/-! ### The composite reduction, returning the datum

`StableModelPackaging.exists_cubicModel` hides the expansion datum behind the
contraction certificate, so the expansion forest is not visible through it.  The
same composition is re-run here, returning the datum, which is what the finish
vector above is indexed by. -/

section Model

open DraismaVargas.LocalCases.StableModelReduction
open DraismaVargas.LocalCases.StableModelPackaging
open DraismaVargas.LocalCases.BridgeReduction

/-- **The reduction to a cubic model, with its expansion datum exposed.**  Every
connected specification of
genus at least two is presented, after bridge contraction, bivalent suppression
and reorientation, by a connected specification `spec₀` carrying an expansion
datum whose `bigSpec` is a cubic loopless connected model, with Brill--Noether
existence transported both ways on every uniform refinement.  The expansion
forest of that datum is `expansionForest D`. -/
theorem exists_expansionModel {n p : ℕ} (spec : Spec n p)
    (hConn : spec.core.Connected) (hGenus : n < p) :
    ∃ (n₀ p₀ : ℕ) (spec₀ : Spec n₀ p₀)
      (D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀))),
      D.Conditions spec₀.core ∧ D.bigCore.Cubic ∧ D.bigCore.Connected ∧
        (∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e) ∧
        0 < 2 * (p₀ - n₀) ∧ spec₀.core.Connected ∧ n₀ < p₀ ∧
        (p₀ : ℤ) - n₀ = (p : ℤ) - n ∧
        (∀ r d : ℤ, BNExists spec₀.graph r d ↔ BNExists spec.graph r d) ∧
        (∀ (k : ℕ) (hk : 0 < k) (r d : ℤ),
          BNExists (spec₀.scale k hk).graph r d ↔
            BNExists (spec.scale k hk).graph r d) := by
  obtain ⟨n₀, p₀, spec₀, mk, hbase, hc₀, hb₀, hlt₀, hg₀, hbn₀, hbns₀⟩ :=
    exists_markedSpec spec hConn hGenus
  have hstable : Stable mk := stable_of_bridgeless mk spec₀.core_loopless hbase hb₀
  obtain ⟨D, hCond, hCubic, hConnBig⟩ :=
    exists_markerExpansion mk hstable spec₀.core_loopless hc₀
  refine ⟨n₀, p₀, spec₀, D, hCond, hCubic, hConnBig,
    fun e ↦ ExpansionData.loopless_of_conditions hCond e, by omega, hc₀, hlt₀,
    hg₀, hbn₀, hbns₀⟩

/-- **The requested endpoint vector with zero expansion rows, in one
sentence.**  For an arbitrary
connected requested specification of genus at least two — no trivalence
hypothesis — there is a cubic connected loopless model together with the finish
vector this file assigns: nonnegative, positive exactly off the expansion
forest, carrying the requested integral lengths role by role, and with
Brill--Noether existence transported back to the request in every rank and
degree.  What it does **not** supply is the pencil transport itself
(`RetainedRelabeling`, `StatementFromLink`). -/
theorem exists_expandedFinish {n p : ℕ} (spec : Spec n p)
    (hConn : spec.core.Connected) (hGenus : n < p) :
    ∃ (n₀ p₀ : ℕ) (spec₀ : Spec n₀ p₀)
      (D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀)))
      (hN : 0 < 2 * (p₀ - n₀))
      (hL : ∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e),
      D.bigCore.Cubic ∧ D.bigCore.Connected ∧
        (p₀ : ℤ) - n₀ = (p : ℤ) - n ∧
        (∀ r d : ℤ, BNExists spec₀.graph r d ↔ BNExists spec.graph r d) ∧
        ∀ (coordinate : Type) (slot : Fin (3 * (p₀ - n₀)) ≃ coordinate),
          (∀ row, 0 ≤
              expandedFinish (D.bigSpec spec₀ hN hL) (expansionForest D) slot row) ∧
            (∀ row, 0 <
                expandedFinish (D.bigSpec spec₀ hN hL) (expansionForest D) slot row ↔
              slot.symm row ∉ expansionForest D) ∧
            (∀ e, expandedLength (D.bigSpec spec₀ hN hL) (expansionForest D) slot
                (slot e) = expansionLength D spec₀ e) := by
  obtain ⟨n₀, p₀, spec₀, D, hCond, hCubic, hConnBig, hL, hN, -, -, hg₀, hbn₀, -⟩ :=
    exists_expansionModel spec hConn hGenus
  refine ⟨n₀, p₀, spec₀, D, hN, hL, hCubic, hConnBig, hg₀, hbn₀, ?_⟩
  intro coordinate slot
  exact ⟨fun row ↦ expandedFinish_nonneg _ _ _ _,
    fun row ↦ expandedFinish_pos_iff _ _ _ _,
    fun e ↦ expandedLength_bigSpec D spec₀ hN hL slot e⟩

end Model

/-! ## 5.  Non-vacuity: an explicit expansion with a two-slot forest

The four-fold banana `bananaCore` is connected, loopless and **not** cubic (both
vertices are four-valent), so it is exactly the kind of request the positive-only
interface cannot serve.  `bananaExpansion` expands it to a cubic core on four
vertices and six slots; two of those slots are contracted, and the endpoint
vector this file assigns is `![0, 0, 2, 3, 5, 7]`. -/

section Witness

/-- Two vertices joined by four parallel slots: genus three, four-valent. -/
def bananaCore : Core 2 4 where
  tail := ![0, 0, 0, 0]
  head := ![1, 1, 1, 1]

/-- The requested integral lengths. -/
def bananaSpec : Spec 2 4 :=
  Spec.ofCore bananaCore (by norm_num) (by decide) ![2, 3, 5, 7] (by decide)

/-- The cubic expansion: `0, 1` sit over the small vertex `0` and `2, 3` over
the small vertex `1`; slots `0` and `1` are the contracted ones. -/
def bananaBigCore : Core 4 6 where
  tail := ![0, 2, 0, 0, 1, 1]
  head := ![1, 3, 2, 3, 2, 3]

/-- The expansion datum. -/
def bananaExpansion : ExpansionData 2 4 4 6 where
  bigCore := bananaBigCore
  fib := ![0, 0, 1, 1]
  kind := ![SlotKind.contracted, SlotKind.contracted, SlotKind.single 0,
    SlotKind.single 1, SlotKind.single 2, SlotKind.single 3]
  owner := ![2, 3, 4, 5]
  side := ![false, false, false, false]

theorem banana_bigLoopless :
    ∀ e : Fin 6, bananaBigCore.tail e ≠ bananaBigCore.head e := by decide

theorem banana_conditions : bananaExpansion.Conditions bananaCore := by decide

theorem banana_cubic : bananaBigCore.Cubic := by
  intro v
  fin_cases v <;> decide

/-- **The forest is not empty**: two slots of the cubic model carry no requested
length at all. -/
theorem banana_expansionForest : expansionForest bananaExpansion = {0, 1} := by decide

theorem banana_expansionForest_nonempty : (expansionForest bananaExpansion).Nonempty :=
  ⟨0, by decide⟩

/-- The cubic model of the four-fold banana. -/
def bananaBigSpec : Spec 4 6 :=
  bananaExpansion.bigSpec bananaSpec (by norm_num) banana_bigLoopless

/-- **The finish vector**: zero on the two forest slots, the requested integral
lengths on the four retained ones. -/
theorem banana_expandedLength :
    expandedLength bananaBigSpec (expansionForest bananaExpansion)
      (Equiv.refl (Fin 6)) = ![0, 0, 2, 3, 5, 7] := by decide

/-- An inhabitant of `ExpandedInterface` at a **nonempty** forest. -/
def bananaInterface :
    ExpandedInterface bananaBigSpec (expansionForest bananaExpansion)
      (1 : Matrix (Fin 6) (Fin 6) ℚ)
      (expandedFinish bananaBigSpec (expansionForest bananaExpansion)
        (Equiv.refl (Fin 6))) where
  slot := Equiv.refl (Fin 6)
  matrixMap := Matrix.one_mulVec _

example : (0 : Fin 6) ∈ expansionForest bananaExpansion := by decide

/-- **Non-vacuity of `InputRefinementData.RetainedIndex` at a nonempty
forest.**  The four retained slots of the banana's cubic model each carry
exactly one of the four requested slots, with the requested lengths: the
contracted request the retained refinement lives on is `bananaSpec` itself.
Compare `InputRefinementData.RetainedIndex.self`, the `F = ∅` instance.

The carrier field is a *list* (a retained slot may carry two requested slots in
series through a marker); here every list is a singleton, which is exactly what
`RetainedIndexProducer.MarkerFree` says of `bananaExpansion`. -/
def bananaRetained :
    InputRefinementData.RetainedIndex bananaBigSpec
      (expansionForest bananaExpansion) bananaSpec where
  carried := fun e ↦ [⟨(e : Fin 6).val - 2, by have := (e : Fin 6).isLt; omega⟩]
  owner := fun j ↦ ⟨⟨j.val + 2, by have := j.isLt; omega⟩, by
    rw [banana_expansionForest]
    fin_cases j <;> decide⟩
  pos := fun _ ↦ 0
  carried_getElem := by decide
  owner_eq_of_mem := by decide
  nodup := fun _ ↦ List.nodup_singleton _
  carried_ne_nil := fun _ ↦ List.cons_ne_nil _ _
  length_eq := by decide

end Witness

end DraismaVargas.LocalCases.RequestedExpandedEndpoints
