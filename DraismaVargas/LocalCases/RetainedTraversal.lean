import DraismaVargas.LocalCases.RetainedCut

/-!
# The oriented row at a nonempty expansion forest

**Source.**  The traversal is Part I's row order, formalized in
`DraismaVargas.LocalCases.OrientedTraversal` §1--§3; nothing here is in the
papers beyond that.  At a nonempty expansion forest the `F`-rows are zero rows,
so `vertexClass (Sum.inl w)` is well defined by
`classOf_rowWalk_eq_of_zero_run` applied to a whole row.

## What is proved

`OrientedTraversal` §3 builds the oriented walk along a row, the positions of
the surviving occurrences in it, and the orientation flag, but the whole of its
`RowDictionary` section is typed at the **empty** forest: its section variable
is `InputInterface spec strong.toPresentation coordinates` with `F = ∅`.
`RetainedRelabeling` §1 re-proves at a general forest the part that the slot
half needs (`positiveRow`, `keptSlotEquiv`, `card_keptSlots`).  This file re-proves the
rest, which the **vertex** half needs, and which is forest-independent for the
same reason: the walk uses only `PresentationDecomposition.Decomposes` and the
two path-end fields of the strong presentation, never the interface's row
totals.

* §1 the walk: `rowWalk`, its step and incidence equations, its end
  (`rowWalk_length`, on the one orientation bit `OrientedTraversal` §2 shows a
  `StrongPresentation` leaves open), and the confinement
  `classOf_rowWalk_eq_of_zero_run` -- along a run of contracted occurrences the
  walk stays in one contraction class.

* §2 the positions: `position i m` is the place in the row of the `m`-th
  surviving occurrence, `slotPosition` is it for a kept slot, and
  `sourceLength_eq_zero_of_*` say that everything before the first, after the
  last and strictly between two consecutive surviving occurrences is
  contracted.  These are the three runs the endpoint equations of a
  `RefinementCore.CoreModel` have to absorb.

* §3 the orientation flag `reversedAt`, with the two equations naming the ends
  of an occurrence on the walk (`sourceEnds_occurrence_fst`, `..._snd`).  It is
  computed, not assumed.

* §4 is the general-forest content: **a forest row is contracted to a point.**
  `classOf_rowWalk_eq_of_mem_forest` and
  `classOf_finish_eq_classOf_start_of_mem_forest`: every vertex the walk
  meets along a row of the expansion forest lies in one contraction class,
  its two ends included, with **no** orientation hypothesis (if the row's two
  ends are literally equal there is nothing to prove, and otherwise the
  orientation bit is free).  This is what makes the requested core vertex map
  of the retained core model well defined: the definition
  `vertexClass (Sum.inl w) := classOf (vertexAt (any model vertex over w))`
  does not depend on the choice, because two model core vertices over the same
  requested one are joined by forest rows.

## What is not proved here

Nothing is assumed beyond `StrongPresentation` and `InputInterface`: no
dictionary, no faithfulness, no spanning, no genus receipt.  In particular

1. **No `vertexClass` is built here.**  The retained analogue of
   `OrientedTraversal.RowDictionary.vertexClass` needs, besides §1--§4, the
   expansion datum's correspondence between the requested core vertices of
   `spec₀` and the core vertices of the cubic model together with the markers
   (`ExpansionData.fib`, `ExpansionData.MarkerIsolated`); that correspondence
   is `DraismaVargas.LocalCases.RetainedFibre`, which uses §4.  The map itself
   is built in `RetainedVertexModel.vertexModel`.
2. **No bijectivity.**  As at the empty forest (`TerminalExhausts`), that is a
   genus count (`RetainedExhausts`), not something the walk provides.

## Used by

The vertex half of the core model on the far end of `RetainedCut.cutChain`,
for `RetainedRelabeling.CutRelabeling`.
-/

namespace DraismaVargas.LocalCases.RetainedTraversal

noncomputable section

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.IteratedSplitRefinement
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.OrientedTraversal
open DraismaVargas.LocalCases.RetainedRelabeling
open DraismaVargas.LocalCases.TraversalPresentation
open DraismaVargas.LocalCases.W4StableSource

variable {target : CFGraph} {degree : ℕ}
  {gluing : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree gluing wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ}
  {n p : ℕ} {spec : SubdivisionGraph.Spec n p} {F : Finset (Fin p)}
  {strong : StrongPresentation candidate.datum coordinate}
  {face : ClearedFace candidate strong.toPresentation coordinates}

/-! ## 1.  The oriented walk along a row, at a general forest -/

section Walk

variable {iface : InputInterface spec strong.toPresentation coordinates F}

theorem row_nodup (i : Fin p) : (row iface i).Nodup :=
  strong.decomposes.nodup _

theorem row_survives (i : Fin p) :
    ∀ edge ∈ row iface i, ¬ IsDangling candidate.datum edge :=
  fun _ hEdge ↦ strong.decomposes.not_isDangling_of_mem hEdge

theorem row_chain (i : Fin p) :
    (row iface i).IsChain (MeetsAt candidate.datum) :=
  strong.chain _

theorem row_ne_nil (i : Fin p) : row iface i ≠ [] :=
  strong.path_ne_nil _

theorem row_length_pos (i : Fin p) : 0 < (row iface i).length :=
  List.length_pos_of_ne_nil (row_ne_nil (iface := iface) i)

theorem row_head_isPathEnd (i : Fin p) (h : 0 < (row iface i).length) :
    IsPathEnd candidate.datum (row iface i)[0] (strong.start (iface.slot i)) :=
  strong.head_isPathEnd _ _ (by rw [Option.mem_def, head?_eq_getElem _ h])

theorem row_getLast_isPathEnd (i : Fin p) (h : 0 < (row iface i).length) :
    IsPathEnd candidate.datum (row iface i)[(row iface i).length - 1]
      (strong.finish (iface.slot i)) :=
  strong.getLast_isPathEnd _ _ (by rw [Option.mem_def, getLast?_eq_getElem _ h])

/-- **The oriented walk along the row displaying stable slot `i`**, at a general
expansion forest: `OrientedTraversal.RowDictionary.rowWalk` verbatim, with the
interface's forest free.  The walk never reads the interface beyond
`iface.slot`. -/
def rowWalk (strong : StrongPresentation candidate.datum coordinate)
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (i : Fin p) (k : ℕ) : candidate.datum.SourceVertex :=
  walkVertex candidate.datum (row iface i) (strong.start (iface.slot i)) k

@[simp] theorem rowWalk_zero (i : Fin p) :
    rowWalk strong iface i 0 = strong.start (iface.slot i) := rfl

theorem rowWalk_succ {i : Fin p} {k : ℕ} (hk : k < (row iface i).length) :
    rowWalk strong iface i (k + 1) =
      otherEnd candidate.datum (row iface i)[k] (rowWalk strong iface i k) :=
  walkVertex_succ _ _ hk

theorem rowWalk_incident {i : Fin p} {k : ℕ} (hk : k < (row iface i).length) :
    Incident candidate.datum (row iface i)[k] (rowWalk strong iface i k) :=
  walkVertex_incident (row_nodup i) (row_survives i) (row_chain i)
    (row_head_isPathEnd i) hk

theorem rowWalk_succ_incident {i : Fin p} {k : ℕ} (hk : k < (row iface i).length) :
    Incident candidate.datum (row iface i)[k] (rowWalk strong iface i (k + 1)) :=
  walkVertex_succ_incident hk

/-- **The walk ends at the row's finish vertex**, given the orientation bit. -/
theorem rowWalk_length {i : Fin p}
    (hOrient : 2 ≤ (row iface i).length ∨
      strong.finish (iface.slot i) ≠ strong.start (iface.slot i)) :
    rowWalk strong iface i (row iface i).length = strong.finish (iface.slot i) :=
  walkVertex_length (row_nodup i) (row_survives i) (row_chain i)
    (row_head_isPathEnd i) (row_getLast_isPathEnd i) (strong.path_ne_nil _) hOrient

/-- An interior walk vertex has surviving valency two. -/
theorem nonDanglingValency_rowWalk_succ {i : Fin p} {k : ℕ}
    (hk : k + 1 < (row iface i).length) :
    nonDanglingValency candidate.datum (rowWalk strong iface i (k + 1)) = 2 :=
  walkVertex_succ_valency (row_nodup i) (row_survives i) (row_chain i)
    (row_head_isPathEnd i) hk

/-- **Along a run of contracted occurrences the walk stays in one contraction
class.**  `OrientedTraversal.RowDictionary.classOf_rowWalk_eq_of_zero_run` at a
general forest; the proof is unchanged, since
`OrientedTraversal.classOf_otherEnd_of_sourceLength_zero` never mentions an
interface. -/
theorem classOf_rowWalk_eq_of_zero_run (topology : ClearedFace.SourceContractionTopology face)
    {i : Fin p} {a b : ℕ} (hab : a ≤ b) (hb : b ≤ (row iface i).length)
    (hZero : ∀ k, ∀ _ : k < (row iface i).length, a ≤ k → k < b →
      face.realization.sourceLength (row iface i)[k] = 0) :
    classOf topology (rowWalk strong iface i a) =
      classOf topology (rowWalk strong iface i b) := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      have hblt : b < (row iface i).length := by omega
      rw [ih (by omega) (fun k hk hak hkb ↦ hZero k hk hak (by omega)), rowWalk_succ hblt]
      exact classOf_otherEnd_of_sourceLength_zero topology
        (rowWalk_incident (strong := strong) (iface := iface) hblt)
        (hZero b hblt hab (Nat.lt_succ_self b))

end Walk

/-! ## 2.  Where the surviving occurrences sit in the row -/

section Position

variable {iface : InputInterface spec strong.toPresentation coordinates F}

theorem positiveRow_sublist (i : Fin p) :
    (positiveRow iface face i).Sublist (row iface i) :=
  List.filter_sublist

theorem exists_positionEmbedding (i : Fin p) :
    ∃ f : Fin (positiveRow iface face i).length ↪o Fin (row iface i).length,
      ∀ m : Fin (positiveRow iface face i).length,
        (positiveRow iface face i)[(m : ℕ)] = (row iface i)[((f m : Fin _) : ℕ)] := by
  obtain ⟨f, hf⟩ :=
    List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
      (positiveRow_sublist (iface := iface) (face := face) i)
  refine ⟨f, fun m ↦ ?_⟩
  have h := hf m
  simp only [List.get_eq_getElem] at h
  exact h

/-- The positions of the surviving occurrences of row `i`, as an order
embedding into the positions of the row. -/
def positionEmbedding (i : Fin p) :
    Fin (positiveRow iface face i).length ↪o Fin (row iface i).length :=
  Classical.choose (exists_positionEmbedding (iface := iface) (face := face) i)

/-- **The place in its row of the `m`-th surviving occurrence.** -/
def position (i : Fin p) (m : Fin (positiveRow iface face i).length) : ℕ :=
  ((positionEmbedding (iface := iface) (face := face) i m : Fin _) : ℕ)

theorem position_lt (i : Fin p) (m : Fin (positiveRow iface face i).length) :
    position (iface := iface) (face := face) i m < (row iface i).length :=
  (positionEmbedding (iface := iface) (face := face) i m).isLt

theorem getElem_position (i : Fin p) (m : Fin (positiveRow iface face i).length) :
    (row iface i)[position (iface := iface) (face := face) i m]'(position_lt i m) =
      (positiveRow iface face i)[(m : ℕ)] :=
  (Classical.choose_spec (exists_positionEmbedding (iface := iface) (face := face) i) m).symm

theorem position_lt_position_iff {i : Fin p}
    {m m' : Fin (positiveRow iface face i).length} :
    position (iface := iface) (face := face) i m <
        position (iface := iface) (face := face) i m' ↔ m < m' := by
  unfold position
  rw [← Fin.lt_def]
  exact (positionEmbedding i).lt_iff_lt

theorem position_le_position_iff {i : Fin p}
    {m m' : Fin (positiveRow iface face i).length} :
    position (iface := iface) (face := face) i m ≤
        position (iface := iface) (face := face) i m' ↔ m ≤ m' := by
  unfold position
  rw [← Fin.le_def]
  exact (positionEmbedding i).le_iff_le

theorem position_strictMono (i : Fin p) :
    StrictMono (position (iface := iface) (face := face) i) :=
  fun _ _ h ↦ position_lt_position_iff.mpr h

/-- The occurrence at a surviving position survives. -/
theorem sourceLength_position_pos (i : Fin p) (m : Fin (positiveRow iface face i).length) :
    0 < face.realization.sourceLength
      ((row iface i)[position (iface := iface) (face := face) i m]'(position_lt i m)) := by
  rw [getElem_position]
  exact (mem_positiveRow.mp (List.getElem_mem m.isLt)).2

/-- and every surviving position is one of them. -/
theorem exists_position_of_pos {i : Fin p} {k : ℕ} (hk : k < (row iface i).length)
    (hPos : 0 < face.realization.sourceLength (row iface i)[k]) :
    ∃ m : Fin (positiveRow iface face i).length,
      position (iface := iface) (face := face) i m = k := by
  have hMem : (row iface i)[k] ∈ positiveRow iface face i :=
    mem_positiveRow.mpr ⟨List.getElem_mem hk, hPos⟩
  obtain ⟨m, hm, hmEq⟩ := List.mem_iff_getElem.mp hMem
  refine ⟨⟨m, hm⟩, ?_⟩
  refine (List.Nodup.getElem_inj_iff (row_nodup (iface := iface) i)
    (hi := position_lt i ⟨m, hm⟩) (hj := hk)).mp ?_
  rw [getElem_position]
  exact hmEq

/-- A position that is no surviving position carries a contracted occurrence. -/
theorem sourceLength_eq_zero_of_forall_position_ne {i : Fin p} {k : ℕ}
    (hk : k < (row iface i).length)
    (hNe : ∀ m : Fin (positiveRow iface face i).length,
      position (iface := iface) (face := face) i m ≠ k) :
    face.realization.sourceLength (row iface i)[k] = 0 := by
  by_contra hPos
  obtain ⟨m, hm⟩ := exists_position_of_pos hk (Nat.pos_of_ne_zero hPos)
  exact hNe m hm

/-- Before the first surviving occurrence everything is contracted. -/
theorem sourceLength_eq_zero_of_lt_position_zero {i : Fin p} {k : ℕ}
    (hk : k < (row iface i).length) (m₀ : Fin (positiveRow iface face i).length)
    (hlt : k < position (iface := iface) (face := face) i m₀) (hFirst : (m₀ : ℕ) = 0) :
    face.realization.sourceLength (row iface i)[k] = 0 := by
  refine sourceLength_eq_zero_of_forall_position_ne hk fun m hm ↦ ?_
  have h : position (iface := iface) (face := face) i m <
      position (iface := iface) (face := face) i m₀ := by omega
  have := position_lt_position_iff.mp h
  rw [Fin.lt_def, hFirst] at this
  omega

/-- After the last surviving occurrence everything is contracted. -/
theorem sourceLength_eq_zero_of_position_last_lt {i : Fin p} {k : ℕ}
    (hk : k < (row iface i).length) (m₁ : Fin (positiveRow iface face i).length)
    (hlt : position (iface := iface) (face := face) i m₁ < k)
    (hLast : (m₁ : ℕ) + 1 = (positiveRow iface face i).length) :
    face.realization.sourceLength (row iface i)[k] = 0 := by
  refine sourceLength_eq_zero_of_forall_position_ne hk fun m hm ↦ ?_
  have h : position (iface := iface) (face := face) i m₁ <
      position (iface := iface) (face := face) i m := by omega
  have := position_lt_position_iff.mp h
  rw [Fin.lt_def] at this
  have := m.isLt
  omega

/-- Between two consecutive surviving occurrences everything is contracted. -/
theorem sourceLength_eq_zero_of_position_lt_of_lt_position {i : Fin p} {k : ℕ}
    (hk : k < (row iface i).length) (m₀ m₁ : Fin (positiveRow iface face i).length)
    (hSucc : (m₀ : ℕ) + 1 = (m₁ : ℕ))
    (hlt₀ : position (iface := iface) (face := face) i m₀ < k)
    (hlt₁ : k < position (iface := iface) (face := face) i m₁) :
    face.realization.sourceLength (row iface i)[k] = 0 := by
  refine sourceLength_eq_zero_of_forall_position_ne hk fun m hm ↦ ?_
  have h₀ : position (iface := iface) (face := face) i m₀ <
      position (iface := iface) (face := face) i m := by omega
  have h₁ : position (iface := iface) (face := face) i m <
      position (iface := iface) (face := face) i m₁ := by omega
  have := position_lt_position_iff.mp h₀
  have := position_lt_position_iff.mp h₁
  rw [Fin.lt_def] at *
  omega

/-- The place in its row of the occurrence carrying a kept slot. -/
def slotPosition (x : SlotIndex iface face) : ℕ := position (face := face) x.1 x.2

theorem slotPosition_lt (x : SlotIndex iface face) :
    slotPosition (face := face) x < (row iface x.1).length :=
  position_lt x.1 x.2

theorem occurrence_eq_getElem (x : SlotIndex iface face) :
    occurrence x = (row iface x.1)[slotPosition (face := face) x]'(slotPosition_lt x) :=
  (getElem_position x.1 x.2).symm

end Position

/-! ## 3.  The orientation flag -/

section Orientation

variable {iface : InputInterface spec strong.toPresentation coordinates F}

/-- Whether the row traverses the occurrence carrying the kept slot `x`
backwards, i.e. enters it at the second of its two named ends. -/
def reversedAt (x : SlotIndex iface face) : Bool :=
  if (candidate.datum.sourceEnds (occurrence x)).1 =
      rowWalk strong iface x.1 (slotPosition (face := face) x) then false else true

/-- **The first named end of the occurrence, located on the walk.** -/
theorem sourceEnds_occurrence_fst (x : SlotIndex iface face) :
    (candidate.datum.sourceEnds (occurrence x)).1 =
      rowWalk strong iface x.1
        (if reversedAt (strong := strong) x then slotPosition (face := face) x + 1
          else slotPosition (face := face) x) := by
  have hb := slotPosition_lt (iface := iface) (face := face) x
  by_cases hc : (candidate.datum.sourceEnds (occurrence x)).1 =
      rowWalk strong iface x.1 (slotPosition (face := face) x)
  · rw [show reversedAt (strong := strong) x = false from if_pos hc, if_neg (by simp)]
    exact hc
  · rw [show reversedAt (strong := strong) x = true from if_neg hc, if_pos rfl,
      rowWalk_succ hb, ← occurrence_eq_getElem x]
    unfold otherEnd
    rw [if_neg hc]

/-- **and the second.** -/
theorem sourceEnds_occurrence_snd (x : SlotIndex iface face) :
    (candidate.datum.sourceEnds (occurrence x)).2 =
      rowWalk strong iface x.1
        (if reversedAt (strong := strong) x then slotPosition (face := face) x
          else slotPosition (face := face) x + 1) := by
  have hb := slotPosition_lt (iface := iface) (face := face) x
  by_cases hc : (candidate.datum.sourceEnds (occurrence x)).1 =
      rowWalk strong iface x.1 (slotPosition (face := face) x)
  · rw [show reversedAt (strong := strong) x = false from if_pos hc, if_neg (by simp),
      rowWalk_succ hb, ← occurrence_eq_getElem x]
    unfold otherEnd
    rw [if_pos hc]
  · rw [show reversedAt (strong := strong) x = true from if_neg hc, if_pos rfl]
    have hInc := rowWalk_incident (strong := strong) (iface := iface) hb
    rw [← occurrence_eq_getElem x] at hInc
    rcases hInc with hCase | hCase
    · exact absurd hCase hc
    · exact hCase

end Orientation

/-! ## 4.  A forest row is contracted to a point -/

section Forest

variable {iface : InputInterface spec strong.toPresentation coordinates F}

/-- **Every vertex the walk meets along a forest row lies in one class.**  The
whole row is contracted (`InputRefinementData.sourceLength_eq_zero_of_mem_forest`),
so §1's confinement applies to the whole of it. -/
theorem classOf_rowWalk_eq_of_mem_forest
    (topology : ClearedFace.SourceContractionTopology face)
    {i : Fin p} (hi : i ∈ F) {k : ℕ} (hk : k ≤ (row iface i).length) :
    classOf topology (rowWalk strong iface i k) =
      classOf topology (strong.start (iface.slot i)) := by
  rw [← rowWalk_zero (strong := strong) (iface := iface) i]
  refine (classOf_rowWalk_eq_of_zero_run topology (Nat.zero_le k) hk fun j hj _ _ ↦ ?_).symm
  exact sourceLength_eq_zero_of_mem_forest iface face hi _ (List.getElem_mem hj)

/-- **and the two ends of a forest row are in the same class.**  No orientation
bit is needed: if the two ends are literally the same vertex there is nothing
to prove, and otherwise `rowWalk_length` applies.

This is the well-definedness clause of the requested core vertex map: the map of
the retained core model sends a requested core vertex to the contraction class
of *any* model core vertex above it, and the choice does not matter because the
model vertices above one requested vertex are joined by forest rows. -/
theorem classOf_finish_eq_classOf_start_of_mem_forest
    (topology : ClearedFace.SourceContractionTopology face)
    {i : Fin p} (hi : i ∈ F) :
    classOf topology (strong.finish (iface.slot i)) =
      classOf topology (strong.start (iface.slot i)) := by
  by_cases hEq : strong.finish (iface.slot i) = strong.start (iface.slot i)
  · rw [hEq]
  · rw [← rowWalk_length (strong := strong) (iface := iface) (Or.inr hEq)]
    exact classOf_rowWalk_eq_of_mem_forest topology hi le_rfl

/-- **A forest row's occurrences all lie in the one class too.** -/
theorem classOf_sourceEnds_eq_of_mem_forest
    (topology : ClearedFace.SourceContractionTopology face)
    {i : Fin p} (hi : i ∈ F) {edge : candidate.datum.SourceEdge}
    (hedge : edge ∈ row iface i) :
    classOf topology (candidate.datum.sourceEnds edge).1 =
      classOf topology (candidate.datum.sourceEnds edge).2 :=
  ClearedFace.SourceContractionTopology.classOf_eq_of_sourceLength_zero topology
    (sourceLength_eq_zero_of_mem_forest iface face hi edge hedge)

end Forest

/-! ## 5.  What is inhabited

No structure is introduced in this file: everything is a function of, or a
theorem about, `InputInterface`, `StrongPresentation` and `ClearedFace`.  The
two definitions `rowWalk` and `position` are total functions with no side
condition, and `reversedAt` is a `Bool`, so there is nothing to witness for
non-vacuity beyond the definitions themselves. -/

theorem rowWalk_zero' {iface : InputInterface spec strong.toPresentation coordinates F}
    (i : Fin p) : rowWalk strong iface i 0 = strong.start (iface.slot i) := rfl

end

end DraismaVargas.LocalCases.RetainedTraversal
