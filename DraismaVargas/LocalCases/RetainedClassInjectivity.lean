import DraismaVargas.LocalCases.ClassInjectivity
import DraismaVargas.LocalCases.RetainedVertexModel
import DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneLink

/-!
# The class half of the injectivity of the retained vertex map

**Source.**  A requested type is presented as a point of the closed cone of a
trivalent one, with zero length on the collapsed edges: Draisma--Vargas Part I
(arXiv:1909.12924), Section 5, in the proof of the main theorem.  Here the rows
of the expansion forest `F` are zero rows.  The marker cut used below, and the
transport of a pencil from the trivalent model back to the requested graph at an
exact integral scale, are written down in neither Draisma--Vargas paper, so, as
in `DraismaVargas.LocalCases.RetainedCut`, `RetainedStraddle` and
`RetainedVertexModel`, nothing here is a transcription of either paper.  The
`F = ∅` model of §1--§6 is `DraismaVargas.LocalCases.ClassInjectivity` §3--§4.

Below, "the Statement" is the theorem
`DraismaVargas.nonempty_evenSubdivisionPencil_ceil_half_genus_add_one` of
`DraismaVargas/Statement.lean`, and "the trivalent-model producer" is the
retained index of `RetainedIndexProducer`, which presents a requested core
through a trivalent (cubic) model.

## What is proved

`RetainedVertexModel` reduces the transport of a pencil from the trivalent model
back to the requested graph to **one statement** at every terminal face of the
trivalent-model producer: the hypothesis `hcls` of
`RetainedVertexModel.injective_vertexModel_of_inl` -- two refined core vertices
of the retained segment data sent to the same kept contraction class are equal.
**This file proves it.**

* §1 is `ClassInjectivity` §3 at a **general forest**: a surviving valency-two
  vertex carries only two surviving occurrences, so distinct interior positions
  of the retained rows give distinct quotient-source vertices
  (`eq_of_incident_interior`, `rowWalk_interior_inj`,
  `rowWalk_interior_row_eq`, `interior_eq`), and the row ends are excluded
  because `IsPathEnd` forbids valency two there.  Nothing in it reads the
  interface's row totals, so it is forest-independent; it is re-proved rather
  than reused because `ClassInjectivity` is typed at `F = ∅`.

* §2--§5 are `ClassInjectivity` §4 at a general forest.  `IsGap` names a **zero
  run** of a retained row -- two surviving places with nothing surviving
  strictly between -- and `NearGap` the vertices it reaches; `NearPlace` and
  `NearClass` name the zero runs around a placement and around a whole
  `ForestClosed` set of placements.  `nearGap_step` and `nearClass_step` are
  the two closure lemmas, and `not_nearClass_of_nearGap`, `mem_of_nearClass`
  and `nearGap_eq` the three separations.  **The one forest-sensitive step** of
  the `F = ∅` argument -- "a zero run can never traverse a whole row, because
  every row carries a surviving occurrence" -- is false on a forest row, and is
  replaced by `RetainedCut.positiveRow_ne_nil_of_not_mem_forest` together with
  the observation that a row a zero run *does* traverse whole is a forest row,
  whose two ends are placements of one forest class (`ForestClosed`).  The
  pendant-excursion lemmas of `ClassInjectivity` §4 mention no interface and are
  reused, not copied: §5's `reflTransGen_of_classOf_eq` is
  `ClassInjectivity.reflTransGen_survivingZeroStep_of_reflTransGen_zeroStep`
  (which is where `exists_step_avoiding_set`,
  `nonDanglingValency_eq_zero_of_danglingSide` and
  `nonDanglingValency_eq_zero_of_mem_side` do their work) composed with
  `ClassInjectivity.reflTransGen_zeroStep_of_classOf_eq`.  Taking `NearClass`
  over a whole `ForestClosed` set of placements is what makes the fibre classes
  well defined here, so neither
  `RetainedTraversal.classOf_finish_eq_classOf_start_of_mem_forest` nor
  `RetainedFibre.coreClass_eq_of_fib_eq` is needed: what is used instead is
  `ExpansionData.SlotCompatible`'s contracted clause, as `forestClosed_fib`.

* §6 packages the three collisions on the source: `gap_collision`,
  `not_class_collision`, `class_collision`.

* §7 specializes to the trivalent-model producer.  `clsSource` is the
  quotient-source vertex a
  class-valued refined core vertex sits on -- any placement of its fibre for a
  non-marker requested core vertex, the occurrence boundary the handover names
  for an **aligned** marker, the vertex just after the piece it follows for a
  breakpoint -- and `cutVertex_eq_cutLeft` says the kept class a refined core
  vertex lands on is the class of that vertex.  `forestClosed_fib` is
  `ExpansionData.SlotCompatible`'s first clause: a forest row does not separate
  two fibres.  The two clauses with no `F = ∅` analogue are
  `blockSlot_handover_ne_zero` (an aligned marker's kept slot is not the first
  of its row, so its walk vertex is strictly inside the row and has surviving
  valency two, while `Spanning` puts every fibre class at a row end) and
  `retPos_succ_ne_offset_one` with `marker_ne_break` (a marker and a breakpoint
  never sit at one piece boundary: the marker is the first block boundary of
  the retained refinement, a breakpoint of the first requested slot the row
  carries is strictly below it and one of the second is at or above it).

* §8 assembles `classInjective` -- the hypothesis `hcls` -- and hence
  `injective_vertexModel`.

* §9 feeds it back: `cutRelabeling_of_expansion` is the retained relabeling
  with **no** hypothesis, `nonempty_evenSubdivisionPencil_of_link` is the
  Statement's conclusion from the walk's type-change `link` alone, and
  `nonempty_evenSubdivisionPencil` is the Statement's conclusion from its four
  binders alone, obtained by feeding `NonTrivalentValencyTwoBaseOneLink.link_all`,
  which supplies the `link` binder with no hypothesis.  Its binders and
  conclusion are
  `DraismaVargas.nonempty_evenSubdivisionPencil_ceil_half_genus_add_one`'s,
  binder for binder.

## Hypotheses left explicit here

1. **None** in `nonempty_evenSubdivisionPencil`: it has the Statement's four
   binders and no receipt.  `classInjective`, `injective_vertexModel` and the
   two conditional statements keep exactly what
   `RetainedRelabeling.CutRelabeling` already keeps inside its binder --
   `hCond` (the producer's own output), the core dictionary, `Faithful` and
   `Spanning` -- plus, for `nonempty_evenSubdivisionPencil_of_link`, the
   type-change `link`.  `Connected` and `SourceGenusMatches` are carried by the
   binder but are not used by this file's proofs.
2. This file does not import `DraismaVargas/Statement.lean`; that file proves
   the Statement from `nonempty_evenSubdivisionPencil`.
3. Nothing about a *straddling* marker's image is needed here:
   `RetainedVertexModel.eq_of_cutVertex_inr` already handles the new split
   vertices, and `not_straddles_of_inl` shows a marker that lands on a kept
   class is aligned.

## Consumers

`RetainedRelabeling.CutRelabeling` at the trivalent-model producer (through
`cutRelabeling_of_expansion`), and the Statement,
`DraismaVargas.nonempty_evenSubdivisionPencil_ceil_half_genus_add_one`, which
`DraismaVargas/Statement.lean` proves from `nonempty_evenSubdivisionPencil`.
-/
namespace DraismaVargas.LocalCases.RetainedClassInjectivity

noncomputable section

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.IteratedSplitRefinement
open Utilities.Subdivision.CoreExpansion
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.BlockSplitCount
open DraismaVargas.Infrastructure.FlattenIndex
open DraismaVargas.Infrastructure.OccurrenceCut
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.OrientedTraversal
open DraismaVargas.LocalCases.RefinementCore
open DraismaVargas.LocalCases.RequestedExpandedEndpoints
open DraismaVargas.LocalCases.RetainedCoreModel
open DraismaVargas.LocalCases.RetainedCut
open DraismaVargas.LocalCases.RetainedRelabeling
open DraismaVargas.LocalCases.RetainedRowPieces
open DraismaVargas.LocalCases.RetainedStraddle
open DraismaVargas.LocalCases.RetainedVertexModel
open DraismaVargas.LocalCases.SlotRefinement
open DraismaVargas.LocalCases.StrongRefinement
open DraismaVargas.LocalCases.TraversalPresentation
open DraismaVargas.LocalCases.W4StableSource

variable {target : CFGraph} {degree : ℕ}
  {gluing : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree gluing wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ}
  {strong : StrongPresentation candidate.datum coordinate}
  {face : ClearedFace candidate strong.toPresentation coordinates}

/-! ## 1.  `ClassInjectivity` §3 at a general forest -/

section Interior

variable {n p : ℕ} {spec : SubdivisionGraph.Spec n p} {F : Finset (Fin p)}
  {iface : InputInterface spec strong.toPresentation coordinates F}

/-- **Only the two occurrences the walk joins there meet an interior walk
vertex.**  `ClassInjectivity.eq_of_incident_interior` at a general forest: the
proof reads only `PresentationDecomposition.Decomposes` and the path-end
fields, never the interface's row totals. -/
theorem eq_of_incident_interior {i : Fin p} {k : ℕ}
    (hk : k + 1 < (row iface i).length)
    {e : candidate.datum.SourceEdge} (he : ¬ IsDangling candidate.datum e)
    (hInc : Incident candidate.datum e (RetainedTraversal.rowWalk strong iface i (k + 1))) :
    e = (row iface i)[k] ∨ e = (row iface i)[k + 1] := by
  by_contra hContra
  obtain ⟨hNe1, hNe2⟩ := not_or.mp hContra
  have hklt : k < (row iface i).length := Nat.lt_of_succ_lt hk
  have hEdgeNe : (row iface i)[k] ≠ (row iface i)[k + 1] := by
    intro hEq
    exact absurd ((RetainedTraversal.row_nodup (iface := iface) i).getElem_inj_iff.mp hEq)
      (by omega)
  exact ClassInjectivity.not_three_incident
    (RetainedTraversal.nonDanglingValency_rowWalk_succ hk) hNe1 hNe2 hEdgeNe he
    (RetainedTraversal.row_survives i _ (List.getElem_mem hklt))
    (RetainedTraversal.row_survives i _ (List.getElem_mem hk))
    hInc (RetainedTraversal.rowWalk_succ_incident hklt)
    (RetainedTraversal.rowWalk_incident hk)

/-- **Distinct interior positions of one row give distinct vertices.** -/
theorem rowWalk_interior_inj {i : Fin p} {k l : ℕ}
    (hk : k + 1 < (row iface i).length) (hl : l + 1 < (row iface i).length)
    (hEq : RetainedTraversal.rowWalk strong iface i (k + 1) =
      RetainedTraversal.rowWalk strong iface i (l + 1)) : k = l := by
  have hllt : l < (row iface i).length := Nat.lt_of_succ_lt hl
  have hFirst := eq_of_incident_interior hk
    (RetainedTraversal.row_survives i _ (List.getElem_mem hllt))
    (hEq ▸ RetainedTraversal.rowWalk_succ_incident (strong := strong) (iface := iface) hllt)
  have hSecond := eq_of_incident_interior hk
    (RetainedTraversal.row_survives i _ (List.getElem_mem hl))
    (hEq ▸ RetainedTraversal.rowWalk_incident (strong := strong) (iface := iface) hl)
  have hIndex : ∀ {a b : ℕ} (_ha : a < (row iface i).length)
      (_hb : b < (row iface i).length),
      (row iface i)[a] = (row iface i)[b] → a = b :=
    fun _ha _hb hab ↦ (RetainedTraversal.row_nodup (iface := iface) i).getElem_inj_iff.mp hab
  have hIdx1 : l = k ∨ l = k + 1 := by
    rcases hFirst with h | h
    · exact Or.inl (hIndex hllt (Nat.lt_of_succ_lt hk) h)
    · exact Or.inr (hIndex hllt hk h)
  have hIdx2 : l + 1 = k ∨ l + 1 = k + 1 := by
    rcases hSecond with h | h
    · exact Or.inl (hIndex hl (Nat.lt_of_succ_lt hk) h)
    · exact Or.inr (hIndex hl hk h)
  omega

/-- **Distinct rows give distinct interior vertices.** -/
theorem rowWalk_interior_row_eq {i j : Fin p} {k l : ℕ}
    (hk : k + 1 < (row iface i).length) (hl : l + 1 < (row iface j).length)
    (hEq : RetainedTraversal.rowWalk strong iface i (k + 1) =
      RetainedTraversal.rowWalk strong iface j (l + 1)) : i = j := by
  by_contra hNe
  have hllt : l < (row iface j).length := Nat.lt_of_succ_lt hl
  have hMem : (row iface j)[l] ∈ row iface j := List.getElem_mem hllt
  have hIn := eq_of_incident_interior hk (RetainedTraversal.row_survives j _ hMem)
    (hEq ▸ RetainedTraversal.rowWalk_succ_incident (strong := strong) (iface := iface) hllt)
  refine strong.decomposes.disjoint (iface.slot i) (iface.slot j)
    (fun hSlot ↦ hNe (iface.slot.injective hSlot)) ((row iface j)[l]) ?_ hMem
  rcases hIn with hIn | hIn
  · exact hIn ▸ List.getElem_mem (Nat.lt_of_succ_lt hk)
  · exact hIn ▸ List.getElem_mem hk

/-- **An interior walk vertex determines its row and its position.** -/
theorem interior_eq {i j : Fin p} {k l : ℕ} (hk : 0 < k) (hk' : k < (row iface i).length)
    (hl : 0 < l) (hl' : l < (row iface j).length)
    (hEq : RetainedTraversal.rowWalk strong iface i k =
      RetainedTraversal.rowWalk strong iface j l) : i = j ∧ k = l := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have hij : i = j := rowWalk_interior_row_eq hk' hl' hEq
  subst hij
  exact ⟨rfl, congrArg (· + 1) (rowWalk_interior_inj hk' hl' hEq)⟩

/-- The two ends of a displayed row are path ends: neither has surviving
valency two. -/
theorem start_valency_ne_two (i : Fin p) :
    nonDanglingValency candidate.datum (strong.start (iface.slot i)) ≠ 2 :=
  (RetainedTraversal.row_head_isPathEnd (iface := iface) i
    (RetainedTraversal.row_length_pos (iface := iface) i)).2

theorem finish_valency_ne_two (i : Fin p) :
    nonDanglingValency candidate.datum (strong.finish (iface.slot i)) ≠ 2 :=
  (RetainedTraversal.row_getLast_isPathEnd (iface := iface) i
    (RetainedTraversal.row_length_pos (iface := iface) i)).2

/-- A walk position carrying a vertex of surviving valency `≠ 2` is a row
end. -/
theorem eq_zero_or_eq_length_of_valency_ne_two {j : Fin p} {t : ℕ}
    (ht : t ≤ (row iface j).length)
    (hVal : nonDanglingValency candidate.datum
      (RetainedTraversal.rowWalk strong iface j t) ≠ 2) :
    t = 0 ∨ t = (row iface j).length := by
  by_contra hContra
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  exact hVal (RetainedTraversal.nonDanglingValency_rowWalk_succ (by omega))

/-- A spanning placement lands only on row ends, so never on an interior
vertex of a walk. -/
theorem vertexAt_valency_ne_two (dict : CoreDictionary spec strong iface)
    (hSpan : Spanning dict) (v : Fin n) :
    nonDanglingValency candidate.datum (dict.vertexAt v) ≠ 2 := by
  rcases hSpan v with ⟨i, hi⟩ | ⟨i, hi⟩
  · rw [show dict.vertexAt v = strong.start (iface.slot i) from hi]
    exact start_valency_ne_two i
  · rw [show dict.vertexAt v = strong.finish (iface.slot i) from hi]
    exact finish_valency_ne_two i

/-- and it still meets a surviving occurrence. -/
theorem vertexAt_valency_ne_zero (dict : CoreDictionary spec strong iface)
    (hSpan : Spanning dict) (v : Fin n) :
    nonDanglingValency candidate.datum (dict.vertexAt v) ≠ 0 := by
  rcases hSpan v with ⟨i, hi⟩ | ⟨i, hi⟩
  · rw [show dict.vertexAt v = strong.start (iface.slot i) from hi]
    exact (RetainedVertexModel.nonDanglingValency_start_pos iface i).ne'
  · rw [show dict.vertexAt v = strong.finish (iface.slot i) from hi]
    exact (RetainedVertexModel.nonDanglingValency_finish_pos iface i).ne'

end Interior

/-! ## 2.  The zero runs of a retained row -/

section Gap

variable {n p : ℕ} {spec : SubdivisionGraph.Spec n p} {F : Finset (Fin p)}
  {iface : InputInterface spec strong.toPresentation coordinates F}

/-- **A zero run of the row `i`.**  `lo` and `hi` are the places of two
surviving occurrences of the row, `lo` comes first, and no surviving occurrence
lies strictly between them: everything the walk meets between the two is
contracted. -/
def IsGap (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (i : Fin p) (lo hi : ℕ) : Prop :=
  (∃ m : Fin (positiveRow iface face i).length,
      RetainedTraversal.position (iface := iface) (face := face) i m = lo) ∧
  (∃ m : Fin (positiveRow iface face i).length,
      RetainedTraversal.position (iface := iface) (face := face) i m = hi) ∧
  lo < hi ∧
  ∀ m : Fin (positiveRow iface face i).length,
    RetainedTraversal.position (iface := iface) (face := face) i m ≤ lo ∨
      hi ≤ RetainedTraversal.position (iface := iface) (face := face) i m

/-- **Consecutive surviving occurrences bound a zero run.** -/
theorem isGap_succ {i : Fin p} {m m' : Fin (positiveRow iface face i).length}
    (hmm : (m : ℕ) + 1 = (m' : ℕ)) :
    IsGap iface face i (RetainedTraversal.position (iface := iface) (face := face) i m)
      (RetainedTraversal.position (iface := iface) (face := face) i m') := by
  refine ⟨⟨m, rfl⟩, ⟨m', rfl⟩,
    RetainedTraversal.position_lt_position_iff.mpr (by rw [Fin.lt_def]; omega), fun m'' ↦ ?_⟩
  by_cases h : (m'' : ℕ) ≤ (m : ℕ)
  · exact Or.inl (RetainedTraversal.position_le_position_iff.mpr (by rw [Fin.le_def]; omega))
  · exact Or.inr (RetainedTraversal.position_le_position_iff.mpr (by rw [Fin.le_def]; omega))

theorem isGap_hi_lt {i : Fin p} {lo hi : ℕ} (h : IsGap iface face i lo hi) :
    hi < (row iface i).length := by
  obtain ⟨-, ⟨m, hm⟩, -, -⟩ := h
  exact hm ▸ RetainedTraversal.position_lt (iface := iface) (face := face) i m

theorem isGap_lo_lt {i : Fin p} {lo hi : ℕ} (h : IsGap iface face i lo hi) :
    lo < (row iface i).length := lt_trans h.2.2.1 (isGap_hi_lt h)

/-- **The occurrence at the foot of a zero run survives.** -/
theorem isGap_sourceLength_lo_pos {i : Fin p} {lo hi : ℕ} (h : IsGap iface face i lo hi) :
    0 < face.realization.sourceLength ((row iface i)[lo]'(isGap_lo_lt h)) := by
  obtain ⟨m, hm⟩ := h.1
  subst hm
  exact RetainedTraversal.sourceLength_position_pos (iface := iface) (face := face) i m

/-- and so does the occurrence at its head. -/
theorem isGap_sourceLength_hi_pos {i : Fin p} {lo hi : ℕ} (h : IsGap iface face i lo hi) :
    0 < face.realization.sourceLength ((row iface i)[hi]'(isGap_hi_lt h)) := by
  obtain ⟨m, hm⟩ := h.2.1
  subst hm
  exact RetainedTraversal.sourceLength_position_pos (iface := iface) (face := face) i m

/-- **Everything strictly inside a zero run is contracted.** -/
theorem isGap_sourceLength_eq_zero {i : Fin p} {lo hi : ℕ} (h : IsGap iface face i lo hi)
    {k : ℕ} (hk : k < (row iface i).length) (h1 : lo < k) (h2 : k < hi) :
    face.realization.sourceLength (row iface i)[k] = 0 := by
  refine RetainedTraversal.sourceLength_eq_zero_of_forall_position_ne hk fun m hm ↦ ?_
  rcases h.2.2.2 m with hle | hle <;> omega

/-- **Two zero runs of one row that share a point are the same run.** -/
theorem isGap_unique {i : Fin p} {lo hi lo' hi' k : ℕ} (h : IsGap iface face i lo hi)
    (h' : IsGap iface face i lo' hi') (hk1 : lo < k) (hk2 : k ≤ hi)
    (hk1' : lo' < k) (hk2' : k ≤ hi') : lo = lo' ∧ hi = hi' := by
  obtain ⟨⟨mlo, hmlo⟩, ⟨mhi, hmhi⟩, -, hmid⟩ := h
  obtain ⟨⟨mlo', hmlo'⟩, ⟨mhi', hmhi'⟩, -, hmid'⟩ := h'
  have e1 := hmid mlo'
  have e2 := hmid mhi'
  have e3 := hmid' mlo
  have e4 := hmid' mhi
  rw [hmlo'] at e1
  rw [hmhi'] at e2
  rw [hmlo] at e3
  rw [hmhi] at e4
  omega

/-- **The vertices a zero run reaches** from the surviving occurrence at its
head, walking backwards to just after the one at its foot. -/
def NearGap (iface : InputInterface spec strong.toPresentation coordinates F)
    (i : Fin p) (lo hi : ℕ) (a : candidate.datum.SourceVertex) : Prop :=
  ∃ k : ℕ, lo < k ∧ k ≤ hi ∧ a = RetainedTraversal.rowWalk strong iface i k

theorem nearGap_interior {i : Fin p} {lo hi : ℕ} (h : IsGap iface face i lo hi)
    {a : candidate.datum.SourceVertex} (ha : NearGap iface i lo hi a) :
    ∃ k : ℕ, 0 < k ∧ k < (row iface i).length ∧
      a = RetainedTraversal.rowWalk strong iface i k := by
  obtain ⟨k, hk1, hk2, hk3⟩ := ha
  exact ⟨k, by omega, by have := isGap_hi_lt h; omega, hk3⟩

/-- A vertex a zero run reaches has surviving valency two. -/
theorem nonDanglingValency_of_nearGap {i : Fin p} {lo hi : ℕ}
    (h : IsGap iface face i lo hi) {a : candidate.datum.SourceVertex}
    (ha : NearGap iface i lo hi a) :
    nonDanglingValency candidate.datum a = 2 := by
  obtain ⟨k, hk0, hk1, rfl⟩ := nearGap_interior h ha
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact RetainedTraversal.nonDanglingValency_rowWalk_succ hk1

end Gap

/-! ## 3.  A surviving zero step moves one place along a row -/

section Step

variable {n p : ℕ} {spec : SubdivisionGraph.Spec n p} {F : Finset (Fin p)}
  {iface : InputInterface spec strong.toPresentation coordinates F}

/-- **A surviving zero step, located on the row of its occurrence.**
`ClassInjectivity.step_along_row` at a general forest. -/
theorem step_along_row {a b : candidate.datum.SourceVertex}
    (hStep : ClassInjectivity.SurvivingZeroStep face a b) :
    ∃ (j : Fin p) (t : ℕ) (_ : t < (row iface j).length),
      face.realization.sourceLength (row iface j)[t] = 0 ∧
        ((a = RetainedTraversal.rowWalk strong iface j t ∧
            b = RetainedTraversal.rowWalk strong iface j (t + 1)) ∨
          (a = RetainedTraversal.rowWalk strong iface j (t + 1) ∧
            b = RetainedTraversal.rowWalk strong iface j t)) := by
  obtain ⟨e, hSurvives, hZero, hEnds⟩ := hStep
  obtain ⟨r, hr⟩ := strong.decomposes.surviving_mem e hSurvives
  have hMem : e ∈ row iface (iface.slot.symm r) := by
    show e ∈ strong.toPresentation.path (iface.slot (iface.slot.symm r))
    rw [Equiv.apply_symm_apply]; exact hr
  obtain ⟨t, ht, hte⟩ := List.mem_iff_getElem.mp hMem
  refine ⟨iface.slot.symm r, t, ht, by rw [hte]; exact hZero, ?_⟩
  have hb : b = otherEnd candidate.datum e a :=
    (ClassInjectivity.otherEnd_eq_of_sourceEnds hEnds).symm
  have hInc : Incident candidate.datum e a := ClassInjectivity.incident_fst_of_sourceEnds hEnds
  rw [← hte] at hb hInc
  rcases eq_or_eq_otherEnd candidate.datum
    (RetainedTraversal.rowWalk_incident (strong := strong) (iface := iface) ht) hInc with
    hCase | hCase
  · refine Or.inl ⟨hCase, ?_⟩
    rw [hb, hCase, RetainedTraversal.rowWalk_succ ht]
  · refine Or.inr ⟨by rw [hCase, RetainedTraversal.rowWalk_succ ht], ?_⟩
    rw [hb, hCase, ClassInjectivity.otherEnd_otherEnd
      (RetainedTraversal.rowWalk_incident (strong := strong) (iface := iface) ht)]

/-- An interior walk vertex is the start of no displayed row. -/
theorem ne_start_of_interior {i j : Fin p} {k : ℕ} (hk : 0 < k)
    (hk' : k < (row iface i).length) :
    RetainedTraversal.rowWalk strong iface i k ≠ strong.start (iface.slot j) := by
  intro hEq
  refine start_valency_ne_two (iface := iface) j ?_
  rw [← hEq]
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact RetainedTraversal.nonDanglingValency_rowWalk_succ hk'

/-- nor the finish of one. -/
theorem ne_finish_of_interior {i j : Fin p} {k : ℕ} (hk : 0 < k)
    (hk' : k < (row iface i).length) :
    RetainedTraversal.rowWalk strong iface i k ≠ strong.finish (iface.slot j) := by
  intro hEq
  refine finish_valency_ne_two (iface := iface) j ?_
  rw [← hEq]
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact RetainedTraversal.nonDanglingValency_rowWalk_succ hk'

/-- nor a spanning placement. -/
theorem ne_vertexAt_of_interior (dict : CoreDictionary spec strong iface)
    (hSpan : Spanning dict) {i : Fin p} {k : ℕ} {w : Fin n} (hk : 0 < k)
    (hk' : k < (row iface i).length) :
    RetainedTraversal.rowWalk strong iface i k ≠ dict.vertexAt w := by
  intro hEq
  refine vertexAt_valency_ne_two dict hSpan w ?_
  rw [← hEq]
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact RetainedTraversal.nonDanglingValency_rowWalk_succ hk'

/-- A contracted place of a row is no surviving place of it. -/
theorem position_ne_of_sourceLength_zero {j : Fin p} {t : ℕ} (ht : t < (row iface j).length)
    (hz : face.realization.sourceLength (row iface j)[t] = 0)
    (m : Fin (positiveRow iface face j).length) :
    RetainedTraversal.position (iface := iface) (face := face) j m ≠ t := by
  intro h
  subst h
  have := RetainedTraversal.sourceLength_position_pos (iface := iface) (face := face) j m
  omega

/-- **The zero runs are closed under surviving zero steps.** -/
theorem nearGap_step (dict : CoreDictionary spec strong iface) (hF : Faithful dict)
    {i : Fin p} {lo hi : ℕ} (hGap : IsGap iface face i lo hi)
    {a b : candidate.datum.SourceVertex} (ha : NearGap iface i lo hi a)
    (hStep : ClassInjectivity.SurvivingZeroStep face a b) : NearGap iface i lo hi b := by
  obtain ⟨j, t, ht, hZero, hCross⟩ := step_along_row (iface := iface) hStep
  obtain ⟨k, hk1, hk2, rfl⟩ := ha
  have hkpos : 0 < k := by omega
  have hklt : k < (row iface i).length := by have := isGap_hi_lt hGap; omega
  rcases hCross with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · have ht0 : 0 < t := by
      by_contra h0
      exact ne_start_of_interior (j := j) hkpos hklt
        (by rw [hA, show t = 0 by omega]; rfl)
    obtain ⟨hij, hkt⟩ := interior_eq hkpos hklt ht0 ht hA
    subst hij
    refine ⟨k + 1, by omega, ?_, by rw [hB, hkt]⟩
    obtain ⟨m, hm⟩ := hGap.2.1
    have hne : RetainedTraversal.position (iface := iface) (face := face) i m ≠ t :=
      position_ne_of_sourceLength_zero ht hZero m
    omega
  · have ht1 : t + 1 < (row iface j).length := by
      by_contra h1
      refine ne_finish_of_interior (j := j) hkpos hklt ?_
      rw [hA, show t + 1 = (row iface j).length by omega,
        RetainedVertexModel.rowWalk_length_of_faithful dict hF j]
    obtain ⟨hij, hkt⟩ := interior_eq hkpos hklt (Nat.succ_pos t) ht1 hA
    subst hij
    refine ⟨t, ?_, by omega, hB⟩
    obtain ⟨m, hm⟩ := hGap.1
    have hne : RetainedTraversal.position (iface := iface) (face := face) i m ≠ t :=
      position_ne_of_sourceLength_zero ht hZero m
    omega

end Step

/-! ## 4.  The zero runs around a placement, and the forest classes -/

section Place

variable {n p : ℕ} {spec : SubdivisionGraph.Spec n p} {F : Finset (Fin p)}
  {iface : InputInterface spec strong.toPresentation coordinates F}

/-- A retained row carries a surviving occurrence, hence a surviving place.
This is `RetainedCut.positiveRow_ne_nil_of_not_mem_forest`, the general-forest
replacement of `OrientedTraversal.RowDictionary.positiveRow_ne_nil`. -/
theorem exists_place_of_not_mem_forest {j : Fin p} (hj : j ∉ F) :
    Nonempty (Fin (positiveRow iface face j).length) :=
  ⟨⟨0, List.length_pos_of_ne_nil (positiveRow_ne_nil_of_not_mem_forest (iface := iface)
    (face := face) hj)⟩⟩

/-- **and therefore a row with no surviving place is a forest row.** -/
theorem mem_forest_of_no_place {j : Fin p}
    (h : IsEmpty (Fin (positiveRow iface face j).length)) : j ∈ F := by
  by_contra hj
  obtain ⟨m⟩ := exists_place_of_not_mem_forest (iface := iface) (face := face) hj
  exact h.false m

/-- **The vertices a zero run reaches from a placement** without crossing a
surviving occurrence: the placement itself, the initial runs of the rows
starting there and the final runs of the rows ending there. -/
def NearPlace (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (u a : candidate.datum.SourceVertex) : Prop :=
  a = u ∨
  (∃ (j : Fin p) (k : ℕ), strong.start (iface.slot j) = u ∧ 0 < k ∧
      k < (row iface j).length ∧
      (∀ m : Fin (positiveRow iface face j).length,
        k ≤ RetainedTraversal.position (iface := iface) (face := face) j m) ∧
      a = RetainedTraversal.rowWalk strong iface j k) ∨
  (∃ (j : Fin p) (k : ℕ), strong.finish (iface.slot j) = u ∧ 0 < k ∧
      k < (row iface j).length ∧
      (∀ m : Fin (positiveRow iface face j).length,
        RetainedTraversal.position (iface := iface) (face := face) j m < k) ∧
      a = RetainedTraversal.rowWalk strong iface j k)

/-- **A set of stable core vertices closed under the forest rows.** -/
def ForestClosed (spec : SubdivisionGraph.Spec n p) (F : Finset (Fin p))
    (S : Set (Fin n)) : Prop :=
  ∀ j ∈ F, (spec.core.tail j ∈ S ↔ spec.core.head j ∈ S)

/-- **The zero-run neighbourhood of a whole forest class of placements.** -/
def NearClass (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (dict : CoreDictionary spec strong iface) (S : Set (Fin n))
    (a : candidate.datum.SourceVertex) : Prop :=
  ∃ u : Fin n, u ∈ S ∧ NearPlace iface face (dict.vertexAt u) a

theorem nearClass_self (dict : CoreDictionary spec strong iface) {S : Set (Fin n)}
    {u : Fin n} (hu : u ∈ S) : NearClass iface face dict S (dict.vertexAt u) :=
  ⟨u, hu, Or.inl rfl⟩

/-- **The forest class neighbourhoods are closed under surviving zero steps.**

The one forest-sensitive step of `ClassInjectivity` §4: at the empty forest a
zero run can never traverse a whole row, because every row carries a surviving
occurrence.  At a general forest a *forest* row is traversed whole, and the
placement at its far end is in the same forest class, which is what
`ForestClosed` records. -/
theorem nearClass_step (dict : CoreDictionary spec strong iface) (hF : Faithful dict)
    (hSpan : Spanning dict) {S : Set (Fin n)} (hClosed : ForestClosed spec F S)
    {a b : candidate.datum.SourceVertex} (ha : NearClass iface face dict S a)
    (hStep : ClassInjectivity.SurvivingZeroStep face a b) :
    NearClass iface face dict S b := by
  obtain ⟨j, t, ht, hZero, hCross⟩ := step_along_row (iface := iface) hStep
  obtain ⟨u, huS, hplace⟩ := ha
  have hzeroPos : ∀ m : Fin (positiveRow iface face j).length,
      RetainedTraversal.position (iface := iface) (face := face) j m ≠ t :=
    position_ne_of_sourceLength_zero ht hZero
  have hfin : ∀ i : Fin p, RetainedTraversal.rowWalk strong iface i (row iface i).length =
      strong.finish (iface.slot i) :=
    fun i ↦ RetainedVertexModel.rowWalk_length_of_faithful dict hF i
  rcases hplace with rfl | ⟨j', k, hstart, hkpos, hklt, hle, rfl⟩ | ⟨j', k, hfinish, hkpos,
    hklt, hlt, rfl⟩
  · -- at the placement itself
    have hVal : ∀ s : ℕ, dict.vertexAt u = RetainedTraversal.rowWalk strong iface j s →
        s ≤ (row iface j).length → s = 0 ∨ s = (row iface j).length := by
      intro s hs hsle
      refine eq_zero_or_eq_length_of_valency_ne_two hsle ?_
      rw [← hs]
      exact vertexAt_valency_ne_two dict hSpan u
    rcases hCross with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · have ht0 : t = 0 := by rcases hVal t hA ht.le with h | h <;> omega
      subst ht0
      by_cases hlen : 1 < (row iface j).length
      · exact ⟨u, huS, Or.inr (Or.inl ⟨j, 1, hA.symm, Nat.one_pos, hlen,
          fun m ↦ by have := hzeroPos m; omega, hB⟩)⟩
      · have hlen1 : (row iface j).length = 1 := by
          have := RetainedTraversal.row_length_pos (iface := iface) j; omega
        have hjF : j ∈ F := mem_forest_of_no_place (iface := iface) (face := face)
          ⟨fun m ↦ by
            have h1 := RetainedTraversal.position_lt (iface := iface) (face := face) j m
            have h2 := hzeroPos m
            omega⟩
        have hu : spec.core.tail j = u := hF (by rw [dict.tail_eq j]; exact hA.symm)
        refine ⟨spec.core.head j, (hClosed j hjF).mp (by rw [hu]; exact huS), Or.inl ?_⟩
        rw [hB, dict.head_eq j, ← hfin j, hlen1]
    · have ht1 : t + 1 = (row iface j).length := by
        rcases hVal (t + 1) hA (by omega) with h | h <;> omega
      have hufin : strong.finish (iface.slot j) = dict.vertexAt u := by
        rw [← hfin j, ← ht1, ← hA]
      by_cases ht0 : 0 < t
      · exact ⟨u, huS, Or.inr (Or.inr ⟨j, t, hufin, ht0, ht,
          fun m ↦ by
            have h1 := RetainedTraversal.position_lt (iface := iface) (face := face) j m
            have h2 := hzeroPos m
            omega, hB⟩)⟩
      · have hlen1 : (row iface j).length = 1 := by omega
        have hjF : j ∈ F := mem_forest_of_no_place (iface := iface) (face := face)
          ⟨fun m ↦ by
            have h1 := RetainedTraversal.position_lt (iface := iface) (face := face) j m
            have h2 := hzeroPos m
            omega⟩
        have hu : spec.core.head j = u := hF (by rw [dict.head_eq j, hufin])
        refine ⟨spec.core.tail j, (hClosed j hjF).mpr (by rw [hu]; exact huS), Or.inl ?_⟩
        rw [hB, dict.tail_eq j, show t = 0 by omega]
        rfl
  · -- on the initial run of a row starting at the placement
    rcases hCross with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · have ht0 : 0 < t := by
        by_contra h0
        exact ne_start_of_interior (iface := iface) (j := j) hkpos hklt
          (by rw [hA, show t = 0 by omega]; rfl)
      obtain ⟨hjj, hkt⟩ := interior_eq hkpos hklt ht0 ht hA
      subst hjj
      have hlek : ∀ m : Fin (positiveRow iface face j').length,
          k + 1 ≤ RetainedTraversal.position (iface := iface) (face := face) j' m := by
        intro m
        have h1 := hle m
        have h2 := hzeroPos m
        omega
      by_cases hlen : k + 1 < (row iface j').length
      · exact ⟨u, huS, Or.inr (Or.inl ⟨j', k + 1, hstart, by omega, hlen, hlek,
          by rw [hB, hkt]⟩)⟩
      · have hlen1 : k + 1 = (row iface j').length := by omega
        have hjF : j' ∈ F := mem_forest_of_no_place (iface := iface) (face := face)
          ⟨fun m ↦ by
            have h1 := RetainedTraversal.position_lt (iface := iface) (face := face) j' m
            have h2 := hlek m
            omega⟩
        have hu : spec.core.tail j' = u := hF (by rw [dict.tail_eq j', hstart])
        refine ⟨spec.core.head j', (hClosed j' hjF).mp (by rw [hu]; exact huS), Or.inl ?_⟩
        rw [hB, dict.head_eq j', ← hfin j', ← hlen1, hkt]
    · have ht1 : t + 1 < (row iface j).length := by
        by_contra h1
        refine ne_finish_of_interior (iface := iface) (j := j) hkpos hklt ?_
        rw [hA, show t + 1 = (row iface j).length by omega, hfin j]
      obtain ⟨hjj, hkt⟩ := interior_eq hkpos hklt (Nat.succ_pos t) ht1 hA
      subst hjj
      by_cases ht0 : 0 < t
      · exact ⟨u, huS, Or.inr (Or.inl ⟨j', t, hstart, ht0, by omega,
          fun m ↦ by have := hle m; omega, hB⟩)⟩
      · refine ⟨u, huS, Or.inl ?_⟩
        rw [hB, show t = 0 by omega, ← hstart]
        rfl
  · -- on the final run of a row ending at the placement
    rcases hCross with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · have ht0 : 0 < t := by
        by_contra h0
        exact ne_start_of_interior (iface := iface) (j := j) hkpos hklt
          (by rw [hA, show t = 0 by omega]; rfl)
      obtain ⟨hjj, hkt⟩ := interior_eq hkpos hklt ht0 ht hA
      subst hjj
      by_cases hlen : k + 1 < (row iface j').length
      · exact ⟨u, huS, Or.inr (Or.inr ⟨j', k + 1, hfinish, by omega, hlen,
          fun m ↦ by have := hlt m; omega, by rw [hB, hkt]⟩)⟩
      · refine ⟨u, huS, Or.inl ?_⟩
        rw [hB, ← hfinish, ← hfin j', show (row iface j').length = k + 1 by omega, hkt]
    · have ht1 : t + 1 < (row iface j).length := by
        by_contra h1
        refine ne_finish_of_interior (iface := iface) (j := j) hkpos hklt ?_
        rw [hA, show t + 1 = (row iface j).length by omega, hfin j]
      obtain ⟨hjj, hkt⟩ := interior_eq hkpos hklt (Nat.succ_pos t) ht1 hA
      subst hjj
      have hltk : ∀ m : Fin (positiveRow iface face j').length,
          RetainedTraversal.position (iface := iface) (face := face) j' m < t := by
        intro m
        have h1 := hlt m
        have h2 := hzeroPos m
        omega
      by_cases ht0 : 0 < t
      · exact ⟨u, huS, Or.inr (Or.inr ⟨j', t, hfinish, ht0, by omega, hltk, hB⟩)⟩
      · have hjF : j' ∈ F := mem_forest_of_no_place (iface := iface) (face := face)
          ⟨fun m ↦ by have := hltk m; omega⟩
        have hu : spec.core.head j' = u := hF (by rw [dict.head_eq j', hfinish])
        refine ⟨spec.core.tail j', (hClosed j' hjF).mpr (by rw [hu]; exact huS), Or.inl ?_⟩
        rw [hB, dict.tail_eq j', show t = 0 by omega]
        rfl

end Place

/-! ## 5.  The two kinds of neighbourhood do not meet -/

section Separate

variable {n p : ℕ} {spec : SubdivisionGraph.Spec n p} {F : Finset (Fin p)}
  {iface : InputInterface spec strong.toPresentation coordinates F}

/-- **A zero run of a retained row never reaches a forest class of
placements.**  Its vertices are interior walk vertices, where a spanning
placement never sits, and both of the run's ends are surviving occurrences,
which an initial or final run of a row may not cross. -/
theorem not_nearClass_of_nearGap (dict : CoreDictionary spec strong iface)
    (hSpan : Spanning dict) {S : Set (Fin n)} {i : Fin p} {lo hi : ℕ}
    (hGap : IsGap iface face i lo hi) {a : candidate.datum.SourceVertex}
    (hga : NearGap iface i lo hi a) (hca : NearClass iface face dict S a) : False := by
  obtain ⟨k, hk1, hk2, rfl⟩ := hga
  have hkpos : 0 < k := by omega
  have hklt : k < (row iface i).length := by have := isGap_hi_lt hGap; omega
  obtain ⟨u, -, hplace⟩ := hca
  rcases hplace with hEq | ⟨j, k', -, hkpos', hklt', hle, hEq⟩ | ⟨j, k', -, hkpos', hklt',
    hlt, hEq⟩
  · exact ne_vertexAt_of_interior dict hSpan hkpos hklt hEq
  · obtain ⟨hij, hkk⟩ := interior_eq hkpos hklt hkpos' hklt' hEq
    subst hij
    obtain ⟨m, hm⟩ := hGap.1
    have := hle m
    omega
  · obtain ⟨hij, hkk⟩ := interior_eq hkpos hklt hkpos' hklt' hEq
    subst hij
    obtain ⟨m, hm⟩ := hGap.2.1
    have := hlt m
    omega

/-- **and a placement that a forest class reaches is in that class.** -/
theorem mem_of_nearClass (dict : CoreDictionary spec strong iface) (hF : Faithful dict)
    (hSpan : Spanning dict) {S : Set (Fin n)} {u' : Fin n}
    (h : NearClass iface face dict S (dict.vertexAt u')) : u' ∈ S := by
  obtain ⟨u, huS, hplace⟩ := h
  rcases hplace with hEq | ⟨j, k', -, hkpos', hklt', -, hEq⟩ | ⟨j, k', -, hkpos', hklt',
    -, hEq⟩
  · exact hF hEq ▸ huS
  · exact absurd hEq.symm (ne_vertexAt_of_interior dict hSpan hkpos' hklt')
  · exact absurd hEq.symm (ne_vertexAt_of_interior dict hSpan hkpos' hklt')

/-- **Two zero runs of one row that share a vertex are the same run.** -/
theorem nearGap_eq {i i' : Fin p} {lo hi lo' hi' : ℕ} (hGap : IsGap iface face i lo hi)
    (hGap' : IsGap iface face i' lo' hi') {a : candidate.datum.SourceVertex}
    (hga : NearGap iface i lo hi a) (hga' : NearGap iface i' lo' hi' a) :
    i = i' ∧ lo = lo' ∧ hi = hi' := by
  obtain ⟨k, hk1, hk2, rfl⟩ := hga
  obtain ⟨k', hk1', hk2', hEq⟩ := hga'
  have hkpos : 0 < k := by omega
  have hklt : k < (row iface i).length := by have := isGap_hi_lt hGap; omega
  have hkpos' : 0 < k' := by omega
  have hklt' : k' < (row iface i').length := by have := isGap_hi_lt hGap'; omega
  obtain ⟨hij, hkk⟩ := interior_eq hkpos hklt hkpos' hklt' hEq
  subst hij
  subst hkk
  exact ⟨rfl, isGap_unique hGap hGap' hk1 hk2 hk1' hk2'⟩

/-! ### The zero-run confinement, transported along the contraction -/

/-- A walk of surviving zero steps out of a zero run stays in it. -/
theorem nearGap_of_reflTransGen (dict : CoreDictionary spec strong iface) (hF : Faithful dict)
    {i : Fin p} {lo hi : ℕ} (hGap : IsGap iface face i lo hi)
    {a b : candidate.datum.SourceVertex} (ha : NearGap iface i lo hi a)
    (hab : Relation.ReflTransGen (ClassInjectivity.SurvivingZeroStep face) a b) :
    NearGap iface i lo hi b := by
  induction hab with
  | refl => exact ha
  | tail _ hstep ih => exact nearGap_step dict hF hGap ih hstep

/-- and out of a forest class stays in it. -/
theorem nearClass_of_reflTransGen (dict : CoreDictionary spec strong iface)
    (hF : Faithful dict) (hSpan : Spanning dict) {S : Set (Fin n)}
    (hClosed : ForestClosed spec F S) {a b : candidate.datum.SourceVertex}
    (ha : NearClass iface face dict S a)
    (hab : Relation.ReflTransGen (ClassInjectivity.SurvivingZeroStep face) a b) :
    NearClass iface face dict S b := by
  induction hab with
  | refl => exact ha
  | tail _ hstep ih => exact nearClass_step dict hF hSpan hClosed ih hstep

/-- **The contraction joins two surviving vertices only by surviving zero
steps.**  `ClassInjectivity.reflTransGen_survivingZeroStep_of_reflTransGen_zeroStep`
composed with `ClassInjectivity.reflTransGen_zeroStep_of_classOf_eq`; neither
mentions an interface, so both transport verbatim. -/
theorem reflTransGen_of_classOf_eq (topology : ClearedFace.SourceContractionTopology face)
    {a b : candidate.datum.SourceVertex}
    (ha : nonDanglingValency candidate.datum a ≠ 0)
    (hb : nonDanglingValency candidate.datum b ≠ 0)
    (h : classOf topology a = classOf topology b) :
    Relation.ReflTransGen (ClassInjectivity.SurvivingZeroStep face) a b :=
  ClassInjectivity.reflTransGen_survivingZeroStep_of_reflTransGen_zeroStep ha hb
    (ClassInjectivity.reflTransGen_zeroStep_of_classOf_eq topology h)

end Separate

/-! ## 6.  The collisions, on the quotient source -/

section Collision

variable {n p : ℕ} {spec : SubdivisionGraph.Spec n p} {F : Finset (Fin p)}
  {iface : InputInterface spec strong.toPresentation coordinates F}

/-- Distinct surviving places of a row are distinct places. -/
theorem position_inj {i : Fin p} {m m' : Fin (positiveRow iface face i).length}
    (h : RetainedTraversal.position (iface := iface) (face := face) i m =
      RetainedTraversal.position (iface := iface) (face := face) i m') :
    (m : ℕ) = (m' : ℕ) := by
  have h1 := RetainedTraversal.position_le_position_iff.mp (le_of_eq h)
  have h2 := RetainedTraversal.position_le_position_iff.mp (le_of_eq h.symm)
  rw [Fin.le_def] at h1 h2
  omega

/-- **Two class-valued refined core vertices strictly inside retained rows, on
one contraction class, lie in one zero run.** -/
theorem gap_collision (dict : CoreDictionary spec strong iface) (hF : Faithful dict)
    (topology : ClearedFace.SourceContractionTopology face)
    {i i' : Fin p} {lo hi lo' hi' k k' : ℕ}
    (hGap : IsGap iface face i lo hi) (hGap' : IsGap iface face i' lo' hi')
    (hk1 : lo < k) (hk2 : k ≤ hi) (hk1' : lo' < k') (hk2' : k' ≤ hi')
    (hcls : classOf topology (RetainedTraversal.rowWalk strong iface i k) =
      classOf topology (RetainedTraversal.rowWalk strong iface i' k')) :
    i = i' ∧ lo = lo' ∧ hi = hi' := by
  have hva := nonDanglingValency_of_nearGap hGap (a := RetainedTraversal.rowWalk strong iface i k)
    ⟨k, hk1, hk2, rfl⟩
  have hvb := nonDanglingValency_of_nearGap hGap'
    (a := RetainedTraversal.rowWalk strong iface i' k') ⟨k', hk1', hk2', rfl⟩
  have hwalk := reflTransGen_of_classOf_eq topology (by omega) (by omega) hcls
  exact nearGap_eq hGap hGap'
    (nearGap_of_reflTransGen dict hF hGap ⟨k, hk1, hk2, rfl⟩ hwalk) ⟨k', hk1', hk2', rfl⟩

/-- **and a class-valued refined core vertex strictly inside a retained row is
on no forest class of placements.** -/
theorem not_class_collision (dict : CoreDictionary spec strong iface) (hF : Faithful dict)
    (hSpan : Spanning dict) (topology : ClearedFace.SourceContractionTopology face)
    {S : Set (Fin n)} (hClosed : ForestClosed spec F S) {i : Fin p} {lo hi k : ℕ}
    (hGap : IsGap iface face i lo hi) (hk1 : lo < k) (hk2 : k ≤ hi) {u : Fin n} (hu : u ∈ S)
    (hcls : classOf topology (dict.vertexAt u) =
      classOf topology (RetainedTraversal.rowWalk strong iface i k)) : False := by
  have hvb := nonDanglingValency_of_nearGap hGap (a := RetainedTraversal.rowWalk strong iface i k)
    ⟨k, hk1, hk2, rfl⟩
  have hwalk := reflTransGen_of_classOf_eq topology
    (vertexAt_valency_ne_zero dict hSpan u) (by omega) hcls
  exact not_nearClass_of_nearGap dict hSpan hGap ⟨k, hk1, hk2, rfl⟩
    (nearClass_of_reflTransGen dict hF hSpan hClosed (nearClass_self dict hu) hwalk)

/-- **Two placements on one contraction class are in one forest class.** -/
theorem class_collision (dict : CoreDictionary spec strong iface) (hF : Faithful dict)
    (hSpan : Spanning dict) (topology : ClearedFace.SourceContractionTopology face)
    {S : Set (Fin n)} (hClosed : ForestClosed spec F S) {u u' : Fin n} (hu : u ∈ S)
    (hcls : classOf topology (dict.vertexAt u) = classOf topology (dict.vertexAt u')) :
    u' ∈ S :=
  mem_of_nearClass dict hF hSpan (nearClass_of_reflTransGen dict hF hSpan hClosed
    (nearClass_self dict hu)
    (reflTransGen_of_classOf_eq topology (vertexAt_valency_ne_zero dict hSpan u)
      (vertexAt_valency_ne_zero dict hSpan u') hcls))

/-- **A kept slot is determined by its place along its row.** -/
theorem slotIndex_eq_of_slotPosition {x x' : SlotIndex iface face} (h1 : x.1 = x'.1)
    (h2 : RetainedTraversal.slotPosition (iface := iface) (face := face) x =
      RetainedTraversal.slotPosition (iface := iface) (face := face) x') : x = x' := by
  obtain ⟨i, m⟩ := x
  obtain ⟨i', m'⟩ := x'
  simp only at h1
  subst h1
  exact sigma_fin_ext rfl (position_inj h2)

/-- **The zero run just before a kept slot that is not the first of its
row.** -/
theorem isGap_slot_pred {x : SlotIndex iface face} (hx : (x.2 : ℕ) ≠ 0)
    (hb : (x.2 : ℕ) - 1 < (positiveRow iface face x.1).length) :
    IsGap iface face x.1
      (RetainedTraversal.slotPosition (iface := iface) (face := face)
        (⟨x.1, ⟨(x.2 : ℕ) - 1, hb⟩⟩ : SlotIndex iface face))
      (RetainedTraversal.slotPosition (iface := iface) (face := face) x) :=
  isGap_succ (m := (⟨(x.2 : ℕ) - 1, hb⟩ : Fin (positiveRow iface face x.1).length))
    (m' := x.2) (by show (x.2 : ℕ) - 1 + 1 = (x.2 : ℕ); omega)

/-- **and the one just after a kept slot that is not the last of its row.** -/
theorem isGap_slot_succ {x : SlotIndex iface face}
    (hx : (x.2 : ℕ) + 1 < (positiveRow iface face x.1).length) :
    IsGap iface face x.1 (RetainedTraversal.slotPosition (iface := iface) (face := face) x)
      (RetainedTraversal.slotPosition (iface := iface) (face := face)
        (⟨x.1, ⟨(x.2 : ℕ) + 1, hx⟩⟩ : SlotIndex iface face)) :=
  isGap_succ (m := x.2) rfl

end Collision

/-! ## 7.  At the trivalent-model producer: the class of a refined core
vertex, and where it sits -/

section Producer

variable {n₀ p₀ N Q : ℕ} {D : ExpansionData n₀ p₀ N Q} {spec₀ : SubdivisionGraph.Spec n₀ p₀}
  {hN : 0 < N} {hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e}
  {iface : InputInterface (D.bigSpec spec₀ hN hL) strong.toPresentation coordinates
    (expansionForest D)}

/-- **The retained index of the trivalent-model producer, named once**, so that
the
statements below stay readable; it is reducibly
`RetainedIndexProducer.retainedIndex hCond hN hL`. -/
abbrev ridx (hCond : D.Conditions spec₀.core) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) :
    RetainedIndex (D.bigSpec spec₀ hN hL) (expansionForest D) spec₀ :=
  RetainedIndexProducer.retainedIndex hCond hN hL

/-- **A forest row does not separate two fibres.**  `ExpansionData.SlotCompatible`'s
first clause, read as a closure condition on the fibre of a requested core
vertex. -/
theorem forestClosed_fib (hCond : D.Conditions spec₀.core) (w : Fin n₀) :
    ForestClosed (D.bigSpec spec₀ hN hL) (expansionForest D) {u : Fin N | D.fib u = w} := by
  intro j hj
  have h := (ExpansionData.compatible_of_conditions hCond j).1
    ((mem_expansionForest D j).mp hj)
  show D.fib (D.bigCore.tail j) = w ↔ D.fib (D.bigCore.head j) = w
  rw [h]

variable (hCond : D.Conditions spec₀.core)
  (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface) (hSpan : Spanning dict)
  (topology : ClearedFace.SourceContractionTopology face)
  (rev : SlotIndex iface face → Bool)
  (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
  (hTwo : CarriesAtMostTwo (ridx hCond hN hL))

/-- **The quotient-source vertex a refined core vertex of the retained
refinement sits on**, in the three class-valued cases: a marker at the
occurrence boundary its handover point names, a breakpoint just after the piece
it follows, and every other requested core vertex at any placement of its
fibre. -/
def clsSource (v : RefinementCore.RefinedVertex (Retained.segmentData iface face
      (ridx hCond hN hL))) : candidate.datum.SourceVertex :=
  match v with
  | Sum.inl w =>
      if h : IsHandover (ridx hCond hN hL) w then
        RetainedTraversal.rowWalk strong iface
          (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
            (handoverPair hCond face h)).1
          (RetainedTraversal.slotPosition (blockSlot (ridx hCond hN hL) topology rev hKept
            hTwo (handoverPair hCond face h)))
      else dict.vertexAt (exists_fib_of_not_handover hCond h).choose
  | Sum.inr y =>
      RetainedTraversal.rowWalk strong iface
        (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
          (breakPair (ridx hCond hN hL) y)).1
        (RetainedTraversal.slotPosition (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
          (breakPair (ridx hCond hN hL) y)) + 1)

theorem clsSource_handover {w : Fin n₀} (h : IsHandover (ridx hCond hN hL) w) :
    clsSource hCond dict topology rev hKept hTwo (Sum.inl w) =
      RetainedTraversal.rowWalk strong iface
        (blockSlot (ridx hCond hN hL) topology rev hKept hTwo (handoverPair hCond face h)).1
        (RetainedTraversal.slotPosition (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
          (handoverPair hCond face h))) :=
  dif_pos h

theorem clsSource_not_handover {w : Fin n₀} (h : ¬ IsHandover (ridx hCond hN hL) w) :
    clsSource hCond dict topology rev hKept hTwo (Sum.inl w) =
      dict.vertexAt (exists_fib_of_not_handover hCond h).choose :=
  dif_neg h

theorem clsSource_break (y : Σ j : Fin p₀, Fin (((Retained.segmentData iface face
    (ridx hCond hN hL)).segments j).length - 1)) :
    clsSource hCond dict topology rev hKept hTwo (Sum.inr y) =
      RetainedTraversal.rowWalk strong iface
        (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
          (breakPair (ridx hCond hN hL) y)).1
        (RetainedTraversal.slotPosition (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
          (breakPair (ridx hCond hN hL) y)) + 1) := rfl

include hSpan in
/-- **and its class is kept.** -/
theorem keptClass_clsSource (v : RefinementCore.RefinedVertex (Retained.segmentData iface face
      (ridx hCond hN hL))) :
    ClearedFace.SourceContractionTopology.KeptClass topology
      (classOf topology (clsSource hCond dict topology rev hKept hTwo v)) := by
  match v with
  | Sum.inl w =>
      by_cases h : IsHandover (ridx hCond hN hL) w
      · rw [clsSource_handover hCond dict topology rev hKept hTwo h]
        exact keptClass_startClass topology _
      · rw [clsSource_not_handover hCond dict topology rev hKept hTwo h]
        exact keptClass_requestedClass dict hSpan topology
          (exists_fib_of_not_handover hCond h)
  | Sum.inr y =>
      rw [clsSource_break hCond dict topology rev hKept hTwo y]
      exact keptClass_endClass topology _

/-- The class of an aligned marker's quotient-source vertex is the class the
row is in when it enters the occurrence the marker's slot begins on. -/
theorem classOf_clsSource_handover {w : Fin n₀} (h : IsHandover (ridx hCond hN hL) w) :
    classOf topology (clsSource hCond dict topology rev hKept hTwo (Sum.inl w)) =
      startClass topology (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
        (handoverPair hCond face h)) := by
  rw [clsSource_handover hCond dict topology rev hKept hTwo h]
  rfl

/-- and of a non-marker's, its fibre class. -/
theorem classOf_clsSource_not_handover {w : Fin n₀} (h : ¬ IsHandover (ridx hCond hN hL) w) :
    classOf topology (clsSource hCond dict topology rev hKept hTwo (Sum.inl w)) =
      RetainedFibre.requestedClass dict topology (exists_fib_of_not_handover hCond h) := by
  rw [clsSource_not_handover hCond dict topology rev hKept hTwo h]
  rfl

/-- and of a breakpoint's, the class the row is in when it leaves the
occurrence whose piece the breakpoint follows. -/
theorem classOf_clsSource_break (y : Σ j : Fin p₀, Fin (((Retained.segmentData iface face
    (ridx hCond hN hL)).segments j).length - 1)) :
    classOf topology (clsSource hCond dict topology rev hKept hTwo (Sum.inr y)) =
      endClass topology (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
        (breakPair (ridx hCond hN hL) y)) := by
  rw [clsSource_break hCond dict topology rev hKept hTwo y]
  rfl

include hSpan in
/-- **A refined core vertex that lands on a kept class lands on the class of
the quotient-source vertex it sits on.**  The three branches are
`RetainedVertexModel.cutVertex_inr_eq_cutLeft`,
`RetainedVertexModel.coreVertex_of_not_handover` and the aligned branch of
`RetainedVertexModel.cutTail`; a straddling marker lands on a new split vertex
instead, which the hypothesis excludes. -/
theorem cutVertex_eq_cutLeft
    {v : RefinementCore.RefinedVertex (Retained.segmentData iface face (ridx hCond hN hL))}
    {c : Fin (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)).n}
    (hv : cutVertex hCond dict hSpan topology rev hKept hTwo v = Sum.inl c) :
    cutVertex hCond dict hSpan topology rev hKept hTwo v =
      cutLeft (ridx hCond hN hL) topology rev hKept
        (RefinementCore.keptClassIndex topology
          ⟨classOf topology (clsSource hCond dict topology rev hKept hTwo v),
            keptClass_clsSource hCond dict hSpan topology rev hKept hTwo v⟩) := by
  match v with
  | Sum.inr y =>
      refine (cutVertex_inr_eq_cutLeft hCond dict hSpan topology rev hKept hTwo y).trans
        (congrArg (fun z ↦ cutLeft (ridx hCond hN hL) topology rev hKept
          (RefinementCore.keptClassIndex topology z)) (Subtype.ext ?_))
      exact (classOf_clsSource_break hCond dict topology rev hKept hTwo y).symm
  | Sum.inl w =>
      by_cases h : IsHandover (ridx hCond hN hL) w
      · have hcv : cutVertex hCond dict hSpan topology rev hKept hTwo (Sum.inl w) =
            cutTail (ridx hCond hN hL) topology rev hKept
            (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
            (handoverPair hCond face h)) (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
            (handoverPair hCond face h)) :=
          (cutVertex_inl hCond dict hSpan topology rev hKept hTwo w).trans
            (coreVertex_of_handover hCond dict hSpan topology rev hKept hTwo h)
        by_cases hs : Straddles iface face (ridx hCond hN hL)
            (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
            (handoverPair hCond face h)) ∧ (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
            (handoverPair hCond face h)) ≠ 0
        · exfalso
          rw [hcv, cutTail_of_ne_zero (ridx hCond hN hL) topology rev hKept hs.2 hs.1] at hv
          simp [splitVertex] at hv
        · have hd : cutTail (ridx hCond hN hL) topology rev hKept
            (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
            (handoverPair hCond face h)) (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
            (handoverPair hCond face h)) =
              cutLeft (ridx hCond hN hL) topology rev hKept
                (RefinementCore.keptClassIndex topology
                  ⟨startClass topology (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
            (handoverPair hCond face h)), keptClass_startClass topology
            (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
            (handoverPair hCond face h))⟩) :=
            dif_neg hs
          refine hcv.trans (hd.trans (congrArg (fun z ↦ cutLeft (ridx hCond hN hL) topology
            rev hKept (RefinementCore.keptClassIndex topology z)) (Subtype.ext ?_)))
          exact (classOf_clsSource_handover hCond dict topology rev hKept hTwo h).symm
      · refine ((cutVertex_inl hCond dict hSpan topology rev hKept hTwo w).trans
          (coreVertex_of_not_handover hCond dict hSpan topology rev hKept hTwo h)).trans
          (congrArg (fun z ↦ cutLeft (ridx hCond hN hL) topology rev hKept
            (RefinementCore.keptClassIndex topology z)) (Subtype.ext ?_))
        exact (classOf_clsSource_not_handover hCond dict topology rev hKept hTwo h).symm

include hSpan in
/-- **so two refined core vertices on one kept class sit on quotient-source
vertices of one contraction class.** -/
theorem classOf_clsSource_eq
    {v v' : RefinementCore.RefinedVertex (Retained.segmentData iface face (ridx hCond hN hL))}
    {c : Fin (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)).n}
    (hv : cutVertex hCond dict hSpan topology rev hKept hTwo v = Sum.inl c)
    (hv' : cutVertex hCond dict hSpan topology rev hKept hTwo v' = Sum.inl c) :
    classOf topology (clsSource hCond dict topology rev hKept hTwo v) =
      classOf topology (clsSource hCond dict topology rev hKept hTwo v') := by
  have h1 := cutVertex_eq_cutLeft hCond dict hSpan topology rev hKept hTwo hv
  have h2 := cutVertex_eq_cutLeft hCond dict hSpan topology rev hKept hTwo hv'
  have h3 : cutLeft (ridx hCond hN hL) topology rev hKept
        (RefinementCore.keptClassIndex topology
          ⟨classOf topology (clsSource hCond dict topology rev hKept hTwo v),
            keptClass_clsSource hCond dict hSpan topology rev hKept hTwo v⟩) =
      cutLeft (ridx hCond hN hL) topology rev hKept
        (RefinementCore.keptClassIndex topology
          ⟨classOf topology (clsSource hCond dict topology rev hKept hTwo v'),
            keptClass_clsSource hCond dict hSpan topology rev hKept hTwo v'⟩) := by
    rw [← h1, ← h2, hv, hv']
  have h4 : RefinementCore.keptClassIndex topology
        ⟨classOf topology (clsSource hCond dict topology rev hKept hTwo v),
          keptClass_clsSource hCond dict hSpan topology rev hKept hTwo v⟩ =
      RefinementCore.keptClassIndex topology
        ⟨classOf topology (clsSource hCond dict topology rev hKept hTwo v'),
          keptClass_clsSource hCond dict hSpan topology rev hKept hTwo v'⟩ :=
    Sum.inl.inj h3
  exact congrArg Subtype.val ((RefinementCore.keptClassIndex topology).injective h4)

/-! ### Where a breakpoint and an aligned marker sit along their row -/

/-- **A breakpoint follows the last piece of its kept slot.**  Its own piece
index is one below the piece count: a straddled kept slot has two pieces and
`RetainedVertexModel.not_straddles_blockSlot_breakPair` excludes the first, an
unstraddled one has a single piece. -/
theorem blockIndex_break_succ (y : Σ j : Fin p₀, Fin (((Retained.segmentData iface face
    (ridx hCond hN hL)).segments j).length - 1)) :
    (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) + 1 = pieceCount iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) := by
  have hlt := blockIndex_lt (ridx hCond hN hL) topology rev hKept hTwo
    (breakPair (ridx hCond hN hL) y)
  by_cases hstr : Straddles iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y))
  · have h2 := pieceCount_of_straddles (ridx hCond hN hL) hstr
    have h0 := not_straddles_blockSlot_breakPair hCond topology rev hKept hTwo y
    have hne : (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) ≠ 0 := fun hz ↦ h0 ⟨hstr, hz⟩
    omega
  · have h2 := pieceCount_of_not_straddles (ridx hCond hN hL) hstr
    omega

/-- **and its kept slot is not the last of its row**: a further piece of the
same requested slot follows it. -/
theorem blockSlot_break_lt (y : Σ j : Fin p₀, Fin (((Retained.segmentData iface face
    (ridx hCond hN hL)).segments j).length - 1)) :
    ((blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)).2 : ℕ) + 1 < (positiveRow iface face
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)).1).length := by
  have hlast := blockIndex_break_succ hCond topology rev hKept hTwo y
  have hoff : piecePos iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) + 1 =
      offset (cutBlocks iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)).1) (((blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)).2 : ℕ) + 1) := by
    rw [offset_cutBlocks_succ (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)), piecePos_eq]
    omega
  have hrow : slotRow (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) = (ridx hCond hN hL).owner y.1 :=
    Subtype.ext (blockSlot_row (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y))
  have hp : piecePos iface face (ridx hCond hN hL)
        (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
          (breakPair (ridx hCond hN hL) y))
        (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
          (breakPair (ridx hCond hN hL) y)) =
      retPos iface face (ridx hCond hN hL) y.1 (y.2 : ℕ) :=
    piecePos_blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)
  have hseg : 0 < ((Retained.segmentData iface face (ridx hCond hN hL)).segments y.1).length :=
    RefinementCore.length_segments_pos _ _
  have hy := y.2.isLt
  have hlt2 : retPos iface face (ridx hCond hN hL) y.1 ((y.2 : ℕ) + 1) <
      (rowPieces iface face (ridx hCond hN hL) ((ridx hCond hN hL).owner y.1)).length :=
    retPos_lt iface face (ridx hCond hN hL) y.1 (by omega)
  have hsucc : retPos iface face (ridx hCond hN hL) y.1 ((y.2 : ℕ) + 1) =
      retPos iface face (ridx hCond hN hL) y.1 (y.2 : ℕ) + 1 := by
    rw [retPos_eq, retPos_eq]
    omega
  by_contra hcon
  have hx2 := (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)).2.isLt
  have heq : ((blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)).2 : ℕ) + 1 = (cutBlocks iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)).1).length := by
    rw [length_cutBlocks (ridx hCond hN hL) (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)).1]
    omega
  have htot : piecePos iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) + 1 =
      (rowPieces iface face (ridx hCond hN hL) (slotRow
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)))).length := by
    rw [hoff, heq, offset_cutBlocks_length (ridx hCond hN hL) hTwo
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y))]
  rw [hrow] at htot
  omega

/-- **An aligned marker is at the first piece of its kept slot.** -/
theorem blockIndex_handover_eq_zero {w : Fin n₀} (h : IsHandover (ridx hCond hN hL) w)
    (hs : ¬ (Straddles iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) ∧ (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) ≠ 0)) : (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) = 0 := by
  by_contra h0
  have hstr : ¬ Straddles iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) := fun hc ↦ hs ⟨hc, h0⟩
  have h1 := pieceCount_of_not_straddles (ridx hCond hN hL) hstr
  have h2 := blockIndex_lt (ridx hCond hN hL) topology rev hKept hTwo
    (handoverPair hCond face h)
  omega

/-- **The row place of an aligned marker is the first block boundary of the
retained refinement**, which is positive because the first requested slot the
row carries prescribes at least one piece. -/
theorem piecePos_handover {w : Fin n₀} (h : IsHandover (ridx hCond hN hL) w) :
    piecePos iface face (ridx hCond hN hL) (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) =
      offset (rowBlocks iface face (ridx hCond hN hL)
        ((ridx hCond hN hL).owner h.choose)) 1 := by
  rw [piecePos_blockIndex (ridx hCond hN hL) topology rev hKept hTwo
    (handoverPair hCond face h), retPos_eq]
  show offset (rowBlocks iface face (ridx hCond hN hL)
      ((ridx hCond hN hL).owner h.choose)) ((ridx hCond hN hL).pos h.choose) + 0 = _
  rw [h.choose_spec.1, Nat.add_zero]

/-- and it is positive. -/
theorem offset_rowBlocks_one_pos {w : Fin n₀} (h : IsHandover (ridx hCond hN hL) w) :
    0 < offset (rowBlocks iface face (ridx hCond hN hL)
      ((ridx hCond hN hL).owner h.choose)) 1 := by
  obtain ⟨j₁, hk⟩ := exists_double_of_pos_one hCond h.choose_spec.1
  obtain ⟨how, hside, -, -⟩ := ExpansionData.owner_eq_of_double hCond hk
  have hpos1 : (ridx hCond hN hL).pos j₁ = 0 := by
    rw [retainedIndex_pos, hside]
    rfl
  have hown : (ridx hCond hN hL).owner j₁ = (ridx hCond hN hL).owner h.choose :=
    Subtype.ext (by show D.owner j₁ = D.owner h.choose; rw [how])
  have hone := offset_rowBlocks_one (iface := iface) (face := face) (ridx hCond hN hL) hpos1
  rw [hown] at hone
  rw [hone]
  exact RefinementCore.length_segments_pos _ _

/-- **An aligned marker's kept slot is not the first of its row.** -/
theorem blockSlot_handover_ne_zero {w : Fin n₀} (h : IsHandover (ridx hCond hN hL) w)
    (hs : ¬ (Straddles iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) ∧ (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) ≠ 0)) :
    ((blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)).2 : ℕ) ≠ 0 := by
  intro hx0
  have hT0 := blockIndex_handover_eq_zero hCond topology rev hKept hTwo h hs
  have hpp : piecePos iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) = 0 := by
    rw [piecePos_eq, hx0, hT0, offset_zero]
  have h1 := piecePos_handover hCond topology rev hKept hTwo h
  have h2 := offset_rowBlocks_one_pos (iface := iface) (face := face) hCond h
  omega

/-! ### The three collisions at the trivalent-model producer -/

variable (hF : Faithful dict)

include hSpan in
/-- **A marker that lands on a kept class is aligned**: it does not straddle a
kept slot, since a straddling marker lands on a new split vertex. -/
theorem not_straddles_of_inl {w : Fin n₀} (h : IsHandover (ridx hCond hN hL) w)
    {c : Fin (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)).n}
    (hv : cutVertex hCond dict hSpan topology rev hKept hTwo (Sum.inl w) = Sum.inl c) :
    ¬ (Straddles iface face (ridx hCond hN hL) (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) ∧ (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) ≠ 0) := by
  intro hstr
  rw [cutVertex_inl hCond dict hSpan topology rev hKept hTwo w,
    coreVertex_of_handover hCond dict hSpan topology rev hKept hTwo h,
    cutTail_of_ne_zero (ridx hCond hN hL) topology rev hKept hstr.2 hstr.1] at hv
  simp [splitVertex] at hv

include hTwo in
/-- **A breakpoint's row place is never one below the marker's.**  The marker
sits at the first block boundary of the retained refinement; a breakpoint of
the first requested slot the row carries is strictly below it, and one of the
second is at or above it. -/
theorem retPos_succ_ne_offset_one
    (y : Σ j : Fin p₀, Fin (((Retained.segmentData iface face
      (ridx hCond hN hL)).segments j).length - 1))
    {j₂ : Fin p₀} (hown : (ridx hCond hN hL).owner y.1 = (ridx hCond hN hL).owner j₂)
    (hEq : retPos iface face (ridx hCond hN hL) y.1 (y.2 : ℕ) + 1 =
      offset (rowBlocks iface face (ridx hCond hN hL) ((ridx hCond hN hL).owner j₂)) 1) :
    False := by
  have hlt := (ridx hCond hN hL).pos_lt y.1
  have hle := hTwo ((ridx hCond hN hL).owner y.1)
  have hret : retPos iface face (ridx hCond hN hL) y.1 (y.2 : ℕ) =
      offset (rowBlocks iface face (ridx hCond hN hL) ((ridx hCond hN hL).owner j₂))
        ((ridx hCond hN hL).pos y.1) + (y.2 : ℕ) := by
    rw [retPos_eq, hown]
  have hseg : 0 < ((Retained.segmentData iface face (ridx hCond hN hL)).segments y.1).length :=
    RefinementCore.length_segments_pos _ _
  have hy := y.2.isLt
  rcases (show (ridx hCond hN hL).pos y.1 = 0 ∨ (ridx hCond hN hL).pos y.1 = 1 by omega) with
    h0 | h1
  · have hone := offset_rowBlocks_one (iface := iface) (face := face) (ridx hCond hN hL) h0
    rw [hown] at hone
    rw [h0, offset_zero] at hret
    omega
  · rw [h1] at hret
    omega

include hF in
/-- **An aligned marker and a breakpoint never land on one contraction
class.**  They would lie in one zero run of one retained row, hence at one
piece boundary along it, which the previous lemma forbids. -/
theorem marker_ne_break {w : Fin n₀} (h : IsHandover (ridx hCond hN hL) w)
    (hs : ¬ (Straddles iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) ∧ (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) ≠ 0))
    (y : Σ j : Fin p₀, Fin (((Retained.segmentData iface face
      (ridx hCond hN hL)).segments j).length - 1))
    (hcls : classOf topology (clsSource hCond dict topology rev hKept hTwo (Sum.inl w)) =
      classOf topology (clsSource hCond dict topology rev hKept hTwo (Sum.inr y))) : False := by
  have hxM := blockSlot_handover_ne_zero hCond topology rev hKept hTwo h hs
  have hbM : ((blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)).2 : ℕ) - 1 < (positiveRow iface face
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)).1).length := by
    have := (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)).2.isLt
    omega
  have hGapM := isGap_slot_pred (iface := iface) (face := face) hxM hbM
  have hxB := blockSlot_break_lt hCond topology rev hKept hTwo y
  have hGapB := isGap_slot_succ (iface := iface) (face := face) hxB
  rw [clsSource_handover hCond dict topology rev hKept hTwo h,
    clsSource_break hCond dict topology rev hKept hTwo y] at hcls
  obtain ⟨hrow, hlo, -⟩ := gap_collision dict hF topology hGapM hGapB
    hGapM.2.2.1 le_rfl (Nat.lt_succ_self _) hGapB.2.2.1 hcls
  have hpred : (⟨(blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)).1, ⟨((blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)).2 : ℕ) - 1, hbM⟩⟩ : SlotIndex iface face) =
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) :=
    slotIndex_eq_of_slotPosition hrow hlo
  have hidx : ((blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)).2 : ℕ) = ((blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)).2 : ℕ) + 1 := by
    have hc := congrArg (fun z : SlotIndex iface face ↦ (z.2 : ℕ)) hpred
    simp only at hc
    omega
  have hown : (ridx hCond hN hL).owner y.1 = (ridx hCond hN hL).owner h.choose :=
    Subtype.ext ((blockSlot_row (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)).symm.trans (hrow.symm.trans
        (blockSlot_row (ridx hCond hN hL) topology rev hKept hTwo (handoverPair hCond face h))))
  have hT0 := blockIndex_handover_eq_zero hCond topology rev hKept hTwo h hs
  have hM := piecePos_handover hCond topology rev hKept hTwo h
  have hlastB := blockIndex_break_succ hCond topology rev hKept hTwo y
  have hB : piecePos iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) =
      retPos iface face (ridx hCond hN hL) y.1 (y.2 : ℕ) :=
    piecePos_blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)
  have hsuccB := offset_cutBlocks_succ (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y))
  have hpeM := piecePos_eq (ridx hCond hN hL) (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h))
  have hpeB := piecePos_eq (ridx hCond hN hL) (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y))
  have hoffEq : offset (cutBlocks iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)).1) ((blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)).2 : ℕ) =
      offset (cutBlocks iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)).1) (((blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)).2 : ℕ) + 1) := by
    rw [← hidx]
    exact congrArg (fun i ↦ offset (cutBlocks iface face (ridx hCond hN hL) i)
      ((blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)).2 : ℕ)) hrow
  exact retPos_succ_ne_offset_one hCond hTwo y hown
    (by omega)

include hF in
/-- **Two aligned markers on one contraction class are one marker.** -/
theorem handover_eq_of_cls {w w' : Fin n₀} (h : IsHandover (ridx hCond hN hL) w)
    (h' : IsHandover (ridx hCond hN hL) w')
    (hs : ¬ (Straddles iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) ∧ (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) ≠ 0))
    (hs' : ¬ (Straddles iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h')) ∧ (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h')) ≠ 0))
    (hcls : classOf topology (clsSource hCond dict topology rev hKept hTwo (Sum.inl w)) =
      classOf topology (clsSource hCond dict topology rev hKept hTwo (Sum.inl w'))) :
    w = w' := by
  have hxM := blockSlot_handover_ne_zero hCond topology rev hKept hTwo h hs
  have hxM' := blockSlot_handover_ne_zero hCond topology rev hKept hTwo h' hs'
  have hbM : ((blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)).2 : ℕ) - 1 < (positiveRow iface face
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)).1).length := by
    have := (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)).2.isLt
    omega
  have hbM' : ((blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h')).2 : ℕ) - 1 < (positiveRow iface face
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h')).1).length := by
    have := (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h')).2.isLt
    omega
  have hGapM := isGap_slot_pred (iface := iface) (face := face) hxM hbM
  have hGapM' := isGap_slot_pred (iface := iface) (face := face) hxM' hbM'
  rw [clsSource_handover hCond dict topology rev hKept hTwo h,
    clsSource_handover hCond dict topology rev hKept hTwo h'] at hcls
  obtain ⟨hrow, -, hhi⟩ := gap_collision dict hF topology hGapM hGapM'
    hGapM.2.2.1 le_rfl hGapM'.2.2.1 le_rfl hcls
  have hXX : (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)) = (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h')) := slotIndex_eq_of_slotPosition hrow hhi
  have hown : (ridx hCond hN hL).owner h.choose = (ridx hCond hN hL).owner h'.choose :=
    Subtype.ext ((blockSlot_row (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h)).symm.trans
      ((congrArg (fun z : SlotIndex iface face ↦ z.1) hXX).trans
        (blockSlot_row (ridx hCond hN hL) topology rev hKept hTwo (handoverPair hCond face h'))))
  have hj : h.choose = h'.choose :=
    owner_pos_determines (ridx hCond hN hL) hown (h.choose_spec.1.trans h'.choose_spec.1.symm)
  exact h.choose_spec.2.symm.trans ((congrArg spec₀.core.tail hj).trans h'.choose_spec.2)

include hF in
/-- **Two breakpoints on one contraction class are one breakpoint.** -/
theorem break_eq_of_cls
    (y y' : Σ j : Fin p₀, Fin (((Retained.segmentData iface face
      (ridx hCond hN hL)).segments j).length - 1))
    (hcls : classOf topology (clsSource hCond dict topology rev hKept hTwo (Sum.inr y)) =
      classOf topology (clsSource hCond dict topology rev hKept hTwo (Sum.inr y'))) :
    y = y' := by
  have hxB := blockSlot_break_lt hCond topology rev hKept hTwo y
  have hxB' := blockSlot_break_lt hCond topology rev hKept hTwo y'
  have hGapB := isGap_slot_succ (iface := iface) (face := face) hxB
  have hGapB' := isGap_slot_succ (iface := iface) (face := face) hxB'
  rw [clsSource_break hCond dict topology rev hKept hTwo y,
    clsSource_break hCond dict topology rev hKept hTwo y'] at hcls
  obtain ⟨hrow, hlo, -⟩ := gap_collision dict hF topology hGapB hGapB'
    (Nat.lt_succ_self _) hGapB.2.2.1 (Nat.lt_succ_self _) hGapB'.2.2.1 hcls
  have hXX : (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) = (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y')) := slotIndex_eq_of_slotPosition hrow hlo
  have hlast := blockIndex_break_succ hCond topology rev hKept hTwo y
  have hlast' := blockIndex_break_succ hCond topology rev hKept hTwo y'
  have hpc : pieceCount iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) =
      pieceCount iface face (ridx hCond hN hL) (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y')) :=
    congrArg (pieceCount iface face (ridx hCond hN hL)) hXX
  have htt : (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) = (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y')) := by omega
  have hB : piecePos iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) =
      retPos iface face (ridx hCond hN hL) y.1 (y.2 : ℕ) :=
    piecePos_blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)
  have hB' : piecePos iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y')) (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y')) =
      retPos iface face (ridx hCond hN hL) y'.1 (y'.2 : ℕ) :=
    piecePos_blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y')
  have hpp : piecePos iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)) =
      piecePos iface face (ridx hCond hN hL) (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y')) (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y')) := by rw [hXX, htt]
  have hret : retPos iface face (ridx hCond hN hL) y.1 (y.2 : ℕ) =
      retPos iface face (ridx hCond hN hL) y'.1 (y'.2 : ℕ) := hB.symm.trans (hpp.trans hB')
  have hown : (ridx hCond hN hL).owner y.1 = (ridx hCond hN hL).owner y'.1 :=
    Subtype.ext ((blockSlot_row (ridx hCond hN hL) topology rev hKept hTwo
      (breakPair (ridx hCond hN hL) y)).symm.trans
      ((congrArg (fun z : SlotIndex iface face ↦ z.1) hXX).trans
        (blockSlot_row (ridx hCond hN hL) topology rev hKept hTwo
          (breakPair (ridx hCond hN hL) y'))))
  have hbp : breakPair (ridx hCond hN hL) y = breakPair (ridx hCond hN hL) y' :=
    (retRowEquiv iface face (ridx hCond hN hL)).injective (sigma_fin_ext hown hret)
  have h1 : (breakPair (ridx hCond hN hL) y).1 = (breakPair (ridx hCond hN hL) y').1 :=
    congrArg Sigma.fst hbp
  have h2 : ((breakPair (ridx hCond hN hL) y).2 : ℕ) =
      ((breakPair (ridx hCond hN hL) y').2 : ℕ) :=
    congrArg (fun z : Σ j : Fin p₀, Fin (((Retained.segmentData iface face
      (ridx hCond hN hL)).segments j).length) ↦ (z.2 : ℕ)) hbp
  exact sigma_fin_ext h1 h2

include hSpan hF in
/-- **A non-marker requested core vertex and an aligned marker never land on
one contraction class.**  The marker's quotient-source vertex is interior to a
retained row, where `Spanning` puts no placement and where a zero run out of a
placement cannot reach. -/
theorem class_ne_marker {w w' : Fin n₀} (h : ¬ IsHandover (ridx hCond hN hL) w)
    (h' : IsHandover (ridx hCond hN hL) w')
    (hs' : ¬ (Straddles iface face (ridx hCond hN hL)
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h')) ∧ (blockIndex (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h')) ≠ 0))
    (hcls : classOf topology (clsSource hCond dict topology rev hKept hTwo (Sum.inl w)) =
      classOf topology (clsSource hCond dict topology rev hKept hTwo (Sum.inl w'))) : False := by
  have hxM := blockSlot_handover_ne_zero hCond topology rev hKept hTwo h' hs'
  have hbM : ((blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h')).2 : ℕ) - 1 < (positiveRow iface face
      (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h')).1).length := by
    have := (blockSlot (ridx hCond hN hL) topology rev hKept hTwo
      (handoverPair hCond face h')).2.isLt
    omega
  have hGapM := isGap_slot_pred (iface := iface) (face := face) hxM hbM
  rw [clsSource_not_handover hCond dict topology rev hKept hTwo h,
    clsSource_handover hCond dict topology rev hKept hTwo h'] at hcls
  exact not_class_collision dict hF hSpan topology (forestClosed_fib hCond w) hGapM
    hGapM.2.2.1 le_rfl (exists_fib_of_not_handover hCond h).choose_spec hcls

include hSpan hF in
/-- **and neither do a non-marker requested core vertex and a breakpoint.** -/
theorem class_ne_break {w : Fin n₀} (h : ¬ IsHandover (ridx hCond hN hL) w)
    (y : Σ j : Fin p₀, Fin (((Retained.segmentData iface face
      (ridx hCond hN hL)).segments j).length - 1))
    (hcls : classOf topology (clsSource hCond dict topology rev hKept hTwo (Sum.inl w)) =
      classOf topology (clsSource hCond dict topology rev hKept hTwo (Sum.inr y))) : False := by
  have hxB := blockSlot_break_lt hCond topology rev hKept hTwo y
  have hGapB := isGap_slot_succ (iface := iface) (face := face) hxB
  rw [clsSource_not_handover hCond dict topology rev hKept hTwo h,
    clsSource_break hCond dict topology rev hKept hTwo y] at hcls
  exact not_class_collision dict hF hSpan topology (forestClosed_fib hCond w) hGapB
    (Nat.lt_succ_self _) hGapB.2.2.1 (exists_fib_of_not_handover hCond h).choose_spec hcls

include hSpan hF in
/-- **Two non-marker requested core vertices on one contraction class have one
fibre, hence are equal.** -/
theorem class_eq_of_cls {w w' : Fin n₀} (h : ¬ IsHandover (ridx hCond hN hL) w)
    (h' : ¬ IsHandover (ridx hCond hN hL) w')
    (hcls : classOf topology (clsSource hCond dict topology rev hKept hTwo (Sum.inl w)) =
      classOf topology (clsSource hCond dict topology rev hKept hTwo (Sum.inl w'))) : w = w' := by
  rw [clsSource_not_handover hCond dict topology rev hKept hTwo h,
    clsSource_not_handover hCond dict topology rev hKept hTwo h'] at hcls
  have hmem := class_collision dict hF hSpan topology (forestClosed_fib hCond w)
    (exists_fib_of_not_handover hCond h).choose_spec hcls
  exact ((((exists_fib_of_not_handover hCond h').choose_spec).symm.trans hmem).symm)

/-! ## 8.  `hcls`: the class half of the injectivity of the retained vertex map -/

include hSpan hF in
/-- **Two refined core vertices of the retained refinement sent to the same
kept contraction class are equal.**

This is the hypothesis `hcls` of
`RetainedVertexModel.injective_vertexModel_of_inl`, the general-forest form of
`DraismaVargas.LocalCases.ClassInjectivity` §3--§4 at the trivalent-model
producer.  The three
class values are the fibre class of a non-marker requested core vertex, the
walk class of an aligned marker at the occurrence boundary it names, and the
walk class of a breakpoint just after the piece it follows; §5--§7 separate
them pairwise. -/
theorem classInjective
    (v v' : RefinementCore.RefinedVertex (Retained.segmentData iface face (ridx hCond hN hL)))
    (c : Fin (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)).n)
    (hv : cutVertex hCond dict hSpan topology rev hKept hTwo v = Sum.inl c)
    (hv' : cutVertex hCond dict hSpan topology rev hKept hTwo v' = Sum.inl c) : v = v' := by
  have hcls := classOf_clsSource_eq hCond dict hSpan topology rev hKept hTwo hv hv'
  rcases v with w | y
  · rcases v' with w' | y'
    · by_cases h : IsHandover (ridx hCond hN hL) w
      · have hs := not_straddles_of_inl hCond dict hSpan topology rev hKept hTwo h hv
        by_cases h' : IsHandover (ridx hCond hN hL) w'
        · have hs' := not_straddles_of_inl hCond dict hSpan topology rev hKept hTwo h' hv'
          exact congrArg Sum.inl
            (handover_eq_of_cls hCond dict topology rev hKept hTwo hF h h' hs hs' hcls)
        · exact absurd hcls.symm
            (fun hc ↦ class_ne_marker hCond dict hSpan topology rev hKept hTwo hF h' h hs hc)
      · by_cases h' : IsHandover (ridx hCond hN hL) w'
        · have hs' := not_straddles_of_inl hCond dict hSpan topology rev hKept hTwo h' hv'
          exact absurd hcls
            (fun hc ↦ class_ne_marker hCond dict hSpan topology rev hKept hTwo hF h h' hs' hc)
        · exact congrArg Sum.inl
            (class_eq_of_cls hCond dict hSpan topology rev hKept hTwo hF h h' hcls)
    · by_cases h : IsHandover (ridx hCond hN hL) w
      · have hs := not_straddles_of_inl hCond dict hSpan topology rev hKept hTwo h hv
        exact absurd hcls
          (fun hc ↦ marker_ne_break hCond dict topology rev hKept hTwo hF h hs y' hc)
      · exact absurd hcls
          (fun hc ↦ class_ne_break hCond dict hSpan topology rev hKept hTwo hF h y' hc)
  · rcases v' with w' | y'
    · by_cases h' : IsHandover (ridx hCond hN hL) w'
      · have hs' := not_straddles_of_inl hCond dict hSpan topology rev hKept hTwo h' hv'
        exact absurd hcls.symm
          (fun hc ↦ marker_ne_break hCond dict topology rev hKept hTwo hF h' hs' y hc)
      · exact absurd hcls.symm
          (fun hc ↦ class_ne_break hCond dict hSpan topology rev hKept hTwo hF h' y hc)
    · exact congrArg Sum.inr
        (break_eq_of_cls hCond dict topology rev hKept hTwo hF y y' hcls)

include hSpan hF in
/-- **The vertex map of the retained core model is injective**, with no
hypothesis beyond what `RetainedRelabeling.CutRelabeling` already keeps inside
its binder.  `RetainedVertexModel.injective_vertexModel_of_inl` reduced this to
`classInjective`. -/
theorem injective_vertexModel :
    Function.Injective (vertexModel hCond dict hSpan topology hKept) :=
  injective_vertexModel_of_inl hCond dict hSpan topology hKept
    (fun v v' c hv hv' ↦ classInjective hCond dict hSpan topology
      (RetainedTraversal.reversedAt (strong := strong) (iface := iface) (face := face)) hKept
      (RetainedCut.carried_length_le_two hCond hN hL) hF v v' c hv hv')

end Producer

/-! ## 9.  The retained relabeling, and the Statement -/

section Receipt

open DraismaVargas.LocalCases.TerminalExhausts

variable {n₀ p₀ : ℕ} {D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀))}
  {spec₀ : SubdivisionGraph.Spec n₀ p₀} {hN : 0 < 2 * (p₀ - n₀)}
  {hL : ∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e}

/-- **The retained relabeling, unconditional.**
`RetainedVertexModel.cutRelabeling_of_expansion` fed with §8's injectivity: at the
trivalent-model producer the retained relabeling exists with no hypothesis at
all. -/
theorem cutRelabeling_of_expansion (hCond : D.Conditions spec₀.core) :
    RetainedRelabeling.CutRelabeling (D.bigSpec spec₀ hN hL) (expansionForest D) spec₀
      (RetainedIndexProducer.retainedIndex hCond hN hL) :=
  RetainedVertexModel.cutRelabeling_of_expansion hCond
    (fun _degree _coordinate _ _ _tgt _gdata _wall _cand _strong _coordinates _iface dict
      hFaithful hSpan _hConnected _hSource _face topology hKept ↦
      injective_vertexModel hCond dict hSpan topology hKept hFaithful)

end Receipt

section Statement

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StableSourceDarts
open DraismaVargas.LocalCases.TerminalExhausts

/-- **The Statement's conclusion from the type-change `link` alone.**  The
binders
`spec`, `hconn`, `hGenus`, `hEven`, the conclusion and `link` are
`RetainedVertexModel.nonempty_evenSubdivisionPencil_of_link_of_injective_vertexModel`'s
verbatim; its remaining hypothesis `inj` is §8. -/
theorem nonempty_evenSubdivisionPencil_of_link {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p)
    (hconn : graph_connected spec.graph) (hGenus : 6 ≤ p + 1 - n)
    (hEven : Even (p + 1 - n))
    (link : ∀ m : ℕ, p + 1 - n = 2 * m + 2 →
      ∀ K : CubicDartGraph (Dart (CaterpillarSeed.seed m).candidate.datum)
        (BranchVertex (CaterpillarSeed.seed m).candidate.datum),
      CubicDartGraph.Reaches (seedGraph m) K →
      ∀ (mv : K.MoveData)
        (arrival : OuterWalk.FacetArrival (m + 2) K (seedLabel m) (seedLabel m mv.base))
        (wd : OuterWalk.WallData arrival), OuterWalk.TypeChangeLink mv wd) :
    Nonempty (DraismaVargas.SubdivisionPencil spec ((p + 2 - n) / 2 + 1)) :=
  RetainedVertexModel.nonempty_evenSubdivisionPencil_of_link_of_injective_vertexModel spec hconn
    hGenus hEven link
    (fun _spec₀ _D _hN _hL hCond _degree _coordinate _ _ _tgt _gdata _wall _cand _strong
      _coordinates _iface dict hFaithful hSpan _hConnected _hSource _face topology hKept ↦
      injective_vertexModel hCond dict hSpan topology hKept hFaithful)

/-- **The Statement, with exactly the binders of
`DraismaVargas.nonempty_evenSubdivisionPencil_ceil_half_genus_add_one`.**
`nonempty_evenSubdivisionPencil_of_link` fed with
`NonTrivalentValencyTwoBaseOneLink.link_all`, the walk's `link` binder with no
hypothesis. -/
theorem nonempty_evenSubdivisionPencil {n p : ℕ} (spec : SubdivisionGraph.Spec n p)
    (hconn : graph_connected spec.graph) (hGenus : 6 ≤ p + 1 - n)
    (hEven : Even (p + 1 - n)) :
    Nonempty (DraismaVargas.SubdivisionPencil spec ((p + 2 - n) / 2 + 1)) :=
  nonempty_evenSubdivisionPencil_of_link spec hconn hGenus hEven
    (fun _ _ ↦ NonTrivalentValencyTwoBaseOneLink.link_all)

end Statement

/-! ## 10.  Non-vacuity

No structure is introduced in this file: `IsGap`, `NearGap`, `NearPlace`,
`ForestClosed` and `NearClass` are `Prop`s about the existing `InputInterface`,
`StrongPresentation`, `ClearedFace` and `CoreDictionary`, and `clsSource` is a
total function into `candidate.datum.SourceVertex`.  Each of them is inhabited,
and the file's headline `nonempty_evenSubdivisionPencil` carries no hypothesis
at all, so nothing in the chain is vacuous. -/

section Inhabited

variable {n p : ℕ} {spec : SubdivisionGraph.Spec n p} {F : Finset (Fin p)}
  {iface : InputInterface spec strong.toPresentation coordinates F}

/-- **`NearPlace` is inhabited**: a placement is in its own zero run. -/
theorem nearPlace_self (u : candidate.datum.SourceVertex) : NearPlace iface face u u :=
  Or.inl rfl

/-- **`ForestClosed` is inhabited**: everything is closed under the forest
rows, and so is the fibre of a requested core vertex at the trivalent-model
producer (`forestClosed_fib`). -/
theorem forestClosed_univ : ForestClosed spec F (Set.univ : Set (Fin n)) :=
  fun _ _ ↦ Iff.rfl

/-- **`NearClass` is inhabited** at every placement of the class
(`nearClass_self`), hence so is the hypothesis `nearClass_step` transports. -/
theorem nearClass_univ (dict : CoreDictionary spec strong iface) (u : Fin n) :
    NearClass iface face dict (Set.univ : Set (Fin n)) (dict.vertexAt u) :=
  nearClass_self dict (Set.mem_univ u)

/-- **`IsGap` and `NearGap` are inhabited** at every retained row displaying
two surviving occurrences: the run between the first two.  At the
trivalent-model producer `isGap_slot_pred` and `isGap_slot_succ` produce them at
every aligned marker
and every breakpoint, which is what `marker_ne_break` consumes. -/
theorem isGap_first {i : Fin p} (h : 1 < (positiveRow iface face i).length) :
    IsGap iface face i
      (RetainedTraversal.position (iface := iface) (face := face) i
        ⟨0, by omega⟩)
      (RetainedTraversal.position (iface := iface) (face := face) i ⟨1, h⟩) :=
  isGap_succ rfl

theorem nearGap_head {i : Fin p} {lo hi : ℕ} (h : lo < hi) :
    NearGap iface i lo hi (RetainedTraversal.rowWalk strong iface i hi) :=
  ⟨hi, h, le_rfl, rfl⟩

end Inhabited

/-! `clsSource` is total, and both of its branches are reached at the
trivalent-model producer itself: `RetainedVertexModel.exists_isHandover` exhibits
a genuine handover
point of the marker-aware expansion of the wedge of two loops, and
`RetainedFibre.isMarker_or_exists_fib` makes every other requested core vertex
the image of a model core vertex. -/

end

end DraismaVargas.LocalCases.RetainedClassInjectivity
