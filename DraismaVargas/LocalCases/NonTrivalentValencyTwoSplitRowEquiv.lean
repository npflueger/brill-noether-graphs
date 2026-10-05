module

public import DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRows
public import DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv

@[expose] public section

/-!
# The row dictionary of the Base II **split** candidate above a two-valent wall

Source: Vargas, Part II (arXiv:2609.09109), Section 5.4 (Configuration A of
Case {v2-nd4}, base tree `T_2` = Base II), with Section 5.1 for the ordinary
blocks.

`NonTrivalentValencyTwoSplitRows` builds the split candidate's anchor
census -- `nd(S) = nd(A_v) = 3`, `nd(P_u) = nd(P_v) = 2`, the bridge alone in
its stable class, the piece and the pass-through lying on the retained rows of
`e_delta` and `e_beta` -- and the unconditional retained-row map
`retainedRowFree`.  This module builds the inverse row map and packages the two
into the equivalence

```text
StablePath (validCandidate ra.setup).datum ≃ Option (StablePath data)
```

over the gauged wall datum of `NonTrivalentValencyTwoSplitGauge`, exactly as
`NonTrivalentValencyTwoRowEquiv` does for the merge member.

## What is new relative to the merge member

The merge candidate has one new occurrence per retained thick class and one
divalent new vertex (only in Configuration B); the split candidate has
**three** new occurrences over the anchor -- the piece, the bridge and the
pass-through -- and **two** divalent new vertices, `P_v` over `v` (carrying the
piece) and `P_u` over `u` (carrying the pass-through).  So the anchor half of
the witness map `newWitness` has three branches rather than two
(`splitAnchorWitness`), and the anchor half of the reverse map's
well-definedness (`rowOfEdge_eq_wall`) has a divalent case on *each* side.
Everything away from the anchor is the argument of
`NonTrivalentValencyTwoRowEquiv` over
`NonTrivalentValencyTwoSplitRows.ordinaryStar`.

## What is proved

* `splitAnchorWitness`, `ordinaryWitness`, `ordSide`, `newWitness`: the old
  survivor whose stable row carries a given new occurrence -- `none` exactly on
  the bridge class (`splitAnchorWitness_bridge`), `e_delta` on the piece class
  (`splitAnchorWitness_piece`), `e_beta` on the pass-through class
  (`splitAnchorWitness_pass`), and over an ordinary block a survivor on the side
  carrying fewer of them (`newWitness_ordinary_spec`).
* `rowOfEdge`, `rowOfEdge_anchor_pair_piece`, `rowOfEdge_anchor_pair_pass`,
  `rowOfEdge_ordinary_pair`, `rowOfEdge_eq_wall`, `rowOfEdge_eq_away` and
  `rowOfEdge_eq_of_consecutive`: the reverse map on surviving occurrences is
  constant on stable paths.
* `rowEquiv`: the two maps are mutually inverse (`rowMap_rowOfEdge` is
  surjectivity, `rowDescend_retainedRow` injectivity), with
  `rowEquiv_retainedRow` and `rowEquiv_bridgeRow`.
* `labelling`: the outgoing candidate's honest stable length-matrix labelling
  over `Option coordinate`, with `labelling_row_retained` and
  `labelling_row_bridge`.

## What is NOT proved -- the hypotheses that remain explicit

1. `SplitAnchor` (from `NonTrivalentValencyTwoSplitRows`) and
   `OrdinaryTrivalent` (the predicate of `NonTrivalentValencyTwoRowEquiv`,
   reused verbatim: it is a statement about the *incoming* datum only).  At an
   actual wall `OrdinaryTrivalent` is discharged by
   `NonTrivalentValencyTwoRowEquiv.ordinaryTrivalent_of_wall_metric`; the
   statement at an actual wall for the split family is not made here.
2. No `AgreeOffColumn` / entrywise common-minor identity against the incoming
   full-dimensional matrix, no chart re-indexing, no exit, no tracking.
3. The orientation is that of `NonTrivalentValencyTwoCandidate`
   (`rightAssignment`: `t_thick` at `u`).

## Consumers

The common minor and the exit of the split family
(`NonTrivalentValencyTwoSplitRowDictionary`, `NonTrivalentValencyTwoSplitExit`)
and the valency-two move dispatcher (`NonTrivalentValencyTwoDispatcher`).
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRowEquiv

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate.Prescribed
  (thickEdge thinEdge rightAssignment)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRows
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv (OrdinaryTrivalent
  sourceEndpoint_eq_of_rel ordinaryTrivalent_degree_one)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (ra : SplitAnchor data star anchor)

local notation "cand" => (validCandidate ra.setup)

local notation "meetP" =>
  (meet (data.edgePartition (thickEdge data star anchor))
    (data.edgePartition (thinEdge data star anchor)))

/-! ## 1.  The chosen side and the witness of a new occurrence -/

/-- The side of an ordinary block along which its new occurrence continues:
the side carrying fewer surviving retained occurrences. -/
noncomputable def ordSide (data : GluingDatum target degree) (star : TwoStar target wall)
    (anchor : WallBlock data wall) (x : Fin degree) : Bool := by
  classical
  exact decide ((ordinaryStar data star anchor x true).card <
    (ordinaryStar data star anchor x false).card)

theorem ordSide_eq_true {x : Fin degree}
    (h : (ordinaryStar data star anchor x true).card <
      (ordinaryStar data star anchor x false).card) :
    ordSide data star anchor x = true := by
  classical
  simpa [ordSide] using h

theorem ordSide_eq_false {x : Fin degree}
    (h : ¬ ((ordinaryStar data star anchor x true).card <
      (ordinaryStar data star anchor x false).card)) :
    ordSide data star anchor x = false := by
  classical
  simpa [ordSide] using h

/-- **The anchor witness.**  Over the anchor block the new occurrence of a sheet
is the piece (whose row is `e_delta`'s), the pass-through (whose row is
`e_beta`'s) or the bridge (which carries no old row). -/
noncomputable def splitAnchorWitness (x : Fin degree) : Option (NonDanglingEdge data) :=
  open Classical in
  if (meetP).Rel (occurrenceSheet ra.deltaEdge) x then
    some ⟨ra.deltaEdge.1,
      NonTrivalentValencyTwoRows.survivor_not_isDangling ra.delta_mem⟩
  else if (meetP).Rel (occurrenceSheet ra.betaEdge) x then
    some ⟨ra.betaEdge.1,
      NonTrivalentValencyTwoRows.survivor_not_isDangling ra.beta_mem⟩
  else none

theorem splitAnchorWitness_piece {x : Fin degree}
    (hRel : (meetP).Rel (occurrenceSheet ra.deltaEdge) x) :
    splitAnchorWitness ra x =
      some ⟨ra.deltaEdge.1,
        NonTrivalentValencyTwoRows.survivor_not_isDangling ra.delta_mem⟩ := by
  classical
  rw [splitAnchorWitness, ite_eq_left hRel]

theorem splitAnchorWitness_pass {x : Fin degree}
    (hNot : ¬ (meetP).Rel (occurrenceSheet ra.deltaEdge) x)
    (hRel : (meetP).Rel (occurrenceSheet ra.betaEdge) x) :
    splitAnchorWitness ra x =
      some ⟨ra.betaEdge.1,
        NonTrivalentValencyTwoRows.survivor_not_isDangling ra.beta_mem⟩ := by
  classical
  rw [splitAnchorWitness, ite_eq_right hNot, ite_eq_left hRel]

theorem splitAnchorWitness_bridge {x : Fin degree}
    (hRel : (meetP).Rel (occurrenceSheet ra.alphaEdge) x) :
    splitAnchorWitness ra x = none := by
  classical
  have hNotDelta : ¬ (meetP).Rel (occurrenceSheet ra.deltaEdge) x := by
    intro hDelta
    exact ra.setup.not_thin
      ((meet_rel_iff _ _ _ _).mp (hRel.trans hDelta.symm)).2
  have hNotBeta : ¬ (meetP).Rel (occurrenceSheet ra.betaEdge) x := by
    intro hBeta
    exact ra.not_thick_rel_alpha_beta
      ((meet_rel_iff _ _ _ _).mp (hRel.trans hBeta.symm)).1
  rw [splitAnchorWitness, ite_eq_right hNotDelta, ite_eq_right hNotBeta]

/-- A chosen survivor on the continuing side of an ordinary block. -/
noncomputable def ordinaryWitness (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) (x : Fin degree) :
    Option (NonDanglingEdge data) :=
  open Classical in
  if h : ∃ old : data.SourceEdge,
      old ∈ ordinaryStar data star anchor x (ordSide data star anchor x) then
    some ⟨Classical.choose h,
      ((mem_ordinaryStar (Classical.choose h)).mp (Classical.choose_spec h)).1.1⟩
  else none

theorem ordinaryWitness_eq {x : Fin degree}
    (h : ∃ old : data.SourceEdge,
      old ∈ ordinaryStar data star anchor x (ordSide data star anchor x)) :
    ∃ old : NonDanglingEdge data, ordinaryWitness data star anchor x = some old ∧
      old.1 ∈ ordinaryStar data star anchor x (ordSide data star anchor x) := by
  classical
  refine ⟨⟨Classical.choose h,
    ((mem_ordinaryStar (Classical.choose h)).mp (Classical.choose_spec h)).1.1⟩, ?_,
    Classical.choose_spec h⟩
  rw [ordinaryWitness, dite_eq_left h]

/-- The old survivor whose stable row carries the new occurrence of the sheet
`x`, when there is one.  At the anchor's bridge class there is none. -/
noncomputable def newWitness (x : Fin degree) : Option (NonDanglingEdge data) :=
  open Classical in
  if (data.vertexPartition wall).Rel anchor.1 x then splitAnchorWitness ra x
  else ordinaryWitness data star anchor x

theorem newWitness_of_anchor {x : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel anchor.1 x) :
    newWitness ra x = splitAnchorWitness ra x := by
  classical
  rw [newWitness, ite_eq_left hAnchor]

theorem newWitness_of_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    newWitness ra x = ordinaryWitness data star anchor x := by
  classical
  rw [newWitness, ite_eq_right hX]

/-! ## 2.  The canonical sheet of a new occurrence -/

theorem newEdge_rel_sheet (y : Fin degree) :
    (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
      (cand).contracts).newEdge.Rel y (newEdgeAt ra y).1.2 :=
  (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
    (cand).contracts).newEdge.rel_repr_right y

theorem wall_rel_newEdgeAt_sheet (y : Fin degree) :
    (data.vertexPartition wall).Rel y (newEdgeAt ra y).1.2 :=
  (newEdge_refines_wall ra).rel (newEdge_rel_sheet ra y)

theorem newEdgeAt_sheet_eq_self (y : Fin degree) :
    newEdgeAt ra ((newEdgeAt ra y).1.2) = newEdgeAt ra y :=
  (newEdgeAt_eq_of_rel ra (newEdge_rel_sheet ra y)).symm

/-- Inside the anchor block the new occurrence of a sheet lies in the
meet-class of that sheet. -/
theorem meet_rel_newEdgeAt_sheet {y : Fin degree}
    (hY : (data.vertexPartition wall).Rel anchor.1 y) :
    (meetP).Rel y (newEdgeAt ra y).1.2 :=
  (newEdge_rel_iff ra hY).mp (newEdge_rel_sheet ra y)

/-! ## 3.  Two survivors alone on their sides lie on one wall-datum row -/

theorem ordinaryStar_eq_of_rel {a b : Fin degree}
    (hRel : (data.vertexPartition wall).Rel a b) (sideValue : Bool) :
    ordinaryStar data star anchor a sideValue =
      ordinaryStar data star anchor b sideValue := by
  classical
  ext old
  rw [mem_ordinaryStar, mem_ordinaryStar, sourceEndpoint_eq_of_rel hRel]

theorem stablePath_eq_of_card_one {x : Fin degree} {sa sb : Bool}
    {a b : NonDanglingEdge data}
    (ha : a.1 ∈ ordinaryStar data star anchor x sa)
    (hb : b.1 ∈ ordinaryStar data star anchor x sb)
    (hca : (ordinaryStar data star anchor x sa).card = 1)
    (hcb : (ordinaryStar data star anchor x sb).card = 1) :
    a.stablePath = b.stablePath := by
  classical
  by_cases hSide : sa = sb
  · subst hSide
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hca
    rw [hc, Finset.mem_singleton] at ha hb
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext (ha.trans hb.symm))
  · have hNeVal : a.1 ≠ b.1 := by
      intro hEq
      apply hSide
      rw [← ((mem_ordinaryStar a.1).mp ha).2, ← ((mem_ordinaryStar b.1).mp hb).2, hEq]
    have hSum := card_ordinaryStar_add (data := data) (star := star) (anchor := anchor) x
    have hVal : nonDanglingValency data (data.sourceEndpoint wall x) = 2 := by
      cases sa <;> cases sb
      · exact absurd rfl hSide
      · omega
      · omega
      · exact absurd rfl hSide
    exact stablePath_eq_of_consecutive ⟨fun hEq ↦ hNeVal (congrArg Subtype.val hEq),
      data.sourceEndpoint wall x, ((mem_ordinaryStar a.1).mp ha).1.2,
      ((mem_ordinaryStar b.1).mp hb).1.2, hVal⟩

/-- At an ordinary block with a surviving new occurrence and surviving valency
at most three, the chosen side really carries exactly one survivor. -/
theorem newWitness_ordinary_spec (hValid : data.Valid) {z : Fin degree}
    (hZ : ¬ (data.vertexPartition wall).Rel anchor.1 z)
    (hLe : nonDanglingValency data (data.sourceEndpoint wall z) ≤ 3)
    (hSurvives : ¬ IsDangling (cand).datum (newEdgeAt ra z)) :
    ∃ w : NonDanglingEdge data, newWitness ra z = some w ∧
      w.1 ∈ ordinaryStar data star anchor z (ordSide data star anchor z) ∧
      (ordinaryStar data star anchor z (ordSide data star anchor z)).card = 1 := by
  classical
  have hFalse := ordinaryStar_card_ne_zero_of_new_survives ra hValid false hZ hSurvives
  have hTrue := ordinaryStar_card_ne_zero_of_new_survives ra hValid true hZ hSurvives
  have hSum := card_ordinaryStar_add (data := data) (star := star) (anchor := anchor) z
  have hCard : (ordinaryStar data star anchor z (ordSide data star anchor z)).card = 1 := by
    by_cases hLt : (ordinaryStar data star anchor z true).card <
        (ordinaryStar data star anchor z false).card
    · rw [ordSide_eq_true hLt]
      omega
    · rw [ordSide_eq_false hLt]
      omega
  have hEx : ∃ old : data.SourceEdge,
      old ∈ ordinaryStar data star anchor z (ordSide data star anchor z) := by
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hCard
    exact ⟨c, by rw [hc]; exact Finset.mem_singleton_self c⟩
  obtain ⟨w, hw, hwMem⟩ := ordinaryWitness_eq hEx
  exact ⟨w, (newWitness_of_ordinary ra hZ).trans hw, hwMem, hCard⟩

/-! ## 4.  The reverse row map on surviving occurrences -/

/-- The wall datum's row carrying a surviving occurrence of the candidate, with
`none` for the bridge row. -/
noncomputable def rowOfEdge (hValid : data.Valid)
    (e : NonDanglingEdge (cand).datum) : Option (StablePath data) :=
  open Classical in
  if h : ∃ old : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old = e then
    some (Classical.choose h).stablePath
  else (newWitness ra e.1.1.2).map NonDanglingEdge.stablePath

theorem rowOfEdge_pos (hValid : data.Valid) (e : NonDanglingEdge (cand).datum)
    (h : ∃ old : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old = e) :
    rowOfEdge ra hValid e = some (Classical.choose h).stablePath := by
  classical
  rw [rowOfEdge, dite_eq_left h]

theorem rowOfEdge_neg (hValid : data.Valid) (e : NonDanglingEdge (cand).datum)
    (h : ¬ ∃ old : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old = e) :
    rowOfEdge ra hValid e = (newWitness ra e.1.1.2).map NonDanglingEdge.stablePath := by
  classical
  rw [rowOfEdge, dite_eq_right h]

theorem rowOfEdge_retained (hValid : data.Valid) (old : NonDanglingEdge data) :
    rowOfEdge ra hValid (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old) =
      some old.stablePath := by
  classical
  have h : ∃ o : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 o =
        ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old := ⟨old, rfl⟩
  rw [rowOfEdge_pos ra hValid _ h]
  exact congrArg (fun o : NonDanglingEdge data ↦ some o.stablePath)
    (ResolutionAwayFromWall.retainedEdge_injective (cand) hValid.1 (Classical.choose_spec h))

theorem rowOfEdge_old (hValid : data.Valid) {old : data.SourceEdge}
    (hSurvives : ¬ IsDangling (cand).datum ((cand).oldSourceEdge old))
    (hData : ¬ IsDangling data old) :
    rowOfEdge ra hValid ⟨(cand).oldSourceEdge old, hSurvives⟩ =
      some (NonDanglingEdge.stablePath (⟨old, hData⟩ : NonDanglingEdge data)) :=
  rowOfEdge_retained ra hValid ⟨old, hData⟩

theorem rowOfEdge_new (hValid : data.Valid) {y : Fin degree}
    (hSurvives : ¬ IsDangling (cand).datum (newEdgeAt ra y)) :
    rowOfEdge ra hValid ⟨newEdgeAt ra y, hSurvives⟩ =
      (newWitness ra (newEdgeAt ra y).1.2).map NonDanglingEdge.stablePath := by
  classical
  have hNot : ¬ ∃ old : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old =
        (⟨newEdgeAt ra y, hSurvives⟩ : NonDanglingEdge (cand).datum) := by
    rintro ⟨old, hEq⟩
    exact newEdgeAt_ne_oldSourceEdge ra y old.1 (congrArg Subtype.val hEq).symm
  exact rowOfEdge_neg ra hValid _ hNot

/-! ## 5.  The reverse map is constant on stable paths -/

theorem rowOfEdge_eq_away (hValid : data.Valid) {v : (cand).datum.SourceVertex}
    {place : target.V} (hAway : place ≠ wall) (hTarget : v.1.1 = oldVertex target place)
    {e f : NonDanglingEdge (cand).datum} (hNe : e ≠ f)
    (hE : Incident (cand).datum e.1 v) (hF : Incident (cand).datum f.1 v)
    (hValency : nonDanglingValency (cand).datum v = 2) :
    rowOfEdge ra hValid e = rowOfEdge ra hValid f := by
  obtain ⟨old, hOldTarget, hOldVertex⟩ :=
    ResolutionAwayFromWall.exists_retainedVertex_of_target (cand) v place hAway hTarget
  have hOldAway : old.1.1 ≠ wall := fun hEq ↦ hAway (hOldTarget.symm.trans hEq)
  subst hOldVertex
  rcases ResolutionAwayFromWall.nonDanglingEdge_cases (cand) hValid
    (candidate_sourceGenus ra) e with ⟨oe, rfl⟩ | ⟨sheet, hSheet, rfl⟩
  · rcases ResolutionAwayFromWall.nonDanglingEdge_cases (cand) hValid
      (candidate_sourceGenus ra) f with ⟨of, rfl⟩ | ⟨sheet, hSheet, rfl⟩
    · rw [rowOfEdge_retained ra hValid oe, rowOfEdge_retained ra hValid of]
      refine congrArg (fun r : StablePath data ↦ some r)
        (stablePath_eq_of_consecutive ⟨?_, old, ?_, ?_, ?_⟩)
      · exact fun hEq ↦ hNe (congrArg
          (ResolutionAwayFromWall.retainedEdge (cand) hValid.1) hEq)
      · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff (cand) old hOldAway oe.1).mp hE
      · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff (cand) old hOldAway of.1).mp hF
      · exact (ResolutionAwayFromWall.nonDanglingValency_retainedVertex (cand) hValid
          (candidate_sourceGenus ra) old hOldAway).symm.trans hValency
    · exact absurd hF
        (ResolutionAwayFromWall.not_incident_newSourceEdge (cand) old hOldAway sheet)
  · exact absurd hE
      (ResolutionAwayFromWall.not_incident_newSourceEdge (cand) old hOldAway sheet)

/-- **The piece and `e_delta`'s retained occurrence carry the same row.** -/
theorem rowOfEdge_anchor_pair_piece (hValid : data.Valid)
    (hNewSurv : ¬ IsDangling (cand).datum (newEdgeAt ra (occurrenceSheet ra.deltaEdge)))
    (hOldSurv : ¬ IsDangling (cand).datum ((cand).oldSourceEdge ra.deltaEdge.1)) :
    rowOfEdge ra hValid ⟨newEdgeAt ra (occurrenceSheet ra.deltaEdge), hNewSurv⟩ =
      rowOfEdge ra hValid ⟨(cand).oldSourceEdge ra.deltaEdge.1, hOldSurv⟩ := by
  classical
  have hDataSurv : ¬ IsDangling data ra.deltaEdge.1 :=
    NonTrivalentValencyTwoRows.survivor_not_isDangling ra.delta_mem
  rw [rowOfEdge_old ra hValid hOldSurv hDataSurv,
    rowOfEdge_new ra hValid (y := occurrenceSheet ra.deltaEdge) hNewSurv]
  have hAnchorZ : (data.vertexPartition wall).Rel anchor.1
      (newEdgeAt ra (occurrenceSheet ra.deltaEdge)).1.2 :=
    (occurrenceSheet_wall_rel ra.deltaEdge).trans (wall_rel_newEdgeAt_sheet ra _)
  have hMeet := meet_rel_newEdgeAt_sheet ra (occurrenceSheet_wall_rel ra.deltaEdge)
  rw [newWitness_of_anchor ra hAnchorZ, splitAnchorWitness_piece ra hMeet]
  rfl

/-- **The pass-through and `e_beta`'s retained occurrence carry the same
row.** -/
theorem rowOfEdge_anchor_pair_pass (hValid : data.Valid)
    (hNewSurv : ¬ IsDangling (cand).datum (newEdgeAt ra (occurrenceSheet ra.betaEdge)))
    (hOldSurv : ¬ IsDangling (cand).datum ((cand).oldSourceEdge ra.betaEdge.1)) :
    rowOfEdge ra hValid ⟨newEdgeAt ra (occurrenceSheet ra.betaEdge), hNewSurv⟩ =
      rowOfEdge ra hValid ⟨(cand).oldSourceEdge ra.betaEdge.1, hOldSurv⟩ := by
  classical
  have hDataSurv : ¬ IsDangling data ra.betaEdge.1 :=
    NonTrivalentValencyTwoRows.survivor_not_isDangling ra.beta_mem
  rw [rowOfEdge_old ra hValid hOldSurv hDataSurv,
    rowOfEdge_new ra hValid (y := occurrenceSheet ra.betaEdge) hNewSurv]
  have hAnchorZ : (data.vertexPartition wall).Rel anchor.1
      (newEdgeAt ra (occurrenceSheet ra.betaEdge)).1.2 :=
    (occurrenceSheet_wall_rel ra.betaEdge).trans (wall_rel_newEdgeAt_sheet ra _)
  have hMeet := meet_rel_newEdgeAt_sheet ra (occurrenceSheet_wall_rel ra.betaEdge)
  have hNotDelta : ¬ (meetP).Rel (occurrenceSheet ra.deltaEdge)
      (newEdgeAt ra (occurrenceSheet ra.betaEdge)).1.2 := by
    intro hDelta
    refine ra.not_thick_rel_alpha_beta ?_
    exact ra.thick_rel_alpha_delta.trans
      ((meet_rel_iff _ _ _ _).mp (hDelta.trans hMeet.symm)).1
  rw [newWitness_of_anchor ra hAnchorZ, splitAnchorWitness_pass ra hNotDelta hMeet]
  rfl

/-- An ordinary block whose side carries a single survivor: the new occurrence
and that survivor carry the same wall-datum row. -/
theorem rowOfEdge_ordinary_pair (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hNewSurv : ¬ IsDangling (cand).datum (newEdgeAt ra x))
    {old : data.SourceEdge} (hOld : old ∈ ordinaryStar data star anchor x sideValue)
    (hCard : (ordinaryStar data star anchor x sideValue).card = 1)
    (hOldSurv : ¬ IsDangling (cand).datum ((cand).oldSourceEdge old)) :
    rowOfEdge ra hValid ⟨newEdgeAt ra x, hNewSurv⟩ =
      rowOfEdge ra hValid ⟨(cand).oldSourceEdge old, hOldSurv⟩ := by
  classical
  have hDataSurv : ¬ IsDangling data old := ((mem_ordinaryStar old).mp hOld).1.1
  rw [rowOfEdge_old ra hValid hOldSurv hDataSurv, rowOfEdge_new ra hValid hNewSurv]
  have hWallRel : (data.vertexPartition wall).Rel x (newEdgeAt ra x).1.2 :=
    wall_rel_newEdgeAt_sheet ra x
  have hZ : ¬ (data.vertexPartition wall).Rel anchor.1 (newEdgeAt ra x).1.2 :=
    fun h ↦ hX (h.trans hWallRel.symm)
  have hStar : ∀ t : Bool,
      ordinaryStar data star anchor ((newEdgeAt ra x).1.2) t =
        ordinaryStar data star anchor x t :=
    fun t ↦ ordinaryStar_eq_of_rel hWallRel.symm t
  have hSurvZ : ¬ IsDangling (cand).datum (newEdgeAt ra ((newEdgeAt ra x).1.2)) := by
    rw [newEdgeAt_sheet_eq_self ra x]
    exact hNewSurv
  obtain ⟨w, hw, hwMem, hwCard⟩ := newWitness_ordinary_spec ra hValid hZ (hOrd _ hZ) hSurvZ
  rw [hw]
  refine congrArg (fun r : StablePath data ↦ some r) ?_
  refine stablePath_eq_of_card_one (x := (newEdgeAt ra x).1.2) (sb := sideValue)
    hwMem ?_ hwCard ?_
  · rw [hStar sideValue]
    exact hOld
  · rw [hStar sideValue]
    exact hCard

theorem rowOfEdge_eq_wall (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) (sideValue : Bool)
    {v : (cand).datum.SourceVertex} (x : Fin degree)
    (hv : endpointVertex ra sideValue x = v)
    {e f : NonDanglingEdge (cand).datum} (hNe : e ≠ f)
    (hE : Incident (cand).datum e.1 v) (hF : Incident (cand).datum f.1 v)
    (hValency : nonDanglingValency (cand).datum v = 2) :
    rowOfEdge ra hValid e = rowOfEdge ra hValid f := by
  classical
  subst hv
  have hNeVal : e.1 ≠ f.1 := fun hEq ↦ hNe (Subtype.ext hEq)
  by_cases hA : (data.vertexPartition wall).Rel anchor.1 x
  · cases sideValue
    · rcases ra.thick_cover hA with hCase | hCase
      · exfalso
        have hEq : endpointVertex ra false (occurrenceSheet ra.alphaEdge) =
            endpointVertex ra false x :=
          endpointVertex_eq ra false (occurrenceSheet_wall_rel ra.alphaEdge) hCase
        rw [← hEq, nonDanglingValency_endpointVertex_alpha ra hValid] at hValency
        omega
      · have hEq : endpointVertex ra false (occurrenceSheet ra.betaEdge) =
            endpointVertex ra false x :=
          endpointVertex_eq ra false (occurrenceSheet_wall_rel ra.betaEdge) hCase
        have hStar := nonDanglingIncident_endpointVertex_beta ra hValid
        rw [hEq] at hStar
        have hEmem : e.1 ∈ nonDanglingIncident (cand).datum (endpointVertex ra false x) :=
          (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hE⟩
        have hFmem : f.1 ∈ nonDanglingIncident (cand).datum (endpointVertex ra false x) :=
          (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, hF⟩
        rw [hStar, Finset.mem_insert, Finset.mem_singleton] at hEmem hFmem
        rcases hEmem with hEc | hEc <;> rcases hFmem with hFc | hFc
        · exact absurd (hEc.trans hFc.symm) hNeVal
        · have hNewSurv : ¬ IsDangling (cand).datum (passEdge ra) := by
            rw [← hEc]; exact e.2
          have hOldSurv : ¬ IsDangling (cand).datum
              ((cand).oldSourceEdge ra.betaEdge.1) := by
            rw [← hFc]; exact f.2
          rw [show e = (⟨_, hNewSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hEc,
            show f = (⟨_, hOldSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hFc]
          exact rowOfEdge_anchor_pair_pass ra hValid hNewSurv hOldSurv
        · have hOldSurv : ¬ IsDangling (cand).datum
              ((cand).oldSourceEdge ra.betaEdge.1) := by
            rw [← hEc]; exact e.2
          have hNewSurv : ¬ IsDangling (cand).datum (passEdge ra) := by
            rw [← hFc]; exact f.2
          rw [show e = (⟨_, hOldSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hEc,
            show f = (⟨_, hNewSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hFc]
          exact (rowOfEdge_anchor_pair_pass ra hValid hNewSurv hOldSurv).symm
        · exact absurd (hEc.trans hFc.symm) hNeVal
    · rcases ra.setup.cover x hA with hCase | hCase
      · have hEq : endpointVertex ra true (occurrenceSheet ra.deltaEdge) =
            endpointVertex ra true x :=
          endpointVertex_eq ra true (occurrenceSheet_wall_rel ra.deltaEdge) hCase
        have hStar := nonDanglingIncident_endpointVertex_delta ra hValid
        rw [hEq] at hStar
        have hEmem : e.1 ∈ nonDanglingIncident (cand).datum (endpointVertex ra true x) :=
          (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hE⟩
        have hFmem : f.1 ∈ nonDanglingIncident (cand).datum (endpointVertex ra true x) :=
          (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, hF⟩
        rw [hStar, Finset.mem_insert, Finset.mem_singleton] at hEmem hFmem
        rcases hEmem with hEc | hEc <;> rcases hFmem with hFc | hFc
        · exact absurd (hEc.trans hFc.symm) hNeVal
        · have hNewSurv : ¬ IsDangling (cand).datum (pieceEdge ra) := by
            rw [← hEc]; exact e.2
          have hOldSurv : ¬ IsDangling (cand).datum
              ((cand).oldSourceEdge ra.deltaEdge.1) := by
            rw [← hFc]; exact f.2
          rw [show e = (⟨_, hNewSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hEc,
            show f = (⟨_, hOldSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hFc]
          exact rowOfEdge_anchor_pair_piece ra hValid hNewSurv hOldSurv
        · have hOldSurv : ¬ IsDangling (cand).datum
              ((cand).oldSourceEdge ra.deltaEdge.1) := by
            rw [← hEc]; exact e.2
          have hNewSurv : ¬ IsDangling (cand).datum (pieceEdge ra) := by
            rw [← hFc]; exact f.2
          rw [show e = (⟨_, hOldSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hEc,
            show f = (⟨_, hNewSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hFc]
          exact (rowOfEdge_anchor_pair_piece ra hValid hNewSurv hOldSurv).symm
        · exact absurd (hEc.trans hFc.symm) hNeVal
      · exfalso
        have hEq : endpointVertex ra true (occurrenceSheet ra.alphaEdge) =
            endpointVertex ra true x :=
          endpointVertex_eq ra true (occurrenceSheet_wall_rel ra.alphaEdge) hCase
        rw [← hEq, endpointVertex_true_alpha ra,
          nonDanglingValency_endpointVertex_epsilon ra hValid] at hValency
        omega
  · have hEmem := (mem_nonDanglingIncident_endpointVertex_ordinary ra hValid
      sideValue hA e.1).mp ((mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hE⟩)
    have hFmem := (mem_nonDanglingIncident_endpointVertex_ordinary ra hValid
      sideValue hA f.1).mp ((mem_nonDanglingIncident _ _ _).mpr ⟨f.2, hF⟩)
    by_cases hDang : IsDangling (cand).datum (newEdgeAt ra x)
    · have hCard2 : (ordinaryStar data star anchor x sideValue).card = 2 := by
        have hEq := nonDanglingValency_endpointVertex_of_new_dangling ra hValid
          sideValue hA hDang
        omega
      have hSum := card_ordinaryStar_add (data := data) (star := star) (anchor := anchor) x
      have hLe := hOrd x hA
      have hOther := nonDanglingValency_endpointVertex_of_new_dangling ra hValid
        (!sideValue) hA hDang
      have hNeOne := nonDanglingValency_candidate_ne_one ra hValid
        (endpointVertex ra (!sideValue) x)
      rw [hOther] at hNeOne
      have hValData : nonDanglingValency data (data.sourceEndpoint wall x) = 2 := by
        cases sideValue
        · simp only [Bool.not_false] at hNeOne
          omega
        · simp only [Bool.not_true] at hNeOne
          omega
      rcases hEmem with ⟨oe, hoe, hEc⟩ | ⟨-, hSurv⟩
      · rcases hFmem with ⟨of, hof, hFc⟩ | ⟨-, hSurv⟩
        · have hoeData : ¬ IsDangling data oe := ((mem_ordinaryStar oe).mp hoe).1.1
          have hofData : ¬ IsDangling data of := ((mem_ordinaryStar of).mp hof).1.1
          have hoeSurv : ¬ IsDangling (cand).datum ((cand).oldSourceEdge oe) := by
            rw [← hEc]; exact e.2
          have hofSurv : ¬ IsDangling (cand).datum ((cand).oldSourceEdge of) := by
            rw [← hFc]; exact f.2
          rw [show e = (⟨_, hoeSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hEc,
            show f = (⟨_, hofSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hFc,
            rowOfEdge_old ra hValid hoeSurv hoeData,
            rowOfEdge_old ra hValid hofSurv hofData]
          refine congrArg (fun r : StablePath data ↦ some r)
            (stablePath_eq_of_consecutive ⟨?_, data.sourceEndpoint wall x, ?_, ?_, hValData⟩)
          · intro hEq
            apply hNeVal
            rw [hEc, hFc]
            exact congrArg (fun r : NonDanglingEdge data ↦ (cand).oldSourceEdge r.1) hEq
          · exact ((mem_ordinaryStar oe).mp hoe).1.2
          · exact ((mem_ordinaryStar of).mp hof).1.2
        · exact absurd hDang hSurv
      · exact absurd hDang hSurv
    · have hCard1 : (ordinaryStar data star anchor x sideValue).card = 1 := by
        have hEq := nonDanglingValency_endpointVertex_of_new_survives ra hValid
          sideValue hA hDang
        omega
      rcases hEmem with ⟨oe, hoe, hEc⟩ | ⟨hEc, hSurvE⟩
      · rcases hFmem with ⟨of, hof, hFc⟩ | ⟨hFc, hSurvF⟩
        · exfalso
          obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hCard1
          rw [hc, Finset.mem_singleton] at hoe hof
          exact hNeVal (by rw [hEc, hFc, hoe, hof])
        · have hoeSurv : ¬ IsDangling (cand).datum ((cand).oldSourceEdge oe) := by
            rw [← hEc]; exact e.2
          rw [show e = (⟨_, hoeSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hEc,
            show f = (⟨_, hSurvF⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hFc]
          exact (rowOfEdge_ordinary_pair ra hValid hOrd sideValue hA hSurvF hoe
            hCard1 hoeSurv).symm
      · rcases hFmem with ⟨of, hof, hFc⟩ | ⟨hFc, hSurvF⟩
        · have hofSurv : ¬ IsDangling (cand).datum ((cand).oldSourceEdge of) := by
            rw [← hFc]; exact f.2
          rw [show e = (⟨_, hSurvE⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hEc,
            show f = (⟨_, hofSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hFc]
          exact rowOfEdge_ordinary_pair ra hValid hOrd sideValue hA hSurvE hof
            hCard1 hofSurv
        · exact absurd (hEc.trans hFc.symm) hNeVal

/-- **The reverse row map descends to stable paths.** -/
theorem rowOfEdge_eq_of_consecutive (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor)
    {e f : NonDanglingEdge (cand).datum} (h : Consecutive (cand).datum e f) :
    rowOfEdge ra hValid e = rowOfEdge ra hValid f := by
  obtain ⟨hNe, v, hE, hF, hValency⟩ := h
  cases hTarget : v.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · rw [hAt] at hTarget
        exact rowOfEdge_eq_wall ra hValid hOrd false v.1.2
          (((cand).datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨hTarget.symm, rfl⟩)
          hNe hE hF hValency
      · exact rowOfEdge_eq_away ra hValid hAt hTarget hNe hE hF hValency
  | inr point =>
      cases point
      exact rowOfEdge_eq_wall ra hValid hOrd true v.1.2
        (((cand).datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨hTarget.symm, rfl⟩)
        hNe hE hF hValency

/-! ## 6.  The row equivalence -/

/-- The candidate's one new stable row: the bridge. -/
noncomputable def bridgeRow (hValid : data.Valid) : StablePath (cand).datum :=
  NonDanglingEdge.stablePath
    (⟨bridgeEdge ra, bridgeEdge_survives ra hValid⟩ : NonDanglingEdge (cand).datum)

theorem rowOfEdge_bridge (hValid : data.Valid) :
    rowOfEdge ra hValid
      (⟨bridgeEdge ra, bridgeEdge_survives ra hValid⟩ :
        NonDanglingEdge (cand).datum) = none := by
  refine Eq.trans (rowOfEdge_new ra hValid (y := occurrenceSheet ra.alphaEdge)
    (bridgeEdge_survives ra hValid)) ?_
  rw [newWitness_of_anchor ra
      ((occurrenceSheet_wall_rel ra.alphaEdge).trans (wall_rel_newEdgeAt_sheet ra _)),
    splitAnchorWitness_bridge ra
      (meet_rel_newEdgeAt_sheet ra (occurrenceSheet_wall_rel ra.alphaEdge))]
  rfl

/-- The reverse row map, on stable paths. -/
noncomputable def rowDescend (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) :
    StablePath (cand).datum → Option (StablePath data) :=
  Quot.lift (rowOfEdge ra hValid)
    (fun _ _ h ↦ rowOfEdge_eq_of_consecutive ra hValid hOrd h)

@[simp] theorem rowDescend_mk (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) (e : NonDanglingEdge (cand).datum) :
    rowDescend ra hValid hOrd e.stablePath = rowOfEdge ra hValid e := rfl

/-- The forward row map: the bridge row for `none`, the retained row for a row
of the incoming wall datum. -/
noncomputable def rowMap (hValid : data.Valid) :
    Option (StablePath data) → StablePath (cand).datum
  | none => bridgeRow ra hValid
  | some r => retainedRowFree ra hValid r

theorem rowDescend_bridgeRow (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) :
    rowDescend ra hValid hOrd (bridgeRow ra hValid) = none :=
  rowOfEdge_bridge ra hValid

theorem rowDescend_retainedRow (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) (r : StablePath data) :
    rowDescend ra hValid hOrd (retainedRowFree ra hValid r) = some r := by
  induction r using Quot.inductionOn with
  | h e => exact rowOfEdge_retained ra hValid e

/-- **Every stable row of the split candidate is a retained row or the bridge
row.** -/
theorem rowMap_rowOfEdge (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) (e : NonDanglingEdge (cand).datum) :
    rowMap ra hValid (rowOfEdge ra hValid e) = e.stablePath := by
  classical
  rcases ResolutionAwayFromWall.nonDanglingEdge_cases (cand) hValid
    (candidate_sourceGenus ra) e with ⟨old, rfl⟩ | ⟨y, hSurv, rfl⟩
  · rw [rowOfEdge_retained ra hValid old]
    rfl
  · rw [show rowOfEdge ra hValid ⟨(cand).newSourceEdge y, hSurv⟩ =
      (newWitness ra (newEdgeAt ra y).1.2).map NonDanglingEdge.stablePath from
      rowOfEdge_new ra hValid (y := y) hSurv]
    have hSelf : newEdgeAt ra ((newEdgeAt ra y).1.2) = newEdgeAt ra y :=
      newEdgeAt_sheet_eq_self ra y
    have hSurvZ : ¬ IsDangling (cand).datum (newEdgeAt ra ((newEdgeAt ra y).1.2)) := by
      rw [hSelf]
      exact hSurv
    by_cases hAnchorZ :
        (data.vertexPartition wall).Rel anchor.1 (newEdgeAt ra y).1.2
    · rw [newWitness_of_anchor ra hAnchorZ]
      rcases ra.thick_cover hAnchorZ with hT | hT
      · rcases ra.setup.cover _ hAnchorZ with hN | hN
        · have hMeet : (meetP).Rel (occurrenceSheet ra.deltaEdge)
              (newEdgeAt ra y).1.2 :=
            (meet_rel_iff _ _ _ _).mpr ⟨ra.thick_rel_alpha_delta.symm.trans hT, hN⟩
          rw [splitAnchorWitness_piece ra hMeet]
          have hNewEq : newEdgeAt ra y = pieceEdge ra :=
            newEdgeAt_eq_of_meet_rel ra (occurrenceSheet_wall_rel ra.deltaEdge) hMeet
          have hCast : NonDanglingEdge.stablePath
              (⟨(cand).newSourceEdge y, hSurv⟩ : NonDanglingEdge (cand).datum) =
              NonDanglingEdge.stablePath
              (⟨pieceEdge ra, pieceEdge_survives ra hValid⟩ :
                NonDanglingEdge (cand).datum) :=
            congrArg NonDanglingEdge.stablePath (Subtype.ext hNewEq)
          rw [hCast, pieceEdge_stablePath_eq_retained ra hValid]
          rfl
        · have hMeet : (meetP).Rel (occurrenceSheet ra.alphaEdge)
              (newEdgeAt ra y).1.2 :=
            (meet_rel_iff _ _ _ _).mpr ⟨hT, hN⟩
          rw [splitAnchorWitness_bridge ra hMeet]
          have hNewEq : newEdgeAt ra y = bridgeEdge ra :=
            newEdgeAt_eq_of_meet_rel ra (occurrenceSheet_wall_rel ra.alphaEdge) hMeet
          exact (congrArg NonDanglingEdge.stablePath (Subtype.ext hNewEq)).symm
      · rcases ra.setup.cover _ hAnchorZ with hN | hN
        · exfalso
          refine ra.not_thick_rel_alpha_beta ?_
          have hInside : (data.edgePartition (thickEdge data star anchor)).Rel
              (occurrenceSheet ra.alphaEdge) (newEdgeAt ra y).1.2 :=
            ((data.edgePartition (thickEdge data star anchor)).mem_block_iff _ _).mp
              (ra.setup.sub
                (((data.edgePartition (thinEdge data star anchor)).mem_block_iff _ _).mpr hN))
          exact hInside.trans hT.symm
        · have hMeet : (meetP).Rel (occurrenceSheet ra.betaEdge)
              (newEdgeAt ra y).1.2 :=
            (meet_rel_iff _ _ _ _).mpr ⟨hT, ra.thin_rel_alpha_beta.symm.trans hN⟩
          have hNotDelta : ¬ (meetP).Rel (occurrenceSheet ra.deltaEdge)
              (newEdgeAt ra y).1.2 := by
            intro hDelta
            refine ra.not_thick_rel_alpha_beta ?_
            exact ra.thick_rel_alpha_delta.trans
              ((meet_rel_iff _ _ _ _).mp (hDelta.trans hMeet.symm)).1
          rw [splitAnchorWitness_pass ra hNotDelta hMeet]
          have hNewEq : newEdgeAt ra y = passEdge ra :=
            newEdgeAt_eq_of_meet_rel ra (occurrenceSheet_wall_rel ra.betaEdge) hMeet
          have hCast : NonDanglingEdge.stablePath
              (⟨(cand).newSourceEdge y, hSurv⟩ : NonDanglingEdge (cand).datum) =
              NonDanglingEdge.stablePath
              (⟨passEdge ra, passEdge_survives ra hValid⟩ :
                NonDanglingEdge (cand).datum) :=
            congrArg NonDanglingEdge.stablePath (Subtype.ext hNewEq)
          rw [hCast, passEdge_stablePath_eq_retained ra hValid]
          rfl
    · obtain ⟨w, hw, hwMem, hwCard⟩ := newWitness_ordinary_spec ra hValid hAnchorZ
        (hOrd _ hAnchorZ) hSurvZ
      rw [hw]
      refine Eq.trans (stablePath_retainedEdge_eq_newEdgeAt ra hValid _ hAnchorZ
        hwMem hwCard hSurvZ) ?_
      exact congrArg NonDanglingEdge.stablePath (Subtype.ext hSelf)

/-- **The row dictionary of the Base II split candidate.** -/
noncomputable def rowEquiv (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) :
    StablePath (cand).datum ≃ Option (StablePath data) where
  toFun := rowDescend ra hValid hOrd
  invFun := rowMap ra hValid
  left_inv := by
    intro path
    induction path using Quot.inductionOn with
    | h e => exact rowMap_rowOfEdge ra hValid hOrd e
  right_inv := by
    intro r
    cases r with
    | none => exact rowDescend_bridgeRow ra hValid hOrd
    | some r => exact rowDescend_retainedRow ra hValid hOrd r

@[simp] theorem rowEquiv_retainedRow (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) (r : StablePath data) :
    rowEquiv ra hValid hOrd (retainedRowFree ra hValid r) = some r :=
  rowDescend_retainedRow ra hValid hOrd r

@[simp] theorem rowEquiv_bridgeRow (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) :
    rowEquiv ra hValid hOrd (bridgeRow ra hValid) = none :=
  rowDescend_bridgeRow ra hValid hOrd

/-! ## 7.  The honest labelling of the outgoing candidate -/

/-- **The honest stable length-matrix labelling of the outgoing split
candidate.**  The wall datum's own square labelling supplies every retained row
and column; `Option.none` is the vanishing coordinate of the incoming chart,
re-used for the new target edge `t_1` and for the bridge row `h_1`. -/
noncomputable def labelling {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor)
    (labelling₀ : StableLengthMatrixLabelling data coordinate) :
    StableLengthMatrixLabelling (cand).datum (Option coordinate) where
  targetEdge := (Equiv.optionCongr labelling₀.targetEdge).trans
    (occurrenceEquiv target wall (cand).right)
  row := (rowEquiv ra hValid hOrd).trans (Equiv.optionCongr labelling₀.row)

@[simp] theorem labelling_targetEdge_none {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor)
    (labelling₀ : StableLengthMatrixLabelling data coordinate) :
    (labelling ra hValid hOrd labelling₀).targetEdge none =
      occurrenceEquiv target wall (cand).right none := rfl

@[simp] theorem labelling_targetEdge_some {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor)
    (labelling₀ : StableLengthMatrixLabelling data coordinate) (c : coordinate) :
    (labelling ra hValid hOrd labelling₀).targetEdge (some c) =
      occurrenceEquiv target wall (cand).right (some (labelling₀.targetEdge c)) := rfl

@[simp] theorem labelling_row_retained {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor)
    (labelling₀ : StableLengthMatrixLabelling data coordinate) (r : StablePath data) :
    (labelling ra hValid hOrd labelling₀).row (retainedRowFree ra hValid r) =
      some (labelling₀.row r) := by
  show (Equiv.optionCongr labelling₀.row)
    (rowEquiv ra hValid hOrd (retainedRowFree ra hValid r)) = _
  rw [rowEquiv_retainedRow]
  rfl

@[simp] theorem labelling_row_bridge {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor)
    (labelling₀ : StableLengthMatrixLabelling data coordinate) :
    (labelling ra hValid hOrd labelling₀).row (bridgeRow ra hValid) = none := by
  show (Equiv.optionCongr labelling₀.row) (rowEquiv ra hValid hOrd (bridgeRow ra hValid)) = _
  rw [rowEquiv_bridgeRow]
  rfl

end DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRowEquiv
