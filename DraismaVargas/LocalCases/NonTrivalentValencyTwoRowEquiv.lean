module

public import DraismaVargas.LocalCases.NonTrivalentValencyTwoDescent

@[expose] public section

/-!
# The row dictionary of the prescribed valency-two candidate

Source: Vargas, Part II, arXiv:2609.09109, Section 5.4 (valency-2 limits, case `{v2-nd4}`), with
Section 5.1 (rigidity above `w_0`, `lemma-above-w0`) for the ordinary blocks.

`NonTrivalentValencyTwoRows` builds `retainedRow` modulo `OrdinaryBlockDescent`,
and `NonTrivalentValencyTwoDescent` discharges that `Prop`; this module builds
the inverse row map and packages the two into the
equivalence `StablePath (validCandidate sel).datum ≃ Option (StablePath data)`
that `NonTrivalentValencyTwoRows.labelling` takes as its argument.

## What is proved

* `OrdinaryTrivalent`: the numerical input from Part II, Section 5.1 (every
  vertex of `H_0` other than the four-valent `A` is trivalent) -- every wall
  block other than the anchor has surviving valency at most three -- isolated as
  a named `Prop` on the wall datum, with the non-vacuity
  witness `ordinaryTrivalent_degree_one` and the substantive inhabitant
  `ordinaryTrivalent_of_wall_metric`.
* `newWitness`: the old survivor whose stable row carries a given new
  occurrence, `none` on the bridge class.  Over the anchor it is the retained
  thick survivor of the sheet's fine class (`anchorWitness_eq`); over an
  ordinary block it is a survivor on the side carrying fewer of them
  (`ordSide`, `newWitness_ordinary_spec`), which by the census and `nd(B) <= 3`
  carries exactly one.
* `rowOfEdge` and `rowOfEdge_eq_of_consecutive`: the reverse map on surviving
  occurrences is constant on stable paths.  The three geometric inputs are
  `ResolutionAwayFromWall` off the wall, the exact stars at the anchor of
  `NonTrivalentValencyTwoRows`
  (`nonDanglingIncident_extraEndpointVertex`,
  `nonDanglingValency_endpointVertex_false/true`), and the ordinary-block census
  of `NonTrivalentValencyTwoDescent`.
* `rowEquiv`: the two maps are mutually inverse -- `rowMap_rowOfEdge` is
  surjectivity (every candidate row contains a retained occurrence or is the
  bridge row) and `rowDescend_retainedRow` is injectivity -- with
  `rowEquiv_retainedRow` and `rowEquiv_bridgeRow`.
* `labelling`: `NonTrivalentValencyTwoRows.labelling` instantiated, so the
  outgoing candidate's honest stable length-matrix labelling needs no supplied
  row equivalence; `labelling_row_retained` and `labelling_row_bridge`.
* `exists_rowEquiv_of_wall_metric`: the whole package at an actual two-valent
  wall, with `nd(A) = 4` and `OrdinaryTrivalent` both discharged from the wall
  metric of the existence route.

## What is not proved here

The `AgreeOffColumn` / entrywise common-minor identity of the outgoing labelled
matrix against the incoming full-dimensional matrix, on the pattern of
`NonTrivalentValencyFourRowDictionary.matrix_chartLabelling_eq_incoming`; that
is `NonTrivalentValencyTwoRowDictionary`.
Nothing here constructs a `FullDimensionalSourcePresentation`, a
`ContractionForest`, a star or the wall metric; the Section 8 statements carry
them.

## Consumers

The boundary dispatcher for Part II case `{v2-nd4}`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv

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
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRows
open DraismaVargas.LocalCases.NonTrivalentValencyTwoDescent

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall}
  (source : TwoBranchAnchor data star anchor)
  (sel : Prescribed.Selection data star anchor)

local notation "cand" => (Prescribed.validCandidate sel)

local notation "rep" => (Prescribed.selectedRepresentative sel)

/-! ## 1.  The source input: ordinary blocks are trivalent -/

/-- The trivalence of the wall datum away from the anchor, in sheet form.  This
is the numerical input from Part II, Section 5.1 (every vertex of `H_0` other
than `A` is trivalent), supplied at an actual wall by
`NonTrivalentAnchorValency.nonDanglingValency_wallBlock_le_three_of_twoStar`. -/
def OrdinaryTrivalent (data : GluingDatum target degree) (wall : target.V)
    (anchor : WallBlock data wall) : Prop :=
  ∀ y : Fin degree, ¬ (data.vertexPartition wall).Rel anchor.1 y →
    nonDanglingValency data (data.sourceEndpoint wall y) ≤ 3

theorem sourceEndpoint_eq_of_rel {a b : Fin degree}
    (hRel : (data.vertexPartition wall).Rel a b) :
    data.sourceEndpoint wall a = data.sourceEndpoint wall b := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hRel

/-- Non-vacuity of `OrdinaryTrivalent`: at degree one the wall carries a single
block, which is the anchor, so the hypothesis is vacuously true.  The
substantive inhabitant is `ordinaryTrivalent_of_wall_metric` below. -/
theorem ordinaryTrivalent_degree_one (data : GluingDatum target 1) (wall : target.V)
    (anchor : WallBlock data wall) : OrdinaryTrivalent data wall anchor := by
  intro y hY
  exact absurd (Subsingleton.elim ((data.vertexPartition wall).repr anchor.1)
    ((data.vertexPartition wall).repr y)) hY

theorem ordinaryTrivalent_of_wallBlock
    (h : ∀ block : WallBlock data wall,
      ¬ (data.vertexPartition wall).Rel anchor.1 block.1 →
        nonDanglingValency data (WallBlock.sourceVertex data wall block) ≤ 3) :
    OrdinaryTrivalent data wall anchor := by
  intro y hY
  have hEq : WallBlock.sourceVertex data wall (WallBlock.ofSheet data wall y) =
      data.sourceEndpoint wall y :=
    sourceEndpoint_eq_of_rel ((data.vertexPartition wall).rel_repr_left y)
  rw [← hEq]
  exact h _ (not_rel_repr hY)

/-! ## 2.  The chosen side and the witness of a new occurrence -/

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

/-- The retained thick survivor of the fine class of `x` inside the anchor. -/
noncomputable def anchorWitness (x : Fin degree) : Option (NonDanglingEdge data) :=
  open Classical in
  if h : ∃ edge ∈ retainedThick sel,
      (Prescribed.finePartition sel).Rel (occurrenceSheet edge) x then
    some ⟨(Classical.choose h).1,
      survivor_not_isDangling (mem_retainedThick sel (Classical.choose_spec h).1).1⟩
  else none

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

/-- The old survivor whose stable row carries the new occurrence of the sheet
`x`, when there is one.  At the anchor's bridge class there is none. -/
noncomputable def newWitness (x : Fin degree) : Option (NonDanglingEdge data) :=
  if (data.vertexPartition wall).Rel anchor.1 x then
    (if (Prescribed.finePartition sel).Rel rep x then none else anchorWitness sel x)
  else ordinaryWitness data star anchor x

/-- Over the anchor's bridge class the new occurrence carries no old row. -/
theorem newWitness_bridge {x : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel anchor.1 x)
    (hFine : (Prescribed.finePartition sel).Rel rep x) :
    newWitness sel x = none := by
  rw [newWitness, ite_eq_left hAnchor, ite_eq_left hFine]

theorem newWitness_of_anchor {x : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel anchor.1 x)
    (hFine : ¬ (Prescribed.finePartition sel).Rel rep x) :
    newWitness sel x = anchorWitness sel x := by
  rw [newWitness, ite_eq_left hAnchor, ite_eq_right hFine]

theorem newWitness_of_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    newWitness sel x = ordinaryWitness data star anchor x := by
  rw [newWitness, ite_eq_right hX]

/-- Over the remaining fine classes of the anchor the witness is the retained
thick survivor of that class. -/
theorem anchorWitness_eq {x : Fin degree}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ retainedThick sel)
    (hRel : (Prescribed.finePartition sel).Rel (occurrenceSheet edge) x) :
    ∃ old : NonDanglingEdge data, anchorWitness sel x = some old ∧ old.1 = edge.1 := by
  classical
  have hEx : ∃ e ∈ retainedThick sel,
      (Prescribed.finePartition sel).Rel (occurrenceSheet e) x := ⟨edge, hEdge, hRel⟩
  have hSpec := Classical.choose_spec hEx
  have hSame : Classical.choose hEx = edge :=
    eq_of_finePartition_rel sel hSpec.1 hEdge (hSpec.2.trans hRel.symm)
  refine ⟨⟨(Classical.choose hEx).1, survivor_not_isDangling
    (mem_retainedThick sel hSpec.1).1⟩, ?_, ?_⟩
  · rw [anchorWitness, dite_eq_left hEx]
  · exact congrArg (fun e ↦ e.1) hSame

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

/-! ## 3.  The canonical sheet of a new occurrence -/

theorem newEdge_rel_sheet (y : Fin degree) :
    (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
      (cand).contracts).newEdge.Rel y ((cand).newSourceEdge y).1.2 :=
  (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
    (cand).contracts).newEdge.rel_repr_right y

theorem wall_rel_newSourceEdge_sheet (y : Fin degree) :
    (data.vertexPartition wall).Rel y ((cand).newSourceEdge y).1.2 :=
  (newEdge_refines_wall sel).rel (newEdge_rel_sheet sel y)

theorem newSourceEdge_sheet_eq_self (y : Fin degree) :
    (cand).newSourceEdge (((cand).newSourceEdge y).1.2) = (cand).newSourceEdge y :=
  (newSourceEdge_eq_of_rel sel (newEdge_rel_sheet sel y)).symm

/-! ## 4.  Two survivors alone on their sides lie on one wall-datum row -/

theorem ordinaryStar_eq_of_rel {a b : Fin degree}
    (hRel : (data.vertexPartition wall).Rel a b) (sideValue : Bool) :
    ordinaryStar data star anchor a sideValue = ordinaryStar data star anchor b sideValue := by
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
    (hSurvives : ¬ IsDangling (cand).datum ((cand).newSourceEdge z)) :
    ∃ w : NonDanglingEdge data, newWitness sel z = some w ∧
      w.1 ∈ ordinaryStar data star anchor z (ordSide data star anchor z) ∧
      (ordinaryStar data star anchor z (ordSide data star anchor z)).card = 1 := by
  classical
  have hFalse := ordinaryStar_card_ne_zero_of_new_survives sel hValid false hZ hSurvives
  have hTrue := ordinaryStar_card_ne_zero_of_new_survives sel hValid true hZ hSurvives
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
  exact ⟨w, (newWitness_of_ordinary sel hZ).trans hw, hwMem, hCard⟩

/-! ## 5.  The reverse row map on surviving occurrences -/

/-- The wall datum's row carrying a surviving occurrence of the candidate, with
`none` for the bridge row. -/
noncomputable def rowOfEdge (hValid : data.Valid)
    (e : NonDanglingEdge (cand).datum) : Option (StablePath data) :=
  open Classical in
  if h : ∃ old : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old = e then
    some (Classical.choose h).stablePath
  else (newWitness sel e.1.1.2).map NonDanglingEdge.stablePath

theorem rowOfEdge_pos (hValid : data.Valid) (e : NonDanglingEdge (cand).datum)
    (h : ∃ old : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old = e) :
    rowOfEdge sel hValid e = some (Classical.choose h).stablePath := by
  classical
  rw [rowOfEdge, dite_eq_left h]

theorem rowOfEdge_neg (hValid : data.Valid) (e : NonDanglingEdge (cand).datum)
    (h : ¬ ∃ old : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old = e) :
    rowOfEdge sel hValid e =
      (newWitness sel e.1.1.2).map NonDanglingEdge.stablePath := by
  classical
  rw [rowOfEdge, dite_eq_right h]

theorem rowOfEdge_retained (hValid : data.Valid) (old : NonDanglingEdge data) :
    rowOfEdge sel hValid (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old) =
      some old.stablePath := by
  classical
  have h : ∃ o : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 o =
        ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old := ⟨old, rfl⟩
  rw [rowOfEdge_pos sel hValid _ h]
  exact congrArg (fun o : NonDanglingEdge data ↦ some o.stablePath)
    (ResolutionAwayFromWall.retainedEdge_injective (cand) hValid.1 (Classical.choose_spec h))

theorem rowOfEdge_old (hValid : data.Valid) {old : data.SourceEdge}
    (hSurvives : ¬ IsDangling (cand).datum ((cand).oldSourceEdge old))
    (hData : ¬ IsDangling data old) :
    rowOfEdge sel hValid ⟨(cand).oldSourceEdge old, hSurvives⟩ =
      some (NonDanglingEdge.stablePath (⟨old, hData⟩ : NonDanglingEdge data)) :=
  rowOfEdge_retained sel hValid ⟨old, hData⟩

theorem rowOfEdge_new (hValid : data.Valid) {y : Fin degree}
    (hSurvives : ¬ IsDangling (cand).datum ((cand).newSourceEdge y)) :
    rowOfEdge sel hValid ⟨(cand).newSourceEdge y, hSurvives⟩ =
      (newWitness sel ((cand).newSourceEdge y).1.2).map NonDanglingEdge.stablePath := by
  classical
  have hNot : ¬ ∃ old : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old =
        (⟨(cand).newSourceEdge y, hSurvives⟩ : NonDanglingEdge (cand).datum) := by
    rintro ⟨old, hEq⟩
    exact newSourceEdge_ne_oldSourceEdge sel y old.1 (congrArg Subtype.val hEq).symm
  exact rowOfEdge_neg sel hValid _ hNot

/-! ## 6.  The reverse map is constant on stable paths -/

theorem rowOfEdge_eq_away (hValid : data.Valid) {v : (cand).datum.SourceVertex}
    {place : target.V} (hAway : place ≠ wall) (hTarget : v.1.1 = oldVertex target place)
    {e f : NonDanglingEdge (cand).datum} (hNe : e ≠ f)
    (hE : Incident (cand).datum e.1 v) (hF : Incident (cand).datum f.1 v)
    (hValency : nonDanglingValency (cand).datum v = 2) :
    rowOfEdge sel hValid e = rowOfEdge sel hValid f := by
  obtain ⟨old, hOldTarget, hOldVertex⟩ :=
    ResolutionAwayFromWall.exists_retainedVertex_of_target (cand) v place hAway hTarget
  have hOldAway : old.1.1 ≠ wall := fun hEq ↦ hAway (hOldTarget.symm.trans hEq)
  subst hOldVertex
  rcases ResolutionAwayFromWall.nonDanglingEdge_cases (cand) hValid
    (candidate_sourceGenus sel) e with ⟨oe, rfl⟩ | ⟨sheet, hSheet, rfl⟩
  · rcases ResolutionAwayFromWall.nonDanglingEdge_cases (cand) hValid
      (candidate_sourceGenus sel) f with ⟨of, rfl⟩ | ⟨sheet, hSheet, rfl⟩
    · rw [rowOfEdge_retained sel hValid oe, rowOfEdge_retained sel hValid of]
      refine congrArg (fun r : StablePath data ↦ some r)
        (stablePath_eq_of_consecutive ⟨?_, old, ?_, ?_, ?_⟩)
      · exact fun hEq ↦ hNe (congrArg
          (ResolutionAwayFromWall.retainedEdge (cand) hValid.1) hEq)
      · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff (cand) old hOldAway oe.1).mp hE
      · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff (cand) old hOldAway of.1).mp hF
      · exact (ResolutionAwayFromWall.nonDanglingValency_retainedVertex (cand) hValid
          (candidate_sourceGenus sel) old hOldAway).symm.trans hValency
    · exact absurd hF
        (ResolutionAwayFromWall.not_incident_newSourceEdge (cand) old hOldAway sheet)
  · exact absurd hE
      (ResolutionAwayFromWall.not_incident_newSourceEdge (cand) old hOldAway sheet)

/-- Configuration B's divalent vertex: the new occurrence and the retained
occurrence of that thick class carry the same wall-datum row. -/
theorem rowOfEdge_anchor_pair (hValid : data.Valid)
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ retainedThick sel)
    (hNeFirst : edge ≠ Prescribed.firstSelected sel)
    (hNewSurv : ¬ IsDangling (cand).datum ((cand).newSourceEdge (occurrenceSheet edge)))
    (hOldSurv : ¬ IsDangling (cand).datum ((cand).oldSourceEdge edge.1)) :
    rowOfEdge sel hValid ⟨(cand).newSourceEdge (occurrenceSheet edge), hNewSurv⟩ =
      rowOfEdge sel hValid ⟨(cand).oldSourceEdge edge.1, hOldSurv⟩ := by
  classical
  have hThick := (mem_retainedThick sel hEdge).1
  have hNeSecond := (mem_retainedThick sel hEdge).2
  have hDataSurv : ¬ IsDangling data edge.1 := survivor_not_isDangling hThick
  rw [rowOfEdge_old sel hValid hOldSurv hDataSurv, rowOfEdge_new sel hValid hNewSurv]
  have hWallRel : (data.vertexPartition wall).Rel (occurrenceSheet edge)
      ((cand).newSourceEdge (occurrenceSheet edge)).1.2 :=
    wall_rel_newSourceEdge_sheet sel (occurrenceSheet edge)
  have hFineRel : (Prescribed.finePartition sel).Rel (occurrenceSheet edge)
      ((cand).newSourceEdge (occurrenceSheet edge)).1.2 :=
    (newEdge_rel_iff_finePartition sel (occurrenceSheet_wall_rel edge)).mp
      (newEdge_rel_sheet sel (occurrenceSheet edge))
  have hAnchorZ : (data.vertexPartition wall).Rel anchor.1
      ((cand).newSourceEdge (occurrenceSheet edge)).1.2 :=
    (occurrenceSheet_wall_rel edge).trans hWallRel
  have hNotBridge : ¬ (Prescribed.finePartition sel).Rel rep
      ((cand).newSourceEdge (occurrenceSheet edge)).1.2 := by
    intro hBridge
    rcases (finePartition_rel_thick_iff sel hThick).mp
      (hBridge.trans hFineRel.symm) with hCase | hCase
    · exact hNeFirst hCase
    · exact hNeSecond hCase
  obtain ⟨w, hw, hwVal⟩ := anchorWitness_eq sel hEdge hFineRel
  rw [newWitness_of_anchor sel hAnchorZ hNotBridge, hw]
  exact congrArg (fun o : NonDanglingEdge data ↦ some o.stablePath) (Subtype.ext hwVal)

/-- An ordinary block whose side carries a single survivor: the new occurrence
and that survivor carry the same wall-datum row. -/
theorem rowOfEdge_ordinary_pair (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hNewSurv : ¬ IsDangling (cand).datum ((cand).newSourceEdge x))
    {old : data.SourceEdge} (hOld : old ∈ ordinaryStar data star anchor x sideValue)
    (hCard : (ordinaryStar data star anchor x sideValue).card = 1)
    (hOldSurv : ¬ IsDangling (cand).datum ((cand).oldSourceEdge old)) :
    rowOfEdge sel hValid ⟨(cand).newSourceEdge x, hNewSurv⟩ =
      rowOfEdge sel hValid ⟨(cand).oldSourceEdge old, hOldSurv⟩ := by
  classical
  have hDataSurv : ¬ IsDangling data old := ((mem_ordinaryStar old).mp hOld).1.1
  rw [rowOfEdge_old sel hValid hOldSurv hDataSurv, rowOfEdge_new sel hValid hNewSurv]
  have hWallRel : (data.vertexPartition wall).Rel x ((cand).newSourceEdge x).1.2 :=
    wall_rel_newSourceEdge_sheet sel x
  have hZ : ¬ (data.vertexPartition wall).Rel anchor.1 ((cand).newSourceEdge x).1.2 :=
    fun h ↦ hX (h.trans hWallRel.symm)
  have hStar : ∀ t : Bool,
      ordinaryStar data star anchor ((cand).newSourceEdge x).1.2 t =
        ordinaryStar data star anchor x t :=
    fun t ↦ ordinaryStar_eq_of_rel hWallRel.symm t
  have hSurvZ : ¬ IsDangling (cand).datum
      ((cand).newSourceEdge ((cand).newSourceEdge x).1.2) := by
    rw [newSourceEdge_sheet_eq_self sel x]
    exact hNewSurv
  obtain ⟨w, hw, hwMem, hwCard⟩ := newWitness_ordinary_spec sel hValid hZ
    (hOrd _ hZ) hSurvZ
  rw [hw]
  refine congrArg (fun r : StablePath data ↦ some r) ?_
  refine stablePath_eq_of_card_one (x := ((cand).newSourceEdge x).1.2) (sb := sideValue)
    hwMem ?_ hwCard ?_
  · rw [hStar sideValue]
    exact hOld
  · rw [hStar sideValue]
    exact hCard

include source in
theorem rowOfEdge_eq_wall (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) (sideValue : Bool)
    {v : (cand).datum.SourceVertex} (x : Fin degree)
    (hv : endpointVertex sel sideValue x = v)
    {e f : NonDanglingEdge (cand).datum} (hNe : e ≠ f)
    (hE : Incident (cand).datum e.1 v) (hF : Incident (cand).datum f.1 v)
    (hValency : nonDanglingValency (cand).datum v = 2) :
    rowOfEdge sel hValid e = rowOfEdge sel hValid f := by
  classical
  subst hv
  have hNeVal : e.1 ≠ f.1 := fun hEq ↦ hNe (Subtype.ext hEq)
  by_cases hA : (data.vertexPartition wall).Rel anchor.1 x
  · cases sideValue
    · obtain ⟨edge, hEdge, hFine⟩ := exists_retained_rel source sel hA
      have hVertexEq : endpointVertex sel false (occurrenceSheet edge) =
          endpointVertex sel false x :=
        endpointVertex_eq sel false (occurrenceSheet_wall_rel edge) hFine
      by_cases hFirst : edge = Prescribed.firstSelected sel
      · exfalso
        have h3 : nonDanglingValency (cand).datum
            (endpointVertex sel false (occurrenceSheet edge)) = 3 := by
          subst hFirst
          exact nonDanglingValency_endpointVertex_false source sel hValid
        rw [hVertexEq] at h3
        omega
      · have hStar := nonDanglingIncident_extraEndpointVertex source sel hValid hEdge hFirst
        rw [hVertexEq] at hStar
        have hEmem : e.1 ∈ nonDanglingIncident (cand).datum (endpointVertex sel false x) :=
          (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hE⟩
        have hFmem : f.1 ∈ nonDanglingIncident (cand).datum (endpointVertex sel false x) :=
          (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, hF⟩
        rw [hStar, Finset.mem_insert, Finset.mem_singleton] at hEmem hFmem
        rcases hEmem with hEc | hEc <;> rcases hFmem with hFc | hFc
        · exact absurd (hEc.trans hFc.symm) hNeVal
        · have hNewSurv : ¬ IsDangling (cand).datum
              ((cand).newSourceEdge (occurrenceSheet edge)) := by
            rw [← hEc]; exact e.2
          have hOldSurv : ¬ IsDangling (cand).datum ((cand).oldSourceEdge edge.1) := by
            rw [← hFc]; exact f.2
          rw [show e = (⟨_, hNewSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hEc,
            show f = (⟨_, hOldSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hFc]
          exact rowOfEdge_anchor_pair sel hValid hEdge hFirst hNewSurv hOldSurv
        · have hOldSurv : ¬ IsDangling (cand).datum ((cand).oldSourceEdge edge.1) := by
            rw [← hEc]; exact e.2
          have hNewSurv : ¬ IsDangling (cand).datum
              ((cand).newSourceEdge (occurrenceSheet edge)) := by
            rw [← hFc]; exact f.2
          rw [show e = (⟨_, hOldSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hEc,
            show f = (⟨_, hNewSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hFc]
          exact (rowOfEdge_anchor_pair sel hValid hEdge hFirst hNewSurv hOldSurv).symm
        · exact absurd (hEc.trans hFc.symm) hNeVal
    · exfalso
      have hEqV : endpointVertex sel true x = endpointVertex sel true rep :=
        endpointVertex_eq sel true hA (hA.symm.trans (rep_wall_rel sel))
      rw [hEqV, nonDanglingValency_endpointVertex_true source sel hValid] at hValency
      omega
  · have hEmem := (mem_nonDanglingIncident_endpointVertex_ordinary sel hValid
      sideValue hA e.1).mp ((mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hE⟩)
    have hFmem := (mem_nonDanglingIncident_endpointVertex_ordinary sel hValid
      sideValue hA f.1).mp ((mem_nonDanglingIncident _ _ _).mpr ⟨f.2, hF⟩)
    by_cases hDang : IsDangling (cand).datum ((cand).newSourceEdge x)
    · have hCard2 : (ordinaryStar data star anchor x sideValue).card = 2 := by
        have hEq := nonDanglingValency_endpointVertex_of_new_dangling sel hValid
          sideValue hA hDang
        omega
      have hSum := card_ordinaryStar_add (data := data) (star := star) (anchor := anchor) x
      have hLe := hOrd x hA
      have hOther := nonDanglingValency_endpointVertex_of_new_dangling sel hValid
        (!sideValue) hA hDang
      have hNeOne := nonDanglingValency_candidate_ne_one sel hValid
        (endpointVertex sel (!sideValue) x)
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
            rowOfEdge_old sel hValid hoeSurv hoeData,
            rowOfEdge_old sel hValid hofSurv hofData]
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
        have hEq := nonDanglingValency_endpointVertex_of_new_survives sel hValid
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
          exact (rowOfEdge_ordinary_pair sel hValid hOrd sideValue hA hSurvF hoe
            hCard1 hoeSurv).symm
      · rcases hFmem with ⟨of, hof, hFc⟩ | ⟨hFc, hSurvF⟩
        · have hofSurv : ¬ IsDangling (cand).datum ((cand).oldSourceEdge of) := by
            rw [← hFc]; exact f.2
          rw [show e = (⟨_, hSurvE⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hEc,
            show f = (⟨_, hofSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hFc]
          exact rowOfEdge_ordinary_pair sel hValid hOrd sideValue hA hSurvE hof
            hCard1 hofSurv
        · exact absurd (hEc.trans hFc.symm) hNeVal

include source in
/-- **The reverse row map descends to stable paths.** -/
theorem rowOfEdge_eq_of_consecutive (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor)
    {e f : NonDanglingEdge (cand).datum} (h : Consecutive (cand).datum e f) :
    rowOfEdge sel hValid e = rowOfEdge sel hValid f := by
  obtain ⟨hNe, v, hE, hF, hValency⟩ := h
  cases hTarget : v.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · rw [hAt] at hTarget
        exact rowOfEdge_eq_wall source sel hValid hOrd false v.1.2
          (((cand).datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨hTarget.symm, rfl⟩)
          hNe hE hF hValency
      · exact rowOfEdge_eq_away sel hValid hAt hTarget hNe hE hF hValency
  | inr point =>
      cases point
      exact rowOfEdge_eq_wall source sel hValid hOrd true v.1.2
        (((cand).datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨hTarget.symm, rfl⟩)
        hNe hE hF hValency

/-! ## 7.  The row equivalence -/

/-- The candidate's one new stable row. -/
noncomputable def bridgeRow (hValid : data.Valid) : StablePath (cand).datum :=
  NonDanglingEdge.stablePath
    (⟨bridgeEdge sel rep, bridgeEdge_survives source sel hValid⟩ :
      NonDanglingEdge (cand).datum)

theorem rowOfEdge_bridge (hValid : data.Valid) :
    rowOfEdge sel hValid
      (⟨bridgeEdge sel rep, bridgeEdge_survives source sel hValid⟩ :
        NonDanglingEdge (cand).datum) = none := by
  have hEq := rowOfEdge_new sel hValid (y := rep) (bridgeEdge_survives source sel hValid)
  have hW := newWitness_bridge sel
    ((rep_wall_rel sel).trans (wall_rel_newSourceEdge_sheet sel rep))
    ((newEdge_rel_iff_finePartition sel (rep_wall_rel sel)).mp
      (newEdge_rel_sheet sel rep))
  rw [hW] at hEq
  exact hEq

/-- The reverse row map, on stable paths. -/
noncomputable def rowDescend (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) :
    StablePath (cand).datum → Option (StablePath data) :=
  Quot.lift (rowOfEdge sel hValid)
    (fun _ _ h ↦ rowOfEdge_eq_of_consecutive source sel hValid hOrd h)

@[simp] theorem rowDescend_mk (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) (e : NonDanglingEdge (cand).datum) :
    rowDescend source sel hValid hOrd e.stablePath = rowOfEdge sel hValid e := rfl

/-- The forward row map: the bridge row for `none`, the retained row for a row
of the incoming wall datum. -/
noncomputable def rowMap (hValid : data.Valid) :
    Option (StablePath data) → StablePath (cand).datum
  | none => bridgeRow source sel hValid
  | some r => NonTrivalentValencyTwoDescent.retainedRow source sel hValid r

include source in
theorem rowDescend_bridgeRow (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) :
    rowDescend source sel hValid hOrd (bridgeRow source sel hValid) = none :=
  rowOfEdge_bridge source sel hValid

theorem rowDescend_retainedRow (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) (r : StablePath data) :
    rowDescend source sel hValid hOrd
        (NonTrivalentValencyTwoDescent.retainedRow source sel hValid r) = some r := by
  induction r using Quot.inductionOn with
  | h e => exact rowOfEdge_retained sel hValid e

/-- **Every stable row of the candidate is a retained row or the bridge row.** -/
theorem rowMap_rowOfEdge (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) (e : NonDanglingEdge (cand).datum) :
    rowMap source sel hValid (rowOfEdge sel hValid e) = e.stablePath := by
  classical
  rcases ResolutionAwayFromWall.nonDanglingEdge_cases (cand) hValid
    (candidate_sourceGenus sel) e with ⟨old, rfl⟩ | ⟨y, hSurv, rfl⟩
  · rw [rowOfEdge_retained sel hValid old]
    rfl
  · rw [rowOfEdge_new sel hValid hSurv]
    have hSelf : (cand).newSourceEdge (((cand).newSourceEdge y).1.2) =
        (cand).newSourceEdge y := newSourceEdge_sheet_eq_self sel y
    have hSurvZ : ¬ IsDangling (cand).datum
        ((cand).newSourceEdge (((cand).newSourceEdge y).1.2)) := by
      rw [hSelf]; exact hSurv
    by_cases hAnchorZ : (data.vertexPartition wall).Rel anchor.1 ((cand).newSourceEdge y).1.2
    · by_cases hBridge : (Prescribed.finePartition sel).Rel rep
          ((cand).newSourceEdge y).1.2
      · rw [newWitness_bridge sel hAnchorZ hBridge]
        refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
        exact (newSourceEdge_eq_of_rel sel
          ((newEdge_rel_iff_finePartition sel (rep_wall_rel sel)).mpr hBridge)).trans
          hSelf
      · obtain ⟨edge, hEdge, hFine⟩ := exists_retained_rel source sel hAnchorZ
        have hFirst : edge ≠ Prescribed.firstSelected sel := by
          intro hEq
          subst hEq
          exact hBridge hFine
        obtain ⟨w, hw, hwVal⟩ := anchorWitness_eq sel hEdge hFine
        rw [newWitness_of_anchor sel hAnchorZ hBridge, hw]
        have hThick := (mem_retainedThick sel hEdge).1
        have hNewEq : (cand).newSourceEdge (occurrenceSheet edge) = (cand).newSourceEdge y :=
          (newSourceEdge_eq_of_rel sel
            ((newEdge_rel_iff_finePartition sel
              (occurrenceSheet_wall_rel edge)).mpr hFine)).trans hSelf
        have hRow := newSourceEdge_stablePath_eq_retained source sel hValid hEdge hFirst
        refine Eq.trans ?_ (hRow.symm.trans ?_)
        · exact congrArg NonDanglingEdge.stablePath (Subtype.ext (congrArg
            (cand).oldSourceEdge hwVal))
        · exact congrArg NonDanglingEdge.stablePath (Subtype.ext hNewEq)
    · obtain ⟨w, hw, hwMem, hwCard⟩ := newWitness_ordinary_spec sel hValid hAnchorZ
        (hOrd _ hAnchorZ) hSurvZ
      rw [hw]
      refine Eq.trans (stablePath_retainedEdge_eq_newSourceEdge sel hValid _ hAnchorZ
        hwMem hwCard hSurvZ) ?_
      exact congrArg NonDanglingEdge.stablePath (Subtype.ext hSelf)

/-- **The row dictionary of the prescribed valency-two candidate.** -/
noncomputable def rowEquiv (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) :
    StablePath (cand).datum ≃ Option (StablePath data) where
  toFun := rowDescend source sel hValid hOrd
  invFun := rowMap source sel hValid
  left_inv := by
    intro path
    induction path using Quot.inductionOn with
    | h e => exact rowMap_rowOfEdge source sel hValid hOrd e
  right_inv := by
    intro r
    cases r with
    | none => exact rowDescend_bridgeRow source sel hValid hOrd
    | some r => exact rowDescend_retainedRow source sel hValid hOrd r

include source in
@[simp] theorem rowEquiv_retainedRow (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) (r : StablePath data) :
    rowEquiv source sel hValid hOrd
        (NonTrivalentValencyTwoDescent.retainedRow source sel hValid r) = some r :=
  rowDescend_retainedRow source sel hValid hOrd r

include source in
@[simp] theorem rowEquiv_bridgeRow (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) :
    rowEquiv source sel hValid hOrd (bridgeRow source sel hValid) = none :=
  rowDescend_bridgeRow source sel hValid hOrd

/-- **The honest stable length-matrix labelling of the outgoing candidate**, with
no supplied row equivalence. -/
noncomputable def labelling {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor)
    (labelling₀ : StableLengthMatrixLabelling data coordinate) :
    StableLengthMatrixLabelling (cand).datum (Option coordinate) :=
  NonTrivalentValencyTwoRows.labelling sel labelling₀ (rowEquiv source sel hValid hOrd)

@[simp] theorem labelling_row_retained {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor)
    (labelling₀ : StableLengthMatrixLabelling data coordinate) (r : StablePath data) :
    (labelling source sel hValid hOrd labelling₀).row
        (NonTrivalentValencyTwoDescent.retainedRow source sel hValid r) =
      some (labelling₀.row r) := by
  rw [labelling, NonTrivalentValencyTwoRows.labelling_row, rowEquiv_retainedRow]
  rfl

@[simp] theorem labelling_row_bridge {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor)
    (labelling₀ : StableLengthMatrixLabelling data coordinate) :
    (labelling source sel hValid hOrd labelling₀).row (bridgeRow source sel hValid) = none := by
  rw [labelling, NonTrivalentValencyTwoRows.labelling_row, rowEquiv_bridgeRow]
  rfl

/-! ## 8.  At an actual two-valent wall

The ordinary-block trivalence is discharged from the wall metric of the
existence route, through
`NonTrivalentAnchorValency.nonDanglingValency_wallBlock_le_three_of_twoStar`. -/

section Incoming

open GraphContraction GluingContraction ContractionFibre ContractionRamification
open FullDimensionalSource WallDegeneration

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The ordinary-block input, discharged at an actual wall.**  Given the wall metric
of a Part II open facet and the anchor's surviving valency four, every other
block above the wall is trivalent. -/
theorem ordinaryTrivalent_of_wall_metric
    (cover : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation cover coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest cover a b contracted)
    (wallStar : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (coordinates : coordinate → ℚ) (facet : coordinate)
    (hRows : ∀ row, row ≠ facet →
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates row ≠ 0)
    (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
    (anchorBlock : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩)
    (hNd : nonDanglingValency (contractDatum cover hc hab hOne)
      (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlock) = 4) :
    OrdinaryTrivalent (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlock :=
  ordinaryTrivalent_of_wallBlock
    (NonTrivalentAnchorValency.nonDanglingValency_wallBlock_le_three_of_twoStar cover fd
      hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hNd)

/-- **The full valency-two row dictionary at an actual two-valent wall**, with
every hypothesis discharged from the wall metric: the anchor block, its
`TwoBranchAnchor` classification, the outgoing candidate's validity and source
genus, the ordinary-block trivalence, and the row equivalence itself, sending
every retained row to its incoming row and the bridge row to `none`. -/
theorem exists_rowEquiv_of_wall_metric
    (cover : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation cover coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest cover a b contracted)
    (wallStar : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (coordinates : coordinate → ℚ) (facet : coordinate)
    (hRows : ∀ row, row ≠ facet →
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates row ≠ 0)
    (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
    (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
      0 < coordinates column)
    (hFacetZero :
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates facet = 0) :
    ∃ (anchorBlock : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩)
      (src : TwoBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlock),
      nonDanglingValency (contractDatum cover hc hab hOne)
          (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩
            anchorBlock) = 4 ∧
        ∀ sel : Prescribed.Selection (contractDatum cover hc hab hOne)
            wallStar anchorBlock,
        (Prescribed.validCandidate sel).datum.Valid ∧
        genus (Prescribed.validCandidate sel).datum.sourceGraph =
          genus (contractDatum cover hc hab hOne).sourceGraph ∧
        ∃ hOrd : OrdinaryTrivalent (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlock,
          (∀ r, rowEquiv src sel
              (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd
              (NonTrivalentValencyTwoDescent.retainedRow src sel
                (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) r) =
            some r) ∧
            rowEquiv src sel
                (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd
                (bridgeRow src sel
                  (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest)) =
              none := by
  obtain ⟨anchorBlock, hNd, src⟩ :=
    NonTrivalentAnchorValency.twoBranchAnchor_of_single_row cover fd hc hab hOne
      hForest coordinates facet hRows hZeroCoord hPosCoord hFacetZero wallStar
  refine ⟨anchorBlock, src, hNd, fun sel ↦ ⟨?_, ?_, ?_⟩⟩
  · exact Prescribed.validCandidate_datum_valid sel
      (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest)
  · exact candidate_sourceGenus sel
  · refine ⟨ordinaryTrivalent_of_wall_metric cover fd hc hab hOne hForest wallStar
      coordinates facet hRows hZeroCoord anchorBlock hNd, ?_, ?_⟩
    · exact fun r ↦ rowEquiv_retainedRow src sel _ _ r
    · exact rowEquiv_bridgeRow src sel _ _

end Incoming

end DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv
