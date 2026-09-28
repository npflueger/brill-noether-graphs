import DraismaVargas.LocalCases.NonTrivalentValencyThreeDescent
import DraismaVargas.LocalCases.NonTrivalentAnchorValency

/-!
# The row dictionary of the prescribed valency-three candidate

Source: Vargas, Part II (arXiv:2609.09109), Section 5.3 (Case {v3-nd4}), with
Section 5.1 for the blocks above `w_0` other than the anchor.

`NonTrivalentValencyThreeRows` builds `retainedRow` modulo
`OrdinaryBlockDescent`, and `NonTrivalentValencyThreeDescent` proves that
`Prop`; this module builds the inverse row map and packages the two into the
equivalence
`StablePath (validCandidate source hNoGlue hValid).datum ≃ Option (StablePath data)`
that `NonTrivalentValencyThreeRows.labelling` takes as its argument.

## What is proved

* `newWitness`: the old survivor whose stable row carries a given new
  occurrence.  Over an ordinary block it is the doubled-direction survivor of
  the sheet's own fine class (`ordinaryWitness`), which by the census of
  `NonTrivalentValencyThreeDescent` exists exactly when that new occurrence
  survives; over the anchor block it is `none`, the bridge row.  **No choice of
  side is made**, so -- unlike at valency two -- no ordinary-block
  trivalence hypothesis is needed anywhere in this module.
* `rowOfEdge` and `rowOfEdge_eq_of_consecutive`: the reverse map on surviving
  occurrences is constant on stable paths.  The three geometric inputs are
  `ResolutionAwayFromWall` off the wall (`rowOfEdge_eq_away`), the exact stars
  of `NonTrivalentValencyThreeRows` at the anchor -- where in fact no endpoint
  vertex is divalent at all (`nonDanglingValency_endpointVertex_anchor_ne_two`:
  both ends of the bridge class are trivalent and the other `u`-endpoints are
  empty, `nonDanglingIncident_endpointVertex_anchor_singleton`) -- and the
  ordinary-block census (`rowOfEdge_endpointVertex_false`,
  `rowOfEdge_eq_endpointVertex_true`, the latter through the old witness of
  `exists_rowWitness_true` and `nd(B_v) = nd(B)`).
* `rowEquiv`: the two maps are mutually inverse -- `rowMap_rowOfEdge` is
  surjectivity (every candidate row contains a retained occurrence or is the
  bridge row, `newSourceEdge_eq_bridge_of_anchor`) and `rowDescend_retainedRow`
  is injectivity -- with `rowEquiv_retainedRow` and `rowEquiv_bridgeRow`.
* `labelling`: `NonTrivalentValencyThreeRows.labelling` instantiated, so the
  outgoing candidate's honest stable length-matrix labelling needs no supplied
  row equivalence; `labelling_row_retained` and `labelling_row_bridge`.
* `exists_rowEquiv_of_wall_metric`: the whole package at an actual three-valent
  wall, with `nd(A) = 4` discharged from the wall metric of the existence route
  through `NonTrivalentAnchorValency.threeBranchAnchor_of_single_row`, so it is
  not a hypothesis.

## What is NOT proved

The `AgreeOffColumn` / entrywise common-minor identity of the outgoing labelled
matrix against the incoming full-dimensional matrix, on the pattern of
`NonTrivalentValencyFourRowDictionary.matrix_chartLabelling_eq_incoming`.
Nothing here constructs a `FullDimensionalSourcePresentation`, a
`ContractionForest`, a star or the wall metric; the Section 9 statement carries
them.

## Consumers

The boundary dispatcher for Part II, Case {v3-nd4}
(`NonTrivalentValencyThreeDispatcher`).
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeRowEquiv

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.W3R1SourceProfile
open DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeRows
open DraismaVargas.LocalCases.NonTrivalentValencyThreeDescent

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall}
  (source : ThreeBranchAnchor data star anchor)
  (hNoGlue : DanglingEdgeNoGlue data) (hValid : data.Valid)

local notation "cand" => (Prescribed.validCandidate source hNoGlue hValid)

local notation "rep" => (Prescribed.selectedRepresentative source)

/-! ## 1.  The old survivor carrying a new occurrence -/

/-- A surviving occurrence of the wall datum, as an `Option`. -/
noncomputable def witnessOf (data : GluingDatum target degree) (old : data.SourceEdge) :
    Option (NonDanglingEdge data) :=
  open Classical in
  if h : IsDangling data old then none else some ⟨old, h⟩

theorem witnessOf_pos {old : data.SourceEdge} (h : ¬ IsDangling data old) :
    witnessOf data old = some ⟨old, h⟩ := by
  classical
  rw [witnessOf, dif_neg h]

theorem witnessOf_neg {old : data.SourceEdge} (h : IsDangling data old) :
    witnessOf data old = none := by
  classical
  rw [witnessOf, dif_pos h]

/-- Over an ordinary wall block the new occurrence of a fine class carries the
row of that class's doubled-direction survivor. -/
noncomputable def ordinaryWitness (source : ThreeBranchAnchor data star anchor)
    (x : Fin degree) : Option (NonDanglingEdge data) :=
  witnessOf data (doubledOccurrence source x)

/-- The old survivor whose stable row carries the new occurrence of the sheet
`x`: none over the anchor block, where the new occurrence is the bridge `h_1`
(or a dangling singleton occurrence). -/
noncomputable def newWitness (source : ThreeBranchAnchor data star anchor)
    (x : Fin degree) : Option (NonDanglingEdge data) :=
  if (data.vertexPartition wall).Rel anchor.1 x then none else ordinaryWitness source x

theorem newWitness_anchor {x : Fin degree}
    (hX : (data.vertexPartition wall).Rel anchor.1 x) :
    newWitness source x = none := by
  rw [newWitness, if_pos hX]

theorem newWitness_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    newWitness source x = ordinaryWitness source x := by
  rw [newWitness, if_neg hX]

theorem ordinaryWitness_pos {x : Fin degree}
    (h : ¬ IsDangling data (doubledOccurrence source x)) :
    ordinaryWitness source x = some ⟨doubledOccurrence source x, h⟩ := by
  rw [ordinaryWitness, witnessOf_pos h]

theorem ordinaryWitness_neg {x : Fin degree}
    (h : IsDangling data (doubledOccurrence source x)) :
    ordinaryWitness source x = none := by
  rw [ordinaryWitness, witnessOf_neg h]

/-! ## 2.  The canonical sheet of a new occurrence -/

theorem newEdge_rel_sheet (y : Fin degree) :
    (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
      (cand).contracts).newEdge.Rel y ((cand).newSourceEdge y).1.2 :=
  (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
    (cand).contracts).newEdge.rel_repr_right y

theorem wall_rel_newSourceEdge_sheet (y : Fin degree) :
    (data.vertexPartition wall).Rel y ((cand).newSourceEdge y).1.2 :=
  (newEdge_refines_wall source hNoGlue hValid).rel (newEdge_rel_sheet source hNoGlue hValid y)

theorem newSourceEdge_sheet_eq_self (y : Fin degree) :
    (cand).newSourceEdge (((cand).newSourceEdge y).1.2) = (cand).newSourceEdge y :=
  (newSourceEdge_eq_of_rel source hNoGlue hValid
    (newEdge_rel_sheet source hNoGlue hValid y)).symm

/-- Over an ordinary block the witness only depends on the fine class, so the
canonical sheet of a new occurrence has the same witness as the sheet itself. -/
theorem newWitness_newSourceEdge_sheet {y : Fin degree}
    (hY : ¬ (data.vertexPartition wall).Rel anchor.1 y) :
    newWitness source ((cand).newSourceEdge y).1.2 = newWitness source y := by
  have hWall : (data.vertexPartition wall).Rel y ((cand).newSourceEdge y).1.2 :=
    wall_rel_newSourceEdge_sheet source hNoGlue hValid y
  have hZ : ¬ (data.vertexPartition wall).Rel anchor.1 ((cand).newSourceEdge y).1.2 :=
    fun h ↦ hY (h.trans hWall.symm)
  have hDoubled : doubledOccurrence source ((cand).newSourceEdge y).1.2 =
      doubledOccurrence source y := by
    refine doubledOccurrence_eq_of_rel source ?_
    exact ((newEdge_rel_ordinary source hNoGlue hValid hY).mp
      (newEdge_rel_sheet source hNoGlue hValid y)).symm
  rw [newWitness_ordinary source hZ, newWitness_ordinary source hY, ordinaryWitness,
    ordinaryWitness, hDoubled]


/-! ## 3.  The reverse row map on surviving occurrences -/

/-- The wall datum's row carrying a surviving occurrence of the candidate, with
`none` for the new bridge row. -/
noncomputable def rowOfEdge (e : NonDanglingEdge (cand).datum) :
    Option (StablePath data) :=
  open Classical in
  if h : ∃ old : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old = e then
    some (Classical.choose h).stablePath
  else (newWitness source e.1.1.2).map NonDanglingEdge.stablePath

theorem rowOfEdge_pos (e : NonDanglingEdge (cand).datum)
    (h : ∃ old : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old = e) :
    rowOfEdge source hNoGlue hValid e = some (Classical.choose h).stablePath := by
  classical
  rw [rowOfEdge, dif_pos h]

theorem rowOfEdge_neg (e : NonDanglingEdge (cand).datum)
    (h : ¬ ∃ old : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old = e) :
    rowOfEdge source hNoGlue hValid e =
      (newWitness source e.1.1.2).map NonDanglingEdge.stablePath := by
  classical
  rw [rowOfEdge, dif_neg h]

theorem rowOfEdge_retained (old : NonDanglingEdge data) :
    rowOfEdge source hNoGlue hValid
        (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old) = some old.stablePath := by
  classical
  have h : ∃ o : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 o =
        ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old := ⟨old, rfl⟩
  rw [rowOfEdge_pos source hNoGlue hValid _ h]
  exact congrArg (fun o : NonDanglingEdge data ↦ some o.stablePath)
    (ResolutionAwayFromWall.retainedEdge_injective (cand) hValid.1 (Classical.choose_spec h))

theorem rowOfEdge_old {old : data.SourceEdge}
    (hSurvives : ¬ IsDangling (cand).datum ((cand).oldSourceEdge old))
    (hData : ¬ IsDangling data old) :
    rowOfEdge source hNoGlue hValid ⟨(cand).oldSourceEdge old, hSurvives⟩ =
      some (NonDanglingEdge.stablePath (⟨old, hData⟩ : NonDanglingEdge data)) :=
  rowOfEdge_retained source hNoGlue hValid ⟨old, hData⟩

theorem rowOfEdge_new {y : Fin degree}
    (hSurvives : ¬ IsDangling (cand).datum ((cand).newSourceEdge y)) :
    rowOfEdge source hNoGlue hValid ⟨(cand).newSourceEdge y, hSurvives⟩ =
      (newWitness source ((cand).newSourceEdge y).1.2).map NonDanglingEdge.stablePath := by
  classical
  have hNot : ¬ ∃ old : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old =
        (⟨(cand).newSourceEdge y, hSurvives⟩ : NonDanglingEdge (cand).datum) := by
    rintro ⟨old, hEq⟩
    exact newSourceEdge_ne_oldSourceEdge source hNoGlue hValid y old.1
      (congrArg Subtype.val hEq).symm
  exact rowOfEdge_neg source hNoGlue hValid _ hNot

/-- Over an ordinary block a surviving new occurrence carries the row of its
class's doubled-direction survivor. -/
theorem rowOfEdge_new_ordinary {y : Fin degree}
    (hY : ¬ (data.vertexPartition wall).Rel anchor.1 y)
    (hSurvives : ¬ IsDangling (cand).datum ((cand).newSourceEdge y)) :
    rowOfEdge source hNoGlue hValid ⟨(cand).newSourceEdge y, hSurvives⟩ =
      some (NonDanglingEdge.stablePath (⟨doubledOccurrence source y,
        (newSourceEdge_survives_iff_ordinary source hNoGlue hValid hY).mp hSurvives⟩ :
          NonDanglingEdge data)) := by
  rw [rowOfEdge_new source hNoGlue hValid hSurvives,
    newWitness_newSourceEdge_sheet source hNoGlue hValid hY,
    newWitness_ordinary source hY,
    ordinaryWitness_pos source
      ((newSourceEdge_survives_iff_ordinary source hNoGlue hValid hY).mp hSurvives)]
  rfl

/-- Over the anchor block a surviving new occurrence is the bridge, and carries
no row of the wall datum. -/
theorem rowOfEdge_new_anchor {y : Fin degree}
    (hY : (data.vertexPartition wall).Rel anchor.1 y)
    (hSurvives : ¬ IsDangling (cand).datum ((cand).newSourceEdge y)) :
    rowOfEdge source hNoGlue hValid ⟨(cand).newSourceEdge y, hSurvives⟩ = none := by
  rw [rowOfEdge_new source hNoGlue hValid hSurvives,
    newWitness_anchor source
      (hY.trans (wall_rel_newSourceEdge_sheet source hNoGlue hValid y))]
  rfl

/-! ## 4.  The divalent end of an ordinary block -/

theorem not_isDangling_doubledOccurrence_of_valency {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hVal : nonDanglingValency (cand).datum
      (endpointVertex source hNoGlue hValid false x) ≠ 0) :
    ¬ IsDangling data (doubledOccurrence source x) := by
  classical
  intro hDangling
  refine hVal ?_
  have hNew : IsDangling (cand).datum ((cand).newSourceEdge x) := by
    by_contra h
    exact ((newSourceEdge_survives_iff_ordinary source hNoGlue hValid hX).mp h) hDangling
  have hEmpty : nonDanglingIncident (cand).datum
      (endpointVertex source hNoGlue hValid false x) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem ?_
    intro e he
    rcases (mem_nonDanglingIncident_endpointVertex_false_ordinary source hNoGlue hValid
      hX e).mp he with ⟨-, hSurv⟩ | ⟨-, hSurv⟩
    · exact hSurv hDangling
    · exact hSurv hNew
  rw [← card_nonDanglingIncident, hEmpty, Finset.card_empty]

/-- **Both survivors at a divalent ordinary `u`-endpoint carry the same row**:
the retained doubled-direction survivor of the class and the class's new
occurrence. -/
theorem rowOfEdge_endpointVertex_false {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hOldSurv : ¬ IsDangling data (doubledOccurrence source x))
    {e : NonDanglingEdge (cand).datum}
    (hE : Incident (cand).datum e.1 (endpointVertex source hNoGlue hValid false x)) :
    rowOfEdge source hNoGlue hValid e =
      some (NonDanglingEdge.stablePath
        (⟨doubledOccurrence source x, hOldSurv⟩ : NonDanglingEdge data)) := by
  classical
  rcases (mem_nonDanglingIncident_endpointVertex_false_ordinary source hNoGlue hValid hX
    e.1).mp ((mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hE⟩) with ⟨hc, -⟩ | ⟨hc, -⟩
  · have hSurvOld : ¬ IsDangling (cand).datum
        ((cand).oldSourceEdge (doubledOccurrence source x)) := by
      rw [← hc]; exact e.2
    rw [show e = (⟨_, hSurvOld⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hc,
      rowOfEdge_old source hNoGlue hValid hSurvOld hOldSurv]
  · have hSurvNew : ¬ IsDangling (cand).datum ((cand).newSourceEdge x) := by
      rw [← hc]; exact e.2
    rw [show e = (⟨_, hSurvNew⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hc,
      rowOfEdge_new_ordinary source hNoGlue hValid hX hSurvNew]


/-! ## 5.  The trivalent end of an ordinary block -/

/-- **Every survivor at a trivalent ordinary endpoint has an old witness**: the
retained occurrence itself on the `v` side, the doubled-direction survivor of
the fine class on the `u` side.  Its row is the row of the witness. -/
theorem exists_rowWitness_true {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    {e : NonDanglingEdge (cand).datum}
    (hE : Incident (cand).datum e.1 (endpointVertex source hNoGlue hValid true x)) :
    ∃ w : NonDanglingEdge data,
      Incident data w.1 (data.sourceEndpoint wall x) ∧
      rowOfEdge source hNoGlue hValid e = some w.stablePath ∧
      ((Prescribed.rightAssignment source w.1.1.1 = true ∧ e.1 = (cand).oldSourceEdge w.1) ∨
        (Prescribed.rightAssignment source w.1.1.1 = false ∧
          e.1 = (cand).newSourceEdge w.1.1.2)) := by
  classical
  rcases ResolutionPruning.sourceEdge_cases (cand) e.1 with ⟨old, hc⟩ | ⟨y, hc⟩
  · have hSurv : ¬ IsDangling (cand).datum ((cand).oldSourceEdge old) := by
      rw [← hc]; exact e.2
    have hIncident : Incident (cand).datum ((cand).oldSourceEdge old)
        (endpointVertex source hNoGlue hValid true x) := by
      rw [← hc]; exact hE
    obtain ⟨⟨hMem, hRel⟩, hSide⟩ :=
      (incident_oldSourceEdge_endpointVertex_iff source hNoGlue hValid true hX old).mp hIncident
    have hData : ¬ IsDangling data old := fun h ↦ hSurv
      ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand) hValid
        (candidate_sourceGenus source hNoGlue hValid) old).mpr h)
    refine ⟨⟨old, hData⟩, (incident_sourceEndpoint_wall_iff x old).mpr ⟨hMem, hRel⟩, ?_,
      Or.inl ⟨hSide, hc⟩⟩
    rw [show e = (⟨_, hSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hc,
      rowOfEdge_old source hNoGlue hValid hSurv hData]
  · have hSurv : ¬ IsDangling (cand).datum ((cand).newSourceEdge y) := by
      rw [← hc]; exact e.2
    have hIncident : Incident (cand).datum ((cand).newSourceEdge y)
        (endpointVertex source hNoGlue hValid true x) := by
      rw [← hc]; exact hE
    have hWallRel : (data.vertexPartition wall).Rel x y :=
      wall_rel_of_incident_true source hNoGlue hValid hX hIncident
    have hY : ¬ (data.vertexPartition wall).Rel anchor.1 y :=
      fun h ↦ hX (h.trans hWallRel.symm)
    have hData := (newSourceEdge_survives_iff_ordinary source hNoGlue hValid hY).mp hSurv
    refine ⟨⟨doubledOccurrence source y, hData⟩, ?_, ?_,
      Or.inr ⟨rightAssignment_doubledOccurrence source y, ?_⟩⟩
    · rw [sourceEndpoint_eq_of_rel hWallRel]
      exact incident_doubledOccurrence source y
    · rw [show e = (⟨_, hSurv⟩ : NonDanglingEdge (cand).datum) from Subtype.ext hc,
        rowOfEdge_new_ordinary source hNoGlue hValid hY hSurv]
    · rw [hc]
      exact (newSourceEdge_doubledOccurrence_sheet source hNoGlue hValid hY).symm

/-- **Two survivors at a divalent trivalent ordinary endpoint carry the same
row**: their old witnesses are two distinct survivors of the block, which is
divalent in the wall datum. -/
theorem rowOfEdge_eq_endpointVertex_true {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hValency : nonDanglingValency (cand).datum
      (endpointVertex source hNoGlue hValid true x) = 2)
    {e f : NonDanglingEdge (cand).datum} (hNe : e ≠ f)
    (hE : Incident (cand).datum e.1 (endpointVertex source hNoGlue hValid true x))
    (hF : Incident (cand).datum f.1 (endpointVertex source hNoGlue hValid true x)) :
    rowOfEdge source hNoGlue hValid e = rowOfEdge source hNoGlue hValid f := by
  classical
  obtain ⟨we, hweInc, hweRow, hweCase⟩ :=
    exists_rowWitness_true source hNoGlue hValid hX hE
  obtain ⟨wf, hwfInc, hwfRow, hwfCase⟩ :=
    exists_rowWitness_true source hNoGlue hValid hX hF
  have hDataVal : nonDanglingValency data (data.sourceEndpoint wall x) = 2 := by
    rw [← nonDanglingValency_endpointVertex_true_ordinary source hNoGlue hValid hX]
    exact hValency
  have hNeW : we ≠ wf := by
    intro hEq
    refine hNe (Subtype.ext ?_)
    rcases hweCase with ⟨hs1, h1⟩ | ⟨hs1, h1⟩ <;> rcases hwfCase with ⟨hs2, h2⟩ | ⟨hs2, h2⟩
    · rw [h1, h2, hEq]
    · rw [hEq] at hs1
      rw [hs1] at hs2
      exact absurd hs2 (by simp)
    · rw [hEq] at hs1
      rw [hs1] at hs2
      exact absurd hs2 (by simp)
    · rw [h1, h2, hEq]
  rw [hweRow, hwfRow]
  exact congrArg (fun r : StablePath data ↦ some r)
    (stablePath_eq_of_consecutive
      ⟨hNeW, data.sourceEndpoint wall x, hweInc, hwfInc, hDataVal⟩)

/-! ## 6.  The anchor block carries no divalent endpoint -/

/-- A fine class of the anchor block other than the bridge class is a
singleton, and its divalent endpoint carries nothing at all. -/
theorem nonDanglingIncident_endpointVertex_anchor_singleton {x : Fin degree}
    (hWall : (data.vertexPartition wall).Rel anchor.1 x)
    (hNotRel : ¬ (Prescribed.finePartition source).Rel rep x) :
    nonDanglingIncident (cand).datum
      (endpointVertex source hNoGlue hValid false x) = ∅ := by
  classical
  rcases Prescribed.finePartition_rel_or_singleton source x hWall with hRel | hSing
  · exact absurd hRel hNotRel
  · refine Finset.eq_empty_of_forall_notMem ?_
    intro e he
    have hMem := nonDanglingIncident_singleton_subset source hNoGlue hValid hWall hSing
      hNotRel he
    rw [Finset.mem_singleton] at hMem
    refine ((mem_nonDanglingIncident _ _ _).mp he).1 ?_
    rw [hMem]
    exact newSourceEdge_isDangling_of_singleton source hNoGlue hValid hWall hSing hNotRel

/-- **No endpoint vertex over the anchor block is divalent.**  Both endpoints of
the bridge class are trivalent and the remaining `u`-endpoints are empty, so no
stable path turns inside the anchor. -/
theorem nonDanglingValency_endpointVertex_anchor_ne_two (sideValue : Bool)
    {x : Fin degree} (hWall : (data.vertexPartition wall).Rel anchor.1 x) :
    nonDanglingValency (cand).datum
      (endpointVertex source hNoGlue hValid sideValue x) ≠ 2 := by
  classical
  cases sideValue
  · by_cases hRel : (Prescribed.finePartition source).Rel rep x
    · have hEq : endpointVertex source hNoGlue hValid false rep =
          endpointVertex source hNoGlue hValid false x := by
        refine endpointVertex_eq source hNoGlue hValid false (rep_wall_rel source) ?_
        exact (hRel : (endpointPartition source false).Rel rep x)
      rw [← hEq, nonDanglingValency_endpointVertex source hNoGlue hValid false]
      omega
    · rw [← card_nonDanglingIncident,
        nonDanglingIncident_endpointVertex_anchor_singleton source hNoGlue hValid hWall hRel]
      simp
  · have hEq : endpointVertex source hNoGlue hValid true rep =
        endpointVertex source hNoGlue hValid true x := by
      refine endpointVertex_eq source hNoGlue hValid true (rep_wall_rel source) ?_
      exact ((rep_wall_rel source).symm.trans hWall :
        (endpointPartition source true).Rel rep x)
    rw [← hEq, nonDanglingValency_endpointVertex source hNoGlue hValid true]
    omega

/-! ## 7.  The reverse map is constant on stable paths -/

theorem rowOfEdge_eq_wall (sideValue : Bool)
    {v : (cand).datum.SourceVertex} (x : Fin degree)
    (hv : endpointVertex source hNoGlue hValid sideValue x = v)
    {e f : NonDanglingEdge (cand).datum} (hNe : e ≠ f)
    (hE : Incident (cand).datum e.1 v) (hF : Incident (cand).datum f.1 v)
    (hValency : nonDanglingValency (cand).datum v = 2) :
    rowOfEdge source hNoGlue hValid e = rowOfEdge source hNoGlue hValid f := by
  classical
  subst hv
  by_cases hA : (data.vertexPartition wall).Rel anchor.1 x
  · exact absurd hValency
      (nonDanglingValency_endpointVertex_anchor_ne_two source hNoGlue hValid sideValue hA)
  · cases sideValue
    · have hOldSurv : ¬ IsDangling data (doubledOccurrence source x) :=
        not_isDangling_doubledOccurrence_of_valency source hNoGlue hValid hA
          (by rw [hValency]; omega)
      rw [rowOfEdge_endpointVertex_false source hNoGlue hValid hA hOldSurv hE,
        rowOfEdge_endpointVertex_false source hNoGlue hValid hA hOldSurv hF]
    · exact rowOfEdge_eq_endpointVertex_true source hNoGlue hValid hA hValency hNe hE hF

theorem rowOfEdge_eq_away {v : (cand).datum.SourceVertex}
    {place : target.V} (hAway : place ≠ wall) (hTarget : v.1.1 = oldVertex target place)
    {e f : NonDanglingEdge (cand).datum} (hNe : e ≠ f)
    (hE : Incident (cand).datum e.1 v) (hF : Incident (cand).datum f.1 v)
    (hValency : nonDanglingValency (cand).datum v = 2) :
    rowOfEdge source hNoGlue hValid e = rowOfEdge source hNoGlue hValid f := by
  obtain ⟨old, hOldTarget, hOldVertex⟩ :=
    ResolutionAwayFromWall.exists_retainedVertex_of_target (cand) v place hAway hTarget
  have hOldAway : old.1.1 ≠ wall := fun hEq ↦ hAway (hOldTarget.symm.trans hEq)
  subst hOldVertex
  rcases ResolutionAwayFromWall.nonDanglingEdge_cases (cand) hValid
    (candidate_sourceGenus source hNoGlue hValid) e with ⟨oe, rfl⟩ | ⟨sheet, hSheet, rfl⟩
  · rcases ResolutionAwayFromWall.nonDanglingEdge_cases (cand) hValid
      (candidate_sourceGenus source hNoGlue hValid) f with ⟨of, rfl⟩ | ⟨sheet, hSheet, rfl⟩
    · rw [rowOfEdge_retained source hNoGlue hValid oe,
        rowOfEdge_retained source hNoGlue hValid of]
      refine congrArg (fun r : StablePath data ↦ some r)
        (stablePath_eq_of_consecutive ⟨?_, old, ?_, ?_, ?_⟩)
      · exact fun hEq ↦ hNe (congrArg
          (ResolutionAwayFromWall.retainedEdge (cand) hValid.1) hEq)
      · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff (cand) old hOldAway oe.1).mp hE
      · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff (cand) old hOldAway of.1).mp hF
      · exact (ResolutionAwayFromWall.nonDanglingValency_retainedVertex (cand) hValid
          (candidate_sourceGenus source hNoGlue hValid) old hOldAway).symm.trans hValency
    · exact absurd hF
        (ResolutionAwayFromWall.not_incident_newSourceEdge (cand) old hOldAway sheet)
  · exact absurd hE
      (ResolutionAwayFromWall.not_incident_newSourceEdge (cand) old hOldAway sheet)

/-- **The reverse row map descends to stable paths.** -/
theorem rowOfEdge_eq_of_consecutive {e f : NonDanglingEdge (cand).datum}
    (h : Consecutive (cand).datum e f) :
    rowOfEdge source hNoGlue hValid e = rowOfEdge source hNoGlue hValid f := by
  obtain ⟨hNe, v, hE, hF, hValency⟩ := h
  cases hTarget : v.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · rw [hAt] at hTarget
        exact rowOfEdge_eq_wall source hNoGlue hValid false v.1.2
          (((cand).datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨hTarget.symm, rfl⟩)
          hNe hE hF hValency
      · exact rowOfEdge_eq_away source hNoGlue hValid hAt hTarget hNe hE hF hValency
  | inr point =>
      cases point
      exact rowOfEdge_eq_wall source hNoGlue hValid true v.1.2
        (((cand).datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨hTarget.symm, rfl⟩)
        hNe hE hF hValency


/-! ## 8.  The row equivalence -/

/-- The candidate's one new stable row. -/
noncomputable def bridgeRow : StablePath (cand).datum :=
  NonDanglingEdge.stablePath
    (⟨bridgeEdge source hNoGlue hValid rep, bridgeEdge_survives source hNoGlue hValid⟩ :
      NonDanglingEdge (cand).datum)

theorem rowOfEdge_bridge :
    rowOfEdge source hNoGlue hValid
      (⟨bridgeEdge source hNoGlue hValid rep, bridgeEdge_survives source hNoGlue hValid⟩ :
        NonDanglingEdge (cand).datum) = none := by
  have hSurv : ¬ IsDangling (cand).datum ((cand).newSourceEdge rep) :=
    bridgeEdge_survives source hNoGlue hValid
  have hEq : (⟨bridgeEdge source hNoGlue hValid rep,
      bridgeEdge_survives source hNoGlue hValid⟩ : NonDanglingEdge (cand).datum) =
        ⟨(cand).newSourceEdge rep, hSurv⟩ := rfl
  rw [hEq, rowOfEdge_new_anchor source hNoGlue hValid (rep_wall_rel source) hSurv]

/-- A surviving new occurrence over the anchor block is the bridge. -/
theorem newSourceEdge_eq_bridge_of_anchor {y : Fin degree}
    (hY : (data.vertexPartition wall).Rel anchor.1 y)
    (hSurv : ¬ IsDangling (cand).datum ((cand).newSourceEdge y)) :
    (cand).newSourceEdge y = bridgeEdge source hNoGlue hValid rep := by
  classical
  have hSheet : ((cand).newSourceEdge y).1.2 =
      (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.repr y := rfl
  by_cases hRel : (Prescribed.finePartition source).Rel rep
      ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.repr y)
  · exact newSourceEdge_eq_bridge_of_rel source hNoGlue hValid hRel
  · exfalso
    have hWall : (data.vertexPartition wall).Rel anchor.1
        ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
          (cand).contracts).newEdge.repr y) := by
      refine hY.trans ?_
      rw [← hSheet]
      exact wall_rel_newSourceEdge_sheet source hNoGlue hValid y
    rcases Prescribed.finePartition_rel_or_singleton source _ hWall with hFine | hSing
    · exact hRel hFine
    · refine hSurv ?_
      have hEqU : (cand).newSourceEdge y =
          (cand).newSourceEdge ((LocalResolution.paste (data.vertexPartition wall)
            (cand).resolution (cand).contracts).newEdge.repr y) := by
        rw [← hSheet]
        exact (newSourceEdge_sheet_eq_self source hNoGlue hValid y).symm
      rw [hEqU]
      exact newSourceEdge_isDangling_of_singleton source hNoGlue hValid hWall hSing hRel

/-- The reverse row map, on stable paths. -/
noncomputable def rowDescend : StablePath (cand).datum → Option (StablePath data) :=
  Quot.lift (rowOfEdge source hNoGlue hValid)
    (fun _ _ h ↦ rowOfEdge_eq_of_consecutive source hNoGlue hValid h)

@[simp] theorem rowDescend_mk (e : NonDanglingEdge (cand).datum) :
    rowDescend source hNoGlue hValid e.stablePath = rowOfEdge source hNoGlue hValid e := rfl

/-- The forward row map: the bridge row for `none`, the retained row for a row
of the incoming wall datum. -/
noncomputable def rowMap : Option (StablePath data) → StablePath (cand).datum
  | none => bridgeRow source hNoGlue hValid
  | some r => NonTrivalentValencyThreeDescent.retainedRow source hNoGlue hValid r

theorem rowDescend_bridgeRow :
    rowDescend source hNoGlue hValid (bridgeRow source hNoGlue hValid) = none :=
  rowOfEdge_bridge source hNoGlue hValid

theorem rowDescend_retainedRow (r : StablePath data) :
    rowDescend source hNoGlue hValid
        (NonTrivalentValencyThreeDescent.retainedRow source hNoGlue hValid r) = some r := by
  induction r using Quot.inductionOn with
  | h e => exact rowOfEdge_retained source hNoGlue hValid e

/-- **Every stable row of the candidate is a retained row or the bridge row.** -/
theorem rowMap_rowOfEdge (e : NonDanglingEdge (cand).datum) :
    rowMap source hNoGlue hValid (rowOfEdge source hNoGlue hValid e) = e.stablePath := by
  classical
  rcases ResolutionAwayFromWall.nonDanglingEdge_cases (cand) hValid
    (candidate_sourceGenus source hNoGlue hValid) e with ⟨old, rfl⟩ | ⟨y, hSurv, rfl⟩
  · rw [rowOfEdge_retained source hNoGlue hValid old]
    rfl
  · by_cases hA : (data.vertexPartition wall).Rel anchor.1 y
    · rw [rowOfEdge_new_anchor source hNoGlue hValid hA hSurv]
      show bridgeRow source hNoGlue hValid = _
      refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
      exact (newSourceEdge_eq_bridge_of_anchor source hNoGlue hValid hA hSurv).symm
    · rw [rowOfEdge_new_ordinary source hNoGlue hValid hA hSurv]
      show NonTrivalentValencyThreeDescent.retainedRow source hNoGlue hValid _ = _
      have hData := (newSourceEdge_survives_iff_ordinary source hNoGlue hValid hA).mp hSurv
      have hMem : (⟨doubledOccurrence source y, hData⟩ : NonDanglingEdge data).1 ∈
          ordinaryStar source y false :=
        (mem_ordinaryStar source _).mpr
          ⟨⟨hData, incident_doubledOccurrence source y⟩,
            rightAssignment_doubledOccurrence source y⟩
      refine Eq.trans (stablePath_retainedEdge_eq_newSourceEdge source hNoGlue hValid hA hMem)
        (congrArg NonDanglingEdge.stablePath (Subtype.ext ?_))
      exact newSourceEdge_doubledOccurrence_sheet source hNoGlue hValid hA

/-- **The row dictionary of the prescribed valency-three candidate.** -/
noncomputable def rowEquiv : StablePath (cand).datum ≃ Option (StablePath data) where
  toFun := rowDescend source hNoGlue hValid
  invFun := rowMap source hNoGlue hValid
  left_inv := by
    intro path
    induction path using Quot.inductionOn with
    | h e => exact rowMap_rowOfEdge source hNoGlue hValid e
  right_inv := by
    intro r
    cases r with
    | none => exact rowDescend_bridgeRow source hNoGlue hValid
    | some r => exact rowDescend_retainedRow source hNoGlue hValid r

@[simp] theorem rowEquiv_retainedRow (r : StablePath data) :
    rowEquiv source hNoGlue hValid
        (NonTrivalentValencyThreeDescent.retainedRow source hNoGlue hValid r) = some r :=
  rowDescend_retainedRow source hNoGlue hValid r

@[simp] theorem rowEquiv_bridgeRow :
    rowEquiv source hNoGlue hValid (bridgeRow source hNoGlue hValid) = none :=
  rowDescend_bridgeRow source hNoGlue hValid

/-- **The honest stable length-matrix labelling of the outgoing candidate**, now
with no supplied row equivalence. -/
noncomputable def labelling {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (labelling₀ : StableLengthMatrixLabelling data coordinate) :
    StableLengthMatrixLabelling (cand).datum (Option coordinate) :=
  NonTrivalentValencyThreeRows.labelling source hNoGlue hValid labelling₀
    (rowEquiv source hNoGlue hValid)

@[simp] theorem labelling_row_retained {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (r : StablePath data) :
    (labelling source hNoGlue hValid labelling₀).row
        (NonTrivalentValencyThreeDescent.retainedRow source hNoGlue hValid r) =
      some (labelling₀.row r) := by
  rw [labelling, NonTrivalentValencyThreeRows.labelling_row, rowEquiv_retainedRow]
  rfl

@[simp] theorem labelling_row_bridge {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (labelling₀ : StableLengthMatrixLabelling data coordinate) :
    (labelling source hNoGlue hValid labelling₀).row (bridgeRow source hNoGlue hValid) =
      none := by
  rw [labelling, NonTrivalentValencyThreeRows.labelling_row, rowEquiv_bridgeRow]
  rfl


/-! ## 9.  At an actual three-valent wall

The hypothesis list of `NonTrivalentValencyThreeRows.candidate_sourceGenus_of_contraction`
with the anchor's `nd(A) = 4` removed: it is produced, together with the anchor
block and its `ThreeBranchAnchor` classification, by
`NonTrivalentAnchorValency.threeBranchAnchor_of_single_row` out of the wall
metric of a Part II open facet.  No ordinary-block valency bound is needed: at
valency three the row of a new occurrence is the row of the doubled-direction
survivor of its own fine class, so no choice of side is made. -/

section Incoming

open GraphContraction GluingContraction ContractionFibre ContractionRamification
open FullDimensionalSource WallDegeneration

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The full valency-three row dictionary at an actual three-valent wall**,
with every receipt discharged from the wall metric: the anchor block, its
`ThreeBranchAnchor` classification and surviving valency four, the outgoing
candidate's validity and source genus, and the row equivalence itself, sending
every retained row to its incoming row and the bridge row to `none`. -/
theorem exists_rowEquiv_of_wall_metric
    (cover : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation cover coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest cover a b contracted)
    (wallStar : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
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
      (src : ThreeBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlock)
      (hNoGlue' : DanglingEdgeNoGlue (contractDatum cover hc hab hOne))
      (hValid' : (contractDatum cover hc hab hOne).Valid),
      nonDanglingValency (contractDatum cover hc hab hOne)
          (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩
            anchorBlock) = 4 ∧
        (Prescribed.validCandidate src hNoGlue' hValid').datum.Valid ∧
        genus (Prescribed.validCandidate src hNoGlue' hValid').datum.sourceGraph =
          genus (contractDatum cover hc hab hOne).sourceGraph ∧
        (∀ r, rowEquiv src hNoGlue' hValid'
            (NonTrivalentValencyThreeDescent.retainedRow src hNoGlue' hValid' r) = some r) ∧
          rowEquiv src hNoGlue' hValid' (bridgeRow src hNoGlue' hValid') = none := by
  obtain ⟨anchorBlock, hNd, src⟩ :=
    NonTrivalentAnchorValency.threeBranchAnchor_of_single_row cover fd hc hab hOne
      hForest coordinates facet hRows hZeroCoord hPosCoord hFacetZero wallStar
  have hCompat : DanglingCompatible cover hc hab hOne :=
    WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest
  refine ⟨anchorBlock, src,
    NonTrivalentValencyThreeRows.wall_noGlue cover fd hc hab hOne hCompat,
    NonTrivalentValencyThreeRows.wall_valid cover fd hc hab hOne hForest, hNd, ?_, ?_, ?_, ?_⟩
  · exact Prescribed.validCandidate_datum_valid src _ _
  · exact NonTrivalentValencyThreeRows.candidate_sourceGenus src _ _
  · exact fun r ↦ rowEquiv_retainedRow src _ _ r
  · exact rowEquiv_bridgeRow src _ _

end Incoming

end DraismaVargas.LocalCases.NonTrivalentValencyThreeRowEquiv
