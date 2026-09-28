import DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRows

/-!
# The row dictionary of the prescribed Type I / Type II valency-three candidates

Source: Vargas, Part II (arXiv:2609.09109), Section 5.3 (Case `{v3-nd4}`,
base trees `T_alpha` with `alpha` simple), with Section 5.1 (Lemma
`lemma-above-w0`) for the wall blocks above `w_0` other than the anchor.

`NonTrivalentValencyThreeSimpleRows` builds the anchor picture for the Type I /
Type II candidates -- the three outgoing vertices `A_u`, `A'`, `A_v` with
their exact stars `3, 2, 3`, `bridgeEdge_isolated` and
`newSourceEdge_stablePath_eq_retained` -- and makes `retainedRow`
unconditional.  This module builds the inverse row map and packages the two into
`StablePath (validCandidate base hValid).datum ≃ Option (StablePath base.gaugedData)`.

## What is proved

* `newWitness`: the gauged survivor whose stable row carries a given new
  occurrence.  Over an ordinary block it is the alpha-direction survivor of the
  sheet's own fine class (`ordinaryWitness`); over the **anchor** block it is
  `e_delta` on the class `A'` and `none` on the bridge class (`anchorWitness`).
  This is the one structural difference from the Type III case
  (`NonTrivalentValencyThreeRowEquiv`), where no new vertex above the anchor is
  divalent: here `A'` is, and `e'` shares the retained row of `e_delta`.
* `rowOfEdge` and `rowOfEdge_eq_of_consecutive`: the reverse map on surviving
  occurrences is constant on stable paths.  The geometric inputs are
  `ResolutionAwayFromWall` off the wall (`rowOfEdge_eq_away`), the anchor
  census of `NonTrivalentValencyThreeSimpleRows` (`rowOfEdge_deltaRight` at
  `A'`, `nonDanglingValency_left_anchor_ne_two` and
  `nonDanglingValency_right_anchor_ne_two` everywhere else above the anchor),
  and the ordinary-block census (`rowOfEdge_endpointVertex_false`,
  `rowOfEdge_eq_endpointVertex_true`).
* `rowEquiv`, with `rowEquiv_retainedRow`, `rowEquiv_bridgeRow` and
  `rowEquiv_bridgeDelta` (the `e'` occurrence maps to `e_delta`'s row);
  surjectivity is `rowMap_rowOfEdge` and injectivity `rowDescend_retainedRow`.
* `gaugedLabelling` and `gaugedLabelling_matrix`: the incoming chart carried
  across the two branch gauges, with the honest matrix unchanged
  (`RelabelFullDimensional.sheet_matrix_eq` twice); and `labelling`, the
  candidate's own honest stable length-matrix labelling over
  `Option coordinate`, with `labelling_row_retained` and `labelling_row_bridge`.
* `RowPackage` and `rowPackage`: the whole package (outgoing validity, source
  genus, the `3, 2, 3` census and the three `rowEquiv` identities) for a
  prescribed simple base.  At an actual three-valent wall the anchor's
  `nd(A) = 4` and `DanglingCompatible` come from the wall metric, through
  `NonTrivalentAnchorValency.threeBranchAnchor_of_single_row` and
  `WallAdmissibility.danglingCompatible_of_contractionForest`, exactly as in
  `NonTrivalentValencyThreeRowEquiv.exists_rowEquiv_of_wall_metric`.

## What is not proved here

The entrywise common-minor / `AgreeOffColumn` identity of the outgoing labelled
matrix against the incoming full-dimensional matrix, on the pattern of
`NonTrivalentValencyThreeRowDictionary.matrix_chartLabelling_eq_incoming`.  Its
gauge half is available here as `gaugedLabelling_matrix`; the rest is
`NonTrivalentValencyThreeSimpleRowDictionary.occurrences_retainedRow` /
`matrix_retainedRow` over `base.gaugedData` and one `.trans` with
`StablePathFacetContraction.matrix_wallLabelling`
(`noContractedReturn_of_threeStar` applies verbatim at a three-valent wall),
assembled in `NonTrivalentValencyThreeSimpleExit.matrix_outLabelling_eq_incoming`.

Nothing here constructs a `FullDimensionalSourcePresentation`, a
`ContractionForest`, a `ThreeStar` or the wall metric.

## Consumers

The boundary dispatcher for Part II Case `{v3-nd4}`, and through it
`OuterWalk.TypeChangeLink`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRowEquiv

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
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRows
open DraismaVargas.LocalCases.NonTrivalentValencyThreeRowEquiv (witnessOf witnessOf_pos
  witnessOf_neg)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (datum : GluingDatum target degree)
    (vertex : datum.SourceVertex) : DecidableEq (IncidentSourceEdge datum vertex) :=
  Classical.decEq _

variable {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall} (base : SimpleBase data star anchor)

/-! ## 1.  The old survivor carrying a new occurrence -/

/-- Over an ordinary wall block the new occurrence of a fine class carries the
row of that class's alpha-direction survivor. -/
noncomputable def ordinaryWitness (x : Fin degree) :
    Option (NonDanglingEdge base.gaugedData) :=
  witnessOf base.gaugedData (alphaOccurrenceAt base x)

/-- Over the anchor block the class `A'` carries the row of `e_delta`, while
the bridge class carries the one new row. -/
noncomputable def anchorWitness (x : Fin degree) :
    Option (NonDanglingEdge base.gaugedData) :=
  if x ∈ base.newDeltaBlock then witnessOf base.gaugedData (deltaOccurrence base)
  else none

/-- The old survivor whose stable row carries the new occurrence of the sheet
`x`, if any. -/
noncomputable def newWitness (x : Fin degree) :
    Option (NonDanglingEdge base.gaugedData) :=
  if (data.vertexPartition wall).Rel anchor.1 x then anchorWitness base x
  else ordinaryWitness base x

theorem newWitness_anchor {x : Fin degree}
    (hX : (data.vertexPartition wall).Rel anchor.1 x) :
    newWitness base x = anchorWitness base x := by
  rw [newWitness, if_pos hX]

theorem newWitness_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    newWitness base x = ordinaryWitness base x := by
  rw [newWitness, if_neg hX]

theorem anchorWitness_delta (hValid : data.Valid) {x : Fin degree}
    (hX : x ∈ base.newDeltaBlock) :
    anchorWitness base x =
      some ⟨deltaOccurrence base, deltaOccurrence_survives base hValid⟩ := by
  rw [anchorWitness, if_pos hX, witnessOf_pos (deltaOccurrence_survives base hValid)]

theorem anchorWitness_bridge {x : Fin degree} (hX : x ∉ base.newDeltaBlock) :
    anchorWitness base x = none := by
  rw [anchorWitness, if_neg hX]

theorem ordinaryWitness_pos {x : Fin degree}
    (h : ¬ IsDangling base.gaugedData (alphaOccurrenceAt base x)) :
    ordinaryWitness base x = some ⟨alphaOccurrenceAt base x, h⟩ := by
  rw [ordinaryWitness, witnessOf_pos h]

theorem ordinaryWitness_neg {x : Fin degree}
    (h : IsDangling base.gaugedData (alphaOccurrenceAt base x)) :
    ordinaryWitness base x = none := by
  rw [ordinaryWitness, witnessOf_neg h]

/-! ## 2.  The canonical sheet of a new occurrence -/

theorem newEdge_rel_sheet (hValid : data.Valid) (y : Fin degree) :
    (LocalResolution.paste (base.gaugedData.vertexPartition wall)
      (validCandidate base hValid).resolution
      (validCandidate base hValid).contracts).newEdge.Rel y
        (((validCandidate base hValid).newSourceEdge y).1.2) :=
  (LocalResolution.paste (base.gaugedData.vertexPartition wall)
    (validCandidate base hValid).resolution
    (validCandidate base hValid).contracts).newEdge.rel_repr_right y

/-- Over an ordinary block the witness only depends on the fine class. -/
theorem newWitness_newSourceEdge_sheet_ordinary (hValid : data.Valid) {y : Fin degree}
    (hY : ¬ (data.vertexPartition wall).Rel anchor.1 y) :
    newWitness base (((validCandidate base hValid).newSourceEdge y).1.2) =
      newWitness base y := by
  have hWall : (data.vertexPartition wall).Rel y
      (((validCandidate base hValid).newSourceEdge y).1.2) :=
    wall_rel_newSourceEdge_sheet base hValid y
  have hZ : ¬ (data.vertexPartition wall).Rel anchor.1
      (((validCandidate base hValid).newSourceEdge y).1.2) :=
    fun h ↦ hY (h.trans hWall.symm)
  have hAlpha : alphaOccurrenceAt base
      (((validCandidate base hValid).newSourceEdge y).1.2) =
      alphaOccurrenceAt base y := by
    refine alphaOccurrenceAt_eq_of_rel base ?_
    exact ((newEdge_rel_ordinary base hValid hY).mp
      (newEdge_rel_sheet base hValid y)).symm
  rw [newWitness_ordinary base hZ, newWitness_ordinary base hY, ordinaryWitness,
    ordinaryWitness, hAlpha]

/-! ## 3.  The reverse row map on surviving occurrences -/

/-- The gauged datum's row carrying a surviving occurrence of the candidate,
with `none` for the new bridge row. -/
noncomputable def rowOfEdge (hValid : data.Valid)
    (e : NonDanglingEdge (validCandidate base hValid).datum) :
    Option (StablePath base.gaugedData) :=
  open Classical in
  if h : ∃ old : NonDanglingEdge base.gaugedData,
      ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
        (base.gaugedData_valid hValid).1 old = e then
    some (Classical.choose h).stablePath
  else (newWitness base e.1.1.2).map NonDanglingEdge.stablePath

theorem rowOfEdge_pos (hValid : data.Valid)
    (e : NonDanglingEdge (validCandidate base hValid).datum)
    (h : ∃ old : NonDanglingEdge base.gaugedData,
      ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
        (base.gaugedData_valid hValid).1 old = e) :
    rowOfEdge base hValid e = some (Classical.choose h).stablePath := by
  classical
  rw [rowOfEdge, dif_pos h]

theorem rowOfEdge_neg (hValid : data.Valid)
    (e : NonDanglingEdge (validCandidate base hValid).datum)
    (h : ¬ ∃ old : NonDanglingEdge base.gaugedData,
      ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
        (base.gaugedData_valid hValid).1 old = e) :
    rowOfEdge base hValid e =
      (newWitness base e.1.1.2).map NonDanglingEdge.stablePath := by
  classical
  rw [rowOfEdge, dif_neg h]

theorem rowOfEdge_retained (hValid : data.Valid) (old : NonDanglingEdge base.gaugedData) :
    rowOfEdge base hValid (ResolutionAwayFromWall.retainedEdge
        (validCandidate base hValid) (base.gaugedData_valid hValid).1 old) =
      some old.stablePath := by
  classical
  have h : ∃ o : NonDanglingEdge base.gaugedData,
      ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
          (base.gaugedData_valid hValid).1 o =
        ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
          (base.gaugedData_valid hValid).1 old := ⟨old, rfl⟩
  rw [rowOfEdge_pos base hValid _ h]
  exact congrArg (fun o : NonDanglingEdge base.gaugedData ↦ some o.stablePath)
    (ResolutionAwayFromWall.retainedEdge_injective (validCandidate base hValid)
      (base.gaugedData_valid hValid).1 (Classical.choose_spec h))

theorem rowOfEdge_old (hValid : data.Valid) {old : base.gaugedData.SourceEdge}
    (hSurvives : ¬ IsDangling (validCandidate base hValid).datum
      ((validCandidate base hValid).oldSourceEdge old))
    (hData : ¬ IsDangling base.gaugedData old) :
    rowOfEdge base hValid ⟨(validCandidate base hValid).oldSourceEdge old, hSurvives⟩ =
      some (NonDanglingEdge.stablePath
        (⟨old, hData⟩ : NonDanglingEdge base.gaugedData)) :=
  rowOfEdge_retained base hValid ⟨old, hData⟩

theorem rowOfEdge_new (hValid : data.Valid) {y : Fin degree}
    (hSurvives : ¬ IsDangling (validCandidate base hValid).datum
      ((validCandidate base hValid).newSourceEdge y)) :
    rowOfEdge base hValid ⟨(validCandidate base hValid).newSourceEdge y, hSurvives⟩ =
      (newWitness base (((validCandidate base hValid).newSourceEdge y).1.2)).map
        NonDanglingEdge.stablePath := by
  classical
  have hNot : ¬ ∃ old : NonDanglingEdge base.gaugedData,
      ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
          (base.gaugedData_valid hValid).1 old =
        (⟨(validCandidate base hValid).newSourceEdge y, hSurvives⟩ :
          NonDanglingEdge (validCandidate base hValid).datum) := by
    rintro ⟨old, hEq⟩
    exact newSourceEdge_ne_oldSourceEdge base hValid y old.1
      (congrArg Subtype.val hEq).symm
  exact rowOfEdge_neg base hValid _ hNot

/-- Over an ordinary block a surviving new occurrence carries the row of its
class's alpha-direction survivor. -/
theorem rowOfEdge_new_ordinary (hValid : data.Valid) {y : Fin degree}
    (hY : ¬ (data.vertexPartition wall).Rel anchor.1 y)
    (hSurvives : ¬ IsDangling (validCandidate base hValid).datum
      ((validCandidate base hValid).newSourceEdge y)) :
    rowOfEdge base hValid ⟨(validCandidate base hValid).newSourceEdge y, hSurvives⟩ =
      some (NonDanglingEdge.stablePath (⟨alphaOccurrenceAt base y,
        (newSourceEdge_survives_iff_ordinary base hValid hY).mp hSurvives⟩ :
          NonDanglingEdge base.gaugedData)) := by
  rw [rowOfEdge_new base hValid hSurvives,
    newWitness_newSourceEdge_sheet_ordinary base hValid hY,
    newWitness_ordinary base hY,
    ordinaryWitness_pos base
      ((newSourceEdge_survives_iff_ordinary base hValid hY).mp hSurvives)]
  rfl

theorem wall_rel_anchor_newSourceEdge_sheet (hValid : data.Valid) {y : Fin degree}
    (hY : (data.vertexPartition wall).Rel anchor.1 y) :
    (data.vertexPartition wall).Rel anchor.1
      (((validCandidate base hValid).newSourceEdge y).1.2) :=
  hY.trans (wall_rel_newSourceEdge_sheet base hValid y)

/-- Over the anchor block the second occurrence `e'` above `t_1` carries the
row of `e_delta`. -/
theorem rowOfEdge_new_anchor_delta (hValid : data.Valid) {y : Fin degree}
    (hY : (data.vertexPartition wall).Rel anchor.1 y)
    (hSurvives : ¬ IsDangling (validCandidate base hValid).datum
      ((validCandidate base hValid).newSourceEdge y))
    (hMem : (((validCandidate base hValid).newSourceEdge y).1.2) ∈
      base.newDeltaBlock) :
    rowOfEdge base hValid ⟨(validCandidate base hValid).newSourceEdge y, hSurvives⟩ =
      some (NonDanglingEdge.stablePath
        (⟨deltaOccurrence base, deltaOccurrence_survives base hValid⟩ :
          NonDanglingEdge base.gaugedData)) := by
  rw [rowOfEdge_new base hValid hSurvives,
    newWitness_anchor base (wall_rel_anchor_newSourceEdge_sheet base hValid hY),
    anchorWitness_delta base hValid hMem]
  rfl

/-- Over the anchor block the bridge `e_1` carries no row of the gauged
datum. -/
theorem rowOfEdge_new_anchor_bridge (hValid : data.Valid) {y : Fin degree}
    (hY : (data.vertexPartition wall).Rel anchor.1 y)
    (hSurvives : ¬ IsDangling (validCandidate base hValid).datum
      ((validCandidate base hValid).newSourceEdge y))
    (hMem : (((validCandidate base hValid).newSourceEdge y).1.2) ∉
      base.newDeltaBlock) :
    rowOfEdge base hValid
      ⟨(validCandidate base hValid).newSourceEdge y, hSurvives⟩ = none := by
  rw [rowOfEdge_new base hValid hSurvives,
    newWitness_anchor base (wall_rel_anchor_newSourceEdge_sheet base hValid hY),
    anchorWitness_bridge base hMem]
  rfl

/-! ## 4.  The divalent end of an ordinary block -/

theorem not_isDangling_alphaOccurrenceAt_of_valency (hValid : data.Valid)
    {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hVal : nonDanglingValency (validCandidate base hValid).datum
      (endpointVertex base hValid false x) ≠ 0) :
    ¬ IsDangling base.gaugedData (alphaOccurrenceAt base x) := by
  classical
  intro hDangling
  refine hVal ?_
  have hNew : IsDangling (validCandidate base hValid).datum
      ((validCandidate base hValid).newSourceEdge x) := by
    by_contra h
    exact ((newSourceEdge_survives_iff_ordinary base hValid hX).mp h) hDangling
  have hEmpty : nonDanglingIncident (validCandidate base hValid).datum
      (endpointVertex base hValid false x) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem ?_
    intro e he
    rcases (mem_nonDanglingIncident_endpointVertex_false_ordinary base hValid
      hX e).mp he with ⟨-, hSurv⟩ | ⟨-, hSurv⟩
    · exact hSurv hDangling
    · exact hSurv hNew
  rw [← card_nonDanglingIncident, hEmpty, Finset.card_empty]

/-- **Both survivors at a divalent ordinary `u`-endpoint carry the same row.** -/
theorem rowOfEdge_endpointVertex_false (hValid : data.Valid) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hOldSurv : ¬ IsDangling base.gaugedData (alphaOccurrenceAt base x))
    {e : NonDanglingEdge (validCandidate base hValid).datum}
    (hE : Incident (validCandidate base hValid).datum e.1
      (endpointVertex base hValid false x)) :
    rowOfEdge base hValid e =
      some (NonDanglingEdge.stablePath
        (⟨alphaOccurrenceAt base x, hOldSurv⟩ : NonDanglingEdge base.gaugedData)) := by
  classical
  rcases (mem_nonDanglingIncident_endpointVertex_false_ordinary base hValid hX
    e.1).mp ((mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hE⟩) with ⟨hc, -⟩ | ⟨hc, -⟩
  · have hSurvOld : ¬ IsDangling (validCandidate base hValid).datum
        ((validCandidate base hValid).oldSourceEdge (alphaOccurrenceAt base x)) := by
      rw [← hc]; exact e.2
    rw [show e = (⟨_, hSurvOld⟩ :
        NonDanglingEdge (validCandidate base hValid).datum) from Subtype.ext hc,
      rowOfEdge_old base hValid hSurvOld hOldSurv]
  · have hSurvNew : ¬ IsDangling (validCandidate base hValid).datum
        ((validCandidate base hValid).newSourceEdge x) := by
      rw [← hc]; exact e.2
    rw [show e = (⟨_, hSurvNew⟩ :
        NonDanglingEdge (validCandidate base hValid).datum) from Subtype.ext hc,
      rowOfEdge_new_ordinary base hValid hX hSurvNew]

/-! ## 5.  The trivalent end of an ordinary block -/

/-- **Every survivor at a trivalent ordinary endpoint has an old witness.** -/
theorem exists_rowWitness_true (hValid : data.Valid) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    {e : NonDanglingEdge (validCandidate base hValid).datum}
    (hE : Incident (validCandidate base hValid).datum e.1
      (endpointVertex base hValid true x)) :
    ∃ w : NonDanglingEdge base.gaugedData,
      Incident base.gaugedData w.1 (base.gaugedData.sourceEndpoint wall x) ∧
      rowOfEdge base hValid e = some w.stablePath ∧
      ((base.rightAssignment w.1.1.1 = true ∧
          e.1 = (validCandidate base hValid).oldSourceEdge w.1) ∨
        (base.rightAssignment w.1.1.1 = false ∧
          e.1 = (validCandidate base hValid).newSourceEdge w.1.1.2)) := by
  classical
  rcases ResolutionPruning.sourceEdge_cases (validCandidate base hValid) e.1 with
    ⟨old, hc⟩ | ⟨y, hc⟩
  · have hSurv : ¬ IsDangling (validCandidate base hValid).datum
        ((validCandidate base hValid).oldSourceEdge old) := by
      rw [← hc]; exact e.2
    have hIncident : Incident (validCandidate base hValid).datum
        ((validCandidate base hValid).oldSourceEdge old)
        (endpointVertex base hValid true x) := by
      rw [← hc]; exact hE
    obtain ⟨⟨hMem, hRel⟩, hSide⟩ :=
      (incident_oldSourceEdge_endpointVertex_iff base hValid true hX old).mp hIncident
    have hData : ¬ IsDangling base.gaugedData old := fun h ↦ hSurv
      ((retained_isDangling_iff base hValid old).mpr h)
    refine ⟨⟨old, hData⟩,
      (incident_sourceEndpoint_wall_iff base x old).mpr ⟨hMem, hRel⟩, ?_,
      Or.inl ⟨hSide, hc⟩⟩
    rw [show e = (⟨_, hSurv⟩ :
        NonDanglingEdge (validCandidate base hValid).datum) from Subtype.ext hc,
      rowOfEdge_old base hValid hSurv hData]
  · have hSurv : ¬ IsDangling (validCandidate base hValid).datum
        ((validCandidate base hValid).newSourceEdge y) := by
      rw [← hc]; exact e.2
    have hIncident : Incident (validCandidate base hValid).datum
        ((validCandidate base hValid).newSourceEdge y)
        (endpointVertex base hValid true x) := by
      rw [← hc]; exact hE
    have hWallRel : (base.gaugedData.vertexPartition wall).Rel x y :=
      wall_rel_of_incident_true base hValid hX hIncident
    have hY : ¬ (data.vertexPartition wall).Rel anchor.1 y := by
      intro h
      refine hX ?_
      rw [← gauged_rel_iff base] at h ⊢
      exact h.trans hWallRel.symm
    have hData := (newSourceEdge_survives_iff_ordinary base hValid hY).mp hSurv
    refine ⟨⟨alphaOccurrenceAt base y, hData⟩, ?_, ?_,
      Or.inr ⟨base.rightAssignment_alpha, ?_⟩⟩
    · rw [sourceEndpoint_eq_of_rel base hWallRel]
      exact incident_alphaOccurrenceAt base y
    · rw [show e = (⟨_, hSurv⟩ :
          NonDanglingEdge (validCandidate base hValid).datum) from Subtype.ext hc,
        rowOfEdge_new_ordinary base hValid hY hSurv]
    · rw [hc]
      exact (newSourceEdge_alphaOccurrenceAt_sheet base hValid hY).symm

/-- **Two survivors at a divalent trivalent ordinary endpoint carry the same
row.** -/
theorem rowOfEdge_eq_endpointVertex_true (hValid : data.Valid) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hValency : nonDanglingValency (validCandidate base hValid).datum
      (endpointVertex base hValid true x) = 2)
    {e f : NonDanglingEdge (validCandidate base hValid).datum} (hNe : e ≠ f)
    (hE : Incident (validCandidate base hValid).datum e.1
      (endpointVertex base hValid true x))
    (hF : Incident (validCandidate base hValid).datum f.1
      (endpointVertex base hValid true x)) :
    rowOfEdge base hValid e = rowOfEdge base hValid f := by
  classical
  obtain ⟨we, hweInc, hweRow, hweCase⟩ := exists_rowWitness_true base hValid hX hE
  obtain ⟨wf, hwfInc, hwfRow, hwfCase⟩ := exists_rowWitness_true base hValid hX hF
  have hDataVal : nonDanglingValency base.gaugedData
      (base.gaugedData.sourceEndpoint wall x) = 2 := by
    rw [← nonDanglingValency_endpointVertex_true_ordinary base hValid hX]
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
  exact congrArg (fun r : StablePath base.gaugedData ↦ some r)
    (stablePath_eq_of_consecutive
      ⟨hNeW, base.gaugedData.sourceEndpoint wall x, hweInc, hwfInc, hDataVal⟩)

/-! ## 6.  The anchor block: `A'` is the only divalent new vertex -/

theorem newSourceEdge_deltaRepr_sheet_mem (hValid : data.Valid) :
    (((validCandidate base hValid).newSourceEdge base.deltaRepr).1.2) ∈
      base.newDeltaBlock := by
  refine (newEdge_rel_delta_iff base).mp ?_
  refine (newEdge_rel_iff_newEdgePartition base hValid base.deltaRepr_wall).mp ?_
  exact (LocalResolution.paste (base.gaugedData.vertexPartition wall)
    (validCandidate base hValid).resolution
    (validCandidate base hValid).contracts).newEdge.rel_repr_right base.deltaRepr

theorem newSourceEdge_hubSheet_sheet_not_mem (hValid : data.Valid) :
    (((validCandidate base hValid).newSourceEdge base.hubSheet).1.2) ∉
      base.newDeltaBlock := by
  have hMem : (((validCandidate base hValid).newSourceEdge base.hubSheet).1.2) ∈
      base.alphaBlock \ base.newDeltaBlock := by
    refine (newEdge_rel_hub_iff base).mp ?_
    refine (newEdge_rel_iff_newEdgePartition base hValid base.hubSheet_wall).mp ?_
    exact (LocalResolution.paste (base.gaugedData.vertexPartition wall)
      (validCandidate base hValid).resolution
      (validCandidate base hValid).contracts).newEdge.rel_repr_right base.hubSheet
  exact (Finset.mem_sdiff.mp hMem).2

theorem rowOfEdge_bridge (hValid : data.Valid) :
    rowOfEdge base hValid
      (⟨bridgeEdge base hValid base.hubSheet, bridgeEdge_hub_survives base hValid⟩ :
        NonDanglingEdge (validCandidate base hValid).datum) = none :=
  rowOfEdge_new_anchor_bridge base hValid base.hubSheet_wall
    (bridgeEdge_hub_survives base hValid)
    (newSourceEdge_hubSheet_sheet_not_mem base hValid)

theorem rowOfEdge_bridgeDelta (hValid : data.Valid) :
    rowOfEdge base hValid
        (⟨bridgeEdge base hValid base.deltaRepr, bridgeEdge_delta_survives base hValid⟩ :
          NonDanglingEdge (validCandidate base hValid).datum) =
      some (NonDanglingEdge.stablePath
        (⟨deltaOccurrence base, deltaOccurrence_survives base hValid⟩ :
          NonDanglingEdge base.gaugedData)) :=
  rowOfEdge_new_anchor_delta base hValid base.deltaRepr_wall
    (bridgeEdge_delta_survives base hValid)
    (newSourceEdge_deltaRepr_sheet_mem base hValid)

/-- **Both survivors at the divalent vertex `A'` carry the row of
`e_delta`.** -/
theorem rowOfEdge_deltaRight (hValid : data.Valid)
    {e : NonDanglingEdge (validCandidate base hValid).datum}
    (hE : Incident (validCandidate base hValid).datum e.1
      (endpointVertex base hValid true base.deltaRepr)) :
    rowOfEdge base hValid e =
      some (NonDanglingEdge.stablePath
        (⟨deltaOccurrence base, deltaOccurrence_survives base hValid⟩ :
          NonDanglingEdge base.gaugedData)) := by
  classical
  have hMem : e.1 ∈ nonDanglingIncident (validCandidate base hValid).datum
      (endpointVertex base hValid true base.deltaRepr) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hE⟩
  rw [nonDanglingIncident_deltaRight base hValid, Finset.mem_insert,
    Finset.mem_singleton] at hMem
  rcases hMem with hc | hc
  · rw [show e = (⟨bridgeEdge base hValid base.deltaRepr,
        bridgeEdge_delta_survives base hValid⟩ :
          NonDanglingEdge (validCandidate base hValid).datum) from Subtype.ext hc]
    exact rowOfEdge_bridgeDelta base hValid
  · rw [show e = (⟨(validCandidate base hValid).oldSourceEdge (deltaOccurrence base),
        retained_survives base hValid (deltaOccurrence_survives base hValid)⟩ :
          NonDanglingEdge (validCandidate base hValid).datum) from Subtype.ext hc,
      rowOfEdge_old base hValid _ (deltaOccurrence_survives base hValid)]

/-- Over a sheet of `A` outside `A_u` the divalent end carries nothing. -/
theorem nonDanglingIncident_left_anchor_empty (hValid : data.Valid) {x : Fin degree}
    (hWall : (data.vertexPartition wall).Rel anchor.1 x)
    (hNot : x ∉ base.alphaBlock) :
    nonDanglingIncident (validCandidate base hValid).datum
      (endpointVertex base hValid false x) = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem ?_
  intro e he
  have hMem := nonDanglingIncident_left_singleton_subset base hValid hWall hNot he
  rw [Finset.mem_singleton] at hMem
  refine ((mem_nonDanglingIncident _ _ _).mp he).1 ?_
  rw [hMem]
  exact newSourceEdge_isDangling_of_not_mem_alpha base hValid hWall hNot

/-- **No `u`-endpoint above the anchor block is divalent.** -/
theorem nonDanglingValency_left_anchor_ne_two (hValid : data.Valid) {x : Fin degree}
    (hWall : (data.vertexPartition wall).Rel anchor.1 x) :
    nonDanglingValency (validCandidate base hValid).datum
      (endpointVertex base hValid false x) ≠ 2 := by
  classical
  by_cases hAlpha : x ∈ base.alphaBlock
  · have hEq : endpointVertex base hValid false base.hubSheet =
        endpointVertex base hValid false x :=
      endpointVertex_eq base hValid false base.hubSheet_wall
        ((left_rel_hub_iff base).mpr hAlpha)
    rw [← hEq, nonDanglingValency_hubLeft base hValid]
    omega
  · rw [← card_nonDanglingIncident,
      nonDanglingIncident_left_anchor_empty base hValid hWall hAlpha]
    simp

/-- Above the anchor block only `A'` is divalent on the `v` side. -/
theorem nonDanglingValency_right_anchor_ne_two (hValid : data.Valid) {x : Fin degree}
    (hWall : (data.vertexPartition wall).Rel anchor.1 x)
    (hNot : x ∉ base.newDeltaBlock) :
    nonDanglingValency (validCandidate base hValid).datum
      (endpointVertex base hValid true x) ≠ 2 := by
  have hEq : endpointVertex base hValid true base.hubSheet =
      endpointVertex base hValid true x :=
    endpointVertex_eq base hValid true base.hubSheet_wall
      (base.right_rel_hub_of_mem (Finset.mem_sdiff.mpr
        ⟨mem_wholeBlock_of_wall_rel base hWall, hNot⟩))
  rw [← hEq, nonDanglingValency_hubRight base hValid]
  omega

/-! ## 7.  The reverse map is constant on stable paths -/

theorem rowOfEdge_eq_wall (hValid : data.Valid) (sideValue : Bool)
    {v : (validCandidate base hValid).datum.SourceVertex} (x : Fin degree)
    (hv : endpointVertex base hValid sideValue x = v)
    {e f : NonDanglingEdge (validCandidate base hValid).datum} (hNe : e ≠ f)
    (hE : Incident (validCandidate base hValid).datum e.1 v)
    (hF : Incident (validCandidate base hValid).datum f.1 v)
    (hValency : nonDanglingValency (validCandidate base hValid).datum v = 2) :
    rowOfEdge base hValid e = rowOfEdge base hValid f := by
  classical
  subst hv
  by_cases hA : (data.vertexPartition wall).Rel anchor.1 x
  · cases sideValue
    · exact absurd hValency (nonDanglingValency_left_anchor_ne_two base hValid hA)
    · by_cases hDelta : x ∈ base.newDeltaBlock
      · have hEq : endpointVertex base hValid true base.deltaRepr =
            endpointVertex base hValid true x :=
          endpointVertex_eq base hValid true base.deltaRepr_wall
            (base.right_rel_delta_of_mem hDelta)
        rw [← hEq] at hE hF
        rw [rowOfEdge_deltaRight base hValid hE, rowOfEdge_deltaRight base hValid hF]
      · exact absurd hValency
          (nonDanglingValency_right_anchor_ne_two base hValid hA hDelta)
  · cases sideValue
    · have hOldSurv : ¬ IsDangling base.gaugedData (alphaOccurrenceAt base x) :=
        not_isDangling_alphaOccurrenceAt_of_valency base hValid hA
          (by rw [hValency]; omega)
      rw [rowOfEdge_endpointVertex_false base hValid hA hOldSurv hE,
        rowOfEdge_endpointVertex_false base hValid hA hOldSurv hF]
    · exact rowOfEdge_eq_endpointVertex_true base hValid hA hValency hNe hE hF

theorem rowOfEdge_eq_away (hValid : data.Valid)
    {v : (validCandidate base hValid).datum.SourceVertex}
    {place : target.V} (hAway : place ≠ wall) (hTarget : v.1.1 = oldVertex target place)
    {e f : NonDanglingEdge (validCandidate base hValid).datum} (hNe : e ≠ f)
    (hE : Incident (validCandidate base hValid).datum e.1 v)
    (hF : Incident (validCandidate base hValid).datum f.1 v)
    (hValency : nonDanglingValency (validCandidate base hValid).datum v = 2) :
    rowOfEdge base hValid e = rowOfEdge base hValid f := by
  obtain ⟨old, hOldTarget, hOldVertex⟩ :=
    ResolutionAwayFromWall.exists_retainedVertex_of_target
      (validCandidate base hValid) v place hAway hTarget
  have hOldAway : old.1.1 ≠ wall := fun hEq ↦ hAway (hOldTarget.symm.trans hEq)
  subst hOldVertex
  rcases ResolutionAwayFromWall.nonDanglingEdge_cases (validCandidate base hValid)
    (base.gaugedData_valid hValid) (candidate_sourceGenus base hValid) e with
    ⟨oe, rfl⟩ | ⟨sheet, hSheet, rfl⟩
  · rcases ResolutionAwayFromWall.nonDanglingEdge_cases (validCandidate base hValid)
      (base.gaugedData_valid hValid) (candidate_sourceGenus base hValid) f with
      ⟨of, rfl⟩ | ⟨sheet, hSheet, rfl⟩
    · rw [rowOfEdge_retained base hValid oe, rowOfEdge_retained base hValid of]
      refine congrArg (fun r : StablePath base.gaugedData ↦ some r)
        (stablePath_eq_of_consecutive ⟨?_, old, ?_, ?_, ?_⟩)
      · exact fun hEq ↦ hNe (congrArg
          (ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
            (base.gaugedData_valid hValid).1) hEq)
      · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff
          (validCandidate base hValid) old hOldAway oe.1).mp hE
      · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff
          (validCandidate base hValid) old hOldAway of.1).mp hF
      · exact (ResolutionAwayFromWall.nonDanglingValency_retainedVertex
          (validCandidate base hValid) (base.gaugedData_valid hValid)
          (candidate_sourceGenus base hValid) old hOldAway).symm.trans hValency
    · exact absurd hF (ResolutionAwayFromWall.not_incident_newSourceEdge
        (validCandidate base hValid) old hOldAway sheet)
  · exact absurd hE (ResolutionAwayFromWall.not_incident_newSourceEdge
      (validCandidate base hValid) old hOldAway sheet)

/-- **The reverse row map descends to stable paths.** -/
theorem rowOfEdge_eq_of_consecutive (hValid : data.Valid)
    {e f : NonDanglingEdge (validCandidate base hValid).datum}
    (h : Consecutive (validCandidate base hValid).datum e f) :
    rowOfEdge base hValid e = rowOfEdge base hValid f := by
  obtain ⟨hNe, v, hE, hF, hValency⟩ := h
  cases hTarget : v.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · rw [hAt] at hTarget
        exact rowOfEdge_eq_wall base hValid false v.1.2
          (((validCandidate base hValid).datum.sourceEndpoint_eq_iff _ _ _).mpr
            ⟨hTarget.symm, rfl⟩) hNe hE hF hValency
      · exact rowOfEdge_eq_away base hValid hAt hTarget hNe hE hF hValency
  | inr point =>
      cases point
      exact rowOfEdge_eq_wall base hValid true v.1.2
        (((validCandidate base hValid).datum.sourceEndpoint_eq_iff _ _ _).mpr
          ⟨hTarget.symm, rfl⟩) hNe hE hF hValency

/-! ## 8.  The row equivalence -/

theorem newSourceEdge_anchor_eq_bridgeDelta (hValid : data.Valid) {y : Fin degree}
    (hMem : (((validCandidate base hValid).newSourceEdge y).1.2) ∈ base.newDeltaBlock) :
    (validCandidate base hValid).newSourceEdge y =
      bridgeEdge base hValid base.deltaRepr := by
  rw [← newSourceEdge_sheet_eq_self base hValid y]
  exact (newSourceEdge_eq_of_newEdgePartition_rel base hValid base.deltaRepr_wall
    ((newEdge_rel_delta_iff base).mpr hMem)).symm

theorem newSourceEdge_anchor_eq_bridge (hValid : data.Valid) {y : Fin degree}
    (hY : (data.vertexPartition wall).Rel anchor.1 y)
    (hSurv : ¬ IsDangling (validCandidate base hValid).datum
      ((validCandidate base hValid).newSourceEdge y))
    (hNot : (((validCandidate base hValid).newSourceEdge y).1.2) ∉
      base.newDeltaBlock) :
    (validCandidate base hValid).newSourceEdge y =
      bridgeEdge base hValid base.hubSheet := by
  classical
  have hWallZ : (data.vertexPartition wall).Rel anchor.1
      (((validCandidate base hValid).newSourceEdge y).1.2) :=
    wall_rel_anchor_newSourceEdge_sheet base hValid hY
  have hAlpha : (((validCandidate base hValid).newSourceEdge y).1.2) ∈
      base.alphaBlock := by
    by_contra hNotAlpha
    refine hSurv ?_
    rw [← newSourceEdge_sheet_eq_self base hValid y]
    exact newSourceEdge_isDangling_of_not_mem_alpha base hValid hWallZ hNotAlpha
  rw [← newSourceEdge_sheet_eq_self base hValid y]
  exact (newSourceEdge_eq_of_newEdgePartition_rel base hValid base.hubSheet_wall
    ((newEdge_rel_hub_iff base).mpr (Finset.mem_sdiff.mpr ⟨hAlpha, hNot⟩))).symm

/-- The candidate's one new stable row. -/
noncomputable def bridgeRow (hValid : data.Valid) :
    StablePath (validCandidate base hValid).datum :=
  NonDanglingEdge.stablePath
    (⟨bridgeEdge base hValid base.hubSheet, bridgeEdge_hub_survives base hValid⟩ :
      NonDanglingEdge (validCandidate base hValid).datum)

/-- The reverse row map, on stable paths. -/
noncomputable def rowDescend (hValid : data.Valid) :
    StablePath (validCandidate base hValid).datum →
      Option (StablePath base.gaugedData) :=
  Quot.lift (rowOfEdge base hValid)
    (fun _ _ h ↦ rowOfEdge_eq_of_consecutive base hValid h)

@[simp] theorem rowDescend_mk (hValid : data.Valid)
    (e : NonDanglingEdge (validCandidate base hValid).datum) :
    rowDescend base hValid e.stablePath = rowOfEdge base hValid e := rfl

/-- The forward row map: the bridge row for `none`, the retained row for a row
of the gauged incoming datum. -/
noncomputable def rowMap (hValid : data.Valid)
    (r : Option (StablePath base.gaugedData)) :
    StablePath (validCandidate base hValid).datum :=
  r.elim (bridgeRow base hValid) (retainedRow base hValid)

@[simp] theorem rowMap_none (hValid : data.Valid) :
    rowMap base hValid none = bridgeRow base hValid := rfl

@[simp] theorem rowMap_some (hValid : data.Valid) (r : StablePath base.gaugedData) :
    rowMap base hValid (some r) = retainedRow base hValid r := rfl

theorem rowDescend_bridgeRow (hValid : data.Valid) :
    rowDescend base hValid (bridgeRow base hValid) = none :=
  rowOfEdge_bridge base hValid

theorem rowDescend_retainedRow (hValid : data.Valid) (r : StablePath base.gaugedData) :
    rowDescend base hValid (retainedRow base hValid r) = some r := by
  induction r using Quot.inductionOn with
  | h e => exact rowOfEdge_retained base hValid e

/-- **Every stable row of the candidate is a retained row or the bridge row.** -/
theorem rowMap_rowOfEdge (hValid : data.Valid)
    (e : NonDanglingEdge (validCandidate base hValid).datum) :
    rowMap base hValid (rowOfEdge base hValid e) = e.stablePath := by
  classical
  rcases ResolutionAwayFromWall.nonDanglingEdge_cases (validCandidate base hValid)
    (base.gaugedData_valid hValid) (candidate_sourceGenus base hValid) e with
    ⟨old, rfl⟩ | ⟨y, hSurv, rfl⟩
  · rw [rowOfEdge_retained base hValid old]
    rfl
  · by_cases hA : (data.vertexPartition wall).Rel anchor.1 y
    · by_cases hDelta : (((validCandidate base hValid).newSourceEdge y).1.2) ∈
          base.newDeltaBlock
      · rw [rowOfEdge_new_anchor_delta base hValid hA hSurv hDelta, rowMap_some]
        refine Eq.trans (retainedRow_mk base hValid
          ⟨deltaOccurrence base, deltaOccurrence_survives base hValid⟩) ?_
        refine Eq.trans (newSourceEdge_stablePath_eq_retained base hValid).symm ?_
        exact congrArg NonDanglingEdge.stablePath
          (Subtype.ext (newSourceEdge_anchor_eq_bridgeDelta base hValid hDelta).symm)
      · rw [rowOfEdge_new_anchor_bridge base hValid hA hSurv hDelta, rowMap_none]
        exact congrArg NonDanglingEdge.stablePath
          (Subtype.ext (newSourceEdge_anchor_eq_bridge base hValid hA hSurv hDelta)).symm
    · rw [rowOfEdge_new_ordinary base hValid hA hSurv, rowMap_some]
      have hData := (newSourceEdge_survives_iff_ordinary base hValid hA).mp hSurv
      have hMem : (⟨alphaOccurrenceAt base y, hData⟩ :
          NonDanglingEdge base.gaugedData).1 ∈ ordinaryStar base y false :=
        (mem_ordinaryStar base _).mpr
          ⟨⟨hData, incident_alphaOccurrenceAt base y⟩, base.rightAssignment_alpha⟩
      refine Eq.trans (retainedRow_mk base hValid
        ⟨alphaOccurrenceAt base y, hData⟩) ?_
      refine Eq.trans (stablePath_retainedEdge_eq_newSourceEdge base hValid hA hMem)
        (congrArg NonDanglingEdge.stablePath (Subtype.ext ?_))
      exact newSourceEdge_alphaOccurrenceAt_sheet base hValid hA

/-- **The row dictionary of the prescribed Type I / Type II candidate.** -/
noncomputable def rowEquiv (hValid : data.Valid) :
    StablePath (validCandidate base hValid).datum ≃
      Option (StablePath base.gaugedData) where
  toFun := rowDescend base hValid
  invFun := rowMap base hValid
  left_inv := by
    intro path
    induction path using Quot.inductionOn with
    | h e => exact rowMap_rowOfEdge base hValid e
  right_inv := by
    intro r
    cases r with
    | none => exact rowDescend_bridgeRow base hValid
    | some r => exact rowDescend_retainedRow base hValid r

@[simp] theorem rowEquiv_retainedRow (hValid : data.Valid)
    (r : StablePath base.gaugedData) :
    rowEquiv base hValid (retainedRow base hValid r) = some r :=
  rowDescend_retainedRow base hValid r

@[simp] theorem rowEquiv_bridgeRow (hValid : data.Valid) :
    rowEquiv base hValid (bridgeRow base hValid) = none :=
  rowDescend_bridgeRow base hValid

/-- **`e'` maps to the row of `e_delta`.** -/
@[simp] theorem rowEquiv_bridgeDelta (hValid : data.Valid) :
    rowEquiv base hValid
        (NonDanglingEdge.stablePath
          (⟨bridgeEdge base hValid base.deltaRepr,
            bridgeEdge_delta_survives base hValid⟩ :
              NonDanglingEdge (validCandidate base hValid).datum)) =
      some (NonDanglingEdge.stablePath
        (⟨deltaOccurrence base, deltaOccurrence_survives base hValid⟩ :
          NonDanglingEdge base.gaugedData)) :=
  rowOfEdge_bridgeDelta base hValid

/-! ## 9.  The honest stable length-matrix labelling -/

/-- The incoming chart carried across the two branch gauges. -/
noncomputable def gaugedLabelling {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (labelling₀ : StableLengthMatrixLabelling data coordinate) :
    StableLengthMatrixLabelling base.gaugedData coordinate :=
  RelabelFullDimensional.sheetLabelling base.secondRelabeling
    (middleData_connected base hValid)
    (RelabelFullDimensional.sheetLabelling base.firstRelabeling hValid.1 labelling₀)

/-- **The gauge is invisible to the honest matrix.** -/
theorem gaugedLabelling_matrix {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (labelling₀ : StableLengthMatrixLabelling data coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (gaugedLabelling base hValid labelling₀).presentation =
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation := by
  exact Eq.trans
    (RelabelFullDimensional.sheet_matrix_eq base.secondRelabeling
      (middleData_connected base hValid)
      (RelabelFullDimensional.sheetLabelling base.firstRelabeling hValid.1 labelling₀))
    (RelabelFullDimensional.sheet_matrix_eq base.firstRelabeling hValid.1 labelling₀)

@[simp] theorem gaugedLabelling_targetEdge {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (labelling₀ : StableLengthMatrixLabelling data coordinate) :
    (gaugedLabelling base hValid labelling₀).targetEdge = labelling₀.targetEdge := rfl

/-- **The honest stable length-matrix labelling of the outgoing candidate.**
The gauged wall datum's own square labelling supplies every retained row and
column; `Option.none` is the new target edge `t_1` and the bridge row `h_1`. -/
noncomputable def labelling {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (labelling₀ : StableLengthMatrixLabelling base.gaugedData coordinate) :
    StableLengthMatrixLabelling (validCandidate base hValid).datum
      (Option coordinate) where
  targetEdge := (Equiv.optionCongr labelling₀.targetEdge).trans
    (occurrenceEquiv target wall (validCandidate base hValid).right)
  row := (rowEquiv base hValid).trans (Equiv.optionCongr labelling₀.row)

@[simp] theorem labelling_targetEdge_none {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (labelling₀ : StableLengthMatrixLabelling base.gaugedData coordinate) :
    (labelling base hValid labelling₀).targetEdge none =
      occurrenceEquiv target wall (validCandidate base hValid).right none := rfl

@[simp] theorem labelling_targetEdge_some {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (labelling₀ : StableLengthMatrixLabelling base.gaugedData coordinate)
    (c : coordinate) :
    (labelling base hValid labelling₀).targetEdge (some c) =
      occurrenceEquiv target wall (validCandidate base hValid).right
        (some (labelling₀.targetEdge c)) := rfl

@[simp] theorem labelling_row {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (labelling₀ : StableLengthMatrixLabelling base.gaugedData coordinate)
    (path : StablePath (validCandidate base hValid).datum) :
    (labelling base hValid labelling₀).row path =
      (rowEquiv base hValid path).map labelling₀.row := by
  cases h : rowEquiv base hValid path <;> simp [labelling, h]

@[simp] theorem labelling_row_retained {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (labelling₀ : StableLengthMatrixLabelling base.gaugedData coordinate)
    (r : StablePath base.gaugedData) :
    (labelling base hValid labelling₀).row (retainedRow base hValid r) =
      some (labelling₀.row r) := by
  rw [labelling_row, rowEquiv_retainedRow]
  rfl

@[simp] theorem labelling_row_bridge {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (labelling₀ : StableLengthMatrixLabelling base.gaugedData coordinate) :
    (labelling base hValid labelling₀).row (bridgeRow base hValid) = none := by
  rw [labelling_row, rowEquiv_bridgeRow]
  rfl

/-! ## 10.  The row package

The payload of this file in one proposition, for a prescribed simple base.  At
an actual three-valent wall the anchor's `nd(A) = 4` and `DanglingCompatible`
are produced from the wall metric of a Part II open facet by
`NonTrivalentAnchorValency.threeBranchAnchor_of_single_row` and
`WallAdmissibility.danglingCompatible_of_contractionForest`. -/

section Incoming

open GraphContraction GluingContraction ContractionFibre ContractionRamification
open FullDimensionalSource WallDegeneration

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- The row-dictionary payload of this file, proved by `rowPackage`. -/
def RowPackage {targetGraph : CFGraph} {deg : ℕ} {w : targetGraph.V}
    {datum : GluingDatum targetGraph deg} {st : ThreeStar targetGraph w}
    {anc : WallBlock datum w} (simpleBase : SimpleBase datum st anc)
    (hValid : datum.Valid) : Prop :=
  (validCandidate simpleBase hValid).datum.Valid ∧
    genus (validCandidate simpleBase hValid).datum.sourceGraph =
      genus datum.sourceGraph ∧
    nonDanglingValency (validCandidate simpleBase hValid).datum
        (endpointVertex simpleBase hValid false simpleBase.hubSheet) = 3 ∧
    nonDanglingValency (validCandidate simpleBase hValid).datum
        (endpointVertex simpleBase hValid true simpleBase.deltaRepr) = 2 ∧
    nonDanglingValency (validCandidate simpleBase hValid).datum
        (endpointVertex simpleBase hValid true simpleBase.hubSheet) = 3 ∧
    (∀ r, rowEquiv simpleBase hValid (retainedRow simpleBase hValid r) = some r) ∧
    rowEquiv simpleBase hValid (bridgeRow simpleBase hValid) = none ∧
    rowEquiv simpleBase hValid
        (NonDanglingEdge.stablePath
          (⟨bridgeEdge simpleBase hValid simpleBase.deltaRepr,
            bridgeEdge_delta_survives simpleBase hValid⟩ :
              NonDanglingEdge (validCandidate simpleBase hValid).datum)) =
      some (NonDanglingEdge.stablePath
        (⟨deltaOccurrence simpleBase, deltaOccurrence_survives simpleBase hValid⟩ :
          NonDanglingEdge simpleBase.gaugedData))

theorem rowPackage {targetGraph : CFGraph} {deg : ℕ} {w : targetGraph.V}
    {datum : GluingDatum targetGraph deg} {st : ThreeStar targetGraph w}
    {anc : WallBlock datum w} (simpleBase : SimpleBase datum st anc)
    (hValid : datum.Valid) : RowPackage simpleBase hValid :=
  ⟨validCandidate_datum_valid simpleBase hValid,
    candidate_sourceGenus_incoming simpleBase hValid,
    nonDanglingValency_hubLeft simpleBase hValid,
    nonDanglingValency_deltaRight simpleBase hValid,
    nonDanglingValency_hubRight simpleBase hValid,
    fun r ↦ rowEquiv_retainedRow simpleBase hValid r,
    rowEquiv_bridgeRow simpleBase hValid,
    rowEquiv_bridgeDelta simpleBase hValid⟩

end Incoming

end DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRowEquiv
