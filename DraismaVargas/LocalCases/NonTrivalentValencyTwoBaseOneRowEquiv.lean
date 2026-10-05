module

public import DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRows

@[expose] public section

/-!
# The row dictionary of the valency-two **Base I** candidates

Source: Vargas, Part II (arXiv:2609.09109), Section 5.4, Configuration A of
Case {v2-nd4} (Case {v2-nd4-t3}), with Section 5.1 for the ordinary blocks, and
Draisma--Vargas Part I (arXiv:1909.12924), Case {w2-r2}, Base I.

`NonTrivalentValencyTwoBaseOneRows` proves the genus statement and the exact
endpoint census of `NonTrivalentValencyTwoBaseOne.validCandidate`.  This module
turns that census into the row dictionary
`StablePath (validCandidate setup).datum ≃ Option (StablePath data)` and the
honest stable length-matrix labelling over `Option coordinate`, and states the
whole package at an actual two-valent wall.

## Why Base I is simpler than Base II

At Base II (`NonTrivalentValencyTwoRowEquiv`) a surviving new occurrence may
*continue* an old row, so the reverse row map needs a witness bookkeeping
(`newWitness`, `ordSide`, `OrdinaryTrivalent`).  At Base I the only surviving
new occurrences are the two fold ones, and they form the bridge row alone:

* `NonTrivalentValencyTwoBaseOneRows.newSourceEdge_survives_iff` -- every other
  new occurrence dangles, its end above `u` being a singleton leaf;
* hence `rowOfEdge` is simply "the old row of a retained occurrence, `none`
  otherwise", and
* `ordinaryBlockDescent` is *trivial*: an ordinary block is neither split nor
  joined by a surviving new occurrence, so `retainedRow` is unconditional and
  no analogue of `OrdinaryTrivalent` is needed.

## What is proved

* `nonDanglingValency_anchor = 4`, read off Configuration A's `2 + 2`.
* `ordinaryBlockDescent`, `stablePath_retained_eq_of_consecutive`,
  `retainedRow`: the retained-row map, with `data.Valid` as its only
  hypothesis.
* `bridge_consecutive`, `bridgeRow`, `bridgeRow_foldSecond`: the single new
  stable row, `h_1 : A_1 -> F -> A_2`.
* `rowOfEdge`, `rowOfEdge_eq_of_consecutive`, `rowDescend`, `rowMap`,
  `rowEquiv`, `rowEquiv_retainedRow`, `rowEquiv_bridgeRow`.
* `retainedRow_ne_bridgeRow` and `bridgeRow_isolated`: the bridge row contains
  no retained occurrence, and consists of exactly the two fold occurrences.
* `labelling`: `StableLengthMatrixLabelling (validCandidate setup).datum
  (Option coordinate)`, with `Option.none` the vanishing coordinate re-used for
  the new target edge `t_1` and for the bridge row `h_1`.
* `rows_of_baseOneSetup`: the whole package over one wall datum.
* `exists_rowEquiv_of_wall_metric`: the same at an actual two-valent wall, with
  `nd(A) = 4` discharged from the wall metric through
  `NonTrivalentAnchorValency.twoBranchAnchor_of_single_row` and the Base I
  alignment produced by the gauge of `NonTrivalentValencyTwoGauge`
  (`NonTrivalentValencyTwoGauge.exists_gauged_candidate_of_contraction`).

## What is NOT proved here

* The `AgreeOffColumn` / entrywise common-minor identity of the outgoing
  labelled matrix against the incoming full-dimensional matrix is proved in
  `NonTrivalentValencyTwoBaseOneRowDictionary.agreeOffColumn_chartLabelling`,
  on the pattern of `NonTrivalentValencyTwoRowDictionary` and
  `NonTrivalentValencyFourRowDictionary` §4.
* Configuration A (`hSplit`) and the prescribed cross pairing with its two
  index equalities remain the caller's dispatch data in
  `exists_rowEquiv_of_wall_metric`; `data.Valid` (for the *gauged* datum, which
  is produced from the contraction) remains explicit in the wall-level
  statements.
* Nothing here constructs a `FullDimensionalSourcePresentation`, a
  `ContractionForest`, a star or the wall metric; Section 16 carries them.

## Consumers

The boundary dispatcher for Part II, Case {v2-nd4}
(`NonTrivalentValencyTwoDispatcher`), Configuration A, outgoing Types I and II.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRowEquiv

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
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOne
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRows
open DraismaVargas.LocalCases.W3R1SourceProfile (survivors mem_survivors card_survivors)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (setup : BaseOneSetup data star anchor)

local notation "cand" => (validCandidate setup)

/-! ## 10.  The retained-row descent, unconditionally -/

include setup in
/-- The anchor really has surviving valency four: Configuration A's `2 + 2`. -/
theorem nonDanglingValency_anchor :
    nonDanglingValency data (WallBlock.sourceVertex data wall anchor) = 4 := by
  classical
  have hSum := sum_card_directionSurvivors data star anchor
  rw [card_survivors, Fin.sum_univ_two, setup.split 0, setup.split 1] at hSum
  omega

/-- **`OrdinaryBlockDescent` is trivial at Base I.**  An ordinary wall block is
neither split nor joined by a surviving new occurrence, so two survivors
meeting at a divalent ordinary block still meet at one vertex of the outgoing
candidate. -/
theorem ordinaryBlockDescent (hValid : data.Valid)
    (first second : NonDanglingEdge data) (vertex : data.SourceVertex)
    (hAt : vertex.1.1 = wall)
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 vertex.1.2)
    (hNe : first ≠ second)
    (hFirst : Incident data first.1 vertex) (hSecond : Incident data second.1 vertex)
    (hValency : nonDanglingValency data vertex = 2) :
    Consecutive (cand).datum
      (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 first)
      (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 second) := by
  have hVertex : data.sourceEndpoint wall vertex.1.2 = vertex :=
    (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
  refine ⟨fun hEq ↦ hNe (ResolutionAwayFromWall.retainedEdge_injective (cand) hValid.1 hEq),
    branchVertex setup vertex.1.2, ?_, ?_, ?_⟩
  · refine (incident_oldSourceEdge_branchVertex_ordinary setup hX first.1).mpr ?_
    rw [hVertex]
    exact hFirst
  · refine (incident_oldSourceEdge_branchVertex_ordinary setup hX second.1).mpr ?_
    rw [hVertex]
    exact hSecond
  · rw [nonDanglingValency_branchVertex_ordinary setup hValid hX, hVertex]
    exact hValency

/-- Consecutive survivors of the wall datum stay on one stable row of the
outgoing candidate. -/
theorem stablePath_retained_eq_of_consecutive (hValid : data.Valid)
    {first second : NonDanglingEdge data} (h : Consecutive data first second) :
    (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 first).stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 second).stablePath := by
  obtain ⟨hNe, vertex, hFirst, hSecond, hValency⟩ := h
  by_cases hAt : vertex.1.1 = wall
  · by_cases hAnchorRel : (data.vertexPartition wall).Rel anchor.1 vertex.1.2
    · exfalso
      have hVertexAnchor : WallBlock.sourceVertex data wall anchor = vertex :=
        (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, hAnchorRel⟩
      rw [← hVertexAnchor, nonDanglingValency_anchor setup] at hValency
      omega
    · exact stablePath_eq_of_consecutive (ordinaryBlockDescent setup hValid first second
        vertex hAt hAnchorRel hNe hFirst hSecond hValency)
  · exact stablePath_eq_of_consecutive
      (ResolutionAwayFromWall.consecutive_retained_of_away (cand) hValid
        (candidate_sourceGenus setup) first second hNe vertex hAt hFirst hSecond hValency)

/-- **The retained-row map**, with `data.Valid` as its only hypothesis. -/
noncomputable def retainedRow (hValid : data.Valid) :
    StablePath data → StablePath (cand).datum :=
  Quot.lift
    (fun e ↦ (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 e).stablePath)
    (fun _ _ h ↦ stablePath_retained_eq_of_consecutive setup hValid h)

@[simp] theorem retainedRow_mk (hValid : data.Valid) (e : NonDanglingEdge data) :
    retainedRow setup hValid e.stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 e).stablePath := rfl

/-! ## 11.  The bridge row -/

/-- The two bridge occurrences are consecutive at the divalent fold. -/
theorem bridge_consecutive (hValid : data.Valid) :
    Consecutive (cand).datum
      ⟨(cand).newSourceEdge setup.foldFirst, newSourceEdge_foldFirst_survives setup hValid⟩
      ⟨(cand).newSourceEdge setup.foldSecond, newSourceEdge_foldSecond_survives setup hValid⟩ := by
  refine ⟨?_, leafVertex setup setup.foldFirst, ?_, ?_,
    nonDanglingValency_leafVertex_fold setup hValid⟩
  · intro hEq
    exact setup.foldFirst_ne_foldSecond
      ((newSourceEdge_eq_iff setup _ _).mp (congrArg Subtype.val hEq))
  · exact bridgeEdge_incident_leaf setup setup.foldFirst
  · rw [← leafVertex_fold_eq setup]
    exact bridgeEdge_incident_leaf setup setup.foldSecond

/-- **The one new stable row of the Base I candidate**: `h_1` runs
`A₁ → F → A₂`. -/
noncomputable def bridgeRow (hValid : data.Valid) : StablePath (cand).datum :=
  NonDanglingEdge.stablePath
    (⟨(cand).newSourceEdge setup.foldFirst,
      newSourceEdge_foldFirst_survives setup hValid⟩ : NonDanglingEdge (cand).datum)

theorem bridgeRow_foldSecond (hValid : data.Valid) :
    NonDanglingEdge.stablePath
        (⟨(cand).newSourceEdge setup.foldSecond,
          newSourceEdge_foldSecond_survives setup hValid⟩ :
          NonDanglingEdge (cand).datum) = bridgeRow setup hValid :=
  (stablePath_eq_of_consecutive (bridge_consecutive setup hValid)).symm

include setup in
/-- Every sheet of the anchor meets a `t₂`-survivor. -/
theorem exists_thickPartner {s : Fin degree}
    (hS : (data.vertexPartition wall).Rel anchor.1 s) :
    ∃ thick ∈ directionSurvivors data star anchor 0,
      (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thick) s := by
  rcases setup.cover hS with h | h
  · exact ⟨setup.firstOf 0, setup.firstOf_mem 0, h⟩
  · exact ⟨setup.secondOf 0, setup.secondOf_mem 0, h⟩

/-- **`nd = 3` at every vertex above the new branch point over the anchor.** -/
theorem nonDanglingValency_branchVertex_anchor_sheet (hValid : data.Valid)
    {s : Fin degree} (hS : (data.vertexPartition wall).Rel anchor.1 s) :
    nonDanglingValency (cand).datum (branchVertex setup s) = 3 := by
  obtain ⟨thick, hThick, hRel⟩ := exists_thickPartner setup hS
  obtain ⟨thin, hThin, hMeet⟩ := exists_thinPartner setup (occurrenceSheet_wall_rel thick)
  have hV : branchVertex setup s = branchVertex setup (occurrenceSheet thick) :=
    branchVertex_eq setup ((branchPartition_rel_anchor setup hS).mpr
      ((refineOnBlock_rel_iff (data.vertexPartition wall)
        (data.edgePartition (star.edge 0)) anchor.1 s (occurrenceSheet thick)
        (star.edgePartition_refines_wall data 0) hS).mpr hRel.symm))
  rw [hV]
  exact nonDanglingValency_branchVertex_anchor setup hValid hThick hThin hMeet.symm

/-! ## 12.  The reverse row map -/

/-- The wall datum's row carrying a surviving occurrence of the candidate, with
`none` for the bridge row.  At Base I every surviving new occurrence lies on the
bridge row, so no witness bookkeeping is needed. -/
noncomputable def rowOfEdge (hValid : data.Valid)
    (e : NonDanglingEdge (cand).datum) : Option (StablePath data) :=
  open Classical in
  if h : ∃ old : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old = e then
    some (Classical.choose h).stablePath
  else none

theorem rowOfEdge_pos (hValid : data.Valid) (e : NonDanglingEdge (cand).datum)
    (h : ∃ old : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old = e) :
    rowOfEdge setup hValid e = some (Classical.choose h).stablePath := by
  classical
  rw [rowOfEdge, dite_eq_left h]

theorem rowOfEdge_neg (hValid : data.Valid) (e : NonDanglingEdge (cand).datum)
    (h : ¬ ∃ old : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old = e) :
    rowOfEdge setup hValid e = none := by
  classical
  rw [rowOfEdge, dite_eq_right h]

theorem rowOfEdge_retained (hValid : data.Valid) (old : NonDanglingEdge data) :
    rowOfEdge setup hValid (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old) =
      some old.stablePath := by
  classical
  have h : ∃ o : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 o =
        ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old := ⟨old, rfl⟩
  rw [rowOfEdge_pos setup hValid _ h]
  exact congrArg (fun o : NonDanglingEdge data ↦ some o.stablePath)
    (ResolutionAwayFromWall.retainedEdge_injective (cand) hValid.1
      (Classical.choose_spec h))

theorem rowOfEdge_old (hValid : data.Valid) {old : data.SourceEdge}
    (hSurvives : ¬ IsDangling (cand).datum ((cand).oldSourceEdge old))
    (hData : ¬ IsDangling data old) :
    rowOfEdge setup hValid ⟨(cand).oldSourceEdge old, hSurvives⟩ =
      some (NonDanglingEdge.stablePath (⟨old, hData⟩ : NonDanglingEdge data)) :=
  rowOfEdge_retained setup hValid ⟨old, hData⟩

theorem rowOfEdge_new (hValid : data.Valid) {y : Fin degree}
    (hSurvives : ¬ IsDangling (cand).datum ((cand).newSourceEdge y)) :
    rowOfEdge setup hValid ⟨(cand).newSourceEdge y, hSurvives⟩ = none := by
  classical
  have hNot : ¬ ∃ old : NonDanglingEdge data,
      ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old =
        (⟨(cand).newSourceEdge y, hSurvives⟩ : NonDanglingEdge (cand).datum) := by
    rintro ⟨old, hEq⟩
    exact newSourceEdge_ne_oldSourceEdge setup y old.1 (congrArg Subtype.val hEq).symm
  exact rowOfEdge_neg setup hValid _ hNot

theorem rowOfEdge_eq_none_of_new (hValid : data.Valid) (e : NonDanglingEdge (cand).datum)
    {y : Fin degree} (hEq : e.1 = (cand).newSourceEdge y) :
    rowOfEdge setup hValid e = none := by
  refine rowOfEdge_neg setup hValid e ?_
  rintro ⟨old, hOld⟩
  have h := congrArg Subtype.val hOld
  rw [hEq] at h
  exact newSourceEdge_ne_oldSourceEdge setup y old.1 h.symm

theorem rowOfEdge_eq_of_retained (hValid : data.Valid) (e : NonDanglingEdge (cand).datum)
    {old : data.SourceEdge} (hEq : e.1 = (cand).oldSourceEdge old)
    (hData : ¬ IsDangling data old) :
    rowOfEdge setup hValid e =
      some (NonDanglingEdge.stablePath (⟨old, hData⟩ : NonDanglingEdge data)) := by
  have h : e = ResolutionAwayFromWall.retainedEdge (cand) hValid.1 ⟨old, hData⟩ :=
    Subtype.ext hEq
  rw [h, rowOfEdge_retained setup hValid ⟨old, hData⟩]

/-! ### The three geometric cases -/

theorem rowOfEdge_eq_away (hValid : data.Valid) {v : (cand).datum.SourceVertex}
    {place : target.V} (hAway : place ≠ wall) (hTarget : v.1.1 = oldVertex target place)
    {e f : NonDanglingEdge (cand).datum} (hNe : e ≠ f)
    (hE : Incident (cand).datum e.1 v) (hF : Incident (cand).datum f.1 v)
    (hValency : nonDanglingValency (cand).datum v = 2) :
    rowOfEdge setup hValid e = rowOfEdge setup hValid f := by
  obtain ⟨old, hOldTarget, hOldVertex⟩ :=
    ResolutionAwayFromWall.exists_retainedVertex_of_target (cand) v place hAway hTarget
  have hOldAway : old.1.1 ≠ wall := fun hEq ↦ hAway (hOldTarget.symm.trans hEq)
  subst hOldVertex
  rcases ResolutionAwayFromWall.nonDanglingEdge_cases (cand) hValid
    (candidate_sourceGenus setup) e with ⟨oe, rfl⟩ | ⟨sheet, hSheet, rfl⟩
  · rcases ResolutionAwayFromWall.nonDanglingEdge_cases (cand) hValid
      (candidate_sourceGenus setup) f with ⟨of, rfl⟩ | ⟨sheet, hSheet, rfl⟩
    · rw [rowOfEdge_retained setup hValid oe, rowOfEdge_retained setup hValid of]
      refine congrArg (fun r : StablePath data ↦ some r)
        (stablePath_eq_of_consecutive ⟨?_, old, ?_, ?_, ?_⟩)
      · exact fun hEq ↦ hNe (congrArg
          (ResolutionAwayFromWall.retainedEdge (cand) hValid.1) hEq)
      · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff (cand) old hOldAway oe.1).mp hE
      · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff (cand) old hOldAway of.1).mp hF
      · exact (ResolutionAwayFromWall.nonDanglingValency_retainedVertex (cand) hValid
          (candidate_sourceGenus setup) old hOldAway).symm.trans hValency
    · exact absurd hF
        (ResolutionAwayFromWall.not_incident_newSourceEdge (cand) old hOldAway sheet)
  · exact absurd hE
      (ResolutionAwayFromWall.not_incident_newSourceEdge (cand) old hOldAway sheet)

/-- At the leaf layer a divalent vertex is the fold, and both occurrences there
are bridge occurrences. -/
theorem rowOfEdge_eq_leaf (hValid : data.Valid) (x : Fin degree)
    {v : (cand).datum.SourceVertex} (hv : leafVertex setup x = v)
    {e f : NonDanglingEdge (cand).datum}
    (hE : Incident (cand).datum e.1 v) (hF : Incident (cand).datum f.1 v)
    (hValency : nonDanglingValency (cand).datum v = 2) :
    rowOfEdge setup hValid e = rowOfEdge setup hValid f := by
  classical
  subst hv
  have hFold : x = setup.foldFirst ∨ x = setup.foldSecond := by
    by_cases h1 : x = setup.foldFirst
    · exact Or.inl h1
    · by_cases h2 : x = setup.foldSecond
      · exact Or.inr h2
      · exfalso
        rw [nonDanglingValency_leafVertex_singleton setup hValid h1 h2] at hValency
        omega
  have hVertex : leafVertex setup x = leafVertex setup setup.foldFirst := by
    rcases hFold with rfl | rfl
    · rfl
    · exact leafVertex_fold_eq setup
  rw [hVertex] at hE hF
  have hEmem : e.1 ∈ nonDanglingIncident (cand).datum (leafVertex setup setup.foldFirst) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hE⟩
  have hFmem : f.1 ∈ nonDanglingIncident (cand).datum (leafVertex setup setup.foldFirst) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, hF⟩
  rw [nonDanglingIncident_leafVertex_fold setup hValid, Finset.mem_insert,
    Finset.mem_singleton] at hEmem hFmem
  have hEnone : rowOfEdge setup hValid e = none := by
    rcases hEmem with hCase | hCase
    · exact rowOfEdge_eq_none_of_new setup hValid e hCase
    · exact rowOfEdge_eq_none_of_new setup hValid e hCase
  have hFnone : rowOfEdge setup hValid f = none := by
    rcases hFmem with hCase | hCase
    · exact rowOfEdge_eq_none_of_new setup hValid f hCase
    · exact rowOfEdge_eq_none_of_new setup hValid f hCase
  rw [hEnone, hFnone]

/-- At the branch layer a divalent vertex lies over an ordinary block, and both
occurrences there are retained. -/
theorem rowOfEdge_eq_branch (hValid : data.Valid) (x : Fin degree)
    {v : (cand).datum.SourceVertex} (hv : branchVertex setup x = v)
    {e f : NonDanglingEdge (cand).datum} (hNe : e ≠ f)
    (hE : Incident (cand).datum e.1 v) (hF : Incident (cand).datum f.1 v)
    (hValency : nonDanglingValency (cand).datum v = 2) :
    rowOfEdge setup hValid e = rowOfEdge setup hValid f := by
  classical
  subst hv
  by_cases hX : (data.vertexPartition wall).Rel anchor.1 x
  · exfalso
    rw [nonDanglingValency_branchVertex_anchor_sheet setup hValid hX] at hValency
    omega
  · have hEmem : e.1 ∈ nonDanglingIncident (cand).datum (branchVertex setup x) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hE⟩
    have hFmem : f.1 ∈ nonDanglingIncident (cand).datum (branchVertex setup x) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, hF⟩
    rw [nonDanglingIncident_branchVertex_ordinary setup hValid hX] at hEmem hFmem
    obtain ⟨oe, hoe, hEq⟩ := Finset.mem_image.mp hEmem
    obtain ⟨of, hof, hFq⟩ := Finset.mem_image.mp hFmem
    obtain ⟨hoeSurv, hoeInc⟩ := (mem_nonDanglingIncident _ _ _).mp hoe
    obtain ⟨hofSurv, hofInc⟩ := (mem_nonDanglingIncident _ _ _).mp hof
    rw [rowOfEdge_eq_of_retained setup hValid e hEq.symm hoeSurv,
      rowOfEdge_eq_of_retained setup hValid f hFq.symm hofSurv]
    refine congrArg (fun r : StablePath data ↦ some r)
      (stablePath_eq_of_consecutive ⟨?_, data.sourceEndpoint wall x, hoeInc, hofInc, ?_⟩)
    · intro hEqSub
      refine hNe (Subtype.ext ?_)
      rw [← hEq, ← hFq]
      exact congrArg (cand).oldSourceEdge (congrArg Subtype.val hEqSub)
    · rw [← nonDanglingValency_branchVertex_ordinary setup hValid hX]
      exact hValency

/-- **The reverse row map descends to stable paths.** -/
theorem rowOfEdge_eq_of_consecutive (hValid : data.Valid)
    {e f : NonDanglingEdge (cand).datum} (h : Consecutive (cand).datum e f) :
    rowOfEdge setup hValid e = rowOfEdge setup hValid f := by
  obtain ⟨hNe, v, hE, hF, hValency⟩ := h
  cases hTarget : v.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · rw [hAt] at hTarget
        exact rowOfEdge_eq_leaf setup hValid v.1.2
          (((cand).datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨hTarget.symm, rfl⟩) hE hF hValency
      · exact rowOfEdge_eq_away setup hValid hAt hTarget hNe hE hF hValency
  | inr point =>
      cases point
      exact rowOfEdge_eq_branch setup hValid v.1.2
        (((cand).datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨hTarget.symm, rfl⟩) hNe hE hF hValency

/-! ## 13.  The row equivalence -/

/-- The reverse row map, on stable paths. -/
noncomputable def rowDescend (hValid : data.Valid) :
    StablePath (cand).datum → Option (StablePath data) :=
  Quot.lift (rowOfEdge setup hValid)
    (fun _ _ h ↦ rowOfEdge_eq_of_consecutive setup hValid h)

@[simp] theorem rowDescend_mk (hValid : data.Valid) (e : NonDanglingEdge (cand).datum) :
    rowDescend setup hValid e.stablePath = rowOfEdge setup hValid e := rfl

/-- The forward row map: the bridge row for `none`, the retained row for a row
of the incoming wall datum. -/
noncomputable def rowMap (hValid : data.Valid) :
    Option (StablePath data) → StablePath (cand).datum
  | none => bridgeRow setup hValid
  | some r => retainedRow setup hValid r

theorem rowDescend_bridgeRow (hValid : data.Valid) :
    rowDescend setup hValid (bridgeRow setup hValid) = none :=
  rowOfEdge_new setup hValid (newSourceEdge_foldFirst_survives setup hValid)

theorem rowDescend_retainedRow (hValid : data.Valid) (r : StablePath data) :
    rowDescend setup hValid (retainedRow setup hValid r) = some r := by
  induction r using Quot.inductionOn with
  | h e => exact rowOfEdge_retained setup hValid e

/-- **Every stable row of the Base I candidate is a retained row or the bridge
row.** -/
theorem rowMap_rowOfEdge (hValid : data.Valid) (e : NonDanglingEdge (cand).datum) :
    rowMap setup hValid (rowOfEdge setup hValid e) = e.stablePath := by
  rcases ResolutionAwayFromWall.nonDanglingEdge_cases (cand) hValid
    (candidate_sourceGenus setup) e with ⟨old, rfl⟩ | ⟨y, hSurv, rfl⟩
  · rw [rowOfEdge_retained setup hValid old]
    rfl
  · rw [rowOfEdge_new setup hValid hSurv]
    show bridgeRow setup hValid = _
    rcases (newSourceEdge_survives_iff setup hValid y).mp hSurv with hCase | hCase
    · subst hCase
      rfl
    · subst hCase
      exact (bridgeRow_foldSecond setup hValid).symm

/-- **The row dictionary of the valency-two Base I candidate.** -/
noncomputable def rowEquiv (hValid : data.Valid) :
    StablePath (cand).datum ≃ Option (StablePath data) where
  toFun := rowDescend setup hValid
  invFun := rowMap setup hValid
  left_inv := by
    intro path
    induction path using Quot.inductionOn with
    | h e => exact rowMap_rowOfEdge setup hValid e
  right_inv := by
    intro r
    cases r with
    | none => exact rowDescend_bridgeRow setup hValid
    | some r => exact rowDescend_retainedRow setup hValid r

@[simp] theorem rowEquiv_retainedRow (hValid : data.Valid) (r : StablePath data) :
    rowEquiv setup hValid (retainedRow setup hValid r) = some r :=
  rowDescend_retainedRow setup hValid r

@[simp] theorem rowEquiv_bridgeRow (hValid : data.Valid) :
    rowEquiv setup hValid (bridgeRow setup hValid) = none :=
  rowDescend_bridgeRow setup hValid

/-- **The bridge row carries no retained occurrence.** -/
theorem retainedRow_ne_bridgeRow (hValid : data.Valid) (r : StablePath data) :
    retainedRow setup hValid r ≠ bridgeRow setup hValid := by
  intro hEq
  have hImage := congrArg (rowDescend setup hValid) hEq
  rw [rowDescend_retainedRow setup hValid r, rowDescend_bridgeRow setup hValid] at hImage
  exact Option.some_ne_none r hImage

/-- **`bridgeRow` is exactly the two fold occurrences.**  The stable edge `h₁`
runs `A₁ → F → A₂` and stops: both its ends are trivalent. -/
theorem bridgeRow_isolated (hValid : data.Valid) (other : NonDanglingEdge (cand).datum)
    (hPath : other.stablePath = bridgeRow setup hValid) :
    other.1 = (cand).newSourceEdge setup.foldFirst ∨
      other.1 = (cand).newSourceEdge setup.foldSecond := by
  have hNone : rowOfEdge setup hValid other = none := by
    have hImage := congrArg (rowDescend setup hValid) hPath
    rw [rowDescend_mk setup hValid other, rowDescend_bridgeRow setup hValid] at hImage
    exact hImage
  rcases ResolutionAwayFromWall.nonDanglingEdge_cases (cand) hValid
    (candidate_sourceGenus setup) other with ⟨old, hOld⟩ | ⟨y, hSurv, hNew⟩
  · exfalso
    rw [hOld, rowOfEdge_retained setup hValid old] at hNone
    exact Option.some_ne_none old.stablePath hNone
  · have hVal : other.1 = (cand).newSourceEdge y := congrArg Subtype.val hNew
    rcases (newSourceEdge_survives_iff setup hValid y).mp hSurv with hCase | hCase
    · exact Or.inl (by rw [hVal, hCase])
    · exact Or.inr (by rw [hVal, hCase])

/-! ## 14.  The honest labelling over `Option coordinate` -/

/-- **The stable length-matrix labelling of the Base I candidate.**  The wall
datum's own square labelling supplies every retained row and column;
`Option.none` is the vanishing coordinate of the incoming chart, re-used for the
new target edge `t₁` and for the bridge row `h₁`. -/
noncomputable def labelling {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (labelling₀ : StableLengthMatrixLabelling data coordinate) :
    StableLengthMatrixLabelling (cand).datum (Option coordinate) where
  targetEdge := (Equiv.optionCongr labelling₀.targetEdge).trans
    (occurrenceEquiv target wall (cand).right)
  row := (rowEquiv setup hValid).trans (Equiv.optionCongr labelling₀.row)

@[simp] theorem labelling_targetEdge_none {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (labelling₀ : StableLengthMatrixLabelling data coordinate) :
    (labelling setup hValid labelling₀).targetEdge none =
      occurrenceEquiv target wall (cand).right none := rfl

@[simp] theorem labelling_targetEdge_some {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (labelling₀ : StableLengthMatrixLabelling data coordinate) (c : coordinate) :
    (labelling setup hValid labelling₀).targetEdge (some c) =
      occurrenceEquiv target wall (cand).right (some (labelling₀.targetEdge c)) := rfl

@[simp] theorem labelling_row_retained {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (labelling₀ : StableLengthMatrixLabelling data coordinate) (r : StablePath data) :
    (labelling setup hValid labelling₀).row (retainedRow setup hValid r) =
      some (labelling₀.row r) := by
  show (Equiv.optionCongr labelling₀.row) (rowEquiv setup hValid (retainedRow setup hValid r)) = _
  rw [rowEquiv_retainedRow setup hValid r]
  rfl

@[simp] theorem labelling_row_bridge {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (labelling₀ : StableLengthMatrixLabelling data coordinate) :
    (labelling setup hValid labelling₀).row (bridgeRow setup hValid) = none := by
  show (Equiv.optionCongr labelling₀.row) (rowEquiv setup hValid (bridgeRow setup hValid)) = _
  rw [rowEquiv_bridgeRow setup hValid]
  rfl

/-! ## 15.  The wall-level package -/

/-- **The complete Base I row package over one wall datum.**  Genus, the exact
endpoint census, and the row dictionary, with `data.Valid` as the only
hypothesis beyond `BaseOneSetup`. -/
theorem rows_of_baseOneSetup (hValid : data.Valid) :
    genus (cand).datum.sourceGraph = genus data.sourceGraph ∧
      (cand).datum.Valid ∧
      nonDanglingValency (cand).datum (leafVertex setup setup.foldFirst) = 2 ∧
      (∀ s, (data.vertexPartition wall).Rel anchor.1 s →
        nonDanglingValency (cand).datum (branchVertex setup s) = 3) ∧
      (∀ s, s ≠ setup.foldFirst → s ≠ setup.foldSecond →
        nonDanglingValency (cand).datum (leafVertex setup s) = 0) ∧
      (∀ x, ¬ (data.vertexPartition wall).Rel anchor.1 x →
        nonDanglingValency (cand).datum (branchVertex setup x) =
          nonDanglingValency data (data.sourceEndpoint wall x)) ∧
      (∀ r, rowEquiv setup hValid (retainedRow setup hValid r) = some r) ∧
      rowEquiv setup hValid (bridgeRow setup hValid) = none :=
  ⟨candidate_sourceGenus setup, validCandidate_datum_valid setup hValid,
    nonDanglingValency_leafVertex_fold setup hValid,
    fun _ hS ↦ nonDanglingValency_branchVertex_anchor_sheet setup hValid hS,
    fun _ h1 h2 ↦ nonDanglingValency_leafVertex_singleton setup hValid h1 h2,
    fun _ hX ↦ nonDanglingValency_branchVertex_ordinary setup hValid hX,
    fun r ↦ rowEquiv_retainedRow setup hValid r, rowEquiv_bridgeRow setup hValid⟩

/-! ## 16.  At an actual two-valent wall -/

section Incoming

open GraphContraction GluingContraction ContractionFibre ContractionRamification
open FullDimensionalSource WallDegeneration
open DraismaVargas.LocalCases.NonTrivalentValencyTwoGauge

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The valency-two Base I row dictionary at an actual two-valent wall.**
`nd(A) = 4` is discharged from the wall metric of the existence route through
`NonTrivalentAnchorValency.twoBranchAnchor_of_single_row`; the Base I alignment
is produced by the `t₃`-branch gauge of `NonTrivalentValencyTwoGauge` from the
two index equalities, so the caller's only
dispatch data are Configuration A (`hSplit`) and the prescribed cross pairing
with its index equalities. -/
theorem exists_rowEquiv_of_wall_metric
    (cover : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation cover coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest cover a b contracted)
    (hCompat : DanglingCompatible cover hc hab hOne)
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
    ∃ anchorBlock : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩,
      nonDanglingValency (contractDatum cover hc hab hOne)
          (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩
            anchorBlock) = 4 ∧
      ∀ (_ : ∀ label : Fin 2,
          (directionSurvivors (contractDatum cover hc hab hOne) wallStar anchorBlock
            label).card = 2)
        (thickFirst thickSecond thinFirst thinSecond :
          IncidentSourceEdge (contractDatum cover hc hab hOne)
            (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlock)),
        thickFirst ∈
            directionSurvivors (contractDatum cover hc hab hOne) wallStar anchorBlock 0 →
        thickSecond ∈
            directionSurvivors (contractDatum cover hc hab hOne) wallStar anchorBlock 0 →
        thinFirst ∈
            directionSurvivors (contractDatum cover hc hab hOne) wallStar anchorBlock 1 →
        thinSecond ∈
            directionSurvivors (contractDatum cover hc hab hOne) wallStar anchorBlock 1 →
        thickFirst ≠ thickSecond → thinFirst ≠ thinSecond →
        (contractDatum cover hc hab hOne).sourceEdgeIndex thickFirst.1 =
            (contractDatum cover hc hab hOne).sourceEdgeIndex thinFirst.1 →
        (contractDatum cover hc hab hOne).sourceEdgeIndex thickSecond.1 =
            (contractDatum cover hc hab hOne).sourceEdgeIndex thinSecond.1 →
        ∃ (gauged : BaseOneSetup
            (gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlock
              (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)) wallStar
            (gaugedAnchor (contractDatum cover hc hab hOne) wallStar anchorBlock
              (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)))
          (hGauged : (gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlock
            (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)).Valid),
          (validCandidate gauged).datum.Valid ∧
            genus (validCandidate gauged).datum.sourceGraph =
              genus (gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlock
                (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)).sourceGraph ∧
            nonDanglingValency (validCandidate gauged).datum
                (leafVertex gauged gauged.foldFirst) = 2 ∧
            (∀ s, ((gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlock
                (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)).vertexPartition
                  ⟨a, hab⟩).Rel
                (gaugedAnchor (contractDatum cover hc hab hOne) wallStar anchorBlock
                  (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)).1 s →
              nonDanglingValency (validCandidate gauged).datum
                (branchVertex gauged s) = 3) ∧
            (∀ r, rowEquiv gauged hGauged (retainedRow gauged hGauged r) = some r) ∧
            rowEquiv gauged hGauged (bridgeRow gauged hGauged) = none := by
  obtain ⟨anchorBlock, hNd, -⟩ :=
    NonTrivalentAnchorValency.twoBranchAnchor_of_single_row cover fd hc hab hOne hForest
      coordinates facet hRows hZeroCoord hPosCoord hFacetZero wallStar
  refine ⟨anchorBlock, hNd, ?_⟩
  intro hSplit thickFirst thickSecond thinFirst thinSecond hTF hTS hNF hNS hTNe hNNe
    hIndexFirst hIndexSecond
  obtain ⟨gauged, -⟩ := exists_gauged_candidate_of_contraction cover fd hc hab hOne hForest
    hCompat wallStar anchorBlock hNd hSplit thickFirst thickSecond thinFirst thinSecond
    hTF hTS hNF hNS hTNe hNNe hIndexFirst hIndexSecond
  have hGauged := gaugedData_valid (contractDatum cover hc hab hOne) wallStar anchorBlock
    (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)
    (valid_contractDatum cover hc hab hOne hForest fd.valid)
  exact ⟨gauged, hGauged, validCandidate_datum_valid gauged hGauged,
    candidate_sourceGenus gauged, nonDanglingValency_leafVertex_fold gauged hGauged,
    fun _ hS ↦ nonDanglingValency_branchVertex_anchor_sheet gauged hGauged hS,
    fun r ↦ rowEquiv_retainedRow gauged hGauged r, rowEquiv_bridgeRow gauged hGauged⟩

end Incoming

end DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRowEquiv
