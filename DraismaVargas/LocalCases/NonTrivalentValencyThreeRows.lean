import DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate
import DraismaVargas.LocalCases.NonTrivalentValencyFourRows
import DraismaVargas.LocalCases.NonTrivalentUniqueFourValent

/-!
# Stable rows of the prescribed candidate above a three-valent wall

Source: Vargas, Part II, arXiv:2609.09109, the valency-3 case (subsection `subsec-case-v3`, case
`{v3-nd4}`, base tree `T_2`), read through the labelling convention (1) of the
combinatorial setup (subsection `subsec-setup-determinants`): one edge of
`H^(q)` contracts to the anchor, it is `h_1^(q)`, its two endpoints are
`A_u^(q)` and `A_v^(q)`, and aside from `h_1^(q)` the edges of `H^(q)`
correspond bijectively to those of `H_0`.

This module builds the stable rows of
`NonTrivalentValencyThreeCandidate.Prescribed.validCandidate`.  It is the
valency-three counterpart of `NonTrivalentValencyFourRows` +
`NonTrivalentValencyFourDictionary`, and it is markedly shorter because the
valency-three candidate is built over the **unchanged** incoming datum: there is
no branch gauge, so none of the gauge transport of the four-valent case is
needed here.

## What is proved

* `candidate_sourceGenus`: the candidate preserves the source genus, with no
  further hypothesis.  Both resolutions in play -- the prescribed one at the anchor and the
  single global one on the rigid blocks -- are `ResolutionCoarseFine.fineResolution`,
  hence stars in the sense of `NonTrivalentValencyFourRows.IsStar`, whose API is
  reused verbatim.
* `endpointVertex`, `bridgeEdge` and their incidences, with the exact sizes on
  the outgoing datum: `|A_u| = k_2 + k_5` and `|A_v| = |A|`
  (`endpointVertex_blockCard`).
* `nonDanglingValency_endpointVertex`: **both** endpoint classes are trivalent,
  `nd(A_u) = nd(A_v) = 3`, with the exact surviving stars
  (`nonDanglingIncident_endpointVertex_false/true`): at `A_u` the bridge plus the
  two doubled-direction survivors, at `A_v` the bridge plus the two
  simple-direction survivors.  This is the paper's "two trivalent vertices
  joined by `h_1`" in the valency-three shape.
* `bridgeEdge_isolated`: the bridge is alone in its stable class, i.e. one new
  row.
* `retainedRow` modulo the named `OrdinaryBlockDescent`, and `labelling` over
  `Option coordinate` modulo a supplied row equivalence, exactly as in
  `NonTrivalentValencyFourDictionary`.

## What is not proved here

* `OrdinaryBlockDescent`: the retained-row descent across a *non-anchor* wall
  block of surviving valency two.  Stated as a named predicate, not assumed
  anywhere else; `NonTrivalentValencyThreeDescent.ordinaryBlockDescent` proves it.
* `rowEquiv`: the full row equivalence (`NonTrivalentValencyThreeRowEquiv.rowEquiv`);
  `retainedRow` is its retained half and `bridgeEdge_isolated` identifies the
  extra row.
* `AgreeOffColumn` against the incoming full-dimensional matrix.
* `nd(A) = 4` at the anchor is an explicit hypothesis here, through
  `ThreeBranchAnchor`; `NonTrivalentAnchorValency` proves it.

## Consumers

The boundary dispatcher for Part II case `{v3-nd4}`, and the nonsingularity and
exit statements built on `NonTrivalentLinkMatrix`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeRows

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
open DraismaVargas.LocalCases.NonTrivalentValencyFourRows (IsStar euler_of_isStar
  isStar_fineResolution)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

variable {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall}
  (source : ThreeBranchAnchor data star anchor)
  (hNoGlue : DanglingEdgeNoGlue data) (hValid : data.Valid)

local notation "cand" => (Prescribed.validCandidate source hNoGlue hValid)

/-! ## 1.  Both resolutions are stars, so the source genus is preserved -/

theorem isStar_selectedResolution :
    IsStar (data.vertexPartition wall) (Prescribed.selectedResolution source) :=
  isStar_fineResolution _ _ _

theorem isStar_ordinaryResolution :
    IsStar (data.vertexPartition wall) (Prescribed.ordinaryResolution source) :=
  isStar_fineResolution _ _ _

/-- Off the anchor block the candidate really uses the single global
background resolution of `Prescribed.subdivisionBackground`. -/
theorem candidate_resolution_of_not_wall_rel (block : Fin degree)
    (hBlock : ¬ (data.vertexPartition wall).Rel anchor.1 block) :
    (cand).resolution block = Prescribed.ordinaryResolution source := by
  unfold Prescribed.validCandidate Prescribed.candidate
    Prescribed.SubdivisionBackground.background
    GlobalM11Arbitrary.Background.install
  exact LocalResolution.onBlock_of_not_rel _ _ _ _ _ hBlock

theorem candidate_resolution_of_wall_rel (block : Fin degree)
    (hBlock : (data.vertexPartition wall).Rel anchor.1 block) :
    (cand).resolution block = Prescribed.selectedResolution source :=
  Prescribed.candidate_resolution_of_wall_rel source _ hNoGlue block hBlock

/-- **The valency-three candidate does not change the source genus.**  No
further hypothesis is needed: every wall block carries a `fineResolution`, hence a star,
and the blockwise Euler identity feeds
`M11SourceGenus.candidate_sourceGenus_of_blockwise_euler`. -/
theorem candidate_sourceGenus :
    genus (cand).datum.sourceGraph = genus data.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_blockwise_euler
  intro block _hCanonical
  by_cases hBlock : (data.vertexPartition wall).Rel anchor.1 block
  · rw [candidate_resolution_of_wall_rel source hNoGlue hValid block hBlock]
    exact euler_of_isStar (isStar_selectedResolution source) block
  · rw [candidate_resolution_of_not_wall_rel source hNoGlue hValid block hBlock]
    exact euler_of_isStar (isStar_ordinaryResolution source) block

/-! ## 2.  The two endpoint vertices and the bridge occurrence -/

/-- The endpoint partition on one side of the new target edge: the fine `A_u`
partition over the divalent end `u`, the whole old wall partition over the
trivalent end `v`. -/
noncomputable def endpointPartition (sideValue : Bool) : SheetPartition degree :=
  if sideValue then data.vertexPartition wall else Prescribed.finePartition source

@[simp] theorem endpointPartition_false :
    endpointPartition source false = Prescribed.finePartition source := rfl

@[simp] theorem endpointPartition_true :
    endpointPartition source true = data.vertexPartition wall := rfl

theorem selectedResolution_endpoint (sideValue : Bool) :
    (if sideValue then (Prescribed.selectedResolution source).right
      else (Prescribed.selectedResolution source).left) =
      endpointPartition source sideValue := by
  cases sideValue <;> rfl

theorem endpointPartition_refines (sideValue : Bool) :
    (endpointPartition source sideValue).Refines (data.vertexPartition wall) := by
  cases sideValue
  · exact Prescribed.finePartition_refines source
  · exact SheetPartition.Refines.refl _

/-- The prescribed side assignment really is the candidate's. -/
theorem candidate_right : (cand).right = Prescribed.rightAssignment source := rfl

theorem rep_wall_rel :
    (data.vertexPartition wall).Rel anchor.1
      (Prescribed.selectedRepresentative source) :=
  ((data.vertexPartition wall).mem_block_iff _ _).mp
    (Prescribed.selectedSheets_subset_wall source
      (Prescribed.selectedRepresentative_mem source))

/-- The actual outgoing source vertex on one side of the new target edge. -/
noncomputable def endpointVertex (sideValue : Bool) (sheet : Fin degree) :
    (cand).datum.SourceVertex :=
  (cand).datum.sourceEndpoint
    (if sideValue then freshVertex target else oldVertex target wall) sheet

/-- The new bridge occurrence `h_1` of the resolution. -/
noncomputable def bridgeEdge (sheet : Fin degree) : (cand).datum.SourceEdge :=
  (cand).newSourceEdge sheet

theorem sourceEnds_bridgeEdge (sheet : Fin degree) :
    (cand).datum.sourceEnds (bridgeEdge source hNoGlue hValid sheet) =
      (endpointVertex source hNoGlue hValid false sheet,
        endpointVertex source hNoGlue hValid true sheet) :=
  GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet

/-- The bridge joins the two endpoint vertices carried by its sheet. -/
theorem bridgeEdge_incident (sideValue : Bool) (sheet : Fin degree) :
    Incident (cand).datum (bridgeEdge source hNoGlue hValid sheet)
      (endpointVertex source hNoGlue hValid sideValue sheet) := by
  cases sideValue
  · exact Or.inl (congrArg Prod.fst
      (GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet))
  · exact Or.inr (congrArg Prod.snd
      (GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet))

/-- A retained old occurrence at the wall meets the endpoint vertex on the side
the base tree `T_2` assigns to its target occurrence. -/
theorem retainedEdge_incident (edge : target.edges)
    (hAt : edge ∈ GluingDatum.incidentEdges wall) (sideValue : Bool)
    (hSide : Prescribed.rightAssignment source edge = sideValue)
    (sheet : Fin degree) :
    Incident (cand).datum
      ((cand).oldSourceEdge (data.sourceEdge edge sheet))
      (endpointVertex source hNoGlue hValid sideValue sheet) := by
  cases sideValue
  · exact LimitChainCore.oldSourceEdge_incident_old _ edge hAt hSide sheet
  · exact M11SplitSurvival.oldSourceEdge_incident_fresh _ edge hAt hSide sheet

/-- **The exact endpoint sizes on the actual outgoing source vertices**:
`|A_u| = k_2 + k_5` over the divalent end and `|A_v| = |A|` over the trivalent
end. -/
theorem endpointVertex_blockCard (sideValue : Bool) :
    ((cand).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall)).blockCard
      (Prescribed.selectedRepresentative source) =
      if sideValue then (data.vertexPartition wall).blockCard anchor.1
      else ∑ edge ∈ directionSurvivors data star anchor (Prescribed.doubled source),
        data.sourceEdgeIndex edge.1 := by
  have hReprRel : (data.vertexPartition wall).Rel anchor.1
      ((data.vertexPartition wall).repr (Prescribed.selectedRepresentative source)) :=
    (rep_wall_rel source).trans
      ((data.vertexPartition wall).rel_repr_right _)
  rw [← Prescribed.candidate_endpoint_blockCard source
    (Prescribed.subdivisionBackground source hValid) hNoGlue sideValue,
    Prescribed.candidate_resolution_anchor source _ hNoGlue]
  cases sideValue
  · show ((cand).datum.vertexPartition (oldVertex target wall)).blockCard _ = _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
    rw [LocalResolution.paste_left_blockCard,
      candidate_resolution_of_wall_rel source hNoGlue hValid _ hReprRel]
    simp
  · show ((cand).datum.vertexPartition (freshVertex target)).blockCard _ = _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]
    rw [LocalResolution.paste_right_blockCard,
      candidate_resolution_of_wall_rel source hNoGlue hValid _ hReprRel]
    simp

/-- Inside the anchor block, two sheets name the same outgoing endpoint vertex
exactly when the endpoint partition of that side relates them. -/
theorem candidate_vertexPartition_rel_iff (sideValue : Bool) {a b : Fin degree}
    (hA : (data.vertexPartition wall).Rel anchor.1 a) :
    ((cand).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall)).Rel a b ↔
      (endpointPartition source sideValue).Rel a b := by
  have hReprRel : (data.vertexPartition wall).Rel anchor.1
      ((data.vertexPartition wall).repr a) :=
    hA.trans ((data.vertexPartition wall).rel_repr_right a)
  have hSelected := candidate_resolution_of_wall_rel source hNoGlue hValid _ hReprRel
  cases sideValue
  · show ((cand).datum.vertexPartition (oldVertex target wall)).Rel a b ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
    refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
      (fun blk ↦ ((cand).resolution blk).left)
      (fun blk ↦ ((cand).contracts blk).left_refines) a b) ?_
    rw [hSelected]
    rfl
  · show ((cand).datum.vertexPartition (freshVertex target)).Rel a b ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]
    refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
      (fun blk ↦ ((cand).resolution blk).right)
      (fun blk ↦ ((cand).contracts blk).right_refines) a b) ?_
    rw [hSelected]
    rfl

theorem endpointVertex_eq (sideValue : Bool) {a b : Fin degree}
    (hA : (data.vertexPartition wall).Rel anchor.1 a)
    (hRel : (endpointPartition source sideValue).Rel a b) :
    endpointVertex source hNoGlue hValid sideValue a =
      endpointVertex source hNoGlue hValid sideValue b := by
  apply (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr
  refine ⟨rfl, ?_⟩
  refine Eq.trans ?_ (((cand).datum.vertexPartition
    (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right b)
  exact (candidate_vertexPartition_rel_iff source hNoGlue hValid sideValue hA).mpr hRel

theorem candidate_endpointPartition_refines (sideValue : Bool) :
    ((cand).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall)).Refines
      (data.vertexPartition wall) := by
  cases sideValue
  · show ((cand).datum.vertexPartition (oldVertex target wall)).Refines _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
    exact LocalResolution.pasteLeft_refines (data.vertexPartition wall)
      (cand).resolution (cand).contracts
  · show ((cand).datum.vertexPartition (freshVertex target)).Refines _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]
    exact LocalResolution.pasteRight_refines (data.vertexPartition wall)
      (cand).resolution (cand).contracts

theorem mem_incidentEdges_endpoint_old (sideValue : Bool) (edge : target.edges) :
    occurrenceEquiv target wall (cand).right (some edge) ∈
        GluingDatum.incidentEdges
          (if sideValue then freshVertex target else oldVertex target wall) ↔
      (edge ∈ GluingDatum.incidentEdges wall ∧
        Prescribed.rightAssignment source edge = sideValue) := by
  rw [GluingContraction.mem_incidentEdges_iff, occurrenceEquiv_some,
    GluingContraction.mem_incidentEdges_iff]
  cases sideValue
  · exact oldEnds_incident_oldVertex_iff target wall (cand).right edge
  · exact oldEnds_incident_freshVertex_iff target wall (cand).right edge

theorem mem_incidentEdges_endpoint_new (sideValue : Bool) :
    occurrenceEquiv target wall (cand).right none ∈
      GluingDatum.incidentEdges
        (if sideValue then freshVertex target else oldVertex target wall) := by
  rw [GluingContraction.mem_incidentEdges_iff, occurrenceEquiv_none]
  cases sideValue
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## 3.  The four named survivors of the anchor -/

section Survivors

private theorem exists_simple_survivor (label : Fin 3)
    (hLabel : label ≠ Prescribed.doubled source) :
    ∃ edge, directionSurvivors data star anchor label = {edge} :=
  Finset.card_eq_one.mp (source.distribution.other_count label hLabel)

/-- The unique surviving occurrence of a simple target direction.  The `dite`
gives a harmless total value on the doubled direction, where there are two. -/
noncomputable def simpleSurvivor (label : Fin 3) :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  if hLabel : label ≠ Prescribed.doubled source then
    Classical.choose (exists_simple_survivor source label hLabel)
  else Prescribed.firstDoubled source

theorem directionSurvivors_simple_eq (label : Fin 3)
    (hLabel : label ≠ Prescribed.doubled source) :
    directionSurvivors data star anchor label = {simpleSurvivor source label} := by
  rw [simpleSurvivor, dif_pos hLabel]
  exact Classical.choose_spec (exists_simple_survivor source label hLabel)

theorem simpleSurvivor_mem (label : Fin 3)
    (hLabel : label ≠ Prescribed.doubled source) :
    simpleSurvivor source label ∈ directionSurvivors data star anchor label := by
  rw [directionSurvivors_simple_eq source label hLabel]
  exact Finset.mem_singleton_self _

/-- The literal source occurrence named by an incident survivor. -/
theorem sourceEdge_occurrenceSheet {label : Fin 3}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    data.sourceEdge (directionEdge star label)
        (Prescribed.occurrenceSheet edge) = edge.1 := by
  have hTarget : edge.1.1.1 = directionEdge star label :=
    ((mem_directionSurvivors data star anchor label edge).mp hEdge).2
  apply Subtype.ext
  apply Prod.ext
  · exact hTarget.symm
  · show (data.edgePartition (directionEdge star label)).repr
      (Prescribed.occurrenceSheet edge) = Prescribed.occurrenceSheet edge
    have hRepr := edge.1.2
    rw [hTarget] at hRepr
    exact hRepr

theorem survivor_not_isDangling {label : Fin 3}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    ¬ IsDangling data edge.1 :=
  (mem_survivors data anchor edge).mp
    ((mem_directionSurvivors data star anchor label edge).mp hEdge).1

/-- A surviving old occurrence of a named direction whose sheet lies in the
anchor block is one of that direction's survivors.  This takes the place of the
target-direction injectivity of the four-valent case: at a trivalent wall the
doubled direction genuinely carries two survivors. -/
theorem exists_directionSurvivor_eq
    (label : Fin 3) (old : data.SourceEdge)
    (hTarget : old.1.1 = directionEdge star label)
    (hWall : (data.vertexPartition wall).Rel anchor.1 old.1.2)
    (hSurvives : ¬ IsDangling data old) :
    ∃ edge ∈ directionSurvivors data star anchor label, edge.1 = old := by
  have hIncident : Incident data old (WallBlock.sourceVertex data wall anchor) := by
    refine (incident_wallBlock_sourceVertex_iff data anchor old).mpr
      ⟨hTarget ▸ directionEdge_mem_incidentEdges star label, ?_⟩
    apply Subtype.ext
    change (data.vertexPartition wall).repr old.1.2 = anchor.1
    unfold SheetPartition.Rel at hWall
    rw [← hWall, anchor.2]
  refine ⟨⟨old, hIncident⟩, ?_, rfl⟩
  exact (mem_directionSurvivors data star anchor label _).mpr
    ⟨(mem_survivors data anchor _).mpr hSurvives, hTarget⟩

end Survivors

/-! ## 4.  The retained survivors at the two endpoint vertices -/

local notation "rep" => (Prescribed.selectedRepresentative source)

theorem doubled_occurrenceSheet_mem {edge :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor (Prescribed.doubled source)) :
    Prescribed.occurrenceSheet edge ∈ Prescribed.selectedSheets source := by
  rw [Prescribed.directionSurvivors_doubled_eq_pair source, Finset.mem_insert,
    Finset.mem_singleton] at hEdge
  rcases hEdge with rfl | rfl
  · exact Finset.mem_union_left _
      ((data.edgePartition (Prescribed.doubledEdge source)).self_mem_block _)
  · exact Finset.mem_union_right _
      ((data.edgePartition (Prescribed.doubledEdge source)).self_mem_block _)

/-- A doubled-direction survivor sits in the new bridge class, so its retained
occurrence meets the divalent endpoint `A_u` carried by the representative. -/
theorem endpointPartition_rel_doubled {edge :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor (Prescribed.doubled source)) :
    (endpointPartition source false).Rel rep (Prescribed.occurrenceSheet edge) := by
  show (Prescribed.finePartition source).Rel rep (Prescribed.occurrenceSheet edge)
  rw [← (Prescribed.finePartition source).mem_block_iff,
    Prescribed.finePartition_selected_block source]
  exact doubled_occurrenceSheet_mem source hEdge

/-- A simple-direction survivor lies in the old wall block, which is the whole
trivalent endpoint `A_v`. -/
theorem endpointPartition_rel_wall {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (endpointPartition source true).Rel rep sheet :=
  (rep_wall_rel source).symm.trans hSheet

theorem retained_survivor_survives {label : Fin 3}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    ¬ IsDangling (cand).datum ((cand).oldSourceEdge edge.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ hValid.1 _
    (survivor_not_isDangling hEdge)

theorem retained_survivor_incident (sideValue : Bool) {label : Fin 3}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label)
    (hSide : Prescribed.rightAssignment source (directionEdge star label) = sideValue)
    (hRel : (endpointPartition source sideValue).Rel rep
      (Prescribed.occurrenceSheet edge)) :
    Incident (cand).datum ((cand).oldSourceEdge edge.1)
      (endpointVertex source hNoGlue hValid sideValue rep) := by
  rw [← sourceEdge_occurrenceSheet hEdge,
    endpointVertex_eq source hNoGlue hValid sideValue (rep_wall_rel source) hRel]
  exact retainedEdge_incident source hNoGlue hValid (directionEdge star label)
    (directionEdge_mem_incidentEdges star label) sideValue hSide
    (Prescribed.occurrenceSheet edge)

theorem rightAssignment_doubledDirection :
    Prescribed.rightAssignment source
      (directionEdge star (Prescribed.doubled source)) = false :=
  Prescribed.rightAssignment_doubled source

theorem rightAssignment_firstSimple :
    Prescribed.rightAssignment source
      (directionEdge star (Prescribed.firstSimple source)) = true :=
  Prescribed.rightAssignment_of_ne source
    (Prescribed.directionEdge_firstSimple_ne source)

theorem rightAssignment_secondSimple :
    Prescribed.rightAssignment source
      (directionEdge star (Prescribed.secondSimple source)) = true :=
  Prescribed.rightAssignment_of_ne source
    (Prescribed.directionEdge_secondSimple_ne source)

/-- The two retained occurrences that certify `A_u` and `A_v` are nonempty. -/
theorem nonDanglingValency_endpointVertex_ne_zero (sideValue : Bool) :
    nonDanglingValency (cand).datum
      (endpointVertex source hNoGlue hValid sideValue rep) ≠ 0 := by
  cases sideValue
  · exact ClassInjectivity.nonDanglingValency_ne_zero_of_incident _
      (retained_survivor_survives source hNoGlue hValid
        (Prescribed.firstDoubled_mem source))
      (retained_survivor_incident source hNoGlue hValid false
        (Prescribed.firstDoubled_mem source)
        (rightAssignment_doubledDirection source)
        (endpointPartition_rel_doubled source (Prescribed.firstDoubled_mem source)))
  · exact ClassInjectivity.nonDanglingValency_ne_zero_of_incident _
      (retained_survivor_survives source hNoGlue hValid
        (simpleSurvivor_mem source (Prescribed.firstSimple source)
          (Prescribed.firstSimple_ne source)))
      (retained_survivor_incident source hNoGlue hValid true
        (simpleSurvivor_mem source (Prescribed.firstSimple source)
          (Prescribed.firstSimple_ne source))
        (rightAssignment_firstSimple source)
        (endpointPartition_rel_wall source
          (Prescribed.occurrenceSheet_wall_rel _)))

/-- **The bridge `h_1` survives.**  Both of its endpoint vertices already carry
a retained survivor, so neither can lie on a dangling side. -/
theorem bridgeEdge_survives :
    ¬ IsDangling (cand).datum (bridgeEdge source hNoGlue hValid rep) := by
  have hEnds := sourceEnds_bridgeEdge source hNoGlue hValid rep
  intro hDangling
  rcases hDangling with hSide | hSide
  · obtain ⟨cut⟩ := hSide
    apply nonDanglingValency_endpointVertex_ne_zero source hNoGlue hValid false
    have hFst := congrArg Prod.fst hEnds
    have hZero := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side
      _ cut cut.left_mem
    rwa [hFst] at hZero
  · obtain ⟨cut⟩ := hSide
    apply nonDanglingValency_endpointVertex_ne_zero source hNoGlue hValid true
    have hSnd := congrArg Prod.snd hEnds
    have hZero := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side
      _ cut cut.left_mem
    rwa [hSnd] at hZero

/-! ## 5.  Exhaustion: what else can meet an endpoint vertex -/

theorem endpointPartition_rel_of_incident (sideValue : Bool) {t : Fin degree}
    (hT : (data.vertexPartition wall).Rel anchor.1 t)
    {e : (cand).datum.SourceEdge}
    (hIncident : Incident (cand).datum e
      (endpointVertex source hNoGlue hValid sideValue t)) :
    (endpointPartition source sideValue).Rel t e.1.2 := by
  rw [incident_iff_target_mem_and_rel] at hIncident
  refine (candidate_vertexPartition_rel_iff source hNoGlue hValid sideValue hT).mp ?_
  exact Eq.trans
    (((cand).datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right t)
    hIncident.2

theorem right_eq_of_incident_old (sideValue : Bool) {t : Fin degree}
    {old : data.SourceEdge}
    (hIncident : Incident (cand).datum ((cand).oldSourceEdge old)
      (endpointVertex source hNoGlue hValid sideValue t)) :
    old.1.1 ∈ GluingDatum.incidentEdges wall ∧
      Prescribed.rightAssignment source old.1.1 = sideValue := by
  rw [incident_iff_target_mem_and_rel] at hIncident
  have hTargetMem := hIncident.1
  rw [BalancedGlobal.Candidate.oldSourceEdge_target] at hTargetMem
  exact (mem_incidentEdges_endpoint_old source hNoGlue hValid sideValue
    old.1.1).mp hTargetMem

theorem newSourceEdge_eq_of_rel {a b : Fin degree}
    (h : (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
      (cand).contracts).newEdge.Rel a b) :
    (cand).newSourceEdge a = (cand).newSourceEdge b := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact h

theorem newEdge_rel_iff_finePartition {a b : Fin degree}
    (hA : (data.vertexPartition wall).Rel anchor.1 a) :
    (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.Rel a b ↔
      (Prescribed.finePartition source).Rel a b := by
  have hReprRel : (data.vertexPartition wall).Rel anchor.1
      ((data.vertexPartition wall).repr a) :=
    hA.trans ((data.vertexPartition wall).rel_repr_right a)
  have hSelected := candidate_resolution_of_wall_rel source hNoGlue hValid _ hReprRel
  refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
    (fun blk ↦ ((cand).resolution blk).newEdge)
    (fun blk ↦ ((cand).resolution blk).edge_refines_left.trans
      ((cand).contracts blk).left_refines) a b) ?_
  rw [hSelected]
  rfl

/-- A surviving retained occurrence over the doubled direction at the anchor is
one of the two doubled survivors. -/
theorem eq_doubledSurvivor_of_old {old : data.SourceEdge}
    (hTarget : old.1.1 = Prescribed.doubledEdge source)
    (hWall : (data.vertexPartition wall).Rel anchor.1 old.1.2)
    (hSurvives : ¬ IsDangling data old) :
    old = (Prescribed.firstDoubled source).1 ∨
      old = (Prescribed.secondDoubled source).1 := by
  classical
  obtain ⟨edge, hEdge, rfl⟩ := exists_directionSurvivor_eq (Prescribed.doubled source)
    old hTarget hWall hSurvives
  rw [Prescribed.directionSurvivors_doubled_eq_pair source, Finset.mem_insert,
    Finset.mem_singleton] at hEdge
  rcases hEdge with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A surviving retained occurrence over a simple direction at the anchor is
that direction's unique survivor. -/
theorem eq_simpleSurvivor_of_old {label : Fin 3}
    (hLabel : label ≠ Prescribed.doubled source) {old : data.SourceEdge}
    (hTarget : old.1.1 = directionEdge star label)
    (hWall : (data.vertexPartition wall).Rel anchor.1 old.1.2)
    (hSurvives : ¬ IsDangling data old) :
    old = (simpleSurvivor source label).1 := by
  classical
  obtain ⟨edge, hEdge, rfl⟩ := exists_directionSurvivor_eq label old hTarget hWall
    hSurvives
  rw [directionSurvivors_simple_eq source label hLabel, Finset.mem_singleton]
    at hEdge
  rw [hEdge]

/-- The two occurrences the base tree `T_2` assigns to the trivalent end. -/
theorem target_eq_simple_of_rightAssignment {edge : target.edges}
    (hAt : edge ∈ GluingDatum.incidentEdges wall)
    (hSide : Prescribed.rightAssignment source edge = true) :
    edge = directionEdge star (Prescribed.firstSimple source) ∨
      edge = directionEdge star (Prescribed.secondSimple source) := by
  classical
  rw [Prescribed.incidentEdges_eq_triple source, Finset.mem_insert,
    Finset.mem_insert, Finset.mem_singleton] at hAt
  rcases hAt with rfl | hAt | hAt
  · rw [Prescribed.rightAssignment_doubled source] at hSide
    exact absurd hSide (by simp)
  · exact Or.inl hAt
  · exact Or.inr hAt

/-- A new occurrence on a singleton fine block carries an endpoint vertex with
nothing else on it, so it is dangling. -/
theorem nonDanglingIncident_singleton_subset {u : Fin degree}
    (hWall : (data.vertexPartition wall).Rel anchor.1 u)
    (hSingleton : (Prescribed.finePartition source).block u = {u})
    (hNotRel : ¬ (Prescribed.finePartition source).Rel rep u) :
    nonDanglingIncident (cand).datum
        (endpointVertex source hNoGlue hValid false u) ⊆
      {(cand).newSourceEdge u} := by
  classical
  intro f hf
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hf
  have hRelf : (Prescribed.finePartition source).Rel u f.1.2 :=
    endpointPartition_rel_of_incident source hNoGlue hValid false hWall hIncident
  have hEqSheet : f.1.2 = u := by
    have hMem : f.1.2 ∈ (Prescribed.finePartition source).block u :=
      ((Prescribed.finePartition source).mem_block_iff u f.1.2).mpr hRelf
    rw [hSingleton] at hMem
    simpa using hMem
  rcases ResolutionPruning.sourceEdge_cases (cand) f with ⟨old, rfl⟩ | ⟨s, rfl⟩
  · exfalso
    obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old source hNoGlue hValid false
      hIncident
    have hTarget : old.1.1 = Prescribed.doubledEdge source :=
      (Prescribed.rightAssignment_eq_false_iff source old.1.1).mp hSide
    have hOldSheet : old.1.2 = u := hEqSheet
    have hOldSurv : ¬ IsDangling data old := fun h ↦ hSurvives
      ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand) hValid
        (candidate_sourceGenus source hNoGlue hValid) old).mpr h)
    have hBlockRel : (data.vertexPartition wall).Rel anchor.1 old.1.2 :=
      hOldSheet ▸ hWall
    apply hNotRel
    refine ((Prescribed.finePartition source).mem_block_iff rep u).mp ?_
    rw [Prescribed.finePartition_selected_block source, ← hOldSheet]
    rcases eq_doubledSurvivor_of_old source hTarget hBlockRel hOldSurv with
      hEq | hEq
    · rw [hEq]
      exact doubled_occurrenceSheet_mem source (Prescribed.firstDoubled_mem source)
    · rw [hEq]
      exact doubled_occurrenceSheet_mem source (Prescribed.secondDoubled_mem source)
  · have hRepr : (LocalResolution.paste (data.vertexPartition wall)
        (cand).resolution (cand).contracts).newEdge.repr s = u := hEqSheet
    have hEq : (cand).newSourceEdge s = (cand).newSourceEdge u := by
      apply newSourceEdge_eq_of_rel
      show (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.repr s =
          (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
            (cand).contracts).newEdge.repr u
      rw [← hRepr, (LocalResolution.paste (data.vertexPartition wall)
        (cand).resolution (cand).contracts).newEdge.repr_idem]
    rw [hEq]
    exact Finset.mem_singleton_self _

theorem newSourceEdge_isDangling_of_singleton {u : Fin degree}
    (hWall : (data.vertexPartition wall).Rel anchor.1 u)
    (hSingleton : (Prescribed.finePartition source).block u = {u})
    (hNotRel : ¬ (Prescribed.finePartition source).Rel rep u) :
    IsDangling (cand).datum ((cand).newSourceEdge u) := by
  classical
  by_contra hSurvives
  have hIncident := bridgeEdge_incident source hNoGlue hValid false u
  have hCard := Finset.card_le_card
    (nonDanglingIncident_singleton_subset source hNoGlue hValid hWall hSingleton
      hNotRel)
  rw [card_nonDanglingIncident, Finset.card_singleton] at hCard
  have hNe := NonDanglingValency.nonDanglingValency_ne_one (cand).datum
    ((cand).datum_valid hValid).1
    (endpointVertex source hNoGlue hValid false u)
  have hPos := ClassInjectivity.nonDanglingValency_ne_zero_of_incident
    (cand).datum hSurvives hIncident
  omega

/-! ## 6.  The exact surviving star at each endpoint -/

theorem newSourceEdge_eq_bridge_of_rel {s : Fin degree}
    (hRel : (Prescribed.finePartition source).Rel rep
      ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.repr s)) :
    (cand).newSourceEdge s = bridgeEdge source hNoGlue hValid rep := by
  have hEqU : (cand).newSourceEdge s =
      (cand).newSourceEdge ((LocalResolution.paste (data.vertexPartition wall)
        (cand).resolution (cand).contracts).newEdge.repr s) := by
    apply newSourceEdge_eq_of_rel
    show (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
      (cand).contracts).newEdge.repr s =
        (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
          (cand).contracts).newEdge.repr
            ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
              (cand).contracts).newEdge.repr s)
    rw [(LocalResolution.paste (data.vertexPartition wall) (cand).resolution
      (cand).contracts).newEdge.repr_idem]
  rw [hEqU]
  exact (newSourceEdge_eq_of_rel source hNoGlue hValid
    ((newEdge_rel_iff_finePartition source hNoGlue hValid
      (rep_wall_rel source)).mpr hRel)).symm

/-- **The surviving star at the divalent endpoint `A_u`**: only the bridge and
the two doubled-direction survivors. -/
theorem nonDanglingIncident_endpointVertex_false_subset :
    nonDanglingIncident (cand).datum
        (endpointVertex source hNoGlue hValid false rep) ⊆
      {bridgeEdge source hNoGlue hValid rep,
        (cand).oldSourceEdge (Prescribed.firstDoubled source).1,
        (cand).oldSourceEdge (Prescribed.secondDoubled source).1} := by
  classical
  intro e he
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp he
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, rfl⟩ | ⟨s, rfl⟩
  · obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old source hNoGlue hValid false
      hIncident
    have hTarget : old.1.1 = Prescribed.doubledEdge source :=
      (Prescribed.rightAssignment_eq_false_iff source old.1.1).mp hSide
    have hRel := endpointPartition_rel_of_incident source hNoGlue hValid false
      (rep_wall_rel source) hIncident
    have hWallRel : (data.vertexPartition wall).Rel anchor.1 old.1.2 :=
      (rep_wall_rel source).trans
        ((endpointPartition_refines source false).rel hRel)
    have hOldSurv : ¬ IsDangling data old := fun h ↦ hSurvives
      ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand) hValid
        (candidate_sourceGenus source hNoGlue hValid) old).mpr h)
    rcases eq_doubledSurvivor_of_old source hTarget hWallRel hOldSurv with
      hEq | hEq
    · exact Or.inr (Or.inl (congrArg (cand).oldSourceEdge hEq))
    · exact Or.inr (Or.inr (congrArg (cand).oldSourceEdge hEq))
  · left
    exact newSourceEdge_eq_bridge_of_rel source hNoGlue hValid
      (endpointPartition_rel_of_incident source hNoGlue hValid false
        (rep_wall_rel source) hIncident)

/-- **The surviving star at the trivalent endpoint `A_v`**: only the bridge and
the two simple-direction survivors. -/
theorem nonDanglingIncident_endpointVertex_true_subset :
    nonDanglingIncident (cand).datum
        (endpointVertex source hNoGlue hValid true rep) ⊆
      {bridgeEdge source hNoGlue hValid rep,
        (cand).oldSourceEdge (simpleSurvivor source (Prescribed.firstSimple source)).1,
        (cand).oldSourceEdge (simpleSurvivor source (Prescribed.secondSimple source)).1} := by
  classical
  intro e he
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp he
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, rfl⟩ | ⟨s, rfl⟩
  · obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old source hNoGlue hValid true
      hIncident
    have hRel := endpointPartition_rel_of_incident source hNoGlue hValid true
      (rep_wall_rel source) hIncident
    have hWallRel : (data.vertexPartition wall).Rel anchor.1 old.1.2 :=
      (rep_wall_rel source).trans
        ((endpointPartition_refines source true).rel hRel)
    have hOldSurv : ¬ IsDangling data old := fun h ↦ hSurvives
      ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand) hValid
        (candidate_sourceGenus source hNoGlue hValid) old).mpr h)
    rcases target_eq_simple_of_rightAssignment source hAt hSide with hEdge | hEdge
    · exact Or.inr (Or.inl (congrArg (cand).oldSourceEdge
        (eq_simpleSurvivor_of_old source (Prescribed.firstSimple_ne source)
          hEdge hWallRel hOldSurv)))
    · exact Or.inr (Or.inr (congrArg (cand).oldSourceEdge
        (eq_simpleSurvivor_of_old source (Prescribed.secondSimple_ne source)
          hEdge hWallRel hOldSurv)))
  · left
    set u := (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
      (cand).contracts).newEdge.repr s with hu
    have hRel := endpointPartition_rel_of_incident source hNoGlue hValid true
      (rep_wall_rel source) hIncident
    have hWallRel : (data.vertexPartition wall).Rel anchor.1 u :=
      (rep_wall_rel source).trans
        ((endpointPartition_refines source true).rel hRel)
    by_cases hR : (Prescribed.finePartition source).Rel rep u
    · exact newSourceEdge_eq_bridge_of_rel source hNoGlue hValid hR
    · exfalso
      rcases Prescribed.finePartition_rel_or_singleton source u hWallRel with
        hFine | hSing
      · exact hR hFine
      · refine hSurvives ?_
        have hEqU : (cand).newSourceEdge s = (cand).newSourceEdge u := by
          apply newSourceEdge_eq_of_rel
          show (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
            (cand).contracts).newEdge.repr s =
              (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
                (cand).contracts).newEdge.repr u
          rw [hu, (LocalResolution.paste (data.vertexPartition wall)
            (cand).resolution (cand).contracts).newEdge.repr_idem]
        rw [hEqU]
        exact newSourceEdge_isDangling_of_singleton source hNoGlue hValid
          hWallRel hSing hR

theorem bridge_ne_retained (old : data.SourceEdge) :
    bridgeEdge source hNoGlue hValid rep ≠ (cand).oldSourceEdge old := by
  intro hEq
  have h := congrArg (fun edge : (cand).datum.SourceEdge ↦ edge.1.1) hEq
  have hNone := (occurrenceEquiv target wall (cand).right).injective h
  cases hNone

theorem triple_subset_nonDanglingIncident_false :
    ({bridgeEdge source hNoGlue hValid rep,
        (cand).oldSourceEdge (Prescribed.firstDoubled source).1,
        (cand).oldSourceEdge (Prescribed.secondDoubled source).1} :
          Finset (cand).datum.SourceEdge) ⊆
      nonDanglingIncident (cand).datum
        (endpointVertex source hNoGlue hValid false rep) := by
  classical
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨bridgeEdge_survives source hNoGlue hValid,
        bridgeEdge_incident source hNoGlue hValid false rep⟩
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨retained_survivor_survives source hNoGlue hValid
          (Prescribed.firstDoubled_mem source),
        retained_survivor_incident source hNoGlue hValid false
          (Prescribed.firstDoubled_mem source)
          (rightAssignment_doubledDirection source)
          (endpointPartition_rel_doubled source (Prescribed.firstDoubled_mem source))⟩
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨retained_survivor_survives source hNoGlue hValid
          (Prescribed.secondDoubled_mem source),
        retained_survivor_incident source hNoGlue hValid false
          (Prescribed.secondDoubled_mem source)
          (rightAssignment_doubledDirection source)
          (endpointPartition_rel_doubled source (Prescribed.secondDoubled_mem source))⟩

theorem triple_subset_nonDanglingIncident_true :
    ({bridgeEdge source hNoGlue hValid rep,
        (cand).oldSourceEdge (simpleSurvivor source (Prescribed.firstSimple source)).1,
        (cand).oldSourceEdge (simpleSurvivor source (Prescribed.secondSimple source)).1} :
          Finset (cand).datum.SourceEdge) ⊆
      nonDanglingIncident (cand).datum
        (endpointVertex source hNoGlue hValid true rep) := by
  classical
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨bridgeEdge_survives source hNoGlue hValid,
        bridgeEdge_incident source hNoGlue hValid true rep⟩
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨retained_survivor_survives source hNoGlue hValid
          (simpleSurvivor_mem source _ (Prescribed.firstSimple_ne source)),
        retained_survivor_incident source hNoGlue hValid true
          (simpleSurvivor_mem source _ (Prescribed.firstSimple_ne source))
          (rightAssignment_firstSimple source)
          (endpointPartition_rel_wall source
            (Prescribed.occurrenceSheet_wall_rel _))⟩
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨retained_survivor_survives source hNoGlue hValid
          (simpleSurvivor_mem source _ (Prescribed.secondSimple_ne source)),
        retained_survivor_incident source hNoGlue hValid true
          (simpleSurvivor_mem source _ (Prescribed.secondSimple_ne source))
          (rightAssignment_secondSimple source)
          (endpointPartition_rel_wall source
            (Prescribed.occurrenceSheet_wall_rel _))⟩

theorem nonDanglingIncident_endpointVertex_false :
    nonDanglingIncident (cand).datum
        (endpointVertex source hNoGlue hValid false rep) =
      {bridgeEdge source hNoGlue hValid rep,
        (cand).oldSourceEdge (Prescribed.firstDoubled source).1,
        (cand).oldSourceEdge (Prescribed.secondDoubled source).1} :=
  Finset.Subset.antisymm
    (nonDanglingIncident_endpointVertex_false_subset source hNoGlue hValid)
    (triple_subset_nonDanglingIncident_false source hNoGlue hValid)

theorem nonDanglingIncident_endpointVertex_true :
    nonDanglingIncident (cand).datum
        (endpointVertex source hNoGlue hValid true rep) =
      {bridgeEdge source hNoGlue hValid rep,
        (cand).oldSourceEdge (simpleSurvivor source (Prescribed.firstSimple source)).1,
        (cand).oldSourceEdge (simpleSurvivor source (Prescribed.secondSimple source)).1} :=
  Finset.Subset.antisymm
    (nonDanglingIncident_endpointVertex_true_subset source hNoGlue hValid)
    (triple_subset_nonDanglingIncident_true source hNoGlue hValid)

theorem firstDoubled_val_ne :
    (Prescribed.firstDoubled source).1 ≠ (Prescribed.secondDoubled source).1 :=
  fun hEq ↦ Prescribed.firstDoubled_ne_secondDoubled source (Subtype.ext hEq)

theorem simpleSurvivor_val_ne :
    (simpleSurvivor source (Prescribed.firstSimple source)).1 ≠
      (simpleSurvivor source (Prescribed.secondSimple source)).1 := by
  intro hEq
  have hFirst : (simpleSurvivor source (Prescribed.firstSimple source)).1.1.1 =
      directionEdge star (Prescribed.firstSimple source) :=
    ((mem_directionSurvivors data star anchor _ _).mp
      (simpleSurvivor_mem source _ (Prescribed.firstSimple_ne source))).2
  have hSecond : (simpleSurvivor source (Prescribed.secondSimple source)).1.1.1 =
      directionEdge star (Prescribed.secondSimple source) :=
    ((mem_directionSurvivors data star anchor _ _).mp
      (simpleSurvivor_mem source _ (Prescribed.secondSimple_ne source))).2
  apply Prescribed.directionEdge_simple_ne source
  rw [← hFirst, ← hSecond, hEq]

/-- **Both endpoint classes of the prescribed valency-three resolution are
trivalent.**  Part II, the valency-3 case: the anchor `A` resolves into `A_u` and `A_v`
joined by `h_1`; `A_u` sees the two doubled-direction occurrences and `A_v` the
two simple ones. -/
theorem nonDanglingValency_endpointVertex (sideValue : Bool) :
    nonDanglingValency (cand).datum
      (endpointVertex source hNoGlue hValid sideValue rep) = 3 := by
  classical
  cases sideValue
  · rw [← card_nonDanglingIncident,
      nonDanglingIncident_endpointVertex_false source hNoGlue hValid]
    refine Finset.card_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
    · exact bridge_ne_retained source hNoGlue hValid _
    · exact bridge_ne_retained source hNoGlue hValid _
    · exact fun hEq ↦ firstDoubled_val_ne source
        (ResolutionCut.oldSourceEdge_injective (cand) hEq)
  · rw [← card_nonDanglingIncident,
      nonDanglingIncident_endpointVertex_true source hNoGlue hValid]
    refine Finset.card_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
    · exact bridge_ne_retained source hNoGlue hValid _
    · exact bridge_ne_retained source hNoGlue hValid _
    · exact fun hEq ↦ simpleSurvivor_val_ne source
        (ResolutionCut.oldSourceEdge_injective (cand) hEq)

/-- **The bridge is alone in its stable class**: both of its ends are
trivalent, and a stable path continues only through a divalent surviving
vertex.  So `h_1` really is one new row. -/
theorem bridgeEdge_isolated
    (other : NonDanglingEdge (cand).datum)
    (hPath : other.stablePath =
      NonDanglingEdge.stablePath
        ⟨bridgeEdge source hNoGlue hValid rep,
          bridgeEdge_survives source hNoGlue hValid⟩) :
    other.1 = bridgeEdge source hNoGlue hValid rep := by
  have hEnds := sourceEnds_bridgeEdge source hNoGlue hValid rep
  refine congrArg Subtype.val
    (NonTrivalentUniqueFourValent.eq_of_stablePath_eq_of_ends_ne_two _ ?_ ?_
      other hPath)
  · rw [congrArg Prod.fst hEnds,
      nonDanglingValency_endpointVertex source hNoGlue hValid false]
    omega
  · rw [congrArg Prod.snd hEnds,
      nonDanglingValency_endpointVertex source hNoGlue hValid true]
    omega

/-! ## 7.  The retained-row descent and the packaged labelling -/

include source in
/-- The anchor really has surviving valency four: `2 + 1 + 1` over the three
directions.  (`ThreeBranchAnchor` stores the distribution, not the number.) -/
theorem nonDanglingValency_anchor :
    nonDanglingValency data (WallBlock.sourceVertex data wall anchor) = 4 := by
  have hRotate : ∀ value : Fin 3 → ℕ,
      ∑ other : Fin 3, value other =
        value (Prescribed.doubled source) + value (Prescribed.firstSimple source) +
          value (Prescribed.secondSimple source) := by
    intro value
    have hAny : ∀ (label : Fin 3) (v : Fin 3 → ℕ),
        ∑ other : Fin 3, v other = v label + v (label + 1) + v (label + 2) := by
      intro label v
      fin_cases label <;> simp [Fin.sum_univ_three] <;> omega
    exact hAny (Prescribed.doubled source) value
  have hSum := sum_card_directionSurvivors data star anchor
  rw [card_survivors, hRotate
    (fun label ↦ (directionSurvivors data star anchor label).card)] at hSum
  have hDoubled : (directionSurvivors data star anchor
      (Prescribed.doubled source)).card = 2 := source.distribution.doubled_count
  have hFirst : (directionSurvivors data star anchor
      (Prescribed.firstSimple source)).card = 1 :=
    source.distribution.other_count _ (Prescribed.firstSimple_ne source)
  have hSecond : (directionSurvivors data star anchor
      (Prescribed.secondSimple source)).card = 1 :=
    source.distribution.other_count _ (Prescribed.secondSimple_ne source)
  omega

/-- The geometric input for the retained-row descent: at every wall
block *other than the anchor*, two surviving occurrences meeting at a divalent
quotient-source vertex still lie on one stable path of the candidate. -/
def OrdinaryBlockDescent : Prop :=
  ∀ (first second : NonDanglingEdge data) (vertex : data.SourceVertex),
    vertex.1.1 = wall →
    ¬ (data.vertexPartition wall).Rel anchor.1 vertex.1.2 →
    first ≠ second →
    Incident data first.1 vertex → Incident data second.1 vertex →
    nonDanglingValency data vertex = 2 →
    (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 first).stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 second).stablePath

theorem stablePath_retained_eq_of_consecutive
    (hDescent : OrdinaryBlockDescent source hNoGlue hValid)
    {first second : NonDanglingEdge data}
    (h : Consecutive data first second) :
    (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 first).stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 second).stablePath := by
  obtain ⟨hNe, vertex, hFirst, hSecond, hValency⟩ := h
  by_cases hAt : vertex.1.1 = wall
  · by_cases hAnchorRel : (data.vertexPartition wall).Rel anchor.1 vertex.1.2
    · exfalso
      have hVertex : WallBlock.sourceVertex data wall anchor = vertex :=
        (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, hAnchorRel⟩
      rw [← hVertex, nonDanglingValency_anchor source] at hValency
      omega
    · exact hDescent first second vertex hAt hAnchorRel hNe hFirst hSecond hValency
  · exact stablePath_eq_of_consecutive
      (ResolutionAwayFromWall.consecutive_retained_of_away (cand) hValid
        (candidate_sourceGenus source hNoGlue hValid)
        first second hNe vertex hAt hFirst hSecond hValency)

/-- **The retained-row map.**  Every stable row of the incoming wall datum
descends to a stable row of the outgoing candidate along the literal retained
occurrences. -/
noncomputable def retainedRow
    (hDescent : OrdinaryBlockDescent source hNoGlue hValid) :
    StablePath data → StablePath (cand).datum :=
  Quot.lift
    (fun e ↦ (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 e).stablePath)
    (fun _ _ h ↦ stablePath_retained_eq_of_consecutive source hNoGlue hValid
      hDescent h)

@[simp] theorem retainedRow_mk
    (hDescent : OrdinaryBlockDescent source hNoGlue hValid)
    (e : NonDanglingEdge data) :
    retainedRow source hNoGlue hValid hDescent e.stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 e).stablePath := rfl

/-- **The honest stable length-matrix labelling of the outgoing candidate.**
The wall datum's own square labelling supplies every retained row and column;
`Option.none` is the vanishing coordinate of the incoming chart, re-used for
the new target edge `t_1` and for the bridge row `h_1`. -/
noncomputable def labelling {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate]
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath data)) :
    StableLengthMatrixLabelling (cand).datum (Option coordinate) where
  targetEdge := (Equiv.optionCongr labelling₀.targetEdge).trans
    (occurrenceEquiv target wall (cand).right)
  row := rowEquiv.trans (Equiv.optionCongr labelling₀.row)

@[simp] theorem labelling_targetEdge_none {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate]
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath data)) :
    (labelling source hNoGlue hValid labelling₀ rowEquiv).targetEdge none =
      occurrenceEquiv target wall (cand).right none := rfl

@[simp] theorem labelling_targetEdge_some {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate]
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath data))
    (c : coordinate) :
    (labelling source hNoGlue hValid labelling₀ rowEquiv).targetEdge (some c) =
      occurrenceEquiv target wall (cand).right (some (labelling₀.targetEdge c)) := rfl

@[simp] theorem labelling_row {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate]
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath data))
    (path : StablePath (cand).datum) :
    (labelling source hNoGlue hValid labelling₀ rowEquiv).row path =
      (rowEquiv path).map labelling₀.row := by
  cases h : rowEquiv path <;> simp [labelling, h]

/-! ## 8.  At an actual three-valent wall

The same hypothesis list as
`NonTrivalentValencyThreeCandidate.exists_valid_candidate_of_contraction`: an
incoming full-dimensional cover, its contraction forest, dangling
compatibility, the trivalent star and the anchor's `nd = 4`.  Nothing else is
supplied -- in particular no census, background, genus or trivalence hypothesis.
`hNd` is the only hypothesis beyond the wall data, and
`NonTrivalentAnchorValency` discharges it. -/

section Incoming

open GraphContraction GluingContraction ContractionFibre ContractionRamification
open FullDimensionalSource WallDegeneration

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (cover : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation cover coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hForest : ContractionForest cover a b contracted)
  (hCompat : DanglingCompatible cover hc hab hOne)
  (wallStar : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (anchorBlock : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩)
  (hNd : nonDanglingValency (contractDatum cover hc hab hOne)
    (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩
      anchorBlock) = 4)

include fd hForest hCompat hNd

omit hForest hNd in
theorem wall_noGlue : DanglingEdgeNoGlue (contractDatum cover hc hab hOne) :=
  danglingEdgeNoGlue_contractDatum cover hCompat.2 fd.danglingEdgeNoGlue

omit hCompat hNd in
theorem wall_valid : (contractDatum cover hc hab hOne).Valid :=
  valid_contractDatum cover hc hab hOne hForest fd.valid

/-- The wall datum's own anchor classifier, produced by
`NonTrivalentValencyThreeRigidity.threeBranchAnchor`. -/
theorem wallSource :
    ThreeBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlock :=
  NonTrivalentValencyThreeRigidity.threeBranchAnchor cover fd hc hab hOne hForest
    hCompat wallStar anchorBlock hNd

/-- **The candidate preserves the source genus at an actual three-valent
wall.** -/
theorem candidate_sourceGenus_of_contraction :
    genus (Prescribed.validCandidate
        (wallSource cover fd hc hab hOne hForest hCompat wallStar anchorBlock hNd)
        (wall_noGlue cover fd hc hab hOne hCompat)
        (wall_valid cover fd hc hab hOne hForest)).datum.sourceGraph =
      genus (contractDatum cover hc hab hOne).sourceGraph :=
  candidate_sourceGenus
    (wallSource cover fd hc hab hOne hForest hCompat wallStar anchorBlock hNd)
    (wall_noGlue cover fd hc hab hOne hCompat)
    (wall_valid cover fd hc hab hOne hForest)

/-- **Both endpoint classes are trivalent at an actual three-valent wall.**
The anchor `A` resolves into `A_u` and `A_v` joined by the bridge `h_1`. -/
theorem nonDanglingValency_endpointVertex_of_contraction (sideValue : Bool) :
    nonDanglingValency
      (Prescribed.validCandidate
        (wallSource cover fd hc hab hOne hForest hCompat wallStar anchorBlock hNd)
        (wall_noGlue cover fd hc hab hOne hCompat)
        (wall_valid cover fd hc hab hOne hForest)).datum
      (endpointVertex
        (wallSource cover fd hc hab hOne hForest hCompat wallStar anchorBlock hNd)
        (wall_noGlue cover fd hc hab hOne hCompat)
        (wall_valid cover fd hc hab hOne hForest) sideValue
        (Prescribed.selectedRepresentative
          (wallSource cover fd hc hab hOne hForest hCompat wallStar anchorBlock
            hNd))) = 3 :=
  nonDanglingValency_endpointVertex
    (wallSource cover fd hc hab hOne hForest hCompat wallStar anchorBlock hNd)
    (wall_noGlue cover fd hc hab hOne hCompat)
    (wall_valid cover fd hc hab hOne hForest) sideValue

end Incoming

end DraismaVargas.LocalCases.NonTrivalentValencyThreeRows
