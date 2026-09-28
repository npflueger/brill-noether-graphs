import DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
import DraismaVargas.LocalCases.NonTrivalentValencyFourRows
import DraismaVargas.LocalCases.NonTrivalentUniqueFourValent
import DraismaVargas.LocalCases.NonTrivalentAnchorValency

/-!
# Stable rows of the prescribed candidate above a two-valent wall

Source: Vargas, Part II (arXiv:2609.09109), Section 5.4 (Case `{v2-nd4}`, base
tree `T_2` = Base II), read through the labelling convention (1) of Section 5.1:
one edge of `H^(q)` contracts to the anchor, it is `h_1^(q)`, its two endpoints
are `A_u^(q)` and `A_v^(q)`, and aside from `h_1^(q)` the edges of `H^(q)`
correspond bijectively to those of `H_0`.

This module computes the stable rows of
`NonTrivalentValencyTwoCandidate.Prescribed.validCandidate`.  It is the
valency-two copy of `NonTrivalentValencyThreeRows`.  Like that file it needs no
gauge-transport half (the candidate lives over the **unchanged** incoming
datum), and it is further simplified by the background being the *neutral*
joined resolution.  The one genuinely new feature is Configuration B.

## The two configurations, and why the count is uniform

Write `S` for the survivors of the thick direction and `T` for those of the
thin one, so `|S| + |T| = 4` and `|S| >= 2`
(`NonTrivalentValencyTwoCandidate.Prescribed.card_thick_add_card_thin`), and
let `R := S.erase e_second` index the blocks of `finePartition` inside `A`.

* **Configuration A (`2+2`; Part II, Case `{v2-nd4-t3}`).**  `|S| = |T| = 2`,
  `R = {e_first}`.  The
  merged class is all of `A`; over `u` there is one vertex, over `v` one vertex,
  joined by the single bridge.  Stars: `{h_1, e_first, e_second}` and
  `{h_1} ∪ T`.
* **Configuration B (`3+1`; Part II, Case `{v2-nd4-t2}`).**  `|S| = 3`,
  `|T| = 1`, `R` has two
  elements.  Over `u` there are *two* vertices: the merged one, trivalent, and
  the third thick class's vertex, which is **divalent** -- it carries only its
  own old occurrence and its own new occurrence.  Over `v` there is still one
  vertex, trivalent, seeing two new occurrences and the single thin survivor.

In both cases the counts are `|R| + |T| = (|S| - 1) + (4 - |S|) = 3` at `A_v`
and `1 + 2 = 3` at the merged vertex over `u`, so **both endpoints are
trivalent in both configurations** and the statements below are uniform.  The
extra Configuration B vertex being divalent is exactly what makes its new
occurrence lie on the *retained* row of the third thick survivor rather than be
a second new row (`newSourceEdge_stablePath_eq_retained`); `bridgeEdge_isolated`
then says there is exactly one new stable row in both configurations.

## What is proved

* `candidate_sourceGenus`: the candidate preserves the source genus, with no
  receipt.  Both resolutions in play are stars in the sense of
  `NonTrivalentValencyFourRows.IsStar` -- the prescribed one is a
  `fineResolution` and the background is `joinedResolutionAt`.
* `endpointVertex`, `bridgeEdge` and their incidences, with the exact outgoing
  sizes `|A_u| = k_first + k_second` and `|A_v| = |A|`
  (`endpointVertex_blockCard`).
* `nonDanglingValency_endpointVertex`: `nd(A_u) = nd(A_v) = 3`, with the exact
  surviving stars (`nonDanglingIncident_endpointVertex_false/true`), and
  `nonDanglingValency_extraEndpointVertex = 2` for the Configuration B vertex.
* `bridgeEdge_isolated`: the bridge is alone in its stable class -- one new row.
* `nonDanglingValency_anchor = 4`, read off the distribution.
* `retainedRow` modulo the named `OrdinaryBlockDescent`, and `labelling` over
  `Option coordinate` modulo a supplied row equivalence, exactly as in
  `NonTrivalentValencyThreeRows`.
* The incoming-cover corollaries `rows_of_contraction` and
  `exists_rows_of_wall_metric`, the first with `hNd` explicit and the second
  with `hNd` discharged from the wall metric through
  `NonTrivalentAnchorValency.twoBranchAnchor_of_single_row`.  Both also carry
  the outgoing datum's validity, so `exists_rows_of_wall_metric` is an
  `nd(A) = 4`-free statement of the whole valency-two package.

## What is proved elsewhere

* `OrdinaryBlockDescent`: the retained-row descent across a *non-anchor* wall
  block of surviving valency two, stated here as a named predicate.  It is
  proved in `NonTrivalentValencyTwoDescent`: the background is the neutral
  joined resolution, so an ordinary wall block `B` is
  not split, its vertices over `u` and `v` are both the whole of `B`, joined by
  one new occurrence of index `|B|`; the ordinary-block census there
  (`mem_nonDanglingIncident_endpointVertex_ordinary`,
  `newSourceEdge_survives_iff_ordinary`) gives `ordinaryBlockDescent` from
  `data.Valid` alone, and `NonTrivalentValencyTwoDescent.retainedRow` is the
  unconditional instance of `retainedRow` below.
* `rowEquiv`: the full row equivalence, taken here as an argument of
  `labelling`.  It is proved in `NonTrivalentValencyTwoRowEquiv`: `rowEquiv`,
  `rowEquiv_retainedRow`,
  `rowEquiv_bridgeRow` and the instantiated `labelling`, under the ordinary
  blocks' trivalence `OrdinaryTrivalent` (discharged at an actual wall by
  `ordinaryTrivalent_of_wall_metric`); headline `exists_rowEquiv_of_wall_metric`.
* `AgreeOffColumn` against the incoming full-dimensional matrix:
  `NonTrivalentValencyTwoExit.agreeOffColumn_outLabelling`.

## The merged pair is a parameter

The two merged thick survivors are the explicit datum
`sel : NonTrivalentValencyTwoCandidate.Prescribed.Selection data star anchor`
rather than a `Classical.choose`, so every declaration below carries `sel`
(and, where the anchor's own distribution is used, the anchor `source` too),
and the headlines `rows_of_contraction` and `exists_rows_of_wall_metric` are
universally quantified over the selection.  `Prescribed.Selection.default
source` is the choice-made instance.

## Consumers

The boundary dispatcher for Part II Case `{v2-nd4}`, and the
nonsingularity/exit package built on `NonTrivalentLinkMatrix`
(`NonTrivalentValencyTwoExit`).
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoRows

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.W3R1SourceProfile
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyFourRows (IsStar euler_of_isStar
  isStar_fineResolution)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall}
  (source : TwoBranchAnchor data star anchor)
  (sel : Prescribed.Selection data star anchor)

local notation "cand" => (Prescribed.validCandidate sel)

local notation "rep" => (Prescribed.selectedRepresentative sel)

/-! ## 1.  Both resolutions are stars, so the source genus is preserved -/

theorem isStar_selectedResolution :
    IsStar (data.vertexPartition wall) (Prescribed.selectedResolution sel) :=
  isStar_fineResolution _ _ _

theorem isStar_joinedResolution :
    IsStar (data.vertexPartition wall)
      (joinedResolutionAt (data.vertexPartition wall)) :=
  Or.inr ⟨rfl, rfl⟩

/-- Off the anchor block the candidate really uses the neutral joined
resolution of `Prescribed.subdivisionBackground`. -/
theorem candidate_resolution_of_not_wall_rel (block : Fin degree)
    (hBlock : ¬ (data.vertexPartition wall).Rel anchor.1 block) :
    (cand).resolution block = joinedResolutionAt (data.vertexPartition wall) := by
  unfold Prescribed.validCandidate Prescribed.candidate
    Prescribed.SubdivisionBackground.background
    GlobalM11Arbitrary.Background.install
  exact LocalResolution.onBlock_of_not_rel _ _ _ _ _ hBlock

theorem candidate_resolution_of_wall_rel (block : Fin degree)
    (hBlock : (data.vertexPartition wall).Rel anchor.1 block) :
    (cand).resolution block = Prescribed.selectedResolution sel :=
  Prescribed.candidate_resolution_of_wall_rel sel _ block hBlock

/-- **The valency-two candidate does not change the source genus.**  No receipt
is supplied: every wall block carries a star, and the blockwise Euler identity
feeds `M11SourceGenus.candidate_sourceGenus_of_blockwise_euler`. -/
theorem candidate_sourceGenus :
    genus (cand).datum.sourceGraph = genus data.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_blockwise_euler
  intro block _hCanonical
  by_cases hBlock : (data.vertexPartition wall).Rel anchor.1 block
  · rw [candidate_resolution_of_wall_rel sel block hBlock]
    exact euler_of_isStar (isStar_selectedResolution sel) block
  · rw [candidate_resolution_of_not_wall_rel sel block hBlock]
    exact euler_of_isStar isStar_joinedResolution block

/-! ## 2.  The two endpoint vertices and the bridge occurrence -/

/-- The endpoint partition on one side of the new target edge: the merged
`A_u` partition over `u`, the whole old wall partition over `v`. -/
noncomputable def endpointPartition (sideValue : Bool) : SheetPartition degree :=
  if sideValue then data.vertexPartition wall else Prescribed.finePartition sel

@[simp] theorem endpointPartition_false :
    endpointPartition sel false = Prescribed.finePartition sel := rfl

@[simp] theorem endpointPartition_true :
    endpointPartition sel true = data.vertexPartition wall := rfl

theorem selectedResolution_endpoint (sideValue : Bool) :
    (if sideValue then (Prescribed.selectedResolution sel).right
      else (Prescribed.selectedResolution sel).left) =
      endpointPartition sel sideValue := by
  cases sideValue <;> rfl

theorem endpointPartition_refines (sideValue : Bool) :
    (endpointPartition sel sideValue).Refines (data.vertexPartition wall) := by
  cases sideValue
  · exact Prescribed.finePartition_refines sel
  · exact SheetPartition.Refines.refl _

theorem candidate_right : (cand).right = Prescribed.rightAssignment data star anchor := rfl

theorem rep_wall_rel :
    (data.vertexPartition wall).Rel anchor.1 rep :=
  Prescribed.selectedRepresentative_wall_rel sel

/-- The actual outgoing source vertex on one side of the new target edge. -/
noncomputable def endpointVertex (sideValue : Bool) (sheet : Fin degree) :
    (cand).datum.SourceVertex :=
  (cand).datum.sourceEndpoint
    (if sideValue then freshVertex target else oldVertex target wall) sheet

/-- The new bridge occurrence `h_1` of the resolution. -/
noncomputable def bridgeEdge (sheet : Fin degree) : (cand).datum.SourceEdge :=
  (cand).newSourceEdge sheet

theorem sourceEnds_bridgeEdge (sheet : Fin degree) :
    (cand).datum.sourceEnds (bridgeEdge sel sheet) =
      (endpointVertex sel false sheet, endpointVertex sel true sheet) :=
  GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet

theorem bridgeEdge_incident (sideValue : Bool) (sheet : Fin degree) :
    Incident (cand).datum (bridgeEdge sel sheet)
      (endpointVertex sel sideValue sheet) := by
  cases sideValue
  · exact Or.inl (congrArg Prod.fst
      (GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet))
  · exact Or.inr (congrArg Prod.snd
      (GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet))

/-- A retained old occurrence at the wall meets the endpoint vertex on the side
the base tree assigns to its target occurrence. -/
theorem retainedEdge_incident (edge : target.edges)
    (hAt : edge ∈ GluingDatum.incidentEdges wall) (sideValue : Bool)
    (hSide : Prescribed.rightAssignment data star anchor edge = sideValue)
    (sheet : Fin degree) :
    Incident (cand).datum
      ((cand).oldSourceEdge (data.sourceEdge edge sheet))
      (endpointVertex sel sideValue sheet) := by
  cases sideValue
  · exact LimitChainCore.oldSourceEdge_incident_old _ edge hAt hSide sheet
  · exact M11SplitSurvival.oldSourceEdge_incident_fresh _ edge hAt hSide sheet

/-- **The exact endpoint sizes on the actual outgoing source vertices**:
`|A_u| = k_first + k_second` over `u` and `|A_v| = |A|` over `v`. -/
theorem endpointVertex_blockCard (sideValue : Bool) :
    ((cand).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall)).blockCard rep =
      if sideValue then (data.vertexPartition wall).blockCard anchor.1
      else data.sourceEdgeIndex (Prescribed.firstSelected sel).1 +
        data.sourceEdgeIndex (Prescribed.secondSelected sel).1 := by
  have hReprRel : (data.vertexPartition wall).Rel anchor.1
      ((data.vertexPartition wall).repr rep) :=
    (rep_wall_rel sel).trans ((data.vertexPartition wall).rel_repr_right _)
  rw [← Prescribed.candidate_endpoint_blockCard sel
    (Prescribed.subdivisionBackground data star anchor) sideValue,
    Prescribed.candidate_resolution_anchor sel _]
  cases sideValue
  · show ((cand).datum.vertexPartition (oldVertex target wall)).blockCard _ = _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
    rw [LocalResolution.paste_left_blockCard,
      candidate_resolution_of_wall_rel sel _ hReprRel]
    simp
  · show ((cand).datum.vertexPartition (freshVertex target)).blockCard _ = _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]
    rw [LocalResolution.paste_right_blockCard,
      candidate_resolution_of_wall_rel sel _ hReprRel]
    simp

/-- Inside the anchor block, two sheets name the same outgoing endpoint vertex
exactly when the endpoint partition of that side relates them. -/
theorem candidate_vertexPartition_rel_iff (sideValue : Bool) {a b : Fin degree}
    (hA : (data.vertexPartition wall).Rel anchor.1 a) :
    ((cand).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall)).Rel a b ↔
      (endpointPartition sel sideValue).Rel a b := by
  have hReprRel : (data.vertexPartition wall).Rel anchor.1
      ((data.vertexPartition wall).repr a) :=
    hA.trans ((data.vertexPartition wall).rel_repr_right a)
  have hSelected := candidate_resolution_of_wall_rel sel _ hReprRel
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
    (hRel : (endpointPartition sel sideValue).Rel a b) :
    endpointVertex sel sideValue a = endpointVertex sel sideValue b := by
  apply (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr
  refine ⟨rfl, ?_⟩
  refine Eq.trans ?_ (((cand).datum.vertexPartition
    (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right b)
  exact (candidate_vertexPartition_rel_iff sel sideValue hA).mpr hRel

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
        Prescribed.rightAssignment data star anchor edge = sideValue) := by
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

/-- The literal source occurrence named by an incident survivor. -/
theorem sourceEdge_occurrenceSheet {label : Fin 2}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    data.sourceEdge (star.edge label) (occurrenceSheet edge) = edge.1 := by
  apply Subtype.ext
  apply Prod.ext
  · exact (survivor_target hEdge).symm
  · show (data.edgePartition (star.edge label)).repr (occurrenceSheet edge) =
      occurrenceSheet edge
    exact survivor_repr hEdge

theorem survivor_not_isDangling {label : Fin 2}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    ¬ IsDangling data edge.1 :=
  (mem_survivors data anchor edge).mp
    ((mem_directionSurvivors data star anchor label edge).mp hEdge).1

/-- A surviving old occurrence of a named direction whose sheet lies in the
anchor block is one of that direction's survivors. -/
theorem exists_directionSurvivor_eq (label : Fin 2) (old : data.SourceEdge)
    (hTarget : old.1.1 = star.edge label)
    (hWall : (data.vertexPartition wall).Rel anchor.1 old.1.2)
    (hSurvives : ¬ IsDangling data old) :
    ∃ edge ∈ directionSurvivors data star anchor label, edge.1 = old := by
  have hIncident : Incident data old (WallBlock.sourceVertex data wall anchor) := by
    refine (incident_wallBlock_sourceVertex_iff data anchor old).mpr
      ⟨hTarget ▸ star.edge_mem_incidentEdges label, ?_⟩
    apply Subtype.ext
    change (data.vertexPartition wall).repr old.1.2 = anchor.1
    unfold SheetPartition.Rel at hWall
    rw [← hWall, anchor.2]
  refine ⟨⟨old, hIncident⟩, ?_, rfl⟩
  exact (mem_directionSurvivors data star anchor label _).mpr
    ⟨(mem_survivors data anchor _).mpr hSurvives, hTarget⟩

end Survivors

/-! ## 4.  The blocks of `finePartition` inside the anchor

They are indexed by the *retained* thick survivors `S.erase e_second`, the
class of `e_first` having absorbed that of `e_second`.  In Configuration A
there is one of them (the whole of `A`); in Configuration B there are two. -/

section FineBlocks

theorem mem_selectedSheets_iff_rel (sheet : Fin degree) :
    sheet ∈ Prescribed.selectedSheets sel ↔
      (Prescribed.finePartition sel).Rel rep sheet := by
  rw [← Prescribed.finePartition_block_selected sel]
  exact (Prescribed.finePartition sel).mem_block_iff rep sheet

/-- The second selected class really has been absorbed. -/
theorem finePartition_rel_second :
    (Prescribed.finePartition sel).Rel rep
      (occurrenceSheet (Prescribed.secondSelected sel)) := by
  refine (mem_selectedSheets_iff_rel sel _).mp ?_
  unfold Prescribed.selectedSheets
  exact Finset.mem_union_right _
    ((data.edgePartition (Prescribed.thickEdge data star anchor)).self_mem_block _)

/-- A thick survivor lies in the merged bridge class exactly when it is one of
the two selected ones. -/
theorem finePartition_rel_thick_iff
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor
      (Prescribed.thickDirection data star anchor)) :
    (Prescribed.finePartition sel).Rel rep (occurrenceSheet edge) ↔
      edge = Prescribed.firstSelected sel ∨
        edge = Prescribed.secondSelected sel := by
  classical
  constructor
  · intro hRel
    have hMem := (mem_selectedSheets_iff_rel sel _).mpr hRel
    unfold Prescribed.selectedSheets at hMem
    rcases Finset.mem_union.mp hMem with hCase | hCase
    · left
      rw [SheetPartition.mem_block_iff, Prescribed.thickEdge_eq] at hCase
      by_contra hNe
      exact not_rel_occurrenceSheet (Prescribed.firstSelected_mem sel) hEdge
        (fun h ↦ hNe h.symm) hCase
    · right
      rw [SheetPartition.mem_block_iff, Prescribed.thickEdge_eq] at hCase
      by_contra hNe
      exact not_rel_occurrenceSheet (Prescribed.secondSelected_mem sel) hEdge
        (fun h ↦ hNe h.symm) hCase
  · rintro (rfl | rfl)
    · exact rfl
    · exact finePartition_rel_second sel

/-- Outside the merged class a thick survivor keeps its own class. -/
theorem finePartition_block_of_ne
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor
      (Prescribed.thickDirection data star anchor))
    (hNeFirst : edge ≠ Prescribed.firstSelected sel)
    (hNeSecond : edge ≠ Prescribed.secondSelected sel) :
    (Prescribed.finePartition sel).block (occurrenceSheet edge) =
      (data.edgePartition (Prescribed.thickEdge data star anchor)).block
        (occurrenceSheet edge) := by
  refine SheetPartition.mergeBlocks_block_of_separate _ _ _ _ _ ?_ ?_
  · rw [Prescribed.thickEdge_eq]
    exact not_rel_occurrenceSheet hEdge (Prescribed.firstSelected_mem sel) hNeFirst
  · rw [Prescribed.thickEdge_eq]
    exact not_rel_occurrenceSheet hEdge (Prescribed.secondSelected_mem sel) hNeSecond

include source in
/-- Every sheet of the anchor block lies in the `finePartition` class of a
retained thick survivor. -/
theorem exists_retained_rel {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    ∃ edge ∈ (directionSurvivors data star anchor
        (Prescribed.thickDirection data star anchor)).erase
          (Prescribed.secondSelected sel),
      (Prescribed.finePartition sel).Rel (occurrenceSheet edge) sheet := by
  classical
  have hMem : sheet ∈ (data.vertexPartition wall).block anchor.1 :=
    ((data.vertexPartition wall).mem_block_iff _ _).mpr hSheet
  rw [← biUnion_block_eq_wallBlock source (Prescribed.thickDirection data star anchor)]
    at hMem
  obtain ⟨edge, hEdge, hBlock⟩ := Finset.mem_biUnion.mp hMem
  rw [SheetPartition.mem_block_iff] at hBlock
  have hFine : (Prescribed.finePartition sel).Rel (occurrenceSheet edge) sheet := by
    refine (Prescribed.edgePartition_thick_refines_finePartition sel).rel ?_
    rw [Prescribed.thickEdge_eq]
    exact hBlock
  by_cases hSecond : edge = Prescribed.secondSelected sel
  · refine ⟨Prescribed.firstSelected sel, Finset.mem_erase.mpr
      ⟨Prescribed.firstSelected_ne_secondSelected sel,
        Prescribed.firstSelected_mem sel⟩, ?_⟩
    subst hSecond
    exact (finePartition_rel_second sel).trans hFine
  · exact ⟨edge, Finset.mem_erase.mpr ⟨hSecond, hEdge⟩, hFine⟩

/-- Distinct retained thick survivors name distinct blocks of
`finePartition`. -/
theorem eq_of_finePartition_rel
    {a b : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (ha : a ∈ (directionSurvivors data star anchor
      (Prescribed.thickDirection data star anchor)).erase
        (Prescribed.secondSelected sel))
    (hb : b ∈ (directionSurvivors data star anchor
      (Prescribed.thickDirection data star anchor)).erase
        (Prescribed.secondSelected sel))
    (hRel : (Prescribed.finePartition sel).Rel (occurrenceSheet a)
      (occurrenceSheet b)) : a = b := by
  classical
  obtain ⟨haNe, haMem⟩ := Finset.mem_erase.mp ha
  obtain ⟨hbNe, hbMem⟩ := Finset.mem_erase.mp hb
  by_cases haFirst : a = Prescribed.firstSelected sel
  · subst haFirst
    rcases (finePartition_rel_thick_iff sel hbMem).mp hRel with hCase | hCase
    · exact hCase.symm
    · exact absurd hCase hbNe
  · have hBlock := finePartition_block_of_ne sel haMem haFirst haNe
    have hMem : occurrenceSheet b ∈
        (Prescribed.finePartition sel).block (occurrenceSheet a) :=
      (SheetPartition.mem_block_iff _ _ _).mpr hRel
    rw [hBlock, SheetPartition.mem_block_iff, Prescribed.thickEdge_eq] at hMem
    by_contra hNe
    exact not_rel_occurrenceSheet haMem hbMem hNe hMem

end FineBlocks

/-! ## 5.  Retained survivors, and survival of the new occurrences -/

include source in
theorem one_le_card_directionSurvivors (label : Fin 2) :
    1 ≤ (directionSurvivors data star anchor label).card := by
  classical
  rcases source.distribution with hEven | ⟨tripled, hTripled, hOther⟩
  · rw [hEven label]
    omega
  · by_cases hLabel : label = tripled
    · subst hLabel
      rw [hTripled]
      omega
    · rw [hOther label hLabel]

include source in
/-- The thin direction is never empty: both distributions put at least one
survivor above each target occurrence. -/
theorem exists_thinSurvivor :
    ∃ edge, edge ∈ directionSurvivors data star anchor
      (Prescribed.thinDirection data star anchor) :=
  Finset.card_pos.mp (one_le_card_directionSurvivors source _)

theorem rightAssignment_thickDirection :
    Prescribed.rightAssignment data star anchor
      (star.edge (Prescribed.thickDirection data star anchor)) = false := by
  rw [← Prescribed.thickEdge_eq]
  exact Prescribed.rightAssignment_thick data star anchor

theorem rightAssignment_thinDirection :
    Prescribed.rightAssignment data star anchor
      (star.edge (Prescribed.thinDirection data star anchor)) = true := by
  rw [← Prescribed.thinEdge_eq]
  exact Prescribed.rightAssignment_of_ne data star anchor
    (Prescribed.thinEdge_ne_thickEdge data star anchor)

theorem retained_survivor_survives (hValid : data.Valid) {label : Fin 2}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    ¬ IsDangling (cand).datum ((cand).oldSourceEdge edge.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ hValid.1 _
    (survivor_not_isDangling hEdge)

theorem retained_survivor_incident (sideValue : Bool) {label : Fin 2}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label)
    (hSide : Prescribed.rightAssignment data star anchor (star.edge label) = sideValue)
    {sheet : Fin degree}
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet)
    (hRel : (endpointPartition sel sideValue).Rel sheet (occurrenceSheet edge)) :
    Incident (cand).datum ((cand).oldSourceEdge edge.1)
      (endpointVertex sel sideValue sheet) := by
  rw [← sourceEdge_occurrenceSheet hEdge,
    endpointVertex_eq sel sideValue hWall hRel]
  exact retainedEdge_incident sel (star.edge label)
    (star.edge_mem_incidentEdges label) sideValue hSide (occurrenceSheet edge)

/-- Over `u`, the vertex of a thick survivor carries that survivor. -/
theorem nonDanglingValency_endpointVertex_false_ne_zero (hValid : data.Valid)
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor
      (Prescribed.thickDirection data star anchor)) :
    nonDanglingValency (cand).datum
      (endpointVertex sel false (occurrenceSheet edge)) ≠ 0 :=
  ClassInjectivity.nonDanglingValency_ne_zero_of_incident _
    (retained_survivor_survives sel hValid hEdge)
    (retained_survivor_incident sel false hEdge
      rightAssignment_thickDirection (occurrenceSheet_wall_rel edge) rfl)

include source in
/-- Over `v`, the single vertex `A_v` carries every thin survivor. -/
theorem nonDanglingValency_endpointVertex_true_ne_zero (hValid : data.Valid)
    {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    nonDanglingValency (cand).datum (endpointVertex sel true sheet) ≠ 0 := by
  obtain ⟨thin, hThin⟩ := exists_thinSurvivor source
  exact ClassInjectivity.nonDanglingValency_ne_zero_of_incident _
    (retained_survivor_survives sel hValid hThin)
    (retained_survivor_incident sel true hThin
      rightAssignment_thinDirection hSheet
      (hSheet.symm.trans (occurrenceSheet_wall_rel thin)))

include source in
/-- **Every new occurrence over the anchor survives.**  Both of its endpoint
vertices already carry a retained survivor.  In Configuration A this is only
the bridge `h_1`; in Configuration B it is also the occurrence of the third
thick class. -/
theorem newSourceEdge_survives (hValid : data.Valid)
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor
      (Prescribed.thickDirection data star anchor)) :
    ¬ IsDangling (cand).datum ((cand).newSourceEdge (occurrenceSheet edge)) := by
  have hEnds : (cand).datum.sourceEnds ((cand).newSourceEdge (occurrenceSheet edge)) =
      (endpointVertex sel false (occurrenceSheet edge),
        endpointVertex sel true (occurrenceSheet edge)) :=
    sourceEnds_bridgeEdge sel (occurrenceSheet edge)
  intro hDangling
  rcases hDangling with hSide | hSide
  · obtain ⟨cut⟩ := hSide
    apply nonDanglingValency_endpointVertex_false_ne_zero sel hValid hEdge
    have hFst := congrArg Prod.fst hEnds
    have hZero := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side
      _ cut cut.left_mem
    rwa [hFst] at hZero
  · obtain ⟨cut⟩ := hSide
    apply nonDanglingValency_endpointVertex_true_ne_zero source sel hValid
      (occurrenceSheet_wall_rel edge)
    have hSnd := congrArg Prod.snd hEnds
    have hZero := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side
      _ cut cut.left_mem
    rwa [hSnd] at hZero

include source in
/-- **The bridge `h_1` survives.** -/
theorem bridgeEdge_survives (hValid : data.Valid) :
    ¬ IsDangling (cand).datum (bridgeEdge sel rep) :=
  newSourceEdge_survives source sel hValid (Prescribed.firstSelected_mem sel)

/-! ## 6.  Exhaustion: what else can meet an endpoint vertex -/

theorem endpointPartition_rel_of_incident (sideValue : Bool) {t : Fin degree}
    (hT : (data.vertexPartition wall).Rel anchor.1 t)
    {e : (cand).datum.SourceEdge}
    (hIncident : Incident (cand).datum e (endpointVertex sel sideValue t)) :
    (endpointPartition sel sideValue).Rel t e.1.2 := by
  rw [incident_iff_target_mem_and_rel] at hIncident
  refine (candidate_vertexPartition_rel_iff sel sideValue hT).mp ?_
  exact Eq.trans
    (((cand).datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right t)
    hIncident.2

theorem right_eq_of_incident_old (sideValue : Bool) {t : Fin degree}
    {old : data.SourceEdge}
    (hIncident : Incident (cand).datum ((cand).oldSourceEdge old)
      (endpointVertex sel sideValue t)) :
    old.1.1 ∈ GluingDatum.incidentEdges wall ∧
      Prescribed.rightAssignment data star anchor old.1.1 = sideValue := by
  rw [incident_iff_target_mem_and_rel] at hIncident
  have hTargetMem := hIncident.1
  rw [BalancedGlobal.Candidate.oldSourceEdge_target] at hTargetMem
  exact (mem_incidentEdges_endpoint_old sel sideValue old.1.1).mp hTargetMem

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
      (Prescribed.finePartition sel).Rel a b := by
  have hReprRel : (data.vertexPartition wall).Rel anchor.1
      ((data.vertexPartition wall).repr a) :=
    hA.trans ((data.vertexPartition wall).rel_repr_right a)
  have hSelected := candidate_resolution_of_wall_rel sel _ hReprRel
  refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
    (fun blk ↦ ((cand).resolution blk).newEdge)
    (fun blk ↦ ((cand).resolution blk).edge_refines_left.trans
      ((cand).contracts blk).left_refines) a b) ?_
  rw [hSelected]
  rfl

/-- A new occurrence whose block meets the `finePartition` class of a sheet of
the anchor is the new occurrence of that sheet. -/
theorem newSourceEdge_eq_of_finePartition_rel {t s : Fin degree}
    (hT : (data.vertexPartition wall).Rel anchor.1 t)
    (hRel : (Prescribed.finePartition sel).Rel t
      ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.repr s)) :
    (cand).newSourceEdge s = (cand).newSourceEdge t := by
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
  exact (newSourceEdge_eq_of_rel sel
    ((newEdge_rel_iff_finePartition sel hT).mpr hRel)).symm

theorem newSourceEdge_ne_oldSourceEdge (s : Fin degree) (old : data.SourceEdge) :
    (cand).newSourceEdge s ≠ (cand).oldSourceEdge old := by
  intro hEq
  have h := congrArg (fun edge : (cand).datum.SourceEdge ↦ edge.1.1) hEq
  have hNone := (occurrenceEquiv target wall (cand).right).injective h
  cases hNone

/-- The only incident occurrence the base tree sends to the `v` side is the
thin one. -/
theorem target_eq_thin_of_rightAssignment {edge : target.edges}
    (hAt : edge ∈ GluingDatum.incidentEdges wall)
    (hSide : Prescribed.rightAssignment data star anchor edge = true) :
    edge = Prescribed.thinEdge data star anchor := by
  classical
  rw [Prescribed.incidentEdges_eq_pair data star anchor, Finset.mem_insert,
    Finset.mem_singleton] at hAt
  rcases hAt with rfl | hAt
  · rw [Prescribed.rightAssignment_thick data star anchor] at hSide
    exact absurd hSide (by simp)
  · exact hAt

/-- A surviving retained occurrence meeting a `u`-side endpoint vertex is a
thick survivor lying in that vertex's class. -/
theorem exists_thickSurvivor_of_incident_false (hValid : data.Valid) {t : Fin degree}
    (hT : (data.vertexPartition wall).Rel anchor.1 t) {old : data.SourceEdge}
    (hSurvives : ¬ IsDangling (cand).datum ((cand).oldSourceEdge old))
    (hIncident : Incident (cand).datum ((cand).oldSourceEdge old)
      (endpointVertex sel false t)) :
    ∃ edge ∈ directionSurvivors data star anchor
        (Prescribed.thickDirection data star anchor),
      edge.1 = old ∧ (Prescribed.finePartition sel).Rel t (occurrenceSheet edge) := by
  obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old sel false hIncident
  have hTarget : old.1.1 = star.edge (Prescribed.thickDirection data star anchor) := by
    rw [← Prescribed.thickEdge_eq]
    exact (Prescribed.rightAssignment_eq_false_iff data star anchor old.1.1).mp hSide
  have hRel : (Prescribed.finePartition sel).Rel t old.1.2 :=
    endpointPartition_rel_of_incident sel false hT hIncident
  have hWallRel : (data.vertexPartition wall).Rel anchor.1 old.1.2 :=
    hT.trans ((endpointPartition_refines sel false).rel hRel)
  have hOldSurv : ¬ IsDangling data old := fun h ↦ hSurvives
    ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand) hValid
      (candidate_sourceGenus sel) old).mpr h)
  obtain ⟨edge, hEdge, hVal⟩ := exists_directionSurvivor_eq
    (Prescribed.thickDirection data star anchor) old hTarget hWallRel hOldSurv
  refine ⟨edge, hEdge, hVal, ?_⟩
  show (Prescribed.finePartition sel).Rel t edge.1.1.2
  rw [hVal]
  exact hRel

/-- A surviving retained occurrence meeting the `v`-side endpoint vertex is a
thin survivor. -/
theorem exists_thinSurvivor_of_incident_true (hValid : data.Valid) {t : Fin degree}
    (hT : (data.vertexPartition wall).Rel anchor.1 t) {old : data.SourceEdge}
    (hSurvives : ¬ IsDangling (cand).datum ((cand).oldSourceEdge old))
    (hIncident : Incident (cand).datum ((cand).oldSourceEdge old)
      (endpointVertex sel true t)) :
    ∃ edge ∈ directionSurvivors data star anchor
      (Prescribed.thinDirection data star anchor), edge.1 = old := by
  obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old sel true hIncident
  have hTarget : old.1.1 = star.edge (Prescribed.thinDirection data star anchor) := by
    rw [← Prescribed.thinEdge_eq]
    exact target_eq_thin_of_rightAssignment hAt hSide
  have hRel : (endpointPartition sel true).Rel t old.1.2 :=
    endpointPartition_rel_of_incident sel true hT hIncident
  have hWallRel : (data.vertexPartition wall).Rel anchor.1 old.1.2 :=
    hT.trans ((endpointPartition_refines sel true).rel hRel)
  have hOldSurv : ¬ IsDangling data old := fun h ↦ hSurvives
    ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand) hValid
      (candidate_sourceGenus sel) old).mpr h)
  exact exists_directionSurvivor_eq (Prescribed.thinDirection data star anchor)
    old hTarget hWallRel hOldSurv

/-! ## 7.  The exact surviving star over `u` -/

theorem firstSelected_val_ne :
    (Prescribed.firstSelected sel).1 ≠ (Prescribed.secondSelected sel).1 :=
  fun hEq ↦ Prescribed.firstSelected_ne_secondSelected sel (Subtype.ext hEq)

/-- **The surviving star at the merged endpoint over `u`**: the bridge and the
two selected thick survivors. -/
theorem nonDanglingIncident_endpointVertex_false_subset (hValid : data.Valid) :
    nonDanglingIncident (cand).datum (endpointVertex sel false rep) ⊆
      {bridgeEdge sel rep,
        (cand).oldSourceEdge (Prescribed.firstSelected sel).1,
        (cand).oldSourceEdge (Prescribed.secondSelected sel).1} := by
  classical
  intro e he
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp he
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, rfl⟩ | ⟨s, rfl⟩
  · obtain ⟨edge, hEdge, hVal, hRel⟩ := exists_thickSurvivor_of_incident_false sel
      hValid (rep_wall_rel sel) hSurvives hIncident
    rcases (finePartition_rel_thick_iff sel hEdge).mp hRel with hCase | hCase
    · exact Or.inr (Or.inl (by rw [← hVal, hCase]))
    · exact Or.inr (Or.inr (by rw [← hVal, hCase]))
  · left
    exact newSourceEdge_eq_of_finePartition_rel sel (rep_wall_rel sel)
      (endpointPartition_rel_of_incident sel false (rep_wall_rel sel) hIncident)

include source in
theorem triple_subset_nonDanglingIncident_false (hValid : data.Valid) :
    ({bridgeEdge sel rep,
        (cand).oldSourceEdge (Prescribed.firstSelected sel).1,
        (cand).oldSourceEdge (Prescribed.secondSelected sel).1} :
          Finset (cand).datum.SourceEdge) ⊆
      nonDanglingIncident (cand).datum (endpointVertex sel false rep) := by
  classical
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨bridgeEdge_survives source sel hValid, bridgeEdge_incident sel false rep⟩
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨retained_survivor_survives sel hValid (Prescribed.firstSelected_mem sel),
        retained_survivor_incident sel false (Prescribed.firstSelected_mem sel)
          rightAssignment_thickDirection (rep_wall_rel sel) rfl⟩
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨retained_survivor_survives sel hValid (Prescribed.secondSelected_mem sel),
        retained_survivor_incident sel false (Prescribed.secondSelected_mem sel)
          rightAssignment_thickDirection (rep_wall_rel sel)
          (finePartition_rel_second sel)⟩

include source in
theorem nonDanglingIncident_endpointVertex_false (hValid : data.Valid) :
    nonDanglingIncident (cand).datum (endpointVertex sel false rep) =
      {bridgeEdge sel rep,
        (cand).oldSourceEdge (Prescribed.firstSelected sel).1,
        (cand).oldSourceEdge (Prescribed.secondSelected sel).1} :=
  Finset.Subset.antisymm
    (nonDanglingIncident_endpointVertex_false_subset sel hValid)
    (triple_subset_nonDanglingIncident_false source sel hValid)

include source in
/-- **The merged endpoint over `u` is trivalent.** -/
theorem nonDanglingValency_endpointVertex_false (hValid : data.Valid) :
    nonDanglingValency (cand).datum (endpointVertex sel false rep) = 3 := by
  classical
  rw [← card_nonDanglingIncident,
    nonDanglingIncident_endpointVertex_false source sel hValid]
  refine Finset.card_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
  · exact newSourceEdge_ne_oldSourceEdge sel rep _
  · exact newSourceEdge_ne_oldSourceEdge sel rep _
  · exact fun hEq ↦ firstSelected_val_ne sel
      (ResolutionCut.oldSourceEdge_injective (cand) hEq)

/-! ## 8.  The exact surviving star over `v`

Here the two configurations differ in *composition* but not in *count*: `A_v`
sees one new occurrence per retained thick class and one old occurrence per
thin survivor, and `(|S| - 1) + |T| = 3` in both. -/

/-- The thick survivors indexing the blocks of `finePartition` inside `A`: all
of them but the absorbed `e_second`. -/
noncomputable def retainedThick :
    Finset (IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :=
  (directionSurvivors data star anchor
      (Prescribed.thickDirection data star anchor)).erase
    (Prescribed.secondSelected sel)

theorem retainedThick_subset :
    retainedThick sel ⊆ directionSurvivors data star anchor
      (Prescribed.thickDirection data star anchor) :=
  Finset.erase_subset _ _

theorem mem_retainedThick {edge : IncidentSourceEdge data
    (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ retainedThick sel) :
    edge ∈ directionSurvivors data star anchor
        (Prescribed.thickDirection data star anchor) ∧
      edge ≠ Prescribed.secondSelected sel := by
  rw [retainedThick, Finset.mem_erase] at hEdge
  exact ⟨hEdge.2, hEdge.1⟩

include source in
theorem card_retainedThick_add_one :
    (retainedThick sel).card + 1 =
      (directionSurvivors data star anchor
        (Prescribed.thickDirection data star anchor)).card := by
  classical
  have hPos := Prescribed.two_le_card_thick source
  rw [retainedThick, Finset.card_erase_of_mem (Prescribed.secondSelected_mem sel)]
  omega

include source in
theorem card_retainedThick_add_card_thin :
    (retainedThick sel).card +
      (directionSurvivors data star anchor
        (Prescribed.thinDirection data star anchor)).card = 3 := by
  have hOne := card_retainedThick_add_one source sel
  have hFour := Prescribed.card_thick_add_card_thin source
  omega

include source in
theorem nonDanglingIncident_endpointVertex_true_subset (hValid : data.Valid) :
    nonDanglingIncident (cand).datum (endpointVertex sel true rep) ⊆
      (retainedThick sel).image
          (fun edge ↦ (cand).newSourceEdge (occurrenceSheet edge)) ∪
        (directionSurvivors data star anchor
          (Prescribed.thinDirection data star anchor)).image
            (fun edge ↦ (cand).oldSourceEdge edge.1) := by
  classical
  intro e he
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp he
  rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, rfl⟩ | ⟨s, rfl⟩
  · obtain ⟨edge, hEdge, hVal⟩ := exists_thinSurvivor_of_incident_true sel hValid
      (rep_wall_rel sel) hSurvives hIncident
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨edge, hEdge, by rw [hVal]⟩)
  · refine Finset.mem_union_left _ ?_
    have hRel := endpointPartition_rel_of_incident sel true (rep_wall_rel sel)
      hIncident
    have hWall : (data.vertexPartition wall).Rel anchor.1
        ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
          (cand).contracts).newEdge.repr s) := (rep_wall_rel sel).trans hRel
    obtain ⟨edge, hEdge, hFine⟩ := exists_retained_rel source sel hWall
    exact Finset.mem_image.mpr ⟨edge, hEdge,
      (newSourceEdge_eq_of_finePartition_rel sel (occurrenceSheet_wall_rel edge)
        hFine).symm⟩

include source in
theorem image_subset_nonDanglingIncident_true (hValid : data.Valid) :
    ((retainedThick sel).image
          (fun edge ↦ (cand).newSourceEdge (occurrenceSheet edge)) ∪
        (directionSurvivors data star anchor
          (Prescribed.thinDirection data star anchor)).image
            (fun edge ↦ (cand).oldSourceEdge edge.1)) ⊆
      nonDanglingIncident (cand).datum (endpointVertex sel true rep) := by
  classical
  intro e he
  rcases Finset.mem_union.mp he with hCase | hCase
  · obtain ⟨edge, hEdge, rfl⟩ := Finset.mem_image.mp hCase
    refine (mem_nonDanglingIncident _ _ _).mpr
      ⟨newSourceEdge_survives source sel hValid (retainedThick_subset sel hEdge), ?_⟩
    have hEq : endpointVertex sel true (occurrenceSheet edge) =
        endpointVertex sel true rep :=
      endpointVertex_eq sel true (occurrenceSheet_wall_rel edge)
        ((occurrenceSheet_wall_rel edge).symm.trans (rep_wall_rel sel))
    rw [← hEq]
    exact bridgeEdge_incident sel true (occurrenceSheet edge)
  · obtain ⟨edge, hEdge, rfl⟩ := Finset.mem_image.mp hCase
    refine (mem_nonDanglingIncident _ _ _).mpr
      ⟨retained_survivor_survives sel hValid hEdge, ?_⟩
    exact retained_survivor_incident sel true hEdge rightAssignment_thinDirection
      (rep_wall_rel sel)
      ((rep_wall_rel sel).symm.trans (occurrenceSheet_wall_rel edge))

include source in
theorem nonDanglingIncident_endpointVertex_true (hValid : data.Valid) :
    nonDanglingIncident (cand).datum (endpointVertex sel true rep) =
      (retainedThick sel).image
          (fun edge ↦ (cand).newSourceEdge (occurrenceSheet edge)) ∪
        (directionSurvivors data star anchor
          (Prescribed.thinDirection data star anchor)).image
            (fun edge ↦ (cand).oldSourceEdge edge.1) :=
  Finset.Subset.antisymm
    (nonDanglingIncident_endpointVertex_true_subset source sel hValid)
    (image_subset_nonDanglingIncident_true source sel hValid)

include source in
/-- **The endpoint `A_v` over `v` is trivalent**, in both configurations. -/
theorem nonDanglingValency_endpointVertex_true (hValid : data.Valid) :
    nonDanglingValency (cand).datum (endpointVertex sel true rep) = 3 := by
  classical
  rw [← card_nonDanglingIncident,
    nonDanglingIncident_endpointVertex_true source sel hValid]
  have hDisjoint : Disjoint
      ((retainedThick sel).image
        (fun edge ↦ (cand).newSourceEdge (occurrenceSheet edge)))
      ((directionSurvivors data star anchor
        (Prescribed.thinDirection data star anchor)).image
          (fun edge ↦ (cand).oldSourceEdge edge.1)) := by
    refine Finset.disjoint_left.mpr ?_
    intro e hNew hOld
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hNew
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hOld
    exact newSourceEdge_ne_oldSourceEdge sel _ _ hb.symm
  have hNewCard : ((retainedThick sel).image
      (fun edge ↦ (cand).newSourceEdge (occurrenceSheet edge))).card =
      (retainedThick sel).card := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hEq
    have hRepr : (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.Rel (occurrenceSheet a) (occurrenceSheet b) :=
      congrArg (fun edge : (cand).datum.SourceEdge ↦ edge.1.2) hEq
    exact eq_of_finePartition_rel sel (Finset.mem_coe.mp ha) (Finset.mem_coe.mp hb)
      ((newEdge_rel_iff_finePartition sel (occurrenceSheet_wall_rel a)).mp hRepr)
  have hOldCard : ((directionSurvivors data star anchor
      (Prescribed.thinDirection data star anchor)).image
        (fun edge ↦ (cand).oldSourceEdge edge.1)).card =
      (directionSurvivors data star anchor
        (Prescribed.thinDirection data star anchor)).card := by
    refine Finset.card_image_of_injOn ?_
    intro a _ b _ hEq
    exact Subtype.ext (ResolutionCut.oldSourceEdge_injective (cand) hEq)
  rw [Finset.card_union_of_disjoint hDisjoint, hNewCard, hOldCard]
  exact card_retainedThick_add_card_thin source sel

/-! ## 9.  Configuration B: the extra `u`-vertex is divalent, so it adds no row

In Configuration A `retainedThick` is the singleton `{e_first}` and this
section is vacuous.  In Configuration B it has a second element, whose vertex
over `u` carries exactly its own old occurrence and its own new occurrence: it
is divalent, so the new occurrence lies on the *retained* stable row of that
thick survivor and is not a new row. -/

include source in
theorem nonDanglingIncident_extraEndpointVertex (hValid : data.Valid)
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ retainedThick sel)
    (hNeFirst : edge ≠ Prescribed.firstSelected sel) :
    nonDanglingIncident (cand).datum
        (endpointVertex sel false (occurrenceSheet edge)) =
      {(cand).newSourceEdge (occurrenceSheet edge), (cand).oldSourceEdge edge.1} := by
  classical
  obtain ⟨hThick, hNeSecond⟩ := mem_retainedThick sel hEdge
  refine Finset.Subset.antisymm ?_ ?_
  · intro e he
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp he
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, rfl⟩ | ⟨s, rfl⟩
    · right
      obtain ⟨other, hOther, hVal, hRel⟩ := exists_thickSurvivor_of_incident_false
        sel hValid (occurrenceSheet_wall_rel edge) hSurvives hIncident
      have hOtherNeSecond : other ≠ Prescribed.secondSelected sel := by
        intro hEq
        subst hEq
        have hRepRel : (Prescribed.finePartition sel).Rel rep (occurrenceSheet edge) :=
          (finePartition_rel_second sel).trans hRel.symm
        rcases (finePartition_rel_thick_iff sel hThick).mp hRepRel with hCase | hCase
        · exact hNeFirst hCase
        · exact hNeSecond hCase
      have hEqEdge : edge = other :=
        eq_of_finePartition_rel sel hEdge
          (Finset.mem_erase.mpr ⟨hOtherNeSecond, hOther⟩) hRel
      rw [← hVal, ← hEqEdge]
    · left
      exact newSourceEdge_eq_of_finePartition_rel sel (occurrenceSheet_wall_rel edge)
        (endpointPartition_rel_of_incident sel false (occurrenceSheet_wall_rel edge)
          hIncident)
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨newSourceEdge_survives source sel hValid hThick,
          bridgeEdge_incident sel false (occurrenceSheet edge)⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨retained_survivor_survives sel hValid hThick,
          retained_survivor_incident sel false hThick rightAssignment_thickDirection
            (occurrenceSheet_wall_rel edge) rfl⟩

include source in
/-- **The Configuration B subdivision vertex is divalent.** -/
theorem nonDanglingValency_extraEndpointVertex (hValid : data.Valid)
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ retainedThick sel)
    (hNeFirst : edge ≠ Prescribed.firstSelected sel) :
    nonDanglingValency (cand).datum
      (endpointVertex sel false (occurrenceSheet edge)) = 2 := by
  classical
  rw [← card_nonDanglingIncident,
    nonDanglingIncident_extraEndpointVertex source sel hValid hEdge hNeFirst,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact newSourceEdge_ne_oldSourceEdge sel _ _), Finset.card_singleton]

/-- **The second new occurrence of Configuration B carries no new row**: it is
consecutive with the retained occurrence of its own thick class at the divalent
vertex over `u`, hence lies on that retained stable row. -/
theorem newSourceEdge_stablePath_eq_retained (hValid : data.Valid)
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ retainedThick sel)
    (hNeFirst : edge ≠ Prescribed.firstSelected sel) :
    NonDanglingEdge.stablePath
        (⟨(cand).newSourceEdge (occurrenceSheet edge),
          newSourceEdge_survives source sel hValid
            (mem_retainedThick sel hEdge).1⟩ :
          NonDanglingEdge (cand).datum) =
      NonDanglingEdge.stablePath
        (⟨(cand).oldSourceEdge edge.1,
          retained_survivor_survives sel hValid
            (mem_retainedThick sel hEdge).1⟩ :
          NonDanglingEdge (cand).datum) := by
  obtain ⟨hThick, hNeSecond⟩ := mem_retainedThick sel hEdge
  refine stablePath_eq_of_consecutive ⟨?_, endpointVertex sel false
    (occurrenceSheet edge), ?_, ?_, ?_⟩
  · intro hEq
    exact newSourceEdge_ne_oldSourceEdge sel (occurrenceSheet edge) edge.1
      (congrArg Subtype.val hEq)
  · exact bridgeEdge_incident sel false (occurrenceSheet edge)
  · exact retained_survivor_incident sel false hThick rightAssignment_thickDirection
      (occurrenceSheet_wall_rel edge) rfl
  · exact nonDanglingValency_extraEndpointVertex source sel hValid hEdge hNeFirst

include source in
/-- **The bridge is alone in its stable class**: both of its ends are
trivalent, and a stable path continues only through a divalent surviving
vertex.  So `h_1` really is one new row, in both configurations. -/
theorem bridgeEdge_isolated (hValid : data.Valid)
    (other : NonDanglingEdge (cand).datum)
    (hPath : other.stablePath =
      NonDanglingEdge.stablePath
        ⟨bridgeEdge sel rep, bridgeEdge_survives source sel hValid⟩) :
    other.1 = bridgeEdge sel rep := by
  have hEnds := sourceEnds_bridgeEdge sel rep
  refine congrArg Subtype.val
    (NonTrivalentUniqueFourValent.eq_of_stablePath_eq_of_ends_ne_two _ ?_ ?_
      other hPath)
  · rw [congrArg Prod.fst hEnds, nonDanglingValency_endpointVertex_false source sel hValid]
    omega
  · rw [congrArg Prod.snd hEnds, nonDanglingValency_endpointVertex_true source sel hValid]
    omega

/-! ## 10.  The retained-row descent and the packaged labelling -/

include source in
/-- The anchor really has surviving valency four: `2 + 2` or `3 + 1` over the
two directions.  (`TwoBranchAnchor` stores the distribution, not the number.) -/
theorem nonDanglingValency_anchor :
    nonDanglingValency data (WallBlock.sourceVertex data wall anchor) = 4 := by
  classical
  have hSum := sum_card_directionSurvivors data star anchor
  rw [card_survivors, Fin.sum_univ_two] at hSum
  have hPair := Prescribed.card_thick_add_card_thin source
  have hThin : Prescribed.thinDirection data star anchor =
      Prescribed.thickDirection data star anchor + 1 := rfl
  rcases NonTrivalentValencyTwoAnchor.eq_zero_or_one
    (Prescribed.thickDirection data star anchor) with hCase | hCase
  · rw [hThin, hCase, show ((0 : Fin 2) + 1) = 1 from rfl] at hPair
    omega
  · rw [hThin, hCase, show ((1 : Fin 2) + 1) = 0 from rfl] at hPair
    omega

/-- The remaining geometric input for the retained-row descent: at every wall
block *other than the anchor*, two surviving occurrences meeting at a divalent
quotient-source vertex still lie on one stable path of the candidate. -/
def OrdinaryBlockDescent (hValid : data.Valid) : Prop :=
  ∀ (first second : NonDanglingEdge data) (vertex : data.SourceVertex),
    vertex.1.1 = wall →
    ¬ (data.vertexPartition wall).Rel anchor.1 vertex.1.2 →
    first ≠ second →
    Incident data first.1 vertex → Incident data second.1 vertex →
    nonDanglingValency data vertex = 2 →
    (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 first).stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 second).stablePath

include source in
theorem stablePath_retained_eq_of_consecutive (hValid : data.Valid)
    (hDescent : OrdinaryBlockDescent sel hValid)
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
        (candidate_sourceGenus sel) first second hNe vertex hAt hFirst hSecond
        hValency)

/-- **The retained-row map.**  Every stable row of the incoming wall datum
descends to a stable row of the outgoing candidate along the literal retained
occurrences. -/
noncomputable def retainedRow (hValid : data.Valid)
    (hDescent : OrdinaryBlockDescent sel hValid) :
    StablePath data → StablePath (cand).datum :=
  Quot.lift
    (fun e ↦ (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 e).stablePath)
    (fun _ _ h ↦ stablePath_retained_eq_of_consecutive source sel hValid hDescent h)

@[simp] theorem retainedRow_mk (hValid : data.Valid)
    (hDescent : OrdinaryBlockDescent sel hValid) (e : NonDanglingEdge data) :
    retainedRow source sel hValid hDescent e.stablePath =
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
    (labelling sel labelling₀ rowEquiv).targetEdge none =
      occurrenceEquiv target wall (cand).right none := rfl

@[simp] theorem labelling_targetEdge_some {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate]
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath data))
    (c : coordinate) :
    (labelling sel labelling₀ rowEquiv).targetEdge (some c) =
      occurrenceEquiv target wall (cand).right (some (labelling₀.targetEdge c)) := rfl

@[simp] theorem labelling_row {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate]
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath data))
    (path : StablePath (cand).datum) :
    (labelling sel labelling₀ rowEquiv).row path =
      (rowEquiv path).map labelling₀.row := by
  cases h : rowEquiv path <;> simp [labelling, h]

include source in
/-- **Both endpoint classes of the prescribed valency-two resolution are
trivalent.**  Part II Section 5.4: the anchor `A` resolves into `A_u` and `A_v`
joined by `h_1`. -/
theorem nonDanglingValency_endpointVertex (hValid : data.Valid) (sideValue : Bool) :
    nonDanglingValency (cand).datum (endpointVertex sel sideValue rep) = 3 := by
  cases sideValue
  · exact nonDanglingValency_endpointVertex_false source sel hValid
  · exact nonDanglingValency_endpointVertex_true source sel hValid

/-! ## 11.  At an actual two-valent wall

First with the anchor's `nd = 4` explicit, exactly as in
`NonTrivalentValencyThreeRows`; then with it discharged from the wall metric
through `NonTrivalentAnchorValency.twoBranchAnchor_of_single_row`. -/

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
  (wallStar : TwoStar (contract target hab hOne) ⟨a, hab⟩)

include fd hForest

theorem wall_valid : (contractDatum cover hc hab hOne).Valid :=
  valid_contractDatum cover hc hab hOne hForest fd.valid

/-- **The full stable-row package at an actual two-valent wall**, with the
anchor's surviving valency four supplied.  The source genus is preserved, both
endpoint classes of the prescribed resolution are trivalent, and the bridge is
alone in its stable class. -/
theorem rows_of_contraction
    (hCompat : DanglingCompatible cover hc hab hOne)
    (anchorBlock : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩)
    (hNd : nonDanglingValency (contractDatum cover hc hab hOne)
      (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩
        anchorBlock) = 4) :
    ∃ src : NonTrivalentValencyTwoAnchor.TwoBranchAnchor
        (contractDatum cover hc hab hOne) wallStar anchorBlock,
      ∀ sel : Prescribed.Selection (contractDatum cover hc hab hOne)
          wallStar anchorBlock,
      (Prescribed.validCandidate sel).datum.Valid ∧
      genus (Prescribed.validCandidate sel).datum.sourceGraph =
          genus (contractDatum cover hc hab hOne).sourceGraph ∧
        (∀ sideValue : Bool,
          nonDanglingValency (Prescribed.validCandidate sel).datum
            (endpointVertex sel sideValue
              (Prescribed.selectedRepresentative sel)) = 3) ∧
        (∀ other : NonDanglingEdge (Prescribed.validCandidate sel).datum,
          other.stablePath =
            NonDanglingEdge.stablePath
              ⟨bridgeEdge sel (Prescribed.selectedRepresentative sel),
                bridgeEdge_survives src sel
                  (wall_valid cover fd hc hab hOne hForest)⟩ →
          other.1 = bridgeEdge sel (Prescribed.selectedRepresentative sel)) := by
  set src := NonTrivalentValencyTwoRigidity.twoBranchAnchor cover fd hc hab hOne
    hForest hCompat wallStar anchorBlock hNd with hSrc
  refine ⟨src, fun sel ↦ ⟨?_, ?_, ?_, ?_⟩⟩
  · exact Prescribed.validCandidate_datum_valid sel
      (wall_valid cover fd hc hab hOne hForest)
  · exact candidate_sourceGenus sel
  · exact nonDanglingValency_endpointVertex src sel
      (wall_valid cover fd hc hab hOne hForest)
  · exact bridgeEdge_isolated src sel (wall_valid cover fd hc hab hOne hForest)

/-- **The same package with `nd(A) = 4` discharged**, from the wall metric of
the existence route.  The remaining hypotheses are exactly those of
`NonTrivalentAnchorValency.twoBranchAnchor_of_single_row`. -/
theorem exists_rows_of_wall_metric
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
      (src : NonTrivalentValencyTwoAnchor.TwoBranchAnchor
        (contractDatum cover hc hab hOne) wallStar anchorBlock),
      nonDanglingValency (contractDatum cover hc hab hOne)
          (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩
            anchorBlock) = 4 ∧
        ∀ sel : Prescribed.Selection (contractDatum cover hc hab hOne)
            wallStar anchorBlock,
        (Prescribed.validCandidate sel).datum.Valid ∧
        genus (Prescribed.validCandidate sel).datum.sourceGraph =
          genus (contractDatum cover hc hab hOne).sourceGraph ∧
        (∀ sideValue : Bool,
          nonDanglingValency (Prescribed.validCandidate sel).datum
            (endpointVertex sel sideValue
              (Prescribed.selectedRepresentative sel)) = 3) ∧
        (∀ other : NonDanglingEdge (Prescribed.validCandidate sel).datum,
          other.stablePath =
            NonDanglingEdge.stablePath
              ⟨bridgeEdge sel (Prescribed.selectedRepresentative sel),
                bridgeEdge_survives src sel
                  (wall_valid cover fd hc hab hOne hForest)⟩ →
          other.1 = bridgeEdge sel (Prescribed.selectedRepresentative sel)) := by
  obtain ⟨anchorBlock, hNd, src⟩ :=
    NonTrivalentAnchorValency.twoBranchAnchor_of_single_row cover fd hc hab hOne
      hForest coordinates facet hRows hZeroCoord hPosCoord hFacetZero wallStar
  refine ⟨anchorBlock, src, hNd, fun sel ↦ ⟨?_, ?_, ?_, ?_⟩⟩
  · exact Prescribed.validCandidate_datum_valid sel
      (wall_valid cover fd hc hab hOne hForest)
  · exact candidate_sourceGenus sel
  · exact nonDanglingValency_endpointVertex src sel
      (wall_valid cover fd hc hab hOne hForest)
  · exact bridgeEdge_isolated src sel (wall_valid cover fd hc hab hOne hForest)

end Incoming

end DraismaVargas.LocalCases.NonTrivalentValencyTwoRows
