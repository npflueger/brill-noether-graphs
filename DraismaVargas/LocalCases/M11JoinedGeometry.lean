import DraismaVargas.LocalCases.M11SplitSurvival

/-!
# The actual endpoint geometry of the joined M11 candidate

The joined resolution retains the old wall partition at both endpoints and
on the new edge. Each target endpoint has its one labelled old occurrence
and the new occurrence. Its source incidence count is therefore one plus
the old edge-block count. On the distinguished M11 block that count is three.
Target labels 0/1 need not agree with the profile's double/single labels.
-/

namespace DraismaVargas.LocalCases.M11JoinedGeometry

open DraismaVargas.Infrastructure TargetExpansion
open ResolutionM11 GlobalM11Arbitrary M11SourceCandidates
open W4Assembly W4StableSource W2R1Target SecondEquation

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

/-- The expanded endpoint carrying one of the two old target labels. -/
def endpoint (target : CFGraph) (wall : target.V) (label : Fin 2) : target.V ⊕ Unit :=
  if label = 0 then oldVertex target wall else freshVertex target

variable (data : GluingDatum target degree) (star : TwoStar target wall)
  (block : WallBlock data wall) (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

noncomputable local instance : DecidableEq (graph target wall (joinedPattern data star block hCard).candidate.right).edges := by
  unfold Multiset.ToType
  infer_instance

theorem joined_resolution (anchor : Fin degree) :
    (joinedPattern data star block hCard).candidate.resolution anchor =
      joinedResolutionAt (data.vertexPartition wall) := by
  change LocalResolution.onBlock (data.vertexPartition wall) block.1
    (joinedResolutionAt (data.vertexPartition wall))
    (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor = _
  simp only [LocalResolution.onBlock, ite_self]

theorem pasted_left :
    (LocalResolution.paste (data.vertexPartition wall)
      (joinedPattern data star block hCard).candidate.resolution
      (joinedPattern data star block hCard).candidate.contracts).left = data.vertexPartition wall := by
  apply SheetPartition.ext_repr
  funext sheet
  change ((joinedPattern data star block hCard).candidate.resolution
    ((data.vertexPartition wall).repr sheet)).left.repr sheet = _
  rw [joined_resolution]
  rfl

theorem pasted_right :
    (LocalResolution.paste (data.vertexPartition wall)
      (joinedPattern data star block hCard).candidate.resolution
      (joinedPattern data star block hCard).candidate.contracts).right = data.vertexPartition wall := by
  apply SheetPartition.ext_repr
  funext sheet
  change ((joinedPattern data star block hCard).candidate.resolution
    ((data.vertexPartition wall).repr sheet)).right.repr sheet = _
  rw [joined_resolution]
  rfl

theorem pasted_newEdge :
    (LocalResolution.paste (data.vertexPartition wall)
      (joinedPattern data star block hCard).candidate.resolution
      (joinedPattern data star block hCard).candidate.contracts).newEdge = data.vertexPartition wall := by
  apply SheetPartition.ext_repr
  funext sheet
  change ((joinedPattern data star block hCard).candidate.resolution
    ((data.vertexPartition wall).repr sheet)).newEdge.repr sheet = _
  rw [joined_resolution]
  rfl

theorem vertexPartition_endpoint (label : Fin 2) :
    (joinedPattern data star block hCard).candidate.datum.vertexPartition (endpoint target wall label) =
      data.vertexPartition wall := by
  fin_cases label
  · exact (GlobalResolution.expandedVertexPartition_old_wall data wall _).trans (pasted_left data star block hCard)
  · exact pasted_right data star block hCard

theorem new_edgePartition :
    (joinedPattern data star block hCard).candidate.datum.edgePartition
      (occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right none) =
      data.vertexPartition wall :=
  (GlobalResolution.expandedEdgePartition_new data wall _ _).trans (pasted_newEdge data star block hCard)

theorem old_target_incident (label : Fin 2) :
    occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right (some (star.edge label)) ∈
      GluingDatum.incidentEdges (target := graph target wall (joinedPattern data star block hCard).candidate.right)
        (endpoint target wall label) := by
  have hAt := star.edge_mem_incidentEdges label
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hAt ⊢
  rw [occurrenceEquiv_some]
  fin_cases label
  · exact (oldEnds_incident_oldVertex_iff target wall star.right (star.edge 0)).mpr ⟨hAt, star.right_edge_zero⟩
  · exact (oldEnds_incident_freshVertex_iff target wall star.right (star.edge 1)).mpr ⟨hAt, star.right_edge_one⟩

theorem new_target_incident (label : Fin 2) :
    occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right none ∈
      GluingDatum.incidentEdges (target := graph target wall (joinedPattern data star block hCard).candidate.right)
        (endpoint target wall label) := by
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [occurrenceEquiv_none]
  fin_cases label
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem target_incident_pair (label : Fin 2) :
    GluingDatum.incidentEdges (target := graph target wall (joinedPattern data star block hCard).candidate.right)
        (endpoint target wall label) =
      {occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right none,
        occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right (some (star.edge label))} := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · exact new_target_incident data star block hCard label
    · rw [Finset.mem_singleton] at hEdge
      exact hEdge ▸ old_target_incident data star block hCard label
  · have hNe : occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right none ≠
        occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right (some (star.edge label)) := by
      intro hEqual
      have hLabels := (occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right).injective hEqual
      cases hLabels
    rw [Finset.card_pair hNe]
    fin_cases label
    · exact le_of_eq (joined_target_valencies data star block hCard).1
    · exact le_of_eq (joined_target_valencies data star block hCard).2

theorem endpoint_eq_of_rel (label : Fin 2) (first second : Fin degree)
    (hRel : (data.vertexPartition wall).Rel first second) :
    (joinedPattern data star block hCard).candidate.datum.sourceEndpoint (endpoint target wall label) first =
      (joinedPattern data star block hCard).candidate.datum.sourceEndpoint (endpoint target wall label) second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change ((joinedPattern data star block hCard).candidate.datum.vertexPartition
      (endpoint target wall label)).repr first =
      ((joinedPattern data star block hCard).candidate.datum.vertexPartition (endpoint target wall label)).repr second
    rw [vertexPartition_endpoint]
    exact hRel

/-- Literal same-sheet incidence of the retained occurrence in its assigned
direction. This handles the old target edge's stored orientation internally. -/
theorem oldSourceEdge_incident_endpoint (label : Fin 2) (sheet : Fin degree) :
    Incident (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.oldSourceEdge (data.sourceEdge (star.edge label) sheet))
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint (endpoint target wall label) sheet) := by
  let candidate := (joinedPattern data star block hCard).candidate
  have h := incident_sourceEdge_sourceEndpoint candidate.datum (endpoint target wall label)
    (occurrenceEquiv target wall candidate.right (some (star.edge label)))
    (old_target_incident data star block hCard label) sheet
  have hEqual : candidate.datum.sourceEdge (occurrenceEquiv target wall candidate.right (some (star.edge label))) sheet =
      candidate.oldSourceEdge (data.sourceEdge (star.edge label) sheet) :=
    ResolutionSideCounts.sourceEdge_old data wall candidate.right
      (LocalResolution.paste _ candidate.resolution candidate.contracts)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) _ sheet
  exact hEqual ▸ h

theorem newSourceEdge_incident_endpoint (label : Fin 2) (sheet : Fin degree) :
    Incident (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.newSourceEdge sheet)
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint (endpoint target wall label) sheet) := by
  let candidate := (joinedPattern data star block hCard).candidate
  have h := GlobalResolution.sourceEnds_newSourceEdge data wall candidate.right
    (LocalResolution.paste _ candidate.resolution candidate.contracts)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) sheet
  fin_cases label
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (congrArg Prod.snd h)

/-- Retain an actual occurrence, not merely a canonical sheet expression,
at the endpoint of its target direction and its old wall block. -/
theorem oldSourceEdge_incident_of_target_rel (label : Fin 2) (edge : data.SourceEdge)
    (hTarget : edge.1.1 = star.edge label) (anchor : Fin degree)
    (hRel : (data.vertexPartition wall).Rel anchor edge.1.2) :
    Incident (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.oldSourceEdge edge)
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint (endpoint target wall label) anchor) := by
  have h := oldSourceEdge_incident_endpoint data star block hCard label edge.1.2
  have hEdge : data.sourceEdge (star.edge label) edge.1.2 = edge := by
    rw [← hTarget]
    exact GluingDatum.sourceEdge_self data edge
  rw [hEdge] at h
  exact endpoint_eq_of_rel data star block hCard label edge.1.2 anchor hRel.symm ▸ h

theorem newSourceEdge_eq_of_rel (first second : Fin degree)
    (hRel : (data.vertexPartition wall).Rel first second) :
    (joinedPattern data star block hCard).candidate.newSourceEdge first =
      (joinedPattern data star block hCard).candidate.newSourceEdge second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (LocalResolution.paste (data.vertexPartition wall)
      (joinedPattern data star block hCard).candidate.resolution
      (joinedPattern data star block hCard).candidate.contracts).newEdge.repr first =
      (LocalResolution.paste (data.vertexPartition wall)
        (joinedPattern data star block hCard).candidate.resolution
        (joinedPattern data star block hCard).candidate.contracts).newEdge.repr second
    rw [pasted_newEdge]
    exact hRel

theorem newSourceEdge_sheet (sheet : Fin degree) :
    ((joinedPattern data star block hCard).candidate.newSourceEdge sheet).1.2 =
      (data.vertexPartition wall).repr sheet := by
  change ((joinedPattern data star block hCard).candidate.resolution
    ((data.vertexPartition wall).repr sheet)).newEdge.repr sheet = _
  rw [joined_resolution]
  rfl

/-- The joined new occurrences are in bijection with old wall blocks,
including background blocks of arbitrary cardinality. -/
theorem newSourceEdge_eq_iff_rel (first second : Fin degree) :
    (joinedPattern data star block hCard).candidate.newSourceEdge first =
        (joinedPattern data star block hCard).candidate.newSourceEdge second ↔
      (data.vertexPartition wall).Rel first second := by
  constructor
  · intro hEqual
    exact (newSourceEdge_sheet data star block hCard first).symm.trans
      ((congrArg (fun edge ↦ edge.1.2) hEqual).trans (newSourceEdge_sheet data star block hCard second))
  · exact newSourceEdge_eq_of_rel data star block hCard first second

/-- Each endpoint has one new occurrence per old wall block, plus exactly
the old occurrences in its assigned direction. -/
theorem card_incident_endpoint (label : Fin 2) (sheet : Fin degree) :
    Fintype.card (IncidentSourceEdge (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint (endpoint target wall label) sheet)) =
      1 + (data.edgePartition (star.edge label)).blockCountWithin (data.vertexPartition wall) sheet := by
  classical
  let candidate := (joinedPattern data star block hCard).candidate
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  change (∑ edge ∈ GluingDatum.incidentEdges (endpoint target wall label),
    (candidate.datum.edgePartition edge).blockCountWithin
      (candidate.datum.vertexPartition (endpoint target wall label))
      ((candidate.datum.vertexPartition (endpoint target wall label)).repr sheet)) = _
  rw [target_incident_pair]
  have hNe : occurrenceEquiv target wall candidate.right none ≠
      occurrenceEquiv target wall candidate.right (some (star.edge label)) := by
    intro hEqual
    have hLabels := (occurrenceEquiv target wall candidate.right).injective hEqual
    cases hLabels
  rw [Finset.sum_pair hNe, vertexPartition_endpoint, new_edgePartition]
  have hOld : candidate.datum.edgePartition (occurrenceEquiv target wall candidate.right (some (star.edge label))) =
      data.edgePartition (star.edge label) := GlobalResolution.expandedEdgePartition_old data wall _ _ _
  rw [hOld, SheetPartition.blockCountWithin_self]
  unfold SheetPartition.blockCountWithin
  rw [(data.vertexPartition wall).block_eq_of_rel ((data.vertexPartition wall).rel_repr_left sheet)]

variable {data star block hCard}

theorem card_incident_distinguished_endpoint
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (label : Fin 2) :
    Fintype.card (IncidentSourceEdge (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint (endpoint target wall label) block.1)) = 3 := by
  rw [card_incident_endpoint,
    SheetPartition.blockCountWithin_eq_blockCard_of_refines_splitBlock _ _ _ _
      (exterior_refines_splitBlock profile hCard _ (star.edge_mem_incidentEdges label)) rfl, hCard]

end DraismaVargas.LocalCases.M11JoinedGeometry
