module

public import DraismaVargas.LocalCases.M11JoinedBackground
public import DraismaVargas.LocalCases.ResolutionAwayFromWall

@[expose] public section

/-!
# Induced stable-row map for the actual joined M11 resolution

Source: Draisma--Vargas Part I, the induced-labelling paragraph following the
non-dangling-union lemma (`lemma-class-union`), and the joined resolution of
Figure 32 (Case {w2-r2-nd3-M-11}, abbreviated M11). Retain any surviving occurrence
of an old stable path. Away from the wall consecutive occurrences still
meet at surviving valency two. At the wall a valency-two block cannot be the
distinguished nd3 block; its two retained directions are connected through
the actual divalent background new occurrence. Thus the chosen occurrence
does not affect the resulting stable row.

Every new surviving occurrence is connected to a retained one, so the map is
also surjective. The reverse local checks proving injectivity are in
`M11JoinedRowDescent`; `M11JoinedLimitMatrix` compares the retained columns.
-/

namespace DraismaVargas.LocalCases.M11JoinedStableLift

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11SourceCandidates M11JoinedBackground ResolutionAwayFromWall

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

/-- In an unramified background block there is just one original occurrence
in each target direction, so an incident occurrence is the canonical one. -/
theorem background_sourceEdge_eq (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (label : Fin 2) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet)
    (edge : data.SourceEdge) (hTarget : edge.1.1 = star.edge label)
    (hRel : (data.vertexPartition wall).Rel sheet edge.1.2) :
    data.sourceEdge (star.edge label) sheet = edge := by
  have hBlocks := SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ _
    (star.edgePartition_refines_wall data label) sheet
    (background_blockCount input profile label sheet hBackground)
  have hMember := ((data.vertexPartition wall).mem_block_iff sheet edge.1.2).mpr hRel
  rw [← hBlocks] at hMember
  have hFine := ((data.edgePartition (star.edge label)).mem_block_iff sheet edge.1.2).mp hMember
  calc
    data.sourceEdge (star.edge label) sheet = data.sourceEdge (star.edge label) edge.1.2 := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact hFine
    _ = data.sourceEdge edge.1.1 edge.1.2 := congrArg (fun place ↦ data.sourceEdge place edge.1.2) hTarget.symm
    _ = edge := GluingDatum.sourceEdge_self data edge

theorem background_of_wall_valency_two
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (vertex : data.SourceVertex) (hAt : vertex.1.1 = wall)
    (hValency : nonDanglingValency data vertex = 2) :
    ¬ (data.vertexPartition wall).Rel block.1 vertex.1.2 := by
  intro hRel
  have hVertex : WallBlock.sourceVertex data wall block = vertex :=
    (data.sourceEndpoint_eq_iff wall block.1 vertex).mpr ⟨hAt.symm, hRel⟩
  have hValency' := congrArg (nonDanglingValency data) hVertex
  rw [profile.valency, hValency] at hValency'
  omega

/-- Any surviving occurrence incident to this background wall vertex has the
same lifted row as its actual new occurrence. The target direction is found
from incidence, not supplied by a row receipt. -/
theorem retained_stablePath_eq_background (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (vertex : data.SourceVertex) (hAt : vertex.1.1 = wall)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 vertex.1.2)
    (edge : NonDanglingEdge data) (hIncident : Incident data edge.1 vertex) :
    ∃ hNew : ¬ IsDangling (joinedPattern data star block hCard).candidate.datum
        ((joinedPattern data star block hCard).candidate.newSourceEdge vertex.1.2),
      (retainedEdge (joinedPattern data star block hCard).candidate input.valid.1 edge).stablePath =
        NonDanglingEdge.stablePath ⟨(joinedPattern data star block hCard).candidate.newSourceEdge vertex.1.2, hNew⟩ := by
  have hData := (incident_iff_target_mem_and_rel data edge.1 vertex).mp hIncident
  rw [hAt] at hData
  obtain ⟨label, hLabel⟩ := star.label.surjective ⟨edge.1.1.1, hData.1⟩
  have hTarget : edge.1.1.1 = star.edge label := (congrArg Subtype.val hLabel).symm
  have hCanonical := background_sourceEdge_eq input profile label vertex.1.2 hBackground edge.1 hTarget hData.2
  have hSurvives : ¬ IsDangling data (data.sourceEdge (star.edge label) vertex.1.2) := by
    rw [hCanonical]
    exact edge.2
  refine ⟨background_survives input profile hCard label vertex.1.2 hBackground hSurvives, ?_⟩
  have hPath := (background_stablePath_eq_retained input profile hCard label vertex.1.2 hBackground hSurvives).symm
  have hEdge : (retainedEdge (joinedPattern data star block hCard).candidate input.valid.1 edge) =
      (⟨(joinedPattern data star block hCard).candidate.oldSourceEdge
          (data.sourceEdge (star.edge label) vertex.1.2),
        ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hSurvives⟩ :
          NonDanglingEdge (joinedPattern data star block hCard).candidate.datum) :=
    Subtype.ext (congrArg (joinedPattern data star block hCard).candidate.oldSourceEdge hCanonical.symm)
  exact (congrArg NonDanglingEdge.stablePath hEdge).trans hPath

theorem stablePath_retained_eq_of_consecutive (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (first second : NonDanglingEdge data) (hConsecutive : Consecutive data first second) :
    (retainedEdge (joinedPattern data star block hCard).candidate input.valid.1 first).stablePath =
      (retainedEdge (joinedPattern data star block hCard).candidate input.valid.1 second).stablePath := by
  classical
  obtain ⟨hNe, vertex, hFirst, hSecond, hValency⟩ := hConsecutive
  by_cases hAt : vertex.1.1 = wall
  · have hBackground := background_of_wall_valency_two profile vertex hAt hValency
    obtain ⟨hNewFirst, hFirstPath⟩ := retained_stablePath_eq_background input profile hCard vertex hAt hBackground first hFirst
    obtain ⟨hNewSecond, hSecondPath⟩ := retained_stablePath_eq_background input profile hCard vertex hAt hBackground second hSecond
    exact hFirstPath.trans hSecondPath.symm
  · exact stablePath_eq_of_consecutive (consecutive_retained_of_away
      (joinedPattern data star block hCard).candidate input.valid
      (M11SourceGenus.joined_sourceGenus data star block hCard) first second hNe vertex hAt hFirst hSecond hValency)

/-- The paper's induced stable-row map, evaluated by retaining any actual
surviving occurrence of the old row. Its independence of that choice is
kernel checked against the defining consecutive relation. -/
noncomputable def stablePathLift (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    StablePath data → StablePath (joinedPattern data star block hCard).candidate.datum :=
  Quot.lift (fun edge ↦ (retainedEdge (joinedPattern data star block hCard).candidate input.valid.1 edge).stablePath)
    (stablePath_retained_eq_of_consecutive input profile hCard)

@[simp] theorem stablePathLift_mk (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (edge : NonDanglingEdge data) :
    stablePathLift input profile hCard edge.stablePath =
      (retainedEdge (joinedPattern data star block hCard).candidate input.valid.1 edge).stablePath := rfl

/-- No stable row is created entirely inside the new fibre: its distinguished
occurrence joins `e3`, and every background occurrence joins either retained
direction. This is a statement about all actual surviving occurrences. -/
theorem exists_retained_row (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (edge : NonDanglingEdge (joinedPattern data star block hCard).candidate.datum) :
    ∃ old : NonDanglingEdge data,
      (retainedEdge (joinedPattern data star block hCard).candidate input.valid.1 old).stablePath = edge.stablePath := by
  classical
  let candidate := (joinedPattern data star block hCard).candidate
  obtain ⟨edge, hSurvives⟩ := edge
  rcases ResolutionPruning.sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨sheet, rfl⟩
  · have hOld : ¬ IsDangling data old := fun h ↦ hSurvives
      ((ResolutionPruning.isDangling_oldSourceEdge_iff candidate input.valid
        (M11SourceGenus.joined_sourceGenus data star block hCard) old).mpr h)
    exact ⟨⟨old, hOld⟩, rfl⟩
  · by_cases hRel : (data.vertexPartition wall).Rel block.1 sheet
    · exact ⟨⟨profile.third.1, profile.third_survives⟩,
        (M11JoinedSurvival.joined_new_stablePath_eq_retained input profile hCard sheet hRel).symm⟩
    · have hOld : ¬ IsDangling data (data.sourceEdge (star.edge 0) sheet) := fun h ↦ hSurvives
        ((background_isDangling_iff input profile hCard 0 sheet hRel).mpr h)
      exact ⟨⟨data.sourceEdge (star.edge 0) sheet, hOld⟩,
        (background_stablePath_eq_retained input profile hCard 0 sheet hRel hOld).symm⟩

theorem stablePathLift_surjective (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    Function.Surjective (stablePathLift input profile hCard) := by
  intro path
  induction path using Quot.inductionOn with
  | h edge =>
      obtain ⟨old, hPath⟩ := exists_retained_row input profile hCard edge
      exact ⟨old.stablePath, hPath⟩

end DraismaVargas.LocalCases.M11JoinedStableLift
