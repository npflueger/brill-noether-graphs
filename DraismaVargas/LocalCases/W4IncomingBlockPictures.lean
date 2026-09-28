import DraismaVargas.LocalCases.W4IncomingSheetClasses
import DraismaVargas.LocalCases.W4IncomingBlockRelations
import DraismaVargas.LocalCases.W4IncomingInternalRelations

/-!
# Actual auxiliary pictures determine incoming W4 block patterns

Source: Draisma--Vargas Part I, the non-dangling union lemma
(`lemma-class-union`) and Case {aux-r0}, at a wall of Case {w4} (a four-valent
wall vertex, abbreviated W4). The flags below are the ones stored in
`AuxR0Nd2Picture` and `AuxR0Nd3Picture`.
Their incidences, distinctness and valencies are derived from the literal
picture fields, before applying the incoming side and sheet-class census.
-/

namespace DraismaVargas.LocalCases.W4IncomingBlockPictures

open DraismaVargas.Infrastructure GraphContraction GluingContraction ContractionRamification
open W4StableSource W4Assembly W4IncomingRetainedFlags W4IncomingSheetClasses
open FullDimensionalSource FullContractionFibre PrunedFibreValency PrunedFibreTree WallDegeneration

section Wall

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  (data : GluingDatum target degree) (star : W4TargetPairings.FourStar target wall)
  (sourceBlock : WallBlock data wall)

/-- A canonical labelled occurrence meets the actual wall block of its sheet. -/
theorem flag_incident (label : Fin 4) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet) :
    Incident data (data.sourceEdge (star.edge label) sheet)
      (WallBlock.sourceVertex data wall sourceBlock) := by
  apply (incident_iff_target_mem_and_rel data _ _).mpr
  refine ⟨star.edge_mem_incidentEdges label, ?_⟩
  change (data.vertexPartition wall).Rel ((data.vertexPartition wall).repr sourceBlock.1)
    ((data.edgePartition (star.edge label)).repr sheet)
  rw [sourceBlock.2]
  exact hSheet.trans ((star.edgePartition_refines_wall data label).rel
      ((data.edgePartition (star.edge label)).rel_repr_right sheet))

/-- The nd2 picture's two stored literal flags have distinct target occurrences. -/
theorem nd2_flags_ne {model : Nd2Block}
    (picture : AuxR0Nd2Picture data star sourceBlock model) : picture.first ≠ picture.second := by
  intro h
  exact model.distinct (star.edge_injective
    (congrArg (fun edge : NonDanglingEdge data ↦ edge.1.1.1) h))

/-- The actual nd2 picture exhausts the whole surviving neighbourhood. -/
theorem nd2_nonDanglingIncident {model : Nd2Block}
    (picture : AuxR0Nd2Picture data star sourceBlock model) :
    nonDanglingIncident data (WallBlock.sourceVertex data wall sourceBlock) =
      {picture.first.1, picture.second.1} := by
  classical
  ext edge
  constructor
  · intro h
    obtain ⟨hSurvives, hInc⟩ := (mem_nonDanglingIncident data _ edge).mp h
    obtain ⟨hAt, hRel⟩ := (incident_iff_target_mem_and_rel data edge _).mp hInc
    change (data.vertexPartition wall).Rel ((data.vertexPartition wall).repr sourceBlock.1) edge.1.2 at hRel
    rw [sourceBlock.2] at hRel
    obtain ⟨label, hLabel⟩ := star.exists_edge_eq edge.1.1 hAt
    exact Finset.mem_insert.mpr ((picture.only_surviving edge
      (WallBlock.ofSheet_eq_of_rel data wall sourceBlock edge.1.2 hRel)
      ⟨label, hLabel⟩ hSurvives).imp id Finset.mem_singleton.mpr)
  · intro h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact (mem_nonDanglingIncident data _ _).mpr
        ⟨picture.first_survives, flag_incident data star sourceBlock model.first sourceBlock.1 rfl⟩
    · rw [Finset.mem_singleton.mp h]
      exact (mem_nonDanglingIncident data _ _).mpr
        ⟨picture.second_survives, flag_incident data star sourceBlock model.second sourceBlock.1 rfl⟩

theorem nd2_valency {model : Nd2Block}
    (picture : AuxR0Nd2Picture data star sourceBlock model) :
    nonDanglingValency data (WallBlock.sourceVertex data wall sourceBlock) = 2 := by
  rw [← card_nonDanglingIncident, nd2_nonDanglingIncident data star sourceBlock picture,
    Finset.card_pair]
  exact fun h ↦ nd2_flags_ne data star sourceBlock picture (Subtype.ext h)

/-- The canonical surviving occurrence stored by an active nd3 sheet. -/
noncomputable def nd3Flag {model : Nd3Block}
    (picture : AuxR0Nd3Picture data star sourceBlock model)
    (label : Fin 4) (hLabel : label ∈ model.activeLabels) : NonDanglingEdge data :=
  ⟨data.sourceEdge (star.edge label) (picture.activeSheet label), picture.active_survives label hLabel⟩

theorem nd3_flag_incident {model : Nd3Block}
    (picture : AuxR0Nd3Picture data star sourceBlock model)
    (label : Fin 4) (hLabel : label ∈ model.activeLabels) :
    Incident data (nd3Flag data star sourceBlock picture label hLabel).1
      (WallBlock.sourceVertex data wall sourceBlock) :=
  flag_incident data star sourceBlock label _ (picture.active_sheet label hLabel)

theorem nd3_flags_ne {model : Nd3Block}
    (picture : AuxR0Nd3Picture data star sourceBlock model)
    (first second : Fin 4) (hFirst : first ∈ model.activeLabels) (hSecond : second ∈ model.activeLabels)
    (hNe : first ≠ second) :
    nd3Flag data star sourceBlock picture first hFirst ≠ nd3Flag data star sourceBlock picture second hSecond := by
  intro h
  exact hNe (star.edge_injective (congrArg (fun edge : NonDanglingEdge data ↦ edge.1.1.1) h))

/-- The nd3 picture gives an exact labelled surviving-neighbourhood image. -/
theorem nd3_nonDanglingIncident {model : Nd3Block}
    (picture : AuxR0Nd3Picture data star sourceBlock model) :
    nonDanglingIncident data (WallBlock.sourceVertex data wall sourceBlock) =
      model.activeLabels.image (fun label ↦ data.sourceEdge (star.edge label) (picture.activeSheet label)) := by
  classical
  ext edge
  constructor
  · intro h
    obtain ⟨hSurvives, hInc⟩ := (mem_nonDanglingIncident data _ edge).mp h
    obtain ⟨hAt, hRel⟩ := (incident_iff_target_mem_and_rel data edge _).mp hInc
    change (data.vertexPartition wall).Rel ((data.vertexPartition wall).repr sourceBlock.1) edge.1.2 at hRel
    rw [sourceBlock.2] at hRel
    obtain ⟨label, hLabel⟩ := star.exists_edge_eq edge.1.1 hAt
    obtain ⟨label, hActive, hEdge⟩ := picture.only_surviving edge
      (WallBlock.ofSheet_eq_of_rel data wall sourceBlock edge.1.2 hRel) ⟨label, hLabel⟩ hSurvives
    exact Finset.mem_image.mpr ⟨label, hActive, hEdge.symm⟩
  · intro h
    obtain ⟨label, hLabel, rfl⟩ := Finset.mem_image.mp h
    exact (mem_nonDanglingIncident data _ _).mpr
      ⟨picture.active_survives label hLabel,
        flag_incident data star sourceBlock label _ (picture.active_sheet label hLabel)⟩

theorem nd3_valency {model : Nd3Block}
    (picture : AuxR0Nd3Picture data star sourceBlock model) :
    nonDanglingValency data (WallBlock.sourceVertex data wall sourceBlock) = 3 := by
  classical
  rw [← card_nonDanglingIncident, nd3_nonDanglingIncident data star sourceBlock picture,
    Finset.card_image_of_injective _ (by
      intro first second h
      exact star.edge_injective (congrArg (fun edge : data.SourceEdge ↦ edge.1.1) h))]
  simp [Nd3Block.activeLabels, model.first_ne_second, model.first_ne_third, model.second_ne_third]

/-- The dangling picture leaves no surviving wall incidence. -/
theorem dangling_valency
    (oldDangling : ∀ (edge : data.SourceEdge) (label : Fin 4),
      WallBlock.ofSheet data wall edge.1.2 = sourceBlock → star.edge label = edge.1.1 → IsDangling data edge) :
    nonDanglingValency data (WallBlock.sourceVertex data wall sourceBlock) = 0 := by
  rw [← card_nonDanglingIncident, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro edge h
  obtain ⟨hSurvives, hInc⟩ := (mem_nonDanglingIncident data _ edge).mp h
  obtain ⟨hAt, hRel⟩ := (incident_iff_target_mem_and_rel data edge _).mp hInc
  change (data.vertexPartition wall).Rel ((data.vertexPartition wall).repr sourceBlock.1) edge.1.2 at hRel
  rw [sourceBlock.2] at hRel
  obtain ⟨label, hLabel⟩ := star.exists_edge_eq edge.1.1 hAt
  exact hSurvives (oldDangling edge label
    (WallBlock.ofSheet_eq_of_rel data wall sourceBlock edge.1.2 hRel) hLabel)

end Wall

section Incoming

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*}
  [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)
  (hCompat : DanglingCompatible data hc hab hOne)
  (block : (mergedPartition data a b).Blocks)

local notation "M₀" => contractDatum data hc hab hOne
local notation "q" => W4IncomingTargetNormalization.pairing data fd hc hab hOne star

/-- The wall block retains the same canonical merged representative. -/
def wallBlock : WallBlock M₀ ⟨a, hab⟩ :=
  ⟨block.1, by
    rw [contractDatum_vertexPartition_merge]
    exact block.2⟩

local notation "B₀" => wallBlock data hc hab hOne block

/-- The two ways to name a merged source block agree literally. -/
theorem sourceVertex_eq_merged :
    WallBlock.sourceVertex M₀ ⟨a, hab⟩ B₀ = mergedVertex data hc hab hOne block := by
  apply Subtype.ext
  exact Prod.ext rfl (wallBlock data hc hab hOne block).2

include fd star hCompat

/-- The stored nd2 flags, on the same canonical pairing side, give the
actual empty internal fibre and all three whole-merged sheet classes. -/
theorem nd2_same_classes {model : Nd2Block}
    (picture : AuxR0Nd2Picture M₀ star B₀ model)
    (hSide : star.right q (star.edge model.first) = star.right q (star.edge model.second)) :
    internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = ∅ ∧
    (data.vertexPartition (endpoint data hc hab hOne picture.first.1).1.1).block
        (endpoint data hc hab hOne picture.first.1).1.2 = (mergedPartition data a b).block block.1 ∧
    ((M₀).edgePartition picture.first.1.1.1).block picture.first.1.1.2 = (mergedPartition data a b).block block.1 ∧
    ((M₀).edgePartition picture.second.1.1.1).block picture.second.1.1.2 = (mergedPartition data a b).block block.1 := by
  have hNd := nd2_valency M₀ star B₀ picture
  rw [sourceVertex_eq_merged data hc hab hOne block] at hNd
  have hFirst := flag_incident M₀ star B₀ model.first block.1 rfl
  have hSecond := flag_incident M₀ star B₀ model.second block.1 rfl
  rw [sourceVertex_eq_merged data hc hab hOne block] at hFirst hSecond
  have hNe := nd2_flags_ne M₀ star B₀ picture
  have hCensus := nd2_same_pairing_side data fd hc hab hOne star hCompat block hNd
    picture.first picture.second hNe hFirst hSecond hSide
  have hClasses := nd2_same_side_classes data fd hc hab hOne star hCompat block hNd
    picture.first picture.second hNe hFirst hSecond hSide
  exact ⟨hCensus.2.2.1, hClasses⟩

/-- The stored nd2 flags on opposite pairing sides identify the unique
internal occurrence and both actual endpoint classes with the merged block. -/
theorem nd2_opposite_classes {model : Nd2Block}
    (picture : AuxR0Nd2Picture M₀ star B₀ model)
    (hSide : star.right q (star.edge model.first) ≠ star.right q (star.edge model.second)) :
    ∃ edge : data.SourceEdge,
      internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = {edge} ∧
      (data.edgePartition edge.1.1).block edge.1.2 = (mergedPartition data a b).block block.1 ∧
      (data.vertexPartition (endpoint data hc hab hOne picture.first.1).1.1).block
        (endpoint data hc hab hOne picture.first.1).1.2 = (mergedPartition data a b).block block.1 ∧
      (data.vertexPartition (endpoint data hc hab hOne picture.second.1).1.1).block
        (endpoint data hc hab hOne picture.second.1).1.2 = (mergedPartition data a b).block block.1 := by
  have hNd := nd2_valency M₀ star B₀ picture
  rw [sourceVertex_eq_merged data hc hab hOne block] at hNd
  have hFirst := flag_incident M₀ star B₀ model.first block.1 rfl
  have hSecond := flag_incident M₀ star B₀ model.second block.1 rfl
  rw [sourceVertex_eq_merged data hc hab hOne block] at hFirst hSecond
  exact nd2_opposite_side_classes data fd hc hab hOne star hCompat block hNd
    picture.first picture.second hFirst hSecond hSide

/-- Any ordering of the actual nd3 active labels with singleton first
derives the small and large incoming classes; the flags are constructed here. -/
theorem nd3_ordered_classes {model : Nd3Block}
    (picture : AuxR0Nd3Picture M₀ star B₀ model)
    (first second third : Fin 4)
    (hFirst : first ∈ model.activeLabels) (hSecond : second ∈ model.activeLabels)
    (hThird : third ∈ model.activeLabels) (hNe : second ≠ third)
    (hOpposite : star.right q (star.edge first) ≠ star.right q (star.edge second))
    (hSame : star.right q (star.edge second) = star.right q (star.edge third)) :
    ∃ edge : data.SourceEdge,
      internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = {edge} ∧
      (data.edgePartition edge.1.1).block edge.1.2 =
        ((M₀).edgePartition (star.edge first)).block (picture.activeSheet first) ∧
      (data.vertexPartition (endpoint data hc hab hOne
          ((M₀).sourceEdge (star.edge first) (picture.activeSheet first))).1.1).block
        (endpoint data hc hab hOne ((M₀).sourceEdge (star.edge first) (picture.activeSheet first))).1.2 =
          ((M₀).edgePartition (star.edge first)).block (picture.activeSheet first) ∧
      (data.vertexPartition (endpoint data hc hab hOne
          ((M₀).sourceEdge (star.edge second) (picture.activeSheet second))).1.1).block
        (endpoint data hc hab hOne ((M₀).sourceEdge (star.edge second) (picture.activeSheet second))).1.2 =
          (mergedPartition data a b).block block.1 := by
  have hNd := nd3_valency M₀ star B₀ picture
  rw [sourceVertex_eq_merged data hc hab hOne block] at hNd
  have hFirstInc := nd3_flag_incident M₀ star B₀ picture first hFirst
  have hSecondInc := nd3_flag_incident M₀ star B₀ picture second hSecond
  have hThirdInc := nd3_flag_incident M₀ star B₀ picture third hThird
  rw [sourceVertex_eq_merged data hc hab hOne block] at hFirstInc hSecondInc hThirdInc
  have hResult := nd3_singleton_side_classes data fd hc hab hOne star hCompat block hNd
    (nd3Flag M₀ star B₀ picture first hFirst) (nd3Flag M₀ star B₀ picture second hSecond)
    (nd3Flag M₀ star B₀ picture third hThird)
    (nd3_flags_ne M₀ star B₀ picture second third hSecond hThird hNe)
    hFirstInc hSecondInc hThirdInc hOpposite hSame
  simpa only [nd3Flag, GluingDatum.sourceEdge_target, GluingDatum.sourceEdge_sheet,
    SheetPartition.block_eq_of_rel _ (SheetPartition.rel_repr_left _ _)] using hResult

end Incoming

end DraismaVargas.LocalCases.W4IncomingBlockPictures
