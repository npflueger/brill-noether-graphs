module

public import DraismaVargas.LocalCases.W3R1SourceProfile

@[expose] public section

/-!
# Part II valency-three anchor classifier

Source: Vargas, Part II, Section 5.3, case `{v3-nd4}`.  At the
distinguished ramification-one block with four surviving occurrences, their
index sum is `2|A|+1`.  Harmonicity bounds the survivor-index sum in each
literal target direction by `|A|`; hence the trivalent target cannot use only
two directions.  Thus all three actual directions occur, and the occurrence
counts are exactly `2+1+1`.

The ramification-one equality is an explicit input here.  Producing it from
an incoming one-row degeneration is the separate `lemma-above-w0` rigidity
step, proved in `NonTrivalentValencyThreeRigidity`: the anchor carries the
target change in the valency-three case.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor

open DraismaVargas.Infrastructure
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable def activeTargets (data : GluingDatum target degree)
    (block : WallBlock data wall) : Finset target.edges := by
  classical
  exact (survivors data block).image fun edge ↦ edge.1.1.1

@[simp] theorem mem_activeTargets (data : GluingDatum target degree)
    (block : WallBlock data wall) (edge : target.edges) :
    edge ∈ activeTargets data block ↔
      ∃ sourceEdge ∈ survivors data block, sourceEdge.1.1.1 = edge := by
  classical
  simp [activeTargets]

theorem activeTargets_subset_incidentEdges (data : GluingDatum target degree)
    (block : WallBlock data wall) :
    activeTargets data block ⊆ GluingDatum.incidentEdges wall := by
  intro edge hEdge
  obtain ⟨sourceEdge, _, rfl⟩ := (mem_activeTargets data block edge).mp hEdge
  have h := (incident_iff_target_mem_and_rel data sourceEdge.1
    (WallBlock.sourceVertex data wall block)).mp sourceEdge.2 |>.1
  simpa only [WallBlock.sourceVertex, GluingDatum.sourceEndpoint] using h

theorem sum_survivor_index_le_activeTargets
    (data : GluingDatum target degree) (block : WallBlock data wall) :
    (∑ edge ∈ survivors data block, (data.sourceEdgeIndex edge.1 : ℤ)) ≤
      (activeTargets data block).card *
        (data.vertexPartition wall).blockCard block.1 := by
  classical
  let vertex := WallBlock.sourceVertex data wall block
  let mapTarget : IncidentSourceEdge data vertex → target.edges := fun edge ↦ edge.1.1.1
  have hFiber (targetEdge : target.edges) (hTarget : targetEdge ∈ activeTargets data block) :
      (∑ edge ∈ (survivors data block).filter (fun edge ↦ mapTarget edge = targetEdge),
        (data.sourceEdgeIndex edge.1 : ℤ)) ≤
        ((data.vertexPartition wall).blockCard block.1 : ℤ) := by
    have hAt := activeTargets_subset_incidentEdges data block hTarget
    have hAt' : targetEdge ∈ GluingDatum.incidentEdges vertex.1.1 := by
      change targetEdge ∈ GluingDatum.incidentEdges wall
      exact hAt
    have hBound := sum_index_le_of_same_target data vertex
      ((survivors data block).filter (fun edge ↦ mapTarget edge = targetEdge))
      targetEdge hAt' (by
        intro edge hEdge
        exact (Finset.mem_filter.mp hEdge).2)
    simpa only [vertex, WallBlock.sourceVertex, GluingDatum.sourceEndpoint, block.2] using hBound
  calc
    (∑ edge ∈ survivors data block, (data.sourceEdgeIndex edge.1 : ℤ)) =
        ∑ targetEdge ∈ activeTargets data block,
          ∑ edge ∈ (survivors data block).filter (fun edge ↦ mapTarget edge = targetEdge),
            (data.sourceEdgeIndex edge.1 : ℤ) := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (s := survivors data block) (t := activeTargets data block)
        (g := mapTarget) (fun edge hEdge ↦
          (mem_activeTargets data block (mapTarget edge)).2 ⟨edge, hEdge, rfl⟩)
        (fun edge ↦ (data.sourceEdgeIndex edge.1 : ℤ))]
    _ ≤ ∑ _targetEdge ∈ activeTargets data block,
          ((data.vertexPartition wall).blockCard block.1 : ℤ) := by
      exact Finset.sum_le_sum hFiber
    _ = (activeTargets data block).card *
        (data.vertexPartition wall).blockCard block.1 := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Ramification one and four surviving occurrences force all three target
directions to occur. -/
theorem activeTargets_card_eq_three
    (data : GluingDatum target degree) (star : ThreeStar target wall)
    (hNoGlue : DanglingEdgeNoGlue data) (block : WallBlock data wall)
    (hR : data.localRamification wall block = 1)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 4) :
    (activeTargets data block).card = 3 := by
  have hUpper := Finset.card_le_card (activeTargets_subset_incidentEdges data block)
  rw [star.card_incidentEdges] at hUpper
  have hSum := sum_survivor_index hNoGlue block hR
  rw [hNd] at hSum
  have hBound := sum_survivor_index_le_activeTargets data block
  have hBlockPos := (data.vertexPartition wall).blockCard_pos block.1
  by_contra hNe
  have hAtMostTwo : (activeTargets data block).card ≤ 2 := by omega
  interval_cases hCard : (activeTargets data block).card <;>
    norm_num at hBound <;> omega

/-- Hence the active target set is literally the whole trivalent star. -/
theorem activeTargets_eq_incidentEdges
    (data : GluingDatum target degree) (star : ThreeStar target wall)
    (hNoGlue : DanglingEdgeNoGlue data) (block : WallBlock data wall)
    (hR : data.localRamification wall block = 1)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 4) :
    activeTargets data block = GluingDatum.incidentEdges wall := by
  apply Finset.eq_of_subset_of_card_le (activeTargets_subset_incidentEdges data block)
  rw [activeTargets_card_eq_three data star hNoGlue block hR hNd,
    star.card_incidentEdges]

/-- The actual incident target occurrence named by a ThreeStar label. -/
def directionEdge (star : ThreeStar target wall) (label : Fin 3) : target.edges :=
  (star.label label).1

theorem directionEdge_mem_incidentEdges (star : ThreeStar target wall) (label : Fin 3) :
    directionEdge star label ∈ GluingDatum.incidentEdges wall :=
  (star.label label).2

theorem directionEdge_injective (star : ThreeStar target wall) :
    Function.Injective (directionEdge star) := by
  intro first second hEq
  apply star.label.injective
  exact Subtype.ext hEq

/-- Label the literal target occurrence of an actual incident source flag. -/
noncomputable def survivorLabel (data : GluingDatum target degree)
    (star : ThreeStar target wall)
    (block : WallBlock data wall)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) : Fin 3 :=
  star.label.symm ⟨edge.1.1.1, by
    have h := (incident_iff_target_mem_and_rel data edge.1
      (WallBlock.sourceVertex data wall block)).mp edge.2 |>.1
    simpa only [WallBlock.sourceVertex, GluingDatum.sourceEndpoint] using h⟩

theorem directionEdge_survivorLabel (data : GluingDatum target degree)
    (star : ThreeStar target wall) (block : WallBlock data wall)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    directionEdge star (survivorLabel data star block edge) = edge.1.1.1 := by
  exact congrArg Subtype.val (star.label.apply_symm_apply _)

/-- The surviving actual source occurrences in one named target direction. -/
noncomputable def directionSurvivors (data : GluingDatum target degree)
    (star : ThreeStar target wall) (block : WallBlock data wall) (label : Fin 3) :
    Finset (IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :=
  (survivors data block).filter fun edge ↦ survivorLabel data star block edge = label

@[simp] theorem mem_directionSurvivors (data : GluingDatum target degree)
    (star : ThreeStar target wall) (block : WallBlock data wall) (label : Fin 3)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    edge ∈ directionSurvivors data star block label ↔
      edge ∈ survivors data block ∧ edge.1.1.1 = directionEdge star label := by
  classical
  rw [directionSurvivors, Finset.mem_filter]
  constructor
  · rintro ⟨hSurvives, hLabel⟩
    exact ⟨hSurvives, (directionEdge_survivorLabel data star block edge).symm.trans
      (congrArg (directionEdge star) hLabel)⟩
  · rintro ⟨hSurvives, hTarget⟩
    refine ⟨hSurvives, ?_⟩
    apply directionEdge_injective star
    rw [directionEdge_survivorLabel]
    exact hTarget

/-- The three direction fibres partition all surviving actual incidences. -/
theorem sum_card_directionSurvivors (data : GluingDatum target degree)
    (star : ThreeStar target wall) (block : WallBlock data wall) :
    ∑ label : Fin 3, (directionSurvivors data star block label).card =
      (survivors data block).card := by
  classical
  simp_rw [Finset.card_eq_sum_ones]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := survivors data block) (t := (Finset.univ : Finset (Fin 3)))
    (g := survivorLabel data star block) (fun _ _ ↦ Finset.mem_univ _)
    (fun _ ↦ 1)]
  rfl

/-- The exact source-facing `2+1+1` incidence distribution.  Counts are of
literal source occurrences, and labels name literal target occurrences. -/
def DirectionDistribution (data : GluingDatum target degree)
    (star : ThreeStar target wall) (block : WallBlock data wall) : Prop :=
  ∃ doubled : Fin 3,
    (directionSurvivors data star block doubled).card = 2 ∧
      ∀ label, label ≠ doubled →
        (directionSurvivors data star block label).card = 1

namespace DirectionDistribution

variable {data : GluingDatum target degree} {star : ThreeStar target wall}
  {block : WallBlock data wall}

/-- The unique target direction containing two surviving occurrences. -/
noncomputable def doubledDirection
    (source : DirectionDistribution data star block) : Fin 3 :=
  Classical.choose source

theorem doubled_count (source : DirectionDistribution data star block) :
    (directionSurvivors data star block source.doubledDirection).card = 2 :=
  (Classical.choose_spec source).1

theorem other_count (source : DirectionDistribution data star block)
    (label : Fin 3) (hNe : label ≠ source.doubledDirection) :
    (directionSurvivors data star block label).card = 1 :=
  (Classical.choose_spec source).2 label hNe

end DirectionDistribution

/-- Four survivors at a ramification-one trivalent wall have exactly one
doubled target direction and one occurrence in each other direction. -/
theorem directionDistribution
    (data : GluingDatum target degree) (star : ThreeStar target wall)
    (hNoGlue : DanglingEdgeNoGlue data) (block : WallBlock data wall)
    (hR : data.localRamification wall block = 1)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 4) :
    DirectionDistribution data star block := by
  have hPositive (label : Fin 3) :
      0 < (directionSurvivors data star block label).card := by
    have hActive : directionEdge star label ∈ activeTargets data block := by
      rw [activeTargets_eq_incidentEdges data star hNoGlue block hR hNd]
      exact directionEdge_mem_incidentEdges star label
    obtain ⟨edge, hEdge, hTarget⟩ := (mem_activeTargets data block _).mp hActive
    exact Finset.card_pos.mpr ⟨edge,
      (mem_directionSurvivors data star block label edge).2 ⟨hEdge, hTarget⟩⟩
  have hSum := sum_card_directionSurvivors data star block
  rw [card_survivors, hNd, Fin.sum_univ_three] at hSum
  have h0 := hPositive 0
  have h1 := hPositive 1
  have h2 := hPositive 2
  have hLabels (label : Fin 3) : label = 0 ∨ label = 1 ∨ label = 2 := by
    have hLt := label.isLt
    rcases Nat.eq_zero_or_pos label.val with hZero | hPositive
    · left
      apply Fin.ext
      exact hZero
    · have hLeTwo : label.val ≤ 2 := by omega
      have hOneOrTwo : label.val = 1 ∨ label.val = 2 := by omega
      rcases hOneOrTwo with hOne | hTwo
      · right; left
        apply Fin.ext
        exact hOne
      · right; right
        apply Fin.ext
        exact hTwo
  have hCases :
      (directionSurvivors data star block 0).card = 2 ∨
      (directionSurvivors data star block 1).card = 2 ∨
      (directionSurvivors data star block 2).card = 2 := by
    omega
  rcases hCases with hDouble | hDouble | hDouble
  · refine ⟨0, hDouble, ?_⟩
    intro label hNe
    rcases hLabels label with rfl | rfl | rfl
    · exact (hNe rfl).elim
    · omega
    · omega
  · refine ⟨1, hDouble, ?_⟩
    intro label hNe
    rcases hLabels label with rfl | rfl | rfl
    · omega
    · exact (hNe rfl).elim
    · omega
  · refine ⟨2, hDouble, ?_⟩
    intro label hNe
    rcases hLabels label with rfl | rfl | rfl
    · omega
    · omega
    · exact (hNe rfl).elim

/-- The modular source classifier for case `{v3-nd4}`.  Its sets and counts
refer to literal target occurrences and literal surviving source incidences;
there is no supplied active-label pattern. -/
structure ThreeBranchAnchor (data : GluingDatum target degree)
    (star : ThreeStar target wall) (block : WallBlock data wall) : Prop where
  active_all : activeTargets data block = GluingDatum.incidentEdges wall
  distribution : DirectionDistribution data star block
  survivor_index_sum :
    (∑ edge ∈ survivors data block, (data.sourceEdgeIndex edge.1 : ℤ)) =
      2 * ((data.vertexPartition wall).blockCard block.1 : ℤ) + 1

/-- Actual producer of the valency-three anchor from no-glue, ramification
one, and the distinguished block's surviving valency four. -/
theorem threeBranchAnchor
    (data : GluingDatum target degree) (star : ThreeStar target wall)
    (hNoGlue : DanglingEdgeNoGlue data) (block : WallBlock data wall)
    (hR : data.localRamification wall block = 1)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 4) :
    ThreeBranchAnchor data star block := by
  refine ⟨activeTargets_eq_incidentEdges data star hNoGlue block hR hNd,
    directionDistribution data star hNoGlue block hR hNd, ?_⟩
  have hSum := sum_survivor_index hNoGlue block hR
  rw [hNd] at hSum
  norm_num at hSum
  linarith

end DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
