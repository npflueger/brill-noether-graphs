module

public import DraismaVargas.LocalCases.W3ShiftIncomingMatching

@[expose] public section

namespace DraismaVargas.LocalCases.W3ShiftSelectedCensus

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties NonDanglingValency
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open IncomingTargetExpansion IncomingW2TargetPlacement TargetExpansion
open PrunedFibreValency PrunedFibreTree
open FullContractionFibre
open W4IncomingRetainedFlags
open W3Nd2IncomingTargetPlacement W3Nd2IncomingDirection
open W3Nd2IncomingSelectedCensus W3Nd2IncomingSheetClasses
open W3ShiftSourceCandidates

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
  {contracted : target.edges}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

/-! ## The three survivors of a shift profile -/

section Survivors

variable {wall : target.V} {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}

theorem moving_survives (shift : ShiftProfile input) : ¬ IsDangling data shift.moving.1 := by
  apply (mem_survivors data input.distinguishedBlock _).mp
  rw [shift.surviving]
  exact Finset.mem_insert_self _ _

theorem firstRest_survives (shift : ShiftProfile input) :
    ¬ IsDangling data shift.firstRest.1 := by
  apply (mem_survivors data input.distinguishedBlock _).mp
  rw [shift.surviving]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem secondRest_survives (shift : ShiftProfile input) :
    ¬ IsDangling data shift.secondRest.1 := by
  apply (mem_survivors data input.distinguishedBlock _).mp
  rw [shift.surviving]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

end Survivors

/-! ## The three canonical endpoints of a shift profile -/

section Endpoints

variable (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)

/-- The canonical same-sheet endpoint of the moving survivor `e_α`. -/
noncomputable abbrev movingEndpoint (shift : ShiftProfile input) : data.SourceVertex :=
  endpoint data hc hab hOne shift.moving.1

/-- The canonical same-sheet endpoint of the first retained survivor `e_β`. -/
noncomputable abbrev firstEndpoint (shift : ShiftProfile input) : data.SourceVertex :=
  endpoint data hc hab hOne shift.firstRest.1

/-- The canonical same-sheet endpoint of the second retained survivor `e_γ`. -/
noncomputable abbrev secondEndpoint (shift : ShiftProfile input) : data.SourceVertex :=
  endpoint data hc hab hOne shift.secondRest.1

end Endpoints

section Placement

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (shift : ShiftProfile input)
  (hMoving : shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star)

include fullDim hMoving

/-- The first retained direction is restored to the *other* original endpoint. -/
theorem first_side_ne :
    IncomingTargetExpansion.right hc hab hOne shift.firstTarget ≠
      IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) :=
  W3Nd3IncomingCensus.side_ne_of_ne_divalentOccurrence data hc hab hOne fullDim star _
    shift.firstTarget_mem (by rw [← hMoving]; exact fun h ↦ shift.moving_target_ne_first h.symm)

/-- The second retained direction is restored to the *other* original endpoint. -/
theorem second_side_ne :
    IncomingTargetExpansion.right hc hab hOne shift.secondTarget ≠
      IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) :=
  W3Nd3IncomingCensus.side_ne_of_ne_divalentOccurrence data hc hab hOne fullDim star _
    shift.secondTarget_mem (by rw [← hMoving]; exact fun h ↦ shift.moving_target_ne_second h.symm)

/-- Both retained survivors sit above one and the same original endpoint. -/
theorem first_second_endpoint_target_eq :
    (firstEndpoint data hc hab hOne star input shift).1.1 =
      (secondEndpoint data hc hab hOne star input shift).1.1 := by
  refine (endpoint_target_eq_iff data hc hab hOne shift.firstRest.1 shift.secondRest.1).mpr ?_
  have hFirst := first_side_ne data hc hab hOne fullDim star input shift hMoving
  have hSecond := second_side_ne data hc hab hOne fullDim star input shift hMoving
  revert hFirst hSecond
  cases IncomingTargetExpansion.right hc hab hOne shift.firstTarget <;>
    cases IncomingTargetExpansion.right hc hab hOne shift.secondTarget <;>
    cases IncomingTargetExpansion.right hc hab hOne
      (divalentOccurrence data hc hab hOne fullDim star) <;> simp

/-- The moving survivor sits above the *other* original endpoint from them. -/
theorem moving_endpoint_target_ne :
    (movingEndpoint data hc hab hOne star input shift).1.1 ≠
      (firstEndpoint data hc hab hOne star input shift).1.1 := by
  intro hEq
  refine first_side_ne data hc hab hOne fullDim star input shift hMoving ?_
  refine ((endpoint_target_eq_iff data hc hab hOne shift.firstRest.1 shift.moving.1).mp
    hEq.symm).trans ?_
  exact congrArg (IncomingTargetExpansion.right hc hab hOne) hMoving

/-- The original endpoint carrying both retained survivors is unramified. -/
theorem first_targetChange_eq_zero :
    data.targetChange (firstEndpoint data hc hab hOne star input shift).1.1 = 0 :=
  targetChange_endpoint_eq_zero_of_side_ne data fullDim hc hab hOne star shift.firstRest.1
    (first_side_ne data hc hab hOne fullDim star input shift hMoving)

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hMoving in
/-- It is one of the two original endpoints of the contracted occurrence. -/
theorem first_endpoint_target_mem :
    (firstEndpoint data hc hab hOne star input shift).1.1 = a ∨
      (firstEndpoint data hc hab hOne star input shift).1.1 = b :=
  W3Nd3IncomingCensus.endpoint_target_mem data hc hab hOne shift.firstRest.1

end Placement

/-! ## Two blocks above one original endpoint are disjoint -/

section Blocks

variable (data : GluingDatum target degree)

theorem not_mem_both_blocks (place : target.V) (first second : data.SourceVertex)
    (hFirst : first.1.1 = place) (hSecond : second.1.1 = place) (hNe : first ≠ second)
    (sheet : Fin degree)
    (hMemFirst : sheet ∈ (data.vertexPartition place).block first.1.2)
    (hMemSecond : sheet ∈ (data.vertexPartition place).block second.1.2) : False := by
  have hReprFirst : (data.vertexPartition place).repr first.1.2 = first.1.2 := by
    rw [← hFirst]; exact first.2
  have hReprSecond : (data.vertexPartition place).repr second.1.2 = second.1.2 := by
    rw [← hSecond]; exact second.2
  have hRelFirst := ((data.vertexPartition place).mem_block_iff _ _).mp hMemFirst
  have hRelSecond := ((data.vertexPartition place).mem_block_iff _ _).mp hMemSecond
  have hSheetEq : first.1.2 = second.1.2 := by
    have : (data.vertexPartition place).repr first.1.2 =
        (data.vertexPartition place).repr second.1.2 := hRelFirst.trans hRelSecond.symm
    rwa [hReprFirst, hReprSecond] at this
  exact hNe (Subtype.ext (Prod.ext (hFirst.trans hSecond.symm) hSheetEq))

/-- The same, with each block read at its own original endpoint. -/
theorem not_mem_both_blocks' (first second : data.SourceVertex)
    (hTarget : first.1.1 = second.1.1) (hNe : first ≠ second) (sheet : Fin degree)
    (hMemFirst : sheet ∈ (data.vertexPartition first.1.1).block first.1.2)
    (hMemSecond : sheet ∈ (data.vertexPartition second.1.1).block second.1.2) : False := by
  rw [← hTarget] at hMemSecond
  exact not_mem_both_blocks data first.1.1 first second rfl hTarget.symm hNe sheet
    hMemFirst hMemSecond

end Blocks

/-! ## The distinguished block has non-dangling valency three -/

section Valency

variable {wall : target.V} {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}

theorem shift_valency (shift : ShiftProfile input) :
    nonDanglingValency data
      (WallBlock.sourceVertex data wall input.distinguishedBlock) = 3 := by
  classical
  rw [← card_survivors, shift.surviving,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact fun h ↦ h.elim shift.moving_ne_first shift.moving_ne_second),
    Finset.card_pair shift.first_ne_second]

end Valency

/-! ## Both retained survivors have one and the same canonical endpoint -/

section Retained

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (shift : ShiftProfile input)

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem moving_incident_merged :
    Incident (contractDatum data hc hab hOne) shift.moving.1
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) := by
  rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input]
  exact shift.moving.2

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem firstRest_incident_merged :
    Incident (contractDatum data hc hab hOne) shift.firstRest.1
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) := by
  rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input]
  exact shift.firstRest.2

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem secondRest_incident_merged :
    Incident (contractDatum data hc hab hOne) shift.secondRest.1
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) := by
  rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input]
  exact shift.secondRest.2

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- Each survivor's class lies inside the distinguished wall block. -/
theorem survivor_block_subset_wall
    (edge : (contractDatum data hc hab hOne).SourceEdge)
    (hMem : edge.1.1 ∈ GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V))
    (hRel : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
      input.distinguishedBlock.1 edge.1.2) :
    ((contractDatum data hc hab hOne).edgePartition edge.1.1).block edge.1.2 ⊆
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block
        input.distinguishedBlock.1 := by
  intro sheet hSheet
  refine (SheetPartition.mem_block_iff _ _ _).mpr (hRel.trans ?_)
  exact (refines_of_mem_incidentEdges (contractDatum data hc hab hOne) hMem).rel
    ((SheetPartition.mem_block_iff _ _ _).mp hSheet)

variable (hMoving : shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star)

include fullDim hMoving

/-- **The two retained survivors share their canonical endpoint.**  If they did
not, their classes `e_β`, `e_γ` would sit in two *disjoint* blocks above the one
original endpoint that carries them both, while `k_β + k_γ = 2|A₀| − k_α > |A₀|`
by the case's own `k_α < |A₀|`. -/
theorem first_eq_second_endpoint :
    firstEndpoint data hc hab hOne star input shift =
      secondEndpoint data hc hab hOne star input shift := by
  classical
  by_contra hNe
  set wallBlock := ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block
    input.distinguishedBlock.1 with hWallBlock
  have hFirstSub : ((contractDatum data hc hab hOne).edgePartition shift.firstTarget).block
      shift.firstAnchor ⊆
      (data.vertexPartition (firstEndpoint data hc hab hOne star input shift).1.1).block
        (firstEndpoint data hc hab hOne star input shift).1.2 :=
    block_subset_endpoint_block data hc hab hOne (selectedBlock data hc hab hOne star input)
      shift.firstRest.1 (firstRest_incident_merged data hc hab hOne star input shift)
  have hSecondSub : ((contractDatum data hc hab hOne).edgePartition shift.secondTarget).block
      shift.secondAnchor ⊆
      (data.vertexPartition (secondEndpoint data hc hab hOne star input shift).1.1).block
        (secondEndpoint data hc hab hOne star input shift).1.2 :=
    block_subset_endpoint_block data hc hab hOne (selectedBlock data hc hab hOne star input)
      shift.secondRest.1 (secondRest_incident_merged data hc hab hOne star input shift)
  have hTargetEq := first_second_endpoint_target_eq data hc hab hOne fullDim star input
    shift hMoving
  have hDisjoint : Disjoint
      (((contractDatum data hc hab hOne).edgePartition shift.firstTarget).block
        shift.firstAnchor)
      (((contractDatum data hc hab hOne).edgePartition shift.secondTarget).block
        shift.secondAnchor) := by
    rw [Finset.disjoint_left]
    intro sheet hFirst hSecond
    exact not_mem_both_blocks' data _ _ hTargetEq hNe sheet (hFirstSub hFirst)
      (hSecondSub hSecond)
  have hFirstWall := survivor_block_subset_wall data hc hab hOne star input
    shift.firstRest.1 shift.firstTarget_mem shift.firstAnchor_wall_rel
  have hSecondWall := survivor_block_subset_wall data hc hab hOne star input
    shift.secondRest.1 shift.secondTarget_mem shift.secondAnchor_wall_rel
  have hCard : (contractDatum data hc hab hOne).sourceEdgeIndex shift.firstRest.1 +
      (contractDatum data hc hab hOne).sourceEdgeIndex shift.secondRest.1 ≤
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
        input.distinguishedBlock.1 := by
    have hUnion : (((contractDatum data hc hab hOne).edgePartition shift.firstTarget).block
        shift.firstAnchor) ∪
        (((contractDatum data hc hab hOne).edgePartition shift.secondTarget).block
          shift.secondAnchor) ⊆ wallBlock := Finset.union_subset hFirstWall hSecondWall
    have hCount := Finset.card_le_card hUnion
    rwa [Finset.card_union_of_disjoint hDisjoint] at hCount
  have hSum := shift.index_sum
  have hLt := shift.moving_lt
  omega

end Retained

/-! ## The selected fibre of an incoming `w3Shift` cover -/

section Fibre

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (shift : ShiftProfile input)
  (hMoving : shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star)

include fullDim hForest hCompat hMoving

/-- **Figure 29's exact incoming fibre census.**  The moving survivor's
canonical endpoint `P` sits alone above the divalent original endpoint and is
divalent; the two retained survivors share one canonical endpoint `Q` above the
trivalent original endpoint, which is the branch vertex; and the selected pruned
fibre is exactly one surviving occurrence of the contracted direction joining
them.

Unlike Figure 30's `M⁽²⁾` the branch vertex lies on the **unramified** side, so
`W3Nd2IncomingSheetClasses.sheet_classes_of_active_pair` does not apply and the
classes are determined instead by the two local `nd. r` identities; see
`selected_sheet_classes`. -/
theorem selected_fibre_census :
    ∃ internal : data.SourceEdge,
      internalEdges data hc hab hOne (selectedVertex data hc hab hOne star input) =
          {internal} ∧
      activeFibreVertices data hc hab hOne
          (selectedVertex data hc hab hOne star input) =
        {movingEndpoint data hc hab hOne star input shift,
          firstEndpoint data hc hab hOne star input shift} ∧
      (activeFibreVertices data hc hab hOne
            (selectedVertex data hc hab hOne star input)).filter
          (fun other ↦ other.1.1 =
            (movingEndpoint data hc hab hOne star input shift).1.1) =
        {movingEndpoint data hc hab hOne star input shift} ∧
      (activeFibreVertices data hc hab hOne
            (selectedVertex data hc hab hOne star input)).filter
          (fun other ↦ other.1.1 =
            (firstEndpoint data hc hab hOne star input shift).1.1) =
        {firstEndpoint data hc hab hOne star input shift} ∧
      Incident data internal (movingEndpoint data hc hab hOne star input shift) ∧
      Incident data internal (firstEndpoint data hc hab hOne star input shift) ∧
      nonDanglingValency data (movingEndpoint data hc hab hOne star input shift) = 2 ∧
      nonDanglingValency data (firstEndpoint data hc hab hOne star input shift) = 3 := by
  classical
  have hVertex := selectedVertex_eq_mergedVertex data hc hab hOne star input
  have hWallNd : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) = 3 := by
    rw [← hVertex]
    exact shift_valency shift
  have hMovingActive : movingEndpoint data hc hab hOne star input shift ∈
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) :=
    endpoint_active data hc hab hOne hCompat.1
      (selectedBlock data hc hab hOne star input)
      ⟨shift.moving.1, moving_survives shift⟩
      (moving_incident_merged data hc hab hOne star input shift)
  have hFirstActive : firstEndpoint data hc hab hOne star input shift ∈
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) :=
    endpoint_active data hc hab hOne hCompat.1
      (selectedBlock data hc hab hOne star input)
      ⟨shift.firstRest.1, firstRest_survives shift⟩
      (firstRest_incident_merged data hc hab hOne star input shift)
  have hChangeV : data.targetChange
      (firstEndpoint data hc hab hOne star input shift).1.1 = 0 :=
    first_targetChange_eq_zero data hc hab hOne fullDim star input shift hMoving
  have hSideV : (firstEndpoint data hc hab hOne star input shift).1.1 = a ∨
      (firstEndpoint data hc hab hOne star input shift).1.1 = b :=
    first_endpoint_target_mem data hc hab hOne star input shift
  have hMovingNeV : (movingEndpoint data hc hab hOne star input shift).1.1 ≠
      (firstEndpoint data hc hab hOne star input shift).1.1 :=
    moving_endpoint_target_ne data hc hab hOne fullDim star input shift hMoving
  -- at most one active constituent above the divalent original endpoint
  have hOtherLe := W3Nd3IncomingCensus.otherSide_card_le_one data hc hab hOne fullDim
    hForest hCompat (selectedBlock data hc hab hOne star input) hWallNd
    (firstEndpoint data hc hab hOne star input shift).1.1 hSideV hChangeV
  have hMovingMemOther : movingEndpoint data hc hab hOne star input shift ∈
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input))).filter
        (fun point ↦ ¬ point.1.1 =
          (firstEndpoint data hc hab hOne star input shift).1.1) :=
    Finset.mem_filter.mpr ⟨hMovingActive, hMovingNeV⟩
  have hOtherSingleton : (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
        (fun point ↦ ¬ point.1.1 =
          (firstEndpoint data hc hab hOne star input shift).1.1) =
      {movingEndpoint data hc hab hOne star input shift} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hMovingMemOther,
      fun point hPoint ↦ Finset.card_le_one.mp hOtherLe _ hPoint _ hMovingMemOther⟩
  have hInternalInc : ∀ edge ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)),
      Incident data edge (movingEndpoint data hc hab hOne star input shift) :=
    fun edge hEdge ↦ W3Nd3IncomingCensus.internal_incident_otherEnd data hc hab hOne _ _
      hSideV _ hOtherSingleton edge hEdge
  -- the moving survivor's own retained copy already sits at `P`
  have hExtraMoving : ∀ edge ∈ ({sourceEdgeEmbedding data hc hab hOne shift.moving.1} :
        Finset data.SourceEdge),
      (¬ IsDangling data edge) ∧
        Incident data edge (movingEndpoint data hc hab hOne star input shift) ∧
        edge.1.1 ≠ contracted := by
    intro edge hEdge
    rcases Finset.mem_singleton.mp hEdge with rfl
    exact ⟨(nonDanglingEmbedding data hCompat.1
        ⟨shift.moving.1, moving_survives shift⟩).2,
      endpoint_incident data hc hab hOne (selectedBlock data hc hab hOne star input)
        shift.moving.1 (moving_incident_merged data hc hab hOne star input shift),
      sourceEdgeEmbedding_ne_contracted data hc hab hOne shift.moving.1⟩
  have hMovingBound := W3Nd3IncomingCensus.extra_add_internal_card_le data hc hab hOne
    (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input))
    (movingEndpoint data hc hab hOne star input shift) hInternalInc _ hExtraMoving
  rw [Finset.card_singleton] at hMovingBound
  have hMovingLe : nonDanglingValency data
      (movingEndpoint data hc hab hOne star input shift) ≤ 3 := by
    rcases W3Nd3IncomingCensus.active_valency_two_or_three data hc hab hOne fullDim
      hForest hCompat (selectedBlock data hc hab hOne star input) hWallNd _
      hMovingActive with h | h <;> omega
  -- the pruned tree count and the two-sided split
  have hTree := internalEdges_card_add_one_eq_activeFibreVertices_card
    data hc hab hOne hForest (selectedBlock data hc hab hOne star input)
    (W3Nd3IncomingCensus.activeFibre_nonempty data hc hab hOne hCompat
      (selectedBlock data hc hab hOne star input) hWallNd)
  have hSplit : ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
      fun point ↦ point.1.1 =
        (firstEndpoint data hc hab hOne star input shift).1.1).card +
      ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
      fun point ↦ ¬ point.1.1 =
        (firstEndpoint data hc hab hOne star input shift).1.1).card =
      (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).card :=
    Finset.card_filter_add_card_filter_not _
  have hOtherCard : ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
      fun point ↦ ¬ point.1.1 =
        (firstEndpoint data hc hab hOne star input shift).1.1).card = 1 := by
    rw [hOtherSingleton, Finset.card_singleton]
  have hFirstMemSide : firstEndpoint data hc hab hOne star input shift ∈
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input))).filter
        (fun point ↦ point.1.1 =
          (firstEndpoint data hc hab hOne star input shift).1.1) :=
    Finset.mem_filter.mpr ⟨hFirstActive, rfl⟩
  have hSidePos : 1 ≤ ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
      fun point ↦ point.1.1 =
        (firstEndpoint data hc hab hOne star input shift).1.1).card :=
    Finset.card_pos.mpr ⟨_, hFirstMemSide⟩
  have hSideCard : ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
      fun point ↦ point.1.1 =
        (firstEndpoint data hc hab hOne star input shift).1.1).card =
      (internalEdges data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input))).card := by omega
  -- the branch vertex is `Q`: it carries both retained copies and an internal occurrence
  have hImage := W3Nd3IncomingCensus.sideEnd_image data hc hab hOne fullDim hForest
    hCompat (selectedBlock data hc hab hOne star input) hWallNd
    (firstEndpoint data hc hab hOne star input shift).1.1 hSideV hChangeV hSideCard.le
  obtain ⟨witness, hWitnessMem, hWitnessEq⟩ : ∃ witness ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)),
      W3Nd3IncomingCensus.sideEnd data
          (firstEndpoint data hc hab hOne star input shift).1.1 witness =
        firstEndpoint data hc hab hOne star input shift := by
    have := hImage ▸ hFirstMemSide
    exact Finset.mem_image.mp this
  have hWitnessInc : Incident data witness
      (firstEndpoint data hc hab hOne star input shift) := by
    rw [← hWitnessEq]
    exact W3Nd3IncomingCensus.sideEnd_incident data _ witness
  have hWitnessTarget : witness.1.1 = contracted :=
    ((mem_internalEdges data hc hab hOne _ witness).mp hWitnessMem).2.1
  have hFirstThree : 3 ≤ nonDanglingValency data
      (firstEndpoint data hc hab hOne star input shift) := by
    have hSecondInc : Incident data
        (sourceEdgeEmbedding data hc hab hOne shift.secondRest.1)
        (firstEndpoint data hc hab hOne star input shift) := by
      rw [first_eq_second_endpoint data hc hab hOne fullDim star input shift hMoving]
      exact endpoint_incident data hc hab hOne
        (selectedBlock data hc hab hOne star input) shift.secondRest.1
        (secondRest_incident_merged data hc hab hOne star input shift)
    have hSubset : ({sourceEdgeEmbedding data hc hab hOne shift.firstRest.1,
        sourceEdgeEmbedding data hc hab hOne shift.secondRest.1, witness} :
        Finset data.SourceEdge) ⊆
        nonDanglingIncident data (firstEndpoint data hc hab hOne star input shift) := by
      intro edge hEdge
      simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
      rcases hEdge with rfl | rfl | hWitness
      · exact (mem_nonDanglingIncident data _ _).mpr
          ⟨(nonDanglingEmbedding data hCompat.1
              ⟨shift.firstRest.1, firstRest_survives shift⟩).2,
            endpoint_incident data hc hab hOne
              (selectedBlock data hc hab hOne star input) shift.firstRest.1
              (firstRest_incident_merged data hc hab hOne star input shift)⟩
      · exact (mem_nonDanglingIncident data _ _).mpr
          ⟨(nonDanglingEmbedding data hCompat.1
              ⟨shift.secondRest.1, secondRest_survives shift⟩).2, hSecondInc⟩
      · rw [hWitness]
        exact (mem_nonDanglingIncident data _ _).mpr
          ⟨((mem_internalEdges data hc hab hOne _ witness).mp hWitnessMem).1, hWitnessInc⟩
    have hFirstNeSecond : sourceEdgeEmbedding data hc hab hOne shift.firstRest.1 ≠
        sourceEdgeEmbedding data hc hab hOne shift.secondRest.1 :=
      embedding_ne data hc hab hOne hCompat.1
        ⟨shift.firstRest.1, firstRest_survives shift⟩
        ⟨shift.secondRest.1, secondRest_survives shift⟩
        (fun h ↦ shift.first_ne_second (Subtype.ext (congrArg
          (fun edge : NonDanglingEdge (contractDatum data hc hab hOne) ↦ edge.1) h)))
    have hFirstNeWitness : sourceEdgeEmbedding data hc hab hOne shift.firstRest.1 ≠
        witness := fun h ↦ sourceEdgeEmbedding_ne_contracted data hc hab hOne
          shift.firstRest.1 (by rw [h]; exact hWitnessTarget)
    have hSecondNeWitness : sourceEdgeEmbedding data hc hab hOne shift.secondRest.1 ≠
        witness := fun h ↦ sourceEdgeEmbedding_ne_contracted data hc hab hOne
          shift.secondRest.1 (by rw [h]; exact hWitnessTarget)
    have hCard : ({sourceEdgeEmbedding data hc hab hOne shift.firstRest.1,
        sourceEdgeEmbedding data hc hab hOne shift.secondRest.1, witness} :
        Finset data.SourceEdge).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact fun h ↦ h.elim hFirstNeSecond hFirstNeWitness),
        Finset.card_pair hSecondNeWitness]
    have := Finset.card_le_card hSubset
    rwa [hCard, card_nonDanglingIncident] at this
  have hEndpointsNe : movingEndpoint data hc hab hOne star input shift ≠
      firstEndpoint data hc hab hOne star input shift :=
    fun h ↦ hMovingNeV (congrArg (fun point : data.SourceVertex ↦ point.1.1) h)
  have hFirstNd : nonDanglingValency data
      (firstEndpoint data hc hab hOne star input shift) = 3 := by
    rcases W3Nd3IncomingCensus.active_valency_two_or_three data hc hab hOne fullDim
      hForest hCompat (selectedBlock data hc hab hOne star input) hWallNd _
      hFirstActive with h | h <;> omega
  have hMovingNe3 : nonDanglingValency data
      (movingEndpoint data hc hab hOne star input shift) ≠ 3 :=
    W3Nd3IncomingCensus.active_valency_three_unique data hc hab hOne fullDim hForest
      hCompat (selectedBlock data hc hab hOne star input) hWallNd
      (firstEndpoint data hc hab hOne star input shift)
      (movingEndpoint data hc hab hOne star input shift) hFirstActive hMovingActive
      (Ne.symm hEndpointsNe) hFirstNd
  have hInternalCard : (internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input))).card = 1 := by omega
  have hSideSingleton : (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
        (fun point ↦ point.1.1 =
          (firstEndpoint data hc hab hOne star input shift).1.1) =
      {firstEndpoint data hc hab hOne star input shift} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hFirstMemSide,
      fun point hPoint ↦ Finset.card_le_one.mp (by omega) _ hPoint _ hFirstMemSide⟩
  obtain ⟨internal, hInternal⟩ := Finset.card_eq_one.mp hInternalCard
  have hInternalMem : internal ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) := by
    rw [hInternal]
    exact Finset.mem_singleton_self internal
  have hActiveCard : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input))).card = 2 := by omega
  have hActive : activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) =
      {movingEndpoint data hc hab hOne star input shift,
        firstEndpoint data hc hab hOne star input shift} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro point hPoint
      rcases Finset.mem_insert.mp hPoint with rfl | hPoint
      · exact hMovingActive
      · exact (Finset.mem_singleton.mp hPoint) ▸ hFirstActive
    · rw [hActiveCard, Finset.card_pair hEndpointsNe]
  have hIncMoving := hInternalInc internal hInternalMem
  have hIncFirst := W3Nd3IncomingCensus.internal_incident_sideEnd data hc hab hOne _ _
    hSideV _ hSideSingleton internal hInternalMem
  have hMovingNd : nonDanglingValency data
      (movingEndpoint data hc hab hOne star input shift) = 2 := by
    rcases W3Nd3IncomingCensus.active_valency_two_or_three data hc hab hOne fullDim
      hForest hCompat (selectedBlock data hc hab hOne star input) hWallNd _
      hMovingActive with h | h <;> omega
  have hFilterMoving : (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
        (fun other ↦ other.1.1 =
          (movingEndpoint data hc hab hOne star input shift).1.1) =
      {movingEndpoint data hc hab hOne star input shift} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr
      ⟨Finset.mem_filter.mpr ⟨hMovingActive, rfl⟩, ?_⟩
    intro point hPoint
    obtain ⟨hPointActive, hPointTarget⟩ := Finset.mem_filter.mp hPoint
    rw [hActive] at hPointActive
    rcases Finset.mem_insert.mp hPointActive with rfl | hPointRest
    · rfl
    · rw [Finset.mem_singleton] at hPointRest
      subst hPointRest
      exact absurd hPointTarget.symm hMovingNeV
  rw [← hVertex] at hInternal hActive hFilterMoving hSideSingleton
  exact ⟨internal, hInternal, hActive, hFilterMoving, hSideSingleton, hIncMoving,
    hIncFirst, hMovingNd, hFirstNd⟩

end Fibre

/-! ## Reading the two local `nd. r` identities off an exact incidence list -/

section Filters

variable (data : GluingDatum target degree)

theorem nonDangling_filter_eq_pair (vertex : data.SourceVertex)
    (first second : IncidentSourceEdge data vertex) (hNe : first ≠ second)
    (hFirst : ¬ IsDangling data first.1) (hSecond : ¬ IsDangling data second.1)
    (hNd : nonDanglingValency data vertex = 2) :
    (Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
        (fun edge ↦ ¬ IsDangling data edge.1) = {first, second} := by
  classical
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFirst⟩
    · rw [Finset.mem_singleton.mp hEdge]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSecond⟩
  · rw [card_filter_not_isDangling_eq_nonDanglingValency, hNd,
      Finset.card_pair hNe]

theorem nonDangling_filter_eq_triple (vertex : data.SourceVertex)
    (first second third : IncidentSourceEdge data vertex)
    (hFirstSecond : first ≠ second) (hFirstThird : first ≠ third)
    (hSecondThird : second ≠ third)
    (hFirst : ¬ IsDangling data first.1) (hSecond : ¬ IsDangling data second.1)
    (hThird : ¬ IsDangling data third.1)
    (hNd : nonDanglingValency data vertex = 3) :
    (Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
        (fun edge ↦ ¬ IsDangling data edge.1) = {first, second, third} := by
  classical
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro edge hEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFirst⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSecond⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hThird⟩
  · rw [card_filter_not_isDangling_eq_nonDanglingValency, hNd,
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact fun h ↦ h.elim hFirstSecond hFirstThird),
      Finset.card_pair hSecondThird]

/-- The surviving index sum at a divalent source vertex with a named incidence
pair. -/
theorem sum_index_of_pair (vertex : data.SourceVertex)
    (first second : IncidentSourceEdge data vertex) (hNe : first ≠ second)
    (hFirst : ¬ IsDangling data first.1) (hSecond : ¬ IsDangling data second.1)
    (hNd : nonDanglingValency data vertex = 2) :
    (∑ edge ∈ (Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
        (fun edge ↦ ¬ IsDangling data edge.1), (data.sourceEdgeIndex edge.1 : ℤ)) =
      (data.sourceEdgeIndex first.1 : ℤ) + (data.sourceEdgeIndex second.1 : ℤ) := by
  classical
  rw [nonDangling_filter_eq_pair data vertex first second hNe hFirst hSecond hNd]
  have hPair : (∑ edge ∈ ({first, second} : Finset (IncidentSourceEdge data vertex)),
      (data.sourceEdgeIndex edge.1 : ℤ)) =
      (data.sourceEdgeIndex first.1 : ℤ) + (data.sourceEdgeIndex second.1 : ℤ) :=
    Finset.sum_pair hNe
  exact hPair

/-- The surviving index sum at a trivalent source vertex with a named incidence
triple. -/
theorem sum_index_of_triple (vertex : data.SourceVertex)
    (first second third : IncidentSourceEdge data vertex)
    (hFirstSecond : first ≠ second) (hFirstThird : first ≠ third)
    (hSecondThird : second ≠ third)
    (hFirst : ¬ IsDangling data first.1) (hSecond : ¬ IsDangling data second.1)
    (hThird : ¬ IsDangling data third.1)
    (hNd : nonDanglingValency data vertex = 3) :
    (∑ edge ∈ (Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
        (fun edge ↦ ¬ IsDangling data edge.1), (data.sourceEdgeIndex edge.1 : ℤ)) =
      (data.sourceEdgeIndex first.1 : ℤ) + (data.sourceEdgeIndex second.1 : ℤ) +
        (data.sourceEdgeIndex third.1 : ℤ) := by
  classical
  rw [nonDangling_filter_eq_triple data vertex first second third hFirstSecond
    hFirstThird hSecondThird hFirst hSecond hThird hNd]
  have hInsert : (∑ edge ∈ ({first, second, third} :
        Finset (IncidentSourceEdge data vertex)), (data.sourceEdgeIndex edge.1 : ℤ)) =
      (data.sourceEdgeIndex first.1 : ℤ) +
        ∑ edge ∈ ({second, third} : Finset (IncidentSourceEdge data vertex)),
          (data.sourceEdgeIndex edge.1 : ℤ) :=
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hFirstSecond, hFirstThird⟩)
  have hPair : (∑ edge ∈ ({second, third} : Finset (IncidentSourceEdge data vertex)),
      (data.sourceEdgeIndex edge.1 : ℤ)) =
      (data.sourceEdgeIndex second.1 : ℤ) + (data.sourceEdgeIndex third.1 : ℤ) :=
    Finset.sum_pair hSecondThird
  rw [hInsert, hPair]
  ring

end Filters

/-! ## Blocks outside the active picture are singletons -/

section Singletons

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)

include fullDim

/-- An endpoint block of the merged wall block other than the fibre's unique
active constituent above that original endpoint is a literal singleton. -/
theorem inactive_vertex_block (block : (mergedPartition data a b).Blocks)
    (place : target.V) (hPlace : place = a ∨ place = b)
    (point : data.SourceVertex)
    (hFilter : (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block)).filter
        (fun other ↦ other.1.1 = place) = {point})
    (sheet : Fin degree)
    (hSheet : sheet ∈ (mergedPartition data a b).block block.1)
    (hNot : sheet ∉ (data.vertexPartition place).block point.1.2) :
    (data.vertexPartition place).block sheet = {sheet} := by
  classical
  refine inactive_endpoint_block_local data fullDim place sheet ?_
  by_contra hNonzero
  have hMap : sourceVertexMap data hc hab hOne (data.sourceEndpoint place sheet) =
      mergedVertex data hc hab hOne block := by
    refine (mem_fibreVertices data hc hab hOne _ _).mp ?_
    refine (mem_fibreVertices_mergedVertex_iff data hc hab hOne block _).mpr ⟨hPlace, ?_⟩
    have hRelPlace : (mergedPartition data a b).Rel
        ((data.vertexPartition place).repr sheet) sheet := by
      rcases hPlace with rfl | rfl
      · exact (vertexPartition_refines_mergedPartition data place b).rel
          ((data.vertexPartition place).rel_repr_left sheet)
      · exact (vertexPartition_refines_mergedPartition_right data a place).rel
          ((data.vertexPartition place).rel_repr_left sheet)
    have hBlockRel : (mergedPartition data a b).Rel block.1 sheet :=
      ((mergedPartition data a b).mem_block_iff _ _).mp hSheet
    have hFinal : (mergedPartition data a b).repr
        ((data.vertexPartition place).repr sheet) = block.1 :=
      (hRelPlace.trans hBlockRel.symm).trans block.2
    exact hFinal
  have hActive : data.sourceEndpoint place sheet ∈
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) :=
    (mem_activeFibreVertices data hc hab hOne _ _).mpr ⟨hMap, hNonzero⟩
  have hMem : data.sourceEndpoint place sheet ∈
      (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block)).filter
        (fun other ↦ other.1.1 = place) :=
    Finset.mem_filter.mpr ⟨hActive, rfl⟩
  rw [hFilter, Finset.mem_singleton] at hMem
  have hSheetRepr : (data.vertexPartition place).repr sheet = point.1.2 :=
    congrArg (fun v : data.SourceVertex ↦ v.1.2) hMem
  have hPointRepr : (data.vertexPartition place).repr point.1.2 = point.1.2 := by
    have hTarget : point.1.1 = place := by
      rw [← hMem]
      rfl
    rw [← hTarget]
    exact point.2
  refine hNot (((data.vertexPartition place).mem_block_iff _ _).mpr ?_)
  change (data.vertexPartition place).repr point.1.2 =
    (data.vertexPartition place).repr sheet
  rw [hPointRepr, hSheetRepr]

end Singletons

/-! ## Contracted occurrences outside the pruned fibre are singletons -/

section ContractedSingleton

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)

include fullDim

/-- An occurrence of the contracted direction above the merged wall block other
than the fibre's unique internal occurrence is dangling, hence a literal
singleton by the dangling-no-glue condition. -/
theorem inactive_contracted_block (block : (mergedPartition data a b).Blocks)
    (internal : data.SourceEdge)
    (hInternal : internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne block) = {internal})
    (sheet : Fin degree)
    (hSheet : sheet ∈ (mergedPartition data a b).block block.1)
    (hNot : sheet ∉ (data.edgePartition internal.1.1).block internal.1.2) :
    (data.edgePartition contracted).block sheet = {sheet} := by
  classical
  have hMergedSheet : (mergedPartition data a b).repr sheet = block.1 :=
    (((mergedPartition data a b).mem_block_iff _ _).mp hSheet).symm.trans block.2
  set occurrence := data.sourceEdge contracted sheet with hOccurrence
  have hOccurrenceTarget : occurrence.1.1 = contracted := rfl
  have hOccurrenceSheet : occurrence.1.2 = (data.edgePartition contracted).repr sheet := rfl
  have hDangling : IsDangling data occurrence := by
    by_contra hSurvives
    have hEndA : (data.sourceEnds occurrence).1 =
        data.sourceEndpoint a occurrence.1.2 := by
      have hFirst : (occurrence.1.1 : target.V × target.V).1 = a := by
        rw [hOccurrenceTarget, hc]
      exact congrArg (fun place ↦ data.sourceEndpoint place occurrence.1.2) hFirst
    have hMergedOccurrence : (mergedPartition data a b).repr occurrence.1.2 = block.1 := by
      rw [hOccurrenceSheet]
      refine Eq.trans ?_ hMergedSheet
      exact (edgePartition_refines_mergedPartition data hc).rel
        ((data.edgePartition contracted).rel_repr_left sheet)
    have hMap : sourceVertexMap data hc hab hOne (data.sourceEnds occurrence).1 =
        mergedVertex data hc hab hOne block := by
      rw [hEndA]
      refine (mem_fibreVertices data hc hab hOne _ _).mp ?_
      refine (mem_fibreVertices_mergedVertex_iff data hc hab hOne block _).mpr
        ⟨Or.inl rfl, ?_⟩
      refine Eq.trans ?_ hMergedOccurrence
      exact (vertexPartition_refines_mergedPartition data a b).rel
        ((data.vertexPartition a).rel_repr_left occurrence.1.2)
    have hMem : occurrence ∈ internalEdges data hc hab hOne
        (mergedVertex data hc hab hOne block) :=
      (mem_internalEdges data hc hab hOne _ _).mpr ⟨hSurvives, hOccurrenceTarget, hMap⟩
    rw [hInternal, Finset.mem_singleton] at hMem
    refine hNot ?_
    rw [← hMem, hOccurrenceTarget, hOccurrenceSheet]
    exact ((data.edgePartition contracted).mem_block_iff _ _).mpr
      ((data.edgePartition contracted).rel_repr_left sheet)
  have hIndex := fullDim.danglingEdgeNoGlue occurrence hDangling
  have hCard : (data.edgePartition contracted).blockCard sheet = 1 := by
    have hStep : (data.edgePartition contracted).blockCard occurrence.1.2 = 1 := hIndex
    rw [hOccurrenceSheet] at hStep
    rwa [SheetPartition.blockCard_congr (data.edgePartition contracted)
      ((data.edgePartition contracted).rel_repr_left sheet)] at hStep
  exact (data.edgePartition contracted).block_eq_singleton_of_blockCard_eq_one sheet hCard

end ContractedSingleton

/-! ## The two Figure 29 positions, as literal sheet sets -/

section Classes

variable (data : GluingDatum target degree)

/-- An incident occurrence's sheet class sits inside its endpoint's. -/
theorem incident_block_subset (edge : data.SourceEdge) (vertex : data.SourceVertex)
    (hIncident : Incident data edge vertex) :
    (data.edgePartition edge.1.1).block edge.1.2 ⊆
      (data.vertexPartition vertex.1.1).block vertex.1.2 := by
  obtain ⟨hMember, hRel⟩ := (incident_iff_target_mem_and_rel data edge vertex).mp hIncident
  intro sheet hSheet
  exact (SheetPartition.mem_block_iff _ _ _).mpr
    (hRel.trans ((refines_of_mem_incidentEdges data hMember).rel
      ((SheetPartition.mem_block_iff _ _ _).mp hSheet)))

end Classes

section Positions

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (shift : ShiftProfile input)
  (hMoving : shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star)

include fullDim hForest hCompat hMoving

/-- **Figure 29's Position II dichotomy, read on the incoming cover's own sheet
classes.**  The divalent original endpoint carries either `e_α` exactly
(Position II.b, with a transferred sheet `x ∈ e_α` outside both retained
classes, the trivalent endpoint carrying `A₀ ∖ {x}` and the contracted
occurrence `e_α ∖ {x}`) or `e_α ∪ {y}` for a single sheet `y ∈ A₀ ∖ e_α`
(Position II.a, with the whole of `A₀` at the trivalent endpoint and the same
`e_α ∪ {y}` on the contracted occurrence).

Both alternatives occur, and nothing beyond `W3IncomingClassification`'s own
`w3Shift` payload -- the profile, the distinctness of the three directions and
`k_α < |A₀|` -- is used.  The Position II.a sheet `y` is *not* determined by
the profile: `|A₀ ∖ e_α| = |A₀| − k_α` may exceed one. -/
theorem selected_sheet_classes :
    ∃ internal : data.SourceEdge,
      internalEdges data hc hab hOne (selectedVertex data hc hab hOne star input) =
          {internal} ∧
      ((∃ transfer : Fin degree,
          ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).Rel
              shift.movingAnchor transfer ∧
          ¬((contractDatum data hc hab hOne).edgePartition shift.firstTarget).Rel
              shift.firstAnchor transfer ∧
          ¬((contractDatum data hc hab hOne).edgePartition shift.secondTarget).Rel
              shift.secondAnchor transfer ∧
          (data.vertexPartition
                (movingEndpoint data hc hab hOne star input shift).1.1).block
              (movingEndpoint data hc hab hOne star input shift).1.2 =
            ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block
              shift.movingAnchor ∧
          (data.vertexPartition
                (firstEndpoint data hc hab hOne star input shift).1.1).block
              (firstEndpoint data hc hab hOne star input shift).1.2 =
            (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block
              input.distinguishedBlock.1).erase transfer ∧
          (data.edgePartition internal.1.1).block internal.1.2 =
            (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block
              shift.movingAnchor).erase transfer) ∨
        (∃ extra : Fin degree,
          ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
              input.distinguishedBlock.1 extra ∧
          ¬((contractDatum data hc hab hOne).edgePartition shift.movingTarget).Rel
              shift.movingAnchor extra ∧
          (data.vertexPartition
                (movingEndpoint data hc hab hOne star input shift).1.1).block
              (movingEndpoint data hc hab hOne star input shift).1.2 =
            insert extra
              (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block
                shift.movingAnchor) ∧
          (data.vertexPartition
                (firstEndpoint data hc hab hOne star input shift).1.1).block
              (firstEndpoint data hc hab hOne star input shift).1.2 =
            ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block
              input.distinguishedBlock.1 ∧
          (data.edgePartition internal.1.1).block internal.1.2 =
            insert extra
              (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block
                shift.movingAnchor))) := by
  classical
  obtain ⟨internal, hInternal, hActive, hFilterMoving, hFilterFirst, hIncMoving,
    hIncFirst, hMovingNd, hFirstNd⟩ :=
    selected_fibre_census data hc hab hOne fullDim hForest hCompat star input shift hMoving
  refine ⟨internal, hInternal, ?_⟩
  have hVertex := selectedVertex_eq_mergedVertex data hc hab hOne star input
  have hMergedWall := W3ShiftIncomingMatching.merged_eq_wall data hc hab hOne
  have hA0 : (mergedPartition data a b).block
        (selectedBlock data hc hab hOne star input).1 =
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block
        input.distinguishedBlock.1 :=
    congrArg (fun partition : SheetPartition degree ↦
      partition.block input.distinguishedBlock.1) hMergedWall
  have hUnion : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block
        input.distinguishedBlock.1 =
      (data.vertexPartition
          (movingEndpoint data hc hab hOne star input shift).1.1).block
        (movingEndpoint data hc hab hOne star input shift).1.2 ∪
      (data.vertexPartition
          (firstEndpoint data hc hab hOne star input shift).1.1).block
        (firstEndpoint data hc hab hOne star input shift).1.2 := by
    rw [← hA0]
    exact W4IncomingClassUnion.AnyWall.block_eq_union_of_active_pair data fullDim hc hab
      hOne (selectedBlock data hc hab hOne star input) _ _ (by rw [← hVertex]; exact hActive)
  have hMovingSub : ((contractDatum data hc hab hOne).edgePartition
        shift.movingTarget).block shift.movingAnchor ⊆
      (data.vertexPartition
          (movingEndpoint data hc hab hOne star input shift).1.1).block
        (movingEndpoint data hc hab hOne star input shift).1.2 :=
    block_subset_endpoint_block data hc hab hOne
      (selectedBlock data hc hab hOne star input) shift.moving.1
      (moving_incident_merged data hc hab hOne star input shift)
  have hFirstSub : ((contractDatum data hc hab hOne).edgePartition
        shift.firstTarget).block shift.firstAnchor ⊆
      (data.vertexPartition
          (firstEndpoint data hc hab hOne star input shift).1.1).block
        (firstEndpoint data hc hab hOne star input shift).1.2 :=
    block_subset_endpoint_block data hc hab hOne
      (selectedBlock data hc hab hOne star input) shift.firstRest.1
      (firstRest_incident_merged data hc hab hOne star input shift)
  have hSecondSub : ((contractDatum data hc hab hOne).edgePartition
        shift.secondTarget).block shift.secondAnchor ⊆
      (data.vertexPartition
          (firstEndpoint data hc hab hOne star input shift).1.1).block
        (firstEndpoint data hc hab hOne star input shift).1.2 := by
    rw [first_eq_second_endpoint data hc hab hOne fullDim star input shift hMoving]
    exact block_subset_endpoint_block data hc hab hOne
      (selectedBlock data hc hab hOne star input) shift.secondRest.1
      (secondRest_incident_merged data hc hab hOne star input shift)
  have hInternalSubMoving : (data.edgePartition internal.1.1).block internal.1.2 ⊆
      (data.vertexPartition
          (movingEndpoint data hc hab hOne star input shift).1.1).block
        (movingEndpoint data hc hab hOne star input shift).1.2 :=
    incident_block_subset data internal _ hIncMoving
  have hInternalSubFirst : (data.edgePartition internal.1.1).block internal.1.2 ⊆
      (data.vertexPartition
          (firstEndpoint data hc hab hOne star input shift).1.1).block
        (firstEndpoint data hc hab hOne star input shift).1.2 :=
    incident_block_subset data internal _ hIncFirst
  have hMovingSubA : (data.vertexPartition
        (movingEndpoint data hc hab hOne star input shift).1.1).block
      (movingEndpoint data hc hab hOne star input shift).1.2 ⊆
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block
        input.distinguishedBlock.1 := by
    rw [hUnion]; exact Finset.subset_union_left
  have hFirstSubA : (data.vertexPartition
        (firstEndpoint data hc hab hOne star input shift).1.1).block
      (firstEndpoint data hc hab hOne star input shift).1.2 ⊆
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block
        input.distinguishedBlock.1 := by
    rw [hUnion]; exact Finset.subset_union_right
  -- the exact incidence lists at the two active constituents
  have hInternalMem : internal ∈ internalEdges data hc hab hOne
      (selectedVertex data hc hab hOne star input) := by
    rw [hInternal]
    exact Finset.mem_singleton_self internal
  have hInternalSurvives : ¬ IsDangling data internal :=
    ((mem_internalEdges data hc hab hOne _ internal).mp hInternalMem).1
  have hInternalTarget : internal.1.1 = contracted :=
    ((mem_internalEdges data hc hab hOne _ internal).mp hInternalMem).2.1
  have hIncEmbMoving : Incident data
      (sourceEdgeEmbedding data hc hab hOne shift.moving.1)
      (movingEndpoint data hc hab hOne star input shift) :=
    endpoint_incident data hc hab hOne (selectedBlock data hc hab hOne star input)
      shift.moving.1 (moving_incident_merged data hc hab hOne star input shift)
  have hIncEmbFirst : Incident data
      (sourceEdgeEmbedding data hc hab hOne shift.firstRest.1)
      (firstEndpoint data hc hab hOne star input shift) :=
    endpoint_incident data hc hab hOne (selectedBlock data hc hab hOne star input)
      shift.firstRest.1 (firstRest_incident_merged data hc hab hOne star input shift)
  have hIncEmbSecond : Incident data
      (sourceEdgeEmbedding data hc hab hOne shift.secondRest.1)
      (firstEndpoint data hc hab hOne star input shift) := by
    rw [first_eq_second_endpoint data hc hab hOne fullDim star input shift hMoving]
    exact endpoint_incident data hc hab hOne (selectedBlock data hc hab hOne star input)
      shift.secondRest.1 (secondRest_incident_merged data hc hab hOne star input shift)
  have hEmbFirstNeSecond : sourceEdgeEmbedding data hc hab hOne shift.firstRest.1 ≠
      sourceEdgeEmbedding data hc hab hOne shift.secondRest.1 :=
    embedding_ne data hc hab hOne hCompat.1
      ⟨shift.firstRest.1, firstRest_survives shift⟩
      ⟨shift.secondRest.1, secondRest_survives shift⟩
      (fun h ↦ shift.first_ne_second (Subtype.ext (congrArg
        (fun edge : NonDanglingEdge (contractDatum data hc hab hOne) ↦ edge.1) h)))
  have hEmbMovingNeInternal : sourceEdgeEmbedding data hc hab hOne shift.moving.1 ≠
      internal := fun h ↦ sourceEdgeEmbedding_ne_contracted data hc hab hOne
        shift.moving.1 (by rw [h]; exact hInternalTarget)
  have hEmbFirstNeInternal : sourceEdgeEmbedding data hc hab hOne shift.firstRest.1 ≠
      internal := fun h ↦ sourceEdgeEmbedding_ne_contracted data hc hab hOne
        shift.firstRest.1 (by rw [h]; exact hInternalTarget)
  have hEmbSecondNeInternal : sourceEdgeEmbedding data hc hab hOne shift.secondRest.1 ≠
      internal := fun h ↦ sourceEdgeEmbedding_ne_contracted data hc hab hOne
        shift.secondRest.1 (by rw [h]; exact hInternalTarget)
  -- Case (r0-nd3) at the branch vertex
  have hSumQ := sum_index_of_triple data
    (firstEndpoint data hc hab hOne star input shift)
    ⟨_, hIncEmbFirst⟩ ⟨_, hIncEmbSecond⟩ ⟨internal, hIncFirst⟩
    (fun h ↦ hEmbFirstNeSecond (congrArg (fun e : IncidentSourceEdge data
      (firstEndpoint data hc hab hOne star input shift) ↦ e.1) h))
    (fun h ↦ hEmbFirstNeInternal (congrArg (fun e : IncidentSourceEdge data
      (firstEndpoint data hc hab hOne star input shift) ↦ e.1) h))
    (fun h ↦ hEmbSecondNeInternal (congrArg (fun e : IncidentSourceEdge data
      (firstEndpoint data hc hab hOne star input shift) ↦ e.1) h))
    (nonDanglingEmbedding data hCompat.1 ⟨shift.firstRest.1, firstRest_survives shift⟩).2
    (nonDanglingEmbedding data hCompat.1 ⟨shift.secondRest.1, secondRest_survives shift⟩).2
    hInternalSurvives hFirstNd
  have hFormQ := localRamification_eq_nonDangling_form data fullDim.danglingEdgeNoGlue
    (firstEndpoint data hc hab hOne star input shift)
  rw [localRamification_endpoint_eq_zero data fullDim
      (firstEndpoint data hc hab hOne star input shift) _ rfl
      (first_targetChange_eq_zero data hc hab hOne fullDim star input shift hMoving),
    hSumQ, hFirstNd] at hFormQ
  -- Case (r1) at the divalent constituent above the divalent original endpoint
  have hSumP := sum_index_of_pair data
    (movingEndpoint data hc hab hOne star input shift)
    ⟨_, hIncEmbMoving⟩ ⟨internal, hIncMoving⟩
    (fun h ↦ hEmbMovingNeInternal (congrArg (fun e : IncidentSourceEdge data
      (movingEndpoint data hc hab hOne star input shift) ↦ e.1) h))
    (nonDanglingEmbedding data hCompat.1 ⟨shift.moving.1, moving_survives shift⟩).2
    hInternalSurvives hMovingNd
  have hFormP := localRamification_eq_nonDangling_form data fullDim.danglingEdgeNoGlue
    (movingEndpoint data hc hab hOne star input shift)
  rw [hSumP, hMovingNd] at hFormP
  have hRamPnonneg : 0 ≤ data.localRamification
      (movingEndpoint data hc hab hOne star input shift).1.1
      ⟨(movingEndpoint data hc hab hOne star input shift).1.2,
        (movingEndpoint data hc hab hOne star input shift).2⟩ :=
    data.localRamification_nonneg _ (fullDim.valid.2 _) _
  have hSideU : (movingEndpoint data hc hab hOne star input shift).1.1 = a ∨
      (movingEndpoint data hc hab hOne star input shift).1.1 = b :=
    W3Nd3IncomingCensus.endpoint_target_mem data hc hab hOne shift.moving.1
  have hSideV : (firstEndpoint data hc hab hOne star input shift).1.1 = a ∨
      (firstEndpoint data hc hab hOne star input shift).1.1 = b :=
    first_endpoint_target_mem data hc hab hOne star input shift
  have hChangeV := first_targetChange_eq_zero data hc hab hOne fullDim star input shift hMoving
  have hUV : (movingEndpoint data hc hab hOne star input shift).1.1 ≠
      (firstEndpoint data hc hab hOne star input shift).1.1 :=
    moving_endpoint_target_ne data hc hab hOne fullDim star input shift hMoving
  have hChangeU : data.targetChange
      (movingEndpoint data hc hab hOne star input shift).1.1 = 1 := by
    rcases hSideU with hU | hU <;> rcases hSideV with hV | hV
    · exact absurd (hU.trans hV.symm) hUV
    · rcases endpoint_valencies data hc hab hOne fullDim star with ⟨_, _, hA, _⟩ | ⟨_, _, _, hB⟩
      · rw [hU]; exact hA
      · exfalso; rw [hV] at hChangeV; omega
    · rcases endpoint_valencies data hc hab hOne fullDim star with ⟨_, _, hA, _⟩ | ⟨_, _, _, hB⟩
      · exfalso; rw [hV] at hChangeV; omega
      · rw [hU]; exact hB
    · exact absurd (hU.trans hV.symm) hUV
  have hRamPle : data.localRamification
      (movingEndpoint data hc hab hOne star input shift).1.1
      ⟨(movingEndpoint data hc hab hOne star input shift).1.2,
        (movingEndpoint data hc hab hOne star input shift).2⟩ ≤ 1 := by
    have hSum : (∑ blk : (data.vertexPartition
        (movingEndpoint data hc hab hOne star input shift).1.1).Blocks,
        data.localRamification
          (movingEndpoint data hc hab hOne star input shift).1.1 blk) = 1 := hChangeU
    have hNonneg : ∀ blk ∈ (Finset.univ : Finset ((data.vertexPartition
        (movingEndpoint data hc hab hOne star input shift).1.1).Blocks)),
        0 ≤ data.localRamification
          (movingEndpoint data hc hab hOne star input shift).1.1 blk :=
      fun blk _ ↦ data.localRamification_nonneg _ (fullDim.valid.2 _) blk
    have hSingle := Finset.single_le_sum hNonneg (Finset.mem_univ
      (⟨(movingEndpoint data hc hab hOne star input shift).1.2,
        (movingEndpoint data hc hab hOne star input shift).2⟩ :
        (data.vertexPartition
          (movingEndpoint data hc hab hOne star input shift).1.1).Blocks))
    omega
  -- the two indices carried by the retained copies
  have hIdxMoving : data.sourceEdgeIndex
      (sourceEdgeEmbedding data hc hab hOne shift.moving.1) =
      (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block
        shift.movingAnchor).card :=
    congrArg Finset.card (embedding_block data hc hab hOne shift.moving.1)
  have hIdxFirst : data.sourceEdgeIndex
      (sourceEdgeEmbedding data hc hab hOne shift.firstRest.1) =
      (((contractDatum data hc hab hOne).edgePartition shift.firstTarget).block
        shift.firstAnchor).card :=
    congrArg Finset.card (embedding_block data hc hab hOne shift.firstRest.1)
  have hIdxSecond : data.sourceEdgeIndex
      (sourceEdgeEmbedding data hc hab hOne shift.secondRest.1) =
      (((contractDatum data hc hab hOne).edgePartition shift.secondTarget).block
        shift.secondAnchor).card :=
    congrArg Finset.card (embedding_block data hc hab hOne shift.secondRest.1)
  have hIdxInternal : data.sourceEdgeIndex internal =
      ((data.edgePartition internal.1.1).block internal.1.2).card := rfl
  rw [hIdxFirst, hIdxSecond, hIdxInternal] at hFormQ
  rw [hIdxMoving, hIdxInternal] at hFormP
  have hBlockCardQ : (data.vertexPartition
        (firstEndpoint data hc hab hOne star input shift).1.1).blockCard
      (firstEndpoint data hc hab hOne star input shift).1.2 =
      ((data.vertexPartition
        (firstEndpoint data hc hab hOne star input shift).1.1).block
        (firstEndpoint data hc hab hOne star input shift).1.2).card := rfl
  have hBlockCardP : (data.vertexPartition
        (movingEndpoint data hc hab hOne star input shift).1.1).blockCard
      (movingEndpoint data hc hab hOne star input shift).1.2 =
      ((data.vertexPartition
        (movingEndpoint data hc hab hOne star input shift).1.1).block
        (movingEndpoint data hc hab hOne star input shift).1.2).card := rfl
  rw [hBlockCardQ] at hFormQ
  rw [hBlockCardP] at hFormP
  -- the numerical bookkeeping
  have hcardMovingSub := Finset.card_le_card hMovingSub
  have hcardIP := Finset.card_le_card hInternalSubMoving
  have hcardIQ := Finset.card_le_card hInternalSubFirst
  have hcardPA := Finset.card_le_card hMovingSubA
  have hcardQA := Finset.card_le_card hFirstSubA
  have hIndexSum : (((contractDatum data hc hab hOne).edgePartition
        shift.movingTarget).block shift.movingAnchor).card +
      (((contractDatum data hc hab hOne).edgePartition shift.firstTarget).block
        shift.firstAnchor).card +
      (((contractDatum data hc hab hOne).edgePartition shift.secondTarget).block
        shift.secondAnchor).card =
      2 * (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block
        input.distinguishedBlock.1).card := shift.index_sum
  have hMovingLt : (((contractDatum data hc hab hOne).edgePartition
        shift.movingTarget).block shift.movingAnchor).card <
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block
        input.distinguishedBlock.1).card := shift.moving_lt
  have hCase :
      (((data.edgePartition internal.1.1).block internal.1.2).card + 1 =
          (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block
            shift.movingAnchor).card ∧
        ((data.vertexPartition
            (movingEndpoint data hc hab hOne star input shift).1.1).block
          (movingEndpoint data hc hab hOne star input shift).1.2).card =
          (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block
            shift.movingAnchor).card ∧
        ((data.vertexPartition
            (firstEndpoint data hc hab hOne star input shift).1.1).block
          (firstEndpoint data hc hab hOne star input shift).1.2).card + 1 =
          (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block
            input.distinguishedBlock.1).card) ∨
      (((data.edgePartition internal.1.1).block internal.1.2).card =
          (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block
            shift.movingAnchor).card + 1 ∧
        ((data.vertexPartition
            (movingEndpoint data hc hab hOne star input shift).1.1).block
          (movingEndpoint data hc hab hOne star input shift).1.2).card =
          (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block
            shift.movingAnchor).card + 1 ∧
        ((data.vertexPartition
            (firstEndpoint data hc hab hOne star input shift).1.1).block
          (firstEndpoint data hc hab hOne star input shift).1.2).card =
          (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block
            input.distinguishedBlock.1).card) := by omega
  rcases hCase with ⟨hI1, hP1, hQ1⟩ | ⟨hI1, hP1, hQ1⟩
  · -- Position II.b: the divalent endpoint keeps `e_α` and one sheet is detached
    refine Or.inl ?_
    have hPeq : ((contractDatum data hc hab hOne).edgePartition
          shift.movingTarget).block shift.movingAnchor =
        (data.vertexPartition
            (movingEndpoint data hc hab hOne star input shift).1.1).block
          (movingEndpoint data hc hab hOne star input shift).1.2 :=
      Finset.eq_of_subset_of_card_le hMovingSub (by omega)
    have hSdiffCard : ((((contractDatum data hc hab hOne).vertexPartition
          ⟨a, hab⟩).block input.distinguishedBlock.1) \
        ((data.vertexPartition
            (firstEndpoint data hc hab hOne star input shift).1.1).block
          (firstEndpoint data hc hab hOne star input shift).1.2)).card = 1 := by
      rw [Finset.card_sdiff_of_subset hFirstSubA]
      omega
    obtain ⟨transfer, hTransferSet⟩ := Finset.card_eq_one.mp hSdiffCard
    have hTransferMem : transfer ∈ (((contractDatum data hc hab hOne).vertexPartition
          ⟨a, hab⟩).block input.distinguishedBlock.1) \
        ((data.vertexPartition
            (firstEndpoint data hc hab hOne star input shift).1.1).block
          (firstEndpoint data hc hab hOne star input shift).1.2) := by
      rw [hTransferSet]
      exact Finset.mem_singleton_self transfer
    have hTransferMemA := (Finset.mem_sdiff.mp hTransferMem).1
    have hTransferNotQ := (Finset.mem_sdiff.mp hTransferMem).2
    have hQeq : (data.vertexPartition
          (firstEndpoint data hc hab hOne star input shift).1.1).block
        (firstEndpoint data hc hab hOne star input shift).1.2 =
        ((((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block
          input.distinguishedBlock.1)).erase transfer := by
      have hBack := Finset.sdiff_sdiff_eq_self hFirstSubA
      rw [hTransferSet] at hBack
      rw [← hBack, Finset.sdiff_singleton_eq_erase]
    have hTransferE : transfer ∈ ((contractDatum data hc hab hOne).edgePartition
        shift.movingTarget).block shift.movingAnchor := by
      rw [hPeq]
      rcases Finset.mem_union.mp (hUnion ▸ hTransferMemA) with hLeft | hRight
      · exact hLeft
      · exact absurd hRight hTransferNotQ
    have hTransferNotCI : transfer ∉ (data.edgePartition internal.1.1).block internal.1.2 :=
      fun h ↦ hTransferNotQ (hInternalSubFirst h)
    refine ⟨transfer,
      (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mem_block_iff
        _ _).mp hTransferE, ?_, ?_, hPeq.symm, hQeq, ?_⟩
    · intro hRel
      exact hTransferNotQ (hFirstSub ((((contractDatum data hc hab hOne).edgePartition
        shift.firstTarget).mem_block_iff _ _).mpr hRel))
    · intro hRel
      exact hTransferNotQ (hSecondSub ((((contractDatum data hc hab hOne).edgePartition
        shift.secondTarget).mem_block_iff _ _).mpr hRel))
    · refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro sheet hSheet
        refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · intro hEq
          exact hTransferNotCI (hEq ▸ hSheet)
        · rw [hPeq]
          exact hInternalSubMoving hSheet
      · rw [Finset.card_erase_of_mem hTransferE]
        omega
  · -- Position II.a: one extra sheet joins `e_α` at the divalent endpoint
    refine Or.inr ?_
    have hQeq : (data.vertexPartition
          (firstEndpoint data hc hab hOne star input shift).1.1).block
        (firstEndpoint data hc hab hOne star input shift).1.2 =
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block
          input.distinguishedBlock.1 :=
      Finset.eq_of_subset_of_card_le hFirstSubA (by omega)
    have hSdiffCard : (((data.vertexPartition
          (movingEndpoint data hc hab hOne star input shift).1.1).block
        (movingEndpoint data hc hab hOne star input shift).1.2) \
        (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block
          shift.movingAnchor)).card = 1 := by
      rw [Finset.card_sdiff_of_subset hMovingSub]
      omega
    obtain ⟨extra, hExtraSet⟩ := Finset.card_eq_one.mp hSdiffCard
    have hExtraMem : extra ∈ ((data.vertexPartition
          (movingEndpoint data hc hab hOne star input shift).1.1).block
        (movingEndpoint data hc hab hOne star input shift).1.2) \
        (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block
          shift.movingAnchor) := by
      rw [hExtraSet]
      exact Finset.mem_singleton_self extra
    have hExtraMemP := (Finset.mem_sdiff.mp hExtraMem).1
    have hExtraNotE := (Finset.mem_sdiff.mp hExtraMem).2
    have hPeq : (data.vertexPartition
          (movingEndpoint data hc hab hOne star input shift).1.1).block
        (movingEndpoint data hc hab hOne star input shift).1.2 =
        insert extra (((contractDatum data hc hab hOne).edgePartition
          shift.movingTarget).block shift.movingAnchor) := by
      have hBack := Finset.sdiff_union_of_subset hMovingSub
      rw [hExtraSet] at hBack
      rw [← hBack, Finset.singleton_union]
    refine ⟨extra, ?_, ?_, hPeq, hQeq, ?_⟩
    · exact ((((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).mem_block_iff
        _ _).mp (hMovingSubA hExtraMemP))
    · intro hRel
      exact hExtraNotE ((((contractDatum data hc hab hOne).edgePartition
        shift.movingTarget).mem_block_iff _ _).mpr hRel)
    · exact (Finset.eq_of_subset_of_card_le hInternalSubMoving (by omega)).trans hPeq

end Positions

/-! ## Which original endpoint is the divalent one -/

section Sides

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (shift : ShiftProfile input)
  (hMoving : shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star)

include fullDim hMoving

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hMoving in
theorem moving_endpoint_target_mem :
    (movingEndpoint data hc hab hOne star input shift).1.1 = a ∨
      (movingEndpoint data hc hab hOne star input shift).1.1 = b :=
  W3Nd3IncomingCensus.endpoint_target_mem data hc hab hOne shift.moving.1

/-- The moving survivor's canonical endpoint carries the whole unit of target
change: it lies above the **divalent** original endpoint. -/
theorem moving_targetChange_eq_one :
    data.targetChange (movingEndpoint data hc hab hOne star input shift).1.1 = 1 := by
  have hSideU := moving_endpoint_target_mem data hc hab hOne star input shift
  have hSideV := first_endpoint_target_mem data hc hab hOne star input shift
  have hChangeV := first_targetChange_eq_zero data hc hab hOne fullDim star input shift hMoving
  have hUV := moving_endpoint_target_ne data hc hab hOne fullDim star input shift hMoving
  rcases hSideU with hU | hU <;> rcases hSideV with hV | hV
  · exact absurd (hU.trans hV.symm) hUV
  · rcases endpoint_valencies data hc hab hOne fullDim star with ⟨_, _, hA, _⟩ | ⟨_, _, _, hB⟩
    · rw [hU]; exact hA
    · exfalso; rw [hV] at hChangeV; omega
  · rcases endpoint_valencies data hc hab hOne fullDim star with ⟨_, _, hA, _⟩ | ⟨_, _, _, hB⟩
    · exfalso; rw [hV] at hChangeV; omega
    · rw [hU]; exact hB
  · exact absurd (hU.trans hV.symm) hUV

/-- When `a` is the divalent original endpoint, the moving survivor's endpoint
lies above `a` and both retained survivors' above `b`. -/
theorem sides_of_left_divalent (hCard : (GluingDatum.incidentEdges a).card = 2) :
    (movingEndpoint data hc hab hOne star input shift).1.1 = a ∧
      (firstEndpoint data hc hab hOne star input shift).1.1 = b := by
  have hSideU := moving_endpoint_target_mem data hc hab hOne star input shift
  have hSideV := first_endpoint_target_mem data hc hab hOne star input shift
  have hChangeV := first_targetChange_eq_zero data hc hab hOne fullDim star input shift hMoving
  have hChangeU := moving_targetChange_eq_one data hc hab hOne fullDim star input shift hMoving
  rcases endpoint_valencies data hc hab hOne fullDim star with
    ⟨_, _, hchA, hchB⟩ | ⟨hA3, _, _, _⟩
  · refine ⟨?_, ?_⟩
    · rcases hSideU with h | h
      · exact h
      · exfalso; rw [h] at hChangeU; omega
    · rcases hSideV with h | h
      · exfalso; rw [h] at hChangeV; omega
      · exact h
  · exact absurd hA3 (by omega)

/-- The mirror, when `b` is the divalent original endpoint. -/
theorem sides_of_right_divalent (hCard : (GluingDatum.incidentEdges b).card = 2) :
    (movingEndpoint data hc hab hOne star input shift).1.1 = b ∧
      (firstEndpoint data hc hab hOne star input shift).1.1 = a := by
  have hSideU := moving_endpoint_target_mem data hc hab hOne star input shift
  have hSideV := first_endpoint_target_mem data hc hab hOne star input shift
  have hChangeV := first_targetChange_eq_zero data hc hab hOne fullDim star input shift hMoving
  have hChangeU := moving_targetChange_eq_one data hc hab hOne fullDim star input shift hMoving
  rcases endpoint_valencies data hc hab hOne fullDim star with
    ⟨_, hB3, _, _⟩ | ⟨_, _, hchA, hchB⟩
  · exact absurd hB3 (by omega)
  · refine ⟨?_, ?_⟩
    · rcases hSideU with h | h
      · exfalso; rw [h] at hChangeU; omega
      · exact h
    · rcases hSideV with h | h
      · exact h
      · exfalso; rw [h] at hChangeV; omega

/-- **The census assembly.**  Three block identities read at the moving
survivor's endpoint, at the retained survivors' common endpoint and at the
contracted occurrence are exactly a `W3ShiftIncomingMatching.SelectedCensus`. -/
theorem selectedCensus_of_blocks
    (selectedLeft selectedRight selectedNew : SheetPartition degree)
    (hLeft : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (data.vertexPartition
          (movingEndpoint data hc hab hOne star input shift).1.1).block sheet =
        selectedLeft.block sheet)
    (hRight : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (data.vertexPartition
          (firstEndpoint data hc hab hOne star input shift).1.1).block sheet =
        selectedRight.block sheet)
    (hNew : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (data.edgePartition contracted).block sheet = selectedNew.block sheet) :
    W3ShiftIncomingMatching.SelectedCensus data hc hab hOne star input
      selectedLeft selectedRight selectedNew where
  divalentLeft := by
    intro hCard
    obtain ⟨hU, hV⟩ := sides_of_left_divalent data hc hab hOne fullDim star input shift
      hMoving hCard
    rw [hU] at hLeft
    rw [hV] at hRight
    exact ⟨hLeft, hRight, hNew⟩
  divalentRight := by
    intro hCard
    obtain ⟨hU, hV⟩ := sides_of_right_divalent data hc hab hOne fullDim star input shift
      hMoving hCard
    rw [hU] at hLeft
    rw [hV] at hRight
    exact ⟨hLeft, hRight, hNew⟩

end Sides

/-! ## The selected census, in the two Figure 29 positions -/

section Census

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (shift : ShiftProfile input)
  (hMoving : shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star)

include fullDim hForest hCompat hMoving

/-- **The selected census of an incoming `w3Shift` cover, on the classifier's
payload.**  An incoming
`w3Shift` cover displays over the distinguished wall block `A₀` exactly one of
Figure 29's two Position II pictures:

* **Position II.b** -- a `W3ShiftSourceCandidates.ShrinkData` for the incoming
  wall datum actually **exists**, and the cover's three selected classes are
  literally that member's `W3ShiftIncomingMatching.shiftClasses _ 0`;
* **Position II.a** -- the divalent endpoint carries `e_α ∪ {y}` for a single
  sheet `y ∈ A₀ ∖ e_α`, the trivalent endpoint the whole of `A₀`, and the
  contracted occurrence `e_α ∪ {y}` again.

No hypothesis beyond `W3IncomingClassification.Classification.shift`'s own
payload (through `ShiftProfile` and `hMoving`) is used.  In the first case the
`ShrinkData` is *produced*, so `W3ShiftSourceCandidates.HasShrinkSheet` is a
theorem there, rather than a hypothesis. -/
theorem exists_selectedCensus :
    (∃ shrink : ShrinkData shift,
        W3ShiftIncomingMatching.SelectedCensus data hc hab hOne star input
          ((contractDatum data hc hab hOne).edgePartition shift.movingTarget)
          (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet shrink.transfer shrink.remainder
            shrink.transfer_ne_remainder shrink.remainder_wall_rel)
          (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).detachSheet shrink.transfer shrink.remainder
            shrink.transfer_ne_remainder shrink.remainder_moving)) ∨
      (∃ extra : Fin degree, ∃ hSep : ¬((contractDatum data hc hab hOne).edgePartition shift.movingTarget).Rel shift.movingAnchor extra,
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel input.distinguishedBlock.1 extra ∧
        W3ShiftIncomingMatching.SelectedCensus data hc hab hOne star input
          (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mergeBlocks shift.movingAnchor extra hSep) ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
          (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mergeBlocks shift.movingAnchor extra hSep)) := by
  classical
  obtain ⟨internal, hInternal, hPosition⟩ :=
    selected_sheet_classes data hc hab hOne fullDim hForest hCompat star input shift hMoving
  obtain ⟨_, _, _, hFilterMoving, hFilterFirst, _, _, _, _⟩ :=
    selected_fibre_census data hc hab hOne fullDim hForest hCompat star input shift hMoving
  have hSelMerged := selectedVertex_eq_mergedVertex data hc hab hOne star input
  rw [hSelMerged] at hFilterMoving
  rw [hSelMerged] at hFilterFirst
  rw [hSelMerged] at hInternal
  have hInternalMem : internal ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) := by
    rw [hInternal]
    exact Finset.mem_singleton_self internal
  have hInternalTarget : internal.1.1 = contracted :=
    ((mem_internalEdges data hc hab hOne _ internal).mp hInternalMem).2.1
  have hSideU := moving_endpoint_target_mem data hc hab hOne star input shift
  have hSideV := first_endpoint_target_mem data hc hab hOne star input shift
  have hMemA0 : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      sheet ∈ (mergedPartition data a b).block (selectedBlock data hc hab hOne star input).1 :=
    fun sheet h ↦ ((mergedPartition data a b).mem_block_iff _ _).mpr h
  have hWallRel : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel input.distinguishedBlock.1 sheet :=
    fun sheet h ↦ (W3ShiftIncomingMatching.merged_rel_iff_wall_rel data hc hab hOne
      input.distinguishedBlock.1 sheet).mp h
  have hOutU : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      sheet ∉ (data.vertexPartition (movingEndpoint data hc hab hOne star input shift).1.1).block (movingEndpoint data hc hab hOne star input shift).1.2 →
      (data.vertexPartition (movingEndpoint data hc hab hOne star input shift).1.1).block sheet = {sheet} :=
    fun sheet hSheet hNot ↦ inactive_vertex_block data hc hab hOne fullDim (selectedBlock data hc hab hOne star input)
      (movingEndpoint data hc hab hOne star input shift).1.1 hSideU (movingEndpoint data hc hab hOne star input shift) hFilterMoving sheet (hMemA0 sheet hSheet) hNot
  have hOutV : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      sheet ∉ (data.vertexPartition (firstEndpoint data hc hab hOne star input shift).1.1).block (firstEndpoint data hc hab hOne star input shift).1.2 →
      (data.vertexPartition (firstEndpoint data hc hab hOne star input shift).1.1).block sheet = {sheet} :=
    fun sheet hSheet hNot ↦ inactive_vertex_block data hc hab hOne fullDim (selectedBlock data hc hab hOne star input)
      (firstEndpoint data hc hab hOne star input shift).1.1 hSideV (firstEndpoint data hc hab hOne star input shift) hFilterFirst sheet (hMemA0 sheet hSheet) hNot
  have hOutI : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      sheet ∉ (data.edgePartition internal.1.1).block internal.1.2 →
      (data.edgePartition contracted).block sheet = {sheet} :=
    fun sheet hSheet hNot ↦ inactive_contracted_block data hc hab hOne fullDim (selectedBlock data hc hab hOne star input)
      internal hInternal sheet (hMemA0 sheet hSheet) hNot
  have hInU : ∀ sheet, sheet ∈ (data.vertexPartition (movingEndpoint data hc hab hOne star input shift).1.1).block (movingEndpoint data hc hab hOne star input shift).1.2 →
      (data.vertexPartition (movingEndpoint data hc hab hOne star input shift).1.1).block sheet =
        (data.vertexPartition (movingEndpoint data hc hab hOne star input shift).1.1).block (movingEndpoint data hc hab hOne star input shift).1.2 :=
    fun sheet h ↦ ((data.vertexPartition (movingEndpoint data hc hab hOne star input shift).1.1).block_eq_of_rel
      (((data.vertexPartition (movingEndpoint data hc hab hOne star input shift).1.1).mem_block_iff _ _).mp h)).symm
  have hInV : ∀ sheet, sheet ∈ (data.vertexPartition (firstEndpoint data hc hab hOne star input shift).1.1).block (firstEndpoint data hc hab hOne star input shift).1.2 →
      (data.vertexPartition (firstEndpoint data hc hab hOne star input shift).1.1).block sheet =
        (data.vertexPartition (firstEndpoint data hc hab hOne star input shift).1.1).block (firstEndpoint data hc hab hOne star input shift).1.2 :=
    fun sheet h ↦ ((data.vertexPartition (firstEndpoint data hc hab hOne star input shift).1.1).block_eq_of_rel
      (((data.vertexPartition (firstEndpoint data hc hab hOne star input shift).1.1).mem_block_iff _ _).mp h)).symm
  have hInI : ∀ sheet, sheet ∈ (data.edgePartition internal.1.1).block internal.1.2 →
      (data.edgePartition contracted).block sheet =
        (data.edgePartition internal.1.1).block internal.1.2 := by
    intro sheet h
    rw [← hInternalTarget]
    exact ((data.edgePartition internal.1.1).block_eq_of_rel
      (((data.edgePartition internal.1.1).mem_block_iff _ _).mp h)).symm
  rcases hPosition with ⟨transfer, hRelTransfer, hNotFirst, hNotSecond, hPeq, hQeq, hIeq⟩ |
    ⟨extra, hRelExtra, hSep, hPeq, hQeq, hIeq⟩
  · -- Position II.b
    refine Or.inl ?_
    have hCardTwo : 2 ≤ ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).blockCard transfer := by
      rw [← SheetPartition.blockCard_congr ((contractDatum data hc hab hOne).edgePartition shift.movingTarget) hRelTransfer]
      exact shift.two_le_moving
    have hMemSelf : transfer ∈ ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block transfer := ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).self_mem_block transfer
    have hErase : 0 < ((((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block transfer).erase transfer).card := by
      rw [Finset.card_erase_of_mem hMemSelf]
      have hTwo : 2 ≤ (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block transfer).card := hCardTwo
      omega
    obtain ⟨remainder, hMemErase⟩ := Finset.card_pos.mp hErase
    obtain ⟨hNeRemainder, hMemRemainder⟩ := Finset.mem_erase.mp hMemErase
    have hRelRemainder : ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).Rel transfer remainder :=
      (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mem_block_iff transfer remainder).mp hMemRemainder
    have hNeTransfer : transfer ≠ remainder := fun h ↦ hNeRemainder h.symm
    have hWallRemainder : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel transfer remainder :=
      shift.movingTarget_refines.rel hRelRemainder
    refine ⟨⟨transfer, remainder, hRelTransfer, hNotFirst, hNotSecond, hNeTransfer,
      hRelRemainder⟩, ?_⟩
    have hTransferWall : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel input.distinguishedBlock.1 transfer :=
      shift.movingAnchor_wall_rel.trans (shift.movingTarget_refines.rel hRelTransfer)
    have hBlockXW : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block transfer = ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block input.distinguishedBlock.1 :=
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block_eq_of_rel hTransferWall).symm
    have hBlockXM : ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block transfer = ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block shift.movingAnchor :=
      (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block_eq_of_rel hRelTransfer).symm
    have hDetachW := ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet_block_remainder transfer remainder hNeTransfer
      hWallRemainder
    have hDetachM := ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).detachSheet_block_remainder transfer remainder hNeTransfer
      hRelRemainder
    refine selectedCensus_of_blocks data hc hab hOne fullDim star input shift hMoving
      _ _ _ ?_ ?_ ?_
    · -- the divalent endpoint carries `e_α`
      intro sheet hSheet
      by_cases hRel : ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).Rel shift.movingAnchor sheet
      · have hMemP : sheet ∈ (data.vertexPartition (movingEndpoint data hc hab hOne star input shift).1.1).block (movingEndpoint data hc hab hOne star input shift).1.2 := by
          rw [hPeq]
          exact (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mem_block_iff _ _).mpr hRel
        rw [hInU sheet hMemP, hPeq]
        exact ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block_eq_of_rel hRel
      · have hNotP : sheet ∉ (data.vertexPartition (movingEndpoint data hc hab hOne star input shift).1.1).block (movingEndpoint data hc hab hOne star input shift).1.2 := by
          rw [hPeq]
          exact fun h ↦ hRel ((((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mem_block_iff _ _).mp h)
        rw [hOutU sheet hSheet hNotP]
        exact (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block_eq_singleton_of_blockCard_eq_one sheet
          (moving_blockCard_eq_one shift sheet (hWallRel sheet hSheet) hRel)).symm
    · -- the trivalent endpoint carries `A₀ ∖ {x}`
      intro sheet hSheet
      by_cases hEq : sheet = transfer
      · have hNotQ : sheet ∉ (data.vertexPartition (firstEndpoint data hc hab hOne star input shift).1.1).block (firstEndpoint data hc hab hOne star input shift).1.2 := by
          rw [hQeq, hEq]
          exact fun h ↦ (Finset.mem_erase.mp h).1 rfl
        rw [hOutV sheet hSheet hNotQ, hEq]
        exact (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet_block_single transfer remainder hNeTransfer
          hWallRemainder).symm
      · have hMemErased : sheet ∈ (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block input.distinguishedBlock.1).erase transfer :=
          Finset.mem_erase.mpr ⟨hEq, (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).mem_block_iff _ _).mpr (hWallRel sheet hSheet)⟩
        have hMemQ : sheet ∈ (data.vertexPartition (firstEndpoint data hc hab hOne star input shift).1.1).block (firstEndpoint data hc hab hOne star input shift).1.2 := by
          rw [hQeq]
          exact hMemErased
        have hMemDetach : sheet ∈ (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet transfer remainder hNeTransfer
            hWallRemainder).block remainder := by
          rw [hDetachW, hBlockXW]
          exact hMemErased
        have hDetachSheetBlock : (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet transfer remainder hNeTransfer
            hWallRemainder).block sheet = (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block input.distinguishedBlock.1).erase transfer := by
          rw [← SheetPartition.block_eq_of_rel _ (((((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet transfer remainder
            hNeTransfer hWallRemainder).mem_block_iff _ _).mp hMemDetach), hDetachW,
            hBlockXW]
        rw [hInV sheet hMemQ, hQeq, hDetachSheetBlock]
    · -- the contracted occurrence carries `e_α ∖ {x}`
      intro sheet hSheet
      by_cases hEq : sheet = transfer
      · have hNotI : sheet ∉ (data.edgePartition internal.1.1).block internal.1.2 := by
          rw [hIeq, hEq]
          exact fun h ↦ (Finset.mem_erase.mp h).1 rfl
        rw [hOutI sheet hSheet hNotI, hEq]
        exact (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).detachSheet_block_single transfer remainder hNeTransfer
          hRelRemainder).symm
      · by_cases hRel : ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).Rel shift.movingAnchor sheet
        · have hMemErased : sheet ∈ (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block shift.movingAnchor).erase transfer :=
            Finset.mem_erase.mpr ⟨hEq, (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mem_block_iff _ _).mpr hRel⟩
          have hMemI : sheet ∈ (data.edgePartition internal.1.1).block internal.1.2 := by
            rw [hIeq]
            exact hMemErased
          have hMemDetach : sheet ∈ (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).detachSheet transfer remainder hNeTransfer
              hRelRemainder).block remainder := by
            rw [hDetachM, hBlockXM]
            exact hMemErased
          have hDetachSheetBlock : (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).detachSheet transfer remainder hNeTransfer
              hRelRemainder).block sheet =
              (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block shift.movingAnchor).erase transfer := by
            rw [← SheetPartition.block_eq_of_rel _ (((((contractDatum data hc hab hOne).edgePartition shift.movingTarget).detachSheet transfer remainder
              hNeTransfer hRelRemainder).mem_block_iff _ _).mp hMemDetach), hDetachM,
              hBlockXM]
          rw [hInI sheet hMemI, hIeq, hDetachSheetBlock]
        · have hNotRelX : ¬((contractDatum data hc hab hOne).edgePartition shift.movingTarget).Rel transfer sheet := fun h ↦ hRel (hRelTransfer.trans h)
          have hNotI : sheet ∉ (data.edgePartition internal.1.1).block internal.1.2 := by
            rw [hIeq]
            exact fun h ↦ hRel ((((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mem_block_iff _ _).mp (Finset.mem_erase.mp h).2)
          rw [hOutI sheet hSheet hNotI, ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).detachSheet_block_of_not_rel transfer
            remainder sheet hNeTransfer hRelRemainder hNotRelX]
          exact (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block_eq_singleton_of_blockCard_eq_one sheet
            (moving_blockCard_eq_one shift sheet (hWallRel sheet hSheet) hRel)).symm
  · -- Position II.a
    refine Or.inr ⟨extra, hSep, hRelExtra, ?_⟩
    have hExtraSingleton : ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block extra = {extra} :=
      ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block_eq_singleton_of_blockCard_eq_one extra
        (moving_blockCard_eq_one shift extra hRelExtra hSep)
    have hMergeFirst : (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mergeBlocks shift.movingAnchor extra hSep).block
        shift.movingAnchor = insert extra (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block shift.movingAnchor) := by
      rw [((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mergeBlocks_block_first shift.movingAnchor extra hSep, hExtraSingleton,
        Finset.union_comm, Finset.singleton_union]
    refine selectedCensus_of_blocks data hc hab hOne fullDim star input shift hMoving
      _ _ _ ?_ ?_ ?_
    · intro sheet hSheet
      by_cases hRel : (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mergeBlocks shift.movingAnchor extra hSep).Rel
          shift.movingAnchor sheet
      · have hMemP : sheet ∈ (data.vertexPartition (movingEndpoint data hc hab hOne star input shift).1.1).block (movingEndpoint data hc hab hOne star input shift).1.2 := by
          rw [hPeq, ← hMergeFirst]
          exact ((((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mergeBlocks shift.movingAnchor extra hSep).mem_block_iff _ _).mpr hRel
        rw [hInU sheet hMemP, hPeq, ← hMergeFirst]
        exact (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mergeBlocks shift.movingAnchor extra hSep).block_eq_of_rel hRel
      · rw [((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mergeBlocks_rel_first_iff shift.movingAnchor extra sheet hSep,
          not_or] at hRel
        obtain ⟨hNotMoving, hNotExtra⟩ := hRel
        have hNotEq : sheet ≠ extra := fun h ↦ hNotExtra (h ▸ rfl)
        have hNotP : sheet ∉ (data.vertexPartition (movingEndpoint data hc hab hOne star input shift).1.1).block (movingEndpoint data hc hab hOne star input shift).1.2 := by
          rw [hPeq]
          intro h
          rcases Finset.mem_insert.mp h with hEq | hMem
          · exact hNotEq hEq
          · exact hNotMoving ((((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mem_block_iff _ _).mp hMem)
        rw [hOutU sheet hSheet hNotP, ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mergeBlocks_block_of_separate
          shift.movingAnchor extra sheet hSep (fun h ↦ hNotMoving h.symm)
          (fun h ↦ hNotExtra h.symm)]
        exact (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block_eq_singleton_of_blockCard_eq_one sheet
          (moving_blockCard_eq_one shift sheet (hWallRel sheet hSheet) hNotMoving)).symm
    · intro sheet hSheet
      have hMemQ : sheet ∈ (data.vertexPartition (firstEndpoint data hc hab hOne star input shift).1.1).block (firstEndpoint data hc hab hOne star input shift).1.2 := by
        rw [hQeq]
        exact (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).mem_block_iff _ _).mpr (hWallRel sheet hSheet)
      rw [hInV sheet hMemQ, hQeq]
      exact ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block_eq_of_rel (hWallRel sheet hSheet)
    · intro sheet hSheet
      by_cases hRel : (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mergeBlocks shift.movingAnchor extra hSep).Rel
          shift.movingAnchor sheet
      · have hMemI : sheet ∈ (data.edgePartition internal.1.1).block internal.1.2 := by
          rw [hIeq, ← hMergeFirst]
          exact ((((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mergeBlocks shift.movingAnchor extra hSep).mem_block_iff _ _).mpr hRel
        rw [hInI sheet hMemI, hIeq, ← hMergeFirst]
        exact (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mergeBlocks shift.movingAnchor extra hSep).block_eq_of_rel hRel
      · rw [((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mergeBlocks_rel_first_iff shift.movingAnchor extra sheet hSep,
          not_or] at hRel
        obtain ⟨hNotMoving, hNotExtra⟩ := hRel
        have hNotEq : sheet ≠ extra := fun h ↦ hNotExtra (h ▸ rfl)
        have hNotI : sheet ∉ (data.edgePartition internal.1.1).block internal.1.2 := by
          rw [hIeq]
          intro h
          rcases Finset.mem_insert.mp h with hEq | hMem
          · exact hNotEq hEq
          · exact hNotMoving ((((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mem_block_iff _ _).mp hMem)
        rw [hOutI sheet hSheet hNotI, ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).mergeBlocks_block_of_separate
          shift.movingAnchor extra sheet hSep (fun h ↦ hNotMoving h.symm)
          (fun h ↦ hNotExtra h.symm)]
        exact (((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block_eq_singleton_of_blockCard_eq_one sheet
          (moving_blockCard_eq_one shift sheet (hWallRel sheet hSheet) hNotMoving)).symm

end Census

end DraismaVargas.LocalCases.W3ShiftSelectedCensus
