module

public import DraismaVargas.LocalCases.NonTrivalentValencyThreeTracks
public import DraismaVargas.LocalCases.WallSplitIncidenceOrdinary

@[expose] public section

/-!
# The valency-three Type III star count, and the link under (H-III)

Source: Vargas, Part II, arXiv:2609.09109, the combinatorial setup of the section on changing
combinatorial type (subsection `subsec-setup-determinants`: a combinatorial type
change is a Whitehead move on the *ambient* tracked graph, with the labelling
convention (1)) and the valency-3 case (subsection `subsec-case-v3`, case
`{v3-nd4}`, Type III, base tree `T_2`: the anchor `A` resolves into `A_u` and
`A_v` joined by the new occurrence `h_1`, with the two doubled-direction
survivors at `A_u` and the two simple ones at `A_v`), together with
Draisma–Vargas Part I, arXiv:1909.12924: the construction of the stable graph `H(M)` and its row
labels (compatible edge labellings and the limit-matrix lemma
`lemma-limit-matrix-change`) and the non-dangling valency formula
`lemma-ndval-of-GqA0`.

`NonTrivalentValencyThreeTracks` reduces `OuterWalk.TypeChangeLink` at a
three-valent wall to **one** geometric input, the star count `hIncidence` of
`typeChangeLink_of_incidence`.  This module proves that count under (H-III) =
`NonTrivalentValencyThreeTracks.PrescribedDoubledMove`, and hence delivers the
link.

## What is proved

### 1.  (T1): the wall datum's star descends to the candidate

* `incidenceCount_endpointVertex_true_ordinary`: **at an ordinary wall block**
  the trivalent end `B_v` of the candidate keeps the block's row-filtered star.
  The bijection is `trivEnd`: a retained survivor of a simple direction stays
  itself, a doubled-direction survivor is replaced by the new occurrence of its
  own fine class.
  `NonTrivalentValencyThreeDescent.nonDanglingIncident_endpointVertex_true_ordinary`
  lists the target star, `stablePath_retainedEdge_eq_newSourceEdge` puts the new
  occurrence on the row of the survivor it replaces, and `retainedRow` is
  injective (`injective_retainedRow`, from
  `NonTrivalentValencyThreeRowEquiv.rowEquiv`), so the row filter transports.
* `incidenceCount_candVertex`: (T1) at every wall-datum vertex other than the
  anchor -- the ordinary-block case above, and
  `NonTrivalentValencyThreeTracks.incidenceCount_retainedVertex_retainedRow` off
  the merged target vertex.

### 2.  (T2): the wall datum's star lifts to the incoming cover

* `internalEdges_subsingleton_of_ne_anchor`: **an ordinary wall block is
  unramified**, hence its pruned fibre carries at most one internal occurrence.
  Part II `lemma-above-w0` at valency three
  (`NonTrivalentValencyThreeRigidity.localRamification_eq_zero_of_ne_anchor`,
  then `localRamification_eq_zero_in_fibre` and `internalEdges_subsingleton`)
  gives it at the merged target vertex; away from it the fibre has no internal
  occurrence at all (`internalEdges_eq_empty_of_away`).
* `incidenceCount_wall_eq_incoming`: (T2) at every wall-datum vertex other than
  the anchor, from the valency-agnostic
  `WallSplitIncidenceOrdinary.incidenceCount_unramified`.

### 3.  The star count

* `incidence_inl_retained`, `incidence_inl_bridge`: away from the anchor.  On a
  retained row the count is (T1) then (T2) then
  `NonTrivalentValencyThreeTracks.card_star_eq_incidenceCount`, with
  `move_vert_eq_iff_of_ne` erasing the move; on the bridge row both sides
  vanish -- downstairs `h_1` joins `A_u` to `A_v`, upstairs the vanishing chart
  row is the single occurrence `h_1`.
* `incidence_inr_false_retained`, `incidence_inr_false_bridge`: **at `A_u`.**
  The exact star `{h_1, e_2, e_5}` of `NonTrivalentValencyThreeRows`
  (`nonDanglingIncident_endpointVertex_false`, read on surviving occurrences as
  `incidentEdges_endpointVertex_false`) is matched dart by dart with the moved
  star `{m.base, t_2, t_5}` that (H-III) prescribes (`filter_moved_base`,
  `dart_ne`).  `outLabelling_row_bridge` puts the bridge row on `label m.base`,
  `incomingRow_ne_facet` keeps every retained row off it, and
  `label_dart_doubled_iff` identifies the two remaining darts -- from the
  **row** equality of (H-III) alone (`IncomingPairing.label_dart_of_row`), which
  is all the count needs and all a pass-through survivor can give.
* `incidence_inr_true`: **at `A_v`, from the leftover equation.**  A stable row
  of the candidate meets its branch vertices twice in all
  (`sum_incidenceCount_branchVertex`, from `StableSourceDarts.card_row`), a
  chart row carries exactly two darts of the tracked graph
  (`card_filter_label`, `sum_natCard_moved`), and `vertexEquiv` is a bijection;
  the count agrees at every other branch vertex, so it agrees at `A_v`.
* `incidence_of_prescribedDoubledMove`: the star count at every branch vertex
  and every row, and `typeChangeLink_of_prescribedDoubledMove`:
  **`OuterWalk.TypeChangeLink` at a three-valent wall from (H-III) alone.**

## The hypotheses that remain explicit

1. `hPres : NonTrivalentValencyThreeTracks.PrescribedDoubledMove m wd wallStar src`,
   i.e. (H-III), at row level: the two darts the move places with `m.base`
   carry the rows of the two doubled-direction survivors.
   `NonTrivalentValencyThreeTracks` supplies its relative non-vacuity witness
   `prescribedDoubledMove_prescribedMove` from `DoubledSeparated` and the
   orientation clause, and the dispatcher's producer
   `prescribedDoubledMove_of_rows`; neither is derived here.
2. `wallStar : ThirdEquation.ThreeStar (contract wd.coverTarget wd.hab wd.hOne)
   <wd.a, wd.hab>`, `src : ThreeBranchAnchor ...`, `hNoGlue`, `hValid` -- exactly
   the four carried by `NonTrivalentValencyThreeTracks.typeChangeLink_of_incidence`
   and `NonTrivalentValencyThreeExit.exists_anchor_of_wallData`.  The valency
   dispatcher of `OuterWalk.WallData.valency` is not built here.
3. Nothing else: `hPathEnds` is supplied by `WallDatumPathEnds`,
   `NoContractedReturn` (`StablePathFacetContraction`) through
   `NonTrivalentValencyThreeExit`, and the branch-vertex bijection is
   `NonTrivalentValencyThreeTracks.vertexEquiv`.

No structure is introduced.  Every definition (`trivEnd`, `trivEndEdge`,
`doubledWall`, `doubledRetained`, `bridgeND`) is a named occurrence or vertex of
an object already built, and each is applied in the theorems above.

## Consumers

`OuterWalk.TypeChangeLink` at Part II case `{v3-nd4}`, hence the `link`
hypothesis of `OuterWalk.coneEntry_of_reaches`, once the valency dispatcher
(`NonTrivalentValencyThreeDispatcher`) supplies `wallStar` and the walk
supplies (H-III).
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeStarCount

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeRows
open DraismaVargas.LocalCases.NonTrivalentValencyThreeDescent

noncomputable section

/-! ## 1.  (T1) at an ordinary wall block -/

section Ordinary

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall}
  (source : ThreeBranchAnchor data star anchor)
  (hNoGlue : DanglingEdgeNoGlue data) (hValid : data.Valid)

local notation "cand" => (Prescribed.validCandidate source hNoGlue hValid)

/-- **The retained-row map is injective**, from the row dictionary. -/
theorem injective_retainedRow :
    Function.Injective (NonTrivalentValencyThreeDescent.retainedRow source hNoGlue hValid) := by
  intro r r' h
  have h2 := congrArg (NonTrivalentValencyThreeRowEquiv.rowEquiv source hNoGlue hValid) h
  rw [NonTrivalentValencyThreeRowEquiv.rowEquiv_retainedRow source hNoGlue hValid r,
    NonTrivalentValencyThreeRowEquiv.rowEquiv_retainedRow source hNoGlue hValid r'] at h2
  exact Option.some_injective _ h2

/-- A retained row is never the bridge row. -/
theorem retainedRow_ne_bridgeRow (r : StablePath data) :
    NonTrivalentValencyThreeDescent.retainedRow source hNoGlue hValid r ≠
      NonTrivalentValencyThreeRowEquiv.bridgeRow source hNoGlue hValid := by
  intro hBad
  have h := congrArg (NonTrivalentValencyThreeRowEquiv.rowEquiv source hNoGlue hValid) hBad
  rw [NonTrivalentValencyThreeRowEquiv.rowEquiv_retainedRow source hNoGlue hValid r,
    NonTrivalentValencyThreeRowEquiv.rowEquiv_bridgeRow source hNoGlue hValid] at h
  exact Option.some_ne_none r h

/-- The representative of a survivor of an ordinary wall block at the trivalent
end: the retained occurrence itself on the `v` side, the new occurrence of its
own fine class on the `u` side. -/
def trivEndEdge (e : NonDanglingEdge data) : (cand).datum.SourceEdge :=
  if Prescribed.rightAssignment source e.1.1.1 then (cand).oldSourceEdge e.1
  else (cand).newSourceEdge e.1.1.2

theorem trivEndEdge_survives {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (e : NonDanglingEdge data)
    (hInc : Incident data e.1 (data.sourceEndpoint wall x)) :
    ¬ IsDangling (cand).datum (trivEndEdge source hNoGlue hValid e) := by
  classical
  unfold trivEndEdge
  by_cases hs : Prescribed.rightAssignment source e.1.1.1 = true
  · rw [ite_eq_left hs]
    exact ResolutionSurvival.not_isDangling_oldSourceEdge (cand) hValid.1 e.1 e.2
  · have hs' : Prescribed.rightAssignment source e.1.1.1 = false := by
      simpa using hs
    rw [ite_eq_right hs]
    exact newSourceEdge_survives_of_mem_ordinaryStar source hNoGlue hValid hX
      ((mem_ordinaryStar source e.1).mpr ⟨⟨e.2, hInc⟩, hs'⟩)

/-- The same representative, as a surviving occurrence of the candidate. -/
def trivEnd {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (e : NonDanglingEdge data) (hInc : Incident data e.1 (data.sourceEndpoint wall x)) :
    NonDanglingEdge (cand).datum :=
  ⟨trivEndEdge source hNoGlue hValid e,
    trivEndEdge_survives source hNoGlue hValid hX e hInc⟩

theorem stablePath_trivEnd {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (e : NonDanglingEdge data)
    (hInc : Incident data e.1 (data.sourceEndpoint wall x)) :
    (trivEnd source hNoGlue hValid hX e hInc).stablePath =
      NonTrivalentValencyThreeDescent.retainedRow source hNoGlue hValid e.stablePath := by
  classical
  rw [NonTrivalentValencyThreeDescent.retainedRow_mk source hNoGlue hValid e]
  by_cases hs : Prescribed.rightAssignment source e.1.1.1 = true
  · refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
    show trivEndEdge source hNoGlue hValid e = (cand).oldSourceEdge e.1
    unfold trivEndEdge
    rw [ite_eq_left hs]
  · have hs' : Prescribed.rightAssignment source e.1.1.1 = false := by
      simpa using hs
    have hOld : e.1 ∈ ordinaryStar source x false :=
      (mem_ordinaryStar source e.1).mpr ⟨⟨e.2, hInc⟩, hs'⟩
    rw [stablePath_retainedEdge_eq_newSourceEdge source hNoGlue hValid hX hOld]
    refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
    show trivEndEdge source hNoGlue hValid e = (cand).newSourceEdge e.1.1.2
    unfold trivEndEdge
    rw [ite_eq_right hs]

theorem incident_trivEnd {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (e : NonDanglingEdge data)
    (hInc : Incident data e.1 (data.sourceEndpoint wall x)) :
    Incident (cand).datum (trivEnd source hNoGlue hValid hX e hInc).1
      (endpointVertex source hNoGlue hValid true x) := by
  classical
  by_cases hs : Prescribed.rightAssignment source e.1.1.1 = true
  · have hOld : e.1 ∈ ordinaryStar source x true :=
      (mem_ordinaryStar source e.1).mpr ⟨⟨e.2, hInc⟩, hs⟩
    have hVal : (trivEnd source hNoGlue hValid hX e hInc).1 = (cand).oldSourceEdge e.1 := by
      show trivEndEdge source hNoGlue hValid e = _
      unfold trivEndEdge
      rw [ite_eq_left hs]
    rw [hVal]
    exact (incident_oldSourceEdge_endpointVertex_iff source hNoGlue hValid true hX e.1).mpr
      ⟨⟨mem_incidentEdges_of_mem_ordinaryStar source hOld,
        wall_rel_of_mem_ordinaryStar source hOld⟩, hs⟩
  · have hs' : Prescribed.rightAssignment source e.1.1.1 = false := by
      simpa using hs
    have hOld : e.1 ∈ ordinaryStar source x false :=
      (mem_ordinaryStar source e.1).mpr ⟨⟨e.2, hInc⟩, hs'⟩
    have hVal : (trivEnd source hNoGlue hValid hX e hInc).1 = (cand).newSourceEdge e.1.1.2 := by
      show trivEndEdge source hNoGlue hValid e = _
      unfold trivEndEdge
      rw [ite_eq_right hs]
    rw [hVal]
    exact incident_newSourceEdge_endpointVertex_true source hNoGlue hValid hX hOld

/-- **(T1) at an ordinary wall block.**  The trivalent end of a non-anchor wall
block keeps the block's row-filtered star: the retained copies of the simple
directions, and one new occurrence for each doubled-direction survivor, on the
row of the survivor it replaces. -/
theorem incidenceCount_endpointVertex_true_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (row : StablePath data) :
    incidenceCount data (data.sourceEndpoint wall x) row =
      incidenceCount (cand).datum (endpointVertex source hNoGlue hValid true x)
        (NonTrivalentValencyThreeDescent.retainedRow source hNoGlue hValid row) := by
  classical
  unfold incidenceCount
  refine Finset.card_bij (fun e he ↦ trivEnd source hNoGlue hValid hX e
    ((mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp he).1)) ?_ ?_ ?_
  · intro e he
    obtain ⟨hMem, hRow⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr
      (incident_trivEnd source hNoGlue hValid hX e _), ?_⟩
    rw [stablePath_trivEnd source hNoGlue hValid hX e _, hRow]
  · intro e₁ he₁ e₂ he₂ hEq
    have hVal : trivEndEdge source hNoGlue hValid e₁ = trivEndEdge source hNoGlue hValid e₂ :=
      congrArg Subtype.val hEq
    unfold trivEndEdge at hVal
    by_cases hs₁ : Prescribed.rightAssignment source e₁.1.1.1 = true <;>
      by_cases hs₂ : Prescribed.rightAssignment source e₂.1.1.1 = true
    · rw [ite_eq_left hs₁, ite_eq_left hs₂] at hVal
      exact Subtype.ext (ResolutionCut.oldSourceEdge_injective (cand) hVal)
    · rw [ite_eq_left hs₁, ite_eq_right hs₂] at hVal
      exact absurd hVal.symm
        (newSourceEdge_ne_oldSourceEdge source hNoGlue hValid e₂.1.1.2 e₁.1)
    · rw [ite_eq_right hs₁, ite_eq_left hs₂] at hVal
      exact absurd hVal (newSourceEdge_ne_oldSourceEdge source hNoGlue hValid e₁.1.1.2 e₂.1)
    · rw [ite_eq_right hs₁, ite_eq_right hs₂] at hVal
      have hs₁' : Prescribed.rightAssignment source e₁.1.1.1 = false := by simpa using hs₁
      have hs₂' : Prescribed.rightAssignment source e₂.1.1.1 = false := by simpa using hs₂
      have hOld₁ : e₁.1 ∈ ordinaryStar source x false :=
        (mem_ordinaryStar source e₁.1).mpr
          ⟨⟨e₁.2, (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp he₁).1⟩, hs₁'⟩
      have hOld₂ : e₂.1 ∈ ordinaryStar source x false :=
        (mem_ordinaryStar source e₂.1).mpr
          ⟨⟨e₂.2, (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp he₂).1⟩, hs₂'⟩
      exact Subtype.ext
        (newSourceEdge_sheet_injOn source hNoGlue hValid hX hOld₁ hOld₂ hVal)
  · intro f hf
    obtain ⟨hMem, hRow⟩ := Finset.mem_filter.mp hf
    have hStar : f.1 ∈ nonDanglingIncident (cand).datum
        (endpointVertex source hNoGlue hValid true x) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, (mem_incidentEdges _ _ _).mp hMem⟩
    rw [nonDanglingIncident_endpointVertex_true_ordinary source hNoGlue hValid hX,
      Finset.mem_union, Finset.mem_image, Finset.mem_image] at hStar
    rcases hStar with ⟨old, hOld, hEq⟩ | ⟨old, hOld, hEq⟩
    · obtain ⟨⟨hSurv, hIncOld⟩, hSide⟩ := (mem_ordinaryStar source old).mp hOld
      refine ⟨⟨old, hSurv⟩, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hIncOld, ?_⟩
        refine injective_retainedRow source hNoGlue hValid ?_
        rw [← stablePath_trivEnd source hNoGlue hValid hX ⟨old, hSurv⟩ hIncOld]
        refine Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)) hRow
        show trivEndEdge source hNoGlue hValid ⟨old, hSurv⟩ = f.1
        unfold trivEndEdge
        rw [ite_eq_left hSide]
        exact hEq
      · refine Subtype.ext ?_
        show trivEndEdge source hNoGlue hValid ⟨old, hSurv⟩ = f.1
        unfold trivEndEdge
        rw [ite_eq_left hSide]
        exact hEq
    · obtain ⟨⟨hSurv, hIncOld⟩, hSide⟩ := (mem_ordinaryStar source old).mp hOld
      have hSide' : ¬ (Prescribed.rightAssignment source old.1.1 = true) := by
        rw [hSide]
        simp
      refine ⟨⟨old, hSurv⟩, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hIncOld, ?_⟩
        refine injective_retainedRow source hNoGlue hValid ?_
        rw [← stablePath_trivEnd source hNoGlue hValid hX ⟨old, hSurv⟩ hIncOld]
        refine Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)) hRow
        show trivEndEdge source hNoGlue hValid ⟨old, hSurv⟩ = f.1
        unfold trivEndEdge
        rw [ite_eq_right hSide']
        exact hEq
      · refine Subtype.ext ?_
        show trivEndEdge source hNoGlue hValid ⟨old, hSurv⟩ = f.1
        unfold trivEndEdge
        rw [ite_eq_right hSide']
        exact hEq

end Ordinary

/-! ## 2.  The two transports at a wall of the outer walk -/

section Wall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.PrunedFibreValency
open DraismaVargas.LocalCases.PrunedFibreTree
open DraismaVargas.LocalCases.FullContractionFibre
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.ClassInjectivity
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.OuterWalk

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  {wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
  (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)

/-- **(T1), at every wall-datum vertex other than the anchor.**  Off the merged
target vertex this is `NonTrivalentValencyThreeTracks.incidenceCount_retainedVertex_retainedRow`; at
an ordinary wall block it is the ordinary-block census above. -/
theorem incidenceCount_candVertex
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hne : w ≠ NonTrivalentValencyThreeTracks.anchorVertex m wd anchorBlk)
    (row : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) w row =
      incidenceCount (Prescribed.validCandidate src hNoGlue hValid).datum
        (NonTrivalentValencyThreeTracks.candVertex m wd src hNoGlue hValid w)
        (NonTrivalentValencyThreeDescent.retainedRow src hNoGlue hValid row) := by
  classical
  by_cases hw : w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
  · rw [NonTrivalentValencyThreeTracks.candVertex_wall m wd src hNoGlue hValid w hw]
    conv_lhs => rw [← NonTrivalentValencyThreeTracks.sourceEndpoint_self m wd w hw]
    exact incidenceCount_endpointVertex_true_ordinary src hNoGlue hValid
      (NonTrivalentValencyThreeTracks.not_rel_anchor_of_ne m wd w hw hne) row
  · rw [NonTrivalentValencyThreeTracks.candVertex_away m wd src hNoGlue hValid w hw]
    exact NonTrivalentValencyThreeTracks.incidenceCount_retainedVertex_retainedRow m wd src
      hNoGlue hValid w hw row

/-- The injectivity of the incoming-row map, with no further hypothesis at a
three-valent wall (`NoContractedReturn`, through `NonTrivalentValencyThreeExit`). -/
theorem injective_incomingRow
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    Function.Injective (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hCompat m) (wd.hForest m)) :=
  WallSplitIncidence.injective_incomingRow_of_noContractedReturn wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne (wd.hCompat m) (wd.hForest m)
    (NonTrivalentValencyThreeExit.noContractedReturn_of_valency_three m wd wallStar)

/-- Away from the merged target vertex the pruned fibre carries no internal
occurrence. -/
theorem internalEdges_eq_empty_of_away
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hw : w.1.1 ≠ (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)) :
    internalEdges wd.cover wd.hc wd.hab wd.hOne w = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem ?_
  intro e he
  obtain ⟨-, hT, hMap⟩ := (mem_internalEdges wd.cover wd.hc wd.hab wd.hOne w e).mp he
  have h1 : (wd.cover.sourceEnds e).1.1.1 = wd.a := by
    rw [sourceEnds_fst_fst wd.cover e, hT]
  have h2 := congrArg
    (fun z : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex ↦ z.1.1) hMap
  change GraphContraction.fold wd.coverTarget wd.hab (wd.cover.sourceEnds e).1.1.1 = w.1.1 at h2
  rw [h1, GraphContraction.fold_a] at h2
  exact hw h2.symm

/-- **An ordinary wall block is unramified**, so its pruned fibre carries at
most one internal occurrence: Part II `lemma-above-w0` at valency three
(`NonTrivalentValencyThreeRigidity`) says the four-valent anchor consumes the
wall's whole unit of ramification. -/
theorem internalEdges_subsingleton_of_ne_anchor
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hne : w ≠ NonTrivalentValencyThreeTracks.anchorVertex m wd anchorBlk) :
    ∀ e ∈ internalEdges wd.cover wd.hc wd.hab wd.hOne w,
      ∀ f ∈ internalEdges wd.cover wd.hc wd.hab wd.hOne w, e = f := by
  classical
  by_cases hw : w.1.1 = (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
  · have hFixed : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).repr w.1.2 = w.1.2 := by
      have h := w.2
      rw [hw] at h
      exact h
    set blk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) := ⟨w.1.2, hFixed⟩ with hblk
    have hBlkVertex : WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b) blk = w :=
      NonTrivalentValencyThreeTracks.sourceEndpoint_self m wd w hw
    have hBlkNe : blk ≠ anchorBlk := by
      intro hBad
      exact hne (hBlkVertex.symm.trans (congrArg
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)) hBad))
    have hRamZero := NonTrivalentValencyThreeRigidity.localRamification_eq_zero_of_ne_anchor
      wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) (wd.hCompat m) wallStar anchorBlk
      (NonTrivalentValencyThreeRows.nonDanglingValency_anchor src) blk hBlkNe
    set merged : (mergedPartition wd.cover wd.a wd.b).Blocks := ⟨w.1.2, by
      rw [← contractDatum_vertexPartition_merge wd.cover wd.hc wd.hab wd.hOne]
      exact hFixed⟩ with hmerged
    have hMergedVertex : mergedVertex wd.cover wd.hc wd.hab wd.hOne merged = w :=
      Subtype.ext (Prod.ext hw.symm rfl)
    refine NonTrivalentValencyThreeRigidity.internalEdges_subsingleton wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne w ?_
    intro point hPoint
    exact NonTrivalentValencyThreeRigidity.localRamification_eq_zero_in_fibre wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) merged hRamZero point
      (hPoint.trans hMergedVertex.symm)
  · intro e he
    rw [internalEdges_eq_empty_of_away m wd w hw] at he
    exact absurd he (Finset.notMem_empty e)

/-- **(T2), at every wall-datum vertex other than the anchor.**  Off the merged
target vertex this is `WallSplitIncidence.incidenceCount_sourceVertexMap`; at an ordinary
wall block it is `WallSplitIncidenceOrdinary.incidenceCount_unramified`, whose
input is the vanishing ramification above. -/
theorem incidenceCount_wall_eq_incoming
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (w : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hne : w ≠ NonTrivalentValencyThreeTracks.anchorVertex m wd anchorBlk)
    (u : wd.cover.SourceVertex)
    (hMapU : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne u = w)
    (hThreeU : 3 ≤ nonDanglingValency wd.cover u)
    (row : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) w row =
      incidenceCount wd.cover u (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) row) :=
  WallSplitIncidenceOrdinary.incidenceCount_unramified wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (wd.hCompat m) (wd.hForest m) (injective_incomingRow m wd wallStar) wd.fullDim.connected
    w u hMapU hThreeU
    (NonTrivalentValencyThreeTracks.wallDatum_trivalent_away_anchor m wd wallStar src w hne)
    wd.fullDim.trivalent
    (internalEdges_subsingleton_of_ne_anchor m wd wallStar src w hne) row

/-! ## 3.  The dart side -/

include wd in
/-- Every chart coordinate labels exactly two darts of the tracked graph: the
incoming tracking carries the two darts of its stable row. -/
theorem card_filter_label (c : coordinate) :
    (Finset.univ.filter fun d : D ↦ label d = c).card = 2 := by
  classical
  have hEq : (Finset.univ.filter fun e : StableSourceDarts.Dart wd.cover ↦
        StableSourceDarts.row wd.cover e = wd.fullDim.labelling.row.symm c).card =
      (Finset.univ.filter fun d : D ↦ label d = c).card := by
    refine Finset.card_bij (fun e _ ↦ wd.tracks.iso.dart e) ?_ ?_ ?_
    · intro e he
      have hRow := (Finset.mem_filter.mp he).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [wd.tracks.row_map e, hRow, Equiv.apply_symm_apply]
    · intro e₁ _ e₂ _ hEq2
      exact wd.tracks.iso.dart.injective hEq2
    · intro d hd
      have hLab := (Finset.mem_filter.mp hd).2
      refine ⟨wd.tracks.iso.dart.symm d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
        Equiv.apply_symm_apply _ _⟩
      have h := wd.tracks.row_map (wd.tracks.iso.dart.symm d)
      rw [Equiv.apply_symm_apply, hLab] at h
      exact wd.fullDim.labelling.row.injective (by rw [Equiv.apply_symm_apply]; exact h.symm)
  rw [← hEq, ← Fintype.card_subtype]
  exact StableSourceDarts.card_row wd.cover wd.fullDim.connected wd.fullDim.pathEnds _

/-- A retained chart row is not the vanishing one. -/
theorem labelling_row_incomingRow_ne_base
    (row : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hCompat m) (wd.hForest m) row) ≠ label m.base := by
  intro hBad
  refine incomingRow_ne_facet wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m)
    (wd.hForest m) wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero
    row ?_
  exact (Equiv.eq_symm_apply _).mpr hBad

/-- Away from the two ends of the vanishing occurrence the moved star of a
chart row is the star of the incoming cover. -/
theorem natCard_moved_of_ne (u : BranchVertex wd.cover)
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (hBase : wd.tracks.iso.dart (NonTrivalentValencyThreeTracks.facetDartLeft m wd wallStar) =
      m.base)
    (hul : u.1 ≠ NonTrivalentValencyThreeTracks.leftEnd m wd)
    (hur : u.1 ≠ NonTrivalentValencyThreeTracks.rightEnd m wd)
    (row : StablePath wd.cover) :
    Nat.card {d : D // graph.vert (m.perm d) = wd.tracks.iso.vtx u ∧
        label d = wd.fullDim.labelling.row row} =
      incidenceCount wd.cover u.1 row := by
  have hNeBase : wd.tracks.iso.vtx u ≠ graph.vert m.base := by
    rw [NonTrivalentValencyThreeTracks.vert_base_eq m wd wallStar hBase]
    intro hBad
    exact hul (congrArg Subtype.val (wd.tracks.iso.vtx.injective hBad))
  have hNeOp : wd.tracks.iso.vtx u ≠ graph.vert (graph.op m.base) := by
    rw [NonTrivalentValencyThreeTracks.vert_opBase_eq m wd wallStar hBase]
    intro hBad
    exact hur (congrArg Subtype.val (wd.tracks.iso.vtx.injective hBad))
  rw [NonTrivalentValencyThreeTracks.card_star_eq_incidenceCount m wd u row]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun d ↦ and_congr_left'
    (NonTrivalentValencyThreeTracks.move_vert_eq_iff_of_ne m hNeBase hNeOp d))

/-! ## 4.  The chart rows of the outgoing presentation -/

/-- A retained row of the outgoing presentation keeps the chart coordinate of
its own incoming row (`NonTrivalentValencyThreeExit`). -/
theorem outFD_row_retained
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (NonTrivalentValencyThreeExit.wallOutgoingFD m wd src hNoGlue hValid
        (NonTrivalentValencyThreePathEnds.hasPathEnds_wallData m wd src hNoGlue
          hValid)).labelling.row
      (NonTrivalentValencyThreeDescent.retainedRow src hNoGlue hValid p) =
      wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) p) :=
  NonTrivalentValencyThreeExit.outLabelling_row_retained wd.cover wd.fullDim wd.hc wd.hab
    wd.hOne (wd.hForest m)
    (NonTrivalentValencyThreeExit.noContractedReturn_of_valency_three m wd wallStar)
    wd.coordinates (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord wd.hFacetZero src
    hNoGlue hValid p

/-- The bridge row of the outgoing presentation occupies the vanishing chart
row `label m.base` (`NonTrivalentValencyThreeExit`). -/
theorem outFD_row_bridge
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid) :
    (NonTrivalentValencyThreeExit.wallOutgoingFD m wd src hNoGlue hValid
        (NonTrivalentValencyThreePathEnds.hasPathEnds_wallData m wd src hNoGlue
          hValid)).labelling.row
      (NonTrivalentValencyThreeRowEquiv.bridgeRow src hNoGlue hValid) = label m.base :=
  NonTrivalentValencyThreeExit.outLabelling_row_bridge wd.cover wd.fullDim wd.hc wd.hab
    wd.hOne (wd.hForest m)
    (NonTrivalentValencyThreeExit.noContractedReturn_of_valency_three m wd wallStar)
    wd.coordinates (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord wd.hFacetZero src
    hNoGlue hValid

/-! ## 5.  Away from the anchor -/

/-- **The star count at a branch vertex away from the anchor, on a retained
row.**  It is (T1) followed by (T2) followed by the incoming tracking. -/
theorem incidence_inl_retained
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (hBase : wd.tracks.iso.dart
      (NonTrivalentValencyThreeTracks.facetDartLeft m wd wallStar) = m.base)
    (w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
      w.1 ≠ NonTrivalentValencyThreeTracks.anchorVertex m wd anchorBlk})
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (Prescribed.validCandidate src hNoGlue hValid).datum
        (NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid (Sum.inl w)).1
        (NonTrivalentValencyThreeDescent.retainedRow src hNoGlue hValid r₀) =
      Nat.card {d : D // graph.vert (m.perm d) =
          NonTrivalentValencyThreeTracks.vertexEquiv m wd wallStar src hNoGlue hValid
            (NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid (Sum.inl w)) ∧
        label d = (NonTrivalentValencyThreeExit.wallOutgoingFD m wd src hNoGlue hValid
          (NonTrivalentValencyThreePathEnds.hasPathEnds_wallData m wd src hNoGlue
            hValid)).labelling.row
          (NonTrivalentValencyThreeDescent.retainedRow src hNoGlue hValid r₀)} := by
  classical
  have hMapU : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne
      ((NonTrivalentValencyThreeTracks.branchEquivAnchorComplement m wd wallStar src).symm
        w).1.1 = w.1.1 := by
    have h := NonTrivalentValencyThreeTracks.branchEquivAnchorComplement_apply m wd wallStar src
      ((NonTrivalentValencyThreeTracks.branchEquivAnchorComplement m wd wallStar src).symm w)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  rw [NonTrivalentValencyThreeTracks.vertexEquiv_inl m wd wallStar src hNoGlue hValid w,
    outFD_row_retained m wd wallStar src hNoGlue hValid r₀,
    natCard_moved_of_ne m wd
      ((NonTrivalentValencyThreeTracks.branchEquivAnchorComplement m wd wallStar src).symm w).1
      wallStar hBase
      ((NonTrivalentValencyThreeTracks.branchEquivAnchorComplement m wd wallStar src).symm w).2.1
      ((NonTrivalentValencyThreeTracks.branchEquivAnchorComplement m wd wallStar src).symm w).2.2]
  refine Eq.trans ?_ (incidenceCount_wall_eq_incoming m wd wallStar src w.1.1 w.2
    ((NonTrivalentValencyThreeTracks.branchEquivAnchorComplement m wd wallStar src).symm w).1.1
    hMapU
    ((NonTrivalentValencyThreeTracks.branchEquivAnchorComplement m wd wallStar src).symm
      w).1.2 r₀)
  exact (incidenceCount_candVertex m wd src hNoGlue hValid w.1.1 w.2 r₀).symm

/-- The vanishing row of the incoming cover meets only the two ends of its
single occurrence. -/
theorem incidenceCount_facetRow_eq_zero
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (v : wd.cover.SourceVertex) (hl : v ≠ NonTrivalentValencyThreeTracks.leftEnd m wd)
    (hr : v ≠ NonTrivalentValencyThreeTracks.rightEnd m wd) :
    incidenceCount wd.cover v (NonTrivalentValencyThreeTracks.facetRow m wd) = 0 := by
  classical
  unfold incidenceCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hRow
  have hEq := NonTrivalentValencyThreeTracks.eq_facetEdge m wd wallStar e hRow
  have hInc := (mem_incidentEdges _ _ _).mp he
  rw [hEq] at hInc
  rcases hInc with h | h
  · exact hl h.symm
  · exact hr h.symm

/-- A branch vertex of the candidate away from the anchor is neither `A_u` nor
`A_v`. -/
theorem endpointVertex_ne_candBranchMap_inl
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid) (side : Bool)
    (w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
      w.1 ≠ NonTrivalentValencyThreeTracks.anchorVertex m wd anchorBlk}) :
    NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid side
        (Prescribed.selectedRepresentative src) ≠
      (NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid (Sum.inl w)).1 := by
  intro hBad
  exact Sum.inr_ne_inl
    (NonTrivalentValencyThreeTracks.candBranchMap_injective m wd src hNoGlue hValid
      (Subtype.ext hBad))

/-- The bridge row does not reach a branch vertex of the candidate away from
the anchor: its only occurrence joins `A_u` to `A_v`. -/
theorem incidenceCount_bridgeRow_inl_eq_zero
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
      w.1 ≠ NonTrivalentValencyThreeTracks.anchorVertex m wd anchorBlk}) :
    incidenceCount (Prescribed.validCandidate src hNoGlue hValid).datum
      (NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid (Sum.inl w)).1
      (NonTrivalentValencyThreeRowEquiv.bridgeRow src hNoGlue hValid) = 0 := by
  classical
  unfold incidenceCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hRow
  have hVal := NonTrivalentValencyThreeRows.bridgeEdge_isolated src hNoGlue hValid e hRow
  have hInc := (mem_incidentEdges _ _ _).mp he
  rw [hVal] at hInc
  have hInc' : ((Prescribed.validCandidate src hNoGlue hValid).datum.sourceEnds
        (NonTrivalentValencyThreeRows.bridgeEdge src hNoGlue hValid
          (Prescribed.selectedRepresentative src))).1 =
      (NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid (Sum.inl w)).1 ∨
      ((Prescribed.validCandidate src hNoGlue hValid).datum.sourceEnds
        (NonTrivalentValencyThreeRows.bridgeEdge src hNoGlue hValid
          (Prescribed.selectedRepresentative src))).2 =
      (NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid (Sum.inl w)).1 := hInc
  rw [NonTrivalentValencyThreeRows.sourceEnds_bridgeEdge src hNoGlue hValid _] at hInc'
  rcases hInc' with h | h
  · exact endpointVertex_ne_candBranchMap_inl m wd src hNoGlue hValid false w h
  · exact endpointVertex_ne_candBranchMap_inl m wd src hNoGlue hValid true w h

/-- **The star count at a branch vertex away from the anchor, on the bridge
row.**  Both sides vanish: downstairs the bridge joins `A_u` to `A_v`, upstairs
the vanishing chart row is the single occurrence `h_1`. -/
theorem incidence_inl_bridge
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (hBase : wd.tracks.iso.dart
      (NonTrivalentValencyThreeTracks.facetDartLeft m wd wallStar) = m.base)
    (w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
      w.1 ≠ NonTrivalentValencyThreeTracks.anchorVertex m wd anchorBlk}) :
    incidenceCount (Prescribed.validCandidate src hNoGlue hValid).datum
        (NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid (Sum.inl w)).1
        (NonTrivalentValencyThreeRowEquiv.bridgeRow src hNoGlue hValid) =
      Nat.card {d : D // graph.vert (m.perm d) =
          NonTrivalentValencyThreeTracks.vertexEquiv m wd wallStar src hNoGlue hValid
            (NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid (Sum.inl w)) ∧
        label d = (NonTrivalentValencyThreeExit.wallOutgoingFD m wd src hNoGlue hValid
          (NonTrivalentValencyThreePathEnds.hasPathEnds_wallData m wd src hNoGlue
            hValid)).labelling.row
          (NonTrivalentValencyThreeRowEquiv.bridgeRow src hNoGlue hValid)} := by
  classical
  rw [incidenceCount_bridgeRow_inl_eq_zero m wd src hNoGlue hValid w]
  symm
  rw [NonTrivalentValencyThreeTracks.vertexEquiv_inl m wd wallStar src hNoGlue hValid w,
    outFD_row_bridge m wd wallStar src hNoGlue hValid]
  have h := natCard_moved_of_ne m wd
    ((NonTrivalentValencyThreeTracks.branchEquivAnchorComplement m wd wallStar src).symm w).1
    wallStar hBase
    ((NonTrivalentValencyThreeTracks.branchEquivAnchorComplement m wd wallStar src).symm w).2.1
    ((NonTrivalentValencyThreeTracks.branchEquivAnchorComplement m wd wallStar src).symm w).2.2
    (NonTrivalentValencyThreeTracks.facetRow m wd)
  rw [show wd.fullDim.labelling.row (NonTrivalentValencyThreeTracks.facetRow m wd) = label m.base
    from Equiv.apply_symm_apply _ _] at h
  refine h.trans (incidenceCount_facetRow_eq_zero m wd wallStar _ ?_ ?_)
  · exact ((NonTrivalentValencyThreeTracks.branchEquivAnchorComplement m wd wallStar src).symm
      w).2.1
  · exact ((NonTrivalentValencyThreeTracks.branchEquivAnchorComplement m wd wallStar src).symm
      w).2.2

/-! ## 6.  At the anchor -/

theorem card_filter_pair {α : Type*} [DecidableEq α] (X Y : α) (hXY : X ≠ Y) (P : α → Prop)
    [DecidablePred P] :
    (({X, Y} : Finset α).filter P).card = (if P X then 1 else 0) + (if P Y then 1 else 0) := by
  classical
  rw [Finset.filter_insert, Finset.filter_singleton]
  by_cases hX : P X <;> by_cases hY : P Y <;> simp [hX, hY, hXY]

/-- The two doubled-direction survivors of the anchor, as surviving occurrences
of the wall datum. -/
def doubledWall
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk) :
    Bool → NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
  | false => ⟨(Prescribed.firstDoubled src).1,
      NonTrivalentValencyThreeTracks.firstDoubled_survives m wd src⟩
  | true => ⟨(Prescribed.secondDoubled src).1,
      NonTrivalentValencyThreeTracks.secondDoubled_survives m wd src⟩

theorem doubledLift_eq
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (side : Bool) :
    NonTrivalentValencyThreeTracks.doubledLift m wd src side =
      NonTrivalentValencyThreeTracks.liftEdge m wd (doubledWall m wd src side) := by
  cases side <;> rfl

theorem stablePath_doubledLift
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (side : Bool) :
    (NonTrivalentValencyThreeTracks.doubledLift m wd src side).stablePath =
      incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m)
        (doubledWall m wd src side).stablePath := by
  rw [doubledLift_eq m wd src side]
  exact NonTrivalentValencyThreeTracks.stablePath_liftEdge m wd _

/-- The retained doubled-direction survivor at `A_u`. -/
def doubledRetained
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid) (side : Bool) :
    NonDanglingEdge (Prescribed.validCandidate src hNoGlue hValid).datum :=
  ResolutionAwayFromWall.retainedEdge (Prescribed.validCandidate src hNoGlue hValid) hValid.1
    (doubledWall m wd src side)

theorem stablePath_doubledRetained
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid) (side : Bool) :
    (doubledRetained m wd src hNoGlue hValid side).stablePath =
      NonTrivalentValencyThreeDescent.retainedRow src hNoGlue hValid
        (doubledWall m wd src side).stablePath :=
  (NonTrivalentValencyThreeDescent.retainedRow_mk src hNoGlue hValid _).symm

/-- The bridge occurrence, as a surviving occurrence of the candidate. -/
def bridgeND
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid) :
    NonDanglingEdge (Prescribed.validCandidate src hNoGlue hValid).datum :=
  ⟨NonTrivalentValencyThreeRows.bridgeEdge src hNoGlue hValid
      (Prescribed.selectedRepresentative src),
    NonTrivalentValencyThreeRows.bridgeEdge_survives src hNoGlue hValid⟩

theorem stablePath_bridgeND
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid) :
    (bridgeND m wd src hNoGlue hValid).stablePath =
      NonTrivalentValencyThreeRowEquiv.bridgeRow src hNoGlue hValid := rfl

theorem doubledRetained_ne
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid) :
    doubledRetained m wd src hNoGlue hValid false ≠
      doubledRetained m wd src hNoGlue hValid true := by
  intro hBad
  exact NonTrivalentValencyThreeRows.firstDoubled_val_ne src
    (ResolutionCut.oldSourceEdge_injective (Prescribed.validCandidate src hNoGlue hValid)
      (congrArg Subtype.val hBad))

/-- **The exact star at `A_u` of `NonTrivalentValencyThreeRows`**, read on
surviving occurrences: the
bridge and the two retained doubled-direction survivors. -/
theorem incidentEdges_endpointVertex_false
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid) :
    incidentEdges (Prescribed.validCandidate src hNoGlue hValid).datum
        (NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid false
          (Prescribed.selectedRepresentative src)) =
      {bridgeND m wd src hNoGlue hValid, doubledRetained m wd src hNoGlue hValid false,
        doubledRetained m wd src hNoGlue hValid true} := by
  classical
  ext e
  rw [mem_incidentEdges]
  constructor
  · intro hInc
    have h : e.1 ∈ nonDanglingIncident (Prescribed.validCandidate src hNoGlue hValid).datum
        (NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid false
          (Prescribed.selectedRepresentative src)) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hInc⟩
    rw [NonTrivalentValencyThreeRows.nonDanglingIncident_endpointVertex_false src hNoGlue
      hValid] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  · intro h
    have h2 : e.1 ∈ nonDanglingIncident (Prescribed.validCandidate src hNoGlue hValid).datum
        (NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid false
          (Prescribed.selectedRepresentative src)) := by
      rw [NonTrivalentValencyThreeRows.nonDanglingIncident_endpointVertex_false src hNoGlue hValid]
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    exact ((mem_nonDanglingIncident _ _ _).mp h2).2

/-- The chart label of the dart of an occurrence **on the row of** a
doubled-direction survivor.  Only the row equality is needed -- this is
`IncomingPairing.label_dart_of_row` composed with
`stablePath_doubledLift` -- which is why (H-III) is stated at row level. -/
theorem label_dart_doubled
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (d : StableSourceDarts.Dart wd.cover) (side : Bool)
    (hd : d.2.1.stablePath =
      (NonTrivalentValencyThreeTracks.doubledLift m wd src side).stablePath) :
    label (wd.tracks.iso.dart d) = wd.fullDim.labelling.row
      (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m)
        (doubledWall m wd src side).stablePath) := by
  rw [wd.tracks.row_map d]
  refine congrArg wd.fullDim.labelling.row ?_
  show NonDanglingEdge.stablePath d.2.1 = _
  rw [hd]
  exact stablePath_doubledLift m wd src side

theorem label_dart_doubled_iff
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (d : StableSourceDarts.Dart wd.cover) (side : Bool)
    (hd : d.2.1.stablePath =
      (NonTrivalentValencyThreeTracks.doubledLift m wd src side).stablePath)
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (label (wd.tracks.iso.dart d) = wd.fullDim.labelling.row
        (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) r₀)) ↔
      (doubledWall m wd src side).stablePath = r₀ := by
  rw [label_dart_doubled m wd src d side hd]
  constructor
  · intro h
    exact injective_incomingRow m wd wallStar (wd.fullDim.labelling.row.injective h)
  · intro h
    exact congrArg _ (congrArg _ h)

theorem label_dart_doubled_ne_base
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (d : StableSourceDarts.Dart wd.cover) (side : Bool)
    (hd : d.2.1.stablePath =
      (NonTrivalentValencyThreeTracks.doubledLift m wd src side).stablePath) :
    label (wd.tracks.iso.dart d) ≠ label m.base := by
  rw [label_dart_doubled m wd src d side hd]
  exact labelling_row_incomingRow_ne_base m wd _

/-- **(H-III) names the moved star at `graph.vert m.base`**: the contracted
dart together with the darts of the two doubled-direction survivors. -/
theorem filter_moved_base (first second : StableSourceDarts.Dart wd.cover)
    (hStar : (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart first, wd.tracks.iso.dart second}) :
    (Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base) =
      {m.base, wd.tracks.iso.dart first, wd.tracks.iso.dart second} := by
  classical
  ext d
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    by_cases hb : d = m.base
    · exact Finset.mem_insert.mpr (Or.inl hb)
    · refine Finset.mem_insert_of_mem ?_
      rw [← hStar]
      exact Finset.mem_erase.mpr ⟨hb, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  · intro h
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp h with hb | hb
    · rw [hb]
      exact congrArg graph.vert m.perm_base
    · rw [← hStar] at hb
      exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase hb)).2

/-- The two darts (H-III) names are distinct: the moved star has three darts. -/
theorem dart_ne (first second : StableSourceDarts.Dart wd.cover)
    (hStar : (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart first, wd.tracks.iso.dart second}) :
    wd.tracks.iso.dart first ≠ wd.tracks.iso.dart second := by
  classical
  have hBaseMem : m.base ∈
      (Finset.univ.filter fun d : D ↦ (graph.move m).vert d = graph.vert m.base) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg graph.vert m.perm_base⟩
  have hPairCard : ({wd.tracks.iso.dart first, wd.tracks.iso.dart second} : Finset D).card = 2 := by
    rw [← hStar, Finset.card_erase_of_mem hBaseMem, (graph.move m).card_fibre (graph.vert m.base)]
  intro hBad
  rw [hBad] at hPairCard
  simp at hPairCard

/-- **The star count at `A_u`, on a retained row.**  The exact star
`{h_1, e_2, e_5}` is matched dart by dart with the star (H-III) prescribes:
`m.base` carries the vanishing chart row, and the two remaining darts carry the
incoming rows of the two doubled-direction survivors. -/
theorem incidence_inr_false_retained
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (hPres : NonTrivalentValencyThreeTracks.PrescribedDoubledMove m wd wallStar src)
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (Prescribed.validCandidate src hNoGlue hValid).datum
        (NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid (Sum.inr false)).1
        (NonTrivalentValencyThreeDescent.retainedRow src hNoGlue hValid r₀) =
      Nat.card {d : D // graph.vert (m.perm d) =
          NonTrivalentValencyThreeTracks.vertexEquiv m wd wallStar src hNoGlue hValid
            (NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid
              (Sum.inr false)) ∧
        label d = (NonTrivalentValencyThreeExit.wallOutgoingFD m wd src hNoGlue hValid
          (NonTrivalentValencyThreePathEnds.hasPathEnds_wallData m wd src hNoGlue
            hValid)).labelling.row
          (NonTrivalentValencyThreeDescent.retainedRow src hNoGlue hValid r₀)} := by
  classical
  obtain ⟨hBase, first, second, hFirst, hSecond, hStar⟩ := hPres
  rw [NonTrivalentValencyThreeTracks.vertexEquiv_anchor_false m wd wallStar src hNoGlue hValid
      hBase,
    outFD_row_retained m wd wallStar src hNoGlue hValid r₀]
  have hRHS : Nat.card {d : D // graph.vert (m.perm d) = graph.vert m.base ∧
      label d = wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) r₀)} =
      ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
        fun d ↦ label d = wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab
          wd.hOne (wd.hCompat m) (wd.hForest m) r₀)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
  have hBridgeRow : ¬ ((bridgeND m wd src hNoGlue hValid).stablePath =
      NonTrivalentValencyThreeDescent.retainedRow src hNoGlue hValid r₀) := by
    rw [stablePath_bridgeND m wd src hNoGlue hValid]
    exact fun h ↦ retainedRow_ne_bridgeRow src hNoGlue hValid r₀ h.symm
  rw [hRHS, filter_moved_base m wd first second hStar, Finset.filter_insert,
    ite_eq_right (Ne.symm (labelling_row_incomingRow_ne_base m wd r₀)),
    card_filter_pair _ _ (dart_ne m wd first second hStar)]
  show incidenceCount (Prescribed.validCandidate src hNoGlue hValid).datum
    (NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid false
      (Prescribed.selectedRepresentative src))
    (NonTrivalentValencyThreeDescent.retainedRow src hNoGlue hValid r₀) = _
  unfold incidenceCount
  rw [incidentEdges_endpointVertex_false m wd src hNoGlue hValid, Finset.filter_insert,
    ite_eq_right hBridgeRow,
    card_filter_pair _ _ (doubledRetained_ne m wd src hNoGlue hValid)]
  have hcond : ∀ side : Bool, ((doubledRetained m wd src hNoGlue hValid side).stablePath =
      NonTrivalentValencyThreeDescent.retainedRow src hNoGlue hValid r₀) ↔
      (doubledWall m wd src side).stablePath = r₀ := by
    intro side
    rw [stablePath_doubledRetained m wd src hNoGlue hValid side]
    exact ⟨fun h ↦ injective_retainedRow src hNoGlue hValid h, fun h ↦ congrArg _ h⟩
  rw [if_congr (hcond false) rfl rfl, if_congr (hcond true) rfl rfl,
    if_congr (label_dart_doubled_iff m wd wallStar src first false hFirst r₀) rfl rfl,
    if_congr (label_dart_doubled_iff m wd wallStar src second true hSecond r₀) rfl rfl]

/-- **The star count at `A_u`, on the bridge row.**  Both sides are one: the
bridge occurrence `h_1` downstairs, the contracted dart `m.base` upstairs. -/
theorem incidence_inr_false_bridge
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (hPres : NonTrivalentValencyThreeTracks.PrescribedDoubledMove m wd wallStar src) :
    incidenceCount (Prescribed.validCandidate src hNoGlue hValid).datum
        (NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid (Sum.inr false)).1
        (NonTrivalentValencyThreeRowEquiv.bridgeRow src hNoGlue hValid) =
      Nat.card {d : D // graph.vert (m.perm d) =
          NonTrivalentValencyThreeTracks.vertexEquiv m wd wallStar src hNoGlue hValid
            (NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid
              (Sum.inr false)) ∧
        label d = (NonTrivalentValencyThreeExit.wallOutgoingFD m wd src hNoGlue hValid
          (NonTrivalentValencyThreePathEnds.hasPathEnds_wallData m wd src hNoGlue
            hValid)).labelling.row
          (NonTrivalentValencyThreeRowEquiv.bridgeRow src hNoGlue hValid)} := by
  classical
  obtain ⟨hBase, first, second, hFirst, hSecond, hStar⟩ := hPres
  rw [NonTrivalentValencyThreeTracks.vertexEquiv_anchor_false m wd wallStar src hNoGlue hValid
      hBase,
    outFD_row_bridge m wd wallStar src hNoGlue hValid]
  have hRHS : Nat.card {d : D // graph.vert (m.perm d) = graph.vert m.base ∧
      label d = label m.base} =
      ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
        fun d ↦ label d = label m.base).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
  have hEmptyD : (({wd.tracks.iso.dart first, wd.tracks.iso.dart second} : Finset D).filter
      fun d ↦ label d = label m.base) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact label_dart_doubled_ne_base m wd wallStar src first false hFirst
    · exact label_dart_doubled_ne_base m wd wallStar src second true hSecond
  have hR : ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
      fun d ↦ label d = label m.base).card = 1 := by
    rw [filter_moved_base m wd first second hStar, Finset.filter_insert, ite_eq_left rfl, hEmptyD]
    simp
  rw [hRHS, hR]
  show incidenceCount (Prescribed.validCandidate src hNoGlue hValid).datum
    (NonTrivalentValencyThreeRows.endpointVertex src hNoGlue hValid false
      (Prescribed.selectedRepresentative src))
    (NonTrivalentValencyThreeRowEquiv.bridgeRow src hNoGlue hValid) = 1
  have hEmptyC : (({doubledRetained m wd src hNoGlue hValid false,
      doubledRetained m wd src hNoGlue hValid true} :
        Finset (NonDanglingEdge (Prescribed.validCandidate src hNoGlue hValid).datum)).filter
      fun e ↦ e.stablePath =
        NonTrivalentValencyThreeRowEquiv.bridgeRow src hNoGlue hValid) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · rw [stablePath_doubledRetained m wd src hNoGlue hValid false]
      exact retainedRow_ne_bridgeRow src hNoGlue hValid _
    · rw [stablePath_doubledRetained m wd src hNoGlue hValid true]
      exact retainedRow_ne_bridgeRow src hNoGlue hValid _
  unfold incidenceCount
  rw [incidentEdges_endpointVertex_false m wd src hNoGlue hValid, Finset.filter_insert,
    ite_eq_left (stablePath_bridgeND m wd src hNoGlue hValid), hEmptyC]
  simp

/-! ## 7.  The leftover equation at `A_v`, and the link -/

/-- Every stable row of a cover meets its branch vertices twice in all
(`StableSourceDarts.card_row`, read as a sum of incidence counts). -/
theorem sum_incidenceCount_branchVertex {tgt : CFGraph} {deg : ℕ}
    (dat : GluingDatum tgt deg) (hConnected : dat.Connected) (hEnds : HasPathEnds dat)
    (r : StablePath dat) :
    ∑ v : BranchVertex dat, incidenceCount dat v.1 r = 2 := by
  classical
  have hEquiv : {d : StableSourceDarts.Dart dat // StableSourceDarts.row dat d = r} ≃
      Σ v : BranchVertex dat,
        {e : NonDanglingEdge dat // Incident dat e.1 v.1 ∧ e.stablePath = r} :=
    { toFun := fun d ↦ ⟨d.1.1, ⟨d.1.2.1, d.1.2.2, d.2⟩⟩
      invFun := fun d ↦ ⟨⟨d.1, ⟨d.2.1, d.2.2.1⟩⟩, d.2.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have h := StableSourceDarts.card_row dat hConnected hEnds r
  rw [Fintype.card_congr hEquiv, Fintype.card_sigma] at h
  simp_rw [StableSourceDarts.card_incidence] at h
  exact h

include wd in
/-- The same count on the tracked graph: one chart row carries two darts, and
they sit at two vertices of the moved graph. -/
theorem sum_natCard_moved (c : coordinate) :
    ∑ x : V, Nat.card {d : D // graph.vert (m.perm d) = x ∧ label d = c} = 2 := by
  classical
  have h1 : ∀ x : V, Nat.card {d : D // graph.vert (m.perm d) = x ∧ label d = c} =
      ((Finset.univ.filter fun d : D ↦ label d = c).filter
        fun d ↦ graph.vert (m.perm d) = x).card := by
    intro x
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
    refine congrArg Finset.card ?_
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  simp_rw [h1]
  rw [← Finset.card_eq_sum_card_fiberwise
    (fun d (_ : d ∈ Finset.univ.filter fun d : D ↦ label d = c) ↦
      Finset.mem_univ (graph.vert (m.perm d)))]
  exact card_filter_label m wd c

/-- **The star count at every branch vertex except `A_v`.** -/
theorem incidence_of_ne_rightAnchor
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (hPres : NonTrivalentValencyThreeTracks.PrescribedDoubledMove m wd wallStar src)
    (v : BranchVertex (Prescribed.validCandidate src hNoGlue hValid).datum)
    (hv : v ≠ NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid (Sum.inr true))
    (r : StablePath (Prescribed.validCandidate src hNoGlue hValid).datum) :
    incidenceCount (Prescribed.validCandidate src hNoGlue hValid).datum v.1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          NonTrivalentValencyThreeTracks.vertexEquiv m wd wallStar src hNoGlue hValid v ∧
        label d = (NonTrivalentValencyThreeExit.wallOutgoingFD m wd src hNoGlue hValid
          (NonTrivalentValencyThreePathEnds.hasPathEnds_wallData m wd src hNoGlue
            hValid)).labelling.row r} := by
  classical
  obtain ⟨x, rfl⟩ : ∃ x, NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid x
      = v :=
    ⟨(NonTrivalentValencyThreeTracks.candBranchEquiv m wd src hNoGlue hValid).symm v,
      (NonTrivalentValencyThreeTracks.candBranchEquiv m wd src hNoGlue hValid).apply_symm_apply v⟩
  obtain ⟨r', rfl⟩ : ∃ r', NonTrivalentValencyThreeRowEquiv.rowMap src hNoGlue hValid r' = r :=
    ⟨NonTrivalentValencyThreeRowEquiv.rowEquiv src hNoGlue hValid r,
      (NonTrivalentValencyThreeRowEquiv.rowEquiv src hNoGlue hValid).left_inv r⟩
  cases x with
  | inl w =>
    cases r' with
    | none => exact incidence_inl_bridge m wd wallStar src hNoGlue hValid hPres.1 w
    | some r₀ => exact incidence_inl_retained m wd wallStar src hNoGlue hValid hPres.1 w r₀
  | inr side =>
    cases side with
    | true => exact absurd rfl hv
    | false =>
      cases r' with
      | none => exact incidence_inr_false_bridge m wd wallStar src hNoGlue hValid hPres
      | some r₀ => exact incidence_inr_false_retained m wd wallStar src hNoGlue hValid hPres r₀

/-- **The star count at `A_v`, from the leftover equation.**  A stable row of
the candidate meets its branch vertices twice in all, a chart row carries two
darts of the moved graph, `vertexEquiv` is a bijection, and the count agrees at
every other branch vertex; so it agrees at `A_v` too. -/
theorem incidence_inr_true
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (hPres : NonTrivalentValencyThreeTracks.PrescribedDoubledMove m wd wallStar src)
    (r : StablePath (Prescribed.validCandidate src hNoGlue hValid).datum) :
    incidenceCount (Prescribed.validCandidate src hNoGlue hValid).datum
        (NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid (Sum.inr true)).1
        r =
      Nat.card {d : D // graph.vert (m.perm d) =
          NonTrivalentValencyThreeTracks.vertexEquiv m wd wallStar src hNoGlue hValid
            (NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid
              (Sum.inr true)) ∧
        label d = (NonTrivalentValencyThreeExit.wallOutgoingFD m wd src hNoGlue hValid
          (NonTrivalentValencyThreePathEnds.hasPathEnds_wallData m wd src hNoGlue
            hValid)).labelling.row r} := by
  classical
  set outFD := NonTrivalentValencyThreeExit.wallOutgoingFD m wd src hNoGlue hValid
    (NonTrivalentValencyThreePathEnds.hasPathEnds_wallData m wd src hNoGlue hValid) with houtFD
  set v₀ := NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid (Sum.inr true)
    with hv₀
  set f : BranchVertex (Prescribed.validCandidate src hNoGlue hValid).datum → ℕ :=
    fun v ↦ incidenceCount (Prescribed.validCandidate src hNoGlue hValid).datum v.1 r with hf
  set g : BranchVertex (Prescribed.validCandidate src hNoGlue hValid).datum → ℕ :=
    fun v ↦ Nat.card {d : D // graph.vert (m.perm d) =
        NonTrivalentValencyThreeTracks.vertexEquiv m wd wallStar src hNoGlue hValid v ∧
      label d = outFD.labelling.row r} with hg
  have hSumF : ∑ v, f v = 2 :=
    sum_incidenceCount_branchVertex (Prescribed.validCandidate src hNoGlue hValid).datum
      outFD.connected outFD.pathEnds r
  have hSumG : ∑ v, g v = 2 := by
    rw [Fintype.sum_equiv
      (NonTrivalentValencyThreeTracks.vertexEquiv m wd wallStar src hNoGlue hValid) g
      (fun x : V ↦ Nat.card {d : D // graph.vert (m.perm d) = x ∧
        label d = outFD.labelling.row r}) (fun v ↦ rfl)]
    exact sum_natCard_moved m wd (outFD.labelling.row r)
  have hAway : ∀ v ∈ Finset.univ.erase v₀, f v = g v := by
    intro v hv
    exact incidence_of_ne_rightAnchor m wd wallStar src hNoGlue hValid hPres v
      (Finset.mem_erase.mp hv).1 r
  have hfsum := Finset.add_sum_erase Finset.univ f (Finset.mem_univ v₀)
  have hgsum := Finset.add_sum_erase Finset.univ g (Finset.mem_univ v₀)
  have hEq : ∑ x ∈ Finset.univ.erase v₀, f x = ∑ x ∈ Finset.univ.erase v₀, g x :=
    Finset.sum_congr rfl hAway
  show f v₀ = g v₀
  omega

/-- **The star count, at every branch vertex and every row.**  This is the one
geometric input `NonTrivalentValencyThreeTracks.typeChangeLink_of_incidence`
needs, under (H-III). -/
theorem incidence_of_prescribedDoubledMove
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (hPres : NonTrivalentValencyThreeTracks.PrescribedDoubledMove m wd wallStar src)
    (v : BranchVertex (Prescribed.validCandidate src hNoGlue hValid).datum)
    (r : StablePath (Prescribed.validCandidate src hNoGlue hValid).datum) :
    incidenceCount (Prescribed.validCandidate src hNoGlue hValid).datum v.1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          NonTrivalentValencyThreeTracks.vertexEquiv m wd wallStar src hNoGlue hValid v ∧
        label d = (NonTrivalentValencyThreeExit.wallOutgoingFD m wd src hNoGlue hValid
          (NonTrivalentValencyThreePathEnds.hasPathEnds_wallData m wd src hNoGlue
            hValid)).labelling.row r} := by
  classical
  by_cases hv : v =
      NonTrivalentValencyThreeTracks.candBranchMap m wd src hNoGlue hValid (Sum.inr true)
  · subst hv
    exact incidence_inr_true m wd wallStar src hNoGlue hValid hPres r
  · exact incidence_of_ne_rightAnchor m wd wallStar src hNoGlue hValid hPres v hv r

/-- **`OuterWalk.TypeChangeLink` at a three-valent wall under (H-III).**
`NonTrivalentValencyThreeTracks.typeChangeLink_of_incidence` reduces the link to
the star count; this discharges it. -/
def typeChangeLink_of_prescribedDoubledMove
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
    (hPres : NonTrivalentValencyThreeTracks.PrescribedDoubledMove m wd wallStar src) :
    TypeChangeLink m wd :=
  NonTrivalentValencyThreeTracks.typeChangeLink_of_incidence m wd src hNoGlue hValid
    (incidence_of_prescribedDoubledMove m wd wallStar src hNoGlue hValid hPres)

end Wall

end

end DraismaVargas.LocalCases.NonTrivalentValencyThreeStarCount
