module

public import DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneTracks
public import DraismaVargas.LocalCases.NonTrivalentValencyTwoStarCountAll

@[expose] public section

/-!
# The valency-two **Base I** star count, and the Base I link at an actual wall

Source: Vargas, Part II, arXiv:2609.09109, Section 5.1 (a combinatorial type change is a Whitehead
move on the *ambient* tracked graph; the labelling convention (1)) and
Section 5.4 (case `{v2-nd4-t3}`, Configuration A, base tree `T_∅` = Base I, the
numerical condition `|e_α| = |e_β|`, `|e_γ| = |e_δ|`, and the observation that
there is no Base I morphism at all when it fails), together with
Draisma–Vargas Part I, arXiv:1909.12924, case `{w2-r2}`, Base I (the fibre above the new leaf:
one fold `F` with `|F| = 2` and two unramified vertices `A₁`, `A₂` above the new
trivalent point) and the non-dangling valency formula `lemma-ndval-of-GqA0`.

`NonTrivalentValencyTwoBaseOneTracks` reduces `OuterWalk.TypeChangeLink` at a
valency-two Base I wall to a **single star count**, `hIncidence`, against the
branch-vertex bijection `vertexEquiv` and the outgoing presentation
`NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD`; it provides the vertex
dictionary, the row-level (H-BaseI) `PrescribedBaseOneMove`, the off-wall half
of (T1) and the gauge leg of (T2).  **This module discharges that star count**,
so the Base I link follows from (H-BaseI), the wall data and the incoming
two-valent star alone.  It is the Base I analogue of the Base II count
(`NonTrivalentValencyTwoStarCount`, `NonTrivalentValencyTwoStarCountAll`) and of
`NonTrivalentValencyFourStarCount`; everywhere `NonTrivalentValencyTwoStarCount`
carries `StablePathFacetContraction.NoContractedReturn`, the input is taken from
the no-return-free `NonTrivalentValencyTwoStarCountAll.injective_incomingRow`
instead.

## What is proved

### 1.  (T1) at an ordinary wall block, and at every non-anchor vertex

* `incidenceCount_branchVertex_ordinary`: at a wall block other than the anchor
  the Base I candidate splits nothing --
  `NonTrivalentValencyTwoBaseOneRows.nonDanglingIncident_branchVertex_ordinary`
  says the block keeps exactly its old star -- so the row-filtered star is
  transported by the retained-edge map, read through the retained-row map.
* `incidenceCount_candVertex`: (T1) at every vertex of the datum other than the
  anchor, the ordinary-block case above together with the off-wall
  `NonTrivalentValencyTwoBaseOneTracks.incidenceCount_retainedVertex_retainedRow`.

### 2.  (T2) at an ordinary wall block

`incidenceCount_gauged_eq_incoming`: the gauge leg
`NonTrivalentValencyTwoBaseOneTracks.incidenceCount_gauge` composed with
`NonTrivalentValencyTwoStarCountAll.incidenceCount_wall_eq_incoming`, whose
ordinary-block half is the valency-agnostic
`WallSplitIncidenceOrdinary.incidenceCount_unramified`, with
`NonTrivalentValencyTwoStarCount.internalEdges_subsingleton_of_ne_anchor`
supplying the "at most one internal occurrence" hypothesis at every non-anchor
wall block of a two-valent wall.

### 3.  The exact star at `A₁`, `A₂`, and the cross pair across the gauge

* `crossND`, `crossRetained`, `bridgeND`, `incidentEdges_anchorBranchVertex`:
  `NonTrivalentValencyTwoBaseOneTracks.nonDanglingIncident_anchorBranchVertex`
  read as a three-element `Finset` of *surviving occurrences*
  `{h₁, thick, thin}`, with `crossRetained_ne` (the two cross-paired survivors
  lie over the two different edges of the incoming two-valent star, hence are
  distinct occurrences).
* `gaugeRowEquiv_crossWall`, `outFD_row_retained`, `outFD_row_bridge`,
  `outFD_row_cross`: the chart rows of the outgoing presentation -- a retained
  row keeps the chart coordinate of its own incoming row, the bridge row occupies
  the vanishing chart row `label m.base`, and a cross-paired survivor's row is
  the chart row of its lift `crossLift` to the incoming cover.
* `stablePath_crossRetained_iff`, `label_dart_cross_iff`,
  `label_dart_cross_ne_base`: the two matching tests, candidate side and dart
  side.  Row injectivity is `injective_retainedRow`, the gauge equivalence and
  `NonTrivalentValencyTwoStarCountAll.injective_incomingRow` -- **no no-return
  hypothesis of any kind**.

### 4.  The star count

* `incidence_inl_retained`, `incidence_inl_bridge`: away from the anchor,
  (T1)-then-(T2)-then the incoming tracking
  (`card_star_move_eq_incidenceCount`); on the bridge row both sides vanish, by
  `incidenceCount_bridgeRow_inl_eq_zero` (downstairs `h₁` runs `A₁ → F → A₂`
  through the divalent fold) and `incidenceCount_facetRow_eq_zero` (upstairs the
  vanishing row meets only the two anchor ends).
* `vanishingEnds_of_orientation`, `incidenceCount_facetRow_eq_zero`:
  `NonTrivalentValencyTwoStarCountAll.VanishingEnds` built from
  `NonTrivalentValencyTwoTracksLeaf.AnchorEnds` together with (H-BaseI)'s
  orientation clause, which is what says each end meets the vanishing row.
* `incidence_inr_false_retained`, `incidence_inr_false_bridge`: **at `A₁`.**  The
  exact star `{h₁, thick, thin}` is matched occurrence by dart with the moved
  star `{m.base, first, second}` that (H-BaseI) prescribes: `m.base` carries the
  vanishing chart row, the two remaining darts carry the chart rows of the two
  cross-paired survivors.
* `incidence_inr_true`: **at `A₂`, from the leftover equation** -- a stable row
  meets its branch vertices twice in all, a chart row carries two darts of the
  moved graph, `vertexEquiv` is a bijection, and the count agrees everywhere
  else.
* `incidence_of_ne_rightAnchor`, `incidence_of_prescribedBaseOneMove`: the star
  count at every branch vertex and every row.

### 5.  The link and the headline

* `typeChangeLink_of_prescribedBaseOneMove`: `OuterWalk.TypeChangeLink` at a
  valency-two Base I wall from (H-BaseI), through
  `NonTrivalentValencyTwoBaseOneTracks.typeChangeLink_of_incidence`.
* `typeChangeLink_of_rows`: the same from the row condition the move-to-type
  dispatcher discharges, through
  `NonTrivalentValencyTwoBaseOneTracks.prescribedBaseOneMove_of_rows`.
* `exists_typeChangeLink_of_prescribedBaseOneMove_of_wallData`: **the headline**,
  in the shape of
  `NonTrivalentValencyTwoStarCountAll.exists_typeChangeLink_of_prescribedMergedMove_of_wallData`
  and `NonTrivalentValencyTwoBaseOneExit.exists_typeChangeLink_baseOne_of_wallData`.
  From `wd` and the incoming `W2R1Target.TwoStar` alone it produces the anchor
  block and `nd(A) = 4`, the two anchor ends `p`, `q` of the vanishing row (the
  incoming `2 + 2` / `1 + 3` / `3 + 1` trichotomy is discharged internally by
  `NonTrivalentValencyTwoTracksLeaf.exists_anchorEnds`), the ordinary-block
  trivalence `hOrd`, the wall labelling `labelling₀` / `hRowVal` / `hMatrixWall`
  of `NonTrivalentValencyTwoExitFree`, and then -- for every Configuration A
  split and prescribed cross pairing satisfying the two index equalities -- the
  gauged Base I setup `gauged` of `NonTrivalentValencyTwoGauge` with its
  validity, the outgoing `FullDimensionalSourcePresentation` on the incoming
  chart, the common minor `AgreeOffColumn` that `OuterWalk.TypeChangeLink.agree`
  asks for, and the link itself as soon as (H-BaseI) is supplied.

## The hypotheses that remain explicit

1. `PrescribedBaseOneMove m wd thickSheet thinSheet setup p q`, i.e. (H-BaseI):
   the Whitehead move `m` is oriented along the vanishing row (its `A₁` end at
   `graph.vert m.base`) and places with `m.base` exactly two darts carrying the
   stable **rows** of the two survivors the prescribed cross pairing brings
   together at `A₁`.  Its relative witness is
   `NonTrivalentValencyTwoBaseOneTracks.prescribedBaseOneMove_prescribedMove`
   (geometric input: `BaseOneSeparated`, a named hypothesis there and **not**
   derived here), its orientation clause holds in all three incoming sub-cases
   by `orientation_of_hBase_two` / `orientation_of_hBase_leaf` of the same
   module, and `typeChangeLink_of_rows` is the row-only form the dispatcher
   discharges.
2. `wallStar : W2R1Target.TwoStar (contract wd.coverTarget …) ⟨wd.a, …⟩`, the
   incoming two-valent star at the contracted wall.  The valency dispatcher of
   `OuterWalk.WallData.valency` -- which decides valency 4 / 3 / 2 and, at
   valency two, Base I versus Base II -- is not built here.
3. The Configuration A dispatch data of the headline: the `2 + 2` split
   `hSplit`, the four named survivors with their two distinctness facts, and the
   **two index equalities** `|e_α| = |e_β|`, `|e_γ| = |e_δ|` (Part II,
   Section 5.4).  These stay the caller's, exactly as in
   `NonTrivalentValencyTwoBaseOneExit`: with them false there is no Base I
   morphism at all (Part II, Section 5.4, subcase `{v2-nd4-t3-k2<k3}` and
   Configuration B).
4. Nothing else.  Of the binders of
   `NonTrivalentValencyTwoBaseOneExit.exists_typeChangeLink_baseOne_of_wallData`
   the headline produces `anchorBlk`, `thickSheet`, `thinSheet`, `setup`,
   `hGauged`, `hOrd`, `labelling₀`, `hRowVal`, `hMatrixWall` internally; only
   `wallStar` and the dispatch data of item 3 remain.  No no-return hypothesis
   appears in any statement of this module.
5. No structure is introduced.  The one structure inhabited here is
   `NonTrivalentValencyTwoStarCountAll.VanishingEnds`, by
   `vanishingEnds_of_orientation` at a Base I wall.

## Consumers

`OuterWalk.TypeChangeLink` at Part II case `{v2-nd4}`, Configuration A, the two
Base I outgoing types -- hence the `link` hypothesis of
`OuterWalk.coneEntry_of_reaches` -- once the valency dispatcher supplies
`wallStar` and the walk supplies (H-BaseI).  Both are supplied:
`NonTrivalentValencyTwoDispatcher` produces `wallStar`, and
`NonTrivalentValencyTwoBaseOneLink.baseOneCrossLink` discharges (H-BaseI)
unconditionally, so this file's headline feeds `link_all` with no hypothesis.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneStarCount

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoGauge
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOne
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRows
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRowEquiv
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRowDictionary (gaugeRowEquiv
  relabelLabelling relabelLabelling_row chartLabelling)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneTracks
open DraismaVargas.LocalCases.NonTrivalentValencyTwoTracksLeaf (AnchorEnds leftBranch rightBranch
  branchEquivAnchorComplement branchEquivAnchorComplement_apply)

noncomputable section

section Ordinary

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (setup : BaseOneSetup data star anchor)

local notation "cand" => (validCandidate setup)

/-- (T1) at an ordinary wall block. -/
theorem incidenceCount_branchVertex_ordinary (hValid : data.Valid) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (row : StablePath data) :
    incidenceCount data (data.sourceEndpoint wall x) row =
      incidenceCount (cand).datum (branchVertex setup x)
        (retainedRow setup hValid row) := by
  classical
  unfold incidenceCount
  apply Finset.card_bij (fun edge _ ↦ ResolutionAwayFromWall.retainedEdge (cand) hValid.1 edge)
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge ⊢
    refine ⟨(incident_oldSourceEdge_branchVertex_ordinary setup hX edge.1).mpr hEdge.1, ?_⟩
    rw [← retainedRow_mk setup hValid edge, hEdge.2]
  · intro first _ second _ hEq
    exact ResolutionAwayFromWall.retainedEdge_injective (cand) hValid.1 hEq
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge
    have hMem : edge.1 ∈ nonDanglingIncident (cand).datum (branchVertex setup x) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hEdge.1⟩
    rw [nonDanglingIncident_branchVertex_ordinary setup hValid hX] at hMem
    obtain ⟨old, hOld, hEqual⟩ := Finset.mem_image.mp hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOld
    refine ⟨⟨old, hSurvives⟩, ?_, Subtype.ext hEqual⟩
    refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hIncident,
      injective_retainedRow setup hValid ?_⟩
    rw [retainedRow_mk setup hValid (⟨old, hSurvives⟩ : NonDanglingEdge data),
      show ResolutionAwayFromWall.retainedEdge (cand) hValid.1 ⟨old, hSurvives⟩ = edge from
        Subtype.ext hEqual]
    exact hEdge.2

/-- (T1) at every vertex of the datum other than the anchor. -/
theorem incidenceCount_candVertex (hValid : data.Valid) (w : data.SourceVertex)
    (hne : w ≠ WallBlock.sourceVertex data wall anchor) (row : StablePath data) :
    incidenceCount data w row =
      incidenceCount (cand).datum (candVertex setup w) (retainedRow setup hValid row) := by
  classical
  by_cases hw : w.1.1 = wall
  · rw [candVertex_wall setup w hw]
    conv_lhs => rw [← sourceEndpoint_self w hw]
    exact incidenceCount_branchVertex_ordinary setup hValid (not_rel_anchor_of_ne w hw hne) row
  · rw [candVertex_away setup w hw]
    exact incidenceCount_retainedVertex_retainedRow setup hValid w hw row


/-! ### The exact star at `A₁` / `A₂`, as surviving occurrences -/

/-- One member of the prescribed cross pair, as a surviving occurrence of the
datum the candidate is built over. -/
def crossND (side dir : Bool) : NonDanglingEdge data :=
  ⟨(crossSurvivor setup side dir).1, crossSurvivor_not_isDangling setup side dir⟩

/-- The same occurrence, retained by the Base I candidate. -/
def crossRetained (hValid : data.Valid) (side dir : Bool) : NonDanglingEdge (cand).datum :=
  ResolutionAwayFromWall.retainedEdge (cand) hValid.1 (crossND setup side dir)

theorem stablePath_crossRetained (hValid : data.Valid) (side dir : Bool) :
    (crossRetained setup hValid side dir).stablePath =
      NonTrivalentValencyTwoBaseOneRowEquiv.retainedRow setup hValid
        (crossND setup side dir).stablePath :=
  (NonTrivalentValencyTwoBaseOneRowEquiv.retainedRow_mk setup hValid _).symm

/-- **The two members of a cross pair are distinct occurrences**: they lie over
the two different edges of the incoming two-valent star. -/
theorem crossRetained_ne (hValid : data.Valid) (side : Bool) :
    crossRetained setup hValid side false ≠ crossRetained setup hValid side true := by
  intro hBad
  have hVal : (crossThick setup side).1 = (crossThin setup side).1 :=
    ResolutionCut.oldSourceEdge_injective (cand) (congrArg Subtype.val hBad)
  have h0 : (crossThick setup side).1.1.1 = star.edge 0 :=
    ((mem_directionSurvivors data star anchor 0 _).mp (crossThick_mem setup side)).2
  have h1 : (crossThin setup side).1.1.1 = star.edge 1 :=
    ((mem_directionSurvivors data star anchor 1 _).mp (crossThin_mem setup side)).2
  have hEdge : star.edge 0 = star.edge 1 := by
    rw [← h0, ← h1, hVal]
  exact absurd (star.edge_injective hEdge) (by decide)

/-- The bridge occurrence of the fold sheet at `A₁` (side `false`) and at `A₂`
(side `true`), as a surviving occurrence of the candidate. -/
def bridgeND (hValid : data.Valid) : Bool → NonDanglingEdge (cand).datum
  | false => ⟨(cand).newSourceEdge setup.foldFirst,
      newSourceEdge_foldFirst_survives setup hValid⟩
  | true => ⟨(cand).newSourceEdge setup.foldSecond,
      newSourceEdge_foldSecond_survives setup hValid⟩

theorem bridgeND_val (hValid : data.Valid) (side : Bool) :
    (bridgeND setup hValid side).1 = (cand).newSourceEdge (anchorBranchSheet setup side) := by
  cases side <;> rfl

theorem stablePath_bridgeND (hValid : data.Valid) (side : Bool) :
    (bridgeND setup hValid side).stablePath =
      NonTrivalentValencyTwoBaseOneRowEquiv.bridgeRow setup hValid := by
  cases side with
  | false => rfl
  | true => exact NonTrivalentValencyTwoBaseOneRowEquiv.bridgeRow_foldSecond setup hValid

/-- **The exact star at `A₁` / `A₂`, read on surviving occurrences**
(`NonTrivalentValencyTwoBaseOneTracks.nonDanglingIncident_anchorBranchVertex`):
the bridge occurrence of the fold sheet together with the two members of the
cross pair. -/
theorem incidentEdges_anchorBranchVertex (hValid : data.Valid) (side : Bool) :
    incidentEdges (cand).datum (branchVertex setup (anchorBranchSheet setup side)) =
      {bridgeND setup hValid side, crossRetained setup hValid side false,
        crossRetained setup hValid side true} := by
  classical
  ext e
  rw [mem_incidentEdges]
  constructor
  · intro hInc
    have h : e.1 ∈ nonDanglingIncident (cand).datum
        (branchVertex setup (anchorBranchSheet setup side)) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hInc⟩
    rw [nonDanglingIncident_anchorBranchVertex setup hValid side] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h | h
    · exact Or.inl (Subtype.ext (h.trans (bridgeND_val setup hValid side).symm))
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  · intro h
    have h2 : e.1 ∈ nonDanglingIncident (cand).datum
        (branchVertex setup (anchorBranchSheet setup side)) := by
      rw [nonDanglingIncident_anchorBranchVertex setup hValid side]
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl
      · rw [bridgeND_val setup hValid side]
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    exact ((mem_nonDanglingIncident _ _ _).mp h2).2

/-! ### The bridge row misses every branch vertex away from the anchor -/

/-- A branch vertex of the candidate away from the anchor is neither `A₁` nor
`A₂`. -/
theorem anchorBranchVertex_ne_candBranchMap_inl (hValid : data.Valid) (side : Bool)
    (w : {w : BranchVertex data // w.1 ≠ WallBlock.sourceVertex data wall anchor}) :
    branchVertex setup (anchorBranchSheet setup side) ≠
      (candBranchMap setup hValid (Sum.inl w)).1 := by
  intro hBad
  exact Sum.inr_ne_inl (candBranchMap_injective setup hValid
    (Subtype.ext hBad : candBranchMap setup hValid (Sum.inr side) =
      candBranchMap setup hValid (Sum.inl w)))

/-- **The bridge row `h₁` does not reach a branch vertex of the candidate away
from the anchor**: its two occurrences run `A₁ → F → A₂` through the divalent
fold. -/
theorem incidenceCount_bridgeRow_inl_eq_zero (hValid : data.Valid)
    (w : {w : BranchVertex data // w.1 ≠ WallBlock.sourceVertex data wall anchor}) :
    incidenceCount (cand).datum (candBranchMap setup hValid (Sum.inl w)).1
      (NonTrivalentValencyTwoBaseOneRowEquiv.bridgeRow setup hValid) = 0 := by
  classical
  unfold incidenceCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hRow
  have hInc := (mem_incidentEdges _ _ _).mp he
  have hKey : ∀ sheet : Fin degree, ∀ side : Bool,
      anchorBranchSheet setup side = sheet →
      leafVertex setup sheet = leafVertex setup setup.foldFirst →
      e.1 = (cand).newSourceEdge sheet → False := by
    intro sheet side hSide hLeaf hVal
    have hEnds : (cand).datum.sourceEnds e.1 =
        (leafVertex setup sheet, branchVertex setup sheet) := by
      rw [hVal]
      exact sourceEnds_bridgeEdge setup sheet
    rcases hInc with h | h
    · rw [hEnds] at h
      have hNd := (candBranchMap setup hValid (Sum.inl w)).2
      rw [← h, hLeaf, nonDanglingValency_leafVertex_fold setup hValid] at hNd
      omega
    · rw [hEnds] at h
      exact anchorBranchVertex_ne_candBranchMap_inl setup hValid side w (by rw [hSide]; exact h)
  rcases NonTrivalentValencyTwoBaseOneRowEquiv.bridgeRow_isolated setup hValid e hRow with h | h
  · exact hKey setup.foldFirst false rfl rfl h
  · exact hKey setup.foldSecond true rfl (leafVertex_fold_eq setup) h

end Ordinary


section Wall

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {deg : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival deg graph label (label m.base)}
  (wd : WallData arrival)
  {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (thickSheet thinSheet : Fin deg)

variable (setup : BaseOneSetup
    (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet) wallStar
    (gaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet))
  (hGauged : (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
    thickSheet thinSheet).Valid)
  (hOrd : NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)

include src hOrd in
/-- (T2): the gauge leg composed with the wall contraction. -/
theorem incidenceCount_gauged_eq_incoming
    (w₀ : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hne : w₀ ≠ NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk)
    (u : wd.cover.SourceVertex)
    (hMapU : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne u = w₀)
    (hThreeU : 3 ≤ nonDanglingValency wd.cover u)
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk thickSheet thinSheet)
        (NonTrivalentValencyTwoBaseOneExit.gaugeVertexEquiv
          (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet
          thinSheet w₀)
        (gaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀) =
      incidenceCount wd.cover u (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) r₀) := by
  rw [← incidenceCount_gauge (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
    thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 w₀ r₀]
  exact NonTrivalentValencyTwoStarCountAll.incidenceCount_wall_eq_incoming m wd src hOrd w₀ hne
    u hMapU hThreeU r₀

variable (labelling₀ : StableLengthMatrixLabelling
    (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    {column : coordinate // column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted})
  (hRowVal : ∀ pth : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
    (labelling₀.row pth).1 =
      Equiv.swap (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted)
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) pth)))
  (hMatrixWall : ∀ (pth : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (column : {column : coordinate //
      column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted}),
    GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row pth) column =
      GluingDatum.LengthMatrixPresentation.matrix wd.fullDim.labelling.presentation
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) pth)) column.1)

/-- A retained row of the outgoing Base I presentation keeps the chart coordinate
of its own incoming row. -/
theorem outFD_row_retained
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD m wd wallStar anchorBlk thickSheet
        thinSheet labelling₀ setup hGauged hOrd hRowVal hMatrixWall).labelling.row
      (retainedRow setup hGauged
        (gaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀)) =
      wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) r₀) := by
  show (NonTrivalentValencyTwoExit.rowChart wd.cover wd.fullDim (label m.base)
      (contracted := wd.contracted))
      ((NonTrivalentValencyTwoBaseOneRowEquiv.labelling setup hGauged
        (relabelLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1
          labelling₀)).row
        (retainedRow setup hGauged
          (gaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
            thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀))) = _
  have hRelab : (relabelLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
      anchorBlk thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1
      labelling₀).row
        (gaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀) =
      labelling₀.row r₀ :=
    relabelLabelling_row (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 labelling₀ r₀
  rw [NonTrivalentValencyTwoBaseOneRowEquiv.labelling_row_retained setup hGauged _ _,
    NonTrivalentValencyTwoExit.rowChart_some, hRelab, hRowVal r₀,
    Equiv.swap_comm (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted)]
  exact Equiv.swap_apply_self _ _ _

/-- The bridge row of the outgoing Base I presentation occupies the vanishing
chart row. -/
theorem outFD_row_bridge :
    (NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD m wd wallStar anchorBlk thickSheet
        thinSheet labelling₀ setup hGauged hOrd hRowVal hMatrixWall).labelling.row
      (bridgeRow setup hGauged) = label m.base := by
  show (NonTrivalentValencyTwoExit.rowChart wd.cover wd.fullDim (label m.base)
      (contracted := wd.contracted))
      ((NonTrivalentValencyTwoBaseOneRowEquiv.labelling setup hGauged
        (relabelLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1
          labelling₀)).row (bridgeRow setup hGauged)) = label m.base
  rw [NonTrivalentValencyTwoBaseOneRowEquiv.labelling_row_bridge setup hGauged _]
  rfl

/-! ### The pair of vanishing ends, from (H-BaseI)'s orientation -/

variable {p q : wd.cover.SourceVertex}

/-- `NonTrivalentValencyTwoStarCountAll.VanishingEnds` from
`NonTrivalentValencyTwoTracksLeaf.AnchorEnds` together with
(H-BaseI)'s orientation clause: the two named darts of the vanishing row sit one
at each end, so each end meets the vanishing row. -/
def vanishingEnds_of_orientation (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q) :
    NonTrivalentValencyTwoStarCountAll.VanishingEnds m wd anchorBlk where
  left := p
  right := q
  ends := hEnds
  leftMeets := by
    refine (incidenceCount_pos_iff wd.cover _ _).mpr
      ⟨(IncomingPairing.baseDart m wd).2.1, ?_, stablePath_baseDart m wd⟩
    rw [← hLeft]
    exact (IncomingPairing.baseDart m wd).2.2
  rightMeets := by
    refine (incidenceCount_pos_iff wd.cover _ _).mpr
      ⟨(IncomingPairing.opBaseDart m wd).2.1, ?_, stablePath_opBaseDart m wd⟩
    rw [← hRight]
    exact (IncomingPairing.opBaseDart m wd).2.2

@[simp] theorem vanishingEnds_left (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q) :
    (vanishingEnds_of_orientation m wd hEnds hLeft hRight).left = p := rfl

@[simp] theorem vanishingEnds_right (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q) :
    (vanishingEnds_of_orientation m wd hEnds hLeft hRight).right = q := rfl

/-- **The vanishing row meets no branch vertex of the incoming cover other than
the two anchor ends.**  The counting argument of
`NonTrivalentValencyTwoStarCountAll`, read at the pair
(H-BaseI)'s orientation names. -/
theorem incidenceCount_facetRow_eq_zero (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q)
    (u : BranchVertex wd.cover) (hl : u.1 ≠ p) (hr : u.1 ≠ q) :
    incidenceCount wd.cover u.1 (NonTrivalentValencyTwoTracks.facetRow m wd) = 0 :=
  NonTrivalentValencyTwoStarCountAll.incidenceCount_facetRow_eq_zero m wd
    (vanishingEnds_of_orientation m wd hEnds hLeft hRight) u hl hr


/-! ### The cross pair across the gauge, and its chart row -/

/-- **The gauge carries the row of a cross-paired survivor to its own row.**
`gaugeRowEquiv` follows the literal source-edge map of the relabelling of
`NonTrivalentValencyTwoGauge`, and
`crossWallEdge` is the same occurrence read back along that map. -/
theorem gaugeRowEquiv_crossWall (side dir : Bool) :
    gaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet
        thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1
        (crossWallEdge m wd thickSheet thinSheet setup side dir).stablePath =
      (crossND setup side dir).stablePath := by
  show SheetRelabelStable.stablePathEquiv
      (NonTrivalentValencyTwoGauge.relabeling
        (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet)
      (NonTrivalentValencyTwoTracks.wallValid m wd).1
      (crossWallEdge m wd thickSheet thinSheet setup side dir).stablePath = _
  rw [SheetRelabelStable.stablePathEquiv_mk]
  refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
  show (NonTrivalentValencyTwoGauge.relabeling
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet
      thinSheet).sourceEdgeEquiv
      (ungaugeSurvivor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        thickSheet thinSheet (crossSurvivor setup side dir)).1 =
    (crossSurvivor setup side dir).1
  exact congrArg (fun z : IncidentSourceEdge
      (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet
        thinSheet)
      (WallBlock.sourceVertex
        (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet
          thinSheet) ⟨wd.a, wd.hab⟩
        (gaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet)) ↦ z.1)
    (Equiv.apply_symm_apply
      (NonTrivalentValencyTwoGauge.survivorEquiv
        (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet)
      (crossSurvivor setup side dir))

/-- **The chart row of a cross-paired survivor** is the chart row of its lift to
the incoming cover. -/
theorem outFD_row_cross (side dir : Bool) :
    (NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD m wd wallStar anchorBlk thickSheet
        thinSheet labelling₀ setup hGauged hOrd hRowVal hMatrixWall).labelling.row
      (retainedRow setup hGauged (crossND setup side dir).stablePath) =
      wd.fullDim.labelling.row
        (crossLift m wd thickSheet thinSheet setup side dir).stablePath := by
  rw [← gaugeRowEquiv_crossWall m wd thickSheet thinSheet setup side dir,
    outFD_row_retained m wd thickSheet thinSheet setup hGauged hOrd labelling₀ hRowVal
      hMatrixWall (crossWallEdge m wd thickSheet thinSheet setup side dir).stablePath,
    crossLift_stablePath m wd thickSheet thinSheet setup side dir]

/-- The candidate-side test: a retained occurrence of a cross-paired survivor
carries a given retained row exactly when the survivor's own row is that row. -/
theorem stablePath_crossRetained_iff (side dir : Bool)
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    ((crossRetained setup hGauged side dir).stablePath =
        retainedRow setup hGauged
          (gaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
            thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀)) ↔
      (crossWallEdge m wd thickSheet thinSheet setup side dir).stablePath = r₀ := by
  rw [stablePath_crossRetained setup hGauged side dir,
    ← gaugeRowEquiv_crossWall m wd thickSheet thinSheet setup side dir]
  constructor
  · intro h
    exact (gaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1).injective
      (injective_retainedRow setup hGauged h)
  · intro h
    exact congrArg _ (congrArg _ h)

/-- The dart-side test, the mirror of `stablePath_crossRetained_iff`.  Row
injectivity of `incomingRow` is
`NonTrivalentValencyTwoStarCountAll.injective_incomingRow`, which needs no
no-return hypothesis. -/
theorem label_dart_cross_iff (side dir : Bool) (d : StableSourceDarts.Dart wd.cover)
    (hd : label (wd.tracks.iso.dart d) = wd.fullDim.labelling.row
      (crossLift m wd thickSheet thinSheet setup side dir).stablePath)
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (label (wd.tracks.iso.dart d) = wd.fullDim.labelling.row
        (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m)
          r₀)) ↔
      (crossWallEdge m wd thickSheet thinSheet setup side dir).stablePath = r₀ := by
  rw [hd, crossLift_stablePath m wd thickSheet thinSheet setup side dir]
  constructor
  · intro h
    exact NonTrivalentValencyTwoStarCountAll.injective_incomingRow m wd wallStar
      (wd.fullDim.labelling.row.injective h)
  · intro h
    exact congrArg _ (congrArg _ h)

/-- No member of a cross pair carries the vanishing chart row. -/
theorem label_dart_cross_ne_base (side dir : Bool) (d : StableSourceDarts.Dart wd.cover)
    (hd : label (wd.tracks.iso.dart d) = wd.fullDim.labelling.row
      (crossLift m wd thickSheet thinSheet setup side dir).stablePath) :
    label (wd.tracks.iso.dart d) ≠ label m.base := by
  rw [hd, crossLift_stablePath m wd thickSheet thinSheet setup side dir]
  exact NonTrivalentValencyThreeStarCount.labelling_row_incomingRow_ne_base m wd _

/-! ### The star count away from the anchor -/

include src in
/-- **The star count at a branch vertex away from the anchor, on a retained
row**: (T1), then the gauge leg and (T2), then the incoming tracking. -/
theorem incidence_inl_retained (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q)
    (w : {w : BranchVertex (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk thickSheet thinSheet) //
      w.1 ≠ gaugedAnchorVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk thickSheet thinSheet})
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (validCandidate setup).datum
        (candBranchMap setup hGauged (Sum.inl w)).1
        (retainedRow setup hGauged
          (gaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
            thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀)) =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd thickSheet thinSheet setup hGauged hOrd hEnds
            (candBranchMap setup hGauged (Sum.inl w)) ∧
        label d = (NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD m wd wallStar anchorBlk
            thickSheet thinSheet labelling₀ setup hGauged hOrd hRowVal hMatrixWall).labelling.row
          (retainedRow setup hGauged
            (gaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
              thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀))} := by
  classical
  set w₀ := (gaugeBranchEquivAnchorComplement (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    wallStar anchorBlk thickSheet thinSheet
    (NonTrivalentValencyTwoTracks.wallValid m wd).1).symm w with hw₀
  set j := (branchEquivGaugedAnchorComplement m wd thickSheet thinSheet hOrd hEnds).symm w
    with hj
  have hgw : gaugeBranchEquivAnchorComplement (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      wallStar anchorBlk thickSheet thinSheet
      (NonTrivalentValencyTwoTracks.wallValid m wd).1 w₀ = w := Equiv.apply_symm_apply _ _
  have hGV : NonTrivalentValencyTwoBaseOneExit.gaugeVertexEquiv
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet
      w₀.1.1 = w.1.1 :=
    (gaugeBranchEquivAnchorComplement_apply (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      wallStar anchorBlk thickSheet thinSheet
      (NonTrivalentValencyTwoTracks.wallValid m wd).1 w₀).symm.trans
      (congrArg (fun z : {z : BranchVertex (gaugedData
          (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet
          thinSheet) // z.1 ≠ gaugedAnchorVertex
          (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet
          thinSheet} ↦ z.1.1) hgw)
  have hjw : branchEquivAnchorComplement m wd hOrd hEnds j = w₀ := Equiv.apply_symm_apply _ _
  have hMapU : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne j.1.1 = w₀.1.1 :=
    (branchEquivAnchorComplement_apply m wd hOrd hEnds j).symm.trans
      (congrArg (fun z : {z : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
        z.1 ≠ NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk} ↦ z.1.1) hjw)
  rw [vertexEquiv_inl m wd thickSheet thinSheet setup hGauged hOrd hEnds w,
    outFD_row_retained m wd thickSheet thinSheet setup hGauged hOrd labelling₀ hRowVal
      hMatrixWall r₀,
    ← card_star_move_eq_incidenceCount m wd hEnds hLeft hRight j.1 j.2.1 j.2.2
      (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) r₀)]
  refine Eq.trans ?_ (incidenceCount_gauged_eq_incoming m wd thickSheet thinSheet hOrd src
    w₀.1.1 w₀.2 j.1.1 hMapU j.1.2 r₀)
  rw [hGV]
  exact (incidenceCount_candVertex setup hGauged w.1.1 w.2
    (gaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet
      thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀)).symm

/-- **The star count at a branch vertex away from the anchor, on the bridge
row.**  Both sides vanish: downstairs `h₁` runs `A₁ → F → A₂`, upstairs the
vanishing chart row reaches only the two anchor ends. -/
theorem incidence_inl_bridge (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q)
    (w : {w : BranchVertex (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk thickSheet thinSheet) //
      w.1 ≠ gaugedAnchorVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk thickSheet thinSheet}) :
    incidenceCount (validCandidate setup).datum
        (candBranchMap setup hGauged (Sum.inl w)).1 (bridgeRow setup hGauged) =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd thickSheet thinSheet setup hGauged hOrd hEnds
            (candBranchMap setup hGauged (Sum.inl w)) ∧
        label d = (NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD m wd wallStar anchorBlk
            thickSheet thinSheet labelling₀ setup hGauged hOrd hRowVal hMatrixWall).labelling.row
          (bridgeRow setup hGauged)} := by
  classical
  set j := (branchEquivGaugedAnchorComplement m wd thickSheet thinSheet hOrd hEnds).symm w
    with hj
  rw [incidenceCount_bridgeRow_inl_eq_zero setup hGauged w]
  symm
  rw [vertexEquiv_inl m wd thickSheet thinSheet setup hGauged hOrd hEnds w,
    outFD_row_bridge m wd thickSheet thinSheet setup hGauged hOrd labelling₀ hRowVal hMatrixWall]
  have h := card_star_move_eq_incidenceCount m wd hEnds hLeft hRight j.1 j.2.1 j.2.2
    (NonTrivalentValencyTwoTracks.facetRow m wd)
  rw [show wd.fullDim.labelling.row (NonTrivalentValencyTwoTracks.facetRow m wd) = label m.base
    from Equiv.apply_symm_apply _ _] at h
  rw [← h]
  exact incidenceCount_facetRow_eq_zero m wd hEnds hLeft hRight j.1 j.2.1 j.2.2


/-! ### The star count at `A₁`, against (H-BaseI) -/

/-- **The star count at `A₁`, on a retained row.**  The exact star
`{h₁, thick, thin}` is matched occurrence by dart with the moved star (H-BaseI)
prescribes: `m.base` carries the vanishing chart row, and the two remaining darts
carry the incoming rows of the two cross-paired survivors. -/
theorem incidence_inr_false_retained (hEnds : AnchorEnds m wd anchorBlk p q)
    (hPres : PrescribedBaseOneMove m wd thickSheet thinSheet setup p q)
    (r₀ : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (validCandidate setup).datum
        (candBranchMap setup hGauged (Sum.inr false)).1
        (retainedRow setup hGauged
          (gaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
            thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀)) =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd thickSheet thinSheet setup hGauged hOrd hEnds
            (candBranchMap setup hGauged (Sum.inr false)) ∧
        label d = (NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD m wd wallStar anchorBlk
            thickSheet thinSheet labelling₀ setup hGauged hOrd hRowVal hMatrixWall).labelling.row
          (retainedRow setup hGauged
            (gaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
              thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀))} := by
  classical
  obtain ⟨first, second, -, hFirstLab, hSecondLab, hStar⟩ :=
    prescribedBaseOneMove_spec m wd thickSheet thinSheet setup p q hPres
  rw [vertexEquiv_anchor_false m wd thickSheet thinSheet setup hGauged hOrd hEnds hPres.1.1,
    outFD_row_retained m wd thickSheet thinSheet setup hGauged hOrd labelling₀ hRowVal
      hMatrixWall r₀]
  have hRHS : Nat.card {d : D // graph.vert (m.perm d) = graph.vert m.base ∧
      label d = wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) r₀)} =
      ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
        fun d ↦ label d = wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc
          wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) r₀)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
  have hBridgeRow : ¬ ((bridgeND setup hGauged false).stablePath =
      retainedRow setup hGauged
        (gaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀)) := by
    rw [stablePath_bridgeND setup hGauged false]
    exact fun h ↦ retainedRow_ne_bridgeRow setup hGauged _ h.symm
  rw [hRHS, NonTrivalentValencyThreeStarCount.filter_moved_base m wd first second hStar,
    Finset.filter_insert,
    ite_eq_right (Ne.symm
      (NonTrivalentValencyThreeStarCount.labelling_row_incomingRow_ne_base m wd r₀)),
    NonTrivalentValencyThreeStarCount.card_filter_pair _ _
      (NonTrivalentValencyThreeStarCount.dart_ne m wd first second hStar)]
  show incidenceCount (validCandidate setup).datum
    (branchVertex setup (anchorBranchSheet setup false))
    (retainedRow setup hGauged
      (gaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1 r₀)) = _
  unfold incidenceCount
  rw [incidentEdges_anchorBranchVertex setup hGauged false, Finset.filter_insert,
    ite_eq_right hBridgeRow,
    NonTrivalentValencyThreeStarCount.card_filter_pair _ _
      (crossRetained_ne setup hGauged false),
    if_congr (stablePath_crossRetained_iff m wd thickSheet thinSheet setup hGauged false false
      r₀) rfl rfl,
    if_congr (stablePath_crossRetained_iff m wd thickSheet thinSheet setup hGauged false true
      r₀) rfl rfl,
    if_congr (label_dart_cross_iff m wd thickSheet thinSheet setup false false first hFirstLab
      r₀) rfl rfl,
    if_congr (label_dart_cross_iff m wd thickSheet thinSheet setup false true second hSecondLab
      r₀) rfl rfl]

/-- **The star count at `A₁`, on the bridge row.**  Both sides are one: the
bridge occurrence of `A₁`'s own fold sheet downstairs, the contracted dart
`m.base` upstairs. -/
theorem incidence_inr_false_bridge (hEnds : AnchorEnds m wd anchorBlk p q)
    (hPres : PrescribedBaseOneMove m wd thickSheet thinSheet setup p q) :
    incidenceCount (validCandidate setup).datum
        (candBranchMap setup hGauged (Sum.inr false)).1 (bridgeRow setup hGauged) =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd thickSheet thinSheet setup hGauged hOrd hEnds
            (candBranchMap setup hGauged (Sum.inr false)) ∧
        label d = (NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD m wd wallStar anchorBlk
            thickSheet thinSheet labelling₀ setup hGauged hOrd hRowVal hMatrixWall).labelling.row
          (bridgeRow setup hGauged)} := by
  classical
  obtain ⟨first, second, -, hFirstLab, hSecondLab, hStar⟩ :=
    prescribedBaseOneMove_spec m wd thickSheet thinSheet setup p q hPres
  rw [vertexEquiv_anchor_false m wd thickSheet thinSheet setup hGauged hOrd hEnds hPres.1.1,
    outFD_row_bridge m wd thickSheet thinSheet setup hGauged hOrd labelling₀ hRowVal hMatrixWall]
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
    · exact label_dart_cross_ne_base m wd thickSheet thinSheet setup false false first hFirstLab
    · exact label_dart_cross_ne_base m wd thickSheet thinSheet setup false true second hSecondLab
  have hR : ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
      fun d ↦ label d = label m.base).card = 1 := by
    rw [NonTrivalentValencyThreeStarCount.filter_moved_base m wd first second hStar,
      Finset.filter_insert, ite_eq_left rfl, hEmptyD]
    simp
  rw [hRHS, hR]
  show incidenceCount (validCandidate setup).datum
    (branchVertex setup (anchorBranchSheet setup false)) (bridgeRow setup hGauged) = 1
  have hEmptyC : (({crossRetained setup hGauged false false,
        crossRetained setup hGauged false true} :
        Finset (NonDanglingEdge (validCandidate setup).datum)).filter
      fun e ↦ e.stablePath = bridgeRow setup hGauged) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · rw [stablePath_crossRetained setup hGauged false false]
      exact retainedRow_ne_bridgeRow setup hGauged _
    · rw [stablePath_crossRetained setup hGauged false true]
      exact retainedRow_ne_bridgeRow setup hGauged _
  unfold incidenceCount
  rw [incidentEdges_anchorBranchVertex setup hGauged false, Finset.filter_insert,
    ite_eq_left (stablePath_bridgeND setup hGauged false), hEmptyC]
  simp

/-! ### The whole star count, and the link -/

include src in
/-- **The star count at every branch vertex except `A₂`.** -/
theorem incidence_of_ne_rightAnchor (hEnds : AnchorEnds m wd anchorBlk p q)
    (hPres : PrescribedBaseOneMove m wd thickSheet thinSheet setup p q)
    (v : BranchVertex (validCandidate setup).datum)
    (hv : v ≠ candBranchMap setup hGauged (Sum.inr true))
    (r : StablePath (validCandidate setup).datum) :
    incidenceCount (validCandidate setup).datum v.1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd thickSheet thinSheet setup hGauged hOrd hEnds v ∧
        label d = (NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD m wd wallStar anchorBlk
            thickSheet thinSheet labelling₀ setup hGauged hOrd hRowVal
            hMatrixWall).labelling.row r} := by
  classical
  obtain ⟨x, rfl⟩ : ∃ x, candBranchMap setup hGauged x = v :=
    ⟨(candBranchEquiv setup hGauged).symm v, (candBranchEquiv setup hGauged).apply_symm_apply v⟩
  obtain ⟨r', rfl⟩ : ∃ r', rowMap setup hGauged r' = r :=
    ⟨rowEquiv setup hGauged r, (rowEquiv setup hGauged).left_inv r⟩
  cases x with
  | inl w =>
    cases r' with
    | none =>
      exact incidence_inl_bridge m wd thickSheet thinSheet setup hGauged hOrd labelling₀
        hRowVal hMatrixWall hEnds hPres.1.1 hPres.1.2 w
    | some r₀ =>
      have h := incidence_inl_retained m wd thickSheet thinSheet setup hGauged hOrd src
        labelling₀ hRowVal hMatrixWall hEnds hPres.1.1 hPres.1.2 w
        ((gaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1).symm r₀)
      rwa [Equiv.apply_symm_apply] at h
  | inr side =>
    cases side with
    | true => exact absurd rfl hv
    | false =>
      cases r' with
      | none =>
        exact incidence_inr_false_bridge m wd thickSheet thinSheet setup hGauged hOrd
          labelling₀ hRowVal hMatrixWall hEnds hPres
      | some r₀ =>
        have h := incidence_inr_false_retained m wd thickSheet thinSheet setup hGauged hOrd
          labelling₀ hRowVal hMatrixWall hEnds hPres
          ((gaugeRowEquiv (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
            thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd).1).symm r₀)
        rwa [Equiv.apply_symm_apply] at h

include src in
/-- **The star count at `A₂`, from the leftover equation.**  A stable row of the
candidate meets its branch vertices twice in all, a chart row carries two darts
of the moved graph, `vertexEquiv` is a bijection, and the count agrees at every
other branch vertex; so it agrees at `A₂` too. -/
theorem incidence_inr_true (hEnds : AnchorEnds m wd anchorBlk p q)
    (hPres : PrescribedBaseOneMove m wd thickSheet thinSheet setup p q)
    (r : StablePath (validCandidate setup).datum) :
    incidenceCount (validCandidate setup).datum
        (candBranchMap setup hGauged (Sum.inr true)).1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd thickSheet thinSheet setup hGauged hOrd hEnds
            (candBranchMap setup hGauged (Sum.inr true)) ∧
        label d = (NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD m wd wallStar anchorBlk
            thickSheet thinSheet labelling₀ setup hGauged hOrd hRowVal
            hMatrixWall).labelling.row r} := by
  classical
  set outFD := NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD m wd wallStar anchorBlk
    thickSheet thinSheet labelling₀ setup hGauged hOrd hRowVal hMatrixWall with houtFD
  set v₀ := candBranchMap setup hGauged (Sum.inr true) with hv₀
  set f : BranchVertex (validCandidate setup).datum → ℕ :=
    fun v ↦ incidenceCount (validCandidate setup).datum v.1 r with hf
  set g : BranchVertex (validCandidate setup).datum → ℕ :=
    fun v ↦ Nat.card {d : D // graph.vert (m.perm d) =
        vertexEquiv m wd thickSheet thinSheet setup hGauged hOrd hEnds v ∧
      label d = outFD.labelling.row r} with hg
  have hSumF : ∑ v, f v = 2 :=
    NonTrivalentValencyThreeStarCount.sum_incidenceCount_branchVertex
      (validCandidate setup).datum outFD.connected outFD.pathEnds r
  have hSumG : ∑ v, g v = 2 := by
    rw [Fintype.sum_equiv (vertexEquiv m wd thickSheet thinSheet setup hGauged hOrd hEnds)
      g (fun x : V ↦ Nat.card {d : D // graph.vert (m.perm d) = x ∧
        label d = outFD.labelling.row r}) (fun v ↦ rfl)]
    exact NonTrivalentValencyThreeStarCount.sum_natCard_moved m wd (outFD.labelling.row r)
  have hAway : ∀ v ∈ Finset.univ.erase v₀, f v = g v := by
    intro v hv
    exact incidence_of_ne_rightAnchor m wd thickSheet thinSheet setup hGauged hOrd src
      labelling₀ hRowVal hMatrixWall hEnds hPres v (Finset.mem_erase.mp hv).1 r
  have hfsum := Finset.add_sum_erase Finset.univ f (Finset.mem_univ v₀)
  have hgsum := Finset.add_sum_erase Finset.univ g (Finset.mem_univ v₀)
  have hEq : ∑ x ∈ Finset.univ.erase v₀, f x = ∑ x ∈ Finset.univ.erase v₀, g x :=
    Finset.sum_congr rfl hAway
  show f v₀ = g v₀
  omega

include src in
/-- **The star count, at every branch vertex and every row, at a valency-two
Base I wall.**  This is the one geometric input
`NonTrivalentValencyTwoBaseOneTracks.typeChangeLink_of_incidence` needs, here
under (H-BaseI) alone. -/
theorem incidence_of_prescribedBaseOneMove (hEnds : AnchorEnds m wd anchorBlk p q)
    (hPres : PrescribedBaseOneMove m wd thickSheet thinSheet setup p q)
    (v : BranchVertex (validCandidate setup).datum)
    (r : StablePath (validCandidate setup).datum) :
    incidenceCount (validCandidate setup).datum v.1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd thickSheet thinSheet setup hGauged hOrd hEnds v ∧
        label d = (NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD m wd wallStar anchorBlk
            thickSheet thinSheet labelling₀ setup hGauged hOrd hRowVal
            hMatrixWall).labelling.row r} := by
  classical
  by_cases hv : v = candBranchMap setup hGauged (Sum.inr true)
  · subst hv
    exact incidence_inr_true m wd thickSheet thinSheet setup hGauged hOrd src labelling₀
      hRowVal hMatrixWall hEnds hPres r
  · exact incidence_of_ne_rightAnchor m wd thickSheet thinSheet setup hGauged hOrd src
      labelling₀ hRowVal hMatrixWall hEnds hPres v hv r

include src in
/-- **`OuterWalk.TypeChangeLink` at a valency-two Base I wall under (H-BaseI).**
`NonTrivalentValencyTwoBaseOneTracks` reduces the link to one star count against
the outgoing Base I presentation of `NonTrivalentValencyTwoBaseOneExit`; this
discharges it. -/
def typeChangeLink_of_prescribedBaseOneMove (hEnds : AnchorEnds m wd anchorBlk p q)
    (hPres : PrescribedBaseOneMove m wd thickSheet thinSheet setup p q) :
    TypeChangeLink m wd :=
  typeChangeLink_of_incidence m wd thickSheet thinSheet setup hGauged hOrd labelling₀ hRowVal
    hMatrixWall hEnds
    (incidence_of_prescribedBaseOneMove m wd thickSheet thinSheet setup hGauged hOrd src
      labelling₀ hRowVal hMatrixWall hEnds hPres)


include src in
/-- **The link from the row condition alone** -- the shape the move-to-type
dispatcher discharges (`NonTrivalentValencyTwoDispatcher`).  Under the
orientation clause the move always places one dart at each anchor end, so all
that has to be checked is that those two darts carry the *stable rows* of the two
cross-paired survivors. -/
def typeChangeLink_of_rows (hEnds : AnchorEnds m wd anchorBlk p q)
    (hLeft : (IncomingPairing.baseDart m wd).1.1 = p)
    (hRight : (IncomingPairing.opBaseDart m wd).1.1 = q)
    (hRows : ∀ x y : StableSourceDarts.Dart wd.cover, x.1.1 = p → y.1.1 = q →
      (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
          {wd.tracks.iso.dart x, wd.tracks.iso.dart y} →
      x.2.1.stablePath = (crossLift m wd thickSheet thinSheet setup false false).stablePath ∧
        y.2.1.stablePath =
          (crossLift m wd thickSheet thinSheet setup false true).stablePath) :
    TypeChangeLink m wd :=
  typeChangeLink_of_prescribedBaseOneMove m wd thickSheet thinSheet setup hGauged hOrd src
    labelling₀ hRowVal hMatrixWall hEnds
    (prescribedBaseOneMove_of_rows m wd thickSheet thinSheet setup hLeft hRight hRows)

end Wall

/-! ## 5.  The headline at an actual wall, with no hypothesis about the candidate -/

section Headline

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {deg : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival deg graph label (label m.base)}
  (wd : WallData arrival)

/-- **The Base I type-changing exit at a two-valent wall of the outer walk, with
the star count discharged.**
`NonTrivalentValencyTwoBaseOneExit.exists_typeChangeLink_baseOne_of_wallData`
with its `Tracks` hypothesis replaced by (H-BaseI): from the wall data and the
incoming two-valent star alone this produces the anchor block, the two anchor
ends `p`, `q` of the vanishing row (the incoming `2 + 2` / `1 + 3` / `3 + 1`
trichotomy is discharged internally by
`NonTrivalentValencyTwoTracksLeaf.exists_anchorEnds`), the ordinary-block
trivalence, the wall labelling of `NonTrivalentValencyTwoExitFree`, and -- for
every Configuration A split and prescribed cross pairing satisfying the two
index equalities -- the gauged Base I setup of `NonTrivalentValencyTwoGauge`,
the outgoing
`FullDimensionalSourcePresentation` on the incoming chart, the common minor
`AgreeOffColumn` that `OuterWalk.TypeChangeLink.agree` asks for, and the link
itself as soon as (H-BaseI) is supplied. -/
theorem exists_typeChangeLink_of_prescribedBaseOneMove_of_wallData
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    ∃ (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
      (p q : wd.cover.SourceVertex),
      nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            ⟨wd.a, wd.hab⟩ anchorBlock) = 4 ∧
      ∀ (_ : ∀ direction : Fin 2,
          (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
            anchorBlock direction).card = 2)
        (thickFirst thickSecond thinFirst thinSecond :
          IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
              ⟨wd.a, wd.hab⟩ anchorBlock)),
        thickFirst ∈ directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            wallStar anchorBlock 0 →
        thickSecond ∈ directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            wallStar anchorBlock 0 →
        thinFirst ∈ directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            wallStar anchorBlock 1 →
        thinSecond ∈ directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            wallStar anchorBlock 1 →
        thickFirst ≠ thickSecond → thinFirst ≠ thinSecond →
        (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex thickFirst.1 =
            (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex thinFirst.1 →
        (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex thickSecond.1 =
            (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex thinSecond.1 →
        ∃ (gauged : BaseOneSetup
            (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlock
              (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)) wallStar
            (gaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlock
              (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)))
          (out : FullDimensionalSourcePresentation (validCandidate gauged).datum coordinate),
          AgreeOffColumn wd.incomingMatrix
              (GluingDatum.LengthMatrixPresentation.matrix out.labelling.presentation)
              wd.column ∧
            (NonTrivalentValencyTwoBaseOneTracks.PrescribedBaseOneMove m wd
                (occurrenceSheet thickFirst) (occurrenceSheet thinFirst) gauged p q →
              Nonempty (TypeChangeLink m wd)) := by
  classical
  obtain ⟨anchorBlock, hNd, src⟩ :=
    NonTrivalentAnchorValency.twoBranchAnchor_of_single_row wd.cover wd.fullDim wd.hc wd.hab
      wd.hOne (wd.hForest m) wd.coordinates (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord
      wd.hFacetZero wallStar
  have hOrd := NonTrivalentValencyTwoRowEquiv.ordinaryTrivalent_of_wall_metric wd.cover
    wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base)
    wd.hRows wd.hZeroCoord anchorBlock hNd
  obtain ⟨labelling₀, hRowVal, hMatrixWall⟩ :=
    NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) wallStar wd.coordinates wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨p, q, hEnds⟩ := NonTrivalentValencyTwoTracksLeaf.exists_anchorEnds m wd src hOrd
  refine ⟨anchorBlock, p, q, hNd, ?_⟩
  intro hSplit thickFirst thickSecond thinFirst thinSecond hTF hTS hNF hNS hTNe hNNe
    hIndexFirst hIndexSecond
  obtain ⟨gauged, -⟩ := NonTrivalentValencyTwoGauge.exists_gauged_candidate_of_contraction
    wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) (wd.hCompat m) wallStar anchorBlock
    hNd hSplit thickFirst thickSecond thinFirst thinSecond hTF hTS hNF hNS hTNe hNNe
    hIndexFirst hIndexSecond
  have hGauged := NonTrivalentValencyTwoGauge.gaugedData_valid
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlock
    (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)
    (NonTrivalentValencyTwoTracks.wallValid m wd)
  refine ⟨gauged, NonTrivalentValencyTwoBaseOneExit.wallOutgoingFD m wd wallStar anchorBlock
    (occurrenceSheet thickFirst) (occurrenceSheet thinFirst) labelling₀ gauged hGauged hOrd
    hRowVal hMatrixWall, ?_, ?_⟩
  · have h := NonTrivalentValencyTwoBaseOneRowDictionary.agreeOffColumn_chartLabelling wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) wallStar anchorBlock
      (occurrenceSheet thickFirst) (occurrenceSheet thinFirst) labelling₀ gauged hGauged
      wd.coordinates wd.hZeroCoord wd.hPosCoord wd.hFacetZero hRowVal hMatrixWall
    rw [wd.targetEdge_symm_contracted] at h
    exact h
  · intro hPres
    exact ⟨typeChangeLink_of_prescribedBaseOneMove m wd (occurrenceSheet thickFirst)
      (occurrenceSheet thinFirst) gauged hGauged hOrd src labelling₀ hRowVal hMatrixWall
      hEnds hPres⟩

end Headline

end

end DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneStarCount
