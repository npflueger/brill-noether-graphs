module

public import DraismaVargasCount.GeneralKTracks
public import DraismaVargasCount.GeneralKExit

@[expose] public section

/-!
# The tracking of the general-`K` candidate at a four-valent wall

A. Vargas, *Catalan-many tropical morphisms to trees; Part II: A space and a count*,
arXiv:2609.09109, subsection "Valency-4 limits: Case {v4-nd4}" (`subsec-case-v4`), general `K`.

The tracking is produced through the entry point `GeneralKLink.tracksK_of_movedIncidence`, which
takes a vertex equivalence `BranchVertex (candK …).datum ≃ V` and the row-by-row star count
against the moved vertex map of `graph.move m`; no equivalence of stable rows is needed.

## Main results

* `vertexEquivK`: the branch vertices of `candK` are those of the gauged datum away
  from the anchor (`GeneralKTracks.branchEquiv`), which are those of the wall datum
  away from the anchor (`gaugeSub`), which are the branch vertices of the incoming
  cover other than the two ends of the vanishing occurrence (`K = 0`'s
  `branchEquivAnchorComplement`), plus the two bridge endpoints, sent to the two ends;
  then `coverBranchEquiv` and the incoming isomorphism.
* `incidence_of_prescribedPairingMove`: the star count at every branch vertex and
  every row, for any full-dimensional presentation `fdOut` of `candK` whose rows read
  the incoming chart on retained occurrences (`hRowOld`) and `label m.base` on the
  bridge (`hRowBridge`).  Away from the anchor it is (T1) + (T2) + (T3); at the bridge
  endpoint `A_1` it is the three survivors against (H-IV); at `A_2` it is the leftover
  equation (a row meets branch vertices twice, a chart label carries two darts).
* `tracksK`, and for the presentation `GeneralKExit.outgoingFDK` over the localized canonical
  background (`hRowOld`, `hRowBridge` discharged by `rowOld_outgoingFDK`,
  `rowBridge_outgoingFDK`): `tracksOutgoingFDK`, `nonempty_tracks_outgoingFDK`.

## The hypothesis (H-IV)

(H-IV), `NonTrivalentValencyFourTracks.PrescribedPairingMove`, is a hypothesis here, exactly as
in the `K = 0` case `NonTrivalentValencyFourStarCount.typeChangeLink_of_prescribedPairingMove`.
It is not discharged for a fixed `wallStar`: the `K = 0` dispatcher
(`NonTrivalentValencyFourDispatcher`) obtains it only after relabelling the star (`relabel`).
The general-`K` dispatch, which relabels the star in the same way and discharges (H-IV), is done
in `ValencyFourRealisation`; there `nonempty_tracks_outgoingFDK` enters the valency-four case of
the type-change step (step 3 of `DraismaVargasCount.Assembly`).  No `Prop` is introduced here.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.GeneralKStarCount

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.Count.GeneralKReceipts
open DraismaVargas.Count.GeneralKExitSetup
open DraismaVargas.Count.GeneralKTracksBlock
open DraismaVargas.Count.GeneralKTracks
open DraismaVargas.Count.GeneralKRowCore
open DraismaVargas.Count.GeneralKRowStar

/-! ## 1.  Two counting helpers -/

/-- A filtered three-element count is the sum of the three indicators. -/
theorem card_filter_triple {α : Type*} [DecidableEq α] (a b c : α) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (P : α → Prop) [DecidablePred P] :
    (({a, b, c} : Finset α).filter P).card =
      (if P a then 1 else 0) + (if P b then 1 else 0) + (if P c then 1 else 0) := by
  rw [Finset.filter_insert]
  by_cases h : P a
  · rw [ite_eq_left h, Finset.card_insert_of_notMem (by simp [Finset.mem_filter, hab, hac]),
      NonTrivalentValencyThreeStarCount.card_filter_pair b c hbc P, ite_eq_left h]
    omega
  · rw [ite_eq_right h, NonTrivalentValencyThreeStarCount.card_filter_pair b c hbc P, ite_eq_right h]
    omega

theorem ite3_congr {κ : Type*} [DecidableEq κ] {X₁ X₂ X₃ Y₁ Y₂ Y₃ c : κ} (h₁ : X₁ = Y₁)
    (h₂ : X₂ = Y₂) (h₃ : X₃ = Y₃) :
    ((if X₁ = c then 1 else 0) + (if X₂ = c then 1 else 0) + (if X₃ = c then 1 else 0) : ℕ) =
      (if Y₁ = c then 1 else 0) + (if Y₂ = c then 1 else 0) + (if Y₃ = c then 1 else 0) := by
  subst h₁ h₂ h₃
  rfl

/-! ## 2.  At the wall data of the outer walk -/

section Wall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
    ⟨wd.a, wd.hab⟩)
  (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
  (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      anchorBlock) = 4)
  (pairing : Fin 3)

local notation "vSrc" =>
  (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    wallStar (wd.hForest m) anchorBlock hAnchor)
local notation "vNG" =>
  (NonTrivalentUniqueFourValent.wall_noGlue wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (wd.hForest m))
local notation "vProf" =>
  (NonTrivalentUniqueFourValent.ordinaryBlockProfile_of_single_row wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne wallStar (wd.hForest m) wd.coordinates (label m.base) wd.hRows
    wd.hZeroCoord anchorBlock hAnchor)
local notation "vConn" =>
  (NonTrivalentUniqueFourValent.wall_target_connected wd.cover wd.fullDim wd.hab wd.hOne)
local notation "vGen" =>
  (NonTrivalentUniqueFourValent.wall_target_genus wd.cover wd.fullDim wd.hab wd.hOne)
local notation "vVal" =>
  (NonTrivalentUniqueFourValent.wall_valid wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (wd.hForest m))
set_option quotPrecheck false in
local notation "wW" => (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
local notation "vIncRow" =>
  (StablePathFacetContraction.incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (wd.hCompat m) (wd.hForest m))

/-! ### The incoming census at the wall -/

include wallStar hAnchor in
/-- **From the wall datum to the incoming cover (T3), label by label.**  At a
branch vertex of the wall datum other than the anchor, the surviving star filtered
by incoming chart label is the incoming cover's star filtered by that label.  On a
retained label this is `incidenceCount_wall_eq_incoming`; the vanishing label
`label m.base` meets neither side away from the two ends of the vanishing
occurrence. -/
theorem card_filter_wall_eq_incoming
    (w0 : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex)
    (hne : w0 ≠ NonTrivalentValencyFourTracks.anchorVertex m wd anchorBlock)
    (u : BranchVertex wd.cover) (hul : u.1 ≠ NonTrivalentValencyFourTracks.leftEnd m wd)
    (hur : u.1 ≠ NonTrivalentValencyFourTracks.rightEnd m wd)
    (hMapU : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne u.1 = w0) (c : coordinate) :
    ((incidentEdges (contractDatum wd.cover wd.hc wd.hab wd.hOne) w0).filter
        (fun e ↦ wd.fullDim.labelling.row (vIncRow e.stablePath) = c)).card =
      incidenceCount wd.cover u.1 (wd.fullDim.labelling.row.symm c) := by
  classical
  by_cases hc : ∃ p, vIncRow p = wd.fullDim.labelling.row.symm c
  · obtain ⟨p, hp⟩ := hc
    have hcEq : c = wd.fullDim.labelling.row (vIncRow p) := by rw [hp]; simp
    rw [← hp, ← NonTrivalentValencyFourStarCount.incidenceCount_wall_eq_incoming m wd wallStar
      anchorBlock hAnchor w0 hne u.1 hMapU u.2 p]
    unfold incidenceCount
    congr 1
    ext e
    simp only [Finset.mem_filter]
    refine and_congr_right fun _ ↦ ?_
    rw [hcEq]
    constructor
    · intro h
      exact NonTrivalentValencyFourStarCount.injective_incomingRow m wd wallStar
        (wd.fullDim.labelling.row.injective h)
    · intro h
      rw [h]
  · have hFacet : wd.fullDim.labelling.row.symm c = NonTrivalentValencyFourTracks.facetRow m wd := by
      by_contra hNe
      obtain ⟨p, hp⟩ := StablePathFacetContraction.exists_incomingRow_eq wd.cover wd.fullDim wd.hc
        wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) wd.coordinates (label m.base) wd.hRows
        wd.hZeroCoord _ hNe
      exact hc ⟨p, hp⟩
    rw [hFacet, NonTrivalentValencyFourStarCount.incidenceCount_facetRow_eq_zero m wd wallStar
      u.1 hul hur, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e _ he
    apply hc
    exact ⟨e.stablePath, by rw [← he]; simp⟩

variable (position : GeneralKReceipts.Position
    (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      wallStar (wd.hForest m) anchorBlock hAnchor) pairing
    (smallerSide (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor) pairing))
  (geometry : GeneralKReceipts.PairingBackground position.datum wallStar pairing
    anchorBlock.1)

local notation "cK" => (candK m wd wallStar anchorBlock hAnchor pairing position geometry)

/-- The gauge `GeneralKRowGauge.gaugeIso`, read on the branch vertices. -/
noncomputable def gaugeBranch :
    BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ≃ BranchVertex position.datum :=
  (GeneralKRowGauge.gaugeIso wallStar position.gauge).sourceVertexEquiv.subtypeEquiv fun v ↦ by
    rw [(GeneralKRowGauge.gaugeIso wallStar position.gauge).nonDanglingValency_map (vVal).1]

/-- The gauge, read on the branch vertices other than the anchor. -/
noncomputable def gaugeSub :
    {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
        w.1 ≠ NonTrivalentValencyFourTracks.anchorVertex m wd anchorBlock} ≃
      {w : BranchVertex position.datum // w.1 ≠ anchorV position} :=
  (gaugeBranch m wd wallStar anchorBlock hAnchor pairing position).subtypeEquiv fun w ↦ by
    show w.1 ≠ _ ↔ (GeneralKRowGauge.gaugeIso wallStar position.gauge).sourceVertexEquiv w.1 ≠
      position.datum.sourceEndpoint wW anchorBlock.1
    rw [← gaugeIso_sourceEndpoint_wall wallStar position.gauge anchorBlock.1]
    exact (GeneralKRowGauge.gaugeIso wallStar position.gauge).sourceVertexEquiv.injective.ne_iff.symm

theorem gaugeSub_val (w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
        w.1 ≠ NonTrivalentValencyFourTracks.anchorVertex m wd anchorBlock}) :
    (gaugeSub m wd wallStar anchorBlock hAnchor pairing position w).1.1 =
      (GeneralKRowGauge.gaugeIso wallStar position.gauge).sourceVertexEquiv w.1.1 := rfl

section Branch

variable (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor
  pairing position geometry)
include hBg

/-- **The branch vertices of the general-`K` candidate**: those of the gauged datum
other than the anchor, and the two endpoint vertices of the bridge. -/
noncomputable def branchEquivK :
    ({w : BranchVertex position.datum // w.1 ≠ anchorV position} ⊕ Bool) ≃
      BranchVertex (cK).datum :=
  branchEquiv position (vConn) (vGen) (vNG) geometry (vVal)
    (GeneralKRowsK.cK_genus m wd wallStar anchorBlock hAnchor pairing position geometry hBg)
    (GeneralKSourceFacts.newEdge_isDangling_off_bridge m wd wallStar anchorBlock hAnchor pairing
      position geometry hBg)
    (GeneralKSourceFacts.bridge_not_isDangling m wd wallStar anchorBlock hAnchor pairing position
      geometry)
    (GeneralKRowsK.starHyp m wd wallStar anchorBlock hAnchor pairing position geometry hBg)

theorem branchEquivK_inr (b : Bool) :
    (branchEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
      (Sum.inr b)).1 = epv (cK) b position.split.bridge := rfl

/-- **The vertex dictionary of the general-`K` type change**: the `K = 0` dictionary's
legs away from the anchor (the wall contraction and the incoming tracking), after the
general-`K` gauge; the two bridge endpoints go to the two ends of the vanishing
occurrence. -/
noncomputable def vertexEquivK : BranchVertex (cK).datum ≃ V :=
  ((branchEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).symm.trans
    (Equiv.sumCongr
      ((gaugeSub m wd wallStar anchorBlock hAnchor pairing position).symm.trans
        (NonTrivalentValencyFourTracks.branchEquivAnchorComplement m wd wallStar anchorBlock
          hAnchor).symm)
      (Equiv.refl Bool))).trans
    ((NonTrivalentValencyFourTracks.coverBranchEquiv m wd wallStar).trans wd.tracks.iso.vtx)

theorem vertexEquivK_inl (w : {w : BranchVertex position.datum // w.1 ≠ anchorV position}) :
    vertexEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
        (branchEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
          (Sum.inl w)) =
      wd.tracks.iso.vtx ((NonTrivalentValencyFourTracks.branchEquivAnchorComplement m wd wallStar
        anchorBlock hAnchor).symm
          ((gaugeSub m wd wallStar anchorBlock hAnchor pairing position).symm w)).1 := by
  simp only [vertexEquivK, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
    Sum.map_inl]
  rfl

theorem vertexEquivK_inr (b : Bool) :
    vertexEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
        (branchEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
          (Sum.inr b)) =
      wd.tracks.iso.vtx (if b then NonTrivalentValencyFourTracks.rightBranch m wd wallStar
        else NonTrivalentValencyFourTracks.leftBranch m wd wallStar) := by
  simp only [vertexEquivK, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
    Sum.map_inr]
  rfl

/-! ### The star count -/

section Count

variable
  (fdOut : FullDimensionalSourcePresentation
    (candK m wd wallStar anchorBlock hAnchor pairing position geometry).datum coordinate)
  (hRowOld : ∀ (e : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (h : ¬ IsDangling (candK m wd wallStar anchorBlock hAnchor pairing position geometry).datum
      ((candK m wd wallStar anchorBlock hAnchor pairing position geometry).oldSourceEdge
        ((GeneralKRowGauge.gaugeIso wallStar position.gauge).sourceEdgeEquiv e.1))),
    fdOut.labelling.row (NonDanglingEdge.stablePath
      (⟨(candK m wd wallStar anchorBlock hAnchor pairing position geometry).oldSourceEdge
          ((GeneralKRowGauge.gaugeIso wallStar position.gauge).sourceEdgeEquiv e.1), h⟩ :
        NonDanglingEdge (candK m wd wallStar anchorBlock hAnchor pairing position
          geometry).datum)) =
      wd.fullDim.labelling.row (StablePathFacetContraction.incomingRow wd.cover wd.fullDim wd.hc
        wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) e.stablePath))
  (hRowBridge : ∀ h : ¬ IsDangling
      (candK m wd wallStar anchorBlock hAnchor pairing position geometry).datum
      ((candK m wd wallStar anchorBlock hAnchor pairing position geometry).newSourceEdge
        position.split.bridge),
    fdOut.labelling.row (NonDanglingEdge.stablePath
      (⟨(candK m wd wallStar anchorBlock hAnchor pairing position geometry).newSourceEdge
          position.split.bridge, h⟩ :
        NonDanglingEdge (candK m wd wallStar anchorBlock hAnchor pairing position
          geometry).datum)) = label m.base)

include hRowOld in
/-- **The star count at a branch vertex away from the anchor**: (T1) the candidate's
star is the gauged datum's (`card_filter_branchMap_inl`), (T2) the gauged datum's is
the wall datum's (the four swap steps), (T3) the wall datum's is the incoming cover's
(`card_filter_wall_eq_incoming`), and away from the two ends of the vanishing
occurrence the Whitehead move does not change the star (`natCard_moved_of_ne`). -/
theorem incidence_inl
    (hBase : wd.tracks.iso.dart
      (NonTrivalentValencyFourTracks.facetDartLeft m wd wallStar) = m.base)
    (w : {w : BranchVertex position.datum // w.1 ≠ anchorV position})
    (r : StablePath (cK).datum) :
    incidenceCount (cK).datum
        (branchEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
          (Sum.inl w)).1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
            (branchEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
              (Sum.inl w)) ∧
        label d = fdOut.labelling.row r} := by
  classical
  have hValidG : position.datum.Valid := position.datum_valid (vVal)
  set c := fdOut.labelling.row r with hc
  set w0 := (gaugeSub m wd wallStar anchorBlock hAnchor pairing position).symm w with hw0
  set u := (NonTrivalentValencyFourTracks.branchEquivAnchorComplement m wd wallStar anchorBlock
    hAnchor).symm w0 with hu
  have hwVal : w.1.1 = (GeneralKRowGauge.gaugeIso wallStar position.gauge).sourceVertexEquiv w0.1.1 := by
    have h := (gaugeSub m wd wallStar anchorBlock hAnchor pairing position).apply_symm_apply w
    rw [← hw0] at h
    rw [← h]
    rfl
  have hMapU : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne u.1.1 = w0.1.1 := by
    have h := (NonTrivalentValencyFourTracks.branchEquivAnchorComplement m wd wallStar
      anchorBlock hAnchor).apply_symm_apply w0
    rw [← hu] at h
    rw [← h]
    rfl
  rw [vertexEquivK_inl]
  have hRHS := NonTrivalentValencyFourStarCount.natCard_moved_of_ne m wd wallStar u.1 hBase
    u.2.1 u.2.2 (wd.fullDim.labelling.row.symm c)
  rw [Equiv.apply_symm_apply] at hRHS
  rw [hRHS, ← card_filter_wall_eq_incoming m wd wallStar anchorBlock hAnchor w0.1.1 w0.2 u.1
    u.2.1 u.2.2 hMapU c, incidenceCount_eq_card_filter _ fdOut.labelling.row
    fdOut.labelling.row.injective r, ← hc]
  refine (card_filter_branchMap_inl position (vConn) (vGen) (vNG) geometry (vVal)
    (GeneralKRowsK.cK_genus m wd wallStar anchorBlock hAnchor pairing position geometry hBg)
    (GeneralKSourceFacts.newEdge_isDangling_off_bridge m wd wallStar anchorBlock hAnchor pairing
      position geometry hBg)
    (GeneralKSourceFacts.bridge_not_isDangling m wd wallStar anchorBlock hAnchor pairing position
      geometry)
    (GeneralKRowsK.starHyp m wd wallStar anchorBlock hAnchor pairing position geometry hBg)
    fdOut.labelling.row w c).trans ?_
  symm
  refine card_filter_of_star_map w0.1.1 w.1.1
    (fun e ↦ wd.fullDim.labelling.row (vIncRow e.stablePath))
    (fun o ↦ fdOut.labelling.row (ResolutionAwayFromWall.retainedEdge (cK) hValidG.1 o).stablePath)
    (fun e _ ↦ ⟨(GeneralKRowGauge.gaugeIso wallStar position.gauge).sourceEdgeEquiv e.1,
      fun h ↦ e.2 (((GeneralKRowGauge.gaugeIso wallStar position.gauge).isDangling_map_iff (vVal).1 e.1).mp h)⟩)
    ?_ ?_ ?_ ?_ c
  · intro e he
    refine (StablePathCount.mem_incidentEdges _ _ _).mpr ?_
    show Incident position.datum ((GeneralKRowGauge.gaugeIso wallStar position.gauge).sourceEdgeEquiv e.1) w.1.1
    rw [hwVal]
    exact ((GeneralKRowGauge.gaugeIso wallStar position.gauge).incident_map_iff e.1 w0.1.1).mpr
      ((StablePathCount.mem_incidentEdges _ _ _).mp he)
  · intro e _
    exact hRowOld e _
  · intro e₁ e₂ _ _ hEq
    exact Subtype.ext ((GeneralKRowGauge.gaugeIso wallStar position.gauge).sourceEdgeEquiv.injective (congrArg Subtype.val hEq))
  · rw [hwVal, (GeneralKRowGauge.gaugeIso wallStar position.gauge).nonDanglingValency_map (vVal).1]

omit hBg in
theorem gedge_selectedWallEdge (which : Bool) :
    (GeneralKRowGauge.gaugeIso wallStar position.gauge).sourceEdgeEquiv (NonTrivalentValencyFourStarCount.selectedWallEdge m wd wallStar
      anchorBlock hAnchor pairing which).1 =
      survG position (NonTrivalentValencyFourTracks.selectedLabel pairing false which) :=
  gaugeIso_sourceEdge_star wallStar position.gauge (vConn) (vGen) _ _

omit hBg in
include hRowOld in
/-- The chart label of a retained side-`false` anchor survivor. -/
theorem label_survND (which : Bool) :
    fdOut.labelling.row (survND position (vConn) (vGen) (vNG) geometry (vVal)
        (NonTrivalentValencyFourTracks.selectedLabel pairing false which)).stablePath =
      wd.fullDim.labelling.row (vIncRow (NonTrivalentValencyFourStarCount.selectedWallEdge m wd
        wallStar anchorBlock hAnchor pairing which).stablePath) := by
  have h' : ¬ IsDangling (cK).datum ((cK).oldSourceEdge ((GeneralKRowGauge.gaugeIso wallStar position.gauge).sourceEdgeEquiv
      (NonTrivalentValencyFourStarCount.selectedWallEdge m wd wallStar anchorBlock hAnchor pairing
        which).1)) := by
    rw [gedge_selectedWallEdge]
    exact (survND position (vConn) (vGen) (vNG) geometry (vVal)
      (NonTrivalentValencyFourTracks.selectedLabel pairing false which)).2
  rw [← hRowOld _ h']
  congr 2
  apply Subtype.ext
  show (cK).oldSourceEdge (survG position _) = _
  exact congrArg _ (gedge_selectedWallEdge m wd wallStar anchorBlock hAnchor pairing position
    which).symm

include hRowOld hRowBridge in
/-- **The star count at `A_1`.**  The exact star of the bridge endpoint on side `false`
(`card_filter_bridge`) is matched dart by dart with the moved star that (H-IV)
prescribes at `graph.vert m.base`: the bridge carries the vanishing chart label, as
`m.base` does, and the two anchor survivors carry the chart labels of the two
side-`false` darts. -/
theorem incidence_inr_false
    (hPres : NonTrivalentValencyFourTracks.PrescribedPairingMove m wd wallStar anchorBlock
      hAnchor pairing)
    (r : StablePath (cK).datum) :
    incidenceCount (cK).datum
        (branchEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
          (Sum.inr false)).1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
            (branchEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
              (Sum.inr false)) ∧
        label d = fdOut.labelling.row r} := by
  classical
  obtain ⟨hBase, first, second, hFirst, hSecond, hStarM⟩ := hPres
  set c := fdOut.labelling.row r with hc
  rw [vertexEquivK_inr, ite_eq_right Bool.false_ne_true,
    ← NonTrivalentValencyFourTracks.vert_base_eq m wd wallStar hBase,
    branchEquivK_inr, incidenceCount_eq_card_filter _ fdOut.labelling.row
      fdOut.labelling.row.injective r, ← hc]
  have hRHS : Nat.card {d : D // graph.vert (m.perm d) = graph.vert m.base ∧ label d = c} =
      ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
        fun d ↦ label d = c).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
  rw [hRHS, NonTrivalentValencyThreeStarCount.filter_moved_base m wd first second hStarM]
  have hMemErase : ∀ d ∈ ({wd.tracks.iso.dart first, wd.tracks.iso.dart second} : Finset D),
      d ≠ m.base := by
    intro d hd
    rw [← hStarM] at hd
    exact (Finset.mem_erase.mp hd).1
  have hb1 := hMemErase _ (Finset.mem_insert_self _ _)
  have hb2 := hMemErase _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hd12 := NonTrivalentValencyThreeStarCount.dart_ne m wd first second hStarM
  rw [card_filter_triple _ _ _ hb1.symm hb2.symm hd12]
  refine (card_filter_bridge position (vConn) (vGen) (vNG) geometry (vVal)
    (GeneralKRowsK.cK_genus m wd wallStar anchorBlock hAnchor pairing position geometry hBg)
    (GeneralKSourceFacts.newEdge_isDangling_off_bridge m wd wallStar anchorBlock hAnchor pairing
      position geometry hBg)
    (GeneralKSourceFacts.bridge_not_isDangling m wd wallStar anchorBlock hAnchor pairing position
      geometry) false fdOut.labelling.row c).trans ?_
  refine ite3_congr (hRowBridge _) ?_ ?_
  · refine (label_survND m wd wallStar anchorBlock hAnchor pairing position geometry fdOut
      hRowOld false).trans ?_
    exact (NonTrivalentValencyFourStarCount.label_dart_selected m wd wallStar anchorBlock hAnchor
      pairing first false hFirst).symm
  · refine (label_survND m wd wallStar anchorBlock hAnchor pairing position geometry fdOut
      hRowOld true).trans ?_
    exact (NonTrivalentValencyFourStarCount.label_dart_selected m wd wallStar anchorBlock hAnchor
      pairing second true hSecond).symm

include hRowOld hRowBridge in
/-- **The star count at every branch vertex except `A_2`.** -/
theorem incidence_of_ne_true
    (hPres : NonTrivalentValencyFourTracks.PrescribedPairingMove m wd wallStar anchorBlock
      hAnchor pairing)
    (v : BranchVertex (cK).datum)
    (hv : v ≠ branchEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
      (Sum.inr true))
    (r : StablePath (cK).datum) :
    incidenceCount (cK).datum v.1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg v ∧
        label d = fdOut.labelling.row r} := by
  obtain ⟨x, rfl⟩ : ∃ x, branchEquivK m wd wallStar anchorBlock hAnchor pairing position
      geometry hBg x = v :=
    ⟨_, (branchEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).apply_symm_apply v⟩
  rcases x with w | b
  · exact incidence_inl m wd wallStar anchorBlock hAnchor pairing position geometry hBg fdOut
      hRowOld hPres.1 w r
  · cases b with
    | true => exact absurd rfl hv
    | false =>
      exact incidence_inr_false m wd wallStar anchorBlock hAnchor pairing position geometry hBg
        fdOut hRowOld hRowBridge hPres r

include hRowOld hRowBridge in
/-- **The star count at `A_2`, from the leftover equation.**  A stable row of the
candidate meets its branch vertices twice in all (the candidate is connected with path
ends, as every full-dimensional presentation is), a chart row carries two darts of the
moved graph, `vertexEquivK` is a bijection, and the count agrees at every other
branch vertex. -/
theorem incidence_inr_true
    (hPres : NonTrivalentValencyFourTracks.PrescribedPairingMove m wd wallStar anchorBlock
      hAnchor pairing)
    (r : StablePath (cK).datum) :
    incidenceCount (cK).datum
        (branchEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
          (Sum.inr true)).1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
            (branchEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
              (Sum.inr true)) ∧
        label d = fdOut.labelling.row r} := by
  classical
  set v₀ := branchEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
    (Sum.inr true) with hv₀
  set f : BranchVertex (cK).datum → ℕ := fun v ↦ incidenceCount (cK).datum v.1 r with hf
  set g : BranchVertex (cK).datum → ℕ := fun v ↦ Nat.card {d : D // graph.vert (m.perm d) =
      vertexEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg v ∧
    label d = fdOut.labelling.row r} with hg
  have hSumF : ∑ v, f v = 2 :=
    NonTrivalentValencyThreeStarCount.sum_incidenceCount_branchVertex (cK).datum
      fdOut.connected fdOut.pathEnds r
  have hSumG : ∑ v, g v = 2 := by
    rw [Fintype.sum_equiv (vertexEquivK m wd wallStar anchorBlock hAnchor pairing position
      geometry hBg) g
      (fun x : V ↦ Nat.card {d : D // graph.vert (m.perm d) = x ∧
        label d = fdOut.labelling.row r}) (fun v ↦ rfl)]
    exact NonTrivalentValencyThreeStarCount.sum_natCard_moved m wd (fdOut.labelling.row r)
  have hAway : ∀ v ∈ Finset.univ.erase v₀, f v = g v := fun v hv ↦
    incidence_of_ne_true m wd wallStar anchorBlock hAnchor pairing position geometry hBg fdOut
      hRowOld hRowBridge hPres v (Finset.mem_erase.mp hv).1 r
  have hfsum := Finset.add_sum_erase Finset.univ f (Finset.mem_univ v₀)
  have hgsum := Finset.add_sum_erase Finset.univ g (Finset.mem_univ v₀)
  have hEq : ∑ x ∈ Finset.univ.erase v₀, f x = ∑ x ∈ Finset.univ.erase v₀, g x :=
    Finset.sum_congr rfl hAway
  show f v₀ = g v₀
  omega

include hRowOld hRowBridge in
/-- **The star count of the general-`K` candidate, at every branch vertex and every
row**, against the permuted vertex map of `graph.move m`, under (H-IV). -/
theorem incidence_of_prescribedPairingMove
    (hPres : NonTrivalentValencyFourTracks.PrescribedPairingMove m wd wallStar anchorBlock
      hAnchor pairing)
    (v : BranchVertex (cK).datum) (r : StablePath (cK).datum) :
    incidenceCount (cK).datum v.1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg v ∧
        label d = fdOut.labelling.row r} := by
  by_cases hv : v = branchEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
      (Sum.inr true)
  · subst hv
    exact incidence_inr_true m wd wallStar anchorBlock hAnchor pairing position geometry hBg
      fdOut hRowOld hRowBridge hPres r
  · exact incidence_of_ne_true m wd wallStar anchorBlock hAnchor pairing position geometry hBg
      fdOut hRowOld hRowBridge hPres v hv r

/-- **The tracking of the general-`K` member**, through the entry point
`GeneralKLink.tracksK_of_movedIncidence`. -/
noncomputable def tracksK
    (hPres : NonTrivalentValencyFourTracks.PrescribedPairingMove m wd wallStar anchorBlock
      hAnchor pairing) :
    Tracks fdOut (graph.move m) label :=
  GeneralKLink.tracksK_of_movedIncidence m wd wallStar anchorBlock hAnchor pairing position
    geometry fdOut (vertexEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg)
    (incidence_of_prescribedPairingMove m wd wallStar anchorBlock hAnchor pairing position
      geometry hBg fdOut hRowOld hRowBridge hPres)

end Count

/-! ### The outgoing presentation `outgoingFDK` -/

/-- **The retained rows of `outgoingFDK` keep their incoming chart labels**, read on the
literal retained copy of each surviving wall occurrence
(`outLabK_row_retained`, then the row chart and `wallLab_row_val`). -/
theorem rowOld_outgoingFDK
    (e : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (h : ¬ IsDangling (cK).datum ((cK).oldSourceEdge
      ((GeneralKRowGauge.gaugeIso wallStar position.gauge).sourceEdgeEquiv e.1))) :
    (GeneralKExit.outgoingFDK m wd wallStar anchorBlock hAnchor pairing position geometry
        hBg).labelling.row (NonDanglingEdge.stablePath
          (⟨(cK).oldSourceEdge ((GeneralKRowGauge.gaugeIso wallStar position.gauge).sourceEdgeEquiv e.1), h⟩ :
            NonDanglingEdge (cK).datum)) =
      wd.fullDim.labelling.row (vIncRow e.stablePath) := by
  refine (GeneralKExit.outLabK_row_retained m wd wallStar anchorBlock hAnchor pairing position
    geometry hBg e.stablePath).trans ?_
  rw [NonTrivalentValencyTwoExit.rowChart_some, NonTrivalentValencyTwoExit.wallLab_row_val,
    Equiv.swap_comm]
  exact Equiv.swap_apply_self _ _ _

/-- **The bridge row of `outgoingFDK` is the vanishing chart row**
(`outLabK_row_bridge`). -/
theorem rowBridge_outgoingFDK
    (h : ¬ IsDangling (cK).datum ((cK).newSourceEdge position.split.bridge)) :
    (GeneralKExit.outgoingFDK m wd wallStar anchorBlock hAnchor pairing position geometry
        hBg).labelling.row (NonDanglingEdge.stablePath
          (⟨(cK).newSourceEdge position.split.bridge, h⟩ : NonDanglingEdge (cK).datum)) =
      label m.base :=
  GeneralKExit.outLabK_row_bridge m wd wallStar anchorBlock hAnchor pairing position geometry hBg

/-- **The tracking of the general-`K` member by its outgoing presentation**
(`GeneralKExit.outgoingFDK`), under (H-IV). -/
noncomputable def tracksOutgoingFDK
    (hPres : NonTrivalentValencyFourTracks.PrescribedPairingMove m wd wallStar anchorBlock
      hAnchor pairing) :
    Tracks (GeneralKExit.outgoingFDK m wd wallStar anchorBlock hAnchor pairing position geometry
      hBg) (graph.move m) label :=
  tracksK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
    (GeneralKExit.outgoingFDK m wd wallStar anchorBlock hAnchor pairing position geometry hBg)
    (rowOld_outgoingFDK m wd wallStar anchorBlock hAnchor pairing position geometry hBg)
    (rowBridge_outgoingFDK m wd wallStar anchorBlock hAnchor pairing position geometry hBg)
    hPres

/-- **Headline.**  Over every localized canonical background, the outgoing
presentation `outgoingFDK` of the general-`K` candidate tracks the Whitehead move
`graph.move m`, under (H-IV) for the prescribed pairing. -/
theorem nonempty_tracks_outgoingFDK
    (hPres : NonTrivalentValencyFourTracks.PrescribedPairingMove m wd wallStar anchorBlock
      hAnchor pairing) :
    Nonempty (Tracks (GeneralKExit.outgoingFDK m wd wallStar anchorBlock hAnchor pairing position
      geometry hBg) (graph.move m) label) :=
  ⟨tracksOutgoingFDK m wd wallStar anchorBlock hAnchor pairing position geometry hBg hPres⟩

end Branch

end Wall

end DraismaVargas.Count.GeneralKStarCount
