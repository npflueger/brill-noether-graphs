import DraismaVargasCount.GeneralKTracksBlock
import DraismaVargasCount.GeneralKRowGauge

/-!
# The branch vertices of the general-`K` candidate at a four-valent wall

Vargas, Part II, the combinatorial setup for a change of combinatorial type and the
rigidity above `w_0` (`subsec-setup-determinants`, `lemma-above-w0`), and the valency-four
case `{v4-nd4}` (`subsec-case-v4`). The valency-four limits of general `K` feed the type
changes at merged-vertex valency four (step 3 of `Assembly`).

This file works over an arbitrary `GeneralKReceipts.Position` over a four-branch
anchor at a star `star` of a genus-zero connected target, and its candidate
`position.candidate … geometry` (at the wall of the outer walk this candidate is
`GeneralKExitSetup.candK`).  It classifies the branch vertices of the candidate:
they are the branch vertices of the gauged datum away from the anchor, together with
the two endpoints of the bridge occurrence.

## What is proved

* §1  The gauge `GeneralKRowGauge.gaugeIso` fixes wall vertices and relabels each star
  occurrence by its own permutation (`gaugeIso_sourceEndpoint_wall`,
  `gaugeIso_sourceEdge_star`); datum isomorphisms carry canonical occurrences to
  canonical occurrences (`sourceEdge_map`).
* §2  Survival of star occurrences, before and after the gauge
  (`data_survives_iff`, `gauged_survives_iff`, `gauged_isDangling_iff_off`).
* §3  The anchor block.  Its endpoint classes are `sideSheets` (`A₋` on the oriented
  side, `A₊` on the other); given B2 (`hB2`: the new occurrences of `A₋ ∆ A₊` dangle)
  and B3 (`hB3`: the bridge occurrence survives), each endpoint of the bridge carries
  exactly three survivors -- the bridge and the gauged survivors (`survG`) of the two
  star labels on its side (`incidentEdges_bridge`, `card_filter_bridge`) -- and every
  other vertex above the anchor block has surviving valency zero
  (`nd_anchor_of_mem`, `nd_anchor_of_not_mem`).
* §3, `Classification`.  Given `GeneralKRowStar.StarHyp` at the anchor, the branch
  vertices of the candidate are in bijection with (branch vertices of the gauged datum
  other than the anchor vertex) ⊕ `Bool` (`branchEquiv`, the `Bool` summand being the
  two bridge endpoints, `branchMap_inr`), and each branch vertex away from the anchor
  keeps its label-filtered star counts, read through the retained copies
  (`card_filter_branchMap_inl`).

At the wall, B2, B3, the genus hypothesis and `StarHyp` are theorems
(`GeneralKSourceFacts.newEdge_isDangling_off_bridge`, `bridge_not_isDangling`,
`GeneralKRowsK.cK_genus`, `GeneralKRowsK.starHyp`); `GeneralKStarCount` feeds them in.

**Overlap with `GeneralKRowsK`.**  `sideSheets`, `survG`, `endPart_anchor`,
`newPart_anchor` and `endpoint_rel_of_mem` here are the `Position`-generic forms of
the wall-level declarations of the same names in `GeneralKRowsK` (a separate
namespace); at the wall, `sideSheets` and `survG` agree with those by `rfl`.  Both are
needed because the classification below is stated for an arbitrary `Position`, where
the wall-level forms do not apply.

## What is NOT proved here

B2, B3, the genus equality and `StarHyp` are hypotheses in this file (discharged at the
wall elsewhere, as above).  Nothing here concerns stable rows, labellings or the
tracking itself; see `GeneralKStarCount`.  No `Prop` is introduced.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.GeneralKTracks

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.Count.GeneralKReceipts
open DraismaVargas.Count.GeneralKRowCore
open DraismaVargas.Count.GeneralKRowStar

/-! ## 1.  The general-`K` gauge, read through `GeneralKRowGauge.gaugeIso` -/

section Gauge

open GeneralKRowGauge

/-- A datum isomorphism carries canonical source occurrences to canonical source
occurrences (the edge analogue of `Transport.DatumIso.sourceEndpoint_map`). -/
theorem sourceEdge_map {target₁ target₂ : CFGraph} {degree : ℕ}
    {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
    (iso : Transport.DatumIso first second) (edge : target₁.edges) (sheet : Fin degree) :
    second.sourceEdge (iso.targetEdge edge) (iso.edgePerm edge sheet) =
      iso.sourceEdgeEquiv (first.sourceEdge edge sheet) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · show (second.edgePartition (iso.targetEdge edge)).repr (iso.edgePerm edge sheet) =
      iso.edgePerm edge ((first.edgePartition edge).repr sheet)
    rw [iso.edgePartition edge]
    simp [SheetPartition.relabel]

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  (star : W4TargetPairings.FourStar target wall)
  {data : GluingDatum target degree} {anchor : Fin degree}
  (gauge : LabelGauge data wall anchor)

theorem gaugeIso_vertexPerm_wall (s : Fin degree) :
    (gaugeIso star gauge).vertexPerm wall s = s := by
  simp [gaugeIso, Transport.DatumIso.trans, Transport.DatumIso.ofSheetRelabeling,
    step_vertexPermutation_wall]

theorem gaugeIso_edgePerm_star (hConnected : graph_connected target) (hGenus : genus target = 0)
    (label : Fin 4) (s : Fin degree) :
    (gaugeIso star gauge).edgePerm (star.edge label) s = gauge.perm label s := by
  simp [gaugeIso, Transport.DatumIso.trans, Transport.DatumIso.ofSheetRelabeling,
    step_edgePermutation star _ _ _ _ hConnected hGenus]
  fin_cases label <;> simp

/-- The gauge fixes every wall vertex of the source. -/
theorem gaugeIso_sourceEndpoint_wall (s : Fin degree) :
    (gaugeIso star gauge).sourceVertexEquiv (data.sourceEndpoint wall s) =
      (gauge.gaugedData star).sourceEndpoint wall s := by
  rw [← Transport.DatumIso.sourceEndpoint_map, gaugeIso_targetVertex,
    gaugeIso_vertexPerm_wall]

/-- The gauge relabels each star occurrence by its own permutation. -/
theorem gaugeIso_sourceEdge_star (hConnected : graph_connected target)
    (hGenus : genus target = 0) (label : Fin 4) (s : Fin degree) :
    (gaugeIso star gauge).sourceEdgeEquiv (data.sourceEdge (star.edge label) s) =
      (gauge.gaugedData star).sourceEdge (star.edge label) (gauge.perm label s) := by
  rw [← sourceEdge_map, gaugeIso_targetEdge, gaugeIso_edgePerm_star star gauge hConnected hGenus]

end Gauge

/-! ## 2.  Survivors at the wall, through the gauge -/

section Survivors

open NonTrivalentValencyFourKZero NonTrivalentValencyFourKZero.PrescribedPairing

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall} {anchor : W4Assembly.WallBlock data wall}
  (source : FourBranchAnchor data star anchor)

/-- At the anchor block, an occurrence of a star label survives exactly on that
label's branch class (target-direction injectivity). -/
theorem data_survives_iff (label : Fin 4) {s : Fin degree}
    (hs : (data.vertexPartition wall).Rel anchor.1 s) :
    ¬ IsDangling data (data.sourceEdge (star.edge label) s) ↔ s ∈ branchBlock source label := by
  constructor
  · intro h
    have hEqual := source.target_injective.unique label
      (source.sourceEdge label) (data.sourceEdge (star.edge label) s)
      (WallBlock.ofSourceEdge_eq_of_rel data star anchor label
        (source.sheet label) (source.sheet_wall_rel label))
      (WallBlock.ofSourceEdge_eq_of_rel data star anchor label s hs)
      rfl rfl (source.sourceEdge_survives label) h
    exact ((data.edgePartition (star.edge label)).mem_block_iff _ _).mpr
      ((LimitChainCore.sourceEdge_eq_iff_rel data _ _ _).mp hEqual)
  · intro h
    have hRel := ((data.edgePartition (star.edge label)).mem_block_iff _ _).mp h
    have hEq : data.sourceEdge (star.edge label) s = source.sourceEdge label :=
      ((LimitChainCore.sourceEdge_eq_iff_rel data _ _ _).mpr hRel).symm
    rw [hEq]
    exact source.sourceEdge_survives label

variable (gauge : LabelGauge data wall anchor.1)
  (hConnected : graph_connected target) (hGenus : genus target = 0) (hValid : data.Valid)
include hConnected hGenus hValid

/-- **The anchor survivors of the gauged datum**: at the anchor block, an
occurrence of a star label survives exactly on the gauged branch class. -/
theorem gauged_survives_iff (label : Fin 4) {s : Fin degree}
    (hs : (data.vertexPartition wall).Rel anchor.1 s) :
    ¬ IsDangling (gauge.gaugedData star) ((gauge.gaugedData star).sourceEdge (star.edge label) s) ↔
      s ∈ gaugedBlock source gauge label := by
  have hs' : s = gauge.perm label ((gauge.perm label).symm s) := by simp
  have hIn : (data.vertexPartition wall).Rel anchor.1 ((gauge.perm label).symm s) :=
    ((data.vertexPartition wall).mem_block_iff _ _).mp ((gauge.preserving label).symm_mem
      (((data.vertexPartition wall).mem_block_iff _ _).mpr hs))
  rw [hs', GeneralKRowGauge.isDangling_gauged_iff star gauge hConnected hGenus hValid, ← hs',
    data_survives_iff source label hIn]
  unfold gaugedBlock
  constructor
  · intro h
    exact Finset.mem_image.mpr ⟨_, h, by simp⟩
  · intro h
    obtain ⟨t, ht, hEq⟩ := Finset.mem_image.mp h
    rw [← hEq]
    simpa using ht

/-- Off the anchor block the gauge moves no sheet, so pruning is unchanged. -/
theorem gauged_isDangling_iff_off (label : Fin 4) {s : Fin degree}
    (hs : ¬ (data.vertexPartition wall).Rel anchor.1 s) :
    IsDangling (gauge.gaugedData star) ((gauge.gaugedData star).sourceEdge (star.edge label) s) ↔
      IsDangling data (data.sourceEdge (star.edge label) s) := by
  have hFix : gauge.perm label s = s :=
    (gauge.preserving label).2 s
      (fun hMem ↦ hs (((data.vertexPartition wall).mem_block_iff _ _).mp hMem))
  have h := GeneralKRowGauge.isDangling_gauged_iff star gauge hConnected hGenus hValid label s
  rw [hFix] at h
  exact h

omit hValid in
theorem gauged_sourceEdge_eq_iff (label : Fin 4) (s t : Fin degree) :
    (gauge.gaugedData star).sourceEdge (star.edge label) s =
        (gauge.gaugedData star).sourceEdge (star.edge label) t ↔
      (data.edgePartition (star.edge label)).Rel ((gauge.perm label).symm s)
        ((gauge.perm label).symm t) := by
  rw [LimitChainCore.sourceEdge_eq_iff_rel,
    gauge.gaugedData_edgePartition star hConnected hGenus label]
  have h := SheetPartition.relabel_rel_iff (data.edgePartition (star.edge label))
    (gauge.perm label) ((gauge.perm label).symm s) ((gauge.perm label).symm t)
  simpa using h

end Survivors

/-! ## 3.  The anchor block of the general-`K` candidate -/

section Anchor

open NonTrivalentValencyFourKZero NonTrivalentValencyFourKZero.PrescribedPairing
open GeneralKTracksBlock

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall} {anchor : W4Assembly.WallBlock data wall}
  {source : FourBranchAnchor data star anchor} {pairing : Fin 3} {side : Bool}
  (position : Position source pairing side)

/-- The endpoint class on one Boolean side: `A₋` on the oriented side, `A₊` on the
other. -/
noncomputable def sideSheets (b : Bool) : Finset (Fin degree) :=
  if b = side then position.split.minusSheets else position.split.plusSheets

theorem bridge_mem_sideSheets (b : Bool) : position.split.bridge ∈ sideSheets position b := by
  unfold sideSheets
  split_ifs
  · exact position.split.bridge_mem_minus
  · exact position.split.bridge_mem_plus

theorem sideSheets_subset (b : Bool) :
    sideSheets position b ⊆ (data.vertexPartition wall).block anchor.1 := by
  unfold sideSheets
  split_ifs
  · exact position.split.minus_subset
  · exact position.split.plus_subset

theorem rel_of_mem_sideSheets (b : Bool) {s : Fin degree} (hs : s ∈ sideSheets position b) :
    (data.vertexPartition wall).Rel anchor.1 s :=
  ((data.vertexPartition wall).mem_block_iff _ _).mp (sideSheets_subset position b hs)

theorem gaugedBlock_subset_sideSheets (label : Fin 4) :
    gaugedBlock source position.gauge label ⊆
      sideSheets position (W4TargetPairings.Pairing.labelRight pairing label) := by
  unfold sideSheets
  split_ifs with h
  · exact position.minus_sub label h
  · apply position.plus_sub label
    cases hL : W4TargetPairings.Pairing.labelRight pairing label <;> cases side <;> simp_all

theorem mem_sideSheets_or (b : Bool) {s : Fin degree}
    (hs : (data.vertexPartition wall).Rel anchor.1 s) :
    s ∈ sideSheets position b ∨ s ∈ sideSheets position (!b) := by
  have hMem : s ∈ position.split.minusSheets ∪ position.split.plusSheets := by
    rw [position.split.union_eq]
    exact ((data.vertexPartition wall).mem_block_iff _ _).mpr hs
  unfold sideSheets
  rcases Finset.mem_union.mp hMem with h | h <;> cases b <;> cases side <;> simp_all

theorem mem_bridgeSheets_iff {s : Fin degree} (b : Bool) :
    s ∈ position.split.bridgeSheets ↔ s ∈ sideSheets position b ∧ s ∈ sideSheets position (!b) := by
  unfold sideSheets GeneralKResolution.SplitData.bridgeSheets
  rw [Finset.mem_inter]
  cases b <;> cases side <;> simp [and_comm]

theorem endpoint_eq (b : Bool) :
    position.endpoint b = if b = side then position.split.left else position.split.right := rfl

/-- On the endpoint class of its side, the endpoint partition is that class. -/
theorem endpoint_rel_of_mem (b : Bool) {s : Fin degree} (hs : s ∈ sideSheets position b)
    (t : Fin degree) : (position.endpoint b).Rel s t ↔ t ∈ sideSheets position b := by
  rw [endpoint_eq]
  unfold sideSheets at hs ⊢
  split_ifs with h
  · rw [if_pos h] at hs
    have hb := (position.split.left_rel_bridge_iff s).mpr hs
    rw [← position.split.left_rel_bridge_iff]
    exact ⟨fun h' ↦ hb.trans h', fun h' ↦ hb.symm.trans h'⟩
  · rw [if_neg h] at hs
    have hb := (position.split.right_rel_bridge_iff s).mpr hs
    rw [← position.split.right_rel_bridge_iff]
    exact ⟨fun h' ↦ hb.trans h', fun h' ↦ hb.symm.trans h'⟩

/-- Elsewhere in the anchor block, the endpoint partition is a singleton. -/
theorem endpoint_rel_of_not_mem (b : Bool) {s : Fin degree}
    (hsA : (data.vertexPartition wall).Rel anchor.1 s) (hs : s ∉ sideSheets position b)
    (t : Fin degree) : (position.endpoint b).Rel s t ↔ t = s := by
  rw [endpoint_eq, ← SheetPartition.mem_block_iff]
  unfold sideSheets at hs
  split_ifs with h
  · rw [if_pos h] at hs
    rw [position.split.left_block_of_not_mem hs hsA, Finset.mem_singleton]
  · rw [if_neg h] at hs
    rw [position.split.right_block_of_not_mem hs hsA, Finset.mem_singleton]

theorem newEdge_rel_of_mem {s : Fin degree} (hs : s ∈ position.split.bridgeSheets)
    (t : Fin degree) : position.split.newEdge.Rel s t ↔ t ∈ position.split.bridgeSheets := by
  have hb := (position.split.newEdge_rel_bridge_iff s).mpr hs
  rw [← position.split.newEdge_rel_bridge_iff]
  exact ⟨fun h' ↦ hb.trans h', fun h' ↦ hb.symm.trans h'⟩

theorem newEdge_rel_of_not_mem {s : Fin degree}
    (hsA : (data.vertexPartition wall).Rel anchor.1 s) (hs : s ∉ position.split.bridgeSheets)
    (t : Fin degree) : position.split.newEdge.Rel s t ↔ t = s := by
  rw [← SheetPartition.mem_block_iff, position.split.newEdge_block_of_not_mem hs hsA,
    Finset.mem_singleton]

/-- The anchor survivor of one star label in the gauged datum. -/
noncomputable def survG (label : Fin 4) : position.datum.SourceEdge :=
  position.datum.sourceEdge (star.edge label) (position.gauge.perm label (source.sheet label))

section Candidate

variable (hConnected : graph_connected target) (hGenus : genus target = 0)
  (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
  (geometry : PairingBackground position.datum star pairing anchor.1)

theorem cand_right : (position.candidate hConnected hGenus hNoGlue geometry).right =
    star.right pairing := rfl

theorem cand_resolution_anchor {s : Fin degree}
    (hs : (data.vertexPartition wall).Rel anchor.1 s) :
    (position.candidate hConnected hGenus hNoGlue geometry).resolution
        ((position.datum.vertexPartition wall).repr s) = position.selected := by
  apply position.candidate_resolution_of_wall_rel hConnected hGenus hNoGlue geometry
  rw [position.datum_vertexPartition_wall]
  exact hs.trans ((data.vertexPartition wall).rel_repr_right s)

theorem endPart_anchor (b : Bool) {s : Fin degree}
    (hs : (data.vertexPartition wall).Rel anchor.1 s) (t : Fin degree) :
    (endPart (position.candidate hConnected hGenus hNoGlue geometry) b).Rel s t ↔
      (position.endpoint b).Rel s t := by
  rw [endPart_rel_iff, cand_resolution_anchor position hConnected hGenus hNoGlue geometry hs,
    position.selected_endpoint]

theorem newPart_anchor {s : Fin degree} (hs : (data.vertexPartition wall).Rel anchor.1 s)
    (t : Fin degree) :
    (pasted (position.candidate hConnected hGenus hNoGlue geometry)).newEdge.Rel s t ↔
      position.split.newEdge.Rel s t := by
  rw [newPart_rel_iff, cand_resolution_anchor position hConnected hGenus hNoGlue geometry hs,
    position.selected_newEdge]

/-- The new occurrence of a sheet of the bridge class is the bridge occurrence. -/
theorem newSourceEdge_eq_bridge {t : Fin degree} (ht : t ∈ position.split.bridgeSheets) :
    (position.candidate hConnected hGenus hNoGlue geometry).newSourceEdge t =
      (position.candidate hConnected hGenus hNoGlue geometry).newSourceEdge
        position.split.bridge := by
  rw [newSourceEdge_eq_iff, newPart_anchor position hConnected hGenus hNoGlue geometry
    (rel_of_mem_sideSheets position side
      ((mem_bridgeSheets_iff position side).mp ht).1)]
  exact (newEdge_rel_of_mem position ht _).mpr position.split.bridge_mem_bridgeSheets

variable (hValid : data.Valid)
  (hGenusC : genus (position.candidate hConnected hGenus hNoGlue geometry).datum.sourceGraph =
    genus position.datum.sourceGraph)
  (hB2 : ∀ sheet : Fin degree,
    sheet ∈ position.split.minusSheets \ position.split.plusSheets ∨
      sheet ∈ position.split.plusSheets \ position.split.minusSheets →
    IsDangling (position.candidate hConnected hGenus hNoGlue geometry).datum
      ((position.candidate hConnected hGenus hNoGlue geometry).newSourceEdge sheet))
  (hB3 : ¬ IsDangling (position.candidate hConnected hGenus hNoGlue geometry).datum
    ((position.candidate hConnected hGenus hNoGlue geometry).newSourceEdge
      position.split.bridge))

include hB2 in
/-- By B2, every surviving new occurrence of the anchor block is the bridge. -/
theorem new_anchor_survivor {t : Fin degree} (hb : ∃ b, t ∈ sideSheets position b)
    (hSurv : ¬ IsDangling (position.candidate hConnected hGenus hNoGlue geometry).datum
      ((position.candidate hConnected hGenus hNoGlue geometry).newSourceEdge t)) :
    t ∈ position.split.bridgeSheets := by
  by_contra hNot
  apply hSurv
  apply hB2
  obtain ⟨b, hb⟩ := hb
  have hMem : t ∈ position.split.minusSheets ∨ t ∈ position.split.plusSheets := by
    unfold sideSheets at hb
    split_ifs at hb
    · exact Or.inl hb
    · exact Or.inr hb
  unfold GeneralKResolution.SplitData.bridgeSheets at hNot
  simp only [Finset.mem_inter, not_and] at hNot
  simp only [Finset.mem_sdiff]
  rcases hMem with h | h
  · exact Or.inl ⟨h, hNot h⟩
  · exact Or.inr ⟨h, fun h' ↦ hNot h' h⟩

omit hNoGlue geometry in
theorem survG_ne (b : Bool) :
    survG position (firstLabel pairing b) ≠ survG position (secondLabel pairing b) := by
  intro h
  have h1 := congrArg (fun e : position.datum.SourceEdge ↦ e.1.1) h
  exact firstLabel_ne_secondLabel pairing b (star.edge_injective h1)

omit hNoGlue geometry in
theorem survG_target (label : Fin 4) : (survG position label).1.1 = star.edge label := rfl

omit hNoGlue geometry in
theorem survG_sheet_rel (label : Fin 4) :
    (data.vertexPartition wall).Rel anchor.1 (survG position label).1.2 := by
  have hPermA : (data.vertexPartition wall).Rel anchor.1
      (position.gauge.perm label (source.sheet label)) :=
    ((data.vertexPartition wall).mem_block_iff _ _).mp
      (gaugedBlock_subset_wall source position.gauge label
        (active_mem_gaugedBlock source position.gauge label))
  have h1 : (position.datum.vertexPartition wall).Rel
      (position.gauge.perm label (source.sheet label)) (survG position label).1.2 :=
    (star.edgePartition_refines_wall position.datum label).rel
      ((position.datum.edgePartition (star.edge label)).rel_repr_right _)
  rw [position.datum_vertexPartition_wall] at h1
  exact hPermA.trans h1

include hConnected hGenus hValid in
omit hNoGlue geometry in
theorem survG_survives (label : Fin 4) :
    ¬ IsDangling position.datum (survG position label) :=
  (gauged_survives_iff source position.gauge hConnected hGenus hValid label
    ((data.vertexPartition wall).mem_block_iff _ _ |>.mp
      (gaugedBlock_subset_wall source position.gauge label
        (active_mem_gaugedBlock source position.gauge label)))).mpr
    (active_mem_gaugedBlock source position.gauge label)

include hConnected hGenus hValid in
omit hNoGlue geometry in
/-- A surviving wall occurrence of the gauged datum at the anchor block is the
anchor survivor of its label. -/
theorem eq_survG {o : position.datum.SourceEdge} {label : Fin 4} (hT : o.1.1 = star.edge label)
    (hA : (data.vertexPartition wall).Rel anchor.1 o.1.2)
    (hSurv : ¬ IsDangling position.datum o) :
    o = survG position label ∧ o.1.2 ∈ gaugedBlock source position.gauge label := by
  have hSelf : position.datum.sourceEdge (star.edge label) o.1.2 = o := by
    rw [← hT]
    exact GluingDatum.sourceEdge_self position.datum o
  have hMem : o.1.2 ∈ gaugedBlock source position.gauge label := by
    rw [← gauged_survives_iff source position.gauge hConnected hGenus hValid label hA, hSelf]
    exact hSurv
  refine ⟨?_, hMem⟩
  rw [← hSelf]
  unfold survG
  rw [gauged_sourceEdge_eq_iff position.gauge hConnected hGenus]
  obtain ⟨t, ht, hEq⟩ := Finset.mem_image.mp hMem
  rw [← hEq]
  simp only [Equiv.symm_apply_apply]
  exact (((data.edgePartition (star.edge label)).mem_block_iff _ _).mp ht).symm

include hValid hGenusC hB2 hB3 in
/-- **The star of an anchor endpoint vertex** (the `K ≥ 1` analogue of the `K = 0` statement
`NonTrivalentValencyFourDictionary.nonDanglingIncident_endpointVertex`): on the endpoint class
of side `b`, the bridge and the two anchor survivors of that side. -/
theorem ndI_anchor_of_mem (b : Bool) {s : Fin degree} (hs : s ∈ sideSheets position b) :
    nonDanglingIncident (position.candidate hConnected hGenus hNoGlue geometry).datum
        (epv (position.candidate hConnected hGenus hNoGlue geometry) b s) =
      {(position.candidate hConnected hGenus hNoGlue geometry).newSourceEdge
          position.split.bridge,
        (position.candidate hConnected hGenus hNoGlue geometry).oldSourceEdge
          (survG position (firstLabel pairing b)),
        (position.candidate hConnected hGenus hNoGlue geometry).oldSourceEdge
          (survG position (secondLabel pairing b))} := by
  classical
  have hValidG : position.datum.Valid := position.datum_valid hValid
  have hsA := rel_of_mem_sideSheets position b hs
  ext f
  rw [mem_ndI_epv _ hValidG hGenusC]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨o, hSurv, hAt, hSide, hRel, rfl⟩ | ⟨t, hRel, hSt, rfl⟩)
    · obtain ⟨label, hLabel⟩ := star.exists_edge_eq o.1.1 hAt
      have hRel' := (endPart_anchor position hConnected hGenus hNoGlue geometry b hsA _).mp hRel
      have hMemS := (endpoint_rel_of_mem position b hs _).mp hRel'
      have hLab : W4TargetPairings.Pairing.labelRight pairing label = b := by
        rw [← star.right_edge, hLabel]
        exact hSide
      obtain ⟨hEq, -⟩ := eq_survG position hConnected hGenus hValid hLabel.symm
        (rel_of_mem_sideSheets position b hMemS) hSurv
      rw [hEq]
      rcases eq_first_or_second pairing label with h | h <;> rw [hLab] at h <;> rw [h] <;>
        simp
    · have htS := (endpoint_rel_of_mem position b hs _).mp
        ((endPart_anchor position hConnected hGenus hNoGlue geometry b hsA _).mp hRel)
      have hBr := new_anchor_survivor position hConnected hGenus hNoGlue geometry hB2
        ⟨b, htS⟩ hSt
      exact Or.inl (newSourceEdge_eq_bridge position hConnected hGenus hNoGlue geometry hBr)
  · have hOld : ∀ label, W4TargetPairings.Pairing.labelRight pairing label = b →
        (∃ o : position.datum.SourceEdge, ¬ IsDangling position.datum o ∧
          o.1.1 ∈ GluingDatum.incidentEdges wall ∧
          (position.candidate hConnected hGenus hNoGlue geometry).right o.1.1 = b ∧
          (endPart (position.candidate hConnected hGenus hNoGlue geometry) b).Rel s o.1.2 ∧
          (position.candidate hConnected hGenus hNoGlue geometry).oldSourceEdge
              (survG position label) =
            (position.candidate hConnected hGenus hNoGlue geometry).oldSourceEdge o) := by
      intro label hLab
      have hMemG : (survG position label).1.2 ∈ gaugedBlock source position.gauge label :=
        (eq_survG position hConnected hGenus hValid (survG_target position label)
          (survG_sheet_rel position label)
          (survG_survives position hConnected hGenus hValid label)).2
      refine ⟨survG position label, survG_survives position hConnected hGenus hValid label,
        star.edge_mem_incidentEdges label, by rw [cand_right, survG_target, star.right_edge,
          hLab], ?_, rfl⟩
      rw [endPart_anchor position hConnected hGenus hNoGlue geometry b hsA,
        endpoint_rel_of_mem position b hs]
      rw [← hLab]
      exact gaugedBlock_subset_sideSheets position label hMemG
    rintro (rfl | rfl | rfl)
    · refine Or.inr ⟨position.split.bridge, ?_, hB3, rfl⟩
      rw [endPart_anchor position hConnected hGenus hNoGlue geometry b hsA,
        endpoint_rel_of_mem position b hs]
      exact bridge_mem_sideSheets position b
    · exact Or.inl (hOld _ (labelRight_firstLabel pairing b))
    · exact Or.inl (hOld _ (labelRight_secondLabel pairing b))

include hValid hGenusC hB2 in
/-- **Off its endpoint class, an anchor vertex carries no surviving occurrence.** -/
theorem ndI_anchor_of_not_mem (b : Bool) {s : Fin degree}
    (hsA : (data.vertexPartition wall).Rel anchor.1 s) (hs : s ∉ sideSheets position b) :
    nonDanglingIncident (position.candidate hConnected hGenus hNoGlue geometry).datum
        (epv (position.candidate hConnected hGenus hNoGlue geometry) b s) = ∅ := by
  classical
  have hValidG : position.datum.Valid := position.datum_valid hValid
  ext f
  rw [mem_ndI_epv _ hValidG hGenusC]
  simp only [Finset.notMem_empty, iff_false]
  rintro (⟨o, hSurv, hAt, hSide, hRel, rfl⟩ | ⟨t, hRel, hSt, rfl⟩)
  · have hEq := (endpoint_rel_of_not_mem position b hsA hs _).mp
      ((endPart_anchor position hConnected hGenus hNoGlue geometry b hsA _).mp hRel)
    obtain ⟨label, hLabel⟩ := star.exists_edge_eq o.1.1 hAt
    have hLab : W4TargetPairings.Pairing.labelRight pairing label = b := by
      rw [← star.right_edge, hLabel]
      exact hSide
    have hMem := (eq_survG position hConnected hGenus hValid hLabel.symm (hEq ▸ hsA) hSurv).2
    rw [hEq] at hMem
    exact hs (hLab ▸ gaugedBlock_subset_sideSheets position label hMem)
  · have hEq := (endpoint_rel_of_not_mem position b hsA hs _).mp
      ((endPart_anchor position hConnected hGenus hNoGlue geometry b hsA _).mp hRel)
    subst hEq
    have hOther : t ∈ sideSheets position (!b) := by
      rcases mem_sideSheets_or position b hsA with h | h
      · exact absurd h hs
      · exact h
    have hBr := new_anchor_survivor position hConnected hGenus hNoGlue geometry hB2
      ⟨!b, hOther⟩ hSt
    exact hs ((mem_bridgeSheets_iff position b).mp hBr).1

include hValid hGenusC hB2 hB3 in
theorem nd_anchor_of_mem (b : Bool) {s : Fin degree} (hs : s ∈ sideSheets position b) :
    nonDanglingValency (position.candidate hConnected hGenus hNoGlue geometry).datum
        (epv (position.candidate hConnected hGenus hNoGlue geometry) b s) = 3 := by
  classical
  rw [← card_nonDanglingIncident,
    ndI_anchor_of_mem position hConnected hGenus hNoGlue geometry hValid hGenusC hB2 hB3 b hs]
  have hne := survG_ne position b
  have hInj := ResolutionCut.oldSourceEdge_injective
    (position.candidate hConnected hGenus hNoGlue geometry)
  rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨new_ne_old _ _ _, new_ne_old _ _ _⟩),
    Finset.card_pair (fun h ↦ hne (hInj h))]

include hValid hGenusC hB2 in
theorem nd_anchor_of_not_mem (b : Bool) {s : Fin degree}
    (hsA : (data.vertexPartition wall).Rel anchor.1 s) (hs : s ∉ sideSheets position b) :
    nonDanglingValency (position.candidate hConnected hGenus hNoGlue geometry).datum
        (epv (position.candidate hConnected hGenus hNoGlue geometry) b s) = 0 := by
  rw [← card_nonDanglingIncident,
    ndI_anchor_of_not_mem position hConnected hGenus hNoGlue geometry hValid hGenusC hB2 b hsA hs,
    Finset.card_empty]

/-! ### The bridge endpoints, as surviving occurrences -/

/-- The bridge, as a surviving occurrence of the candidate. -/
noncomputable def bridgeND : NonDanglingEdge (position.candidate hConnected hGenus hNoGlue geometry).datum :=
  ⟨(position.candidate hConnected hGenus hNoGlue geometry).newSourceEdge position.split.bridge, hB3⟩

omit hB2 hGenusC in
/-- The retained anchor survivor of one star label, as a surviving occurrence of the
candidate. -/
noncomputable def survND (label : Fin 4) :
    NonDanglingEdge (position.candidate hConnected hGenus hNoGlue geometry).datum :=
  ResolutionAwayFromWall.retainedEdge (position.candidate hConnected hGenus hNoGlue geometry)
    (position.datum_valid hValid).1 ⟨survG position label,
      survG_survives position hConnected hGenus hValid label⟩

include hValid hGenusC hB2 hB3 in
/-- **The exact star of a bridge endpoint**, on surviving occurrences. -/
theorem incidentEdges_bridge (b : Bool) :
    incidentEdges (position.candidate hConnected hGenus hNoGlue geometry).datum
        (epv (position.candidate hConnected hGenus hNoGlue geometry) b position.split.bridge) =
      {bridgeND position hConnected hGenus hNoGlue geometry hB3,
        survND position hConnected hGenus hNoGlue geometry hValid (firstLabel pairing b),
        survND position hConnected hGenus hNoGlue geometry hValid (secondLabel pairing b)} := by
  have hStar := ndI_anchor_of_mem position hConnected hGenus hNoGlue geometry hValid hGenusC hB2
    hB3 b (bridge_mem_sideSheets position b)
  ext e
  rw [StablePathCount.mem_incidentEdges]
  have hIff : Incident (position.candidate hConnected hGenus hNoGlue geometry).datum e.1
      (epv (position.candidate hConnected hGenus hNoGlue geometry) b position.split.bridge) ↔
      e.1 ∈ nonDanglingIncident (position.candidate hConnected hGenus hNoGlue geometry).datum
        (epv (position.candidate hConnected hGenus hNoGlue geometry) b position.split.bridge) := by
    rw [mem_nonDanglingIncident]
    exact ⟨fun h ↦ ⟨e.2, h⟩, fun h ↦ h.2⟩
  rw [hIff, hStar]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  · rintro (h | h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))

omit hB2 hGenusC in
theorem bridgeND_ne_survND (label : Fin 4) :
    bridgeND position hConnected hGenus hNoGlue geometry hB3 ≠
      survND position hConnected hGenus hNoGlue geometry hValid label := by
  intro h
  exact new_ne_old _ _ _ (congrArg Subtype.val h)

omit hB2 hGenusC hB3 in
theorem survND_ne (b : Bool) :
    survND position hConnected hGenus hNoGlue geometry hValid (firstLabel pairing b) ≠
      survND position hConnected hGenus hNoGlue geometry hValid (secondLabel pairing b) := by
  intro h
  exact survG_ne position b (ResolutionCut.oldSourceEdge_injective _ (congrArg Subtype.val h))

include hValid hGenusC hB2 hB3 in
/-- **The label-filtered count at a bridge endpoint**: three indicators, for the bridge
and the two anchor survivors of that side. -/
theorem card_filter_bridge (b : Bool) {κ : Type*} [DecidableEq κ]
    (lab : StablePath (position.candidate hConnected hGenus hNoGlue geometry).datum → κ) (c : κ) :
    ((incidentEdges (position.candidate hConnected hGenus hNoGlue geometry).datum
        (epv (position.candidate hConnected hGenus hNoGlue geometry) b position.split.bridge)).filter
        (fun f ↦ lab f.stablePath = c)).card =
      (if lab (bridgeND position hConnected hGenus hNoGlue geometry hB3).stablePath = c
        then 1 else 0) +
      (if lab (survND position hConnected hGenus hNoGlue geometry hValid
        (firstLabel pairing b)).stablePath = c then 1 else 0) +
      (if lab (survND position hConnected hGenus hNoGlue geometry hValid
        (secondLabel pairing b)).stablePath = c then 1 else 0) := by
  classical
  rw [incidentEdges_bridge position hConnected hGenus hNoGlue geometry hValid hGenusC hB2 hB3 b,
    Finset.filter_insert]
  have hne1 := bridgeND_ne_survND position hConnected hGenus hNoGlue geometry hValid hB3
    (firstLabel pairing b)
  have hne2 := bridgeND_ne_survND position hConnected hGenus hNoGlue geometry hValid hB3
    (secondLabel pairing b)
  have hne12 := survND_ne position hConnected hGenus hNoGlue geometry hValid b
  by_cases h : lab (bridgeND position hConnected hGenus hNoGlue geometry hB3).stablePath = c
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp [Finset.mem_filter, hne1, hne2]),
      NonTrivalentValencyThreeStarCount.card_filter_pair _ _ hne12, if_pos h]
    omega
  · rw [if_neg h, NonTrivalentValencyThreeStarCount.card_filter_pair _ _ hne12, if_neg h]
    omega

/-! ### Non-anchor blocks of the gauged datum -/

section Classification

variable (S : StarHyp (position.candidate hConnected hGenus hNoGlue geometry) anchor.1)

/-- The anchor vertex of the gauged datum. -/
noncomputable abbrev anchorV : position.datum.SourceVertex :=
  position.datum.sourceEndpoint wall anchor.1

local notation "cP" => (position.candidate hConnected hGenus hNoGlue geometry)

omit hNoGlue geometry in
theorem rel_datum_iff (x y : Fin degree) :
    (position.datum.vertexPartition wall).Rel x y ↔ (data.vertexPartition wall).Rel x y := by
  rw [position.datum_vertexPartition_wall]

omit hNoGlue geometry in
theorem eq_sourceEndpoint_of_wall (v : position.datum.SourceVertex) (hv : v.1.1 = wall) :
    v = position.datum.sourceEndpoint wall v.1.2 :=
  ((position.datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨hv.symm, rfl⟩).symm

omit hNoGlue geometry in
theorem not_rel_of_ne_anchorV {x : Fin degree}
    (hne : position.datum.sourceEndpoint wall x ≠ anchorV position) :
    ¬ (position.datum.vertexPartition wall).Rel anchor.1 x := by
  intro h
  apply hne
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact h.symm

include S in
theorem exists_candVertex (w : BranchVertex position.datum) (hw : w.1 ≠ anchorV position) :
    ∃ v : BranchVertex (cP).datum,
      (w.1.1.1 ≠ wall ∧ v.1 = ResolutionAwayFromWall.retainedVertex (cP) w.1) ∨
      (w.1.1.1 = wall ∧ ∃ (b : Bool) (y : Fin degree),
        (position.datum.vertexPartition wall).Rel w.1.1.2 y ∧ v.1 = epv (cP) b y ∧
        ∀ (b' : Bool) (y' : Fin degree), (position.datum.vertexPartition wall).Rel w.1.1.2 y' →
          3 ≤ nonDanglingValency (cP).datum (epv (cP) b' y') → epv (cP) b' y' = epv (cP) b y) := by
  by_cases hW : w.1.1.1 = wall
  · have hwE := eq_sourceEndpoint_of_wall position w.1 hW
    have hx : ¬ (position.datum.vertexPartition wall).Rel anchor.1 w.1.1.2 :=
      not_rel_of_ne_anchorV position (hwE ▸ hw)
    have h3 : nonDanglingValency position.datum
        (position.datum.sourceEndpoint wall w.1.1.2) = 3 := by
      have hle := S.valency _ hx
      have hge := w.2
      rw [hwE] at hge
      omega
    obtain ⟨b₀, y₀, hy₀, hnd, hUniq, -⟩ :=
      census_branch S.valid S.genus (S.star _ hx) (side_of_starHyp S hx) h3
    exact ⟨⟨epv (cP) b₀ y₀, by omega⟩, Or.inr ⟨hW, b₀, y₀, hy₀, rfl, hUniq⟩⟩
  · refine ⟨⟨ResolutionAwayFromWall.retainedVertex (cP) w.1, ?_⟩, Or.inl ⟨hW, rfl⟩⟩
    rw [ResolutionAwayFromWall.nonDanglingValency_retainedVertex _ S.valid S.genus _ hW]
    exact w.2

/-- The branch vertex of the candidate above a branch vertex of the gauged datum
other than the anchor. -/
noncomputable def candVertex (w : BranchVertex position.datum) (hw : w.1 ≠ anchorV position) :
    BranchVertex (cP).datum :=
  Classical.choose (exists_candVertex position hConnected hGenus hNoGlue geometry S w hw)

theorem candVertex_spec (w : BranchVertex position.datum) (hw : w.1 ≠ anchorV position) :
    (w.1.1.1 ≠ wall ∧ (candVertex position hConnected hGenus hNoGlue geometry S w hw).1 = ResolutionAwayFromWall.retainedVertex (cP) w.1) ∨
      (w.1.1.1 = wall ∧ ∃ (b : Bool) (y : Fin degree),
        (position.datum.vertexPartition wall).Rel w.1.1.2 y ∧
        (candVertex position hConnected hGenus hNoGlue geometry S w hw).1 = epv (cP) b y ∧
        ∀ (b' : Bool) (y' : Fin degree), (position.datum.vertexPartition wall).Rel w.1.1.2 y' →
          3 ≤ nonDanglingValency (cP).datum (epv (cP) b' y') → epv (cP) b' y' = epv (cP) b y) :=
  Classical.choose_spec (exists_candVertex position hConnected hGenus hNoGlue geometry S w hw)

omit hNoGlue geometry in
theorem bridge_rel_anchor :
    (position.datum.vertexPartition wall).Rel anchor.1 position.split.bridge := by
  rw [rel_datum_iff position]
  exact rel_of_mem_sideSheets position side (bridge_mem_sideSheets position side)

theorem epv_bool_eq {b b' : Bool} {y y' : Fin degree} (h : epv (cP) b y = epv (cP) b' y') :
    b = b' := by
  by_contra hne
  have hb' : b' = !b := by cases b <;> cases b' <;> simp_all
  subst hb'
  exact epv_ne_flip (cP) b y y' h

theorem rel_of_epv_eq {b : Bool} {y y' : Fin degree} (h : epv (cP) b y = epv (cP) b y') :
    (position.datum.vertexPartition wall).Rel y y' :=
  (endPart_refines (cP) b).rel ((epv_eq_iff (cP) b y y').mp h)

include hValid hGenusC hB2 hB3 in
theorem three_le_nd_bridge (b : Bool) :
    3 ≤ nonDanglingValency (cP).datum (epv (cP) b position.split.bridge) := by
  rw [nd_anchor_of_mem position hConnected hGenus hNoGlue geometry hValid hGenusC hB2 hB3 b
    (bridge_mem_sideSheets position b)]

/-- **The branch-vertex map of the general-`K` candidate**: the branch vertex above
each branch vertex of the gauged datum other than the anchor, and the two endpoint
vertices of the bridge. -/
noncomputable def branchMap :
    ({w : BranchVertex position.datum // w.1 ≠ anchorV position} ⊕ Bool) →
      BranchVertex (cP).datum
  | Sum.inl w => candVertex position hConnected hGenus hNoGlue geometry S w.1 w.2
  | Sum.inr b => ⟨epv (cP) b position.split.bridge,
      three_le_nd_bridge position hConnected hGenus hNoGlue geometry hValid hGenusC hB2 hB3 b⟩

theorem branchMap_inr (b : Bool) :
    (branchMap position hConnected hGenus hNoGlue geometry hValid hGenusC hB2 hB3 S (Sum.inr b)).1 = epv (cP) b position.split.bridge := rfl

theorem branchMap_injective :
    Function.Injective (branchMap position hConnected hGenus hNoGlue geometry hValid hGenusC hB2
      hB3 S) := by
  have hSpec := candVertex_spec position hConnected hGenus hNoGlue geometry S
  rintro (w₁ | b₁) (w₂ | b₂) hEq
  · have hv := congrArg Subtype.val hEq
    simp only [branchMap] at hv
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    rcases hSpec w₁.1 w₁.2 with ⟨hW₁, h₁⟩ | ⟨hW₁, c₁, y₁, hy₁, h₁, -⟩ <;>
      rcases hSpec w₂.1 w₂.2 with ⟨hW₂, h₂⟩ | ⟨hW₂, c₂, y₂, hy₂, h₂, -⟩
    · rw [h₁, h₂] at hv
      exact ResolutionStableIncidence.retainedVertex_injective_away _ _ _ hW₁ hW₂ hv
    · rw [h₁, h₂] at hv
      exact absurd hv (retainedVertex_ne_epv _ _ hW₁ _ _)
    · rw [h₁, h₂] at hv
      exact absurd hv.symm (retainedVertex_ne_epv _ _ hW₂ _ _)
    · rw [h₁, h₂] at hv
      have hc := epv_bool_eq position hConnected hGenus hNoGlue geometry hv
      subst hc
      have hr := rel_of_epv_eq position hConnected hGenus hNoGlue geometry hv
      rw [eq_sourceEndpoint_of_wall position w₁.1.1 hW₁,
        eq_sourceEndpoint_of_wall position w₂.1.1 hW₂]
      exact (position.datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl,
        ((hy₁.trans hr).trans hy₂.symm).trans (SheetPartition.rel_repr_right _ _)⟩
  · have hv := congrArg Subtype.val hEq
    simp only [branchMap] at hv
    exfalso
    rcases hSpec w₁.1 w₁.2 with ⟨hW₁, h₁⟩ | ⟨hW₁, c₁, y₁, hy₁, h₁, -⟩
    · rw [h₁] at hv
      exact retainedVertex_ne_epv _ _ hW₁ _ _ hv
    · rw [h₁] at hv
      have hc := epv_bool_eq position hConnected hGenus hNoGlue geometry hv
      subst hc
      have hr := rel_of_epv_eq position hConnected hGenus hNoGlue geometry hv
      have hwE := eq_sourceEndpoint_of_wall position w₁.1.1 hW₁
      exact not_rel_of_ne_anchorV position (hwE ▸ w₁.2)
        ((bridge_rel_anchor position).trans (hy₁.trans hr).symm)
  · have hv := congrArg Subtype.val hEq
    simp only [branchMap] at hv
    exfalso
    rcases hSpec w₂.1 w₂.2 with ⟨hW₂, h₂⟩ | ⟨hW₂, c₂, y₂, hy₂, h₂, -⟩
    · rw [h₂] at hv
      exact retainedVertex_ne_epv _ _ hW₂ _ _ hv.symm
    · rw [h₂] at hv
      have hc := epv_bool_eq position hConnected hGenus hNoGlue geometry hv
      subst hc
      have hr := rel_of_epv_eq position hConnected hGenus hNoGlue geometry hv
      have hwE := eq_sourceEndpoint_of_wall position w₂.1.1 hW₂
      exact not_rel_of_ne_anchorV position (hwE ▸ w₂.2)
        ((bridge_rel_anchor position).trans (hr.trans hy₂.symm))
  · have hv := congrArg Subtype.val hEq
    simp only [branchMap] at hv
    rw [epv_bool_eq position hConnected hGenus hNoGlue geometry hv]

include hB2 hB3 in
theorem branchMap_surjective :
    Function.Surjective (branchMap position hConnected hGenus hNoGlue geometry hValid hGenusC hB2
      hB3 S) := by
  have hValidG : position.datum.Valid := position.datum_valid hValid
  have hSpec := candVertex_spec position hConnected hGenus hNoGlue geometry S
  intro v
  rcases vertex_cases (cP) v.1 with ⟨old, hAway, hRet⟩ | ⟨b, hb⟩
  · have hnd : 3 ≤ nonDanglingValency position.datum old := by
      rw [← ResolutionAwayFromWall.nonDanglingValency_retainedVertex (cP) hValidG hGenusC old
        hAway, hRet]
      exact v.2
    have hw : (⟨old, hnd⟩ : BranchVertex position.datum).1 ≠ anchorV position := by
      intro h
      apply hAway
      rw [show old = anchorV position from h]
      rfl
    refine ⟨Sum.inl ⟨⟨old, hnd⟩, hw⟩, Subtype.ext ?_⟩
    rcases hSpec ⟨old, hnd⟩ hw with ⟨-, h⟩ | ⟨hW, -⟩
    · exact h.trans hRet
    · exact absurd hW hAway
  · by_cases hA : (position.datum.vertexPartition wall).Rel anchor.1 v.1.1.2
    · have hA' : (data.vertexPartition wall).Rel anchor.1 v.1.1.2 := (rel_datum_iff position _ _).mp hA
      by_cases hS : v.1.1.2 ∈ sideSheets position b
      · refine ⟨Sum.inr b, Subtype.ext ?_⟩
        show epv (cP) b position.split.bridge = v.1
        rw [← hb]
        apply (epv_eq_iff (cP) b _ _).mpr
        rw [endPart_anchor position hConnected hGenus hNoGlue geometry b
          ((rel_datum_iff position _ _).mp (bridge_rel_anchor position)),
          endpoint_rel_of_mem position b (bridge_mem_sideSheets position b)]
        exact hS
      · exfalso
        have h0 := nd_anchor_of_not_mem position hConnected hGenus hNoGlue geometry hValid hGenusC
          hB2 b hA' hS
        have h3 := v.2
        rw [← hb] at h3
        omega
    · have h3 := census_three_of_starHyp S hA b
        (rfl : (position.datum.vertexPartition wall).Rel v.1.1.2 v.1.1.2) (by rw [hb]; exact v.2)
      have hw : (⟨position.datum.sourceEndpoint wall v.1.1.2, by rw [h3]⟩ :
          BranchVertex position.datum).1 ≠ anchorV position := by
        intro h
        apply hA
        have := congrArg (fun u : position.datum.SourceVertex ↦ u.1.2) h
        exact this.symm
      refine ⟨Sum.inl ⟨_, hw⟩, Subtype.ext ?_⟩
      rcases hSpec _ hw with ⟨hW, -⟩ | ⟨-, c, y, hy, h, hUniq⟩
      · exact absurd rfl hW
      · show (candVertex position hConnected hGenus hNoGlue geometry S _ hw).1 = v.1
        rw [h, ← hb]
        refine (hUniq b v.1.1.2 (SheetPartition.rel_repr_left _ _) ?_).symm
        rw [hb]
        exact v.2

/-- **The branch-vertex classification of the general-`K` candidate.** -/
noncomputable def branchEquiv :
    ({w : BranchVertex position.datum // w.1 ≠ anchorV position} ⊕ Bool) ≃
      BranchVertex (cP).datum :=
  Equiv.ofBijective (branchMap position hConnected hGenus hNoGlue geometry hValid hGenusC hB2 hB3 S)
    ⟨branchMap_injective position hConnected hGenus hNoGlue geometry hValid hGenusC hB2 hB3 S,
     branchMap_surjective position hConnected hGenus hNoGlue geometry hValid hGenusC hB2 hB3 S⟩

theorem branchEquiv_apply (x : {w : BranchVertex position.datum // w.1 ≠ anchorV position} ⊕ Bool) :
    branchEquiv position hConnected hGenus hNoGlue geometry hValid hGenusC hB2 hB3 S x =
    branchMap position hConnected hGenus hNoGlue geometry hValid hGenusC hB2 hB3 S x := rfl

include hB2 hB3 in
/-- **(T1) at every branch vertex of the gauged datum other than the anchor**: its
label-filtered star counts, read through the retained copies, are those of the
branch vertex of the candidate above it. -/
theorem card_filter_branchMap_inl {κ : Type*} [DecidableEq κ] (lab : StablePath (cP).datum → κ)
    (w : {w : BranchVertex position.datum // w.1 ≠ anchorV position}) (c : κ) :
    ((incidentEdges (cP).datum (branchMap position hConnected hGenus hNoGlue geometry hValid
        hGenusC hB2 hB3 S (Sum.inl w)).1).filter
        (fun f ↦ lab f.stablePath = c)).card =
      ((incidentEdges position.datum w.1.1).filter (fun e ↦
        lab (ResolutionAwayFromWall.retainedEdge (cP) S.valid.1 e).stablePath = c)).card := by
  rcases candVertex_spec position hConnected hGenus hNoGlue geometry S w.1 w.2 with ⟨hW, h⟩ | ⟨hW, b, y, hy, h, hUniq⟩
  · show ((incidentEdges (cP).datum (candVertex position hConnected hGenus hNoGlue geometry
      S w.1 w.2).1).filter _).card = _
    rw [h]
    exact card_filter_retainedVertex S.valid S.genus lab w.1.1 hW c
  · have hwE := eq_sourceEndpoint_of_wall position w.1.1 hW
    have hx : ¬ (position.datum.vertexPartition wall).Rel anchor.1 w.1.1.1.2 :=
      not_rel_of_ne_anchorV position (hwE ▸ w.2)
    have h3 : nonDanglingValency position.datum
        (position.datum.sourceEndpoint wall w.1.1.1.2) = 3 := by
      have hle := S.valency _ hx
      have hge := w.1.2
      rw [hwE] at hge
      omega
    obtain ⟨b₀, y₀, hy₀, hnd, -, hCount⟩ := census_transport_of_starHyp S lab hx h3
    have hEq : epv (cP) b₀ y₀ = epv (cP) b y := hUniq b₀ y₀ hy₀ (by rw [hnd])
    show ((incidentEdges (cP).datum (candVertex position hConnected hGenus hNoGlue geometry
      S w.1 w.2).1).filter _).card = _
    rw [h, ← hEq, hCount c, ← hwE]

end Classification

end Candidate

end Anchor

end DraismaVargas.Count.GeneralKTracks
