module

public import DraismaVargasCount.GeneralKBackground

@[expose] public section

/-!
# Source facts of the general-`K` candidate at a four-valent wall

Vargas, Part II, the valency-four case `{v4-nd4}` (`subsec-case-v4`).  For the
general-`K` candidate `GeneralKExitSetup.candK` this file proves the source facts
used by its outgoing presentation (`GeneralKExit`) and by the tracking of the resulting
link (`GeneralKStarCount`): trivalence, dangling of the extra new-edge classes, survival
of the bridge, the source genus and path ends.
The valency-four limits feed the type changes at merged-vertex valency four
(step 3 of `Assembly`).

## The background hypothesis

`GeneralKExitSetup.CanonicalBackground` is the *literal* equality with
`W4Assembly.blockwiseResolution`.  That predicate is not satisfiable in general
(`GeneralKBackground.not_exists_literalBackground`), so theorems over it can be
vacuous.  The results here are stated over `LocalCanonicalBackground`, the localized
form, which is inhabited at every wall (`exists_localCanonicalBackground`).  The
candidate datum only reads a block's resolution on that block, so the two
forms describe the same candidate whenever both hold.

## What is proved (all at the wall data of the outer walk)

* **Trivalence** (`candidate_trivalent`): the candidate is trivalent.  Away from the
  wall, incoming trivalence descends through the four swap steps
  (`datum_valency_away`) and `ResolutionAwayFromWall`.  At the anchor block the
  endpoint class `A_b` of the bridge carries exactly the bridge and the two
  survivors of side `b` (`nonDanglingIncident_bridge_subset`,
  `nonDanglingValency_bridge_eq_three`), and every other anchor sheet is a
  singleton class whose only possible survivor is its own new occurrence
  (`nonDanglingIncident_singleton_subset`).  At a non-anchor block the
  `K = 0` census is ported generically (section `Ordinary`), for any candidate
  over the localized canonical background.
* **The extra new-edge classes dangle** (`newEdge_isDangling_off_bridge`): the new
  occurrence at every sheet of `A₋ \ A₊` or `A₊ \ A₋` is dangling.  Indeed the
  far endpoint class is `{sheet}` (`endpoint_block_of_not_mem`), and no branch
  on that side survives there, by target-direction injectivity in the gauged
  datum (`mem_gaugedBlock_of_survives`, via `datum_isDangling_iff`).  This
  holds on either side, for every sheet of the anchor block outside `A_b`
  (`newSourceEdge_isDangling_of_not_mem`).
* **The bridge survives** (`bridge_not_isDangling`), over *any* geometry.
  No background hypothesis is needed.
* **Source genus** (`candidate_sourceGenus`): the source genus of the wall datum.
* **Path ends** (`hasPathEnds_candidate`): `HasPathEnds`, by the generic port of the
  `K = 0` retained-row descent (`ordinaryBlockDescent`, `retainedRow`), the
  absorption of surviving new occurrences at non-anchor blocks
  (`newSourceEdge_absorbed`), and the non-anchor path-end transport
  (`exists_isPathEnd_ordinary`).  No row equivalence is needed.
* `exists_candidate_sourceFacts`: all of the above for one geometry.

The Position-level forms (`candidate_trivalent_of`, `hasPathEnds_of`,
`newEdge_isDangling_off_bridge'`, `bridge_not_isDangling_general`) take the
incoming census as explicit hypotheses: trivalence away from the wall,
target-direction injectivity at every wall block, `nd ≤ 3` at non-anchor
blocks, and `HasPathEnds` of the incoming datum.  At the wall data these are
`wallDatum_trivalent_away`, `wall_starInjective`,
`nonDanglingValency_wallBlock_le_three` and
`hasPathEnds_contractDatum_of_noContractedReturn`.

## What is NOT proved

* The outgoing `FullDimensionalSourcePresentation` of the candidate, its
  row dictionary and `AgreeOffColumn` against the incoming matrix: these are in
  `GeneralKExit`, and the tracking of the resulting link, under the prescribed-pairing
  hypothesis (H-IV) (`NonTrivalentValencyFourTracks.PrescribedPairingMove`), in
  `GeneralKStarCount` (`tracksOutgoingFDK`).
* The `K`-member `TypeChangeLink` with its `ColumnReceipt`: see
  `ValencyFourRealisation.linkReadsK_four_of_anchor`, whose only hypothesis is the
  wall valency.
* `GeneralKExitSetup.CanonicalBackground` is not used, and nothing here shows it is
  ever satisfiable at a wall with an ordinary r0-nd3 block; indeed it is not
  satisfiable in general (`GeneralKBackground.not_exists_literalBackground`).  Everything
  here goes through `LocalCanonicalBackground` instead.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.GeneralKSourceFacts

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.Count.GeneralKReceipts
open DraismaVargas.Count.GeneralKBackground

/-! ## 1.  Generic facts about an installed candidate -/

section Generic

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {gData : GluingDatum target degree}
  (C : BalancedGlobal.Candidate target degree gData wall)

/-- The outgoing source vertex above one side of the new target edge, on a
chosen sheet. -/
noncomputable def epv (sideValue : Bool) (sheet : Fin degree) : C.datum.SourceVertex :=
  C.datum.sourceEndpoint (if sideValue then freshVertex target else oldVertex target wall) sheet

theorem newSourceEdge_incident (sideValue : Bool) (sheet : Fin degree) :
    Incident C.datum (C.newSourceEdge sheet) (epv C sideValue sheet) := by
  cases sideValue
  · exact Or.inl (congrArg Prod.fst
      (GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet))
  · exact Or.inr (congrArg Prod.snd
      (GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet))

theorem oldSourceEdge_incident (edge : target.edges)
    (hAt : edge ∈ GluingDatum.incidentEdges wall) (sideValue : Bool)
    (hSide : C.right edge = sideValue) (sheet : Fin degree) :
    Incident C.datum (C.oldSourceEdge (gData.sourceEdge edge sheet)) (epv C sideValue sheet) := by
  cases sideValue
  · exact LimitChainCore.oldSourceEdge_incident_old _ edge hAt hSide sheet
  · exact M11SplitSurvival.oldSourceEdge_incident_fresh _ edge hAt hSide sheet

theorem datum_vertexPartition_eq (sideValue : Bool) :
    C.datum.vertexPartition (if sideValue then freshVertex target else oldVertex target wall) =
      (if sideValue then
          (LocalResolution.paste (gData.vertexPartition wall) C.resolution C.contracts).right
        else (LocalResolution.paste (gData.vertexPartition wall) C.resolution C.contracts).left) := by
  cases sideValue
  · show C.datum.vertexPartition (oldVertex target wall) = _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
    rfl
  · show C.datum.vertexPartition (freshVertex target) = _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]
    rfl

theorem endpoint_rel_iff (sideValue : Bool) (x y : Fin degree) :
    (C.datum.vertexPartition (if sideValue then freshVertex target else oldVertex target wall)).Rel
        x y ↔
      (if sideValue then (C.resolution ((gData.vertexPartition wall).repr x)).right
        else (C.resolution ((gData.vertexPartition wall).repr x)).left).Rel x y := by
  rw [datum_vertexPartition_eq]
  cases sideValue
  · exact SheetPartition.paste_rel_iff _ (fun blk ↦ (C.resolution blk).left)
      (fun blk ↦ (C.contracts blk).left_refines) x y
  · exact SheetPartition.paste_rel_iff _ (fun blk ↦ (C.resolution blk).right)
      (fun blk ↦ (C.contracts blk).right_refines) x y

theorem newEdge_rel_iff (x y : Fin degree) :
    (LocalResolution.paste (gData.vertexPartition wall) C.resolution C.contracts).newEdge.Rel x y ↔
      (C.resolution ((gData.vertexPartition wall).repr x)).newEdge.Rel x y :=
  SheetPartition.paste_rel_iff _ (fun blk ↦ (C.resolution blk).newEdge)
    (fun blk ↦ (C.resolution blk).edge_refines_left.trans (C.contracts blk).left_refines) x y

theorem endpoint_refines (sideValue : Bool) :
    (C.datum.vertexPartition (if sideValue then freshVertex target else oldVertex target wall)).Refines
      (gData.vertexPartition wall) := by
  rw [datum_vertexPartition_eq]
  cases sideValue
  · exact LocalResolution.pasteLeft_refines _ C.resolution C.contracts
  · exact LocalResolution.pasteRight_refines _ C.resolution C.contracts

theorem rel_of_incident (sideValue : Bool) {t : Fin degree} {e : C.datum.SourceEdge}
    (hIncident : Incident C.datum e (epv C sideValue t)) :
    (C.datum.vertexPartition (if sideValue then freshVertex target else oldVertex target wall)).Rel
      t e.1.2 := by
  rw [incident_iff_target_mem_and_rel] at hIncident
  exact Eq.trans
    ((C.datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right t)
    hIncident.2

theorem right_eq_of_incident_old (sideValue : Bool) {t : Fin degree} {old : gData.SourceEdge}
    (hIncident : Incident C.datum (C.oldSourceEdge old) (epv C sideValue t)) :
    old.1.1 ∈ GluingDatum.incidentEdges wall ∧ C.right old.1.1 = sideValue := by
  rw [incident_iff_target_mem_and_rel] at hIncident
  have hTargetMem := hIncident.1
  rw [BalancedGlobal.Candidate.oldSourceEdge_target] at hTargetMem
  have hMem : occurrenceEquiv target wall C.right (some old.1.1) ∈
      GluingDatum.incidentEdges (if sideValue then freshVertex target else oldVertex target wall) :=
    hTargetMem
  rw [GluingContraction.mem_incidentEdges_iff, occurrenceEquiv_some] at hMem
  cases sideValue
  · obtain ⟨hAt, hR⟩ := (oldEnds_incident_oldVertex_iff target wall C.right old.1.1).mp hMem
    exact ⟨(GluingContraction.mem_incidentEdges_iff wall _).mpr hAt, hR⟩
  · obtain ⟨hAt, hR⟩ := (oldEnds_incident_freshVertex_iff target wall C.right old.1.1).mp hMem
    exact ⟨(GluingContraction.mem_incidentEdges_iff wall _).mpr hAt, hR⟩

theorem newSourceEdge_eq_of_rel {a b : Fin degree}
    (h : (LocalResolution.paste (gData.vertexPartition wall) C.resolution C.contracts).newEdge.Rel
      a b) :
    C.newSourceEdge a = C.newSourceEdge b := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact h

/-- Every new occurrence is the new occurrence of the canonical sheet it
carries. -/
theorem newSourceEdge_repr (s : Fin degree) :
    C.newSourceEdge s = C.newSourceEdge (C.newSourceEdge s).1.2 := by
  apply newSourceEdge_eq_of_rel
  show _ = (LocalResolution.paste (gData.vertexPartition wall) C.resolution
    C.contracts).newEdge.repr
      ((LocalResolution.paste (gData.vertexPartition wall) C.resolution C.contracts).newEdge.repr s)
  rw [SheetPartition.repr_idem]

theorem epv_eq_of_rel (sideValue : Bool) {a b : Fin degree}
    (h : (C.datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).Rel a b) :
    epv C sideValue a = epv C sideValue b :=
  (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨rfl, h.trans
    ((C.datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right b)⟩

theorem new_ne_old (s : Fin degree) (old : gData.SourceEdge) :
    C.newSourceEdge s ≠ C.oldSourceEdge old := by
  intro hEq
  have h := (occurrenceEquiv target wall C.right).injective
    (congrArg (fun e : C.datum.SourceEdge ↦ e.1.1) hEq)
  cases h

end Generic

/-! ## 2.  The general-`K` gauge moves no danglingness -/

section Transport

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

/-- One branch swap across `label`, read on the star occurrence `other`: the
occurrence is relabelled exactly when `other = label`, and danglingness is
unchanged. -/
theorem swapStep_isDangling_iff (star : W4TargetPairings.FourStar target wall)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (current : GluingDatum target degree) (label : Fin 4)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (current.vertexPartition wall).Rel (permutation sheet) sheet)
    (hCurrent : current.Connected) (other : Fin 4) (x : Fin degree) :
    IsDangling (swapStep star current label permutation hFix)
        ((swapStep star current label permutation hFix).sourceEdge (star.edge other)
          (if other = label then permutation x else x)) ↔
      IsDangling current (current.sourceEdge (star.edge other) x) := by
  let r := BlockPreservingBranchSwap.branchSwapOfPerm current wall
    (TargetSeparation.farEndpoint wall (star.edge label))
    (TargetSeparation.farEndpoint_ne (selectedEdge_incident (star := star) label))
    permutation hFix
  have h := SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff r hCurrent
    (current.sourceEdge (star.edge other) x)
  rw [SheetRelabelPruning.sourceEdgeEquiv_sourceEdge] at h
  have hPerm : r.edgePermutation (star.edge other) x =
      if other = label then permutation x else x := by
    show GluingDatum.SheetRelabeling.togglePermutation
      (TargetBranchRegion.edgeMoved wall _ _ (star.edge other)) permutation x = _
    split_ifs with hOther
    · subst hOther
      rw [TargetSeparation.edgeMoved_self_eq_true (selectedEdge_incident (star := star) other)]
      rfl
    · rw [TargetSeparation.edgeMoved_eq_false hConnected hGenus
        (selectedEdge_incident (star := star) label)
        (selectedEdge_incident (star := star) other)
        (fun hEqual ↦ hOther (star.edge_injective hEqual).symm)]
      rfl
  rw [hPerm] at h
  exact h

variable {data : GluingDatum target degree} {star : W4TargetPairings.FourStar target wall}
  {anchor : W4Assembly.WallBlock data wall}
  {source : FourBranchAnchor data star anchor} {pairing : Fin 3} {side : Bool}
  (position : Position source pairing side)
  (hConnected : graph_connected target) (hGenus : genus target = 0) (hValid : data.Valid)

include hConnected hGenus hValid in
/-- **The gauge moves no danglingness.**  The star occurrence of `label` on
sheet `x` of the incoming datum is dangling exactly when its relabelled copy,
on sheet `perm label x`, is dangling in the gauged datum. -/
theorem datum_isDangling_iff (label : Fin 4) (x : Fin degree) :
    IsDangling position.datum
        (position.datum.sourceEdge (star.edge label) (position.gauge.perm label x)) ↔
      IsDangling data (data.sourceEdge (star.edge label) x) := by
  have hV1 : (position.gauge.stage1 star).Valid := swapStep_valid _ _ _ _ _ hValid
  have hV2 : (position.gauge.stage2 star).Valid := swapStep_valid _ _ _ _ _ hV1
  have hV3 : (position.gauge.stage3 star).Valid := swapStep_valid _ _ _ _ _ hV2
  have h1 := swapStep_isDangling_iff star hConnected hGenus data 0 (position.gauge.perm 0)
    (position.gauge.fix 0) hValid.1 label x
  have h2 := swapStep_isDangling_iff star hConnected hGenus (position.gauge.stage1 star) 1
    (position.gauge.perm 1)
    (fun sheet ↦ by rw [LabelGauge.stage1_wall]; exact position.gauge.fix 1 sheet) hV1.1 label
    (if label = 0 then position.gauge.perm 0 x else x)
  have h3 := swapStep_isDangling_iff star hConnected hGenus (position.gauge.stage2 star) 2
    (position.gauge.perm 2)
    (fun sheet ↦ by rw [LabelGauge.stage2_wall]; exact position.gauge.fix 2 sheet) hV2.1 label
    (if label = 1 then position.gauge.perm 1 (if label = 0 then position.gauge.perm 0 x else x)
      else (if label = 0 then position.gauge.perm 0 x else x))
  have h4 := swapStep_isDangling_iff star hConnected hGenus (position.gauge.stage3 star) 3
    (position.gauge.perm 3)
    (fun sheet ↦ by rw [LabelGauge.stage3_wall]; exact position.gauge.fix 3 sheet) hV3.1 label
    (if label = 2 then position.gauge.perm 2
        (if label = 1 then position.gauge.perm 1 (if label = 0 then position.gauge.perm 0 x else x)
          else (if label = 0 then position.gauge.perm 0 x else x))
      else (if label = 1 then position.gauge.perm 1
          (if label = 0 then position.gauge.perm 0 x else x)
        else (if label = 0 then position.gauge.perm 0 x else x)))
  have hSheet : (if label = 3 then position.gauge.perm 3
      (if label = 2 then position.gauge.perm 2
        (if label = 1 then position.gauge.perm 1 (if label = 0 then position.gauge.perm 0 x else x)
          else (if label = 0 then position.gauge.perm 0 x else x))
      else (if label = 1 then position.gauge.perm 1
          (if label = 0 then position.gauge.perm 0 x else x)
        else (if label = 0 then position.gauge.perm 0 x else x)))
    else (if label = 2 then position.gauge.perm 2
        (if label = 1 then position.gauge.perm 1 (if label = 0 then position.gauge.perm 0 x else x)
          else (if label = 0 then position.gauge.perm 0 x else x))
      else (if label = 1 then position.gauge.perm 1
          (if label = 0 then position.gauge.perm 0 x else x)
        else (if label = 0 then position.gauge.perm 0 x else x)))) =
      position.gauge.perm label x := by
    fin_cases label <;> simp
  rw [hSheet] at h4
  exact h4.trans (h3.trans (h2.trans h1))

end Transport

/-! ## 3.  Relabellings fixing the wall vertex -/

section Relabel

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {current : GluingDatum target degree}
  (r : current.SheetRelabeling) (hW : r.vertexPermutation wall = Equiv.refl (Fin degree))

include hW

theorem apply_vertexPartition_wall :
    r.apply.vertexPartition wall = current.vertexPartition wall := by
  show (current.vertexPartition wall).relabel (r.vertexPermutation wall) = _
  rw [hW]
  cases current.vertexPartition wall
  rfl

theorem sourceVertexEquiv_endpoint (y : Fin degree) :
    r.sourceVertexEquiv (current.sourceEndpoint wall y) = r.apply.sourceEndpoint wall y := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · show r.vertexPermutation wall ((current.vertexPartition wall).repr y) =
      (r.apply.vertexPartition wall).repr y
    rw [apply_vertexPartition_wall r hW, hW]
    rfl

theorem nonDanglingValency_endpoint (hConn : current.Connected) (y : Fin degree) :
    nonDanglingValency r.apply (r.apply.sourceEndpoint wall y) =
      nonDanglingValency current (current.sourceEndpoint wall y) := by
  rw [← sourceVertexEquiv_endpoint r hW y]
  exact SheetRelabelStable.nonDanglingValency_map r hConn _

theorem edgePermutation_rel (edge : target.edges)
    (hAt : edge ∈ GluingDatum.incidentEdges wall) (z : Fin degree) :
    (current.vertexPartition wall).Rel (r.edgePermutation edge z) z := by
  rcases (GluingContraction.mem_incidentEdges_iff wall edge).mp hAt with hE | hE
  · have h := r.compatible_left edge z
    rw [hE, hW] at h
    exact h
  · have h := r.compatible_right edge z
    rw [hE, hW] at h
    exact h

theorem starInjective_apply (star : W4TargetPairings.FourStar target wall)
    (hConn : current.Connected) (y : Fin degree)
    (hInj : NonDanglingStarInjective current star (WallBlock.ofSheet current wall y)) :
    NonDanglingStarInjective r.apply star (WallBlock.ofSheet r.apply wall y) := by
  constructor
  intro label first second hb1 hb2 ht1 ht2 hs1 hs2
  have hf : r.sourceEdgeEquiv (r.sourceEdgeEquiv.symm first) = first :=
    r.sourceEdgeEquiv.apply_symm_apply first
  have hg : r.sourceEdgeEquiv (r.sourceEdgeEquiv.symm second) = second :=
    r.sourceEdgeEquiv.apply_symm_apply second
  have hfs : ¬IsDangling current (r.sourceEdgeEquiv.symm first) := by
    intro h
    apply hs1
    rw [← hf]
    exact (SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff r hConn _).mpr h
  have hgs : ¬IsDangling current (r.sourceEdgeEquiv.symm second) := by
    intro h
    apply hs2
    rw [← hg]
    exact (SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff r hConn _).mpr h
  have hBlock : ∀ e : r.apply.SourceEdge, e.1.1 = star.edge label →
      WallBlock.ofSheet r.apply wall e.1.2 = WallBlock.ofSheet r.apply wall y →
      WallBlock.ofSheet current wall (r.sourceEdgeEquiv.symm e).1.2 =
        WallBlock.ofSheet current wall y := by
    intro e he hb
    rw [WallBlock.ofSheet_eq_iff_rel] at hb ⊢
    have hb' : (r.apply.vertexPartition wall).Rel ((r.apply.vertexPartition wall).repr y) e.1.2 :=
      hb
    rw [apply_vertexPartition_wall r hW] at hb'
    show (current.vertexPartition wall).Rel ((current.vertexPartition wall).repr y) _
    have hPerm := edgePermutation_rel r hW e.1.1
      (he ▸ star.edge_mem_incidentEdges label) ((r.edgePermutation e.1.1).symm e.1.2)
    rw [Equiv.apply_symm_apply] at hPerm
    exact hb'.trans hPerm
  have hEq := hInj.unique label (r.sourceEdgeEquiv.symm first) (r.sourceEdgeEquiv.symm second)
    (hBlock first ht1 hb1) (hBlock second ht2 hb2) ht1 ht2 hfs hgs
  rw [← hf, ← hg, hEq]

omit hW in
theorem nonDanglingValency_symm (hConn : current.Connected) (v : r.apply.SourceVertex) :
    nonDanglingValency r.apply v = nonDanglingValency current (r.sourceVertexEquiv.symm v) := by
  conv_lhs => rw [← r.sourceVertexEquiv.apply_symm_apply v]
  exact SheetRelabelStable.nonDanglingValency_map r hConn _

omit hW in
theorem sourceVertexEquiv_symm_fst (v : r.apply.SourceVertex) :
    (r.sourceVertexEquiv.symm v).1.1 = v.1.1 := rfl

end Relabel

/-! ### The four swap steps are such relabellings -/

section Steps

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

/-- The relabelling underlying one swap step. -/
noncomputable def stepRelabel (star : W4TargetPairings.FourStar target wall)
    (current : GluingDatum target degree) (label : Fin 4)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (current.vertexPartition wall).Rel (permutation sheet) sheet) :
    current.SheetRelabeling :=
  BlockPreservingBranchSwap.branchSwapOfPerm current wall
    (TargetSeparation.farEndpoint wall (star.edge label))
    (TargetSeparation.farEndpoint_ne (selectedEdge_incident (star := star) label))
    permutation hFix

theorem stepRelabel_apply (star : W4TargetPairings.FourStar target wall)
    (current : GluingDatum target degree) (label : Fin 4)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (current.vertexPartition wall).Rel (permutation sheet) sheet) :
    (stepRelabel star current label permutation hFix).apply =
      swapStep star current label permutation hFix := rfl

theorem stepRelabel_wall (star : W4TargetPairings.FourStar target wall)
    (current : GluingDatum target degree) (label : Fin 4)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (current.vertexPartition wall).Rel (permutation sheet) sheet) :
    (stepRelabel star current label permutation hFix).vertexPermutation wall =
      Equiv.refl (Fin degree) := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.vertexMoved wall _ _ wall) permutation = _
  rw [TargetBranchRegion.vertexMoved_wall]
  rfl

end Steps

/-! ### Chained through the general-`K` gauge -/

section Chain

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : W4TargetPairings.FourStar target wall}
  {anchor : W4Assembly.WallBlock data wall}
  {source : FourBranchAnchor data star anchor} {pairing : Fin 3} {side : Bool}
  (position : Position source pairing side) (hValid : data.Valid)

include hValid in
/-- A property of wall blocks that every swap step preserves is preserved by
the whole gauge. -/
theorem gauge_chain (P : GluingDatum target degree → Prop)
    (hStep : ∀ (current : GluingDatum target degree) (label : Fin 4)
      (permutation : Equiv.Perm (Fin degree))
      (hFix : ∀ sheet, (current.vertexPartition wall).Rel (permutation sheet) sheet),
      current.Valid → P current → P (swapStep star current label permutation hFix))
    (hData : P data) : P position.datum := by
  have hV1 : (position.gauge.stage1 star).Valid := swapStep_valid _ _ _ _ _ hValid
  have hV2 : (position.gauge.stage2 star).Valid := swapStep_valid _ _ _ _ _ hV1
  have hV3 : (position.gauge.stage3 star).Valid := swapStep_valid _ _ _ _ _ hV2
  have h1 : P (position.gauge.stage1 star) := hStep _ _ _ _ hValid hData
  have h2 : P (position.gauge.stage2 star) := hStep _ _ _ _ hV1 h1
  have h3 : P (position.gauge.stage3 star) := hStep _ _ _ _ hV2 h2
  exact hStep _ _ _ _ hV3 h3

include hValid

theorem datum_nonDanglingValency_endpoint (y : Fin degree) :
    nonDanglingValency position.datum (position.datum.sourceEndpoint wall y) =
      nonDanglingValency data (data.sourceEndpoint wall y) :=
  gauge_chain position hValid
    (fun g ↦ nonDanglingValency g (g.sourceEndpoint wall y) =
      nonDanglingValency data (data.sourceEndpoint wall y))
    (fun current label permutation hFix hCurrent hP ↦
      (nonDanglingValency_endpoint (stepRelabel star current label permutation hFix)
        (stepRelabel_wall star current label permutation hFix) hCurrent.1 y).trans hP)
    rfl

theorem datum_starInjective (y : Fin degree)
    (hInj : NonDanglingStarInjective data star (WallBlock.ofSheet data wall y)) :
    NonDanglingStarInjective position.datum star (WallBlock.ofSheet position.datum wall y) :=
  gauge_chain position hValid
    (fun g ↦ NonDanglingStarInjective g star (WallBlock.ofSheet g wall y))
    (fun current label permutation hFix hCurrent hP ↦
      starInjective_apply (stepRelabel star current label permutation hFix)
        (stepRelabel_wall star current label permutation hFix) star hCurrent.1 y hP)
    hInj

theorem datum_hasPathEnds (hEnds : HasPathEnds data) : HasPathEnds position.datum :=
  gauge_chain position hValid HasPathEnds
    (fun current label permutation hFix hCurrent hP ↦
      StableGraphIncidence.hasPathEnds_sheetRelabel
        (stepRelabel star current label permutation hFix) hCurrent.1 hP)
    hEnds

/-- Away from the wall vertex the gauge moves no surviving valency. -/
theorem datum_valency_away (hAway : ∀ w : data.SourceVertex, w.1.1 ≠ wall →
      nonDanglingValency data w ≤ 3) :
    ∀ v : position.datum.SourceVertex, v.1.1 ≠ wall → nonDanglingValency position.datum v ≤ 3 :=
  gauge_chain position hValid
    (fun g ↦ ∀ v : g.SourceVertex, v.1.1 ≠ wall → nonDanglingValency g v ≤ 3)
    (fun current label permutation hFix hCurrent hP v hv ↦ by
      have h := nonDanglingValency_symm (stepRelabel star current label permutation hFix)
        hCurrent.1 v
      show nonDanglingValency (stepRelabel star current label permutation hFix).apply v ≤ 3
      rw [h]
      exact hP _ hv)
    hAway

end Chain

/-! ## 4.  Survivors of the four branches in the gauged datum -/

section Survivors

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : W4TargetPairings.FourStar target wall}
  {anchor : W4Assembly.WallBlock data wall}
  {source : FourBranchAnchor data star anchor} {pairing : Fin 3} {side : Bool}
  (position : Position source pairing side)
  (hConnected : graph_connected target) (hGenus : genus target = 0) (hValid : data.Valid)

/-- The sheet carrying the surviving occurrence of one branch in the gauged
datum. -/
noncomputable def survivorSheet (label : Fin 4) : Fin degree :=
  position.gauge.perm label (source.sheet label)

/-- The surviving occurrence of one branch in the gauged datum. -/
noncomputable def survivorEdge (label : Fin 4) : position.datum.SourceEdge :=
  position.datum.sourceEdge (star.edge label) (survivorSheet position label)

theorem survivorSheet_mem (label : Fin 4) :
    survivorSheet position label ∈ gaugedBlock source position.gauge label :=
  active_mem_gaugedBlock source position.gauge label

include hConnected hGenus hValid in
theorem survivorEdge_survives (label : Fin 4) :
    ¬IsDangling position.datum (survivorEdge position label) := by
  intro h
  exact source.sourceEdge_survives label
    ((datum_isDangling_iff position hConnected hGenus hValid label (source.sheet label)).mp h)

include hConnected hGenus hValid in
/-- **Injectivity at the anchor, in the gauged datum.**  A surviving
occurrence of a branch on a sheet of the anchor block lies in that branch's
gauged class. -/
theorem mem_gaugedBlock_of_survives (label : Fin 4) {y : Fin degree}
    (hWall : (data.vertexPartition wall).Rel anchor.1 y)
    (hSurv : ¬IsDangling position.datum (position.datum.sourceEdge (star.edge label) y)) :
    y ∈ gaugedBlock source position.gauge label := by
  set x := (position.gauge.perm label).symm y with hx
  have hy : y = position.gauge.perm label x := by simp [hx]
  have hxWall : (data.vertexPartition wall).Rel anchor.1 x :=
    ((data.vertexPartition wall).mem_block_iff _ _).mp
      ((position.gauge.preserving label).symm_mem
        (((data.vertexPartition wall).mem_block_iff _ _).mpr hWall))
  rw [hy] at hSurv
  have hData : ¬IsDangling data (data.sourceEdge (star.edge label) x) := fun h ↦
    hSurv ((datum_isDangling_iff position hConnected hGenus hValid label x).mpr h)
  have hEqual := source.target_injective.unique label
    (source.sourceEdge label) (data.sourceEdge (star.edge label) x)
    (WallBlock.ofSourceEdge_eq_of_rel data star anchor label
      (source.sheet label) (source.sheet_wall_rel label))
    (WallBlock.ofSourceEdge_eq_of_rel data star anchor label x hxWall)
    rfl rfl (source.sourceEdge_survives label) hData
  have hRepr := congrArg (fun edge : data.SourceEdge ↦ edge.1.2) hEqual
  have hxMem : x ∈ branchBlock source label :=
    ((data.edgePartition (star.edge label)).mem_block_iff _ _).mpr hRepr
  rw [hy]
  exact Finset.mem_image_of_mem _ hxMem

include hConnected hGenus hValid in
/-- Every surviving occurrence of a branch at the anchor block of the gauged
datum *is* that branch's survivor. -/
theorem eq_survivorEdge (label : Fin 4) (old : position.datum.SourceEdge)
    (hTarget : old.1.1 = star.edge label)
    (hWall : (data.vertexPartition wall).Rel anchor.1 old.1.2)
    (hSurv : ¬IsDangling position.datum old) :
    old = survivorEdge position label := by
  have hOld : position.datum.sourceEdge (star.edge label) old.1.2 = old := by
    rw [← hTarget]
    exact W2MkkGraphData.sourceEdge_self _ old
  have hMem := mem_gaugedBlock_of_survives position hConnected hGenus hValid label hWall
    (by rw [hOld]; exact hSurv)
  have hRel : (gaugedEdge star position.gauge label).Rel (survivorSheet position label) old.1.2 :=
    gaugedEdge_rel_of_mem source position.gauge label hMem
  have hRel' : (position.datum.edgePartition (star.edge label)).Rel
      (survivorSheet position label) old.1.2 := by
    show ((position.gauge.gaugedData star).edgePartition (star.edge label)).Rel _ _
    rw [position.gauge.gaugedData_edgePartition star hConnected hGenus label]
    exact hRel
  rw [← hOld]
  unfold survivorEdge
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hRel'.symm

end Survivors

/-! ## 5.  The candidate at the anchor block -/

section Anchor

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : W4TargetPairings.FourStar target wall}
  {anchor : W4Assembly.WallBlock data wall}
  {source : FourBranchAnchor data star anchor} {pairing : Fin 3} {side : Bool}
  (position : Position source pairing side)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
  (geometry : PairingBackground position.datum star pairing anchor.1)

/-- The sheets of the endpoint class of the bridge on side `b`: `A₋` on the
oriented side, `A₊` on the other. -/
noncomputable def endSheets (b : Bool) : Finset (Fin degree) :=
  if b = side then position.split.minusSheets else position.split.plusSheets

theorem endpoint_rel_bridge_iff (b : Bool) (y : Fin degree) :
    (position.endpoint b).Rel position.split.bridge y ↔ y ∈ endSheets position b := by
  unfold Position.endpoint endSheets
  split_ifs
  · exact position.split.left_rel_bridge_iff y
  · exact position.split.right_rel_bridge_iff y

theorem endpoint_block_of_not_mem (b : Bool) {y : Fin degree}
    (hy : y ∉ endSheets position b) (hWall : (data.vertexPartition wall).Rel anchor.1 y) :
    (position.endpoint b).block y = {y} := by
  unfold Position.endpoint
  unfold endSheets at hy
  split_ifs at hy ⊢
  · exact position.split.left_block_of_not_mem hy hWall
  · exact position.split.right_block_of_not_mem hy hWall

theorem position_endpoint_refines (b : Bool) :
    (position.endpoint b).Refines (data.vertexPartition wall) := by
  unfold Position.endpoint
  split_ifs
  · exact position.split.left_refines_coarse
  · exact position.split.right_refines_coarse

theorem gaugedBlock_subset_endSheets (label : Fin 4) :
    gaugedBlock source position.gauge label ⊆
      endSheets position (W4TargetPairings.Pairing.labelRight pairing label) := by
  unfold endSheets
  split_ifs with h
  · exact position.minus_sub label h
  · apply position.plus_sub label
    cases hL : W4TargetPairings.Pairing.labelRight pairing label <;> cases side <;> simp_all

theorem mem_bridgeSheets_of (b : Bool) {u : Fin degree} (h1 : u ∈ endSheets position b)
    (h2 : u ∈ endSheets position (!b)) : u ∈ position.split.bridgeSheets := by
  unfold endSheets at h1 h2
  unfold GeneralKResolution.SplitData.bridgeSheets
  by_cases hb : b = side
  · subst hb
    rw [ite_eq_left rfl] at h1
    rw [ite_eq_right (by cases b <;> simp)] at h2
    exact Finset.mem_inter.mpr ⟨h1, h2⟩
  · rw [ite_eq_right hb] at h1
    rw [ite_eq_left (by cases b <;> cases side <;> simp_all)] at h2
    exact Finset.mem_inter.mpr ⟨h2, h1⟩

theorem endSheets_subset_wall (b : Bool) :
    endSheets position b ⊆ (data.vertexPartition wall).block anchor.1 := by
  unfold endSheets
  split_ifs
  · exact position.split.minus_subset
  · exact position.split.plus_subset

local notation "C" => (position.candidate hConnected hGenus hNoGlue geometry)

theorem candidate_right : (C).right = star.right pairing := rfl

theorem candidate_resolution_of_not_rel (block : Fin degree)
    (hBlock : ¬(position.datum.vertexPartition wall).Rel anchor.1 block) :
    (C).resolution block = geometry.resolution block := by
  unfold Position.candidate GeneralKReceipts.PairingBackground.background
    GlobalM11Arbitrary.Background.install
  exact LocalResolution.onBlock_of_not_rel _ _ _ _ _ hBlock

theorem candidate_resolution_repr {x : Fin degree}
    (hx : (data.vertexPartition wall).Rel anchor.1 x) :
    (C).resolution ((position.datum.vertexPartition wall).repr x) = position.selected := by
  apply position.candidate_resolution_of_wall_rel
  rw [position.datum_vertexPartition_wall]
  exact hx.trans ((data.vertexPartition wall).rel_repr_right x)

theorem candidate_endpoint_rel_iff (b : Bool) {x : Fin degree}
    (hx : (data.vertexPartition wall).Rel anchor.1 x) (y : Fin degree) :
    ((C).datum.vertexPartition (if b then freshVertex target else oldVertex target wall)).Rel x y ↔
      (position.endpoint b).Rel x y := by
  rw [endpoint_rel_iff, candidate_resolution_repr position hConnected hGenus hNoGlue geometry hx,
    position.selected_endpoint]

theorem candidate_newEdge_rel_iff {x : Fin degree}
    (hx : (data.vertexPartition wall).Rel anchor.1 x) (y : Fin degree) :
    (LocalResolution.paste (position.datum.vertexPartition wall) (C).resolution
        (C).contracts).newEdge.Rel x y ↔ position.split.newEdge.Rel x y := by
  rw [newEdge_rel_iff, candidate_resolution_repr position hConnected hGenus hNoGlue geometry hx,
    position.selected_newEdge]

/-- The endpoint vertex on side `b` at a sheet of `A_b` is the one at the
bridge sheet. -/
theorem epv_eq_bridge (b : Bool) {x : Fin degree} (hx : x ∈ endSheets position b) :
    epv (C) b x = epv (C) b position.split.bridge := by
  have hWall : (data.vertexPartition wall).Rel anchor.1 position.split.bridge :=
    ((data.vertexPartition wall).mem_block_iff _ _).mp
      (position.split.minus_subset position.split.bridge_mem_minus)
  apply (epv_eq_of_rel (C) b _).symm
  exact (candidate_endpoint_rel_iff position hConnected hGenus hNoGlue geometry b hWall x).mpr
    ((endpoint_rel_bridge_iff position b x).mpr hx)

variable (hValid : data.Valid)

/-- The survivor of a branch is incident to the endpoint vertex of its side
at the bridge sheet. -/
theorem survivor_incident (label : Fin 4) :
    Incident (C).datum ((C).oldSourceEdge (survivorEdge position label))
      (epv (C) (W4TargetPairings.Pairing.labelRight pairing label) position.split.bridge) := by
  rw [← epv_eq_bridge position hConnected hGenus hNoGlue geometry _
    (gaugedBlock_subset_endSheets position label (survivorSheet_mem position label))]
  exact oldSourceEdge_incident (C) (star.edge label) (star.edge_mem_incidentEdges label) _
    (star.right_edge pairing label) _

include hValid in
theorem survivor_survives (label : Fin 4) :
    ¬IsDangling (C).datum ((C).oldSourceEdge (survivorEdge position label)) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ (position.datum_valid hValid).1 _
    (survivorEdge_survives position hConnected hGenus hValid label)

end Anchor

/-! ## 6.  The bridge survives (no background hypothesis) -/

section Bridge

/-- The generic form of `NonTrivalentValencyFourRows.bridgeEdge_not_isDangling`:
a new occurrence whose two ends both carry a survivor survives. -/
theorem newSourceEdge_not_isDangling {target : CFGraph} {degree : ℕ} {wall : target.V}
    {gData : GluingDatum target degree} (C : BalancedGlobal.Candidate target degree gData wall)
    (sheet : Fin degree)
    (hLeft : nonDanglingValency C.datum (epv C false sheet) ≠ 0)
    (hRight : nonDanglingValency C.datum (epv C true sheet) ≠ 0) :
    ¬IsDangling C.datum (C.newSourceEdge sheet) := by
  have hEnds := GlobalResolution.sourceEnds_newSourceEdge gData wall C.right
    (LocalResolution.paste _ C.resolution C.contracts)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _ C.exterior) sheet
  intro hDangling
  rcases hDangling with hSide | hSide
  · obtain ⟨cut⟩ := hSide
    apply hLeft
    have hFst : (C.datum.sourceEnds (C.newSourceEdge sheet)).1 = epv C false sheet :=
      congrArg Prod.fst hEnds
    have hZero := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side _ cut cut.left_mem
    rwa [hFst] at hZero
  · obtain ⟨cut⟩ := hSide
    apply hRight
    have hSnd : (C.datum.sourceEnds (C.newSourceEdge sheet)).2 = epv C true sheet :=
      congrArg Prod.snd hEnds
    have hZero := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side _ cut cut.left_mem
    rwa [hSnd] at hZero

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : W4TargetPairings.FourStar target wall}
  {anchor : W4Assembly.WallBlock data wall}
  {source : FourBranchAnchor data star anchor} {pairing : Fin 3} {side : Bool}
  (position : Position source pairing side)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
  (geometry : PairingBackground position.datum star pairing anchor.1) (hValid : data.Valid)

local notation "C" => (position.candidate hConnected hGenus hNoGlue geometry)

include hValid in
theorem epv_bridge_ne_zero (b : Bool) :
    nonDanglingValency (C).datum (epv (C) b position.split.bridge) ≠ 0 := by
  have hL := labelRight_firstLabel pairing b
  have h := survivor_incident position hConnected hGenus hNoGlue geometry
    (firstLabel pairing b)
  rw [hL] at h
  exact ClassInjectivity.nonDanglingValency_ne_zero_of_incident _
    (survivor_survives position hConnected hGenus hNoGlue geometry hValid _) h

include hValid in
/-- **The bridge survives (general form)**, for *every* background
geometry: both of its ends carry a surviving retained branch occurrence. -/
theorem bridge_not_isDangling_general :
    ¬IsDangling (C).datum ((C).newSourceEdge position.split.bridge) :=
  newSourceEdge_not_isDangling (C) _
    (epv_bridge_ne_zero position hConnected hGenus hNoGlue geometry hValid false)
    (epv_bridge_ne_zero position hConnected hGenus hNoGlue geometry hValid true)

end Bridge

/-! ## 7.  The extra new-edge classes are dangling, and the anchor census -/

section Dangling

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : W4TargetPairings.FourStar target wall}
  {anchor : W4Assembly.WallBlock data wall}
  {source : FourBranchAnchor data star anchor} {pairing : Fin 3} {side : Bool}
  (position : Position source pairing side)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
  (geometry : PairingBackground position.datum star pairing anchor.1) (hValid : data.Valid)
  (hGenusC : genus (position.candidate hConnected hGenus hNoGlue geometry).datum.sourceGraph =
    genus position.datum.sourceGraph)

local notation "C" => (position.candidate hConnected hGenus hNoGlue geometry)

include hValid hGenusC in
/-- At a sheet of the anchor block outside `A_b`, the endpoint vertex on side
`b` is a singleton class whose only possible survivor is its own new
occurrence: every branch on side `b` has its survivor inside `A_b`. -/
theorem nonDanglingIncident_singleton_subset (b : Bool) {u : Fin degree}
    (hu : u ∉ endSheets position b) (hWall : (data.vertexPartition wall).Rel anchor.1 u) :
    nonDanglingIncident (C).datum (epv (C) b u) ⊆ {(C).newSourceEdge u} := by
  classical
  intro f hf
  obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hf
  have hRel := rel_of_incident (C) b hInc
  rw [candidate_endpoint_rel_iff position hConnected hGenus hNoGlue geometry b hWall] at hRel
  have hEq : f.1.2 = u := by
    have hMem : f.1.2 ∈ (position.endpoint b).block u :=
      ((position.endpoint b).mem_block_iff _ _).mpr hRel
    rw [endpoint_block_of_not_mem position b hu hWall, Finset.mem_singleton] at hMem
    exact hMem
  rcases ResolutionPruning.sourceEdge_cases (C) f with ⟨old, rfl⟩ | ⟨s, rfl⟩
  · exfalso
    obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old (C) b hInc
    obtain ⟨label, hLabel⟩ := star.exists_edge_eq old.1.1 hAt
    have hLabelSide : W4TargetPairings.Pairing.labelRight pairing label = b := by
      rw [← star.right_edge pairing label, hLabel]
      exact hSide
    have hOldSurv : ¬IsDangling position.datum old := fun h ↦ hSurv
      ((ResolutionPruning.isDangling_oldSourceEdge_iff (C) (position.datum_valid hValid)
        hGenusC old).mpr h)
    have hOldSheet : old.1.2 = u := hEq
    have hOldWall : (data.vertexPartition wall).Rel anchor.1 old.1.2 := hOldSheet ▸ hWall
    have hMem := mem_gaugedBlock_of_survives position hConnected hGenus hValid label hOldWall
      (by rw [hLabel, W2MkkGraphData.sourceEdge_self]; exact hOldSurv)
    have hIn := gaugedBlock_subset_endSheets position label hMem
    rw [hLabelSide, hOldSheet] at hIn
    exact hu hIn
  · rw [newSourceEdge_repr (C) s]
    have hSheet : ((C).newSourceEdge s).1.2 = u := hEq
    rw [hSheet]
    exact Finset.mem_singleton_self _

include hValid hGenusC in
/-- **The extra new-edge classes dangle (general form).**  A new occurrence at a sheet
of the anchor block outside `A_b` (for either side `b`) is dangling. -/
theorem newSourceEdge_isDangling_of_not_mem (b : Bool) {u : Fin degree}
    (hu : u ∉ endSheets position b) (hWall : (data.vertexPartition wall).Rel anchor.1 u) :
    IsDangling (C).datum ((C).newSourceEdge u) := by
  classical
  by_contra hSurv
  have hIncident := newSourceEdge_incident (C) b u
  have hCard := Finset.card_le_card
    (nonDanglingIncident_singleton_subset position hConnected hGenus hNoGlue geometry hValid
      hGenusC b hu hWall)
  rw [card_nonDanglingIncident, Finset.card_singleton] at hCard
  have hNe := NonDanglingValency.nonDanglingValency_ne_one (C).datum
    ((C).datum_valid (position.datum_valid hValid)).1 (epv (C) b u)
  have hPos := ClassInjectivity.nonDanglingValency_ne_zero_of_incident (C).datum hSurv hIncident
  omega

include hValid hGenusC in
/-- The same, stated for the sheets of `A₋ \ A₊` and of `A₊ \ A₋`: their new occurrences
are dangling. -/
theorem newEdge_isDangling_off_bridge' (sheet : Fin degree)
    (hSheet : sheet ∈ position.split.minusSheets \ position.split.plusSheets ∨
      sheet ∈ position.split.plusSheets \ position.split.minusSheets) :
    IsDangling (C).datum ((C).newSourceEdge sheet) := by
  have hNot : side ≠ !side := by cases side <;> simp
  rcases hSheet with h | h
  · obtain ⟨hMinus, hPlus⟩ := Finset.mem_sdiff.mp h
    apply newSourceEdge_isDangling_of_not_mem position hConnected hGenus hNoGlue geometry hValid
      hGenusC (!side)
    · unfold endSheets
      rw [ite_eq_right (Ne.symm hNot)]
      exact hPlus
    · exact ((data.vertexPartition wall).mem_block_iff _ _).mp (position.split.minus_subset hMinus)
  · obtain ⟨hPlus, hMinus⟩ := Finset.mem_sdiff.mp h
    apply newSourceEdge_isDangling_of_not_mem position hConnected hGenus hNoGlue geometry hValid
      hGenusC side
    · unfold endSheets
      rw [ite_eq_left rfl]
      exact hMinus
    · exact ((data.vertexPartition wall).mem_block_iff _ _).mp (position.split.plus_subset hPlus)

include hValid hGenusC in
/-- **The surviving star at the endpoint class of the bridge** on side `b`:
the bridge and the two survivors of the branches the pairing assigns to `b`. -/
theorem nonDanglingIncident_bridge_subset (b : Bool) :
    nonDanglingIncident (C).datum (epv (C) b position.split.bridge) ⊆
      {(C).newSourceEdge position.split.bridge,
        (C).oldSourceEdge (survivorEdge position (firstLabel pairing b)),
        (C).oldSourceEdge (survivorEdge position (secondLabel pairing b))} := by
  classical
  intro f hf
  obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hf
  have hBridgeWall : (data.vertexPartition wall).Rel anchor.1 position.split.bridge :=
    ((data.vertexPartition wall).mem_block_iff _ _).mp
      (position.split.minus_subset position.split.bridge_mem_minus)
  have hRel := rel_of_incident (C) b hInc
  rw [candidate_endpoint_rel_iff position hConnected hGenus hNoGlue geometry b hBridgeWall]
    at hRel
  have hIn : f.1.2 ∈ endSheets position b := (endpoint_rel_bridge_iff position b _).mp hRel
  have hWall : (data.vertexPartition wall).Rel anchor.1 f.1.2 :=
    ((data.vertexPartition wall).mem_block_iff _ _).mp (endSheets_subset_wall position b hIn)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases ResolutionPruning.sourceEdge_cases (C) f with ⟨old, rfl⟩ | ⟨s, rfl⟩
  · right
    obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old (C) b hInc
    obtain ⟨label, hLabel⟩ := star.exists_edge_eq old.1.1 hAt
    have hLabelSide : W4TargetPairings.Pairing.labelRight pairing label = b := by
      rw [← star.right_edge pairing label, hLabel]
      exact hSide
    have hOldSurv : ¬IsDangling position.datum old := fun h ↦ hSurv
      ((ResolutionPruning.isDangling_oldSourceEdge_iff (C) (position.datum_valid hValid)
        hGenusC old).mpr h)
    have hEq := eq_survivorEdge position hConnected hGenus hValid label old hLabel.symm hWall
      hOldSurv
    rcases eq_first_or_second pairing label with h | h <;> rw [hLabelSide] at h <;> subst h
    · exact Or.inl (congrArg (C).oldSourceEdge hEq)
    · exact Or.inr (congrArg (C).oldSourceEdge hEq)
  · left
    set u := ((C).newSourceEdge s).1.2 with hu
    rw [newSourceEdge_repr (C) s, ← hu]
    by_cases hOther : u ∈ endSheets position (!b)
    · have hBridge := mem_bridgeSheets_of position b hIn hOther
      apply (newSourceEdge_eq_of_rel (C) _).symm
      exact (candidate_newEdge_rel_iff position hConnected hGenus hNoGlue geometry hBridgeWall
        u).mpr ((position.split.newEdge_rel_bridge_iff u).mpr hBridge)
    · exfalso
      apply hSurv
      rw [newSourceEdge_repr (C) s, ← hu]
      exact newSourceEdge_isDangling_of_not_mem position hConnected hGenus hNoGlue geometry
        hValid hGenusC (!b) hOther hWall

include hValid hGenusC in
/-- **Trivalence at the anchor block.**  Every source vertex of the candidate
over the anchor block has surviving valency at most three. -/
theorem nonDanglingValency_anchor_le (b : Bool) {x : Fin degree}
    (hx : (data.vertexPartition wall).Rel anchor.1 x) :
    nonDanglingValency (C).datum (epv (C) b x) ≤ 3 := by
  classical
  rw [← card_nonDanglingIncident]
  by_cases hIn : x ∈ endSheets position b
  · rw [epv_eq_bridge position hConnected hGenus hNoGlue geometry b hIn]
    exact (Finset.card_le_card (nonDanglingIncident_bridge_subset position hConnected hGenus
      hNoGlue geometry hValid hGenusC b)).trans Finset.card_le_three
  · have h := Finset.card_le_card (nonDanglingIncident_singleton_subset position hConnected
      hGenus hNoGlue geometry hValid hGenusC b hIn hx)
    rw [Finset.card_singleton] at h
    omega

end Dangling

/-! ## 8.  Non-anchor wall blocks, for any candidate over the localized
canonical background

This is the non-anchor half of the `K = 0` census
(`NonTrivalentValencyFourRowEquiv`, `NonTrivalentValencyFourDescent`,
`NonTrivalentValencyFourRowEquivFinal` and `NonTrivalentValencyFourExit`),
restated for an arbitrary datum `gData` and an arbitrary candidate `C` whose
resolution is the localized canonical W4 resolution on every non-anchor block.
Nothing here depends on `K`. -/

section Ordinary

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {gData : GluingDatum target degree} {star : W4TargetPairings.FourStar target wall}
  {pairing : Fin 3} (C : BalancedGlobal.Candidate target degree gData wall)
  (hRight : C.right = star.right pairing)
  (pattern : Fin degree → W4Assembly.BlockPattern) (anchorSheet : Fin degree)
  (hRes : ∀ block, ¬(gData.vertexPartition wall).Rel anchorSheet block →
    C.resolution block = canonicalLocal gData star pattern pairing block)

local notation "coarse" => (gData.vertexPartition wall)
local notation "blockRes" => (W4Assembly.blockwiseResolution gData star pattern pairing)

include hRes in
theorem resolution_rel_of_not_anchor {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x)
    (y : Fin degree) :
    ((C.resolution ((coarse).repr x)).left.Rel x y ↔ (blockRes ((coarse).repr x)).left.Rel x y) ∧
      ((C.resolution ((coarse).repr x)).right.Rel x y ↔
        (blockRes ((coarse).repr x)).right.Rel x y) ∧
      ((C.resolution ((coarse).repr x)).newEdge.Rel x y ↔
        (blockRes ((coarse).repr x)).newEdge.Rel x y) := by
  have hReprNe : ¬(coarse).Rel anchorSheet ((coarse).repr x) := fun h ↦
    hb (h.trans ((coarse).rel_repr_right x).symm)
  have hOn := localize_onBlock_repr (coarse) ((coarse).repr x) (blockRes ((coarse).repr x)) x
    ((coarse).rel_repr_left x)
  rw [hRes _ hReprNe]
  unfold canonicalLocal localize
  refine ⟨?_, ?_, ?_⟩
  · refine Iff.trans (NonTrivalentValencyFourRowEquiv.pasteLeft_rel_iff _ _ _ x y) ?_
    rw [hOn]
  · refine Iff.trans (NonTrivalentValencyFourRowEquiv.pasteRight_rel_iff _ _ _ x y) ?_
    rw [hOn]
  · refine Iff.trans (NonTrivalentValencyFourRowEquiv.pasteNewEdge_rel_iff _ _ _ x y) ?_
    rw [hOn]

include hRes in
theorem candidate_endpoint_rel_block (b : Bool) {x : Fin degree}
    (hb : ¬(coarse).Rel anchorSheet x) (y : Fin degree) :
    (C.datum.vertexPartition (if b then freshVertex target else oldVertex target wall)).Rel x y ↔
      (if b then (blockRes ((coarse).repr x)).right
        else (blockRes ((coarse).repr x)).left).Rel x y := by
  rw [endpoint_rel_iff]
  obtain ⟨hl, hr, _⟩ := resolution_rel_of_not_anchor C pattern anchorSheet hRes hb y
  cases b
  · exact hl
  · exact hr

include hRes in
theorem candidate_newEdge_rel_block {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x)
    (y : Fin degree) :
    (LocalResolution.paste (coarse) C.resolution C.contracts).newEdge.Rel x y ↔
      (blockRes ((coarse).repr x)).newEdge.Rel x y := by
  rw [newEdge_rel_iff]
  exact (resolution_rel_of_not_anchor C pattern anchorSheet hRes hb y).2.2

omit C in
/-- The side of a non-anchor block whose endpoint retains the whole wall
block. -/
noncomputable def retSide (b : Fin degree) : Bool := by
  classical
  exact if (blockRes b).left = coarse then false else true

omit C in
theorem retSide_endpoint (b : Fin degree) :
    (if retSide (gData := gData) (star := star) (pairing := pairing) pattern b then
        (blockRes b).right else (blockRes b).left) = coarse := by
  classical
  by_cases hLeft : (blockRes b).left = coarse
  · have hR : retSide (gData := gData) (star := star) (pairing := pairing) pattern b = false := by
      unfold retSide
      rw [ite_eq_left hLeft]
    rw [hR]
    exact hLeft
  · have hR : retSide (gData := gData) (star := star) (pairing := pairing) pattern b = true := by
      unfold retSide
      rw [ite_eq_right hLeft]
    rw [hR]
    rcases NonTrivalentValencyFourRows.isStar_blockwiseResolution (data := gData) (star := star)
      pairing pattern b with ⟨hl, _⟩ | ⟨hr, _⟩
    · exact absurd hl hLeft
    · exact hr

omit C in
theorem retSide_other (b : Fin degree) :
    (if !retSide (gData := gData) (star := star) (pairing := pairing) pattern b then
        (blockRes b).right else (blockRes b).left) = (blockRes b).newEdge := by
  classical
  by_cases hLeft : (blockRes b).left = coarse
  · have hR : retSide (gData := gData) (star := star) (pairing := pairing) pattern b = false := by
      unfold retSide
      rw [ite_eq_left hLeft]
    rw [hR]
    rcases NonTrivalentValencyFourRows.isStar_blockwiseResolution (data := gData) (star := star)
      pairing pattern b with ⟨_, hn⟩ | ⟨hr, hn⟩
    · exact hn.symm
    · rw [hn, hLeft]
      exact hr
  · have hR : retSide (gData := gData) (star := star) (pairing := pairing) pattern b = true := by
      unfold retSide
      rw [ite_eq_right hLeft]
    rw [hR]
    rcases NonTrivalentValencyFourRows.isStar_blockwiseResolution (data := gData) (star := star)
      pairing pattern b with ⟨hl, _⟩ | ⟨_, hn⟩
    · exact absurd hl hLeft
    · exact hn.symm

local notation "rs" => (retSide (gData := gData) (star := star) (pairing := pairing) pattern)

omit C in
theorem blockRes_newEdge_refines (b : Fin degree) : (blockRes b).newEdge.Refines (coarse) :=
  (blockRes b).edge_refines_left.trans
    (W4Assembly.blockwiseResolution_contracts gData star pattern pairing b).left_refines

include hRes in
theorem fine_rel_of_incident {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x)
    {e : C.datum.SourceEdge}
    (hIncident : Incident C.datum e (epv C (!rs ((coarse).repr x)) x)) :
    (blockRes ((coarse).repr x)).newEdge.Rel x e.1.2 := by
  have h1 := rel_of_incident C _ hIncident
  rw [candidate_endpoint_rel_block C pattern anchorSheet hRes _ hb, retSide_other] at h1
  exact h1

include hRes in
theorem ret_rel_of_incident {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x)
    {e : C.datum.SourceEdge}
    (hIncident : Incident C.datum e (epv C (rs ((coarse).repr x)) x)) :
    (coarse).Rel x e.1.2 := by
  have h1 := rel_of_incident C _ hIncident
  rw [candidate_endpoint_rel_block C pattern anchorSheet hRes _ hb, retSide_endpoint] at h1
  exact h1

theorem newEdge_rel_repr (b : Bool) (s' : Fin degree) :
    (C.datum.vertexPartition (if b then freshVertex target else oldVertex target wall)).Rel s'
      ((LocalResolution.paste (coarse) C.resolution C.contracts).newEdge.repr s') := by
  rw [datum_vertexPartition_eq]
  cases b
  · exact (LocalResolution.pasteNewEdge_refines_left (coarse) C.resolution C.contracts).rel
      ((LocalResolution.paste (coarse) C.resolution C.contracts).newEdge.rel_repr_right s')
  · exact (LocalResolution.pasteNewEdge_refines_right (coarse) C.resolution C.contracts).rel
      ((LocalResolution.paste (coarse) C.resolution C.contracts).newEdge.rel_repr_right s')

include hRes in
/-- A new occurrence incident to the fine-side endpoint of a non-anchor block
is *the* new occurrence of that block's sheet. -/
theorem newSourceEdge_eq_of_incident_fine {x s' : Fin degree} (hb : ¬(coarse).Rel anchorSheet x)
    (hIncident : Incident C.datum (C.newSourceEdge s') (epv C (!rs ((coarse).repr x)) x)) :
    C.newSourceEdge s' = C.newSourceEdge x := by
  have hX := rel_of_incident C _ hIncident
  have hS := newEdge_rel_repr C (!rs ((coarse).repr x)) s'
  have hSX : (C.datum.vertexPartition
      (if !rs ((coarse).repr x) then freshVertex target else oldVertex target wall)).Rel s' x :=
    hS.trans hX.symm
  have hCoarse : (coarse).Rel s' x := (endpoint_refines C _).rel hSX
  have hbS : ¬(coarse).Rel anchorSheet s' := fun h ↦ hb (h.trans hCoarse)
  have hRepr : (coarse).repr s' = (coarse).repr x := hCoarse
  apply newSourceEdge_eq_of_rel C
  rw [candidate_newEdge_rel_block C pattern anchorSheet hRes hbS, hRepr]
  have := (candidate_endpoint_rel_block C pattern anchorSheet hRes
    (!rs ((coarse).repr x)) hbS x).mp hSX
  rw [hRepr, retSide_other] at this
  exact this

include hRight hRes in
/-- A new occurrence with no surviving old occurrence on its own fine class is
dangling. -/
theorem newSourceEdge_dangling_of_no_fine_survivor (hGValid : gData.Valid)
    (hGenusC : genus C.datum.sourceGraph = genus gData.sourceGraph)
    {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x)
    (hNone : ∀ old : gData.SourceEdge, ¬IsDangling gData old →
      old.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing old.1.1 = !rs ((coarse).repr x) →
      ¬(blockRes ((coarse).repr x)).newEdge.Rel x old.1.2) :
    IsDangling C.datum (C.newSourceEdge x) := by
  classical
  have hSubset : nonDanglingIncident C.datum (epv C (!rs ((coarse).repr x)) x) ⊆
      {C.newSourceEdge x} := by
    intro f hf
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    rcases ResolutionPruning.sourceEdge_cases C f with ⟨old, rfl⟩ | ⟨s', rfl⟩
    · exfalso
      obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old C _ hIncident
      rw [hRight] at hSide
      exact hNone old
        (fun h ↦ hSurvives
          ((ResolutionPruning.isDangling_oldSourceEdge_iff C hGValid hGenusC old).mpr h))
        hAt hSide (fine_rel_of_incident C pattern anchorSheet hRes hb hIncident)
    · rw [newSourceEdge_eq_of_incident_fine C pattern anchorSheet hRes hb hIncident]
      exact Finset.mem_singleton_self _
  by_contra hSurvives
  have hIncident := newSourceEdge_incident C (!rs ((coarse).repr x)) x
  have hCard := Finset.card_le_card hSubset
  rw [card_nonDanglingIncident, Finset.card_singleton] at hCard
  have hNe := NonDanglingValency.nonDanglingValency_ne_one C.datum (C.datum_valid hGValid).1
    (epv C (!rs ((coarse).repr x)) x)
  have hPos := ClassInjectivity.nonDanglingValency_ne_zero_of_incident C.datum hSurvives hIncident
  omega

include hRight hRes in
/-- **The retaining-side dichotomy** at a non-anchor block. -/
theorem nonDanglingIncident_ret_dichotomy (hGValid : gData.Valid)
    (hGenusC : genus C.datum.sourceGraph = genus gData.sourceGraph)
    {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x)
    {f : C.datum.SourceEdge} (hSurv : ¬IsDangling C.datum f)
    (hIncident : Incident C.datum f (epv C (rs ((coarse).repr x)) x)) :
    (∃ old : gData.SourceEdge, ¬IsDangling gData old ∧
        old.1.1 ∈ GluingDatum.incidentEdges wall ∧
        star.right pairing old.1.1 = rs ((coarse).repr x) ∧
        (coarse).Rel x old.1.2 ∧ f = C.oldSourceEdge old) ∨
      (∃ old : gData.SourceEdge, ¬IsDangling gData old ∧
        old.1.1 ∈ GluingDatum.incidentEdges wall ∧
        star.right pairing old.1.1 = !rs ((coarse).repr x) ∧
        (coarse).Rel x old.1.2 ∧ f = C.newSourceEdge old.1.2) := by
  rcases ResolutionPruning.sourceEdge_cases C f with ⟨old, rfl⟩ | ⟨s', rfl⟩
  · left
    obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old C _ hIncident
    rw [hRight] at hSide
    exact ⟨old,
      (fun h ↦ hSurv ((ResolutionPruning.isDangling_oldSourceEdge_iff C hGValid hGenusC old).mpr h)),
      hAt, hSide, ret_rel_of_incident C pattern anchorSheet hRes hb hIncident, rfl⟩
  · right
    have hRelS : (coarse).Rel x s' := by
      have h1 := ret_rel_of_incident C pattern anchorSheet hRes hb hIncident
      have h2 := newEdge_rel_repr C (rs ((coarse).repr x)) s'
      have h3 : (coarse).Rel s'
          ((LocalResolution.paste (coarse) C.resolution C.contracts).newEdge.repr s') :=
        (endpoint_refines C _).rel h2
      exact h1.trans h3.symm
    have hbS : ¬(coarse).Rel anchorSheet s' := fun h ↦ hb (h.trans hRelS.symm)
    have hReprS : (coarse).repr s' = (coarse).repr x := hRelS.symm
    by_contra hNo
    simp only [not_exists, not_and] at hNo
    apply hSurv
    apply newSourceEdge_dangling_of_no_fine_survivor C hRight pattern anchorSheet hRes hGValid
      hGenusC hbS
    intro old hOldSurv hAt hSide hRelNew
    rw [hReprS] at hSide hRelNew
    have hPaste : (LocalResolution.paste (coarse) C.resolution C.contracts).newEdge.Rel s'
        old.1.2 := by
      rw [candidate_newEdge_rel_block C pattern anchorSheet hRes hbS, hReprS]
      exact hRelNew
    have hCoarse : (coarse).Rel x old.1.2 :=
      hRelS.trans ((blockRes_newEdge_refines pattern ((coarse).repr x)).rel
        (by rw [← hReprS]; exact
          (candidate_newEdge_rel_block C pattern anchorSheet hRes hbS old.1.2).mp hPaste))
    exact hNo old hOldSurv hAt hSide hCoarse (newSourceEdge_eq_of_rel C hPaste)

include hRight hRes in
/-- The fine-side endpoint census of a non-anchor block. -/
theorem nonDanglingIncident_fine_cases (hGValid : gData.Valid)
    (hGenusC : genus C.datum.sourceGraph = genus gData.sourceGraph)
    {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x)
    {f : C.datum.SourceEdge} (hSurv : ¬IsDangling C.datum f)
    (hIncident : Incident C.datum f (epv C (!rs ((coarse).repr x)) x)) :
    f = C.newSourceEdge x ∨
      ∃ old : gData.SourceEdge, ¬IsDangling gData old ∧
        old.1.1 ∈ GluingDatum.incidentEdges wall ∧
        star.right pairing old.1.1 = !rs ((coarse).repr x) ∧
        (blockRes ((coarse).repr x)).newEdge.Rel x old.1.2 ∧
        f = C.oldSourceEdge old := by
  rcases ResolutionPruning.sourceEdge_cases C f with ⟨old, rfl⟩ | ⟨s', rfl⟩
  · right
    obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old C _ hIncident
    rw [hRight] at hSide
    exact ⟨old,
      (fun h ↦ hSurv ((ResolutionPruning.isDangling_oldSourceEdge_iff C hGValid hGenusC old).mpr h)),
      hAt, hSide, fine_rel_of_incident C pattern anchorSheet hRes hb hIncident, rfl⟩
  · left
    exact newSourceEdge_eq_of_incident_fine C pattern anchorSheet hRes hb hIncident

/-! ### The surviving star of a wall block of `gData` -/

omit C in
theorem mem_nonDanglingIncident_block {y : Fin degree} {w : gData.SourceEdge}
    (hSurv : ¬IsDangling gData w) (hAt : w.1.1 ∈ GluingDatum.incidentEdges wall)
    (hRel : (coarse).Rel y w.1.2) :
    w ∈ nonDanglingIncident gData
      (WallBlock.sourceVertex gData wall (WallBlock.ofSheet gData wall y)) := by
  refine (mem_nonDanglingIncident _ _ _).mpr ⟨hSurv, ?_⟩
  refine (incident_wallBlock_sourceVertex_iff gData _ w).mpr ⟨hAt, ?_⟩
  exact (WallBlock.ofSheet_eq_iff_rel gData wall _ w.1.2).mpr
    (((coarse).rel_repr_left y).trans hRel)

omit C in
theorem eq_of_same_target {y : Fin degree}
    (hInjY : NonDanglingStarInjective gData star (WallBlock.ofSheet gData wall y))
    {o₁ o₂ : gData.SourceEdge} (h₁ : ¬IsDangling gData o₁) (h₂ : ¬IsDangling gData o₂)
    (hAt₁ : o₁.1.1 ∈ GluingDatum.incidentEdges wall)
    (hRel₁ : (coarse).Rel y o₁.1.2) (hRel₂ : (coarse).Rel y o₂.1.2)
    (hTarget : o₁.1.1 = o₂.1.1) : o₁ = o₂ := by
  obtain ⟨label, hLabel⟩ := star.exists_edge_eq o₁.1.1 hAt₁
  exact hInjY.unique label o₁ o₂
    ((WallBlock.ofSheet_eq_iff_rel gData wall _ o₁.1.2).mpr
      (((coarse).rel_repr_left y).trans hRel₁))
    ((WallBlock.ofSheet_eq_iff_rel gData wall _ o₂.1.2).mpr
      (((coarse).rel_repr_left y).trans hRel₂))
    hLabel.symm (hTarget.symm.trans hLabel.symm) h₁ h₂

omit C in
theorem eq_of_three_on_side {y : Fin degree} {sideValue : Bool}
    (hInjY : NonDanglingStarInjective gData star (WallBlock.ofSheet gData wall y))
    (o₁ o₂ o₃ : gData.SourceEdge)
    (h₁ : ¬IsDangling gData o₁) (h₂ : ¬IsDangling gData o₂) (h₃ : ¬IsDangling gData o₃)
    (hAt₁ : o₁.1.1 ∈ GluingDatum.incidentEdges wall)
    (hAt₂ : o₂.1.1 ∈ GluingDatum.incidentEdges wall)
    (hAt₃ : o₃.1.1 ∈ GluingDatum.incidentEdges wall)
    (hRel₁ : (coarse).Rel y o₁.1.2) (hRel₂ : (coarse).Rel y o₂.1.2)
    (hRel₃ : (coarse).Rel y o₃.1.2)
    (hSide₁ : star.right pairing o₁.1.1 = sideValue)
    (hSide₂ : star.right pairing o₂.1.1 = sideValue)
    (hSide₃ : star.right pairing o₃.1.1 = sideValue) :
    o₁ = o₂ ∨ o₁ = o₃ ∨ o₂ = o₃ := by
  classical
  obtain ⟨l₁, hl₁⟩ := star.exists_edge_eq o₁.1.1 hAt₁
  obtain ⟨l₂, hl₂⟩ := star.exists_edge_eq o₂.1.1 hAt₂
  obtain ⟨l₃, hl₃⟩ := star.exists_edge_eq o₃.1.1 hAt₃
  by_cases h₁₂ : l₁ = l₂
  · exact Or.inl (eq_of_same_target hInjY h₁ h₂ hAt₁ hRel₁ hRel₂ (by rw [← hl₁, ← hl₂, h₁₂]))
  by_cases h₁₃ : l₁ = l₃
  · exact Or.inr (Or.inl (eq_of_same_target hInjY h₁ h₃ hAt₁ hRel₁ hRel₃
      (by rw [← hl₁, ← hl₃, h₁₃])))
  by_cases h₂₃ : l₂ = l₃
  · exact Or.inr (Or.inr (eq_of_same_target hInjY h₂ h₃ hAt₂ hRel₂ hRel₃
      (by rw [← hl₂, ← hl₃, h₂₃])))
  exfalso
  have hMem : ∀ l ∈ ({l₁, l₂, l₃} : Finset (Fin 4)),
      l ∈ W4TargetPairings.Pairing.labelsOnSide pairing sideValue := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rw [W4TargetPairings.Pairing.mem_labelsOnSide]
    rcases hl with rfl | rfl | rfl
    · rw [← W4TargetPairings.FourStar.right_edge star pairing l, hl₁]
      exact hSide₁
    · rw [← W4TargetPairings.FourStar.right_edge star pairing l, hl₂]
      exact hSide₂
    · rw [← W4TargetPairings.FourStar.right_edge star pairing l, hl₃]
      exact hSide₃
  have hCard : ({l₁, l₂, l₃} : Finset (Fin 4)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h₁₂, h₁₃]),
      Finset.card_insert_of_notMem (by simp [h₂₃]), Finset.card_singleton]
  have hLe := Finset.card_le_card (Finset.subset_iff.mpr hMem)
  rw [hCard, W4TargetPairings.Pairing.card_labelsOnSide] at hLe
  omega

omit C in
/-- At most two surviving occurrences of a wall block sit on one side of the
prescribed pairing. -/
theorem card_side_le_two {x : Fin degree}
    (hInj : NonDanglingStarInjective gData star (WallBlock.ofSheet gData wall x))
    (sideValue : Bool) :
    ((nonDanglingIncident gData
        (WallBlock.sourceVertex gData wall (WallBlock.ofSheet gData wall x))).filter
      (fun old ↦ star.right pairing old.1.1 = sideValue)).card ≤ 2 := by
  classical
  by_contra hBig
  have hBig' : 3 ≤ ((nonDanglingIncident gData
        (WallBlock.sourceVertex gData wall (WallBlock.ofSheet gData wall x))).filter
      (fun old ↦ star.right pairing old.1.1 = sideValue)).card := by omega
  obtain ⟨t, hSub, hCard⟩ := Finset.exists_subset_card_eq hBig'
  obtain ⟨o₁, o₂, o₃, h₁₂, h₁₃, h₂₃, rfl⟩ := Finset.card_eq_three.mp hCard
  have hMem : ∀ o ∈ ({o₁, o₂, o₃} : Finset gData.SourceEdge),
      (¬IsDangling gData o ∧ o.1.1 ∈ GluingDatum.incidentEdges wall ∧
        (coarse).Rel x o.1.2) ∧ star.right pairing o.1.1 = sideValue := by
    intro o ho
    obtain ⟨hIncFilter, hSideO⟩ := Finset.mem_filter.mp (hSub ho)
    obtain ⟨hSurvO, hIncO⟩ := (mem_nonDanglingIncident _ _ _).mp hIncFilter
    obtain ⟨hAtO, hBlockO⟩ := (incident_wallBlock_sourceVertex_iff gData _ o).mp hIncO
    refine ⟨⟨hSurvO, hAtO, ?_⟩, hSideO⟩
    have hRepr : (coarse).repr o.1.2 = (coarse).repr x := congrArg Subtype.val hBlockO
    exact hRepr.symm
  obtain ⟨⟨hS₁, hA₁, hR₁⟩, hD₁⟩ := hMem o₁ (by simp)
  obtain ⟨⟨hS₂, hA₂, hR₂⟩, hD₂⟩ := hMem o₂ (by simp)
  obtain ⟨⟨hS₃, hA₃, hR₃⟩, hD₃⟩ := hMem o₃ (by simp)
  rcases eq_of_three_on_side (pairing := pairing) hInj o₁ o₂ o₃ hS₁ hS₂ hS₃ hA₁ hA₂ hA₃ hR₁ hR₂
    hR₃ hD₁ hD₂ hD₃ with h | h | h
  · exact h₁₂ h
  · exact h₁₃ h
  · exact h₂₃ h

include hRight hRes in
/-- **The retaining endpoint of a non-anchor block is trivalent at most.** -/
theorem nonDanglingValency_ret_le (hGValid : gData.Valid)
    (hGenusC : genus C.datum.sourceGraph = genus gData.sourceGraph)
    {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x)
    (hVal : nonDanglingValency gData
      (WallBlock.sourceVertex gData wall (WallBlock.ofSheet gData wall x)) ≤ 3) :
    nonDanglingValency C.datum (epv C (rs ((coarse).repr x)) x) ≤ 3 := by
  classical
  have hSub : nonDanglingIncident C.datum (epv C (rs ((coarse).repr x)) x) ⊆
      (nonDanglingIncident gData
          (WallBlock.sourceVertex gData wall (WallBlock.ofSheet gData wall x))).image
        (fun old ↦ if star.right pairing old.1.1 = rs ((coarse).repr x) then
          C.oldSourceEdge old else C.newSourceEdge old.1.2) := by
    intro f hf
    obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    rcases nonDanglingIncident_ret_dichotomy C hRight pattern anchorSheet hRes hGValid hGenusC hb
      hSurv hInc with
      ⟨old, hOldSurv, hAt, hSide, hRel, rfl⟩ | ⟨old, hOldSurv, hAt, hSide, hRel, rfl⟩
    · refine Finset.mem_image.mpr ⟨old, mem_nonDanglingIncident_block hOldSurv hAt hRel, ?_⟩
      rw [ite_eq_left hSide]
    · refine Finset.mem_image.mpr ⟨old, mem_nonDanglingIncident_block hOldSurv hAt hRel, ?_⟩
      rw [ite_eq_right (by rw [hSide]; exact Bool.not_ne_self _)]
  rw [← card_nonDanglingIncident]
  refine le_trans (Finset.card_le_card hSub) (le_trans Finset.card_image_le ?_)
  rw [card_nonDanglingIncident]
  exact hVal

-- Measured 2026-10-07 on Lean v4.35.0-rc4: fails at the default 200000,
-- passes at 300000.  The bound below is ~2x that, so a regression errors.
include hRight hRes in
set_option maxHeartbeats 600000 in
/-- **A fine endpoint of a non-anchor block is trivalent at most.** -/
theorem nonDanglingValency_fine_le (hGValid : gData.Valid)
    (hGenusC : genus C.datum.sourceGraph = genus gData.sourceGraph)
    {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x)
    (hInj : NonDanglingStarInjective gData star (WallBlock.ofSheet gData wall x)) :
    nonDanglingValency C.datum (epv C (!rs ((coarse).repr x)) x) ≤ 3 := by
  classical
  have hSub : nonDanglingIncident C.datum (epv C (!rs ((coarse).repr x)) x) ⊆
      insert (C.newSourceEdge x)
        (((nonDanglingIncident gData
          (WallBlock.sourceVertex gData wall (WallBlock.ofSheet gData wall x))).filter
          (fun old ↦ star.right pairing old.1.1 = !rs ((coarse).repr x))).image
          C.oldSourceEdge) := by
    intro f hf
    obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    rcases nonDanglingIncident_fine_cases C hRight pattern anchorSheet hRes hGValid hGenusC hb hSurv
      hInc with hNew | ⟨old, hOldSurv, hAt, hSide, hRel, rfl⟩
    · rw [hNew]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨old,
        Finset.mem_filter.mpr ⟨?_, hSide⟩, rfl⟩)
      exact mem_nonDanglingIncident_block hOldSurv hAt
        ((blockRes_newEdge_refines pattern _).rel hRel)
  rw [← card_nonDanglingIncident]
  refine le_trans (Finset.card_le_card hSub) ?_
  have hTwo := le_trans (Finset.card_image_le
    (s := (nonDanglingIncident gData
          (WallBlock.sourceVertex gData wall (WallBlock.ofSheet gData wall x))).filter
      (fun old ↦ star.right pairing old.1.1 = !rs ((coarse).repr x)))
    (f := C.oldSourceEdge)) (card_side_le_two (pairing := pairing) hInj (!rs ((coarse).repr x)))
  have hIns := Finset.card_insert_le (C.newSourceEdge x)
    (((nonDanglingIncident gData
          (WallBlock.sourceVertex gData wall (WallBlock.ofSheet gData wall x))).filter
      (fun old ↦ star.right pairing old.1.1 = !rs ((coarse).repr x))).image C.oldSourceEdge)
  omega

include hRight hRes in
/-- **Both endpoint vertices of a non-anchor wall block are trivalent at
most.** -/
theorem nonDanglingValency_block_le (hGValid : gData.Valid)
    (hGenusC : genus C.datum.sourceGraph = genus gData.sourceGraph)
    (b : Bool) {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x)
    (hVal : nonDanglingValency gData
      (WallBlock.sourceVertex gData wall (WallBlock.ofSheet gData wall x)) ≤ 3)
    (hInj : NonDanglingStarInjective gData star (WallBlock.ofSheet gData wall x)) :
    nonDanglingValency C.datum (epv C b x) ≤ 3 := by
  by_cases hT : b = rs ((coarse).repr x)
  · rw [hT]
    exact nonDanglingValency_ret_le C hRight pattern anchorSheet hRes hGValid hGenusC hb hVal
  · have hb' : b = !rs ((coarse).repr x) := by
      cases b <;> cases hr : rs ((coarse).repr x) <;> simp_all
    rw [hb']
    exact nonDanglingValency_fine_le C hRight pattern anchorSheet hRes hGValid hGenusC hb hInj

end Ordinary

/-! ## 9.  Trivalence of the general-`K` candidate -/

section Trivalence

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : W4TargetPairings.FourStar target wall}
  {anchor : W4Assembly.WallBlock data wall}
  {source : FourBranchAnchor data star anchor} {pairing : Fin 3} {side : Bool}
  (position : Position source pairing side)
  (profile : NonTrivalentValencyFourBackground.OrdinaryBlockProfile data star anchor.1)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
  (geometry : PairingBackground position.datum star pairing anchor.1) (hValid : data.Valid)
  (hBg : ∀ block, ¬(position.datum.vertexPartition wall).Rel anchor.1 block →
    geometry.resolution block = canonicalLocal position.datum star profile.pattern pairing block)

local notation "C" => (position.candidate hConnected hGenus hNoGlue geometry)

include hValid in
theorem datum_valency_block (y : Fin degree) :
    nonDanglingValency position.datum
        (WallBlock.sourceVertex position.datum wall (WallBlock.ofSheet position.datum wall y)) =
      nonDanglingValency data (WallBlock.sourceVertex data wall (WallBlock.ofSheet data wall y)) := by
  show nonDanglingValency position.datum
      (position.datum.sourceEndpoint wall ((position.datum.vertexPartition wall).repr y)) =
    nonDanglingValency data (data.sourceEndpoint wall ((data.vertexPartition wall).repr y))
  rw [position.datum_vertexPartition_wall]
  exact datum_nonDanglingValency_endpoint position hValid _

theorem eq_epv (C' : BalancedGlobal.Candidate target degree position.datum wall) (b : Bool)
    (v : C'.datum.SourceVertex)
    (hv : v.1.1 = (if b then freshVertex target else oldVertex target wall)) :
    epv C' b v.1.2 = v :=
  (C'.datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨hv.symm, rfl⟩

include hBg hValid in
/-- **Trivalence (general form).**  The general-`K` candidate over the localized
canonical background is trivalent, given the incoming census:
* trivalence of the incoming datum away from the wall vertex;
* target-direction injectivity at every wall block;
* surviving valency at most three at every non-anchor wall block. -/
theorem candidate_trivalent_of
    (hAway : ∀ w : data.SourceVertex, w.1.1 ≠ wall → nonDanglingValency data w ≤ 3)
    (hInj : ∀ y, NonDanglingStarInjective data star (WallBlock.ofSheet data wall y))
    (hVal : ∀ y, ¬(data.vertexPartition wall).Rel anchor.1 y →
      nonDanglingValency data (WallBlock.sourceVertex data wall (WallBlock.ofSheet data wall y)) ≤ 3)
    (v : (C).datum.SourceVertex) :
    nonDanglingValency (C).datum v ≤ 3 := by
  classical
  have hGenusC := candidate_sourceGenus_of_local position profile hConnected hGenus hNoGlue
    geometry hBg
  have hDV := position.datum_valid hValid
  have hWallCase : ∀ b : Bool,
      v.1.1 = (if b then freshVertex target else oldVertex target wall) →
      nonDanglingValency (C).datum v ≤ 3 := by
    intro b hv
    rw [← eq_epv position (C) b v hv]
    by_cases hAnchorRel : (data.vertexPartition wall).Rel anchor.1 v.1.2
    · exact nonDanglingValency_anchor_le position hConnected hGenus hNoGlue geometry hValid
        hGenusC b hAnchorRel
    · have hb : ¬(position.datum.vertexPartition wall).Rel anchor.1 v.1.2 := by
        rwa [position.datum_vertexPartition_wall]
      apply nonDanglingValency_block_le (C) (candidate_right position hConnected hGenus hNoGlue
        geometry) profile.pattern anchor.1
        (fun block hBlock ↦ (candidate_resolution_of_not_rel position hConnected hGenus hNoGlue
          geometry block hBlock).trans (hBg block hBlock)) hDV hGenusC b hb
      · rw [datum_valency_block position hValid]
        exact hVal _ hAnchorRel
      · exact datum_starInjective position hValid _ (hInj _)
  rcases hcase : (v.1.1 : TargetExpansion.Vertex target) with place | u
  · by_cases hIsWall : place = wall
    · exact hWallCase false (by rw [hcase, hIsWall]; rfl)
    · obtain ⟨old, hOld, hRet⟩ := ResolutionAwayFromWall.exists_retainedVertex_of_target
        (C) v place hIsWall hcase
      rw [← hRet, ResolutionAwayFromWall.nonDanglingValency_retainedVertex (C) hDV hGenusC old
        (by rw [hOld]; exact hIsWall)]
      exact datum_valency_away position hValid hAway old (by rw [hOld]; exact hIsWall)
  · exact hWallCase true (by rw [hcase]; cases u; rfl)

end Trivalence

/-! ## 10.  The retained-row descent at non-anchor blocks (for `HasPathEnds`)

Generic ports of `NonTrivalentValencyFourRowEquiv` (unique fine survivors),
`NonTrivalentValencyFourDescent` and `NonTrivalentValencyFourRowDictionary`
(the four descent cases). -/

section Descent

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {gData : GluingDatum target degree} {star : W4TargetPairings.FourStar target wall}
  {pairing : Fin 3} (C : BalancedGlobal.Candidate target degree gData wall)
  (hRight : C.right = star.right pairing)
  (pattern : Fin degree → W4Assembly.BlockPattern) (anchorSheet : Fin degree)
  (hRes : ∀ block, ¬(gData.vertexPartition wall).Rel anchorSheet block →
    C.resolution block = canonicalLocal gData star pattern pairing block)
  (hGValid : gData.Valid)
  (hGenusC : genus C.datum.sourceGraph = genus gData.sourceGraph)

local notation "coarse" => (gData.vertexPartition wall)
local notation "blockRes" => (W4Assembly.blockwiseResolution gData star pattern pairing)
local notation "rs" => (retSide (gData := gData) (star := star) (pairing := pairing) pattern)

omit C in
theorem nonDanglingValency_eq_two_of_pair' {data : GluingDatum target degree}
    {v : data.SourceVertex} {a b : data.SourceEdge} (hNe : a ≠ b)
    (hSubset : nonDanglingIncident data v ⊆ {a, b})
    (ha : a ∈ nonDanglingIncident data v) (hb : b ∈ nonDanglingIncident data v) :
    nonDanglingValency data v = 2 := by
  classical
  have hEq : nonDanglingIncident data v = {a, b} := by
    refine Finset.Subset.antisymm hSubset ?_
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ha
    · exact hb
  rw [← card_nonDanglingIncident, hEq, Finset.card_insert_of_notMem (by simpa using hNe),
    Finset.card_singleton]

include hGValid in
theorem isDangling_of_subset_singleton {v : C.datum.SourceVertex} {a : C.datum.SourceEdge}
    (hSubset : nonDanglingIncident C.datum v ⊆ {a}) (hIncident : Incident C.datum a v) :
    IsDangling C.datum a := by
  classical
  by_contra hSurv
  have hCard := Finset.card_le_card hSubset
  rw [card_nonDanglingIncident, Finset.card_singleton] at hCard
  have hNe := NonDanglingValency.nonDanglingValency_ne_one C.datum (C.datum_valid hGValid).1 v
  have hPos := ClassInjectivity.nonDanglingValency_ne_zero_of_incident C.datum hSurv hIncident
  omega

omit C in
theorem incident_sourceEndpoint_iff (x : Fin degree) (z : gData.SourceEdge) :
    Incident gData z (gData.sourceEndpoint wall x) ↔
      z.1.1 ∈ GluingDatum.incidentEdges wall ∧ (coarse).Rel x z.1.2 := by
  rw [incident_iff_target_mem_and_rel]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, ((coarse).rel_repr_right x).trans h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (((coarse).rel_repr_right x).symm).trans h2⟩

include hRes in
theorem epv_ret_eq {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x) {y : Fin degree}
    (hRel : (coarse).Rel x y) :
    epv C (rs ((coarse).repr x)) y = epv C (rs ((coarse).repr x)) x := by
  apply (epv_eq_of_rel C _ _).symm
  exact (candidate_endpoint_rel_block C pattern anchorSheet hRes _ hb y).mpr
    (by rw [retSide_endpoint]; exact hRel)

include hRes in
theorem epv_fine_eq {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x) {y : Fin degree}
    (hRel : (blockRes ((coarse).repr x)).newEdge.Rel x y) :
    epv C (!rs ((coarse).repr x)) y = epv C (!rs ((coarse).repr x)) x := by
  apply (epv_eq_of_rel C _ _).symm
  exact (candidate_endpoint_rel_block C pattern anchorSheet hRes _ hb y).mpr
    (by rw [retSide_other]; exact hRel)

include hRes in
theorem newSourceEdge_incident_ret {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x)
    {y : Fin degree} (hRel : (coarse).Rel x y) :
    Incident C.datum (C.newSourceEdge y) (epv C (rs ((coarse).repr x)) x) := by
  have h := newSourceEdge_incident C (rs ((coarse).repr x)) y
  rwa [epv_ret_eq C pattern anchorSheet hRes hb hRel] at h

include hRight hRes in
theorem oldSourceEdge_incident_ret {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x)
    {z : gData.SourceEdge} (hzAt : z.1.1 ∈ GluingDatum.incidentEdges wall)
    (hzRel : (coarse).Rel x z.1.2) (hzSide : star.right pairing z.1.1 = rs ((coarse).repr x)) :
    Incident C.datum (C.oldSourceEdge z) (epv C (rs ((coarse).repr x)) x) := by
  have h := oldSourceEdge_incident C z.1.1 hzAt (rs ((coarse).repr x))
    (by rw [hRight]; exact hzSide) z.1.2
  rwa [W2MkkGraphData.sourceEdge_self, epv_ret_eq C pattern anchorSheet hRes hb hzRel] at h

include hRight hRes in
theorem oldSourceEdge_incident_fine {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x)
    {z : gData.SourceEdge} (hzAt : z.1.1 ∈ GluingDatum.incidentEdges wall)
    (hzRel : (blockRes ((coarse).repr x)).newEdge.Rel x z.1.2)
    (hzSide : star.right pairing z.1.1 = !rs ((coarse).repr x)) :
    Incident C.datum (C.oldSourceEdge z) (epv C (!rs ((coarse).repr x)) x) := by
  have h := oldSourceEdge_incident C z.1.1 hzAt (!rs ((coarse).repr x))
    (by rw [hRight]; exact hzSide) z.1.2
  rwa [W2MkkGraphData.sourceEdge_self, epv_fine_eq C pattern anchorSheet hRes hb hzRel] at h

include hRight hRes hGValid hGenusC in
/-- A new occurrence whose fine class carries exactly one surviving old
occurrence survives, and the fine endpoint is divalent. -/
theorem newSourceEdge_survives_of_unique_fine_survivor {x : Fin degree}
    (hb : ¬(coarse).Rel anchorSheet x)
    {old : gData.SourceEdge} (hOldSurv : ¬IsDangling gData old)
    (hAt : old.1.1 ∈ GluingDatum.incidentEdges wall)
    (hSide : star.right pairing old.1.1 = !rs ((coarse).repr x))
    (hRel : (blockRes ((coarse).repr x)).newEdge.Rel x old.1.2)
    (hUnique : ∀ other : gData.SourceEdge, ¬IsDangling gData other →
      other.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing other.1.1 = !rs ((coarse).repr x) →
      (blockRes ((coarse).repr x)).newEdge.Rel x other.1.2 → other = old) :
    ¬IsDangling C.datum (C.newSourceEdge x) ∧
      nonDanglingValency C.datum (epv C (!rs ((coarse).repr x)) x) = 2 := by
  classical
  have hOldIncident := oldSourceEdge_incident_fine C hRight pattern anchorSheet hRes hb hAt hRel
    hSide
  have hOldMem : C.oldSourceEdge old ∈ nonDanglingIncident C.datum
      (epv C (!rs ((coarse).repr x)) x) :=
    (mem_nonDanglingIncident _ _ _).mpr
      ⟨ResolutionSurvival.not_isDangling_oldSourceEdge _ hGValid.1 _ hOldSurv, hOldIncident⟩
  have hNeNewOld : C.newSourceEdge x ≠ C.oldSourceEdge old := new_ne_old C x old
  have hSubset : nonDanglingIncident C.datum (epv C (!rs ((coarse).repr x)) x) ⊆
      {C.newSourceEdge x, C.oldSourceEdge old} := by
    intro f hf
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases nonDanglingIncident_fine_cases C hRight pattern anchorSheet hRes hGValid hGenusC hb
      hSurvives hIncident with hNew | ⟨other, hoS, hoAt, hoSide, hoRel, rfl⟩
    · exact Or.inl hNew
    · exact Or.inr (congrArg C.oldSourceEdge (hUnique other hoS hoAt hoSide hoRel))
  have hCardLe := Finset.card_le_card hSubset
  rw [card_nonDanglingIncident, Finset.card_insert_of_notMem (by simpa using hNeNewOld),
    Finset.card_singleton] at hCardLe
  have hPos := ClassInjectivity.nonDanglingValency_ne_zero_of_incident C.datum
    (ResolutionSurvival.not_isDangling_oldSourceEdge _ hGValid.1 _ hOldSurv) hOldIncident
  have hNe := NonDanglingValency.nonDanglingValency_ne_one C.datum (C.datum_valid hGValid).1
    (epv C (!rs ((coarse).repr x)) x)
  have hCard : nonDanglingValency C.datum (epv C (!rs ((coarse).repr x)) x) = 2 := by omega
  refine ⟨?_, hCard⟩
  have hEqSet : nonDanglingIncident C.datum (epv C (!rs ((coarse).repr x)) x) =
      {C.newSourceEdge x, C.oldSourceEdge old} := by
    refine Finset.eq_of_subset_of_card_le hSubset ?_
    rw [card_nonDanglingIncident, hCard, Finset.card_insert_of_notMem (by simpa using hNeNewOld),
      Finset.card_singleton]
  have hMem : C.newSourceEdge x ∈ nonDanglingIncident C.datum
      (epv C (!rs ((coarse).repr x)) x) := by
    rw [hEqSet]
    exact Finset.mem_insert_self _ _
  exact ((mem_nonDanglingIncident _ _ _).mp hMem).1

include hRight hRes hGValid hGenusC in
/-- The stable-row form: the new occurrence lies on the retained row of the
unique survivor of its fine class. -/
theorem stablePath_newSourceEdge_eq {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x)
    {old : gData.SourceEdge} (hOldSurv : ¬IsDangling gData old)
    (hAt : old.1.1 ∈ GluingDatum.incidentEdges wall)
    (hSide : star.right pairing old.1.1 = !rs ((coarse).repr x))
    (hRel : (blockRes ((coarse).repr x)).newEdge.Rel x old.1.2)
    (hUnique : ∀ other : gData.SourceEdge, ¬IsDangling gData other →
      other.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing other.1.1 = !rs ((coarse).repr x) →
      (blockRes ((coarse).repr x)).newEdge.Rel x other.1.2 → other = old) :
    NonDanglingEdge.stablePath
        (⟨C.newSourceEdge x,
          (newSourceEdge_survives_of_unique_fine_survivor C hRight pattern anchorSheet hRes
            hGValid hGenusC hb hOldSurv hAt hSide hRel hUnique).1⟩ :
          NonDanglingEdge C.datum) =
      (ResolutionAwayFromWall.retainedEdge C hGValid.1 ⟨old, hOldSurv⟩).stablePath := by
  obtain ⟨_, hCard⟩ := newSourceEdge_survives_of_unique_fine_survivor C hRight pattern
    anchorSheet hRes hGValid hGenusC hb hOldSurv hAt hSide hRel hUnique
  apply stablePath_eq_of_consecutive
  refine ⟨?_, epv C (!rs ((coarse).repr x)) x, newSourceEdge_incident C _ x,
    oldSourceEdge_incident_fine C hRight pattern anchorSheet hRes hb hAt hRel hSide, hCard⟩
  intro hEq
  exact new_ne_old C x old (congrArg Subtype.val hEq)

omit C in
/-- The two survivors of a divalent wall block exhaust its surviving star. -/
theorem eq_of_survivor (first second : NonDanglingEdge gData) (vertex : gData.SourceVertex)
    (hAt : vertex.1.1 = wall) (hNe : first ≠ second)
    (hFirst : Incident gData first.1 vertex) (hSecond : Incident gData second.1 vertex)
    (hValency : nonDanglingValency gData vertex = 2)
    (z : gData.SourceEdge) (hzS : ¬IsDangling gData z)
    (hzAt : z.1.1 ∈ GluingDatum.incidentEdges wall)
    (hzRel : (coarse).Rel vertex.1.2 z.1.2) : z = first.1 ∨ z = second.1 := by
  classical
  have hV : gData.sourceEndpoint wall vertex.1.2 = vertex :=
    (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
  rw [← hV] at hFirst hSecond hValency
  have hNeVal : first.1 ≠ second.1 := fun h ↦ hNe (Subtype.ext h)
  have hSub : ({first.1, second.1} : Finset gData.SourceEdge) ⊆
      nonDanglingIncident gData (gData.sourceEndpoint wall vertex.1.2) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (mem_nonDanglingIncident _ _ _).mpr ⟨first.2, hFirst⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr ⟨second.2, hSecond⟩
  have hCardPair : ({first.1, second.1} : Finset gData.SourceEdge).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hNeVal), Finset.card_singleton]
  have hEq := Finset.eq_of_subset_of_card_le hSub (by
    rw [card_nonDanglingIncident, hValency, hCardPair])
  have hzMem : z ∈ nonDanglingIncident gData (gData.sourceEndpoint wall vertex.1.2) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨hzS,
      (incident_sourceEndpoint_iff _ z).mpr ⟨hzAt, hzRel⟩⟩
  rw [← hEq] at hzMem
  simpa using hzMem

include hRight hRes hGValid hGenusC in
/-- **Descent, both survivors on the retaining side.** -/
theorem descent_of_both_retaining (first second : NonDanglingEdge gData)
    (vertex : gData.SourceVertex) (hAt : vertex.1.1 = wall) (hNe : first ≠ second)
    (hFirst : Incident gData first.1 vertex) (hSecond : Incident gData second.1 vertex)
    (hValency : nonDanglingValency gData vertex = 2)
    (hbAnchor : ¬(coarse).Rel anchorSheet vertex.1.2)
    (hsE : star.right pairing first.1.1.1 = rs ((coarse).repr vertex.1.2))
    (hsF : star.right pairing second.1.1.1 = rs ((coarse).repr vertex.1.2)) :
    (ResolutionAwayFromWall.retainedEdge C hGValid.1 first).stablePath =
      (ResolutionAwayFromWall.retainedEdge C hGValid.1 second).stablePath := by
  classical
  have hNeVal : first.1 ≠ second.1 := fun h ↦ hNe (Subtype.ext h)
  have hV : gData.sourceEndpoint wall vertex.1.2 = vertex :=
    (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
  obtain ⟨hAtE, hRelE⟩ := (incident_sourceEndpoint_iff _ first.1).mp (by rw [hV]; exact hFirst)
  obtain ⟨hAtF, hRelF⟩ := (incident_sourceEndpoint_iff _ second.1).mp (by rw [hV]; exact hSecond)
  have hIE := oldSourceEdge_incident_ret C hRight pattern anchorSheet hRes hbAnchor hAtE hRelE hsE
  have hIF := oldSourceEdge_incident_ret C hRight pattern anchorSheet hRes hbAnchor hAtF hRelF hsF
  have hSurvE : ¬IsDangling C.datum (C.oldSourceEdge first.1) :=
    ResolutionSurvival.not_isDangling_oldSourceEdge _ hGValid.1 _ first.2
  have hSurvF : ¬IsDangling C.datum (C.oldSourceEdge second.1) :=
    ResolutionSurvival.not_isDangling_oldSourceEdge _ hGValid.1 _ second.2
  have hNeAB : C.oldSourceEdge first.1 ≠ C.oldSourceEdge second.1 :=
    fun h ↦ hNeVal (ResolutionCut.oldSourceEdge_injective C h)
  refine stablePath_eq_of_consecutive ⟨fun h ↦ hNeAB (congrArg Subtype.val h),
    epv C (rs ((coarse).repr vertex.1.2)) vertex.1.2, hIE, hIF, ?_⟩
  refine nonDanglingValency_eq_two_of_pair' hNeAB ?_
    ((mem_nonDanglingIncident _ _ _).mpr ⟨hSurvE, hIE⟩)
    ((mem_nonDanglingIncident _ _ _).mpr ⟨hSurvF, hIF⟩)
  intro f hf
  obtain ⟨hfS, hfI⟩ := (mem_nonDanglingIncident _ _ _).mp hf
  rcases nonDanglingIncident_ret_dichotomy C hRight pattern anchorSheet hRes hGValid hGenusC
    hbAnchor hfS hfI with
    ⟨old, hoS, hoAt, hoSide, hoRel, rfl⟩ | ⟨old, hoS, hoAt, hoSide, hoRel, rfl⟩
  · rcases eq_of_survivor first second vertex hAt hNe hFirst hSecond hValency old hoS hoAt
      hoRel with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · exfalso
    rcases eq_of_survivor first second vertex hAt hNe hFirst hSecond hValency old hoS hoAt
      hoRel with rfl | rfl
    · exact absurd (hsE.symm.trans hoSide) (by simp)
    · exact absurd (hsF.symm.trans hoSide) (by simp)

include hRight hRes hGValid hGenusC in
/-- **Descent, one survivor on each side.** -/
theorem descent_of_mixed (first second : NonDanglingEdge gData)
    (vertex : gData.SourceVertex) (hAt : vertex.1.1 = wall) (hNe : first ≠ second)
    (hFirst : Incident gData first.1 vertex) (hSecond : Incident gData second.1 vertex)
    (hValency : nonDanglingValency gData vertex = 2)
    (hbAnchor : ¬(coarse).Rel anchorSheet vertex.1.2)
    (hsE : star.right pairing first.1.1.1 = rs ((coarse).repr vertex.1.2))
    (hsF : star.right pairing second.1.1.1 = !rs ((coarse).repr vertex.1.2)) :
    (ResolutionAwayFromWall.retainedEdge C hGValid.1 first).stablePath =
      (ResolutionAwayFromWall.retainedEdge C hGValid.1 second).stablePath := by
  classical
  have hV : gData.sourceEndpoint wall vertex.1.2 = vertex :=
    (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
  obtain ⟨hAtE, hRelE⟩ := (incident_sourceEndpoint_iff _ first.1).mp (by rw [hV]; exact hFirst)
  obtain ⟨hAtF, hRelF⟩ := (incident_sourceEndpoint_iff _ second.1).mp (by rw [hV]; exact hSecond)
  have hRepr : (coarse).repr second.1.1.2 = (coarse).repr vertex.1.2 := hRelF.symm
  have hbF : ¬(coarse).Rel anchorSheet second.1.1.2 := fun h ↦ hbAnchor (h.trans hRelF.symm)
  have hSideF : star.right pairing second.1.1.1 = !rs ((coarse).repr second.1.1.2) := by
    rw [hRepr]; exact hsF
  have hRelSelf : (blockRes ((coarse).repr second.1.1.2)).newEdge.Rel second.1.1.2
      second.1.1.2 := rfl
  have hUnique : ∀ other : gData.SourceEdge, ¬IsDangling gData other →
      other.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing other.1.1 = !rs ((coarse).repr second.1.1.2) →
      (blockRes ((coarse).repr second.1.1.2)).newEdge.Rel second.1.1.2 other.1.2 →
      other = second.1 := by
    intro other hoS hoAt hoSide hoRel
    have hCoarse : (coarse).Rel vertex.1.2 other.1.2 :=
      hRelF.trans ((blockRes_newEdge_refines pattern _).rel hoRel)
    rcases eq_of_survivor first second vertex hAt hNe hFirst hSecond hValency other hoS hoAt
      hCoarse with rfl | rfl
    · exfalso
      rw [hRepr] at hoSide
      exact absurd (hsE.symm.trans hoSide) (by simp)
    · rfl
  obtain ⟨hNewSurv, _⟩ := newSourceEdge_survives_of_unique_fine_survivor C hRight pattern
    anchorSheet hRes hGValid hGenusC hbF second.2 hAtF hSideF hRelSelf hUnique
  have hNewRow := stablePath_newSourceEdge_eq C hRight pattern anchorSheet hRes hGValid hGenusC
    hbF second.2 hAtF hSideF hRelSelf hUnique
  have hIncidA := oldSourceEdge_incident_ret C hRight pattern anchorSheet hRes hbAnchor hAtE
    hRelE hsE
  have hIncidB := newSourceEdge_incident_ret C pattern anchorSheet hRes hbAnchor hRelF
  have hSurvA : ¬IsDangling C.datum (C.oldSourceEdge first.1) :=
    ResolutionSurvival.not_isDangling_oldSourceEdge _ hGValid.1 _ first.2
  have hNeAB : C.oldSourceEdge first.1 ≠ C.newSourceEdge second.1.1.2 :=
    fun h ↦ new_ne_old C second.1.1.2 first.1 h.symm
  have hSubset : nonDanglingIncident C.datum (epv C (rs ((coarse).repr vertex.1.2)) vertex.1.2) ⊆
      {C.oldSourceEdge first.1, C.newSourceEdge second.1.1.2} := by
    intro f hf
    obtain ⟨hfS, hfI⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    rcases nonDanglingIncident_ret_dichotomy C hRight pattern anchorSheet hRes hGValid hGenusC
      hbAnchor hfS hfI with
      ⟨old, hoS, hoAt, hoSide, hoRel, rfl⟩ | ⟨old, hoS, hoAt, hoSide, hoRel, rfl⟩
    · rcases eq_of_survivor first second vertex hAt hNe hFirst hSecond hValency old hoS hoAt
        hoRel with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact absurd (hsF.symm.trans hoSide) (by simp)
    · rcases eq_of_survivor first second vertex hAt hNe hFirst hSecond hValency old hoS hoAt
        hoRel with rfl | rfl
      · exact absurd (hsE.symm.trans hoSide) (by simp)
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hValency2 := nonDanglingValency_eq_two_of_pair' hNeAB hSubset
    ((mem_nonDanglingIncident _ _ _).mpr ⟨hSurvA, hIncidA⟩)
    ((mem_nonDanglingIncident _ _ _).mpr ⟨hNewSurv, hIncidB⟩)
  refine Eq.trans (stablePath_eq_of_consecutive
    (⟨fun h ↦ hNeAB (congrArg Subtype.val h),
      epv C (rs ((coarse).repr vertex.1.2)) vertex.1.2, hIncidA, hIncidB, hValency2⟩ :
      Consecutive C.datum (ResolutionAwayFromWall.retainedEdge C hGValid.1 first)
        ⟨C.newSourceEdge second.1.1.2, hNewSurv⟩)) ?_
  exact hNewRow

include hRight hRes hGValid hGenusC in
/-- **Descent, both survivors on the fine side in one new-edge class.** -/
theorem descent_of_both_fine_same (first second : NonDanglingEdge gData)
    (vertex : gData.SourceVertex) (hAt : vertex.1.1 = wall) (hNe : first ≠ second)
    (hFirst : Incident gData first.1 vertex) (hSecond : Incident gData second.1 vertex)
    (hValency : nonDanglingValency gData vertex = 2)
    (hbAnchor : ¬(coarse).Rel anchorSheet vertex.1.2)
    (hsE : star.right pairing first.1.1.1 = !rs ((coarse).repr vertex.1.2))
    (hsF : star.right pairing second.1.1.1 = !rs ((coarse).repr vertex.1.2))
    (hClass : (blockRes ((coarse).repr vertex.1.2)).newEdge.Rel first.1.1.2 second.1.1.2) :
    (ResolutionAwayFromWall.retainedEdge C hGValid.1 first).stablePath =
      (ResolutionAwayFromWall.retainedEdge C hGValid.1 second).stablePath := by
  classical
  have hV : gData.sourceEndpoint wall vertex.1.2 = vertex :=
    (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
  obtain ⟨hAtE, hRelE⟩ := (incident_sourceEndpoint_iff _ first.1).mp (by rw [hV]; exact hFirst)
  obtain ⟨hAtF, hRelF⟩ := (incident_sourceEndpoint_iff _ second.1).mp (by rw [hV]; exact hSecond)
  have hReprE : (coarse).repr first.1.1.2 = (coarse).repr vertex.1.2 := hRelE.symm
  have hbE : ¬(coarse).Rel anchorSheet first.1.1.2 := fun h ↦ hbAnchor (h.trans hRelE.symm)
  have hsE' : star.right pairing first.1.1.1 = !rs ((coarse).repr first.1.1.2) := by
    rw [hReprE]; exact hsE
  have hsF' : star.right pairing second.1.1.1 = !rs ((coarse).repr first.1.1.2) := by
    rw [hReprE]; exact hsF
  have hClass' : (blockRes ((coarse).repr first.1.1.2)).newEdge.Rel first.1.1.2
      second.1.1.2 := by rw [hReprE]; exact hClass
  have hNewEq : C.newSourceEdge first.1.1.2 = C.newSourceEdge second.1.1.2 :=
    newSourceEdge_eq_of_rel C
      ((candidate_newEdge_rel_block C pattern anchorSheet hRes hbE second.1.1.2).mpr hClass')
  have hIncidNew := newSourceEdge_incident_ret C pattern anchorSheet hRes hbAnchor hRelE
  have hSubsetRet : nonDanglingIncident C.datum
      (epv C (rs ((coarse).repr vertex.1.2)) vertex.1.2) ⊆ {C.newSourceEdge first.1.1.2} := by
    intro f hf
    obtain ⟨hfS, hfI⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    rcases nonDanglingIncident_ret_dichotomy C hRight pattern anchorSheet hRes hGValid hGenusC
      hbAnchor hfS hfI with
      ⟨old, hoS, hoAt, hoSide, hoRel, rfl⟩ | ⟨old, hoS, hoAt, hoSide, hoRel, rfl⟩
    · rcases eq_of_survivor first second vertex hAt hNe hFirst hSecond hValency old hoS hoAt
        hoRel with rfl | rfl
      · exact absurd (hsE.symm.trans hoSide) (by simp)
      · exact absurd (hsF.symm.trans hoSide) (by simp)
    · rcases eq_of_survivor first second vertex hAt hNe hFirst hSecond hValency old hoS hoAt
        hoRel with rfl | rfl
      · exact Finset.mem_singleton_self _
      · rw [← hNewEq]
        exact Finset.mem_singleton_self _
  have hNewDangling := isDangling_of_subset_singleton C hGValid hSubsetRet hIncidNew
  have hIncidA : Incident C.datum (C.oldSourceEdge first.1)
      (epv C (!rs ((coarse).repr first.1.1.2)) first.1.1.2) :=
    oldSourceEdge_incident_fine C hRight pattern anchorSheet hRes hbE hAtE rfl hsE'
  have hIncidB : Incident C.datum (C.oldSourceEdge second.1)
      (epv C (!rs ((coarse).repr first.1.1.2)) first.1.1.2) :=
    oldSourceEdge_incident_fine C hRight pattern anchorSheet hRes hbE hAtF hClass' hsF'
  have hSurvA : ¬IsDangling C.datum (C.oldSourceEdge first.1) :=
    ResolutionSurvival.not_isDangling_oldSourceEdge _ hGValid.1 _ first.2
  have hSurvB : ¬IsDangling C.datum (C.oldSourceEdge second.1) :=
    ResolutionSurvival.not_isDangling_oldSourceEdge _ hGValid.1 _ second.2
  have hNeVal : first.1 ≠ second.1 := fun h ↦ hNe (Subtype.ext h)
  have hNeAB : C.oldSourceEdge first.1 ≠ C.oldSourceEdge second.1 :=
    fun h ↦ hNeVal (ResolutionCut.oldSourceEdge_injective C h)
  have hSubsetFine : nonDanglingIncident C.datum
      (epv C (!rs ((coarse).repr first.1.1.2)) first.1.1.2) ⊆
        {C.oldSourceEdge first.1, C.oldSourceEdge second.1} := by
    intro f hf
    obtain ⟨hfS, hfI⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    rcases nonDanglingIncident_fine_cases C hRight pattern anchorSheet hRes hGValid hGenusC hbE
      hfS hfI with hNew | ⟨old, hoS, hoAt, _, hoRel, rfl⟩
    · exact absurd (hNew ▸ hfS) (fun hBad ↦ hBad hNewDangling)
    · have hCoarse : (coarse).Rel vertex.1.2 old.1.2 :=
        hRelE.trans ((blockRes_newEdge_refines pattern _).rel hoRel)
      rcases eq_of_survivor first second vertex hAt hNe hFirst hSecond hValency old hoS hoAt
        hCoarse with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact stablePath_eq_of_consecutive
    ⟨fun h ↦ hNeAB (congrArg Subtype.val h),
      epv C (!rs ((coarse).repr first.1.1.2)) first.1.1.2, hIncidA, hIncidB,
      nonDanglingValency_eq_two_of_pair' hNeAB hSubsetFine
        ((mem_nonDanglingIncident _ _ _).mpr ⟨hSurvA, hIncidA⟩)
        ((mem_nonDanglingIncident _ _ _).mpr ⟨hSurvB, hIncidB⟩)⟩

include hRight hRes hGValid hGenusC in
/-- **Descent, both survivors on the fine side in two new-edge classes.** -/
theorem descent_of_both_fine_split (first second : NonDanglingEdge gData)
    (vertex : gData.SourceVertex) (hAt : vertex.1.1 = wall) (hNe : first ≠ second)
    (hFirst : Incident gData first.1 vertex) (hSecond : Incident gData second.1 vertex)
    (hValency : nonDanglingValency gData vertex = 2)
    (hbAnchor : ¬(coarse).Rel anchorSheet vertex.1.2)
    (hsE : star.right pairing first.1.1.1 = !rs ((coarse).repr vertex.1.2))
    (hsF : star.right pairing second.1.1.1 = !rs ((coarse).repr vertex.1.2))
    (hClass : ¬(blockRes ((coarse).repr vertex.1.2)).newEdge.Rel first.1.1.2 second.1.1.2) :
    (ResolutionAwayFromWall.retainedEdge C hGValid.1 first).stablePath =
      (ResolutionAwayFromWall.retainedEdge C hGValid.1 second).stablePath := by
  classical
  have hV : gData.sourceEndpoint wall vertex.1.2 = vertex :=
    (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
  obtain ⟨hAtE, hRelE⟩ := (incident_sourceEndpoint_iff _ first.1).mp (by rw [hV]; exact hFirst)
  obtain ⟨hAtF, hRelF⟩ := (incident_sourceEndpoint_iff _ second.1).mp (by rw [hV]; exact hSecond)
  have hReprE : (coarse).repr first.1.1.2 = (coarse).repr vertex.1.2 := hRelE.symm
  have hReprF : (coarse).repr second.1.1.2 = (coarse).repr vertex.1.2 := hRelF.symm
  have hbE : ¬(coarse).Rel anchorSheet first.1.1.2 := fun h ↦ hbAnchor (h.trans hRelE.symm)
  have hbF : ¬(coarse).Rel anchorSheet second.1.1.2 := fun h ↦ hbAnchor (h.trans hRelF.symm)
  have hsE' : star.right pairing first.1.1.1 = !rs ((coarse).repr first.1.1.2) := by
    rw [hReprE]; exact hsE
  have hsF' : star.right pairing second.1.1.1 = !rs ((coarse).repr second.1.1.2) := by
    rw [hReprF]; exact hsF
  have hUniqueE : ∀ other : gData.SourceEdge, ¬IsDangling gData other →
      other.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing other.1.1 = !rs ((coarse).repr first.1.1.2) →
      (blockRes ((coarse).repr first.1.1.2)).newEdge.Rel first.1.1.2 other.1.2 →
      other = first.1 := by
    intro other hoS hoAt _ hoRel
    have hCoarse : (coarse).Rel vertex.1.2 other.1.2 :=
      hRelE.trans ((blockRes_newEdge_refines pattern _).rel hoRel)
    rcases eq_of_survivor first second vertex hAt hNe hFirst hSecond hValency other hoS hoAt
      hCoarse with rfl | rfl
    · rfl
    · exact absurd (by rw [← hReprE]; exact hoRel) hClass
  have hUniqueF : ∀ other : gData.SourceEdge, ¬IsDangling gData other →
      other.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing other.1.1 = !rs ((coarse).repr second.1.1.2) →
      (blockRes ((coarse).repr second.1.1.2)).newEdge.Rel second.1.1.2 other.1.2 →
      other = second.1 := by
    intro other hoS hoAt _ hoRel
    have hCoarse : (coarse).Rel vertex.1.2 other.1.2 :=
      hRelF.trans ((blockRes_newEdge_refines pattern _).rel hoRel)
    rcases eq_of_survivor first second vertex hAt hNe hFirst hSecond hValency other hoS hoAt
      hCoarse with rfl | rfl
    · exact absurd (by rw [← hReprF] at hClass ⊢; exact hoRel.symm) hClass
    · rfl
  obtain ⟨hNewSurvE, _⟩ := newSourceEdge_survives_of_unique_fine_survivor C hRight pattern
    anchorSheet hRes hGValid hGenusC hbE first.2 hAtE hsE' rfl hUniqueE
  obtain ⟨hNewSurvF, _⟩ := newSourceEdge_survives_of_unique_fine_survivor C hRight pattern
    anchorSheet hRes hGValid hGenusC hbF second.2 hAtF hsF' rfl hUniqueF
  have hRowE := stablePath_newSourceEdge_eq C hRight pattern anchorSheet hRes hGValid hGenusC
    hbE first.2 hAtE hsE' rfl hUniqueE
  have hRowF := stablePath_newSourceEdge_eq C hRight pattern anchorSheet hRes hGValid hGenusC
    hbF second.2 hAtF hsF' rfl hUniqueF
  have hNeNew : C.newSourceEdge first.1.1.2 ≠ C.newSourceEdge second.1.1.2 := by
    intro hEq
    refine hClass ?_
    rw [← hReprE]
    exact (candidate_newEdge_rel_block C pattern anchorSheet hRes hbE second.1.1.2).mp
      (congrArg (fun e : C.datum.SourceEdge ↦ e.1.2) hEq)
  have hIncidA := newSourceEdge_incident_ret C pattern anchorSheet hRes hbAnchor hRelE
  have hIncidB := newSourceEdge_incident_ret C pattern anchorSheet hRes hbAnchor hRelF
  have hSubset : nonDanglingIncident C.datum
      (epv C (rs ((coarse).repr vertex.1.2)) vertex.1.2) ⊆
        {C.newSourceEdge first.1.1.2, C.newSourceEdge second.1.1.2} := by
    intro f hf
    obtain ⟨hfS, hfI⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    rcases nonDanglingIncident_ret_dichotomy C hRight pattern anchorSheet hRes hGValid hGenusC
      hbAnchor hfS hfI with
      ⟨old, hoS, hoAt, hoSide, hoRel, rfl⟩ | ⟨old, hoS, hoAt, hoSide, hoRel, rfl⟩
    · rcases eq_of_survivor first second vertex hAt hNe hFirst hSecond hValency old hoS hoAt
        hoRel with rfl | rfl
      · exact absurd (hsE.symm.trans hoSide) (by simp)
      · exact absurd (hsF.symm.trans hoSide) (by simp)
    · rcases eq_of_survivor first second vertex hAt hNe hFirst hSecond hValency old hoS hoAt
        hoRel with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hJoin : NonDanglingEdge.stablePath
        (⟨C.newSourceEdge first.1.1.2, hNewSurvE⟩ : NonDanglingEdge C.datum) =
      NonDanglingEdge.stablePath
        (⟨C.newSourceEdge second.1.1.2, hNewSurvF⟩ : NonDanglingEdge C.datum) :=
    stablePath_eq_of_consecutive
      ⟨fun h ↦ hNeNew (congrArg Subtype.val h),
        epv C (rs ((coarse).repr vertex.1.2)) vertex.1.2, hIncidA, hIncidB,
        nonDanglingValency_eq_two_of_pair' hNeNew hSubset
          ((mem_nonDanglingIncident _ _ _).mpr ⟨hNewSurvE, hIncidA⟩)
          ((mem_nonDanglingIncident _ _ _).mpr ⟨hNewSurvF, hIncidB⟩)⟩
  exact ((hRowE.symm.trans hJoin).trans hRowF)

include hRight hRes hGValid hGenusC in
/-- **The descent at a non-anchor wall block of surviving valency two.** -/
theorem ordinaryBlockDescent (first second : NonDanglingEdge gData)
    (vertex : gData.SourceVertex) (hAt : vertex.1.1 = wall)
    (hbAnchor : ¬(coarse).Rel anchorSheet vertex.1.2) (hNe : first ≠ second)
    (hFirst : Incident gData first.1 vertex) (hSecond : Incident gData second.1 vertex)
    (hValency : nonDanglingValency gData vertex = 2) :
    (ResolutionAwayFromWall.retainedEdge C hGValid.1 first).stablePath =
      (ResolutionAwayFromWall.retainedEdge C hGValid.1 second).stablePath := by
  classical
  have bne : ∀ {u v : Bool}, u ≠ v → u = !v := by
    intro u v h
    cases u <;> cases v <;> simp_all
  by_cases hE : star.right pairing first.1.1.1 = rs ((coarse).repr vertex.1.2)
  · by_cases hF : star.right pairing second.1.1.1 = rs ((coarse).repr vertex.1.2)
    · exact descent_of_both_retaining C hRight pattern anchorSheet hRes hGValid hGenusC first
        second vertex hAt hNe hFirst hSecond hValency hbAnchor hE hF
    · exact descent_of_mixed C hRight pattern anchorSheet hRes hGValid hGenusC first second
        vertex hAt hNe hFirst hSecond hValency hbAnchor hE (bne hF)
  · by_cases hF : star.right pairing second.1.1.1 = rs ((coarse).repr vertex.1.2)
    · exact (descent_of_mixed C hRight pattern anchorSheet hRes hGValid hGenusC second first
        vertex hAt hNe.symm hSecond hFirst hValency hbAnchor hF (bne hE)).symm
    · by_cases hRel : (blockRes ((coarse).repr vertex.1.2)).newEdge.Rel first.1.1.2 second.1.1.2
      · exact descent_of_both_fine_same C hRight pattern anchorSheet hRes hGValid hGenusC first
          second vertex hAt hNe hFirst hSecond hValency hbAnchor (bne hE) (bne hF) hRel
      · exact descent_of_both_fine_split C hRight pattern anchorSheet hRes hGValid hGenusC first
          second vertex hAt hNe hFirst hSecond hValency hbAnchor (bne hE) (bne hF) hRel

include hRight hRes hGValid hGenusC in
/-- Consecutive survivors of `gData` have retained copies on one stable row of
the candidate, provided no divalent vertex sits over the anchor block. -/
theorem stablePath_retained_eq_of_consecutive
    (hAnchorVal : ∀ vertex : gData.SourceVertex, vertex.1.1 = wall →
      (coarse).Rel anchorSheet vertex.1.2 → nonDanglingValency gData vertex ≠ 2)
    {first second : NonDanglingEdge gData} (h : Consecutive gData first second) :
    (ResolutionAwayFromWall.retainedEdge C hGValid.1 first).stablePath =
      (ResolutionAwayFromWall.retainedEdge C hGValid.1 second).stablePath := by
  obtain ⟨hNe, vertex, hFirst, hSecond, hValency⟩ := h
  by_cases hAt : vertex.1.1 = wall
  · by_cases hAnchorRel : (coarse).Rel anchorSheet vertex.1.2
    · exact absurd hValency (hAnchorVal vertex hAt hAnchorRel)
    · exact ordinaryBlockDescent C hRight pattern anchorSheet hRes hGValid hGenusC first second
        vertex hAt hAnchorRel hNe hFirst hSecond hValency
  · exact stablePath_eq_of_consecutive
      (ResolutionAwayFromWall.consecutive_retained_of_away C hGValid hGenusC first second hNe
        vertex hAt hFirst hSecond hValency)

/-- **The retained-row map.** -/
noncomputable def retainedRow
    (hAnchorVal : ∀ vertex : gData.SourceVertex, vertex.1.1 = wall →
      (coarse).Rel anchorSheet vertex.1.2 → nonDanglingValency gData vertex ≠ 2) :
    StablePath gData → StablePath C.datum :=
  Quot.lift (fun e ↦ (ResolutionAwayFromWall.retainedEdge C hGValid.1 e).stablePath)
    (fun _ _ h ↦ stablePath_retained_eq_of_consecutive C hRight pattern anchorSheet hRes hGValid
      hGenusC hAnchorVal h)

theorem retainedRow_mk
    (hAnchorVal : ∀ vertex : gData.SourceVertex, vertex.1.1 = wall →
      (coarse).Rel anchorSheet vertex.1.2 → nonDanglingValency gData vertex ≠ 2)
    (e : NonDanglingEdge gData) :
    retainedRow C hRight pattern anchorSheet hRes hGValid hGenusC hAnchorVal e.stablePath =
      (ResolutionAwayFromWall.retainedEdge C hGValid.1 e).stablePath := rfl

include hRight hRes hGValid hGenusC in
/-- **Every surviving new occurrence over a non-anchor wall block lies on the
retained row of a survivor of that block.** -/
theorem newSourceEdge_absorbed
    {x : Fin degree} (hb : ¬(coarse).Rel anchorSheet x)
    (hInj : NonDanglingStarInjective gData star (WallBlock.ofSheet gData wall x))
    (hValency : nonDanglingValency gData
      (WallBlock.sourceVertex gData wall (WallBlock.ofSheet gData wall x)) ≤ 3)
    (hSurv : ¬IsDangling C.datum (C.newSourceEdge x)) :
    ∃ (old : gData.SourceEdge) (hOld : ¬IsDangling gData old),
      NonDanglingEdge.stablePath (⟨C.newSourceEdge x, hSurv⟩ : NonDanglingEdge C.datum) =
        (ResolutionAwayFromWall.retainedEdge C hGValid.1 ⟨old, hOld⟩).stablePath := by
  classical
  by_cases hNone : ∀ old : gData.SourceEdge, ¬IsDangling gData old →
      old.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing old.1.1 = !rs ((coarse).repr x) →
      ¬(blockRes ((coarse).repr x)).newEdge.Rel x old.1.2
  · exact absurd (newSourceEdge_dangling_of_no_fine_survivor C hRight pattern anchorSheet hRes
      hGValid hGenusC hb hNone) hSurv
  simp only [not_forall, not_not] at hNone
  obtain ⟨old, hOldSurv, hOldAt, hOldSide, hOldRel⟩ := hNone
  by_cases hUniq : ∀ other : gData.SourceEdge, ¬IsDangling gData other →
      other.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing other.1.1 = !rs ((coarse).repr x) →
      (blockRes ((coarse).repr x)).newEdge.Rel x other.1.2 → other = old
  · exact ⟨old, hOldSurv, stablePath_newSourceEdge_eq C hRight pattern anchorSheet hRes hGValid
      hGenusC hb hOldSurv hOldAt hOldSide hOldRel hUniq⟩
  simp only [not_forall] at hUniq
  obtain ⟨other, hOtherSurv, hOtherAt, hOtherSide, hOtherRel, hOtherNe⟩ := hUniq
  have hOldCoarse : (coarse).Rel x old.1.2 :=
    (blockRes_newEdge_refines pattern ((coarse).repr x)).rel hOldRel
  have hOtherCoarse : (coarse).Rel x other.1.2 :=
    (blockRes_newEdge_refines pattern ((coarse).repr x)).rel hOtherRel
  have hSideNe : ∀ u v : gData.SourceEdge,
      star.right pairing u.1.1 = (!rs ((coarse).repr x)) →
      star.right pairing v.1.1 = rs ((coarse).repr x) → u ≠ v := by
    intro u v hu hv hEq
    rw [hEq, hv] at hu
    exact absurd hu (by simp)
  have hFineBlock : ∀ z : gData.SourceEdge, ¬IsDangling gData z →
      z.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing z.1.1 = (!rs ((coarse).repr x)) →
      (coarse).Rel x z.1.2 → (blockRes ((coarse).repr x)).newEdge.Rel x z.1.2 := by
    intro z hzS hzAt hzSide hzRel
    rcases eq_of_three_on_side (pairing := pairing) hInj old other z hOldSurv hOtherSurv hzS
      hOldAt hOtherAt hzAt hOldCoarse hOtherCoarse hzRel hOldSide hOtherSide hzSide with
      h | h | h
    · exact absurd h.symm hOtherNe
    · exact h ▸ hOldRel
    · exact h ▸ hOtherRel
  have hNewEq : ∀ z : gData.SourceEdge, ¬IsDangling gData z →
      z.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing z.1.1 = (!rs ((coarse).repr x)) →
      (coarse).Rel x z.1.2 → C.newSourceEdge z.1.2 = C.newSourceEdge x := by
    intro z hzS hzAt hzSide hzRel
    refine (newSourceEdge_eq_of_rel C ?_).symm
    rw [candidate_newEdge_rel_block C pattern anchorSheet hRes hb z.1.2]
    exact hFineBlock z hzS hzAt hzSide hzRel
  have hIncNew : Incident C.datum (C.newSourceEdge x) (epv C (rs ((coarse).repr x)) x) :=
    newSourceEdge_incident C _ x
  by_cases hRet : ∃ r : gData.SourceEdge, ¬IsDangling gData r ∧
      r.1.1 ∈ GluingDatum.incidentEdges wall ∧
      star.right pairing r.1.1 = rs ((coarse).repr x) ∧ (coarse).Rel x r.1.2
  · obtain ⟨r, hrS, hrAt, hrSide, hrRel⟩ := hRet
    have hRetUniq : ∀ z : gData.SourceEdge, ¬IsDangling gData z →
        z.1.1 ∈ GluingDatum.incidentEdges wall →
        star.right pairing z.1.1 = rs ((coarse).repr x) → (coarse).Rel x z.1.2 → z = r := by
      intro z hzS hzAt hzSide hzRel
      by_contra hzr
      have hSub4 : ({old, other, r, z} : Finset gData.SourceEdge) ⊆
          nonDanglingIncident gData
            (WallBlock.sourceVertex gData wall (WallBlock.ofSheet gData wall x)) := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact mem_nonDanglingIncident_block hOldSurv hOldAt hOldCoarse
        · exact mem_nonDanglingIncident_block hOtherSurv hOtherAt hOtherCoarse
        · exact mem_nonDanglingIncident_block hrS hrAt hrRel
        · exact mem_nonDanglingIncident_block hzS hzAt hzRel
      have h₁ : old ≠ other := fun h ↦ hOtherNe h.symm
      have h₂ : old ≠ r := hSideNe old r hOldSide hrSide
      have h₃ : old ≠ z := hSideNe old z hOldSide hzSide
      have h₄ : other ≠ r := hSideNe other r hOtherSide hrSide
      have h₅ : other ≠ z := hSideNe other z hOtherSide hzSide
      have h₆ : r ≠ z := fun h ↦ hzr h.symm
      have hCard4 : ({old, other, r, z} : Finset gData.SourceEdge).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [h₁, h₂, h₃]),
          Finset.card_insert_of_notMem (by simp [h₄, h₅]),
          Finset.card_insert_of_notMem (by simp [h₆]), Finset.card_singleton]
      have hLe := Finset.card_le_card hSub4
      rw [hCard4, card_nonDanglingIncident] at hLe
      omega
    have hSubset : nonDanglingIncident C.datum (epv C (rs ((coarse).repr x)) x) ⊆
        {C.oldSourceEdge r, C.newSourceEdge x} := by
      intro f hf
      obtain ⟨hfS, hfI⟩ := (mem_nonDanglingIncident _ _ _).mp hf
      rcases nonDanglingIncident_ret_dichotomy C hRight pattern anchorSheet hRes hGValid hGenusC
        hb hfS hfI with
        ⟨z, hzS, hzAt, hzSide, hzRel, rfl⟩ | ⟨z, hzS, hzAt, hzSide, hzRel, rfl⟩
      · rw [hRetUniq z hzS hzAt hzSide hzRel]
        exact Finset.mem_insert_self _ _
      · rw [hNewEq z hzS hzAt hzSide hzRel]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hIncOldR := oldSourceEdge_incident_ret C hRight pattern anchorSheet hRes hb hrAt hrRel
      hrSide
    have hSurvOldR : ¬IsDangling C.datum (C.oldSourceEdge r) :=
      ResolutionSurvival.not_isDangling_oldSourceEdge _ hGValid.1 _ hrS
    have hNeOldNew : C.oldSourceEdge r ≠ C.newSourceEdge x := fun h ↦ new_ne_old C x r h.symm
    have hVal2 := nonDanglingValency_eq_two_of_pair' hNeOldNew hSubset
      ((mem_nonDanglingIncident _ _ _).mpr ⟨hSurvOldR, hIncOldR⟩)
      ((mem_nonDanglingIncident _ _ _).mpr ⟨hSurv, hIncNew⟩)
    exact ⟨r, hrS, stablePath_eq_of_consecutive
      ⟨fun h ↦ hNeOldNew (congrArg Subtype.val h).symm, _, hIncNew, hIncOldR, hVal2⟩⟩
  · exfalso
    refine hSurv (isDangling_of_subset_singleton C hGValid ?_ hIncNew)
    intro f hf
    obtain ⟨hfS, hfI⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    rcases nonDanglingIncident_ret_dichotomy C hRight pattern anchorSheet hRes hGValid hGenusC hb
      hfS hfI with
      ⟨z, hzS, hzAt, hzSide, hzRel, rfl⟩ | ⟨z, hzS, hzAt, hzSide, hzRel, rfl⟩
    · exact absurd ⟨z, hzS, hzAt, hzSide, hzRel⟩ hRet
    · rw [hNewEq z hzS hzAt hzSide hzRel]
      exact Finset.mem_singleton_self _

/-! ### Path ends through a non-anchor block -/

omit C in
theorem blockVertex_eq (x : Fin degree) :
    WallBlock.sourceVertex gData wall (WallBlock.ofSheet gData wall x) =
      gData.sourceEndpoint wall x :=
  NonTrivalentValencyFourExit.sourceEndpoint_eq_of_rel ((coarse).rel_repr_left x)

omit C in
theorem mem_block_star {x : Fin degree} {z : gData.SourceEdge} (hz : ¬IsDangling gData z)
    (hAt : z.1.1 ∈ GluingDatum.incidentEdges wall) (hRel : (coarse).Rel x z.1.2) :
    z ∈ nonDanglingIncident gData (gData.sourceEndpoint wall x) :=
  (mem_nonDanglingIncident _ _ _).mpr ⟨hz, (incident_sourceEndpoint_iff x z).mpr ⟨hAt, hRel⟩⟩

omit C in
theorem block_star_mem {x : Fin degree} {z : gData.SourceEdge}
    (hz : z ∈ nonDanglingIncident gData (gData.sourceEndpoint wall x)) :
    ¬IsDangling gData z ∧ z.1.1 ∈ GluingDatum.incidentEdges wall ∧ (coarse).Rel x z.1.2 := by
  obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hz
  obtain ⟨hAt, hRel⟩ := (incident_sourceEndpoint_iff x z).mp hInc
  exact ⟨hSurv, hAt, hRel⟩

theorem bool_ne_iff_eq_not {x y : Bool} : x ≠ y ↔ x = !y := by
  cases x <;> cases y <;> simp

include hRight hRes hGValid hGenusC in
/-- The retaining endpoint of a non-anchor block is trivalent when every
fine-side survivor is alone in its new-edge class. -/
theorem nonDanglingValency_ret_eq_three_of_unique {x : Fin degree}
    (hb : ¬(coarse).Rel anchorSheet x)
    (hVal : nonDanglingValency gData
      (WallBlock.sourceVertex gData wall (WallBlock.ofSheet gData wall x)) ≤ 3)
    (hThree : nonDanglingValency gData (gData.sourceEndpoint wall x) = 3)
    (hUniq : ∀ z z' : gData.SourceEdge,
      z ∈ nonDanglingIncident gData (gData.sourceEndpoint wall x) →
      z' ∈ nonDanglingIncident gData (gData.sourceEndpoint wall x) →
      star.right pairing z.1.1 = !rs ((coarse).repr x) →
      star.right pairing z'.1.1 = !rs ((coarse).repr x) →
      (blockRes ((coarse).repr x)).newEdge.Rel z.1.2 z'.1.2 → z = z') :
    nonDanglingValency C.datum (epv C (rs ((coarse).repr x)) x) = 3 := by
  classical
  refine le_antisymm (nonDanglingValency_ret_le C hRight pattern anchorSheet hRes hGValid hGenusC
    hb hVal) ?_
  rw [← card_nonDanglingIncident, ← hThree, ← card_nonDanglingIncident]
  refine Finset.card_le_card_of_injOn (fun z : gData.SourceEdge ↦
    if star.right pairing z.1.1 = rs ((coarse).repr x) then C.oldSourceEdge z
    else C.newSourceEdge z.1.2) ?_ ?_
  · intro z hz
    obtain ⟨hzS, hzA, hzR⟩ := block_star_mem hz
    have hbz : ¬(coarse).Rel anchorSheet z.1.2 := fun hBad ↦ hb (hBad.trans hzR.symm)
    have hReprZ : (coarse).repr z.1.2 = (coarse).repr x := hzR.symm
    by_cases hSide : star.right pairing z.1.1 = rs ((coarse).repr x)
    · simp only [ite_eq_left hSide]
      exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨ResolutionSurvival.not_isDangling_oldSourceEdge C hGValid.1 _ hzS,
          oldSourceEdge_incident_ret C hRight pattern anchorSheet hRes hb hzA hzR hSide⟩
    · simp only [ite_eq_right hSide]
      have hSurv := (newSourceEdge_survives_of_unique_fine_survivor C hRight pattern anchorSheet
        hRes hGValid hGenusC hbz hzS hzA (by rw [hReprZ]; exact bool_ne_iff_eq_not.mp hSide) rfl
        (by
          intro other hOtherS hOtherA hOtherSide hOtherRel
          rw [hReprZ] at hOtherSide hOtherRel
          refine hUniq other z ?_ hz hOtherSide (bool_ne_iff_eq_not.mp hSide) hOtherRel.symm
          exact mem_block_star hOtherS hOtherA
            (hzR.trans ((blockRes_newEdge_refines pattern _).rel hOtherRel)))).1
      exact (mem_nonDanglingIncident _ _ _).mpr ⟨hSurv,
        newSourceEdge_incident_ret C pattern anchorSheet hRes hb hzR⟩
  · intro z hz z' hz' hEq
    simp only at hEq
    obtain ⟨hzS, hzA, hzR⟩ := block_star_mem hz
    by_cases hSide : star.right pairing z.1.1 = rs ((coarse).repr x)
    · by_cases hSide' : star.right pairing z'.1.1 = rs ((coarse).repr x)
      · rw [ite_eq_left hSide, ite_eq_left hSide'] at hEq
        exact ResolutionCut.oldSourceEdge_injective C hEq
      · rw [ite_eq_left hSide, ite_eq_right hSide'] at hEq
        exact absurd hEq.symm (new_ne_old C z'.1.2 z)
    · by_cases hSide' : star.right pairing z'.1.1 = rs ((coarse).repr x)
      · rw [ite_eq_right hSide, ite_eq_left hSide'] at hEq
        exact absurd hEq (new_ne_old C z.1.2 z')
      · rw [ite_eq_right hSide, ite_eq_right hSide'] at hEq
        have hbz : ¬(coarse).Rel anchorSheet z.1.2 := fun hBad ↦ hb (hBad.trans hzR.symm)
        have hReprZ : (coarse).repr z.1.2 = (coarse).repr x := hzR.symm
        have hRel := (candidate_newEdge_rel_block C pattern anchorSheet hRes hbz z'.1.2).mp
          (congrArg (fun e : C.datum.SourceEdge ↦ e.1.2) hEq)
        rw [hReprZ] at hRel
        exact hUniq z z' hz hz' (bool_ne_iff_eq_not.mp hSide) (bool_ne_iff_eq_not.mp hSide') hRel

include hRight hRes hGValid hGenusC in
/-- Case I of the non-anchor path-end transport. -/
theorem exists_isPathEnd_ordinary_unique {x : Fin degree} (h : NonDanglingEdge gData)
    (hb : ¬(coarse).Rel anchorSheet x)
    (hVal : nonDanglingValency gData
      (WallBlock.sourceVertex gData wall (WallBlock.ofSheet gData wall x)) ≤ 3)
    (hMem : h.1 ∈ nonDanglingIncident gData (gData.sourceEndpoint wall x))
    (hThree : nonDanglingValency gData (gData.sourceEndpoint wall x) = 3)
    (hUniq : ∀ z z' : gData.SourceEdge,
      z ∈ nonDanglingIncident gData (gData.sourceEndpoint wall x) →
      z' ∈ nonDanglingIncident gData (gData.sourceEndpoint wall x) →
      star.right pairing z.1.1 = !rs ((coarse).repr x) →
      star.right pairing z'.1.1 = !rs ((coarse).repr x) →
      (blockRes ((coarse).repr x)).newEdge.Rel z.1.2 z'.1.2 → z = z') :
    ∃ (first : NonDanglingEdge C.datum) (vertex : C.datum.SourceVertex),
      first.stablePath = (ResolutionAwayFromWall.retainedEdge C hGValid.1 h).stablePath ∧
        IsPathEnd C.datum first.1 vertex := by
  classical
  obtain ⟨hS, hA, hR⟩ := block_star_mem hMem
  have hRet3 := nonDanglingValency_ret_eq_three_of_unique C hRight pattern anchorSheet hRes
    hGValid hGenusC hb hVal hThree hUniq
  by_cases hSide : star.right pairing h.1.1.1 = rs ((coarse).repr x)
  · refine ⟨ResolutionAwayFromWall.retainedEdge C hGValid.1 h,
      epv C (rs ((coarse).repr x)) x, rfl,
      oldSourceEdge_incident_ret C hRight pattern anchorSheet hRes hb hA hR hSide, ?_⟩
    rw [hRet3]
    omega
  · have hbz : ¬(coarse).Rel anchorSheet h.1.1.2 := fun hBad ↦ hb (hBad.trans hR.symm)
    have hReprZ : (coarse).repr h.1.1.2 = (coarse).repr x := hR.symm
    have hSideFine : star.right pairing h.1.1.1 = !rs ((coarse).repr h.1.1.2) := by
      rw [hReprZ]
      exact bool_ne_iff_eq_not.mp hSide
    have hUniqLocal : ∀ other : gData.SourceEdge, ¬IsDangling gData other →
        other.1.1 ∈ GluingDatum.incidentEdges wall →
        star.right pairing other.1.1 = !rs ((coarse).repr h.1.1.2) →
        (blockRes ((coarse).repr h.1.1.2)).newEdge.Rel h.1.1.2 other.1.2 → other = h.1 := by
      intro other hOtherS hOtherA hOtherSide hOtherRel
      rw [hReprZ] at hOtherSide hOtherRel
      refine hUniq other h.1 ?_ hMem hOtherSide (bool_ne_iff_eq_not.mp hSide) hOtherRel.symm
      exact mem_block_star hOtherS hOtherA
        (hR.trans ((blockRes_newEdge_refines pattern _).rel hOtherRel))
    have hSurv := (newSourceEdge_survives_of_unique_fine_survivor C hRight pattern anchorSheet
      hRes hGValid hGenusC hbz h.2 hA hSideFine rfl hUniqLocal).1
    refine ⟨⟨C.newSourceEdge h.1.1.2, hSurv⟩, epv C (rs ((coarse).repr x)) x, ?_,
      newSourceEdge_incident_ret C pattern anchorSheet hRes hb hR, ?_⟩
    · exact stablePath_newSourceEdge_eq C hRight pattern anchorSheet hRes hGValid hGenusC hbz h.2
        hA hSideFine rfl hUniqLocal
    · rw [hRet3]
      omega

include hRight hRes hGValid hGenusC in
/-- Case II of the non-anchor path-end transport: two fine-side survivors in
one new-edge class. -/
theorem exists_isPathEnd_ordinary_pair {x : Fin degree} (h : NonDanglingEdge gData)
    (hb : ¬(coarse).Rel anchorSheet x)
    (hInj : NonDanglingStarInjective gData star (WallBlock.ofSheet gData wall x))
    (hMem : h.1 ∈ nonDanglingIncident gData (gData.sourceEndpoint wall x))
    (hThree : nonDanglingValency gData (gData.sourceEndpoint wall x) = 3)
    (f₁ f₂ : gData.SourceEdge)
    (hf₁ : f₁ ∈ nonDanglingIncident gData (gData.sourceEndpoint wall x))
    (hf₂ : f₂ ∈ nonDanglingIncident gData (gData.sourceEndpoint wall x))
    (hfNe : f₁ ≠ f₂)
    (hs₁ : star.right pairing f₁.1.1 = !rs ((coarse).repr x))
    (hs₂ : star.right pairing f₂.1.1 = !rs ((coarse).repr x))
    (hcls : (blockRes ((coarse).repr x)).newEdge.Rel f₁.1.2 f₂.1.2) :
    ∃ (first : NonDanglingEdge C.datum) (vertex : C.datum.SourceVertex),
      first.stablePath = (ResolutionAwayFromWall.retainedEdge C hGValid.1 h).stablePath ∧
        IsPathEnd C.datum first.1 vertex := by
  classical
  obtain ⟨_, _, hR⟩ := block_star_mem hMem
  obtain ⟨h₁S, h₁A, h₁R⟩ := block_star_mem hf₁
  obtain ⟨h₂S, h₂A, h₂R⟩ := block_star_mem hf₂
  have hbf₁ : ¬(coarse).Rel anchorSheet f₁.1.2 := fun hBad ↦ hb (hBad.trans h₁R.symm)
  have hRepr₁ : (coarse).repr f₁.1.2 = (coarse).repr x := h₁R.symm
  set stars := nonDanglingIncident gData (gData.sourceEndpoint wall x) with hStars
  set T := rs ((coarse).repr x) with hT
  have hUnion : stars.filter (fun z ↦ star.right pairing z.1.1 = T) ∪
      stars.filter (fun z ↦ star.right pairing z.1.1 = !T) = stars := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_filter.mp hz).1
      · exact (Finset.mem_filter.mp hz).1
    · intro z hz
      by_cases hSide : star.right pairing z.1.1 = T
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hSide⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hz, bool_ne_iff_eq_not.mp hSide⟩)
  have hDisj : Disjoint (stars.filter (fun z ↦ star.right pairing z.1.1 = T))
      (stars.filter (fun z ↦ star.right pairing z.1.1 = !T)) := by
    refine Finset.disjoint_left.mpr ?_
    intro z hz hz'
    have h1 := (Finset.mem_filter.mp hz).2
    have h2 := (Finset.mem_filter.mp hz').2
    exact Bool.not_ne_self T (h2.symm.trans h1)
  have hSum : (stars.filter (fun z ↦ star.right pairing z.1.1 = T)).card +
      (stars.filter (fun z ↦ star.right pairing z.1.1 = !T)).card = 3 := by
    rw [← Finset.card_union_of_disjoint hDisj, hUnion, hStars, card_nonDanglingIncident]
    exact hThree
  have hFineGe : 2 ≤ (stars.filter (fun z ↦ star.right pairing z.1.1 = !T)).card := by
    have hsub : ({f₁, f₂} : Finset gData.SourceEdge) ⊆
        stars.filter (fun z ↦ star.right pairing z.1.1 = !T) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hf₁, hs₁⟩
      · exact Finset.mem_filter.mpr ⟨hf₂, hs₂⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_insert_of_notMem (by simpa using hfNe), Finset.card_singleton] at this
  have hFineLe : (stars.filter (fun z ↦ star.right pairing z.1.1 = !T)).card ≤ 2 := by
    rw [hStars, ← blockVertex_eq x]
    exact card_side_le_two (pairing := pairing) hInj (!T)
  have hRetOne : (stars.filter (fun z ↦ star.right pairing z.1.1 = T)).card = 1 := by omega
  obtain ⟨z, hzEq⟩ := Finset.card_eq_one.mp hRetOne
  have hzMem : z ∈ stars ∧ star.right pairing z.1.1 = T := by
    have : z ∈ stars.filter (fun w ↦ star.right pairing w.1.1 = T) := by
      rw [hzEq]; exact Finset.mem_singleton_self z
    exact Finset.mem_filter.mp this
  obtain ⟨hzS, hzA, hzR⟩ := block_star_mem hzMem.1
  have hPair : stars.filter (fun w ↦ star.right pairing w.1.1 = !T) = {f₁, f₂} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hf₁, hs₁⟩
      · exact Finset.mem_filter.mpr ⟨hf₂, hs₂⟩
    · rw [Finset.card_insert_of_notMem (by simpa using hfNe), Finset.card_singleton]
      omega
  have hRetSubset : nonDanglingIncident C.datum (epv C T x) ⊆
      {C.oldSourceEdge z, C.newSourceEdge f₁.1.2} := by
    intro w hw
    obtain ⟨hwS, hwI⟩ := (mem_nonDanglingIncident _ _ _).mp hw
    rcases nonDanglingIncident_ret_dichotomy C hRight pattern anchorSheet hRes hGValid hGenusC hb
      hwS hwI with
      ⟨old, hOldS, hOldA, hOldSide, hOldR, rfl⟩ | ⟨old, hOldS, hOldA, hOldSide, hOldR, rfl⟩
    · have hOldMem : old ∈ stars.filter (fun w ↦ star.right pairing w.1.1 = T) :=
        Finset.mem_filter.mpr ⟨mem_block_star hOldS hOldA hOldR, hOldSide⟩
      rw [hzEq, Finset.mem_singleton] at hOldMem
      rw [hOldMem]
      exact Finset.mem_insert_self _ _
    · have hOldMem : old ∈ stars.filter (fun w ↦ star.right pairing w.1.1 = !T) :=
        Finset.mem_filter.mpr ⟨mem_block_star hOldS hOldA hOldR, hOldSide⟩
      rw [hPair, Finset.mem_insert, Finset.mem_singleton] at hOldMem
      refine Finset.mem_insert_of_mem (Finset.mem_singleton.mpr ?_)
      rcases hOldMem with rfl | rfl
      · rfl
      · refine (newSourceEdge_eq_of_rel C ?_).symm
        exact (candidate_newEdge_rel_block C pattern anchorSheet hRes hbf₁ old.1.2).mpr
          (by rw [hRepr₁]; exact hcls)
  have hOldZIncident : Incident C.datum (C.oldSourceEdge z) (epv C T x) :=
    oldSourceEdge_incident_ret C hRight pattern anchorSheet hRes hb hzA hzR hzMem.2
  have hOldZMem : C.oldSourceEdge z ∈ nonDanglingIncident C.datum (epv C T x) :=
    (mem_nonDanglingIncident _ _ _).mpr
      ⟨ResolutionSurvival.not_isDangling_oldSourceEdge C hGValid.1 _ hzS, hOldZIncident⟩
  have hRetTwo : nonDanglingValency C.datum (epv C T x) = 2 := by
    have hLe : nonDanglingValency C.datum (epv C T x) ≤ 2 := by
      rw [← card_nonDanglingIncident]
      refine le_trans (Finset.card_le_card hRetSubset) ?_
      exact le_trans (Finset.card_insert_le _ _) (by simp)
    have hNe0 : nonDanglingValency C.datum (epv C T x) ≠ 0 :=
      ClassInjectivity.nonDanglingValency_ne_zero_of_incident C.datum
        ((mem_nonDanglingIncident _ _ _).mp hOldZMem).1 hOldZIncident
    have hNe1 := NonDanglingValency.nonDanglingValency_ne_one C.datum
      (C.datum_valid hGValid).1 (epv C T x)
    omega
  have hCard2 : 1 < (nonDanglingIncident C.datum (epv C T x)).card := by
    rw [card_nonDanglingIncident, hRetTwo]
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hCard2
  obtain ⟨y, hyMem, hyNe⟩ : ∃ y ∈ nonDanglingIncident C.datum (epv C T x),
      y ≠ C.oldSourceEdge z := by
    by_cases hU : u = C.oldSourceEdge z
    · exact ⟨v, hv, fun hBad ↦ huv (hU.trans hBad.symm)⟩
    · exact ⟨u, hu, hU⟩
  have hyEq : y = C.newSourceEdge f₁.1.2 := by
    have := hRetSubset hyMem
    rw [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact absurd h hyNe
    · exact h
  have hNewSurv : ¬IsDangling C.datum (C.newSourceEdge f₁.1.2) := by
    rw [← hyEq]
    exact ((mem_nonDanglingIncident _ _ _).mp hyMem).1
  have hMove : epv C (!T) f₂.1.2 = epv C (!T) f₁.1.2 := by
    have hM := epv_fine_eq C pattern anchorSheet hRes hbf₁ (y := f₂.1.2)
      (by rw [hRepr₁]; exact hcls)
    rw [hRepr₁] at hM
    exact hM
  have hInc₁ : Incident C.datum (C.oldSourceEdge f₁) (epv C (!T) f₁.1.2) := by
    have hI := oldSourceEdge_incident C f₁.1.1 h₁A (!T) (by rw [hRight]; exact hs₁) f₁.1.2
    rwa [W2MkkGraphData.sourceEdge_self] at hI
  have hInc₂ : Incident C.datum (C.oldSourceEdge f₂) (epv C (!T) f₁.1.2) := by
    have hI := oldSourceEdge_incident C f₂.1.1 h₂A (!T) (by rw [hRight]; exact hs₂) f₂.1.2
    rwa [W2MkkGraphData.sourceEdge_self, hMove] at hI
  have hInc₃ : Incident C.datum (C.newSourceEdge f₁.1.2) (epv C (!T) f₁.1.2) :=
    newSourceEdge_incident C (!T) f₁.1.2
  have hFineThree : nonDanglingValency C.datum (epv C (!T) f₁.1.2) = 3 := by
    have hLe : nonDanglingValency C.datum (epv C (!T) f₁.1.2) ≤ 3 := by
      have := nonDanglingValency_fine_le C hRight pattern anchorSheet hRes hGValid hGenusC hbf₁
        (x := f₁.1.2) (by
          have hEqBlock : WallBlock.ofSheet gData wall f₁.1.2 = WallBlock.ofSheet gData wall x :=
            Subtype.ext hRepr₁
          rw [hEqBlock]
          exact hInj)
      rwa [hRepr₁] at this
    have hSub : ({C.oldSourceEdge f₁, C.oldSourceEdge f₂, C.newSourceEdge f₁.1.2} :
        Finset C.datum.SourceEdge) ⊆ nonDanglingIncident C.datum (epv C (!T) f₁.1.2) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨ResolutionSurvival.not_isDangling_oldSourceEdge C hGValid.1 _ h₁S, hInc₁⟩
      · exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨ResolutionSurvival.not_isDangling_oldSourceEdge C hGValid.1 _ h₂S, hInc₂⟩
      · exact (mem_nonDanglingIncident _ _ _).mpr ⟨hNewSurv, hInc₃⟩
    have hCard := Finset.card_le_card hSub
    rw [card_nonDanglingIncident,
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun hBad ↦ hfNe (ResolutionCut.oldSourceEdge_injective C hBad),
          fun hBad ↦ new_ne_old C f₁.1.2 f₁ hBad.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact fun hBad ↦ new_ne_old C f₁.1.2 f₂ hBad.symm),
      Finset.card_singleton] at hCard
    omega
  by_cases hSideH : star.right pairing h.1.1.1 = T
  · have hHz : h.1 = z := by
      have hMemT : h.1 ∈ stars.filter (fun w ↦ star.right pairing w.1.1 = T) :=
        Finset.mem_filter.mpr ⟨hMem, hSideH⟩
      rw [hzEq, Finset.mem_singleton] at hMemT
      exact hMemT
    refine ⟨⟨C.newSourceEdge f₁.1.2, hNewSurv⟩, epv C (!T) f₁.1.2, ?_, hInc₃, ?_⟩
    · refine stablePath_eq_of_consecutive ⟨?_, epv C T x,
        newSourceEdge_incident_ret C pattern anchorSheet hRes hb h₁R, ?_, hRetTwo⟩
      · intro hBad
        apply hyNe
        rw [hyEq, ← hHz]
        exact congrArg Subtype.val hBad
      · show Incident C.datum (C.oldSourceEdge h.1) (epv C T x)
        rw [hHz]
        exact hOldZIncident
    · rw [hFineThree]
      omega
  · have hSideFine : star.right pairing h.1.1.1 = !T := bool_ne_iff_eq_not.mp hSideH
    have hMemF : h.1 ∈ stars.filter (fun w ↦ star.right pairing w.1.1 = !T) :=
      Finset.mem_filter.mpr ⟨hMem, hSideFine⟩
    rw [hPair, Finset.mem_insert, Finset.mem_singleton] at hMemF
    refine ⟨ResolutionAwayFromWall.retainedEdge C hGValid.1 h, epv C (!T) f₁.1.2, rfl, ?_, ?_⟩
    · show Incident C.datum (C.oldSourceEdge h.1) (epv C (!T) f₁.1.2)
      rcases hMemF with hEq | hEq
      · rw [hEq]
        exact hInc₁
      · rw [hEq]
        exact hInc₂
    · rw [hFineThree]
      omega

include hRight hRes hGValid hGenusC in
/-- **The non-anchor block half of the path-end transport.** -/
theorem exists_isPathEnd_ordinary {x : Fin degree} (h : NonDanglingEdge gData)
    (hb : ¬(coarse).Rel anchorSheet x)
    (hInj : NonDanglingStarInjective gData star (WallBlock.ofSheet gData wall x))
    (hVal : nonDanglingValency gData
      (WallBlock.sourceVertex gData wall (WallBlock.ofSheet gData wall x)) ≤ 3)
    (hInc : Incident gData h.1 (gData.sourceEndpoint wall x))
    (hNd : nonDanglingValency gData (gData.sourceEndpoint wall x) ≠ 2) :
    ∃ (first : NonDanglingEdge C.datum) (vertex : C.datum.SourceVertex),
      first.stablePath = (ResolutionAwayFromWall.retainedEdge C hGValid.1 h).stablePath ∧
        IsPathEnd C.datum first.1 vertex := by
  classical
  have hMem : h.1 ∈ nonDanglingIncident gData (gData.sourceEndpoint wall x) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨h.2, hInc⟩
  have hThree : nonDanglingValency gData (gData.sourceEndpoint wall x) = 3 := by
    have hLe : nonDanglingValency gData (gData.sourceEndpoint wall x) ≤ 3 := by
      rw [← blockVertex_eq x]
      exact hVal
    have hNe0 := ClassInjectivity.nonDanglingValency_ne_zero_of_incident gData h.2 hInc
    have hNe1 := NonDanglingValency.nonDanglingValency_ne_one gData hGValid.1
      (gData.sourceEndpoint wall x)
    omega
  by_cases hU : ∀ z z' : gData.SourceEdge,
      z ∈ nonDanglingIncident gData (gData.sourceEndpoint wall x) →
      z' ∈ nonDanglingIncident gData (gData.sourceEndpoint wall x) →
      star.right pairing z.1.1 = !rs ((coarse).repr x) →
      star.right pairing z'.1.1 = !rs ((coarse).repr x) →
      (blockRes ((coarse).repr x)).newEdge.Rel z.1.2 z'.1.2 → z = z'
  · exact exists_isPathEnd_ordinary_unique C hRight pattern anchorSheet hRes hGValid hGenusC h hb
      hVal hMem hThree hU
  · simp only [not_forall] at hU
    obtain ⟨f₁, f₂, hf₁, hf₂, hs₁, hs₂, hcls, hfNe⟩ := hU
    exact exists_isPathEnd_ordinary_pair C hRight pattern anchorSheet hRes hGValid hGenusC h hb
      hInj hMem hThree f₁ f₂ hf₁ hf₂ hfNe hs₁ hs₂ hcls

end Descent

/-! ## 11.  Path ends of the general-`K` candidate -/

section PathEnds

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : W4TargetPairings.FourStar target wall}
  {anchor : W4Assembly.WallBlock data wall}
  {source : FourBranchAnchor data star anchor} {pairing : Fin 3} {side : Bool}
  (position : Position source pairing side)
  (profile : NonTrivalentValencyFourBackground.OrdinaryBlockProfile data star anchor.1)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)
  (geometry : PairingBackground position.datum star pairing anchor.1) (hValid : data.Valid)
  (hBg : ∀ block, ¬(position.datum.vertexPartition wall).Rel anchor.1 block →
    geometry.resolution block = canonicalLocal position.datum star profile.pattern pairing block)

local notation "C" => (position.candidate hConnected hGenus hNoGlue geometry)

theorem survivorEdge_ne {first second : Fin 4} (hNe : first ≠ second) :
    survivorEdge position first ≠ survivorEdge position second := by
  intro hEq
  exact hNe (star.edge_injective (congrArg (fun e : position.datum.SourceEdge ↦ e.1.1) hEq))

include hValid hBg in
/-- **Both endpoint classes of the bridge are exactly trivalent.** -/
theorem nonDanglingValency_bridge_eq_three (b : Bool) :
    nonDanglingValency (C).datum (epv (C) b position.split.bridge) = 3 := by
  classical
  have hGenusC := candidate_sourceGenus_of_local position profile hConnected hGenus hNoGlue
    geometry hBg
  have hSub := nonDanglingIncident_bridge_subset position hConnected hGenus hNoGlue geometry
    hValid hGenusC b
  have hL1 := labelRight_firstLabel pairing b
  have hL2 := labelRight_secondLabel pairing b
  have hI1 := survivor_incident position hConnected hGenus hNoGlue geometry (firstLabel pairing b)
  have hI2 := survivor_incident position hConnected hGenus hNoGlue geometry (secondLabel pairing b)
  rw [hL1] at hI1
  rw [hL2] at hI2
  have hSup : ({(C).newSourceEdge position.split.bridge,
      (C).oldSourceEdge (survivorEdge position (firstLabel pairing b)),
      (C).oldSourceEdge (survivorEdge position (secondLabel pairing b))} :
        Finset (C).datum.SourceEdge) ⊆ nonDanglingIncident (C).datum
          (epv (C) b position.split.bridge) := by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨bridge_not_isDangling_general position hConnected hGenus hNoGlue geometry hValid,
          newSourceEdge_incident (C) b _⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨survivor_survives position hConnected hGenus hNoGlue geometry hValid _, hI1⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨survivor_survives position hConnected hGenus hNoGlue geometry hValid _, hI2⟩
  rw [← card_nonDanglingIncident, Finset.Subset.antisymm hSub hSup]
  have hNe12 : (C).oldSourceEdge (survivorEdge position (firstLabel pairing b)) ≠
      (C).oldSourceEdge (survivorEdge position (secondLabel pairing b)) := fun h ↦
    survivorEdge_ne position (firstLabel_ne_secondLabel pairing b)
      (ResolutionCut.oldSourceEdge_injective (C) h)
  rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨new_ne_old (C) _ _, new_ne_old (C) _ _⟩),
    Finset.card_insert_of_notMem (by simpa using hNe12), Finset.card_singleton]

include hValid hBg in
/-- **Path ends (general form).**  `HasPathEnds` of the general-`K` candidate, from
`HasPathEnds` of the incoming datum and the incoming census. -/
theorem hasPathEnds_of
    (hInj : ∀ y, NonDanglingStarInjective data star (WallBlock.ofSheet data wall y))
    (hVal : ∀ y, ¬(data.vertexPartition wall).Rel anchor.1 y →
      nonDanglingValency data (WallBlock.sourceVertex data wall (WallBlock.ofSheet data wall y)) ≤ 3)
    (hEnds : HasPathEnds data) :
    HasPathEnds (C).datum := by
  classical
  have hGenusC := candidate_sourceGenus_of_local position profile hConnected hGenus hNoGlue
    geometry hBg
  have hDV := position.datum_valid hValid
  have hRes : ∀ block, ¬(position.datum.vertexPartition wall).Rel anchor.1 block →
      (C).resolution block = canonicalLocal position.datum star profile.pattern pairing block :=
    fun block hBlock ↦ (candidate_resolution_of_not_rel position hConnected hGenus hNoGlue
      geometry block hBlock).trans (hBg block hBlock)
  have hRight := candidate_right position hConnected hGenus hNoGlue geometry
  have hWallIff : ∀ y, (position.datum.vertexPartition wall).Rel anchor.1 y ↔
      (data.vertexPartition wall).Rel anchor.1 y := fun y ↦ by
    rw [position.datum_vertexPartition_wall]
  have hInjG : ∀ y, ¬(position.datum.vertexPartition wall).Rel anchor.1 y →
      NonDanglingStarInjective position.datum star (WallBlock.ofSheet position.datum wall y) :=
    fun y _ ↦ datum_starInjective position hValid y (hInj y)
  have hValG : ∀ y, ¬(position.datum.vertexPartition wall).Rel anchor.1 y →
      nonDanglingValency position.datum
        (WallBlock.sourceVertex position.datum wall (WallBlock.ofSheet position.datum wall y)) ≤ 3 :=
    fun y hy ↦ by
      rw [datum_valency_block position hValid]
      exact hVal y ((hWallIff y).not.mp hy)
  have hAnchorVal : ∀ vertex : position.datum.SourceVertex, vertex.1.1 = wall →
      (position.datum.vertexPartition wall).Rel anchor.1 vertex.1.2 →
      nonDanglingValency position.datum vertex ≠ 2 := by
    intro vertex hAt hRel
    have hV : position.datum.sourceEndpoint wall vertex.1.2 = vertex :=
      (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
    rw [← hV, datum_nonDanglingValency_endpoint position hValid]
    have hEq : data.sourceEndpoint wall vertex.1.2 = WallBlock.sourceVertex data wall anchor :=
      NonTrivalentValencyFourExit.sourceEndpoint_eq_of_rel ((hWallIff _).mp hRel).symm
    rw [hEq, source.nonDanglingValency_eq_four]
    omega
  have hEndsG := datum_hasPathEnds position hValid hEnds
  -- a path end on the retained row of every survivor of the gauged datum
  have hRetained : ∀ g : NonDanglingEdge position.datum,
      ∃ (first : NonDanglingEdge (C).datum) (vertex : (C).datum.SourceVertex),
        first.stablePath = (ResolutionAwayFromWall.retainedEdge (C) hDV.1 g).stablePath ∧
          IsPathEnd (C).datum first.1 vertex := by
    intro g
    obtain ⟨h, w, hRow, hIncW, hNdW⟩ := hEndsG g
    have hRowEq : (ResolutionAwayFromWall.retainedEdge (C) hDV.1 h).stablePath =
        (ResolutionAwayFromWall.retainedEdge (C) hDV.1 g).stablePath := by
      have := congrArg (retainedRow (C) hRight profile.pattern anchor.1 hRes hDV hGenusC
        hAnchorVal) hRow
      rwa [retainedRow_mk, retainedRow_mk] at this
    by_cases hAtW : w.1.1 = wall
    · have hVertex : position.datum.sourceEndpoint wall w.1.2 = w :=
        (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAtW.symm, rfl⟩
      rw [← hVertex] at hIncW hNdW
      by_cases hAnchorRel : (position.datum.vertexPartition wall).Rel anchor.1 w.1.2
      · obtain ⟨hAt, hRelW⟩ := (incident_sourceEndpoint_iff _ h.1).mp hIncW
        obtain ⟨label, hLabel⟩ := star.exists_edge_eq h.1.1.1 hAt
        have hWallH : (data.vertexPartition wall).Rel anchor.1 h.1.1.2 :=
          (hWallIff _).mp (hAnchorRel.trans hRelW)
        have hEqS := eq_survivorEdge position hConnected hGenus hValid label h.1 hLabel.symm
          hWallH h.2
        refine ⟨ResolutionAwayFromWall.retainedEdge (C) hDV.1 h,
          epv (C) (W4TargetPairings.Pairing.labelRight pairing label) position.split.bridge,
          hRowEq, ?_, ?_⟩
        · show Incident (C).datum ((C).oldSourceEdge h.1) _
          rw [hEqS]
          exact survivor_incident position hConnected hGenus hNoGlue geometry label
        · rw [nonDanglingValency_bridge_eq_three position profile hConnected hGenus hNoGlue
            geometry hValid hBg]
          omega
      · obtain ⟨first, vertex, hF, hE⟩ := exists_isPathEnd_ordinary (C) hRight profile.pattern
          anchor.1 hRes hDV hGenusC h hAnchorRel (hInjG _ hAnchorRel) (hValG _ hAnchorRel)
          hIncW hNdW
        exact ⟨first, vertex, hF.trans hRowEq, hE⟩
    · refine ⟨ResolutionAwayFromWall.retainedEdge (C) hDV.1 h,
        ResolutionAwayFromWall.retainedVertex (C) w, hRowEq, ?_, ?_⟩
      · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff (C) w hAtW h.1).mpr hIncW
      · rw [ResolutionAwayFromWall.nonDanglingValency_retainedVertex (C) hDV hGenusC w hAtW]
        exact hNdW
  intro e
  rcases ResolutionPruning.sourceEdge_cases (C) e.1 with ⟨old, hOld⟩ | ⟨s, hs⟩
  · have hOldS : ¬IsDangling position.datum old := fun h ↦ e.2
      (hOld ▸ (ResolutionPruning.isDangling_oldSourceEdge_iff (C) hDV hGenusC old).mpr h)
    have hE : e = ResolutionAwayFromWall.retainedEdge (C) hDV.1 ⟨old, hOldS⟩ := Subtype.ext hOld
    obtain ⟨first, vertex, hF, hEnd⟩ := hRetained ⟨old, hOldS⟩
    exact ⟨first, vertex, hF.trans (congrArg NonDanglingEdge.stablePath hE).symm, hEnd⟩
  · set u := e.1.1.2 with hu
    have hEu : e.1 = (C).newSourceEdge u := by
      rw [hs, hu, hs]
      exact newSourceEdge_repr (C) s
    by_cases hAnchorU : (data.vertexPartition wall).Rel anchor.1 u
    · by_cases hBridge : u ∈ position.split.bridgeSheets
      · have hBridgeWall : (data.vertexPartition wall).Rel anchor.1 position.split.bridge :=
          ((data.vertexPartition wall).mem_block_iff _ _).mp
            (position.split.minus_subset position.split.bridge_mem_minus)
        have hEq : (C).newSourceEdge u = (C).newSourceEdge position.split.bridge :=
          (newSourceEdge_eq_of_rel (C)
            ((candidate_newEdge_rel_iff position hConnected hGenus hNoGlue geometry hBridgeWall
              u).mpr ((position.split.newEdge_rel_bridge_iff u).mpr hBridge))).symm
        refine ⟨e, epv (C) false position.split.bridge, rfl, ?_, ?_⟩
        · rw [hEu, hEq]
          exact newSourceEdge_incident (C) false _
        · rw [nonDanglingValency_bridge_eq_three position profile hConnected hGenus hNoGlue
            geometry hValid hBg]
          omega
      · exfalso
        have hNotBoth : u ∉ endSheets position side ∨ u ∉ endSheets position (!side) := by
          by_contra hBoth
          simp only [not_or, not_not] at hBoth
          exact hBridge (mem_bridgeSheets_of position side hBoth.1 hBoth.2)
        apply e.2
        rw [hEu]
        rcases hNotBoth with h | h
        · exact newSourceEdge_isDangling_of_not_mem position hConnected hGenus hNoGlue geometry
            hValid hGenusC side h hAnchorU
        · exact newSourceEdge_isDangling_of_not_mem position hConnected hGenus hNoGlue geometry
            hValid hGenusC (!side) h hAnchorU
    · have hbU : ¬(position.datum.vertexPartition wall).Rel anchor.1 u :=
        (hWallIff u).not.mpr hAnchorU
      have hSurvU : ¬IsDangling (C).datum ((C).newSourceEdge u) := hEu ▸ e.2
      obtain ⟨old, hOldS, hRowNew⟩ := newSourceEdge_absorbed (C) hRight profile.pattern anchor.1
        hRes hDV hGenusC hbU (hInjG u hbU) (hValG u hbU) hSurvU
      obtain ⟨first, vertex, hF, hEnd⟩ := hRetained ⟨old, hOldS⟩
      have hE : e = ⟨(C).newSourceEdge u, hSurvU⟩ := Subtype.ext hEu
      refine ⟨first, vertex, ?_, hEnd⟩
      rw [hF, ← hRowNew, hE]

end PathEnds

/-! ## 12.  At the wall data of the outer walk -/

section Wall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk
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

variable (position : GeneralKReceipts.Position
    (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      wallStar (wd.hForest m) anchorBlock hAnchor) pairing
    (smallerSide (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor) pairing))
  (geometry : GeneralKReceipts.PairingBackground position.datum wallStar pairing
    anchorBlock.1)

/-- **The localized canonical background** of the non-anchor wall blocks, as a
hypothesis on `geometry`: on every non-anchor block the resolution is the
canonical W4 resolution localized to that block.

interface: equivalent to `geometry` agreeing with
`GeneralKBackground.localBackground` on every non-anchor block; it is inhabited
by `exists_localCanonicalBackground`.  It is used instead of
`GeneralKExitSetup.CanonicalBackground`, whose literal (unlocalized) equality is
not satisfiable in general (`GeneralKBackground.not_exists_literalBackground`). -/
abbrev LocalCanonicalBackground : Prop :=
  ∀ block, ¬(position.datum.vertexPartition ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 block →
    geometry.resolution block =
      canonicalLocal position.datum wallStar (vProf).pattern pairing block

local notation "cK" =>
  (GeneralKExitSetup.candK m wd wallStar anchorBlock hAnchor pairing position geometry)

omit geometry in
/-- **The background at the wall data.**  The localized canonical background exists. -/
theorem exists_localCanonicalBackground :
    ∃ geometry : GeneralKReceipts.PairingBackground position.datum wallStar pairing
        anchorBlock.1,
      LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing position geometry :=
  exists_pairingBackground position (vProf) (vVal)

/-- **Source genus.**  The candidate has the source genus of the wall datum. -/
theorem candidate_sourceGenus
    (hBg : LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing position geometry) :
    genus (cK).datum.sourceGraph =
      genus (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceGraph :=
  (candidate_sourceGenus_of_local position (vProf) (vConn) (vGen) (vNG) geometry hBg).trans
    (position.gauge.gaugedData_sourceGenus wallStar)

/-- **Trivalence of the general-`K` candidate.** -/
theorem candidate_trivalent
    (hBg : LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing position geometry)
    (v : (cK).datum.SourceVertex) :
    nonDanglingValency (cK).datum v ≤ 3 :=
  candidate_trivalent_of position (vProf) (vConn) (vGen) (vNG) geometry (vVal) hBg
    (fun w hw ↦ NonTrivalentValencyTwoExit.wallDatum_trivalent_away wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne (wd.hForest m) w hw)
    (fun _ ↦ NonTrivalentValencyFourRowEquivFinal.wall_starInjective wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne wallStar (wd.hForest m) _)
    (fun y hy ↦ NonTrivalentUniqueFourValent.nonDanglingValency_wallBlock_le_three wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne wallStar
      (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab wd.hOne
        (wd.hForest m))
      wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor _
      (fun hRel ↦ hy (hRel.trans
        (((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          ⟨wd.a, wd.hab⟩).rel_repr_left y))))
    v

/-- **The `K + K'` extra new-edge classes are dangling.** -/
theorem newEdge_isDangling_off_bridge
    (hBg : LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing position geometry)
    (sheet : Fin degree)
    (hSheet : sheet ∈ position.split.minusSheets \ position.split.plusSheets ∨
      sheet ∈ position.split.plusSheets \ position.split.minusSheets) :
    IsDangling (cK).datum ((cK).newSourceEdge sheet) :=
  newEdge_isDangling_off_bridge' position (vConn) (vGen) (vNG) geometry (vVal)
    (candidate_sourceGenus_of_local position (vProf) (vConn) (vGen) (vNG) geometry hBg) sheet
    hSheet

/-- **The bridge survives**, over *any* background geometry. -/
theorem bridge_not_isDangling :
    ¬IsDangling (cK).datum ((cK).newSourceEdge position.split.bridge) :=
  bridge_not_isDangling_general position (vConn) (vGen) (vNG) geometry (vVal)

/-- **Path ends.** -/
theorem hasPathEnds_candidate
    (hBg : LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing position geometry) :
    HasPathEnds (cK).datum :=
  hasPathEnds_of position (vProf) (vConn) (vGen) (vNG) geometry (vVal) hBg
    (fun _ ↦ NonTrivalentValencyFourRowEquivFinal.wall_starInjective wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne wallStar (wd.hForest m) _)
    (fun y hy ↦ NonTrivalentUniqueFourValent.nonDanglingValency_wallBlock_le_three wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne wallStar
      (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab wd.hOne
        (wd.hForest m))
      wd.coordinates (label m.base) wd.hRows wd.hZeroCoord anchorBlock hAnchor _
      (fun hRel ↦ hy (hRel.trans
        (((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          ⟨wd.a, wd.hab⟩).rel_repr_left y))))
    (WallDatumPathEnds.hasPathEnds_contractDatum_of_noContractedReturn wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne (wd.hForest m) wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord
      wd.hFacetZero
      (StablePathFacetContraction.noContractedReturn_of_fourStar wd.cover wd.fullDim wd.hc wd.hab
        wd.hOne wallStar))

omit geometry in
/-- **All source facts at once.**  At the wall data, for every general-`K` position,
there is a background geometry over which the candidate is valid, keeps the
source genus of the wall datum, is trivalent, has path ends, keeps its bridge,
and loses every other new-edge class of the anchor block.  These are all the
source inputs of `NonTrivalentValencyTwoExit.ofTypeChange` except the outgoing
presentation itself (for which see `GeneralKExit`). -/
theorem exists_candidate_sourceFacts :
    ∃ geometry : GeneralKReceipts.PairingBackground position.datum wallStar pairing
        anchorBlock.1,
      LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing position geometry ∧
      (GeneralKExitSetup.candK m wd wallStar anchorBlock hAnchor pairing position
        geometry).datum.Valid ∧
      genus (GeneralKExitSetup.candK m wd wallStar anchorBlock hAnchor pairing position
          geometry).datum.sourceGraph =
        genus (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceGraph ∧
      (∀ v, nonDanglingValency (GeneralKExitSetup.candK m wd wallStar anchorBlock hAnchor pairing
        position geometry).datum v ≤ 3) ∧
      HasPathEnds (GeneralKExitSetup.candK m wd wallStar anchorBlock hAnchor pairing position
        geometry).datum ∧
      ¬IsDangling (GeneralKExitSetup.candK m wd wallStar anchorBlock hAnchor pairing position
          geometry).datum
        ((GeneralKExitSetup.candK m wd wallStar anchorBlock hAnchor pairing position
          geometry).newSourceEdge position.split.bridge) ∧
      ∀ sheet, sheet ∈ position.split.minusSheets \ position.split.plusSheets ∨
          sheet ∈ position.split.plusSheets \ position.split.minusSheets →
        IsDangling (GeneralKExitSetup.candK m wd wallStar anchorBlock hAnchor pairing position
            geometry).datum
          ((GeneralKExitSetup.candK m wd wallStar anchorBlock hAnchor pairing position
            geometry).newSourceEdge sheet) := by
  obtain ⟨geometry, hBg⟩ := exists_localCanonicalBackground m wd wallStar anchorBlock hAnchor
    pairing position
  exact ⟨geometry, hBg, position.candidate_datum_valid (vConn) (vGen) (vNG) geometry (vVal),
    candidate_sourceGenus m wd wallStar anchorBlock hAnchor pairing position geometry hBg,
    candidate_trivalent m wd wallStar anchorBlock hAnchor pairing position geometry hBg,
    hasPathEnds_candidate m wd wallStar anchorBlock hAnchor pairing position geometry hBg,
    bridge_not_isDangling m wd wallStar anchorBlock hAnchor pairing position geometry,
    newEdge_isDangling_off_bridge m wd wallStar anchorBlock hAnchor pairing position geometry hBg⟩

end Wall


end DraismaVargas.Count.GeneralKSourceFacts
