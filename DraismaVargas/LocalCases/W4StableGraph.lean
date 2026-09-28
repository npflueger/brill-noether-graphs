import DraismaVargas.LocalCases.W4StableSource
import DraismaVargas.LocalCases.M11SourceGenus
import DraismaVargas.LocalCases.ResolutionPruning

/-!
# Stable-source prerequisites for the actual W4 candidates

`AuxR0SourceInput.presentedFamily` supplies literal path lists for the
determinant calculation.  Those lists are not themselves certified as the
actual `StablePath` rows of an outgoing datum.  This module records the
graph-theoretic receipts needed to construct such a row equivalence (built in
`W4OutgoingStableRows`): source-genus preservation, exact pruning of retained
old occurrences, and the local new-occurrence census.
-/

namespace DraismaVargas.LocalCases.W4StableGraph

open DraismaVargas.Infrastructure TargetExpansion
open ResolutionM11 W4Assembly GlobalW4 W4StableSource

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

/-! ## The local valency-one exclusion used by the W4 pictures -/

/-- If one surviving incident occurrence is known and every survivor is one
of it and a second incident occurrence, then the second occurrence survives.
Otherwise the surviving valency would be exactly one. -/
theorem second_survives_of_exhausted_pair
    {datum : GluingDatum target degree} (hConnected : datum.Connected)
    (vertex : datum.SourceVertex) (first second : datum.SourceEdge)
    (hFirstIncident : Incident datum first vertex)
    (hFirstSurvives : ¬ IsDangling datum first)
    (hExhaust : ∀ edge : datum.SourceEdge, Incident datum edge vertex →
      ¬ IsDangling datum edge → edge = first ∨ edge = second) :
    ¬ IsDangling datum second := by
  classical
  intro hSecondDangles
  have hIncidentSet : nonDanglingIncident datum vertex = {first} := by
    ext edge
    constructor
    · intro hMem
      obtain ⟨hSurvives, hIncident⟩ :=
        (mem_nonDanglingIncident datum vertex edge).mp hMem
      rcases hExhaust edge hIncident hSurvives with hEdge | hEdge
      · exact Finset.mem_singleton.mpr hEdge
      · exact (hSurvives (hEdge ▸ hSecondDangles)).elim
    · intro hMem
      rw [Finset.mem_singleton] at hMem
      subst edge
      exact (mem_nonDanglingIncident datum vertex first).mpr
        ⟨hFirstSurvives, hFirstIncident⟩
  have hOne : nonDanglingValency datum vertex = 1 := by
    rw [← card_nonDanglingIncident, hIncidentSet]
    simp
  exact NonDanglingValency.nonDanglingValency_ne_one datum hConnected vertex hOne

/-- If every survivor at a vertex would have to be one fixed incident
occurrence, that occurrence dangles: connected quotient sources have no
surviving-valency-one vertices. -/
theorem dangles_of_exhausted_singleton
    {datum : GluingDatum target degree} (hConnected : datum.Connected)
    (vertex : datum.SourceVertex) (only : datum.SourceEdge)
    (hOnlyIncident : Incident datum only vertex)
    (hExhaust : ∀ edge : datum.SourceEdge, Incident datum edge vertex →
      ¬ IsDangling datum edge → edge = only) :
    IsDangling datum only := by
  classical
  by_contra hOnlySurvives
  have hIncidentSet : nonDanglingIncident datum vertex = {only} := by
    ext edge
    constructor
    · intro hMem
      obtain ⟨hSurvives, hIncident⟩ :=
        (mem_nonDanglingIncident datum vertex edge).mp hMem
      exact Finset.mem_singleton.mpr (hExhaust edge hIncident hSurvives)
    · intro hMem
      rw [Finset.mem_singleton] at hMem
      subst edge
      exact (mem_nonDanglingIncident datum vertex only).mpr
        ⟨hOnlySurvives, hOnlyIncident⟩
  have hOne : nonDanglingValency datum vertex = 1 := by
    rw [← card_nonDanglingIncident, hIncidentSet]
    simp
  exact NonDanglingValency.nonDanglingValency_ne_one datum hConnected vertex hOne

/-- Every canonical W4 block resolution is a star in one orientation: one
endpoint is the old wall partition and the new-edge partition is the other. -/
theorem blockwiseResolution_isStar
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3) (anchor : Fin degree) :
    ((blockwiseResolution data star pattern pairing anchor).left =
        data.vertexPartition wall ∧
      (blockwiseResolution data star pattern pairing anchor).newEdge =
        (blockwiseResolution data star pattern pairing anchor).right) ∨
    ((blockwiseResolution data star pattern pairing anchor).right =
        data.vertexPartition wall ∧
      (blockwiseResolution data star pattern pairing anchor).newEdge =
        (blockwiseResolution data star pattern pairing anchor).left) := by
  cases hPattern : pattern anchor with
  | nd2 block =>
      unfold blockwiseResolution
      rw [hPattern]
      simp only [resolutionAt, ResolutionW4.nd2ResolutionForPairing,
        W4TargetPairings.FourStar.right_edge]
      by_cases hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second
      · unfold ResolutionW4.nd2Resolution
        rw [dif_pos hSame]
        cases hSide : W4TargetPairings.Pairing.labelRight pairing block.first <;>
          simp [splitResolutionAt, LocalResolution.reverse]
      · unfold ResolutionW4.nd2Resolution
        rw [dif_neg hSame]
        exact Or.inl ⟨rfl, rfl⟩
  | nd3 block =>
      unfold blockwiseResolution
      rw [hPattern]
      simp only [resolutionAt, ResolutionW4.nd3ResolutionForPairing]
      cases hSide : star.right pairing (star.edge (block.singletonLabel pairing)) <;>
        simp [ResolutionW4.nd3Resolution, ResolutionCoarseFine.fineResolution,
          LocalResolution.reverse]

/-- Pasting preserves the literal local left block selected by the containing
old wall block. -/
theorem wholeResolution_left_block
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (sheet : Fin degree) :
    (wholeResolution data star pattern pairing).left.block sheet =
      (blockwiseResolution data star pattern pairing
        ((data.vertexPartition wall).repr sheet)).left.block sheet := by
  simpa [wholeResolution, LocalResolution.paste, LocalResolution.pasteLeft] using
    (data.vertexPartition wall).paste_block
      (fun anchor ↦ (blockwiseResolution data star pattern pairing anchor).left)
      (fun anchor ↦
        (blockwiseResolution_contracts data star pattern pairing anchor).left_refines)
      sheet

/-- The corresponding block-local formula for the fresh endpoint. -/
theorem wholeResolution_right_block
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (sheet : Fin degree) :
    (wholeResolution data star pattern pairing).right.block sheet =
      (blockwiseResolution data star pattern pairing
        ((data.vertexPartition wall).repr sheet)).right.block sheet := by
  simpa [wholeResolution, LocalResolution.paste, LocalResolution.pasteRight] using
    (data.vertexPartition wall).paste_block
      (fun anchor ↦ (blockwiseResolution data star pattern pairing anchor).right)
      (fun anchor ↦
        (blockwiseResolution_contracts data star pattern pairing anchor).right_refines)
      sheet

/-- The corresponding block-local formula for the regrown edge. -/
theorem wholeResolution_newEdge_block
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (sheet : Fin degree) :
    (wholeResolution data star pattern pairing).newEdge.block sheet =
      (blockwiseResolution data star pattern pairing
        ((data.vertexPartition wall).repr sheet)).newEdge.block sheet := by
  simpa [wholeResolution, LocalResolution.paste, LocalResolution.pasteNewEdge] using
    (data.vertexPartition wall).paste_block
      (fun anchor ↦ (blockwiseResolution data star pattern pairing anchor).newEdge)
      (fun anchor ↦
        (blockwiseResolution data star pattern pairing anchor).edge_refines_left.trans
          (blockwiseResolution_contracts data star pattern pairing anchor).left_refines)
      sheet

/-- Reading an nd2 source picture recovers the exact blockwise resolution
pattern used by every actual candidate. -/
theorem blockPattern_eq_nd2_of_picture
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    (input : AuxR0SourceInput data star) (sourceBlock : WallBlock data wall)
    (block : Nd2Block) (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture) :
    input.activeProfile.blockPattern sourceBlock.1 = .nd2 block := by
  rw [input.activeProfile.blockPattern_anchor]
  change (input.activeProfile.classification sourceBlock).kind.pattern = .nd2 block
  rw [← input.blockPicture_kind sourceBlock, hPicture]
  rfl

/-- The analogous pattern recovery for an nd3 source picture. -/
theorem blockPattern_eq_nd3_of_picture
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    (input : AuxR0SourceInput data star) (sourceBlock : WallBlock data wall)
    (block : Nd3Block) (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture) :
    input.activeProfile.blockPattern sourceBlock.1 = .nd3 block := by
  rw [input.activeProfile.blockPattern_anchor]
  change (input.activeProfile.classification sourceBlock).kind.pattern = .nd3 block
  rw [← input.blockPicture_kind sourceBlock, hPicture]
  rfl

/-- Any actual W4 candidate assembled from the canonical pairing receipts
preserves the complete quotient-source genus. -/
theorem pairingCandidate_sourceGenus
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing) :
    genus receipts.candidate.datum.sourceGraph = genus data.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_stars
  exact blockwiseResolution_isStar data star pattern pairing

/-- Source-genus preservation for the exact candidate exposed by the
source-derived semantic family. -/
theorem candidate_sourceGenus
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    (input : AuxR0SourceInput data star) (pairing : Fin 3) :
    genus ((input.presentedFamily data star).candidate pairing).datum.sourceGraph =
      genus data.sourceGraph := by
  exact pairingCandidate_sourceGenus
    (input.auxProfile.pairingCounts pairing).toPairingReceipts

/-! ## Endpoint-side information for retained old occurrences -/

/-- A labelled old W4 occurrence assigned right is incident to its literal
fresh source endpoint. -/
theorem labelled_old_incident_fresh
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing)
    (label : Fin 4)
    (hRight : W4TargetPairings.Pairing.labelRight pairing label = true)
    (sheet : Fin degree) :
    Incident receipts.candidate.datum
      (receipts.candidate.oldSourceEdge
        (data.sourceEdge (star.edge label) sheet))
      (receipts.candidate.datum.sourceEndpoint (freshVertex target) sheet) := by
  have hAt := star.edge_mem_incidentEdges label
  have hSide : receipts.candidate.right (star.edge label) = true := by
    simpa only [PairingReceipts.candidate,
      W4TargetPairings.FourStar.right_edge] using hRight
  have hAtUp : occurrenceEquiv target wall receipts.candidate.right
      (some (star.edge label)) ∈
      GluingDatum.incidentEdges (freshVertex target) := by
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] at hAt ⊢
    rw [occurrenceEquiv_some]
    exact (oldEnds_incident_freshVertex_iff target wall
      receipts.candidate.right (star.edge label)).mpr ⟨hAt, hSide⟩
  have hIncident := incident_sourceEdge_sourceEndpoint receipts.candidate.datum
    (freshVertex target)
    (occurrenceEquiv target wall receipts.candidate.right
      (some (star.edge label))) hAtUp sheet
  have hEq : receipts.candidate.datum.sourceEdge
      (occurrenceEquiv target wall receipts.candidate.right
        (some (star.edge label))) sheet =
      receipts.candidate.oldSourceEdge
        (data.sourceEdge (star.edge label) sheet) :=
    ResolutionSideCounts.sourceEdge_old data wall receipts.candidate.right
      (wholeResolution data star pattern pairing)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _
        receipts.candidate.exterior) (star.edge label) sheet
  exact hEq ▸ hIncident

/-- The corresponding incidence statement for a labelled occurrence assigned
to the old expanded endpoint. -/
theorem labelled_old_incident_old
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing)
    (label : Fin 4)
    (hRight : W4TargetPairings.Pairing.labelRight pairing label = false)
    (sheet : Fin degree) :
    Incident receipts.candidate.datum
      (receipts.candidate.oldSourceEdge
        (data.sourceEdge (star.edge label) sheet))
      (receipts.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) := by
  have hAt := star.edge_mem_incidentEdges label
  have hSide : receipts.candidate.right (star.edge label) = false := by
    simpa only [PairingReceipts.candidate,
      W4TargetPairings.FourStar.right_edge] using hRight
  have hAtUp : occurrenceEquiv target wall receipts.candidate.right
      (some (star.edge label)) ∈
      GluingDatum.incidentEdges (oldVertex target wall) := by
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] at hAt ⊢
    rw [occurrenceEquiv_some]
    exact (oldEnds_incident_oldVertex_iff target wall
      receipts.candidate.right (star.edge label)).mpr ⟨hAt, hSide⟩
  have hIncident := incident_sourceEdge_sourceEndpoint receipts.candidate.datum
    (oldVertex target wall)
    (occurrenceEquiv target wall receipts.candidate.right
      (some (star.edge label))) hAtUp sheet
  have hEq : receipts.candidate.datum.sourceEdge
      (occurrenceEquiv target wall receipts.candidate.right
        (some (star.edge label))) sheet =
      receipts.candidate.oldSourceEdge
        (data.sourceEdge (star.edge label) sheet) :=
    ResolutionSideCounts.sourceEdge_old data wall receipts.candidate.right
      (wholeResolution data star pattern pairing)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _
        receipts.candidate.exterior) (star.edge label) sheet
  exact hEq ▸ hIncident

/-- The new occurrence meets its old expanded endpoint. -/
theorem new_incident_old
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing)
    (sheet : Fin degree) :
    Incident receipts.candidate.datum (receipts.candidate.newSourceEdge sheet)
      (receipts.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) :=
  Or.inl (congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge data wall
    receipts.candidate.right (wholeResolution data star pattern pairing)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _ receipts.candidate.exterior)
    sheet))

/-- The new occurrence also meets its fresh expanded endpoint. -/
theorem new_incident_fresh
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing)
    (sheet : Fin degree) :
    Incident receipts.candidate.datum (receipts.candidate.newSourceEdge sheet)
      (receipts.candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
  Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall
    receipts.candidate.right (wholeResolution data star pattern pairing)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _ receipts.candidate.exterior)
    sheet))

/-- An old occurrence incident at a fresh W4 endpoint lies in the indicated
old wall block and its star label is assigned to the fresh side. -/
theorem old_incident_fresh_info
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing)
    (sourceBlock : WallBlock data wall) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel sourceBlock.1 anchor)
    (old : data.SourceEdge)
    (hIncident : Incident receipts.candidate.datum
      (receipts.candidate.oldSourceEdge old)
      (receipts.candidate.datum.sourceEndpoint (freshVertex target) anchor)) :
    WallBlock.ofSheet data wall old.1.2 = sourceBlock ∧
      ∃ label : Fin 4, star.edge label = old.1.1 ∧
        W4TargetPairings.Pairing.labelRight pairing label = true := by
  let candidate := receipts.candidate
  let pasted := wholeResolution data star pattern pairing
  have hOutgoing := (incident_iff_target_mem_and_rel candidate.datum
    (candidate.oldSourceEdge old)
    (candidate.datum.sourceEndpoint (freshVertex target) anchor)).mp hIncident
  change occurrenceEquiv target wall candidate.right (some old.1.1) ∈
      GluingDatum.incidentEdges (freshVertex target) ∧
    pasted.right.Rel (pasted.right.repr anchor) old.1.2 at hOutgoing
  have hTargetRaw := hOutgoing.1
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
    true_and, occurrenceEquiv_some] at hTargetRaw
  have hSide := (oldEnds_incident_freshVertex_iff target wall candidate.right
    old.1.1).mp hTargetRaw
  have hRightRefines : pasted.right.Refines (data.vertexPartition wall) :=
    SheetPartition.IsJoin.right_refines (wholeResolution_contracts data star
      pattern pairing)
  have hWallRepr : (data.vertexPartition wall).Rel
      (pasted.right.repr anchor) anchor :=
    hRightRefines.rel (pasted.right.rel_repr_left anchor)
  have hWallOld : (data.vertexPartition wall).Rel sourceBlock.1 old.1.2 :=
    hAnchor.trans (hWallRepr.symm.trans (hRightRefines.rel hOutgoing.2))
  refine ⟨WallBlock.ofSheet_eq_of_rel data wall sourceBlock old.1.2 hWallOld, ?_⟩
  have hAt : old.1.1 ∈ GluingDatum.incidentEdges wall := by
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using hSide.1
  obtain ⟨label, hLabel⟩ := star.exists_edge_eq old.1.1 hAt
  refine ⟨label, hLabel, ?_⟩
  have hRight := hSide.2
  change star.right pairing old.1.1 = true at hRight
  rw [← hLabel] at hRight
  simpa only [W4TargetPairings.FourStar.right_edge] using hRight

/-- The analogous endpoint-side classification at the old expanded
endpoint. -/
theorem old_incident_old_info
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing)
    (sourceBlock : WallBlock data wall) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel sourceBlock.1 anchor)
    (old : data.SourceEdge)
    (hIncident : Incident receipts.candidate.datum
      (receipts.candidate.oldSourceEdge old)
      (receipts.candidate.datum.sourceEndpoint (oldVertex target wall) anchor)) :
    WallBlock.ofSheet data wall old.1.2 = sourceBlock ∧
      ∃ label : Fin 4, star.edge label = old.1.1 ∧
        W4TargetPairings.Pairing.labelRight pairing label = false := by
  let candidate := receipts.candidate
  let pasted := wholeResolution data star pattern pairing
  have hOutgoing := (incident_iff_target_mem_and_rel candidate.datum
    (candidate.oldSourceEdge old)
    (candidate.datum.sourceEndpoint (oldVertex target wall) anchor)).mp hIncident
  simp only [BalancedGlobal.Candidate.oldSourceEdge_target,
    BalancedGlobal.Candidate.oldSourceEdge_sheet,
    BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GluingDatum.sourceEndpoint,
    GlobalResolution.datum_vertexPartition_old_wall] at hOutgoing
  change occurrenceEquiv target wall candidate.right (some old.1.1) ∈
      GluingDatum.incidentEdges (oldVertex target wall) ∧
    pasted.left.Rel (pasted.left.repr anchor) old.1.2 at hOutgoing
  have hTargetRaw := hOutgoing.1
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
    true_and, occurrenceEquiv_some] at hTargetRaw
  have hSide := (oldEnds_incident_oldVertex_iff target wall candidate.right
    old.1.1).mp hTargetRaw
  have hLeftRefines : pasted.left.Refines (data.vertexPartition wall) :=
    SheetPartition.IsJoin.left_refines (wholeResolution_contracts data star
      pattern pairing)
  have hWallRepr : (data.vertexPartition wall).Rel
      (pasted.left.repr anchor) anchor :=
    hLeftRefines.rel (pasted.left.rel_repr_left anchor)
  have hWallOld : (data.vertexPartition wall).Rel sourceBlock.1 old.1.2 :=
    hAnchor.trans (hWallRepr.symm.trans (hLeftRefines.rel hOutgoing.2))
  refine ⟨WallBlock.ofSheet_eq_of_rel data wall sourceBlock old.1.2 hWallOld, ?_⟩
  have hAt : old.1.1 ∈ GluingDatum.incidentEdges wall := by
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using hSide.1
  obtain ⟨label, hLabel⟩ := star.exists_edge_eq old.1.1 hAt
  refine ⟨label, hLabel, ?_⟩
  have hRight := hSide.2
  change star.right pairing old.1.1 = false at hRight
  rw [← hLabel] at hRight
  simpa only [W4TargetPairings.FourStar.right_edge] using hRight

/-- If the fresh endpoint partition is literally the new-edge partition,
then every new occurrence incident to the endpoint block through `anchor` is
the same quotient occurrence as the one represented by `anchor`. -/
theorem new_eq_anchor_of_incident_fresh
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing)
    (anchor sheet : Fin degree)
    (hEndpoint : (wholeResolution data star pattern pairing).right.block anchor =
      (wholeResolution data star pattern pairing).newEdge.block anchor)
    (hIncident : Incident receipts.candidate.datum
      (receipts.candidate.newSourceEdge sheet)
      (receipts.candidate.datum.sourceEndpoint (freshVertex target) anchor)) :
    receipts.candidate.newSourceEdge sheet =
      receipts.candidate.newSourceEdge anchor := by
  let candidate := receipts.candidate
  let pasted := wholeResolution data star pattern pairing
  have hOutgoing := (incident_iff_target_mem_and_rel candidate.datum
    (candidate.newSourceEdge sheet)
    (candidate.datum.sourceEndpoint (freshVertex target) anchor)).mp hIncident
  change occurrenceEquiv target wall candidate.right none ∈
      GluingDatum.incidentEdges (freshVertex target) ∧
    pasted.right.Rel (pasted.right.repr anchor)
      (pasted.newEdge.repr sheet) at hOutgoing
  have hRightRel : pasted.right.Rel anchor (pasted.newEdge.repr sheet) :=
    (pasted.right.rel_repr_right anchor).trans hOutgoing.2
  have hMem : pasted.newEdge.repr sheet ∈ pasted.right.block anchor :=
    (pasted.right.mem_block_iff _ _).mpr hRightRel
  rw [hEndpoint] at hMem
  have hNewRel := (pasted.newEdge.mem_block_iff anchor
    (pasted.newEdge.repr sheet)).mp hMem
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change pasted.newEdge.repr sheet = pasted.newEdge.repr anchor
    exact (pasted.newEdge.repr_idem sheet).symm.trans hNewRel.symm

/-- The corresponding new-occurrence uniqueness statement at the old
expanded endpoint. -/
theorem new_eq_anchor_of_incident_old
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing)
    (anchor sheet : Fin degree)
    (hEndpoint : (wholeResolution data star pattern pairing).left.block anchor =
      (wholeResolution data star pattern pairing).newEdge.block anchor)
    (hIncident : Incident receipts.candidate.datum
      (receipts.candidate.newSourceEdge sheet)
      (receipts.candidate.datum.sourceEndpoint (oldVertex target wall) anchor)) :
    receipts.candidate.newSourceEdge sheet =
      receipts.candidate.newSourceEdge anchor := by
  let candidate := receipts.candidate
  let pasted := wholeResolution data star pattern pairing
  have hOutgoing := (incident_iff_target_mem_and_rel candidate.datum
    (candidate.newSourceEdge sheet)
    (candidate.datum.sourceEndpoint (oldVertex target wall) anchor)).mp hIncident
  simp only [BalancedGlobal.Candidate.newSourceEdge_target,
    BalancedGlobal.Candidate.newSourceEdge_sheet,
    BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GluingDatum.sourceEndpoint,
    GlobalResolution.datum_vertexPartition_old_wall] at hOutgoing
  change occurrenceEquiv target wall candidate.right none ∈
      GluingDatum.incidentEdges (oldVertex target wall) ∧
    pasted.left.Rel (pasted.left.repr anchor)
      (pasted.newEdge.repr sheet) at hOutgoing
  have hLeftRel : pasted.left.Rel anchor (pasted.newEdge.repr sheet) :=
    (pasted.left.rel_repr_right anchor).trans hOutgoing.2
  have hMem : pasted.newEdge.repr sheet ∈ pasted.left.block anchor :=
    (pasted.left.mem_block_iff _ _).mpr hLeftRel
  rw [hEndpoint] at hMem
  have hNewRel := (pasted.newEdge.mem_block_iff anchor
    (pasted.newEdge.repr sheet)).mp hMem
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change pasted.newEdge.repr sheet = pasted.newEdge.repr anchor
    exact (pasted.newEdge.repr_idem sheet).symm.trans hNewRel.symm

/-- Retained old occurrences are dangling in an actual W4 member exactly
when they were dangling in the wall datum. -/
theorem old_isDangling_iff
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (edge : data.SourceEdge) :
    IsDangling ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate pairing).oldSourceEdge edge) ↔
      IsDangling data edge :=
  ResolutionPruning.isDangling_oldSourceEdge_iff _ input.valid
    (candidate_sourceGenus input pairing) edge

/-- A dangling old wall block contributes no retained survivor to any actual
W4 candidate. -/
theorem old_dangles_of_dangling_picture
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall)
    (old_dangling : ∀ (edge : data.SourceEdge) (label : Fin 4),
      WallBlock.ofSheet data wall edge.1.2 = sourceBlock →
      star.edge label = edge.1.1 → IsDangling data edge)
    (_hPicture : input.blockPicture sourceBlock = .dangling old_dangling)
    (edge : data.SourceEdge) (label : Fin 4)
    (hBlock : WallBlock.ofSheet data wall edge.1.2 = sourceBlock)
    (hTarget : star.edge label = edge.1.1) :
    IsDangling ((input.presentedFamily data star).candidate pairing).datum
      (((input.presentedFamily data star).candidate pairing).oldSourceEdge edge) := by
  apply (old_isDangling_iff input pairing edge).mpr
  exact old_dangling edge label hBlock hTarget

/-- In an nd2 old wall block, every retained survivor of any actual member
is literally one of the two canonical active occurrences. -/
theorem old_survivor_eq_first_or_second_of_nd2
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (_hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (edge : data.SourceEdge)
    (hBlock : WallBlock.ofSheet data wall edge.1.2 = sourceBlock)
    (hStar : ∃ label : Fin 4, star.edge label = edge.1.1)
    (hSurvives : ¬ IsDangling
      ((input.presentedFamily data star).candidate pairing).datum
      (((input.presentedFamily data star).candidate pairing).oldSourceEdge edge)) :
    edge = data.sourceEdge (star.edge block.first) sourceBlock.1 ∨
      edge = data.sourceEdge (star.edge block.second) sourceBlock.1 := by
  apply picture.only_surviving edge hBlock hStar
  intro hOld
  exact hSurvives ((old_isDangling_iff input pairing edge).mpr hOld)

/-- In an nd3 old wall block, every retained survivor of any actual member
is literally the chosen occurrence on one of the three active branches. -/
theorem old_survivor_eq_active_of_nd3
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (_hPicture : input.blockPicture sourceBlock = .nd3 block picture)
    (edge : data.SourceEdge)
    (hBlock : WallBlock.ofSheet data wall edge.1.2 = sourceBlock)
    (hStar : ∃ label : Fin 4, star.edge label = edge.1.1)
    (hSurvives : ¬ IsDangling
      ((input.presentedFamily data star).candidate pairing).datum
      (((input.presentedFamily data star).candidate pairing).oldSourceEdge edge)) :
    ∃ label : Fin 4, label ∈ block.activeLabels ∧
      edge = data.sourceEdge (star.edge label) (picture.activeSheet label) := by
  apply picture.only_surviving edge hBlock hStar
  intro hOld
  exact hSurvives ((old_isDangling_iff input pairing edge).mpr hOld)

/-- Both canonical active occurrences of an nd2 wall block survive after
resolution.  This is a statement about literal source-edge occurrences, not
about the rows in the determinant presentation. -/
theorem nd2_first_second_survive
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block) :
    ¬ IsDangling ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate pairing).oldSourceEdge
          (data.sourceEdge (star.edge block.first) sourceBlock.1)) ∧
      ¬ IsDangling ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate pairing).oldSourceEdge
          (data.sourceEdge (star.edge block.second) sourceBlock.1)) := by
  constructor
  · exact ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
      picture.first_survives
  · exact ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
      picture.second_survives

/-- Exact retained-old survivor census in an nd2 wall block: among the four
star directions there are precisely the two canonical active occurrences.
Multiplicity is occurrence multiplicity; no assertion about stable rows is
made here. -/
theorem old_survives_iff_first_or_second_of_nd2
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (edge : data.SourceEdge)
    (hBlock : WallBlock.ofSheet data wall edge.1.2 = sourceBlock)
    (hStar : ∃ label : Fin 4, star.edge label = edge.1.1) :
    ¬ IsDangling ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate pairing).oldSourceEdge edge) ↔
      edge = data.sourceEdge (star.edge block.first) sourceBlock.1 ∨
        edge = data.sourceEdge (star.edge block.second) sourceBlock.1 := by
  constructor
  · exact old_survivor_eq_first_or_second_of_nd2 input pairing sourceBlock block
      picture hPicture edge hBlock hStar
  · intro hEdge
    rcases hEdge with rfl | rfl
    · exact (nd2_first_second_survive input pairing sourceBlock block picture).1
    · exact (nd2_first_second_survive input pairing sourceBlock block picture).2

/-- Every chosen active occurrence of an nd3 wall block survives in every
actual pairing candidate. -/
theorem nd3_active_survives
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (label : Fin 4) (hActive : label ∈ block.activeLabels) :
    ¬ IsDangling ((input.presentedFamily data star).candidate pairing).datum
      (((input.presentedFamily data star).candidate pairing).oldSourceEdge
        (data.sourceEdge (star.edge label) (picture.activeSheet label))) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
    (picture.active_survives label hActive)

/-- Exact retained-old survivor census in an nd3 wall block: among the four
star directions, the surviving occurrences are exactly the three chosen
active ones. -/
theorem old_survives_iff_active_of_nd3
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture)
    (edge : data.SourceEdge)
    (hBlock : WallBlock.ofSheet data wall edge.1.2 = sourceBlock)
    (hStar : ∃ label : Fin 4, star.edge label = edge.1.1) :
    ¬ IsDangling ((input.presentedFamily data star).candidate pairing).datum
        (((input.presentedFamily data star).candidate pairing).oldSourceEdge edge) ↔
      ∃ label : Fin 4, label ∈ block.activeLabels ∧
        edge = data.sourceEdge (star.edge label) (picture.activeSheet label) := by
  constructor
  · exact old_survivor_eq_active_of_nd3 input pairing sourceBlock block picture
      hPicture edge hBlock hStar
  · rintro ⟨label, hActive, rfl⟩
    exact nd3_active_survives input pairing sourceBlock block picture label hActive

/-! ## New-occurrence census -/

/-- If the two active nd2 branches lie on the same target side, every new
occurrence over that old wall block dangles.  At the opposite split endpoint
it would otherwise be the unique survivor. -/
theorem nd2_new_dangles_of_same
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
      W4TargetPairings.Pairing.labelRight pairing block.second)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet) :
    IsDangling ((input.presentedFamily data star).candidate pairing).datum
      (((input.presentedFamily data star).candidate pairing).newSourceEdge sheet) := by
  let pattern := input.activeProfile.blockPattern
  let receipts := (input.auxProfile.pairingCounts pairing).toPairingReceipts
  let candidate := receipts.candidate
  change IsDangling candidate.datum (candidate.newSourceEdge sheet)
  have hPattern : pattern sourceBlock.1 = .nd2 block :=
    blockPattern_eq_nd2_of_picture input sourceBlock block picture hPicture
  have hRepr : (data.vertexPartition wall).repr sheet = sourceBlock.1 :=
    hSheet.symm.trans sourceBlock.2
  cases hFirst : W4TargetPairings.Pairing.labelRight pairing block.first with
  | false =>
      have hSecond : W4TargetPairings.Pairing.labelRight pairing block.second = false := by
        rw [← hSame, hFirst]
      have hBlocks : (wholeResolution data star pattern pairing).right.block sheet =
          (wholeResolution data star pattern pairing).newEdge.block sheet := by
        rw [wholeResolution_right_block, wholeResolution_newEdge_block, hRepr]
        simp [blockwiseResolution, hPattern, resolutionAt,
          ResolutionW4.nd2ResolutionForPairing, hFirst, hSecond,
          ResolutionW4.nd2Resolution, splitResolutionAt]
      apply dangles_of_exhausted_singleton
        (candidate.datum_valid input.valid).1
        (candidate.datum.sourceEndpoint (freshVertex target) sheet)
        (candidate.newSourceEdge sheet)
        (new_incident_fresh receipts sheet)
      intro edge hIncident hSurvives
      rcases ResolutionPruning.sourceEdge_cases candidate edge with
        ⟨old, rfl⟩ | ⟨other, rfl⟩
      · obtain ⟨hBlock, label, hTarget, hSide⟩ :=
          old_incident_fresh_info receipts sourceBlock sheet hSheet old hIncident
        have hOld := (old_survives_iff_first_or_second_of_nd2 input pairing
          sourceBlock block picture hPicture old hBlock ⟨label, hTarget⟩).mp hSurvives
        rcases hOld with hOld | hOld
        · have hLabels : label = block.first := by
            apply star.edge_injective
            exact hTarget.trans (congrArg (fun e : data.SourceEdge ↦ e.1.1) hOld)
          rw [hLabels, hFirst] at hSide
          contradiction
        · have hLabels : label = block.second := by
            apply star.edge_injective
            exact hTarget.trans (congrArg (fun e : data.SourceEdge ↦ e.1.1) hOld)
          rw [hLabels, hSecond] at hSide
          contradiction
      · exact new_eq_anchor_of_incident_fresh receipts sheet other hBlocks hIncident
  | true =>
      have hSecond : W4TargetPairings.Pairing.labelRight pairing block.second = true := by
        rw [← hSame, hFirst]
      have hBlocks : (wholeResolution data star pattern pairing).left.block sheet =
          (wholeResolution data star pattern pairing).newEdge.block sheet := by
        rw [wholeResolution_left_block, wholeResolution_newEdge_block, hRepr]
        simp [blockwiseResolution, hPattern, resolutionAt,
          ResolutionW4.nd2ResolutionForPairing, hFirst, hSecond,
          ResolutionW4.nd2Resolution, splitResolutionAt]
      apply dangles_of_exhausted_singleton
        (candidate.datum_valid input.valid).1
        (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)
        (candidate.newSourceEdge sheet)
        (new_incident_old receipts sheet)
      intro edge hIncident hSurvives
      rcases ResolutionPruning.sourceEdge_cases candidate edge with
        ⟨old, rfl⟩ | ⟨other, rfl⟩
      · obtain ⟨hBlock, label, hTarget, hSide⟩ :=
          old_incident_old_info receipts sourceBlock sheet hSheet old hIncident
        have hOld := (old_survives_iff_first_or_second_of_nd2 input pairing
          sourceBlock block picture hPicture old hBlock ⟨label, hTarget⟩).mp hSurvives
        rcases hOld with hOld | hOld
        · have hLabels : label = block.first := by
            apply star.edge_injective
            exact hTarget.trans (congrArg (fun e : data.SourceEdge ↦ e.1.1) hOld)
          rw [hLabels, hFirst] at hSide
          contradiction
        · have hLabels : label = block.second := by
            apply star.edge_injective
            exact hTarget.trans (congrArg (fun e : data.SourceEdge ↦ e.1.1) hOld)
          rw [hLabels, hSecond] at hSide
          contradiction
      · exact new_eq_anchor_of_incident_old receipts sheet other hBlocks hIncident

/-- If the two active nd2 branches lie on opposite target sides, the unique
new occurrence over the old wall block survives.  At either endpoint it is
paired with exactly one of the two canonical retained survivors. -/
theorem nd2_new_survives_of_ne
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    [DecidableEq target.edges]
    (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (hNe : W4TargetPairings.Pairing.labelRight pairing block.first ≠
      W4TargetPairings.Pairing.labelRight pairing block.second) :
    ¬ IsDangling ((input.presentedFamily data star).candidate pairing).datum
      (((input.presentedFamily data star).candidate pairing).newSourceEdge
        sourceBlock.1) := by
  let pattern := input.activeProfile.blockPattern
  let receipts := (input.auxProfile.pairingCounts pairing).toPairingReceipts
  let candidate := receipts.candidate
  change ¬ IsDangling candidate.datum (candidate.newSourceEdge sourceBlock.1)
  have hPattern : pattern sourceBlock.1 = .nd2 block :=
    blockPattern_eq_nd2_of_picture input sourceBlock block picture hPicture
  cases hFirst : W4TargetPairings.Pairing.labelRight pairing block.first with
  | false =>
      have hSecond : W4TargetPairings.Pairing.labelRight pairing block.second = true := by
        cases h : W4TargetPairings.Pairing.labelRight pairing block.second <;>
          simp_all
      have hBlocks : (wholeResolution data star pattern pairing).left.block sourceBlock.1 =
          (wholeResolution data star pattern pairing).newEdge.block sourceBlock.1 := by
        rw [wholeResolution_left_block, wholeResolution_newEdge_block, sourceBlock.2]
        simp [blockwiseResolution, hPattern, resolutionAt,
          ResolutionW4.nd2ResolutionForPairing, hFirst, hSecond,
          ResolutionW4.nd2Resolution, joinedResolutionAt]
      apply second_survives_of_exhausted_pair
        (candidate.datum_valid input.valid).1
        (candidate.datum.sourceEndpoint (oldVertex target wall) sourceBlock.1)
        (candidate.oldSourceEdge
          (data.sourceEdge (star.edge block.first) sourceBlock.1))
        (candidate.newSourceEdge sourceBlock.1)
        (labelled_old_incident_old receipts block.first hFirst sourceBlock.1)
        (nd2_first_second_survive input pairing sourceBlock block picture).1
      intro edge hIncident hSurvives
      rcases ResolutionPruning.sourceEdge_cases candidate edge with
        ⟨old, rfl⟩ | ⟨other, rfl⟩
      · obtain ⟨hBlock, label, hTarget, hSide⟩ :=
          old_incident_old_info receipts sourceBlock sourceBlock.1 rfl old hIncident
        have hOld := (old_survives_iff_first_or_second_of_nd2 input pairing
          sourceBlock block picture hPicture old hBlock ⟨label, hTarget⟩).mp hSurvives
        rcases hOld with hOld | hOld
        · exact Or.inl (congrArg candidate.oldSourceEdge hOld)
        · have hLabels : label = block.second := by
            apply star.edge_injective
            exact hTarget.trans (congrArg (fun e : data.SourceEdge ↦ e.1.1) hOld)
          rw [hLabels, hSecond] at hSide
          contradiction
      · exact Or.inr
          (new_eq_anchor_of_incident_old receipts sourceBlock.1 other hBlocks hIncident)
  | true =>
      have hSecond : W4TargetPairings.Pairing.labelRight pairing block.second = false := by
        cases h : W4TargetPairings.Pairing.labelRight pairing block.second <;>
          simp_all
      have hBlocks : (wholeResolution data star pattern pairing).right.block sourceBlock.1 =
          (wholeResolution data star pattern pairing).newEdge.block sourceBlock.1 := by
        rw [wholeResolution_right_block, wholeResolution_newEdge_block, sourceBlock.2]
        simp [blockwiseResolution, hPattern, resolutionAt,
          ResolutionW4.nd2ResolutionForPairing, hFirst, hSecond,
          ResolutionW4.nd2Resolution, joinedResolutionAt]
      apply second_survives_of_exhausted_pair
        (candidate.datum_valid input.valid).1
        (candidate.datum.sourceEndpoint (freshVertex target) sourceBlock.1)
        (candidate.oldSourceEdge
          (data.sourceEdge (star.edge block.first) sourceBlock.1))
        (candidate.newSourceEdge sourceBlock.1)
        (labelled_old_incident_fresh receipts block.first hFirst sourceBlock.1)
        (nd2_first_second_survive input pairing sourceBlock block picture).1
      intro edge hIncident hSurvives
      rcases ResolutionPruning.sourceEdge_cases candidate edge with
        ⟨old, rfl⟩ | ⟨other, rfl⟩
      · obtain ⟨hBlock, label, hTarget, hSide⟩ :=
          old_incident_fresh_info receipts sourceBlock sourceBlock.1 rfl old hIncident
        have hOld := (old_survives_iff_first_or_second_of_nd2 input pairing
          sourceBlock block picture hPicture old hBlock ⟨label, hTarget⟩).mp hSurvives
        rcases hOld with hOld | hOld
        · exact Or.inl (congrArg candidate.oldSourceEdge hOld)
        · have hLabels : label = block.second := by
            apply star.edge_injective
            exact hTarget.trans (congrArg (fun e : data.SourceEdge ↦ e.1.1) hOld)
          rw [hLabels, hSecond] at hSide
          contradiction
      · exact Or.inr
          (new_eq_anchor_of_incident_fresh receipts sourceBlock.1 other hBlocks hIncident)

end DraismaVargas.LocalCases.W4StableGraph
