module

public import DraismaVargas.LocalCases.NonTrivalentValencyFourBackground
public import DraismaVargas.LocalCases.M11SourceGenus
public import DraismaVargas.LocalCases.ResolutionAwayFromWall
public import DraismaVargas.LocalCases.DanglingSideStructure
public import DraismaVargas.LocalCases.LimitChainCore

@[expose] public section

/-!
# Stable rows of the `K = 0` candidate above a four-valent wall

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 (rigidity above `w0`,
Lemma `lemma-above-w0`; the resolution of the unique four-valent vertex `A` into
two trivalent vertices `A_1^{(q)}, A_2^{(q)}` joined by the contracting edge
`h_1^{(q)}`; the common-minor argument of Lemma `lm:change-comb-type`) and
Section 5.2, Case `{v4-nd4}` (`K = 0`: `|A_+| = |A|`,
`|A_-| = k_alpha + k_beta - 1` and `k_1^{(q)} = k_alpha + k_beta - 1`).

This module begins the row dictionary for the outgoing candidate
`NonTrivalentValencyFourBackground.candidate`, whose validity and exact endpoint
and bridge sizes are proved there.

## What is proved here

* **Source genus is preserved.**  `candidate_sourceGenus` is unconditional:
  every wall block of the `K = 0` candidate carries a *star* resolution -- one
  endpoint keeps the wall partition and the new edge repeats the other endpoint
  -- on the anchor block because `selectedResolution` is built from
  `ResolutionCoarseFine.fineResolution`, and away from it because the
  localized guarded background is pasted from `W4Assembly.blockwiseResolution`,
  whose two block patterns are the split/joined and fine/reverse-fine stars.
  The blockwise Euler identity `#newEdge + 1 = #left + #right` then feeds
  `M11SourceGenus.candidate_sourceGenus_of_blockwise_euler`.

  This lemma is not decoration: it is the hypothesis `hGenus` of
  `ResolutionPruning.isDangling_oldSourceEdge_iff`,
  `ResolutionAwayFromWall.nonDanglingEdge_cases` and
  `ResolutionAwayFromWall.nonDanglingValency_retainedVertex`, i.e. of every
  statement that transports danglingness and surviving stars from the incoming
  wall datum to the outgoing candidate.  Without it no row dictionary can be
  written down at all.

* **The four-branch classifier survives the gauge.**  `gaugedSource` produces
  `FourBranchAnchor (gaugedData ...) star (gaugedAnchor ...)` from the incoming
  `FourBranchAnchor data star anchor`.  The candidate lives over the *gauged*
  datum, so every later statement about surviving occurrences at the anchor has
  to be read there; the gauge is a `BlockPreservingBranchSwap.branchSwapOfPerm`,
  its vertex permutation at `wall` is the identity and each of its edge
  permutations moves sheets only inside wall blocks, so `activeLabels` is
  literally unchanged (`activeLabels_gauged`) and the surviving valency at the
  anchor is still four (`nonDanglingValency_gaugedAnchor`).  Target-direction
  injectivity is then recovered from
  `W4StableSource.nonDanglingStarInjective_of_card_activeLabels_eq_nonDanglingValency`
  rather than transported by hand.

* **The two `K = 0` endpoint vertices.**  `endpointVertex` names the actual
  outgoing source vertex on each side of the new target edge above the anchor,
  and `endpointVertex_blockCard` restates the exact `K = 0` sizes
  (`|A_-| = k_alpha + k_beta - 1`, `|A_+| = |A|`) as the block cardinalities of
  those vertices in the outgoing gluing datum, rather than as a property of the
  local resolution.  `bridgeEdge` names the new bridge occurrence; its exact
  index `k_1 = k_alpha + k_beta - 1` is
  `NonTrivalentValencyFourBackground.candidate_newSourceEdge_index_add_one'`.
  `bridgeEdge_incident` and `retainedEdge_incident` give the three actual
  incidences at the endpoint carried by one sheet, and `endpointVertex_eq`
  identifies two sheets of the anchor block that name the same endpoint vertex
  with the relation of the prescribed endpoint partition.

* **The bridge is a genuine edge of the resolved type.**
  `bridgeEdge_not_isDangling` proves that the new occurrence survives as soon as
  each of its two endpoint vertices carries one surviving occurrence: a dangling
  side of the bridge contains one of its endpoints, and
  `DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side` then kills every
  occurrence there.  `bridgeEdge_not_isDangling_of_survivors` is the concrete
  form, taking one surviving old occurrence on each side of the prescribed
  pairing.  This is the Lean content of the paper's statement that `A` resolves
  into two trivalent vertices *joined by* `h_1^{(q)}`, as opposed to acquiring a
  pendant tree.

## What is not proved here

This file stops short of the honest `W4StableSource.StableLengthMatrixLabelling`
of the candidate.  Three further steps are needed, in this order; the later
modules `NonTrivalentValencyFourDictionary`, `NonTrivalentValencyFourRowEquiv`,
`NonTrivalentValencyFourRowDictionary` and `NonTrivalentValencyFourExit` carry
them out.

1. `nonDanglingValency (endpointVertex ...) = 3` at both endpoints.  The
   surviving star at `A_-` is
   `{bridge, retained alpha-survivor, retained beta-survivor}`.
   `subset` is the incidence lemmas below plus
   `ResolutionSurvival.not_isDangling_oldSourceEdge`; survival of the bridge
   follows from `DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side`
   applied to whichever end of a hypothetical dangling side is an endpoint
   vertex, because that endpoint already carries a surviving retained
   occurrence; exhaustion is `ResolutionAwayFromWall.nonDanglingEdge_cases`
   together with `gaugedSource.target_injective` for the retained occurrences
   and, on the side carrying the unchanged wall partition, the observation that
   a singleton fine block has non-dangling valency zero (it is not one, by
   `NonDanglingValency.nonDanglingValency_ne_one`, and every old occurrence at it
   is dangling by injectivity), so the new occurrence there is dangling.
   The two halves that this file supplies are `endpointVertex_eq` (so the four
   survivors, which sit on four different sheets of the anchor block, can be
   moved onto the selected representative) and `bridgeEdge_not_isDangling`.
   The remaining step is the exhaustion, i.e. the incidence census
   `nonDanglingIncident (endpointVertex ...)`.
2. The retained-row descent `StablePath (gaugedData ...) -> StablePath C.datum`.
   Off the wall this is `ResolutionAwayFromWall.consecutive_retained_of_away`;
   at a non-anchor wall block of surviving valency two it needs the same
   endpoint analysis as (1), applied to the block's own nd2/nd3 pattern.
3. Hence also the labelling itself, and `AgreeOffColumn` against the incoming
   full-dimensional matrix.  `AgreeOffColumn` additionally needs the *other*
   half of the dictionary, from the incoming full-dimensional cover to the wall
   datum through `GluingContraction.contractDatum`; that transport is not a
   consequence of anything in this file.

Nothing in this file assumes a row dictionary, a stable type, an outgoing
full-dimensional presentation or any receipt about the candidate.

## Consumers

The boundary dispatcher for Part II Case `{v4-nd4}`, and the
nonsingularity/exit package built on `NonTrivalentLinkMatrix`
(`NonTrivalentValencyFourExit`).
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyFourRows

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.ResolutionW4
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.LocalCases.NonTrivalentValencyFourBackground

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall} {anchor : WallBlock data wall}
  (source : FourBranchAnchor data star anchor) (pairing : Fin 3)
  (hNoGlue : DanglingEdgeNoGlue data)
  (hRamification : data.localRamification wall anchor = 0)

/-! ## 1.  Star resolutions and the blockwise Euler identity -/

/-- One endpoint of the local resolution keeps the wall partition and the new
edge repeats the other endpoint.  This is the shape
`M11SourceGenus.paste_block_euler` calls a star. -/
def IsStar {d : ℕ} (partition : SheetPartition d)
    (resolution : LocalResolution d) : Prop :=
  (resolution.left = partition ∧ resolution.newEdge = resolution.right) ∨
    (resolution.right = partition ∧ resolution.newEdge = resolution.left)

theorem euler_of_isStar {d : ℕ} {partition : SheetPartition d}
    {res : LocalResolution d} (h : IsStar partition res) (sheet : Fin d) :
    res.newEdge.blockCountWithin partition sheet + 1 =
      res.left.blockCountWithin partition sheet +
        res.right.blockCountWithin partition sheet := by
  rcases h with ⟨hl, hn⟩ | ⟨hr, hn⟩
  · rw [hl, hn, SheetPartition.blockCountWithin_self]
    omega
  · rw [hr, hn, SheetPartition.blockCountWithin_self]

theorem isStar_fineResolution {d : ℕ} (partition fine : SheetPartition d)
    (hFine : fine.Refines partition) :
    IsStar partition (fineResolution partition fine hFine) := Or.inr ⟨rfl, rfl⟩

theorem isStar_reverse {d : ℕ} {partition : SheetPartition d}
    {res : LocalResolution d} (h : IsStar partition res) :
    IsStar partition res.reverse := by
  rcases h with ⟨hl, hn⟩ | ⟨hr, hn⟩
  · exact Or.inr ⟨hl, hn⟩
  · exact Or.inl ⟨hr, hn⟩

theorem isStar_splitResolutionAt {d : ℕ} (partition : SheetPartition d)
    (a : Fin d) : IsStar partition (splitResolutionAt partition a) :=
  Or.inl ⟨rfl, rfl⟩

theorem isStar_joinedResolutionAt {d : ℕ} (partition : SheetPartition d) :
    IsStar partition (joinedResolutionAt partition) := Or.inl ⟨rfl, rfl⟩

theorem isStar_nd2Resolution {d : ℕ} (partition : SheetPartition d) (a : Fin d)
    (x y : Bool) : IsStar partition (nd2Resolution partition a x y) := by
  unfold nd2Resolution
  split_ifs
  · exact isStar_reverse (isStar_splitResolutionAt partition a)
  · exact isStar_splitResolutionAt partition a
  · exact isStar_joinedResolutionAt partition

theorem isStar_nd3Resolution {d : ℕ} (partition fine : SheetPartition d)
    (hFine : fine.Refines partition) (b : Bool) :
    IsStar partition (nd3Resolution partition fine hFine b) := by
  unfold nd3Resolution
  split_ifs
  · exact isStar_reverse (isStar_fineResolution partition fine hFine)
  · exact isStar_fineResolution partition fine hFine

/-- Every canonical W4 block pattern resolves its wall block into a star. -/
theorem isStar_blockwiseResolution (pattern : Fin degree → BlockPattern)
    (block : Fin degree) :
    IsStar (data.vertexPartition wall)
      (blockwiseResolution data star pattern pairing block) := by
  unfold blockwiseResolution resolutionAt
  cases pattern block with
  | nd2 b => exact isStar_nd2Resolution _ _ _ _
  | nd3 b => exact isStar_nd3Resolution _ _ _ _

/-- The prescribed `K = 0` resolution of the anchor block is a star: the new
bridge class is the fine endpoint on the smaller side, and the other endpoint
keeps the whole old wall block. -/
theorem isStar_selectedResolution :
    IsStar
      ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall)
      (selectedResolution source pairing hNoGlue hRamification) := by
  unfold selectedResolution baseResolution
  by_cases hSide : smallerSide source pairing
  · rw [ite_eq_left hSide]
    exact isStar_reverse (isStar_fineResolution _ _ _)
  · rw [ite_eq_right hSide]
    exact isStar_fineResolution _ _ _

/-! ## 2.  The outgoing candidate preserves the source genus -/

variable (profile : OrdinaryBlockProfile data star anchor.1)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (hValid : data.Valid)

/-- Off the anchor block, the assembled candidate really uses the guarded
background resolution. -/
theorem candidate_resolution_of_not_wall_rel (block : Fin degree)
    (hBlock : ¬ ((gaugedData source pairing hNoGlue hRamification).vertexPartition
      wall).Rel anchor.1 block) :
    (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
      hRamification profile hConnected hGenus hValid).resolution block =
      (pairingBackground source pairing hNoGlue hRamification profile hConnected
        hGenus hValid).resolution block := by
  unfold NonTrivalentValencyFourBackground.candidate PrescribedPairing.candidate
    PrescribedPairing.PairingBackground.background
    GlobalM11Arbitrary.Background.install
  exact LocalResolution.onBlock_of_not_rel _ _ _ _ _ hBlock

/-- **The `K = 0` candidate does not change the source genus.**  No receipt is
supplied: the anchor block's star is the prescribed `K = 0` resolution and every
other block's star is the canonical W4 pattern of the guarded census. -/
theorem candidate_sourceGenus :
    genus (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
        hRamification profile hConnected hGenus hValid).datum.sourceGraph =
      genus (gaugedData source pairing hNoGlue hRamification).sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_blockwise_euler
  intro block hCanonical
  by_cases hBlock :
      ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).Rel
        anchor.1 block
  · rw [show (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
        hRamification profile hConnected hGenus hValid).resolution block =
          selectedResolution source pairing hNoGlue hRamification from
        PrescribedPairing.candidate_resolution_of_wall_rel source pairing hNoGlue
          hRamification _ hConnected hGenus block hBlock]
    exact euler_of_isStar
      (isStar_selectedResolution source pairing hNoGlue hRamification) block
  · rw [candidate_resolution_of_not_wall_rel source pairing hNoGlue hRamification
      profile hConnected hGenus hValid block hBlock]
    have hRes :
        (pairingBackground source pairing hNoGlue hRamification profile
          hConnected hGenus hValid).resolution block =
          BlockLocalBackground.localizedResolution source pairing hNoGlue
            hRamification
            (blockLocalBackground source pairing hNoGlue hRamification profile
              hConnected hGenus hValid) block hBlock := dite_eq_right hBlock
    rw [hRes]
    unfold BlockLocalBackground.localizedResolution
    rw [LocalResolution.pasteNewEdge_blockCountWithin,
      LocalResolution.pasteLeft_blockCountWithin,
      LocalResolution.pasteRight_blockCountWithin, hCanonical,
      LocalResolution.onBlock_of_rel _ _ _ _ _
        (rfl : ((gaugedData source pairing hNoGlue hRamification).vertexPartition
          wall).Rel block block)]
    exact euler_of_isStar
      (isStar_blockwiseResolution (data :=
        gaugedData source pairing hNoGlue hRamification) (star := star) pairing
        profile.pattern block) block

/-! ## 3.  The four-branch classifier in the gauged datum -/

/-- The chosen gauge permutation never leaves a wall block. -/
theorem permutation_rel (sheet : Fin degree) :
    (data.vertexPartition wall).Rel
      (permutation source pairing hNoGlue hRamification sheet) sheet :=
  BlockPreservingBranchSwap.rel_of_stabilizes_block (data.vertexPartition wall)
    anchor.1 (permutation source pairing hNoGlue hRamification)
    (permutation_inside source pairing hNoGlue hRamification)
    (permutation_outside source pairing hNoGlue hRamification) sheet

theorem gauge_edgePermutation_rel (edge : target.edges) (sheet : Fin degree) :
    (data.vertexPartition wall).Rel
      ((relabeling source pairing hNoGlue hRamification).edgePermutation edge
        sheet) sheet := by
  show (data.vertexPartition wall).Rel
    (GluingDatum.SheetRelabeling.togglePermutation _
      (permutation source pairing hNoGlue hRamification) sheet) sheet
  unfold GluingDatum.SheetRelabeling.togglePermutation
  split_ifs
  · exact permutation_rel source pairing hNoGlue hRamification sheet
  · rfl

theorem gauge_vertexPermutation_wall :
    (relabeling source pairing hNoGlue hRamification).vertexPermutation wall =
      Equiv.refl (Fin degree) := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.vertexMoved wall _ _ wall)
    (permutation source pairing hNoGlue hRamification) = _
  rw [TargetBranchRegion.vertexMoved_wall]
  rfl

theorem gauged_isDangling_iff (hValid : data.Valid) (edge : target.edges)
    (sheet : Fin degree) :
    IsDangling (gaugedData source pairing hNoGlue hRamification)
        ((gaugedData source pairing hNoGlue hRamification).sourceEdge edge
          ((relabeling source pairing hNoGlue hRamification).edgePermutation
            edge sheet)) ↔
      IsDangling data (data.sourceEdge edge sheet) := by
  have h := SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff
    (relabeling source pairing hNoGlue hRamification) hValid.1
    (data.sourceEdge edge sheet)
  rw [SheetRelabelPruning.sourceEdgeEquiv_sourceEdge] at h
  exact h

theorem gauged_rel_iff (a b : Fin degree) :
    ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).Rel
        a b ↔ (data.vertexPartition wall).Rel a b := by
  rw [gaugedData_vertexPartition_wall source pairing hNoGlue hRamification]

/-- The distinguished wall block, read in the gauged datum. -/
noncomputable def gaugedAnchor :
    WallBlock (gaugedData source pairing hNoGlue hRamification) wall :=
  ⟨anchor.1, by
    rw [gaugedData_vertexPartition_wall source pairing hNoGlue hRamification]
    exact anchor.2⟩

/-- The gauge changes no active target branch at the anchor block. -/
theorem activeLabels_gauged (hValid : data.Valid) :
    activeLabels (gaugedData source pairing hNoGlue hRamification) star
        (gaugedAnchor source pairing hNoGlue hRamification) =
      activeLabels data star anchor := by
  ext label
  rw [mem_activeLabels_iff, mem_activeLabels_iff]
  set π := (relabeling source pairing hNoGlue hRamification).edgePermutation
    (star.edge label) with hπ
  constructor
  · rintro ⟨sheet, hRel, hSurv⟩
    have hRel' : (data.vertexPartition wall).Rel anchor.1 sheet :=
      (gauged_rel_iff source pairing hNoGlue hRamification anchor.1 sheet).mp hRel
    refine ⟨π.symm sheet, ?_, ?_⟩
    · refine hRel'.trans ?_
      have := gauge_edgePermutation_rel source pairing hNoGlue hRamification
        (star.edge label) (π.symm sheet)
      rw [← hπ, Equiv.apply_symm_apply] at this
      exact this
    · intro hDangling
      apply hSurv
      have := (gauged_isDangling_iff source pairing hNoGlue hRamification hValid
        (star.edge label) (π.symm sheet)).mpr hDangling
      rwa [← hπ, Equiv.apply_symm_apply] at this
  · rintro ⟨sheet, hRel, hSurv⟩
    refine ⟨π sheet, ?_, ?_⟩
    · refine (gauged_rel_iff source pairing hNoGlue hRamification anchor.1
        (π sheet)).mpr ?_
      exact hRel.trans (gauge_edgePermutation_rel source pairing hNoGlue
        hRamification (star.edge label) sheet).symm
    · intro hDangling
      exact hSurv ((gauged_isDangling_iff source pairing hNoGlue hRamification
        hValid (star.edge label) sheet).mp hDangling)

theorem gauged_sourceVertex_eq :
    (relabeling source pairing hNoGlue hRamification).sourceVertexEquiv
        (WallBlock.sourceVertex data wall anchor) =
      WallBlock.sourceVertex (gaugedData source pairing hNoGlue hRamification)
        wall (gaugedAnchor source pairing hNoGlue hRamification) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · show (relabeling source pairing hNoGlue hRamification).vertexPermutation wall
        ((data.vertexPartition wall).repr anchor.1) =
      ((gaugedData source pairing hNoGlue hRamification).vertexPartition
        wall).repr anchor.1
    rw [gauge_vertexPermutation_wall source pairing hNoGlue hRamification,
      gaugedData_vertexPartition_wall source pairing hNoGlue hRamification]
    rfl

/-- The anchor block still has surviving valency four after the gauge. -/
theorem nonDanglingValency_gaugedAnchor (hValid : data.Valid) :
    nonDanglingValency (gaugedData source pairing hNoGlue hRamification)
      (WallBlock.sourceVertex (gaugedData source pairing hNoGlue hRamification)
        wall (gaugedAnchor source pairing hNoGlue hRamification)) = 4 := by
  rw [← gauged_sourceVertex_eq source pairing hNoGlue hRamification]
  exact (SheetRelabelStable.nonDanglingValency_map
    (relabeling source pairing hNoGlue hRamification) hValid.1
    (WallBlock.sourceVertex data wall anchor)).trans
      source.nonDanglingValency_eq_four

/-- **The four-branch classifier survives the block-preserving branch gauge.**
Every target-star direction still has a surviving occurrence at the anchor, and
target-direction injectivity there is recovered from the valency count rather
than transported. -/
theorem gaugedSource (hValid : data.Valid) :
    FourBranchAnchor (gaugedData source pairing hNoGlue hRamification) star
      (gaugedAnchor source pairing hNoGlue hRamification) where
  active_all := by
    rw [activeLabels_gauged source pairing hNoGlue hRamification hValid]
    exact source.active_all
  target_injective := by
    apply nonDanglingStarInjective_of_card_activeLabels_eq_nonDanglingValency
    rw [activeLabels_gauged source pairing hNoGlue hRamification hValid,
      source.active_all,
      nonDanglingValency_gaugedAnchor source pairing hNoGlue hRamification hValid]
    simp

/-! ## 4.  The two `K = 0` endpoint vertices and the bridge occurrence -/

/-- The prescribed target pairing really is the candidate's side assignment. -/
theorem candidate_right :
    (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
      hRamification profile hConnected hGenus hValid).right =
      star.right pairing := rfl

/-- The resolution used on every sheet of the anchor block. -/
theorem candidate_resolution_eq_selected (block : Fin degree)
    (hRel : ((gaugedData source pairing hNoGlue hRamification).vertexPartition
      wall).Rel anchor.1 block) :
    (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
      hRamification profile hConnected hGenus hValid).resolution block =
      selectedResolution source pairing hNoGlue hRamification :=
  PrescribedPairing.candidate_resolution_of_wall_rel source pairing hNoGlue
    hRamification _ hConnected hGenus block hRel

theorem candidate_resolution_anchor' :
    (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
      hRamification profile hConnected hGenus hValid).resolution anchor.1 =
      selectedResolution source pairing hNoGlue hRamification :=
  PrescribedPairing.candidate_resolution_anchor source pairing hNoGlue
    hRamification _ hConnected hGenus

/-- The actual outgoing source vertex above one side of the new target edge,
on a chosen sheet. -/
noncomputable def endpointVertex (sideValue : Bool) (sheet : Fin degree) :
    (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
      hRamification profile hConnected hGenus hValid).datum.SourceVertex :=
  (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
      hRamification profile hConnected hGenus hValid).datum.sourceEndpoint
    (if sideValue then freshVertex target else oldVertex target wall) sheet

/-- The new bridge occurrence of the prescribed `K = 0` resolution. -/
noncomputable def bridgeEdge (sheet : Fin degree) :
    (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
      hRamification profile hConnected hGenus hValid).datum.SourceEdge :=
  (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
    hRamification profile hConnected hGenus hValid).newSourceEdge sheet

/-- The bridge occurrence joins the two endpoint vertices carried by its sheet:
this is the edge `h_1^{(q)}` of Part II Section 5.1. -/
theorem bridgeEdge_incident (sideValue : Bool) (sheet : Fin degree) :
    Incident
      (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
        hRamification profile hConnected hGenus hValid).datum
      (bridgeEdge source pairing hNoGlue hRamification profile hConnected hGenus
        hValid sheet)
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid sideValue sheet) := by
  cases sideValue
  · exact Or.inl (congrArg Prod.fst
      (GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet))
  · exact Or.inr (congrArg Prod.snd
      (GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet))

/-- A retained old occurrence above a wall-incident target edge meets the
endpoint vertex on the side the prescribed pairing assigns to that edge. -/
theorem retainedEdge_incident (edge : target.edges)
    (hAt : edge ∈ GluingDatum.incidentEdges wall) (sideValue : Bool)
    (hSide : star.right pairing edge = sideValue) (sheet : Fin degree) :
    Incident
      (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
        hRamification profile hConnected hGenus hValid).datum
      ((NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
          hRamification profile hConnected hGenus hValid).oldSourceEdge
        ((gaugedData source pairing hNoGlue hRamification).sourceEdge edge sheet))
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid sideValue sheet) := by
  cases sideValue
  · exact LimitChainCore.oldSourceEdge_incident_old _ edge hAt hSide sheet
  · exact M11SplitSurvival.oldSourceEdge_incident_fresh _ edge hAt hSide sheet

/-- **The exact `K = 0` endpoint sizes, on the actual outgoing source vertices.**
On the smaller side the endpoint class has `k_alpha + k_beta - 1` sheets; on the
other side it is the whole old wall block `A`.  This is
`NonTrivalentValencyFourBackground.candidate_endpoint_blockCard_add_one'` read in
the outgoing gluing datum rather than in the local resolution. -/
theorem endpointVertex_blockCard (sideValue : Bool) :
    ((NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
        hRamification profile hConnected hGenus hValid).datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).blockCard
        (selectedRepresentative source pairing) + 1 =
      if sideValue = smallerSide source pairing then
        sideIndex source pairing (smallerSide source pairing)
      else (data.vertexPartition wall).blockCard anchor.1 + 1 := by
  have hRel : ((gaugedData source pairing hNoGlue hRamification).vertexPartition
      wall).Rel anchor.1 (selectedRepresentative source pairing) :=
    (gauged_rel_iff source pairing hNoGlue hRamification _ _).mpr
      (source.sheet_wall_rel _)
  have hReprRel : ((gaugedData source pairing hNoGlue hRamification).vertexPartition
      wall).Rel anchor.1
      (((gaugedData source pairing hNoGlue hRamification).vertexPartition
        wall).repr (selectedRepresentative source pairing)) :=
    hRel.trans (((gaugedData source pairing hNoGlue hRamification).vertexPartition
      wall).rel_repr_right _)
  rw [← candidate_endpoint_blockCard_add_one' source pairing hNoGlue hRamification
    profile hConnected hGenus hValid sideValue]
  congr 1
  cases sideValue
  · show ((NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
        hRamification profile hConnected hGenus hValid).datum.vertexPartition
          (oldVertex target wall)).blockCard
        (selectedRepresentative source pairing) = _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
    rw [LocalResolution.paste_left_blockCard,
      candidate_resolution_eq_selected source pairing hNoGlue hRamification
        profile hConnected hGenus hValid _ hReprRel,
      candidate_resolution_anchor' source pairing hNoGlue hRamification profile
        hConnected hGenus hValid]
    simp
  · show ((NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
        hRamification profile hConnected hGenus hValid).datum.vertexPartition
          (freshVertex target)).blockCard
        (selectedRepresentative source pairing) = _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]
    rw [LocalResolution.paste_right_blockCard,
      candidate_resolution_eq_selected source pairing hNoGlue hRamification
        profile hConnected hGenus hValid _ hReprRel,
      candidate_resolution_anchor' source pairing hNoGlue hRamification profile
        hConnected hGenus hValid]
    simp

/-- Two sheets of the anchor block name the same outgoing endpoint vertex
exactly when the prescribed endpoint partition relates them.  On the smaller
side that partition is the fine `K = 0` endpoint, on the other side the whole
old wall block. -/
theorem endpointVertex_eq (sideValue : Bool) {a b : Fin degree}
    (hA : ((gaugedData source pairing hNoGlue hRamification).vertexPartition
      wall).Rel anchor.1 a)
    (hRel : (endpointForSide source pairing hNoGlue hRamification sideValue).Rel
      a b) :
    endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid sideValue a =
      endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid sideValue b := by
  have hReprRel : ((gaugedData source pairing hNoGlue hRamification).vertexPartition
      wall).Rel anchor.1
      (((gaugedData source pairing hNoGlue hRamification).vertexPartition
        wall).repr a) :=
    hA.trans (((gaugedData source pairing hNoGlue hRamification).vertexPartition
      wall).rel_repr_right a)
  have hSelected := candidate_resolution_eq_selected source pairing hNoGlue
    hRamification profile hConnected hGenus hValid _ hReprRel
  apply (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr
  refine ⟨rfl, ?_⟩
  refine Eq.trans ?_
    (((NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
      hRamification profile hConnected hGenus hValid).datum.vertexPartition
        _).rel_repr_right b)
  cases sideValue
  · show ((NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
        hRamification profile hConnected hGenus hValid).datum.vertexPartition
          (oldVertex target wall)).Rel a b
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
    refine (SheetPartition.paste_rel_iff
      ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall)
      (fun blk ↦ ((NonTrivalentValencyFourBackground.candidate source pairing
        hNoGlue hRamification profile hConnected hGenus hValid).resolution
          blk).left)
      (fun blk ↦ ((NonTrivalentValencyFourBackground.candidate source pairing
        hNoGlue hRamification profile hConnected hGenus hValid).contracts
          blk).left_refines) a b).mpr ?_
    rw [hSelected, selectedResolution_left]
    exact hRel
  · show ((NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
        hRamification profile hConnected hGenus hValid).datum.vertexPartition
          (freshVertex target)).Rel a b
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]
    refine (SheetPartition.paste_rel_iff
      ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall)
      (fun blk ↦ ((NonTrivalentValencyFourBackground.candidate source pairing
        hNoGlue hRamification profile hConnected hGenus hValid).resolution
          blk).right)
      (fun blk ↦ ((NonTrivalentValencyFourBackground.candidate source pairing
        hNoGlue hRamification profile hConnected hGenus hValid).contracts
          blk).right_refines) a b).mpr ?_
    rw [hSelected, selectedResolution_right]
    exact hRel

/-! ## 5.  The bridge survives once both endpoints retain a survivor -/

/-- **The new bridge occurrence is non-dangling as soon as each of its two
endpoint vertices carries one surviving retained occurrence.**  A dangling side
of the bridge would contain one of its endpoints, and every occurrence incident
to a vertex of a dangling side is itself dangling
(`DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side`).  This is the
Lean form of the paper's observation that `h_1^{(q)}` is a genuine edge of the
resolved trivalent type, not an artefact of the expansion. -/
theorem bridgeEdge_not_isDangling (sheet : Fin degree)
    (hLeft : nonDanglingValency
      (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
        hRamification profile hConnected hGenus hValid).datum
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid false sheet) ≠ 0)
    (hRight : nonDanglingValency
      (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
        hRamification profile hConnected hGenus hValid).datum
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid true sheet) ≠ 0) :
    ¬ IsDangling
      (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
        hRamification profile hConnected hGenus hValid).datum
      (bridgeEdge source pairing hNoGlue hRamification profile hConnected hGenus
        hValid sheet) := by
  have hEnds := GlobalResolution.sourceEnds_newSourceEdge
    (gaugedData source pairing hNoGlue hRamification) wall
    (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
      hRamification profile hConnected hGenus hValid).right
    (LocalResolution.paste _
      (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
        hRamification profile hConnected hGenus hValid).resolution
      (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
        hRamification profile hConnected hGenus hValid).contracts)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _
      (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
        hRamification profile hConnected hGenus hValid).exterior) sheet
  intro hDangling
  rcases hDangling with hSide | hSide
  · obtain ⟨cut⟩ := hSide
    apply hLeft
    have hFst :
        ((NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
            hRamification profile hConnected hGenus hValid).datum.sourceEnds
          (bridgeEdge source pairing hNoGlue hRamification profile hConnected
            hGenus hValid sheet)).1 =
          endpointVertex source pairing hNoGlue hRamification profile hConnected
            hGenus hValid false sheet := congrArg Prod.fst hEnds
    have hZero := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side
      _ cut cut.left_mem
    rwa [hFst] at hZero
  · obtain ⟨cut⟩ := hSide
    apply hRight
    have hSnd :
        ((NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
            hRamification profile hConnected hGenus hValid).datum.sourceEnds
          (bridgeEdge source pairing hNoGlue hRamification profile hConnected
            hGenus hValid sheet)).2 =
          endpointVertex source pairing hNoGlue hRamification profile hConnected
            hGenus hValid true sheet := congrArg Prod.snd hEnds
    have hZero := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side
      _ cut cut.left_mem
    rwa [hSnd] at hZero

/-- The concrete form: one surviving old occurrence on each side, on the same
sheet as the bridge, makes the bridge survive. -/
theorem bridgeEdge_not_isDangling_of_survivors (sheet : Fin degree)
    (leftEdge rightEdge : target.edges)
    (hLeftAt : leftEdge ∈ GluingDatum.incidentEdges wall)
    (hLeftSide : star.right pairing leftEdge = false)
    (hLeftSurvives : ¬ IsDangling (gaugedData source pairing hNoGlue hRamification)
      ((gaugedData source pairing hNoGlue hRamification).sourceEdge leftEdge sheet))
    (hRightAt : rightEdge ∈ GluingDatum.incidentEdges wall)
    (hRightSide : star.right pairing rightEdge = true)
    (hRightSurvives : ¬ IsDangling (gaugedData source pairing hNoGlue hRamification)
      ((gaugedData source pairing hNoGlue hRamification).sourceEdge rightEdge sheet)) :
    ¬ IsDangling
      (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
        hRamification profile hConnected hGenus hValid).datum
      (bridgeEdge source pairing hNoGlue hRamification profile hConnected hGenus
        hValid sheet) := by
  have hConnectedGauged :
      (gaugedData source pairing hNoGlue hRamification).Connected :=
    (gaugedData_valid source pairing hNoGlue hRamification hValid).1
  apply bridgeEdge_not_isDangling
  · exact ClassInjectivity.nonDanglingValency_ne_zero_of_incident _
      (ResolutionSurvival.not_isDangling_oldSourceEdge _ hConnectedGauged _
        hLeftSurvives)
      (retainedEdge_incident source pairing hNoGlue hRamification profile
        hConnected hGenus hValid leftEdge hLeftAt false hLeftSide sheet)
  · exact ClassInjectivity.nonDanglingValency_ne_zero_of_incident _
      (ResolutionSurvival.not_isDangling_oldSourceEdge _ hConnectedGauged _
        hRightSurvives)
      (retainedEdge_incident source pairing hNoGlue hRamification profile
        hConnected hGenus hValid rightEdge hRightAt true hRightSide sheet)

end DraismaVargas.LocalCases.NonTrivalentValencyFourRows
