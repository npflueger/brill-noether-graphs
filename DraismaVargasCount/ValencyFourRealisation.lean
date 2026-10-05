module

public import DraismaVargasCount.ValencyFourRigidity
public import DraismaVargasCount.GeneralKStarCount

@[expose] public section

/-!
# Per-`K` realisation at a valency-four metric limit, and the valency-four clause

**Source.**  Vargas, Part II (arXiv:2609.09109), the valency-4 limits of the section on
changing combinatorial type (Case `{v4-nd4}`: the `K`-member of each admissible `K`,
`|A₊| = |A| - K`, `|A₋| = k_α + k_β - 1 - K`).  The consumer is
`ValencyFourRigidity.v4InputsSupply_of_realisation`, whose hypothesis (`hexL`/`hexR` of
`ValencyFourSplit.metricCensus_clause_of_realised`) is `hex_of_resolved` below, verbatim.

## The result, in one paragraph

At every resolved datum of every Whitehead step and every valency-four metric facet limit `m`, every
`K` admissible for the anchor indices of any presenting regrowth is the `K`-index of a class on
**both** sides of `m` (`hex_of_resolved`, degree at least three).  With the injectivity of
`ValencyFourRigidity` this is `CensusAssembly.V4InputsSupply` (`v4InputsSupply`), hence
`V4ClauseSupply 10 15 4` (`v4ClauseSupply_genusSix`), the valency-four clause of the type changes
in step 3 of `Assembly` (`Assembly.typeChanges_genusSix`).  The far class of `K` is the far
regrowth of the general-`K` link at `w₀`'s own wall (`GeneralKLink`, `GeneralKExit`), in `w₀`'s
labelled metric limit (`GeneralKExitSetup.sameMetricLimit_of_columnReceipt`); the near class of `K`
is the far regrowth of the reversed link from any far class (`revMove`, `farCore_revMove`,
`facetDatum_rev`).  The content is that the far regrowth **reads** `K`: at the general-`K`
candidate the two active vertices of the anchor fibre are the two endpoint classes of the bridge
sheet, of sizes `|A| - K'` and `|A| - K`, and `K ≤ K'` at the smaller side, so `|A| - max = K`
(`readsK_candK`).

## What is proved

* §1 `ReadsK` (the far datum reads `K` at every valency-four anchor over one occurrence).
* §2 `K_le_coK`, `bridge_rel`, `blockCard_epv` (endpoint class sizes of the candidate),
  **`anchor_rel_of_nd4`** (any valency-four anchor block of the candidate's contraction is the
  bridge's block: `FacetAdapterPilot.candidateLimitIso`, the gauge's
  `GeneralKSourceFacts.datum_nonDanglingValency_endpoint`, and the wall's unique four-valent
  vertex), **`readsK_candK`**; the chain with the read record: `LinkReadsK`,
  `exists_linkReadsK_of_inputs`, `exists_linkReadsK_of_tracks`,
  `exists_linkReadsK_of_prescribedPairingMove`.
* §3 the dispatch with the read record: `exists_linkReadsK_of_orientation` (the orientation
  branch of the valency-four dispatch), `linkReadsK_ofSwap`,
  **`linkReadsK_four_of_anchor`** (hypothesis: the wall valency only).
* §4 `targetVertex_merge`, `wall_valency` (the synthetic arrival's wall is four-valent at an
  anchored regrowth), `range_of_admissible` (the admissible range read at any four-star),
  **`exists_far_reads`** (one far regrowth reading `K` per admissible `K`, in the same labelled
  metric limit), `exists_kIndexR_eq`, `exists_kIndexL_eq`, `exists_admissible_of_iso`.
* §5 **`hex_of_resolved`**, **`v4InputsSupply`**, **`v4ClauseSupply_genusSix`**.

## The route, checked step by step

* **Step 1 (right side from a left regrowth) holds**: the far regrowth of a column-receipted
  link is in the regrowth's labelled metric limit.
* **Step 2 (recorded `K` = read `K`) holds in substance, with no gauge or side shift**: the
  read `K` of the far regrowth of `GeneralKLink.linkK` at a position is that position's
  `split.K`, the `K` that `GeneralKLink.record_K` records (`readsK_candK`).  **But that
  record alone does not determine it.**  A link produced existentially with only this record
  is constrained only in `link.candidate.resolution sheet` and the index of
  `link.candidate.newSourceEdge sheet`.  The record does not say that (a) the new occurrence
  through `sheet` is the far anchor's bridge (it could be one of the `K + K'` dangling
  singletons, index `1`); (b) the record's pairing is the far cover's read partition
  (`link.candidate.right` is unconstrained); (c) `resolution sheet` is the resolution pasted on
  `sheet`'s block (the candidate pastes `resolution (repr sheet)`).  The read equation
  `k₁ + 2K_read + 1 = min(S_X, S_Y)` (`ValencyFourSplit.bridge_eq`) and the record's
  `k(sheet) + 2K + 1 = S_min(pairing)` agree only given (a) and (b).  So the chain of
  general-`K` links is re-run here (§2--§3) with the record `LinkReadsK`, proved at the
  construction.  The anchor shape (`ValencyFourSplit.shape`, `eq_or_eq_of_mem_fib`) and the
  source facts of `GeneralKSourceFacts` (`epv`, `endSheets`, `epv_bridge_ne_zero`,
  `candidate_endpoint_rel_iff`) suffice.
* **Step 3 (left side through the reverse move) holds**; the admissible range is a limit
  invariant (`ValencyFourSplit.regrowth_reads4`, `exists_admissible_of_iso`).
  `ColumnReceiptExport.metricLinkReceipts_rev` is not needed: the reverse link is the
  general-`K` link of the reversed move itself.
* The range is read at any four-star (`range_of_admissible`).

## What is NOT proved -- every hypothesis

* `hex_of_resolved` keeps `3 ≤ degree` (the `MemberSeed` receipt, through
  `MemberSeedExists.nonempty_memberSeed_of_member`); `v4InputsSupply` also keeps `3 ≤ n`
  (the injectivity of `ValencyFourRigidity`).  The genus-six statements have no hypothesis.
* **Duplication.**  §3 repeats the orientation branch of the valency-four dispatch (about
  130 lines) and §2 re-runs three short lemmas of the general-`K` chain, only to change the
  exported record.  The duplication would disappear if
  `GeneralKLink.exists_typeChangeLinkK_of_inputs` and its consumers exported `LinkReadsK`
  beside (or instead of) the `K` record.
* `ReadsK` is proved at every general-`K` candidate but is not evaluated here at a candidate
  over a literal facet regrowth.
* New `Prop`s: `ReadsK` (see its docstring; producer `readsK_candK`, consumer
  `exists_far_reads`) and the abbreviation `LinkReadsK`.  Neither is a hypothesis of any
  theorem here.
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no `#eval`.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.ValencyFourRealisation

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.Count.GeneralKReceipts
open DraismaVargas.Count.GeneralKExitSetup
open GraphContraction GluingContraction ContractionRamification
open ValencyThreeSplit (fib size anchorSize limA)
open ValencyFourSplit (AnchorInput4 Labelling4 Split4 Reads4)

/-! ## 1.  The read `K` of a cover at every valency-four anchor over one target occurrence -/

/-- **The far datum reads `K`**: at every merged block over the target occurrence `newEdge`
that carries the valency-four anchor input, every split read off the cover (under every
labelling) has index `K`.

Interface: `ValencyFourSplit.Reads4` quantified over the anchor blocks of one contraction;
producer `readsK_candK` (the general-`K` candidate reads its own `position.split.K`); consumer
`exists_far_reads` (via `ValencyFourSplit.kIndexR_spec`). -/
def ReadsK {T : CFGraph} {degree : ℕ} (D : GluingDatum T degree) (newEdge : T.edges) (K : ℕ) :
    Prop :=
  ∀ {a b : T.V} {contracted : T.edges} (hc : (contracted : T.V × T.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges T a b = 1) (block : (mergedPartition D a b).Blocks),
    contracted = newEdge → AnchorInput4 D hc hab hOne block →
    ∀ (L : Labelling4 (contractDatum D hc hab hOne) (limA D hc hab hOne block)) (s : Split4),
      Reads4 L s → s.K = K

/-! ## 2.  The general-`K` candidate reads its own `K` -/

section Wall

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.TargetExpansion
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

local notation "cK" => (candK m wd wallStar anchorBlock hAnchor pairing position geometry)

/-- The minus side of a smaller-side position is the smaller one: `K ≤ K'`. -/
theorem K_le_coK : position.split.K ≤ position.split.coK := by
  have hMinus := position.minus_card
  have hPlus := position.plus_card
  have hMK := position.split.card_minus_add_coK
  have hPK := position.split.card_plus_add_K
  have hSide : sideIndex vSrc pairing (smallerSide vSrc pairing) ≤
      sideIndex vSrc pairing (!smallerSide vSrc pairing) := by
    unfold smallerSide
    by_cases h : sideIndex vSrc pairing true < sideIndex vSrc pairing false
    · simp only [h, decide_true, Bool.not_true]
      exact h.le
    · simp only [h, decide_false, Bool.not_false]
      omega
  omega

/-- The bridge sheet lies in the anchor block. -/
theorem bridge_rel :
    ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition ⟨wd.a, wd.hab⟩).Rel
      anchorBlock.1 position.split.bridge :=
  (((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition ⟨wd.a, wd.hab⟩).mem_block_iff
    _ _).mp (position.split.bridgeSheets_subset position.split.bridge_mem_bridgeSheets)

/-- The endpoint class of the bridge on side `b` is `endSheets b`, in the candidate datum. -/
theorem blockCard_epv (b : Bool) :
    size (cK).datum (GeneralKSourceFacts.epv (cK) b position.split.bridge) =
      (GeneralKSourceFacts.endSheets position b).card := by
  classical
  show (((cK).datum.vertexPartition (if b then freshVertex _ else oldVertex _ _)).block
    (((cK).datum.vertexPartition (if b then freshVertex _ else oldVertex _ _)).repr
      position.split.bridge)).card = _
  rw [← SheetPartition.block_eq_of_rel _ (SheetPartition.rel_repr_right _ _)]
  congr 1
  ext y
  rw [SheetPartition.mem_block_iff]
  rw [GeneralKSourceFacts.candidate_endpoint_rel_iff position vConn vGen vNG geometry b
    (bridge_rel m wd wallStar anchorBlock hAnchor pairing position) y]
  exact GeneralKSourceFacts.endpoint_rel_bridge_iff position b y

/-- **The merged block of any valency-four anchor of the candidate is the bridge's**: its limit
vertex has surviving valency four, the candidate's limit is the gauged wall datum
(`FacetAdapterPilot.candidateLimitIso`), the gauge moves no valency at the wall
(`GeneralKSourceFacts.datum_nonDanglingValency_endpoint`), and the wall datum has one
four-valent vertex (`NonTrivalentUniqueFourValent.eq_of_nonDanglingValency_four`). -/
theorem anchor_rel_of_nd4 (fdOut : FullDimensionalSourcePresentation (cK).datum coordinate)
    {a b : (TargetExpansion.graph (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      (cK).right).V}
    {contracted : (TargetExpansion.graph (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      (cK).right).edges}
    (hc : (contracted : _ × _) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges _ a b = 1) (block : (mergedPartition (cK).datum a b).Blocks)
    (hcon : contracted = occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      (cK).right none)
    (hnd : nonDanglingValency (contractDatum (cK).datum hc hab hOne)
      (limA (cK).datum hc hab hOne block) = 4) :
    ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition ⟨wd.a, wd.hab⟩).Rel
      anchorBlock.1 block.1 := by
  classical
  have hConn : (contractDatum (cK).datum hc hab hOne).Connected :=
    connected_contractDatum _ hc hab hOne fdOut.valid.1
  have hLim : limA (cK).datum hc hab hOne block =
      (contractDatum (cK).datum hc hab hOne).sourceEndpoint ⟨a, hab⟩ block.1 := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · show block.1 = ((contractDatum (cK).datum hc hab hOne).vertexPartition ⟨a, hab⟩).repr block.1
      rw [contractDatum_vertexPartition_merge]
      exact block.2.symm
  have h1 := ((FacetAdapterPilot.candidateLimitIso (cK) hc hab hOne hcon).nonDanglingValency_map
    hConn (limA (cK).datum hc hab hOne block)).trans hnd
  have h2 := ValencyFourRigidity.sourceVertexEquiv_sourceEndpoint
    (FacetAdapterPilot.candidateLimitIso (cK) hc hab hOne hcon) ⟨a, hab⟩ block.1
  rw [← hLim] at h2
  rw [h2] at h1
  have hT : (FacetAdapterPilot.candidateLimitIso (cK) hc hab hOne hcon).targetVertex ⟨a, hab⟩ =
      ⟨wd.a, wd.hab⟩ :=
    (W4LimitContraction.vertexEquiv_apply hc hab hOne hcon ⟨a, hab⟩).trans
      ((congrArg (contractVertex _ _) (W4LimitContraction.fst_eq hc hcon)).trans
        (contract_oldVertex _ _ _))
  have hP : (FacetAdapterPilot.candidateLimitIso (cK) hc hab hOne hcon).vertexPerm ⟨a, hab⟩ =
      FacetAdapterPilot.mergePerm (cK) hc hcon := ite_eq_left rfl
  rw [hT, hP] at h1
  have hRel : (position.datum.vertexPartition ⟨wd.a, wd.hab⟩).Rel
      (FacetAdapterPilot.mergePerm (cK) hc hcon block.1) block.1 :=
    (FacetAdapterPilot.candidate_merge_rel (cK) hc hcon _ _).mp
      (FacetAdapterPilot.blockSwapFun_rel (FacetAdapterPilot.candidate_merge_rel (cK) hc hcon)
        block.1)
  rw [GeneralKSourceFacts.datum_nonDanglingValency_endpoint position vVal] at h1
  have hEq := NonTrivalentUniqueFourValent.eq_of_nonDanglingValency_four wd.cover wd.fullDim
    wd.hc wd.hab wd.hOne wallStar (wd.hCompat m) wd.coordinates (label m.base) wd.hRows
    wd.hZeroCoord _ _ h1 hAnchor
  have hRelA : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
      ⟨wd.a, wd.hab⟩).Rel (FacetAdapterPilot.mergePerm (cK) hc hcon block.1) anchorBlock.1 :=
    congrArg (fun X : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceVertex ↦ X.1.2) hEq
  have hRel' := position.datum_vertexPartition_wall ▸ hRel
  exact hRelA.symm.trans hRel'

/-- **The general-`K` candidate reads its own `K`.**  At the (unique) valency-four anchor of
the candidate's contraction along the regrown occurrence, the two active fibre vertices are the
two endpoint classes of the bridge sheet, of sizes `|A₋| = |A| - K'` and `|A₊| = |A| - K`
(`blockCard_epv`), and `K ≤ K'` at the smaller side (`K_le_coK`); so the read split has
`|A| - max(|A₋|, |A₊|) = K`. -/
theorem readsK_candK (fdOut : FullDimensionalSourcePresentation (cK).datum coordinate) :
    ReadsK (cK).datum (occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      (cK).right none) position.split.K := by
  classical
  intro a b contracted hc hab hOne block hcon H L s hs
  have hA := anchor_rel_of_nd4 m wd wallStar anchorBlock hAnchor pairing position geometry fdOut
    hc hab hOne block hcon H.nd4
  have hB := bridge_rel m wd wallStar anchorBlock hAnchor pairing position
  have hBase : ∀ i j, (mergedPartition (cK).datum a b).Rel i j ↔
      ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition ⟨wd.a, wd.hab⟩).Rel i j := by
    intro i j
    rw [← position.datum_vertexPartition_wall]
    exact FacetAdapterPilot.candidate_merge_rel (cK) hc hcon i j
  have ha := W4LimitContraction.fst_eq hc hcon
  have hb := W4LimitContraction.snd_eq hc hcon
  subst ha hb
  -- the two bridge ends lie in the pruned fibre of `block`
  have hmem : ∀ bb : Bool,
      GeneralKSourceFacts.epv (cK) bb position.split.bridge ∈ fib (cK).datum hc hab hOne block := by
    intro bb
    refine (ValencyThreeSplit.mem_fib_iff _ _ _ _ _ _).mpr ⟨?_, ?_,
      GeneralKSourceFacts.epv_bridge_ne_zero position vConn vGen vNG geometry vVal bb⟩
    · cases bb
      · exact Or.inl rfl
      · exact Or.inr rfl
    · have hRef : ((cK).datum.vertexPartition
          (if bb then freshVertex (contract wd.coverTarget wd.hab wd.hOne)
            else oldVertex (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)).Refines
          (mergedPartition (cK).datum
            (oldVertex (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
            (freshVertex (contract wd.coverTarget wd.hab wd.hOne))) := by
        cases bb
        · exact SheetPartition.left_refines_join _ _
        · exact SheetPartition.right_refines_join _ _
      have h1 := hRef.rel (SheetPartition.rel_repr_left _ position.split.bridge)
      have h2 : (mergedPartition (cK).datum
          (oldVertex (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
          (freshVertex (contract wd.coverTarget wd.hab wd.hOne))).Rel position.split.bridge
          block.1 := (hBase _ _).mpr (hB.symm.trans hA)
      exact (h1.trans h2).trans block.2
  obtain ⟨P⟩ := ValencyFourSplit.shape fdOut H
  obtain ⟨-, X, hX, Y, hY, hXY, -, -, hK⟩ := hs
  have hne : GeneralKSourceFacts.epv (cK) false position.split.bridge ≠
      GeneralKSourceFacts.epv (cK) true position.split.bridge := by
    intro h
    exact hab (congrArg (fun Z : (cK).datum.SourceVertex ↦ Z.1.1) h)
  have hsize : max (size (cK).datum X) (size (cK).datum Y) =
      max (GeneralKSourceFacts.endSheets position false).card
        (GeneralKSourceFacts.endSheets position true).card := by
    rw [← blockCard_epv m wd wallStar anchorBlock hAnchor pairing position geometry false,
      ← blockCard_epv m wd wallStar anchorBlock hAnchor pairing position geometry true]
    rcases ValencyFourSplit.eq_or_eq_of_mem_fib P (hmem false) (hmem true) hne hX with rfl | rfl <;>
      rcases ValencyFourSplit.eq_or_eq_of_mem_fib P (hmem false) (hmem true) hne hY with
        rfl | rfl
    · exact absurd rfl hXY
    · rfl
    · exact max_comm _ _
    · exact absurd rfl hXY
  have hAnchorSize : anchorSize (cK).datum block =
      ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition ⟨wd.a, wd.hab⟩).blockCard
        anchorBlock.1 := by
    show ((mergedPartition (cK).datum _ _).block block.1).card = _
    congr 1
    ext y
    rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff, hBase]
    exact ⟨fun h ↦ hA.trans h, fun h ↦ hA.symm.trans h⟩
  rw [hsize, hAnchorSize] at hK
  have hPK := position.split.card_plus_add_K
  have hMK := position.split.card_minus_add_coK
  have hle := K_le_coK m wd wallStar anchorBlock hAnchor pairing position
  have e0 : (GeneralKSourceFacts.endSheets position false).card =
      if false = smallerSide vSrc pairing then position.split.minusSheets.card
        else position.split.plusSheets.card := by
    unfold GeneralKSourceFacts.endSheets
    split_ifs <;> rfl
  have e1 : (GeneralKSourceFacts.endSheets position true).card =
      if true = smallerSide vSrc pairing then position.split.minusSheets.card
        else position.split.plusSheets.card := by
    unfold GeneralKSourceFacts.endSheets
    split_ifs <;> rfl
  rw [e0, e1] at hK
  by_cases hSide : smallerSide vSrc pairing = true
  · rw [ite_eq_right (by rw [hSide]; decide), ite_eq_left hSide.symm] at hK
    omega
  · rw [Bool.not_eq_true] at hSide
    rw [ite_eq_left hSide.symm, ite_eq_right (by rw [hSide]; decide)] at hK
    omega

/-! ### The general-`K` links, with the read record

The chain of general-`K` links (from the per-position inputs of
`GeneralKLink.exists_typeChangeLinkK_of_inputs`, from `Tracks`, and from the prescribed
pairing move), re-run with the record `ReadsK` in place of the `K` record: the `K` record
is not enough to recover the read `K` (see the module docstring), while every link of the
chain is `GeneralKLink.linkK`
over a position whose `split.K` is the requested `K`, and `readsK_candK` applies to it. -/

omit wallStar anchorBlock hAnchor in
/-- The `K`-record this module consumes: the far datum of the link reads `K` at its
regrown occurrence. -/
abbrev LinkReadsK (link : TypeChangeLink m wd) (K : ℕ) : Prop :=
  ReadsK link.candidate.datum
    (occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      link.candidate.right none) K

/-- **The `K`-links with the read record, from the per-position inputs** (the proof of
`GeneralKLink.exists_typeChangeLinkK_of_inputs`, with `record_K` replaced by `readsK_candK`). -/
theorem exists_linkReadsK_of_inputs
    (hInputs : ∃ p : Fin 3,
      ∀ pos : GeneralKReceipts.Position vSrc p (smallerSide vSrc p),
        ∃ geo : GeneralKReceipts.PairingBackground pos.datum wallStar p anchorBlock.1,
        ∃ fdOut : FullDimensionalSourcePresentation
            (candK m wd wallStar anchorBlock hAnchor p pos geo).datum coordinate,
          AgreeOffColumn wd.incomingMatrix
            (GluingDatum.LengthMatrixPresentation.matrix fdOut.labelling.presentation)
            wd.column ∧
          Nonempty (Tracks fdOut (graph.move m) label) ∧
          fdOut.labelling.targetEdge wd.column =
            occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
              (candK m wd wallStar anchorBlock hAnchor p pos geo).right none ∧
          ∀ j : {column : coordinate //
              column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted},
            fdOut.labelling.targetEdge j.1 =
              occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
                (candK m wd wallStar anchorBlock hAnchor p pos geo).right
                (some (StablePathFacetContraction.punctureTargetEquiv wd.fullDim.labelling
                  wd.hc wd.hab wd.hOne j))) :
    ∀ K : ℕ,
      (∀ l, K + 1 ≤ (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim
          wd.hc wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor).index l) →
      (∀ l, K + (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
          wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor).index l ≤
        ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          ⟨wd.a, wd.hab⟩).blockCard anchorBlock.1) →
      ∃ link : TypeChangeLink m wd, ColumnReceiptExport.ColumnReceipt link ∧
        LinkReadsK m wd link K := by
  obtain ⟨p, hp⟩ := hInputs
  intro K hLower hUpper
  obtain ⟨pos, hK, -⟩ := exists_position_of_range vSrc p vNG
    (NonTrivalentUniqueFourValent.wall_ramification wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      wallStar (wd.hForest m) anchorBlock) hLower hUpper
  obtain ⟨geo, fdOut, hAgree, ⟨tracks⟩, hColNew, hColOld⟩ := hp pos
  subst hK
  exact ⟨GeneralKLink.linkK m wd wallStar anchorBlock hAnchor p pos geo fdOut tracks hAgree,
    GeneralKLink.columnReceipt_linkK m wd wallStar anchorBlock hAnchor p pos geo fdOut tracks
      hAgree hColNew hColOld,
    readsK_candK m wd wallStar anchorBlock hAnchor p pos geo fdOut⟩

/-- **The `K`-links with the read record, from `Tracks` alone.** -/
theorem exists_linkReadsK_of_tracks
    (hTracks : ∃ p : Fin 3,
      ∀ (pos : GeneralKReceipts.Position vSrc p (smallerSide vSrc p))
        (geo : GeneralKReceipts.PairingBackground pos.datum wallStar p anchorBlock.1)
        (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor p
          pos geo),
        Nonempty (InteriorGraphTracking.Tracks
          (GeneralKExit.outgoingFDK m wd wallStar anchorBlock hAnchor p pos geo hBg)
          (graph.move m) label)) :
    ∀ K : ℕ,
      (∀ l, K + 1 ≤ (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim
          wd.hc wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor).index l) →
      (∀ l, K + (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
          wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor).index l ≤
        ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          ⟨wd.a, wd.hab⟩).blockCard anchorBlock.1) →
      ∃ link : TypeChangeLink m wd, ColumnReceiptExport.ColumnReceipt link ∧
        LinkReadsK m wd link K := by
  obtain ⟨p, hp⟩ := hTracks
  refine exists_linkReadsK_of_inputs m wd wallStar anchorBlock hAnchor ⟨p, fun pos ↦ ?_⟩
  obtain ⟨geo, hBg⟩ := GeneralKSourceFacts.exists_localCanonicalBackground m wd wallStar
    anchorBlock hAnchor p pos
  refine ⟨geo, GeneralKExit.outgoingFDK m wd wallStar anchorBlock hAnchor p pos geo hBg, ?_,
    hp pos geo hBg, ?_, ?_⟩
  · have h := GeneralKExit.agreeOffColumn_outLabK m wd wallStar anchorBlock hAnchor p pos geo hBg
    rw [wd.targetEdge_symm_contracted] at h
    exact h
  · have h := GeneralKExit.outLabK_targetEdge_col m wd wallStar anchorBlock hAnchor p pos geo hBg
    rw [wd.targetEdge_symm_contracted] at h
    exact h
  · exact GeneralKExit.outLabK_targetEdge_ne m wd wallStar anchorBlock hAnchor p pos geo hBg

/-- **The `K`-links with the read record under (H-IV)** (the star count of `GeneralKStarCount`). -/
theorem exists_linkReadsK_of_prescribedPairingMove
    (hPres : NonTrivalentValencyFourTracks.PrescribedPairingMove m wd wallStar anchorBlock
      hAnchor pairing) :
    ∀ K : ℕ,
      (∀ l, K + 1 ≤ (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim
          wd.hc wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor).index l) →
      (∀ l, K + (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
          wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor).index l ≤
        ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          ⟨wd.a, wd.hab⟩).blockCard anchorBlock.1) →
      ∃ link : TypeChangeLink m wd, ColumnReceiptExport.ColumnReceipt link ∧
        LinkReadsK m wd link K :=
  exists_linkReadsK_of_tracks m wd wallStar anchorBlock hAnchor
    ⟨pairing, fun pos geo hBg ↦
      GeneralKStarCount.nonempty_tracks_outgoingFDK m wd wallStar anchorBlock hAnchor pairing pos
        geo hBg hPres⟩

end Wall

/-! ## 3.  The dispatch, with the read record

The valency-four dispatch, run with the leaf `exists_linkReadsK_of_prescribedPairingMove`:
the orientation branch is the usual one up to the leaf, and the swap keeps
`candidate` literally (`linkOfSwap`), which is all `LinkReadsK` reads. -/

section Dispatch

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.NonTrivalentValencyFourTracks
open DraismaVargas.LocalCases.NonTrivalentValencyFourDispatcher

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

/-- **The orientation branch with the read record.** -/
theorem exists_linkReadsK_of_orientation
    (h4 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 4)
    (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        anchorBlock) = 4)
    (hBase : wd.tracks.iso.dart
      (facetDartLeft m wd (W4TargetPairings.FourStar.of_card h4)) = m.base) :
    ∃ (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩), ∀ K : ℕ,
      (∀ l, K + 1 ≤ (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim
          wd.hc wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor).index l) →
      (∀ l, K + (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
          wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor).index l ≤
        ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          ⟨wd.a, wd.hab⟩).blockCard anchorBlock.1) →
      ∃ link : TypeChangeLink m wd, ColumnReceiptExport.ColumnReceipt link ∧
        LinkReadsK m wd link K := by
  classical
  set star₀ := W4TargetPairings.FourStar.of_card h4 with hstar₀
  obtain ⟨x, y, hx1, hy1, -, -, hStar⟩ := IncomingPairing.exists_movedStar_darts m wd
  -- the orientation identifies the two ends of the vanishing occurrence
  have hbd : IncomingPairing.baseDart m wd = facetDartLeft m wd star₀ :=
    IncomingPairing.baseDart_eq_facetDartLeft_four m wd star₀ hBase
  have hod : IncomingPairing.opBaseDart m wd = facetDartRight m wd star₀ :=
    IncomingPairing.opBaseDart_eq_facetDartRight_four m wd star₀ hBase
  have hxv : x.1.1 = leftEnd m wd := by rw [hx1, hbd]; rfl
  have hyv : y.1.1 = rightEnd m wd := by rw [hy1, hod]; rfl
  have hxInc : Incident wd.cover x.2.1.1 (leftEnd m wd) := by rw [← hxv]; exact x.2.2
  have hyInc : Incident wd.cover y.2.1.1 (rightEnd m wd) := by rw [← hyv]; exact y.2.2
  -- neither of them is the vanishing occurrence
  have hxmem : wd.tracks.iso.dart x ∈
      (Finset.univ.filter fun c ↦ (graph.move m).vert c = graph.vert m.base).erase m.base := by
    rw [hStar]
    exact Finset.mem_insert_self _ _
  have hymem : wd.tracks.iso.dart y ∈
      (Finset.univ.filter fun c ↦ (graph.move m).vert c = graph.vert m.base).erase m.base := by
    rw [hStar]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hxne : x.2.1 ≠ facetEdge m wd := row_ne_facet_of_mem_movedStar m wd x hxmem
  have hyne : y.2.1 ≠ facetEdge m wd := row_ne_facet_of_mem_movedStar m wd y hymem
  -- they descend to two survivors at the anchor
  have hTx : (x.2.1.1.1.1 : wd.coverTarget.edges) ≠ wd.contracted :=
    target_ne_contracted_of_incident_end m wd star₀ x.2.1 (leftEnd m wd)
      (incident_facetEdge_leftEnd m wd) hxInc hxne
  have hTy : (y.2.1.1.1.1 : wd.coverTarget.edges) ≠ wd.contracted :=
    target_ne_contracted_of_incident_end m wd star₀ y.2.1 (rightEnd m wd)
      (incident_facetEdge_rightEnd m wd) hyInc hyne
  have hIncX : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (descent m wd x.2.1 hTx).1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlock) := by
    have h := incident_descent m wd x.2.1 hTx hxInc
    rwa [sourceVertexMap_leftEnd_eq_anchorVertex m wd star₀ anchorBlock hAnchor] at h
  have hIncY : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (descent m wd y.2.1 hTy).1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlock) := by
    have h := incident_descent m wd y.2.1 hTy hyInc
    rw [← sourceVertexMap_leftEnd_eq_rightEnd m wd,
      sourceVertexMap_leftEnd_eq_anchorVertex m wd star₀ anchorBlock hAnchor] at h
    exact h
  -- the two target directions are different
  set sx : {edge : (contract wd.coverTarget wd.hab wd.hOne).edges //
      edge ∈ GluingDatum.incidentEdges
        (⟨wd.a, wd.hab⟩ : (contract wd.coverTarget wd.hab wd.hOne).V)} :=
    ⟨(descent m wd x.2.1 hTx).1.1.1,
      mem_incidentEdges_of_incident_anchor m wd anchorBlock _ hIncX⟩ with hsx
  set sy : {edge : (contract wd.coverTarget wd.hab wd.hOne).edges //
      edge ∈ GluingDatum.incidentEdges
        (⟨wd.a, wd.hab⟩ : (contract wd.coverTarget wd.hab wd.hOne).V)} :=
    ⟨(descent m wd y.2.1 hTy).1.1.1,
      mem_incidentEdges_of_incident_anchor m wd anchorBlock _ hIncY⟩ with hsy
  have hsne : sx ≠ sy := by
    intro hBad
    have hT : ((descent m wd x.2.1 hTx).1.1.1 :
        (contract wd.coverTarget wd.hab wd.hOne).edges) =
        star₀.edge (star₀.label.symm sx) := by
      show sx.1 = (star₀.label (star₀.label.symm sx)).1
      rw [Equiv.apply_symm_apply]
    have hT' : ((descent m wd y.2.1 hTy).1.1.1 :
        (contract wd.coverTarget wd.hab wd.hOne).edges) =
        star₀.edge (star₀.label.symm sx) := by
      show sy.1 = (star₀.label (star₀.label.symm sx)).1
      rw [Equiv.apply_symm_apply, hBad]
    have hsrc₀ := NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne star₀ (wd.hForest m) anchorBlock hAnchor
    have hEqX := eq_sourceEdge_of_target m wd anchorBlock star₀ hsrc₀ (star₀.label.symm sx)
      (descent m wd x.2.1 hTx) hIncX hT
    have hEqY := eq_sourceEdge_of_target m wd anchorBlock star₀ hsrc₀ (star₀.label.symm sx)
      (descent m wd y.2.1 hTy) hIncY hT'
    have hEq : descent m wd x.2.1 hTx = descent m wd y.2.1 hTy :=
      Subtype.ext (hEqX.trans hEqY.symm)
    have hxy : x.2.1 = y.2.1 := by
      rw [← liftEdge_descent m wd x.2.1 hTx, ← liftEdge_descent m wd y.2.1 hTy, hEq]
    exact not_incident_both_ends m wd anchorBlock star₀ hAnchor x.2.1 hxInc
      (by rw [hxy]; exact hyInc) hTx
  -- relabel the star so that the two directions carry the labels 2 and 3
  set star := relabel star₀ sx sy with hstar
  have hs2 : star.edge 2 = (descent m wd x.2.1 hTx).1.1.1 := relabel_two star₀ sx sy hsne
  have hs3 : star.edge 3 = (descent m wd y.2.1 hTy).1.1.1 := relabel_three star₀ sx sy
  have hsrc := NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne star (wd.hForest m) anchorBlock hAnchor
  have hGx : (descent m wd x.2.1 hTx).1 = hsrc.sourceEdge 2 :=
    eq_sourceEdge_of_target m wd anchorBlock star hsrc 2 (descent m wd x.2.1 hTx) hIncX hs2.symm
  have hGy : (descent m wd y.2.1 hTy).1 = hsrc.sourceEdge 3 :=
    eq_sourceEdge_of_target m wd anchorBlock star hsrc 3 (descent m wd y.2.1 hTy) hIncY hs3.symm
  have hLiftX : liftEdge m wd ⟨hsrc.sourceEdge 2, hsrc.sourceEdge_survives 2⟩ = x.2.1 := by
    rw [show (⟨hsrc.sourceEdge 2, hsrc.sourceEdge_survives 2⟩ :
      NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) =
        descent m wd x.2.1 hTx from Subtype.ext hGx.symm]
    exact liftEdge_descent m wd x.2.1 hTx
  have hLiftY : liftEdge m wd ⟨hsrc.sourceEdge 3, hsrc.sourceEdge_survives 3⟩ = y.2.1 := by
    rw [show (⟨hsrc.sourceEdge 3, hsrc.sourceEdge_survives 3⟩ :
      NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) =
        descent m wd y.2.1 hTy from Subtype.ext hGy.symm]
    exact liftEdge_descent m wd y.2.1 hTy
  have hSel : ∀ (which : Bool) (lbl : Fin 4), selectedLabel 0 false which = lbl →
      selectedLift m wd star anchorBlock hAnchor 0 false which =
        liftEdge m wd ⟨hsrc.sourceEdge lbl, hsrc.sourceEdge_survives lbl⟩ := by
    intro which lbl h
    subst h
    rfl
  -- (H-IV) for the pairing `0`, at the relabelled star; the leaf is the prescribed-pairing producer
  have hPres : PrescribedPairingMove m wd star anchorBlock hAnchor 0 := by
    refine ⟨hBase, ?_⟩
    rcases first_second_zero_false with ⟨hf, hs⟩ | ⟨hf, hs⟩
    · exact ⟨x, y, ((hSel false 2 hf).trans hLiftX).symm,
        ((hSel true 3 hs).trans hLiftY).symm, hStar⟩
    · exact ⟨y, x, ((hSel false 3 hf).trans hLiftY).symm,
        ((hSel true 2 hs).trans hLiftX).symm, by rw [hStar, Finset.pair_comm]⟩
  exact ⟨star, exists_linkReadsK_of_prescribedPairingMove m wd star anchorBlock hAnchor 0 hPres⟩

/-- **The read record survives the swap**: `linkOfSwap` keeps the candidate literally, and the
swapped wall data has the same cover. -/
theorem linkReadsK_ofSwap (hL : label (graph.op m.base) = label m.base)
    (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        anchorBlock) = 4)
    (h : ∃ (wallStar : W4TargetPairings.FourStar
          (contract (swapWallData m wd hL).coverTarget (swapWallData m wd hL).hab
            (swapWallData m wd hL).hOne) ⟨(swapWallData m wd hL).a, (swapWallData m wd hL).hab⟩),
        ∀ K : ℕ,
      (∀ l, K + 1 ≤ (NonTrivalentUniqueFourValent.wallFourBranchAnchor
          (swapWallData m wd hL).cover (swapWallData m wd hL).fullDim
          (swapWallData m wd hL).hc (swapWallData m wd hL).hab (swapWallData m wd hL).hOne
          wallStar ((swapWallData m wd hL).hForest m.swap) anchorBlock hAnchor).index l) →
      (∀ l, K + (NonTrivalentUniqueFourValent.wallFourBranchAnchor
          (swapWallData m wd hL).cover (swapWallData m wd hL).fullDim
          (swapWallData m wd hL).hc (swapWallData m wd hL).hab (swapWallData m wd hL).hOne
          wallStar ((swapWallData m wd hL).hForest m.swap) anchorBlock hAnchor).index l ≤
        ((contractDatum (swapWallData m wd hL).cover (swapWallData m wd hL).hc
          (swapWallData m wd hL).hab (swapWallData m wd hL).hOne).vertexPartition
          ⟨(swapWallData m wd hL).a, (swapWallData m wd hL).hab⟩).blockCard anchorBlock.1) →
      ∃ link : TypeChangeLink m.swap (swapWallData m wd hL),
        ColumnReceiptExport.ColumnReceipt link ∧ LinkReadsK m.swap (swapWallData m wd hL) link K) :
    ∃ (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩), ∀ K : ℕ,
      (∀ l, K + 1 ≤ (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim
          wd.hc wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor).index l) →
      (∀ l, K + (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
          wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor).index l ≤
        ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          ⟨wd.a, wd.hab⟩).blockCard anchorBlock.1) →
      ∃ link : TypeChangeLink m wd, ColumnReceiptExport.ColumnReceipt link ∧
        LinkReadsK m wd link K := by
  obtain ⟨wallStar, hK⟩ := h
  refine ⟨wallStar, fun K hLow hHigh ↦ ?_⟩
  obtain ⟨link, hrec, hRead⟩ := hK K hLow hHigh
  exact ⟨linkOfSwap m wd hL link, ⟨hrec.column_new, hrec.base_col⟩, hRead⟩

/-- **Headline of the dispatch, with the read record**: at every four-valent wall datum and
every anchor block of non-dangling valency four, some four-star has, for every admissible `K`,
a column-receipted type-change link whose far datum reads `K`. -/
theorem linkReadsK_four_of_anchor
    (h4 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 4)
    (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        anchorBlock) = 4) :
    ∃ (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩), ∀ K : ℕ,
      (∀ l, K + 1 ≤ (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim
          wd.hc wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor).index l) →
      (∀ l, K + (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
          wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor).index l ≤
        ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          ⟨wd.a, wd.hab⟩).blockCard anchorBlock.1) →
      ∃ link : TypeChangeLink m wd, ColumnReceiptExport.ColumnReceipt link ∧
        LinkReadsK m wd link K := by
  classical
  rcases dart_facetDartLeft_cases m wd (W4TargetPairings.FourStar.of_card h4) with h | h
  · exact exists_linkReadsK_of_orientation m wd h4 anchorBlock hAnchor h
  · have hL : label (graph.op m.base) = label m.base :=
      MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base
    have hBase' : (swapWallData m wd hL).tracks.iso.dart
        (facetDartLeft m.swap (swapWallData m wd hL)
          (W4TargetPairings.FourStar.of_card h4)) = m.swap.base :=
      (congrArg wd.tracks.iso.dart
        (facetDartLeft_swap m wd hL (W4TargetPairings.FourStar.of_card h4))).trans h
    exact linkReadsK_ofSwap m wd hL anchorBlock hAnchor
      (exists_linkReadsK_of_orientation m.swap (swapWallData m wd hL) h4 anchorBlock
        hAnchor hBase')

end Dispatch

/-! ## 4.  The facet level: one far class of every admissible `K` -/

section Facet

open FacetAdapterPilot MemberCertifiedPencil ValencyThreeGeneral FacetMachine
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open ValencyFourSplit (RegrowthAnchor4 V4Limit kIndexL kIndexR)
open ValencyThreeSplit (anchorOf)

/-- The contraction of a geometric isomorphism carries the merged vertex to the merged
vertex. -/
theorem targetVertex_merge {degree : ℕ} {T₁ T₂ : CFGraph.{0}} {first : GluingDatum T₁ degree}
    {second : GluingDatum T₂ degree} (iso : GeometricDatumIso first second) (e₁ : T₁.edges)
    (e₂ : T₂.edges) (h : iso.targetEdge e₁ = e₂)
    (hOne₁ : num_edges T₁ (e₁ : T₁.V × T₁.V).1 (e₁ : T₁.V × T₁.V).2 = 1)
    (hOne₂ : num_edges T₂ (e₂ : T₂.V × T₂.V).1 (e₂ : T₂.V × T₂.V).2 = 1) :
    ((GeometricLimitTransport.contractDatumIsoOfEdgeEq iso e₁ e₂ h hOne₁ hOne₂).targetVertex
      (⟨(e₁ : T₁.V × T₁.V).1, fst_ne_snd e₁⟩ : GraphContraction.Vertex T₁ _)).1 =
      (e₂ : T₂.V × T₂.V).1 := by
  subst h
  exact GeometricContraction.foldEquiv_merged _ _ _ (iso.ends e₁)

variable {n p degree : ℕ} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- **The wall valency of the synthetic arrival is the regrowth's**: four, at an anchored
regrowth. -/
theorem wall_valency {c : CubicCore n p} {c' : Utilities.Certificate.ExplicitPotential.Core n p}
    (m' : c.graph.MoveData) (hd : FacetDatum c.core c' degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀)) {block}
    (H : RegrowthAnchor4 w block) :
    (GluingDatum.incidentEdges (target := contract (moveWallData m' hd hG hDegree w ms).coverTarget
      (moveWallData m' hd hG hDegree w ms).hab (moveWallData m' hd hG hDegree w ms).hOne)
      ⟨(moveWallData m' hd hG hDegree w ms).a, (moveWallData m' hd hG hDegree w ms).hab⟩).card
      = 4 := by
  have hT : (limitIsoWallDatum m' hd hG hDegree w ms).targetVertex
      ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
        fst_ne_snd (w.frame.edgeOf w.column)⟩ =
      ⟨(moveWallData m' hd hG hDegree w ms).a, (moveWallData m' hd hG hDegree w ms).hab⟩ :=
    Subtype.ext (targetVertex_merge _ _ _ _ _ _)
  have h := ((limitIsoWallDatum m' hd hG hDegree w ms).incidentEdges_card_map
    ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
      fst_ne_snd (w.frame.edgeOf w.column)⟩).trans H.valency
  rw [hT] at h
  exact h

/-- **The admissible range is read off any labelling of the anchor**: a `K` admissible for
the indices of a labelling of a four-branch anchor satisfies the range clauses of the
general-`K` links, for every four-star. -/
theorem range_of_admissible {T : CFGraph} {degree : ℕ} {wall : T.V}
    {data : GluingDatum T degree} {star : W4TargetPairings.FourStar T wall}
    {anchor : WallBlock data wall} (source : FourBranchAnchor data star anchor)
    {A : data.SourceVertex} (L : Labelling4 data A)
    (hA : WallBlock.sourceVertex data wall anchor = A) {K : ℕ}
    (hK : L.indices.KAdmissible K) :
    (∀ l, K + 1 ≤ source.index l) ∧
      ∀ l, K + source.index l ≤ (data.vertexPartition wall).blockCard anchor.1 := by
  classical
  have hnd : nonDanglingValency data A = 4 := hA ▸ source.nonDanglingValency_eq_four
  have hSize : L.indices.A = (data.vertexPartition wall).blockCard anchor.1 := by
    rw [ValencyFourSplit.Labelling4.indices_A, ← hA]
    show (data.vertexPartition wall).blockCard ((data.vertexPartition wall).repr anchor.1) = _
    rw [anchor.2]
  have hIdx : ∀ l, ∃ i, source.index l = L.indices.k i := by
    intro l
    have hmem : source.sourceEdge l ∈ ValencyThreeSplit.ndAt data A := by
      rw [← hA, ValencyThreeSplit.mem_ndAt]
      refine ⟨source.sourceEdge_survives l, (incident_wallBlock_sourceVertex_iff data anchor _).mpr
        ⟨?_, WallBlock.ofSourceEdge_eq_of_rel data star anchor l (source.sheet l)
          (source.sheet_wall_rel l)⟩⟩
      show (data.sourceEdge (star.edge l) (source.sheet l)).1.1 ∈ _
      rw [GluingDatum.sourceEdge_target]
      exact star.edge_mem_incidentEdges l
    rw [L.ndAt_eq hnd] at hmem
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    refine ⟨i, ?_⟩
    rw [ValencyFourSplit.Labelling4.indices_k, hi]
    exact (GluingDatum.sourceEdgeIndex_sourceEdge data (star.edge l) (source.sheet l)).symm
  refine ⟨fun l ↦ ?_, fun l ↦ ?_⟩
  · obtain ⟨i, hi⟩ := hIdx l
    rw [hi]
    exact (hK i).1
  · obtain ⟨i, hi⟩ := hIdx l
    rw [hi, ← hSize]
    exact (hK i).2

/-- **One far class of every admissible `K`** (steps 1 and 2 of the route).  From a regrowth
`w` of `c₁` with a valency-four anchor and a labelling `L`, every `K` admissible for `L`'s
indices has a Whitehead link to a regrowth `w'` of `c₂ = farCore m''` in the same labelled
metric limit whose read `K` (under every anchor block and labelling) is `K`. -/
theorem exists_far_reads (hDegree : 3 ≤ degree) {c₁ c₂ : CubicCore n p}
    (m'' : c₁.graph.MoveData) (hback : farCore m'' = c₂)
    (hd : FacetDatum c₁.core (farCore m'').core degree m''.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀)
    (w : Regrowth c₁.core y₀ degree) {block} (H : RegrowthAnchor4 w block)
    (L : Labelling4 w.limit (anchorOf w block)) {K : ℕ} (hK : L.indices.KAdmissible K) :
    ∃ w' : Regrowth c₂.core y₀ degree,
      SameMetricLimit (c := c₁.core) (c' := c₂.core) (Sum.inl w) (Sum.inr w') ∧
      ∀ {block'} (_ : RegrowthAnchor4 w' block')
        (L' : Labelling4 w'.limit (anchorOf w' block')) (s : Split4), Reads4 L' s → s.K = K := by
  subst hback
  obtain ⟨ms⟩ := MemberSeedExists.nonempty_memberSeed_of_member (w.frame.member y₀) hDegree
  have hD2 : 2 ≤ degree := by omega
  have h4 := wall_valency m'' hd hG hD2 w ms H
  obtain ⟨anchorBlock, hAnchor⟩ :=
    NonTrivalentUniqueFourValent.exists_wallBlock_nonDanglingValency_eq_four
      (moveWallData m'' hd hG hD2 w ms).cover (moveWallData m'' hd hG hD2 w ms).fullDim
      (moveWallData m'' hd hG hD2 w ms).hc (moveWallData m'' hd hG hD2 w ms).hab
      (moveWallData m'' hd hG hD2 w ms).hOne (W4TargetPairings.FourStar.of_card h4)
      ((moveWallData m'' hd hG hD2 w ms).hCompat (pulledMove w ms m''))
      (moveWallData m'' hd hG hD2 w ms).coordinates _
      (moveWallData m'' hd hG hD2 w ms).hZeroCoord (moveWallData m'' hd hG hD2 w ms).hPosCoord
      (moveWallData m'' hd hG hD2 w ms).hFacetZero
  obtain ⟨wallStar, hLinks⟩ := linkReadsK_four_of_anchor (pulledMove w ms m'')
    (moveWallData m'' hd hG hD2 w ms) h4 anchorBlock hAnchor
  have hnd : nonDanglingValency (moveWallData m'' hd hG hD2 w ms).wallDatum
      ((limitIsoWallDatum m'' hd hG hD2 w ms).sourceVertexEquiv (anchorOf w block)) = 4 :=
    ((limitIsoWallDatum m'' hd hG hD2 w ms).nonDanglingValency_map
      (ValencyThreeSplit.connected_limit w) _).trans H.nd4
  have hX₀ := NonTrivalentUniqueFourValent.eq_of_nonDanglingValency_four
    (moveWallData m'' hd hG hD2 w ms).cover (moveWallData m'' hd hG hD2 w ms).fullDim
    (moveWallData m'' hd hG hD2 w ms).hc (moveWallData m'' hd hG hD2 w ms).hab
    (moveWallData m'' hd hG hD2 w ms).hOne (W4TargetPairings.FourStar.of_card h4)
    ((moveWallData m'' hd hG hD2 w ms).hCompat (pulledMove w ms m''))
    (moveWallData m'' hd hG hD2 w ms).coordinates _
    (moveWallData m'' hd hG hD2 w ms).hRows (moveWallData m'' hd hG hD2 w ms).hZeroCoord
    _ _ hAnchor hnd
  have hL := L.indices_transport (limitIsoWallDatum m'' hd hG hD2 w ms)
    (ValencyThreeSplit.connected_limit w)
  obtain ⟨hLow, hHigh⟩ := range_of_admissible
    (NonTrivalentUniqueFourValent.wallFourBranchAnchor (moveWallData m'' hd hG hD2 w ms).cover
      (moveWallData m'' hd hG hD2 w ms).fullDim (moveWallData m'' hd hG hD2 w ms).hc
      (moveWallData m'' hd hG hD2 w ms).hab (moveWallData m'' hd hG hD2 w ms).hOne wallStar
      ((moveWallData m'' hd hG hD2 w ms).hForest (pulledMove w ms m'')) anchorBlock hAnchor)
    (L.transport (limitIsoWallDatum m'' hd hG hD2 w ms) (ValencyThreeSplit.connected_limit w))
    hX₀ (hL ▸ hK)
  obtain ⟨link, hrec, hRead⟩ := hLinks K hLow hHigh
  refine ⟨farRegrowth m'' hd hG hD2 w ms link,
    GeneralKExitSetup.sameMetricLimit_of_columnReceipt m'' hd hG hD2 w ms link hrec, ?_⟩
  intro block' H' L' s hs
  exact hRead rfl (fst_ne_snd _) _ block' hrec.column_new H' L' s hs

/-- A presenting far-side regrowth that reads `K` realises `K` on the far side. -/
theorem exists_kIndexR_eq {c c' : Utilities.Certificate.ExplicitPotential.Core n p}
    {m : MetricFacetLimit c c' y₀ degree} (hm : V4Limit m) {e₀ : Fin p}
    (hpt : FacetPoint e₀ y₀) (w : Regrowth c' y₀ degree)
    (hw : MetricFacetLimit.ofRight (c := c) w = m) {K : ℕ}
    (hread : ∀ {block} (_ : RegrowthAnchor4 w block)
      (L : Labelling4 w.limit (anchorOf w block)) (s : Split4), Reads4 L s → s.K = K) :
    ∃ x, kIndexR hm e₀ hpt x = K := by
  obtain ⟨block, H⟩ := hm.2 w hw
  obtain ⟨L⟩ := ValencyFourSplit.nonempty_labelling4 _ _ H.nd4
  obtain ⟨s, hs, -, -⟩ := ValencyFourSplit.existsUnique_reads4 w.frame.fullDim L H
  exact ⟨⟨FrameClass.mk w.frame, w, rfl, hw⟩,
    (ValencyFourSplit.kIndexR_spec hm e₀ hpt _ w H L rfl hs).trans (hread H L s hs)⟩

/-- A presenting near-side regrowth that reads `K` realises `K` on the near side. -/
theorem exists_kIndexL_eq {c c' : Utilities.Certificate.ExplicitPotential.Core n p}
    {m : MetricFacetLimit c c' y₀ degree} (hm : V4Limit m) {e₀ : Fin p}
    (hpt : FacetPoint e₀ y₀) (w : Regrowth c y₀ degree)
    (hw : MetricFacetLimit.ofLeft (c' := c') w = m) {K : ℕ}
    (hread : ∀ {block} (_ : RegrowthAnchor4 w block)
      (L : Labelling4 w.limit (anchorOf w block)) (s : Split4), Reads4 L s → s.K = K) :
    ∃ x, kIndexL hm e₀ hpt x = K := by
  obtain ⟨block, H⟩ := hm.1 w hw
  obtain ⟨L⟩ := ValencyFourSplit.nonempty_labelling4 _ _ H.nd4
  obtain ⟨s, hs, -, -⟩ := ValencyFourSplit.existsUnique_reads4 w.frame.fullDim L H
  exact ⟨⟨FrameClass.mk w.frame, w, rfl, hw⟩,
    (ValencyFourSplit.kIndexL_spec hm e₀ hpt _ w H L rfl hs).trans (hread H L s hs)⟩

/-- **Admissibility is a limit invariant**: along an isomorphism of two anchored regrowth
limits, a labelling of the first transports to one of the second with the same indices. -/
theorem exists_admissible_of_iso {c₁ c₂ : Utilities.Certificate.ExplicitPotential.Core n p}
    {e₀ : Fin p} (hpt : FacetPoint e₀ y₀) (w₁ : Regrowth c₁ y₀ degree)
    (w₂ : Regrowth c₂ y₀ degree) {block₁ block₂} (H₁ : RegrowthAnchor4 w₁ block₁)
    (H₂ : RegrowthAnchor4 w₂ block₂) (ψ : GeometricDatumIso w₁.limit w₂.limit)
    (L₁ : Labelling4 w₁.limit (anchorOf w₁ block₁)) {K : ℕ} (hK : L₁.indices.KAdmissible K) :
    ∃ L₂ : Labelling4 w₂.limit (anchorOf w₂ block₂), L₂.indices.KAdmissible K := by
  obtain ⟨L₂, -, -, -, hidx, -⟩ := ValencyFourSplit.regrowth_reads4 w₁ w₂ H₁ H₂ e₀ hpt ψ L₁
  exact ⟨L₂, hidx ▸ hK⟩

end Facet

/-! ## 5.  Per-`K` realisation on both sides, at every resolved datum -/

section Census

open FacetAdapterPilot ValencyThreeGeneral FacetMachine
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)
open DraismaVargas.Count.WallStar (Regrowth)
open ValencyFourSplit (RegrowthAnchor4 V4Limit kIndexL kIndexR)
open ValencyThreeSplit (anchorOf)
open CensusAssembly (ResolvedDatum V4InputsSupply V4ClauseSupply)

variable {n p degree : ℕ}

/-- **The realisation conjuncts of `CensusAssembly.V4InputsSupply`**, at every resolved datum
and every valency-four metric limit, in degree at least three: the hypothesis of
`ValencyFourRigidity.v4InputsSupply_of_realisation`, verbatim.

Every admissible `K` of a presenting regrowth `w₀` (either side) is realised on the far side by
a general-`K` link from `w₀` (`exists_far_reads`), and on `w₀`'s own side by the reversed link
from that far regrowth (`exists_far_reads` at `revMove`); admissibility is carried across by
`exists_admissible_of_iso`. -/
theorem hex_of_resolved (hDegree : 3 ≤ degree) :
    ∀ (c c' : CubicCore n p) (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ)
      (R : ResolvedDatum c c' degree e₀ y₀ ε) (m : MetricFacetLimit c.core c'.core y₀ degree)
      (hm : V4Limit m),
      (∀ (w₀ : Regrowth c.core y₀ degree), MetricFacetLimit.ofLeft (c' := c'.core) w₀ = m →
        ∀ {block₀} (_ : RegrowthAnchor4 w₀ block₀)
          (L₀ : Labelling4 w₀.limit (ValencyThreeSplit.anchorOf w₀ block₀)) (K : ℕ),
          L₀.indices.KAdmissible K →
            (∃ x, kIndexL hm e₀ R.datum.point x = K) ∧ ∃ x, kIndexR hm e₀ R.datum.point x = K) ∧
      (∀ (w₀ : Regrowth c'.core y₀ degree), MetricFacetLimit.ofRight (c := c.core) w₀ = m →
        ∀ {block₀} (_ : RegrowthAnchor4 w₀ block₀)
          (L₀ : Labelling4 w₀.limit (ValencyThreeSplit.anchorOf w₀ block₀)) (K : ℕ),
          L₀.indices.KAdmissible K →
            (∃ x, kIndexL hm e₀ R.datum.point x = K) ∧ ∃ x, kIndexR hm e₀ R.datum.point x = K) := by
  intro c c' e₀ y₀ ε R m hm
  obtain ⟨m', hm', rfl⟩ := R.move
  have hc' : c' = farCore m' := CubicCore.graph_injective (hm'.trans (farCore_graph m').symm)
  subst hc'
  have hpt := R.datum.point
  have hd := R.datum
  have hG := R.generic
  constructor
  · intro w₀ hw₀ block₀ H₀ L₀ K hK
    obtain ⟨w', hsame, hread⟩ := exists_far_reads hDegree m' rfl hd hG w₀ H₀ L₀ hK
    have hw' : MetricFacetLimit.ofRight (c := c.core) w' = m :=
      (Quotient.sound hsame).symm.trans hw₀
    refine ⟨?_, exists_kIndexR_eq hm hpt w' hw' hread⟩
    obtain ⟨block', H'⟩ := hm.2 w' hw'
    obtain ⟨L', hK'⟩ := exists_admissible_of_iso hpt w₀ w' H₀ H' hsame.choose L₀ hK
    obtain ⟨w'', hsame', hread'⟩ := exists_far_reads hDegree (revMove m') (farCore_revMove m')
      (facetDatum_rev m' hd) hG w' H' L' hK'
    have h3 : SameMetricLimit (c := c.core) (c' := (farCore m').core) (Sum.inr w')
        (Sum.inl w'') := hsame'
    have hw'' : MetricFacetLimit.ofLeft (c' := (farCore m').core) w'' = m :=
      (Quotient.sound h3).symm.trans hw'
    exact exists_kIndexL_eq hm hpt w'' hw'' hread'
  · intro w₀ hw₀ block₀ H₀ L₀ K hK
    obtain ⟨w'', hsame, hread⟩ := exists_far_reads hDegree (revMove m') (farCore_revMove m')
      (facetDatum_rev m' hd) hG w₀ H₀ L₀ hK
    have h3 : SameMetricLimit (c := c.core) (c' := (farCore m').core) (Sum.inr w₀)
        (Sum.inl w'') := hsame
    have hw'' : MetricFacetLimit.ofLeft (c' := (farCore m').core) w'' = m :=
      (Quotient.sound h3).symm.trans hw₀
    refine ⟨exists_kIndexL_eq hm hpt w'' hw'' hread, ?_⟩
    obtain ⟨block'', H''⟩ := hm.1 w'' hw''
    obtain ⟨L'', hK''⟩ := exists_admissible_of_iso hpt w₀ w'' H₀ H'' hsame.choose L₀ hK
    obtain ⟨w', hsame', hread'⟩ := exists_far_reads hDegree m' rfl hd hG w'' H'' L'' hK''
    have hw' : MetricFacetLimit.ofRight (c := c.core) w' = m :=
      (Quotient.sound hsame').symm.trans hw''
    exact exists_kIndexR_eq hm hpt w' hw' hread'

/-- **`CensusAssembly.V4InputsSupply`**, in degree at least three, for cores with at least three
vertices: the injectivity of `ValencyFourRigidity` (`ValencyFourRigidity.injective_of_resolved`) and the
realisation above. -/
theorem v4InputsSupply (hDegree : 3 ≤ degree) (hn : 3 ≤ n) : V4InputsSupply n p degree :=
  ValencyFourRigidity.v4InputsSupply_of_realisation hn (hex_of_resolved hDegree)

/-- **`CensusAssembly.V4ClauseSupply 10 15 4`**: the valency-four clause at genus six. -/
theorem v4ClauseSupply_genusSix : V4ClauseSupply (4 * 2 + 2) (6 * 2 + 3) (2 + 2) :=
  CensusAssembly.v4ClauseSupply_of_inputs (v4InputsSupply (by norm_num) (by norm_num))

end Census

end DraismaVargas.Count.ValencyFourRealisation
