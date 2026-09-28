import DraismaVargasCount.GeneralKRowGauge
import DraismaVargasCount.GeneralKSourceFacts

/-!
# The general-`K` row dictionary at a four-valent wall

Vargas, Part II (arXiv:2609.09109), the section on changing combinatorial type: the
rigidity above `w_0` (`lemma-above-w0`), the labelling convention that, apart from
`h_1^(q)`, the edges of `H^(q)` correspond bijectively to those of `H_0`, and case
`{v4-nd4}` (`subsec-case-v4`), for every admissible `K`.

The datum-generic row dictionary (`GeneralKRowCore`, `GeneralKRowStar`,
`GeneralKRowEquiv`) is instantiated at the general-`K` candidate
`GeneralKExitSetup.candK` over the gauged wall datum `position.datum`:

* `starHyp`: at every non-anchor wall block the candidate's resolution is the
  canonical W4 star, and the gauged datum is target-direction injective with
  surviving valency at most three there (transported from the wall datum across
  the gauge, `GeneralKRowGauge`);
* `anchorHyp`: above the anchor block the two endpoint classes `A₋`, `A₊` carry
  at least three survivors each (`three_le_nd_side`), every other endpoint class
  is a singleton carrying at most one (`nd_le_one_of_not_mem`), so no vertex
  there is divalent; every surviving new occurrence there is the bridge
  (`new_eq_bridge`), and the bridge survives (`bridge_survives`);
* `rowEquivK`: the row equivalence
  `StablePath (candK …).datum ≃ Option (StablePath position.datum)`, with its
  simp lemmas.

* `rowEquivWall`: the same dictionary read against the incoming wall datum,
  through the gauge.

The only hypothesis is the localized canonical background `hBg`
(`GeneralKSourceFacts.LocalCanonicalBackground`, inhabited at every wall by
`GeneralKSourceFacts.exists_localCanonicalBackground`); the global
`GeneralKExitSetup.CanonicalBackground` is not satisfiable in general
(`GeneralKBackground.not_exists_literalBackground`).  A
localized star is again a star (`isStar_localize`).  Trivalence and path ends
of the candidate are **not** used.

## What is NOT proved here

* The upper bound `nd ≤ 3` at the two endpoint classes: the anchor census here
  gives `nd ≥ 3` there and `nd ≤ 1` at the singleton classes, which is all the
  row dictionary needs.  Trivalence is
  `GeneralKSourceFacts.candidate_trivalent`.
* Any incidence equivalence with the `K = 0` candidate.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.GeneralKRowsK

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.Count.GeneralKReceipts
open DraismaVargas.Count.GeneralKExitSetup
open DraismaVargas.Count.GeneralKRowCore
open DraismaVargas.Count.GeneralKRowStar
open DraismaVargas.Count.GeneralKRowEquiv
open DraismaVargas.Count.GeneralKRowGauge

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

variable (position : GeneralKReceipts.Position
    (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      wallStar (wd.hForest m) anchorBlock hAnchor) pairing
    (smallerSide (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor) pairing))
  (geometry : GeneralKReceipts.PairingBackground position.datum wallStar pairing
    anchorBlock.1)

local notation "cK" => (candK m wd wallStar anchorBlock hAnchor pairing position geometry)
local notation "vNoRet" =>
  (StablePathFacetContraction.noContractedReturn_of_fourStar wd.cover wd.fullDim wd.hc wd.hab
    wd.hOne wallStar)
local notation "vWallLab" =>
  (NonTrivalentValencyTwoExit.wallLab wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m)
    vNoRet wd.coordinates (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord wd.hFacetZero)
local notation "vRowChart" =>
  (NonTrivalentValencyTwoExit.rowChart wd.cover wd.fullDim (label m.base)
    (contracted := wd.contracted))
local notation "vColChart" =>
  (NonTrivalentValencyTwoExit.colChart wd.cover wd.fullDim (contracted := wd.contracted))

/-! ## 1.  Validity, genus and the background blocks -/

theorem datum_valid' : position.datum.Valid := position.datum_valid vVal

theorem cK_right : (cK).right = wallStar.right pairing := rfl

theorem cK_resolution_of_not_rel (block : Fin degree)
    (hBlock : ¬(position.datum.vertexPartition ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 block) :
    (cK).resolution block = geometry.resolution block := by
  unfold candK Position.candidate GeneralKReceipts.PairingBackground.background
    GlobalM11Arbitrary.Background.install
  exact LocalResolution.onBlock_of_not_rel _ _ _ _ _ hBlock

theorem cK_resolution_of_rel (block : Fin degree)
    (hBlock : (position.datum.vertexPartition ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 block) :
    (cK).resolution block = position.selected :=
  position.candidate_resolution_of_wall_rel vConn vGen vNG geometry block hBlock

/-- Localizing a star resolution to one wall block keeps it a star: off the
block the localized resolution is the joined one, `(P, P, P)`. -/
theorem isStar_localize {d : ℕ} (P : SheetPartition d) (B : Fin d) (R : LocalResolution d)
    (hR : R.ContractsTo P) (hS : NonTrivalentValencyFourRows.IsStar P R) :
    NonTrivalentValencyFourRows.IsStar P (GeneralKBackground.localize P B R hR) := by
  rcases hS with ⟨hl, hn⟩ | ⟨hr, hn⟩
  · refine Or.inl ⟨SheetPartition.ext_repr _ _ (funext fun s ↦ ?_),
      SheetPartition.ext_repr _ _ (funext fun s ↦ ?_)⟩
    · show (LocalResolution.onBlock P B R (fun _ ↦ joinedResolutionAt P) (P.repr s)).left.repr s =
        P.repr s
      by_cases h : P.Rel B (P.repr s)
      · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ h, hl]
      · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ h]
        rfl
    · show (LocalResolution.onBlock P B R (fun _ ↦ joinedResolutionAt P) (P.repr s)).newEdge.repr s =
        (LocalResolution.onBlock P B R (fun _ ↦ joinedResolutionAt P) (P.repr s)).right.repr s
      by_cases h : P.Rel B (P.repr s)
      · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ h, hn]
      · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ h]
        rfl
  · refine Or.inr ⟨SheetPartition.ext_repr _ _ (funext fun s ↦ ?_),
      SheetPartition.ext_repr _ _ (funext fun s ↦ ?_)⟩
    · show (LocalResolution.onBlock P B R (fun _ ↦ joinedResolutionAt P) (P.repr s)).right.repr s =
        P.repr s
      by_cases h : P.Rel B (P.repr s)
      · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ h, hr]
      · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ h]
        rfl
    · show (LocalResolution.onBlock P B R (fun _ ↦ joinedResolutionAt P) (P.repr s)).newEdge.repr s =
        (LocalResolution.onBlock P B R (fun _ ↦ joinedResolutionAt P) (P.repr s)).left.repr s
      by_cases h : P.Rel B (P.repr s)
      · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ h, hn]
      · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ h]
        rfl

/-- The candidate keeps the source genus of the gauged datum. -/
theorem cK_genus
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    genus (cK).datum.sourceGraph = genus position.datum.sourceGraph :=
  GeneralKBackground.candidate_sourceGenus_of_local position (vProf) vConn vGen vNG geometry hBg

/-! ## 2.  The non-anchor blocks: `StarHyp` -/

theorem sourceEndpoint_repr {tgt : CFGraph} (data : GluingDatum tgt degree) (v : tgt.V)
    (s : Fin degree) :
    data.sourceEndpoint v ((data.vertexPartition v).repr s) = data.sourceEndpoint v s :=
  Subtype.ext (Prod.ext rfl ((data.vertexPartition v).repr_idem s))

/-- The gauge fixes every sheet outside the anchor block. -/
theorem gauge_fix (l : Fin 4) {s : Fin degree}
    (hs : ¬(position.datum.vertexPartition ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 s) :
    position.gauge.perm l s = s := by
  refine (position.gauge.preserving l).2 s (fun hMem ↦ hs ?_)
  rw [position.datum_vertexPartition_wall]
  exact (SheetPartition.mem_block_iff _ _ _).mp hMem

/-- At most two wall edges on one side of the pairing. -/
theorem side_three (b : Bool)
    (e₁ e₂ e₃ : (contract wd.coverTarget wd.hab wd.hOne).edges)
    (h₁ : e₁ ∈ GluingDatum.incidentEdges (⟨wd.a, wd.hab⟩ :
      (contract wd.coverTarget wd.hab wd.hOne).V))
    (h₂ : e₂ ∈ GluingDatum.incidentEdges (⟨wd.a, wd.hab⟩ :
      (contract wd.coverTarget wd.hab wd.hOne).V))
    (h₃ : e₃ ∈ GluingDatum.incidentEdges (⟨wd.a, wd.hab⟩ :
      (contract wd.coverTarget wd.hab wd.hOne).V))
    (s₁ : wallStar.right pairing e₁ = b) (s₂ : wallStar.right pairing e₂ = b)
    (s₃ : wallStar.right pairing e₃ = b) : e₁ = e₂ ∨ e₁ = e₃ ∨ e₂ = e₃ := by
  classical
  obtain ⟨l₁, rfl⟩ := wallStar.exists_edge_eq e₁ h₁
  obtain ⟨l₂, rfl⟩ := wallStar.exists_edge_eq e₂ h₂
  obtain ⟨l₃, rfl⟩ := wallStar.exists_edge_eq e₃ h₃
  replace s₁ := (wallStar.right_edge pairing l₁).symm.trans s₁
  replace s₂ := (wallStar.right_edge pairing l₂).symm.trans s₂
  replace s₃ := (wallStar.right_edge pairing l₃).symm.trans s₃
  by_cases h₁₂ : l₁ = l₂
  · exact Or.inl (by rw [h₁₂])
  by_cases h₁₃ : l₁ = l₃
  · exact Or.inr (Or.inl (by rw [h₁₃]))
  by_cases h₂₃ : l₂ = l₃
  · exact Or.inr (Or.inr (by rw [h₂₃]))
  exfalso
  have hMem : ∀ l ∈ ({l₁, l₂, l₃} : Finset (Fin 4)),
      l ∈ W4TargetPairings.Pairing.labelsOnSide pairing b := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rw [W4TargetPairings.Pairing.mem_labelsOnSide]
    rcases hl with rfl | rfl | rfl
    · exact s₁
    · exact s₂
    · exact s₃
  have hCard : ({l₁, l₂, l₃} : Finset (Fin 4)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h₁₂, h₁₃]),
      Finset.card_insert_of_notMem (by simp [h₂₃]), Finset.card_singleton]
  have hLe := Finset.card_le_card (Finset.subset_iff.mpr hMem)
  rw [hCard, W4TargetPairings.Pairing.card_labelsOnSide] at hLe
  omega

/-- **The hypotheses on the non-anchor blocks, discharged at the general-`K`
candidate.** -/
theorem starHyp
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    StarHyp (cK) anchorBlock.1 where
  valid := datum_valid' m wd wallStar anchorBlock hAnchor pairing position
  genus := cK_genus m wd wallStar anchorBlock hAnchor pairing position geometry hBg
  star := by
    intro x hx
    have hR : ¬(position.datum.vertexPartition ⟨wd.a, wd.hab⟩).Rel anchorBlock.1
        ((position.datum.vertexPartition ⟨wd.a, wd.hab⟩).repr x) :=
      fun h ↦ hx (h.trans (SheetPartition.rel_repr_right _ x).symm)
    rw [cK_resolution_of_not_rel m wd wallStar anchorBlock hAnchor pairing position geometry _
      hR, hBg _ hR]
    exact isStar_localize _ _ _ _
      (NonTrivalentValencyFourRows.isStar_blockwiseResolution (star := wallStar) pairing
        (vProf).pattern _)
  inj := by
    intro x hx o₁ o₂ h₁ h₂ hT
    obtain ⟨l, hl⟩ := wallStar.exists_edge_eq o₁.1.1 h₁.2.1
    have hs₁ := not_rel_of_rel hx h₁.2.2
    have hs₂ := not_rel_of_rel hx h₂.2.2
    have hf₁ := gauge_fix m wd wallStar anchorBlock hAnchor pairing position l hs₁
    have hf₂ := gauge_fix m wd wallStar anchorBlock hAnchor pairing position l hs₂
    have e₁ : o₁ = position.datum.sourceEdge (wallStar.edge l) (position.gauge.perm l o₁.1.2) := by
      rw [hf₁, hl]
      exact (GluingDatum.sourceEdge_self _ o₁).symm
    have e₂ : o₂ = position.datum.sourceEdge (wallStar.edge l) (position.gauge.perm l o₂.1.2) := by
      rw [hf₂, hl, hT]
      exact (GluingDatum.sourceEdge_self _ o₂).symm
    have w₁ : ¬IsDangling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdge (wallStar.edge l) o₁.1.2) :=
      fun h ↦ h₁.1 (e₁ ▸ (isDangling_gauged_iff wallStar position.gauge vConn vGen vVal l _).mpr h)
    have w₂ : ¬IsDangling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdge (wallStar.edge l) o₂.1.2) :=
      fun h ↦ h₂.1 (e₂ ▸ (isDangling_gauged_iff wallStar position.gauge vConn vGen vVal l _).mpr h)
    have hW := position.datum_vertexPartition_wall
    have hr₁ : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
        ⟨wd.a, wd.hab⟩).Rel (WallBlock.ofSheet (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ x).1 o₁.1.2 := by
      have := h₁.2.2
      rw [hW] at this
      exact (SheetPartition.rel_repr_left _ x).trans this
    have hr₂ : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
        ⟨wd.a, wd.hab⟩).Rel (WallBlock.ofSheet (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ x).1 o₂.1.2 := by
      have := h₂.2.2
      rw [hW] at this
      exact (SheetPartition.rel_repr_left _ x).trans this
    have hWEq := (NonTrivalentValencyFourRowEquivFinal.wall_starInjective wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne wallStar (wd.hForest m)
      (WallBlock.ofSheet (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ x)).unique
      l _ _ (WallBlock.ofSourceEdge_eq_of_rel _ wallStar _ l _ hr₁)
      (WallBlock.ofSourceEdge_eq_of_rel _ wallStar _ l _ hr₂) rfl rfl w₁ w₂
    have hRelE := congrArg (fun e : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceEdge ↦
      e.1.2) hWEq
    rw [e₁, e₂]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · show ((position.datum.edgePartition (wallStar.edge l)).Rel _ _)
      rw [position.gauge.gaugedData_edgePartition wallStar vConn vGen l]
      exact (SheetPartition.relabel_rel_iff _ _ _ _).mpr hRelE
  valency := by
    intro x hx
    rw [nonDanglingValency_gauged_wall wallStar position.gauge vVal x]
    have hNot : ¬((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
        ⟨wd.a, wd.hab⟩).Rel anchorBlock.1
          (WallBlock.ofSheet (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            ⟨wd.a, wd.hab⟩ x).1 := by
      intro h
      apply hx
      rw [position.datum_vertexPartition_wall]
      exact h.trans (SheetPartition.rel_repr_right _ x).symm
    have hB := NonTrivalentUniqueFourValent.nonDanglingValency_wallBlock_le_three wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne wallStar (wd.hCompat m) wd.coordinates (label m.base)
      wd.hRows wd.hZeroCoord anchorBlock hAnchor _ hNot
    exact (congrArg (nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne))
      (sourceEndpoint_repr (contractDatum wd.cover wd.hc wd.hab wd.hOne) _ x).symm).trans_le hB
  side := side_three m wd wallStar pairing

/-! ## 3.  The anchor block: `AnchorHyp` -/

/-- The endpoint class of a Boolean side at the anchor: `A₋` on the oriented
side, `A₊` on the other. -/
noncomputable def sideSheets (b : Bool) : Finset (Fin degree) :=
  if b = smallerSide vSrc pairing then position.split.minusSheets
  else position.split.plusSheets

theorem sideSheets_labelRight (l : Fin 4) :
    gaugedBlock vSrc position.gauge l ⊆
      sideSheets m wd wallStar anchorBlock hAnchor pairing position
        (W4TargetPairings.Pairing.labelRight pairing l) := by
  unfold sideSheets
  split_ifs with h
  · exact position.minus_sub l h
  · apply position.plus_sub l
    cases hv : W4TargetPairings.Pairing.labelRight pairing l <;>
      cases hs : smallerSide vSrc pairing <;> simp_all

theorem bridge_mem_sideSheets (b : Bool) :
    position.split.bridge ∈ sideSheets m wd wallStar anchorBlock hAnchor pairing position b := by
  unfold sideSheets
  split_ifs
  · exact position.split.bridge_mem_minus
  · exact position.split.bridge_mem_plus

theorem endpoint_rel_bridge_iff (b : Bool) (s : Fin degree) :
    (position.endpoint b).Rel position.split.bridge s ↔
      s ∈ sideSheets m wd wallStar anchorBlock hAnchor pairing position b := by
  unfold sideSheets Position.endpoint
  split_ifs
  · exact position.split.left_rel_bridge_iff s
  · exact position.split.right_rel_bridge_iff s

theorem endpoint_rel_of_mem (b : Bool) {s t : Fin degree}
    (hs : s ∈ sideSheets m wd wallStar anchorBlock hAnchor pairing position b)
    (ht : t ∈ sideSheets m wd wallStar anchorBlock hAnchor pairing position b) :
    (position.endpoint b).Rel s t :=
  ((endpoint_rel_bridge_iff m wd wallStar anchorBlock hAnchor pairing position b s).mpr
    hs).symm.trans
    ((endpoint_rel_bridge_iff m wd wallStar anchorBlock hAnchor pairing position b t).mpr ht)

theorem endpoint_eq_of_not_mem (b : Bool) {s t : Fin degree}
    (hW : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
      ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 s)
    (hs : s ∉ sideSheets m wd wallStar anchorBlock hAnchor pairing position b)
    (h : (position.endpoint b).Rel s t) : t = s := by
  have hMem : t ∈ (position.endpoint b).block s := (SheetPartition.mem_block_iff _ _ _).mpr h
  unfold sideSheets at hs
  unfold Position.endpoint at hMem
  split_ifs at hs hMem
  · rw [position.split.left_block_of_not_mem hs hW] at hMem
    exact Finset.mem_singleton.mp hMem
  · rw [position.split.right_block_of_not_mem hs hW] at hMem
    exact Finset.mem_singleton.mp hMem

theorem endPart_anchor (b : Bool) {s : Fin degree}
    (hs : (position.datum.vertexPartition ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 s) (y : Fin degree) :
    (endPart (cK) b).Rel s y ↔ (position.endpoint b).Rel s y := by
  have h1 := endPart_rel_iff (cK) b s y
  rw [cK_resolution_of_rel m wd wallStar anchorBlock hAnchor pairing position
    geometry _ (hs.trans (SheetPartition.rel_repr_right _ s)), position.selected_endpoint] at h1
  exact h1

theorem newPart_anchor {s : Fin degree}
    (hs : (position.datum.vertexPartition ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 s) (y : Fin degree) :
    (pasted (cK)).newEdge.Rel s y ↔ position.split.newEdge.Rel s y := by
  have h1 := newPart_rel_iff (cK) s y
  rw [cK_resolution_of_rel m wd wallStar anchorBlock hAnchor pairing position
    geometry _ (hs.trans (SheetPartition.rel_repr_right _ s)), position.selected_newEdge] at h1
  exact h1

/-- A surviving incoming occurrence of a star label through a sheet of the
anchor block lies in that label's branch class. -/
theorem mem_branchBlock_of_survives (l : Fin 4) {t : Fin degree}
    (hW : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
      ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 t)
    (hSurv : ¬IsDangling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdge (wallStar.edge l) t)) :
    t ∈ branchBlock vSrc l := by
  have hEqual := (vSrc).target_injective.unique l ((vSrc).sourceEdge l)
    ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdge (wallStar.edge l) t)
    (WallBlock.ofSourceEdge_eq_of_rel _ wallStar anchorBlock l ((vSrc).sheet l)
      ((vSrc).sheet_wall_rel l))
    (WallBlock.ofSourceEdge_eq_of_rel _ wallStar anchorBlock l t hW)
    rfl rfl ((vSrc).sourceEdge_survives l) hSurv
  exact (SheetPartition.mem_block_iff _ _ _).mpr
    (congrArg (fun edge : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceEdge ↦
      edge.1.2) hEqual)

/-- The gauged survivor of a star label at the anchor. -/
noncomputable def survG (l : Fin 4) : position.datum.SourceEdge :=
  position.datum.sourceEdge (wallStar.edge l) (position.gauge.perm l ((vSrc).sheet l))

theorem survG_survives (l : Fin 4) :
    ¬IsDangling position.datum (survG m wd wallStar anchorBlock hAnchor pairing position l) :=
  fun h ↦ (vSrc).sourceEdge_survives l
    ((isDangling_gauged_iff wallStar position.gauge vConn vGen vVal l _).mp h)

theorem survG_mem (l : Fin 4) :
    (survG m wd wallStar anchorBlock hAnchor pairing position l).1.2 ∈
      gaugedBlock vSrc position.gauge l := by
  apply gaugedBlock_closed vSrc position.gauge l (active_mem_gaugedBlock vSrc position.gauge l)
  show (gaugedEdge wallStar position.gauge l).Rel _
    ((position.datum.edgePartition (wallStar.edge l)).repr _)
  rw [position.gauge.gaugedData_edgePartition wallStar vConn vGen l]
  exact SheetPartition.rel_repr_right _ _

theorem survG_incident (l : Fin 4) {s : Fin degree}
    (hs : (position.datum.vertexPartition ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 s)
    (hsA : s ∈ sideSheets m wd wallStar anchorBlock hAnchor pairing position
      (W4TargetPairings.Pairing.labelRight pairing l)) :
    Incident (cK).datum ((cK).oldSourceEdge (survG m wd wallStar anchorBlock hAnchor pairing
      position l)) (epv (cK) (W4TargetPairings.Pairing.labelRight pairing l) s) := by
  refine (oldSourceEdge_incident_iff (cK) _ _ s).mpr ⟨wallStar.edge_mem_incidentEdges l,
    wallStar.right_edge pairing l, ?_⟩
  refine (endPart_anchor m wd wallStar anchorBlock hAnchor pairing position geometry _ hs _).mpr ?_
  exact endpoint_rel_of_mem m wd wallStar anchorBlock hAnchor pairing position _ hsA
    (sideSheets_labelRight m wd wallStar anchorBlock hAnchor pairing position l
      (survG_mem m wd wallStar anchorBlock hAnchor pairing position l))

theorem survG_mem_ndI (l : Fin 4) {b : Bool} (hl : W4TargetPairings.Pairing.labelRight pairing l = b)
    {s : Fin degree}
    (hs : (position.datum.vertexPartition ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 s)
    (hsA : s ∈ sideSheets m wd wallStar anchorBlock hAnchor pairing position b) :
    (cK).oldSourceEdge (survG m wd wallStar anchorBlock hAnchor pairing position l) ∈
      nonDanglingIncident (cK).datum (epv (cK) b s) := by
  subst hl
  exact (mem_nonDanglingIncident _ _ _).mpr
    ⟨ResolutionSurvival.not_isDangling_oldSourceEdge _
      (datum_valid' m wd wallStar anchorBlock hAnchor pairing position).1 _
      (survG_survives m wd wallStar anchorBlock hAnchor pairing position l),
    survG_incident m wd wallStar anchorBlock hAnchor pairing position geometry l hs hsA⟩

theorem bridge_rel :
    (position.datum.vertexPartition ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 position.split.bridge := by
  rw [position.datum_vertexPartition_wall]
  exact (SheetPartition.mem_block_iff _ _ _).mp
    (position.split.bridgeSheets_subset position.split.bridge_mem_bridgeSheets)

/-- A new occurrence survives once both of its ends carry a surviving
occurrence (a dangling side would contain one end). -/
theorem newSourceEdge_survives_of_nd {tgt : CFGraph} {G' : GluingDatum tgt degree}
    {w : tgt.V} (C : BalancedGlobal.Candidate tgt degree G' w) (s : Fin degree)
    (h₀ : nonDanglingValency C.datum (epv C false s) ≠ 0)
    (h₁ : nonDanglingValency C.datum (epv C true s) ≠ 0) :
    ¬IsDangling C.datum (C.newSourceEdge s) := by
  rintro (hD | hD)
  · obtain ⟨cut⟩ := hD
    apply h₀
    have h := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side _ cut cut.left_mem
    rw [sourceEnds_newSourceEdge] at h
    exact h
  · obtain ⟨cut⟩ := hD
    apply h₁
    have h := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side _ cut cut.left_mem
    rw [sourceEnds_newSourceEdge] at h
    exact h

/-- **The bridge survives** (skeleton item B3, in the form needed here). -/
theorem bridge_survives :
    ¬IsDangling (cK).datum ((cK).newSourceEdge position.split.bridge) := by
  have hb := bridge_rel m wd wallStar anchorBlock hAnchor pairing position
  refine newSourceEdge_survives_of_nd (cK) _ ?_ ?_
  · exact ClassInjectivity.nonDanglingValency_ne_zero_of_incident _
      ((mem_nonDanglingIncident _ _ _).mp (survG_mem_ndI m wd wallStar anchorBlock hAnchor pairing
        position geometry (firstLabel pairing false) (labelRight_firstLabel pairing false) hb
        (bridge_mem_sideSheets m wd wallStar anchorBlock hAnchor pairing position false))).1
      ((mem_nonDanglingIncident _ _ _).mp (survG_mem_ndI m wd wallStar anchorBlock hAnchor pairing
        position geometry (firstLabel pairing false) (labelRight_firstLabel pairing false) hb
        (bridge_mem_sideSheets m wd wallStar anchorBlock hAnchor pairing position false))).2
  · exact ClassInjectivity.nonDanglingValency_ne_zero_of_incident _
      ((mem_nonDanglingIncident _ _ _).mp (survG_mem_ndI m wd wallStar anchorBlock hAnchor pairing
        position geometry (firstLabel pairing true) (labelRight_firstLabel pairing true) hb
        (bridge_mem_sideSheets m wd wallStar anchorBlock hAnchor pairing position true))).1
      ((mem_nonDanglingIncident _ _ _).mp (survG_mem_ndI m wd wallStar anchorBlock hAnchor pairing
        position geometry (firstLabel pairing true) (labelRight_firstLabel pairing true) hb
        (bridge_mem_sideSheets m wd wallStar anchorBlock hAnchor pairing position true))).2

/-- **An endpoint class of the anchor is trivalent from below**: the two
gauged survivors of its side and the bridge. -/
theorem three_le_nd_side (b : Bool) {s : Fin degree}
    (hs : (position.datum.vertexPartition ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 s)
    (hsA : s ∈ sideSheets m wd wallStar anchorBlock hAnchor pairing position b) :
    3 ≤ nonDanglingValency (cK).datum (epv (cK) b s) := by
  have h₁ := survG_mem_ndI m wd wallStar anchorBlock hAnchor pairing position geometry
    (firstLabel pairing b) (labelRight_firstLabel pairing b) hs hsA
  have h₂ := survG_mem_ndI m wd wallStar anchorBlock hAnchor pairing position geometry
    (secondLabel pairing b) (labelRight_secondLabel pairing b) hs hsA
  have h₃ : (cK).newSourceEdge position.split.bridge ∈
      nonDanglingIncident (cK).datum (epv (cK) b s) := by
    refine (mem_nonDanglingIncident _ _ _).mpr
      ⟨bridge_survives m wd wallStar anchorBlock hAnchor pairing position geometry, ?_⟩
    refine (newSourceEdge_incident_iff (cK) b _ s).mpr ?_
    refine (endPart_anchor m wd wallStar anchorBlock hAnchor pairing position geometry b hs
      _).mpr ?_
    exact endpoint_rel_of_mem m wd wallStar anchorBlock hAnchor pairing position b hsA
      (bridge_mem_sideSheets m wd wallStar anchorBlock hAnchor pairing position b)
  refine three_le_nd h₁ h₂ h₃ ?_ (new_ne_old (cK) _ _).symm (new_ne_old (cK) _ _).symm
  intro h
  have h' := congrArg (fun e : position.datum.SourceEdge ↦ e.1.1)
    (ResolutionCut.oldSourceEdge_injective (cK) h)
  exact firstLabel_ne_secondLabel pairing b (wallStar.edge_injective h')

/-- **A singleton class above the anchor carries at most one surviving
occurrence**: its old occurrences lie outside the gauged branch classes, hence
dangle.  (This is the dangling of the `K + K'` extra new-edge singletons,
skeleton item B2, in the form needed here.) -/
theorem nd_le_one_of_not_mem
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry)
    (b : Bool) {s : Fin degree}
    (hs : (position.datum.vertexPartition ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 s)
    (hsA : s ∉ sideSheets m wd wallStar anchorBlock hAnchor pairing position b) :
    nonDanglingValency (cK).datum (epv (cK) b s) ≤ 1 := by
  classical
  have S := starHyp m wd wallStar anchorBlock hAnchor pairing position geometry hBg
  have hW : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
      ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 s := by
    have h := hs
    rw [position.datum_vertexPartition_wall] at h
    exact h
  have hSub : nonDanglingIncident (cK).datum (epv (cK) b s) ⊆ {(cK).newSourceEdge s} := by
    intro f hf
    rcases (mem_ndI_epv (cK) S.valid S.genus b s f).mp hf with
      ⟨o, hS, hAt, hSide, hRel, rfl⟩ | ⟨t, hRel, _, rfl⟩
    · exfalso
      have hEq : o.1.2 = s := endpoint_eq_of_not_mem m wd wallStar anchorBlock hAnchor pairing
        position b hW hsA
        ((endPart_anchor m wd wallStar anchorBlock hAnchor pairing position geometry b hs _).mp hRel)
      obtain ⟨l, hl⟩ := wallStar.exists_edge_eq o.1.1 hAt
      have hlb : W4TargetPairings.Pairing.labelRight pairing l = b := by
        rw [← wallStar.right_edge pairing l, hl]
        exact hSide
      set t := (position.gauge.perm l).symm s with ht
      have hst : position.gauge.perm l t = s := by rw [ht, Equiv.apply_symm_apply]
      have ho : o = position.datum.sourceEdge (wallStar.edge l) (position.gauge.perm l t) := by
        rw [hst, hl, ← hEq]
        exact (GluingDatum.sourceEdge_self _ o).symm
      have hWS : ¬IsDangling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdge (wallStar.edge l) t) :=
        fun h ↦ hS (ho ▸ (isDangling_gauged_iff wallStar position.gauge vConn vGen vVal l t).mpr h)
      have htW : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
          ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 t :=
        (SheetPartition.mem_block_iff _ _ _).mp
          ((position.gauge.preserving l).symm_mem ((SheetPartition.mem_block_iff _ _ _).mpr hW))
      have hMem := mem_branchBlock_of_survives m wd wallStar anchorBlock hAnchor l htW hWS
      apply hsA
      rw [← hlb, ← hst]
      exact sideSheets_labelRight m wd wallStar anchorBlock hAnchor pairing position l
        (Finset.mem_image_of_mem _ hMem)
    · have hEq : t = s := endpoint_eq_of_not_mem m wd wallStar anchorBlock hAnchor pairing
        position b hW hsA
        ((endPart_anchor m wd wallStar anchorBlock hAnchor pairing position geometry b hs _).mp hRel)
      rw [hEq]
      exact Finset.mem_singleton_self _
  have hCard := Finset.card_le_card hSub
  rwa [card_nonDanglingIncident, Finset.card_singleton] at hCard

theorem nd_ne_two_anchor
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry)
    (b : Bool) {s : Fin degree}
    (hs : (position.datum.vertexPartition ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 s) :
    nonDanglingValency (cK).datum (epv (cK) b s) ≠ 2 := by
  by_cases hsA : s ∈ sideSheets m wd wallStar anchorBlock hAnchor pairing position b
  · have := three_le_nd_side m wd wallStar anchorBlock hAnchor pairing position geometry b hs hsA
    omega
  · have := nd_le_one_of_not_mem m wd wallStar anchorBlock hAnchor pairing position geometry hBg
      b hs hsA
    omega

/-- **Every surviving new occurrence above the anchor is the bridge.** -/
theorem new_eq_bridge
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry)
    {s : Fin degree}
    (hs : (position.datum.vertexPartition ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 s)
    (hN : ¬IsDangling (cK).datum ((cK).newSourceEdge s)) :
    (cK).newSourceEdge s = (cK).newSourceEdge position.split.bridge := by
  by_cases hB : s ∈ position.split.bridgeSheets
  · refine (newSourceEdge_eq_iff (cK) s _).mpr ?_
    exact (newPart_anchor m wd wallStar anchorBlock hAnchor pairing position geometry hs _).mpr
      ((position.split.newEdge_rel_bridge_iff s).mpr hB).symm
  · exfalso
    have hNot : ∃ b : Bool, s ∉ sideSheets m wd wallStar anchorBlock hAnchor pairing position b := by
      by_cases hm : s ∈ position.split.minusSheets
      · refine ⟨!smallerSide vSrc pairing, ?_⟩
        unfold sideSheets
        rw [if_neg (by cases smallerSide vSrc pairing <;> simp)]
        exact fun hp ↦ hB (Finset.mem_inter.mpr ⟨hm, hp⟩)
      · refine ⟨smallerSide vSrc pairing, ?_⟩
        unfold sideSheets
        rw [if_pos rfl]
        exact hm
    obtain ⟨b, hsA⟩ := hNot
    have hle := nd_le_one_of_not_mem m wd wallStar anchorBlock hAnchor pairing position geometry
      hBg b hs hsA
    have hpos := ClassInjectivity.nonDanglingValency_ne_zero_of_incident _ hN
      (newSourceEdge_incident (cK) b s)
    have hne := NonDanglingValency.nonDanglingValency_ne_one (cK).datum
      ((cK).datum_valid (datum_valid' m wd wallStar anchorBlock hAnchor pairing position)).1
      (epv (cK) b s)
    omega

theorem nd_anchor_ne_two :
    nonDanglingValency position.datum (position.datum.sourceEndpoint ⟨wd.a, wd.hab⟩
      anchorBlock.1) ≠ 2 := by
  rw [nonDanglingValency_gauged_wall wallStar position.gauge vVal]
  have h : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint ⟨wd.a, wd.hab⟩
        anchorBlock.1) = 4 := hAnchor
  omega

/-- **The hypotheses at the anchor block, discharged at the general-`K`
candidate.** -/
theorem anchorHyp
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    AnchorHyp (cK) anchorBlock.1 position.split.bridge where
  bridge_rel := bridge_rel m wd wallStar anchorBlock hAnchor pairing position
  nd_ne_two := fun b _ hs ↦
    nd_ne_two_anchor m wd wallStar anchorBlock hAnchor pairing position geometry hBg b hs
  new_eq := fun _ hs hN ↦
    new_eq_bridge m wd wallStar anchorBlock hAnchor pairing position geometry hBg hs hN
  bridge_survives := bridge_survives m wd wallStar anchorBlock hAnchor pairing position geometry
  nd_anchor := nd_anchor_ne_two m wd wallStar anchorBlock hAnchor pairing position

/-! ## 4.  The row dictionary at the general-`K` candidate -/

/-- **The general-`K` row dictionary**: the stable rows of the candidate are the
stable rows of the gauged wall datum together with the bridge row. -/
noncomputable def rowEquivK
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    StablePath (cK).datum ≃ Option (StablePath position.datum) :=
  GeneralKRowEquiv.rowEquiv (starHyp m wd wallStar anchorBlock hAnchor pairing position geometry
    hBg) (anchorHyp m wd wallStar anchorBlock hAnchor pairing position geometry hBg)

/-- A retained row of the candidate. -/
noncomputable abbrev retainedRowK
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    StablePath position.datum → StablePath (cK).datum :=
  GeneralKRowEquiv.retainedRow (starHyp m wd wallStar anchorBlock hAnchor pairing position
    geometry hBg) (anchorHyp m wd wallStar anchorBlock hAnchor pairing position geometry hBg)

/-- The bridge row of the candidate. -/
noncomputable abbrev bridgeRowK
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    StablePath (cK).datum :=
  GeneralKRowEquiv.bridgeRow (anchorHyp m wd wallStar anchorBlock hAnchor pairing position
    geometry hBg)

@[simp] theorem rowEquivK_retainedRow
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry)
    (r : StablePath position.datum) :
    rowEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
      (retainedRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg r) = some r :=
  GeneralKRowEquiv.rowEquiv_retainedRow _ _ r

@[simp] theorem rowEquivK_bridgeRow
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    rowEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
      (bridgeRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg) = none :=
  GeneralKRowEquiv.rowEquiv_bridgeRow _ _

@[simp] theorem rowEquivK_symm_some
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry)
    (r : StablePath position.datum) :
    (rowEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).symm (some r) =
      retainedRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg r := rfl

@[simp] theorem rowEquivK_symm_none
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    (rowEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).symm none =
      bridgeRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg := rfl

/-- A retained row goes through the literal retained occurrences. -/
theorem retainedRowK_mk
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry)
    (o : NonDanglingEdge position.datum) :
    retainedRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg o.stablePath =
      NonDanglingEdge.stablePath (⟨(cK).oldSourceEdge o.1,
        ResolutionSurvival.not_isDangling_oldSourceEdge _
          (datum_valid' m wd wallStar anchorBlock hAnchor pairing position).1 _ o.2⟩ :
          NonDanglingEdge (cK).datum) := rfl

/-- The bridge row is the class of the new occurrence at the bridge sheet. -/
theorem bridgeRowK_eq
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    bridgeRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg =
      NonDanglingEdge.stablePath (⟨(cK).newSourceEdge position.split.bridge,
        bridge_survives m wd wallStar anchorBlock hAnchor pairing position geometry⟩ :
        NonDanglingEdge (cK).datum) := rfl

/-- A surviving retained occurrence of the candidate lies on the retained row of
its own wall row. -/
theorem rowEquivK_mk_old
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry)
    (o : position.datum.SourceEdge) (h : ¬IsDangling position.datum o)
    (h' : ¬IsDangling (cK).datum ((cK).oldSourceEdge o)) :
    rowEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
        (NonDanglingEdge.stablePath (⟨(cK).oldSourceEdge o, h'⟩ : NonDanglingEdge (cK).datum)) =
      some (NonDanglingEdge.stablePath (⟨o, h⟩ : NonDanglingEdge position.datum)) :=
  GeneralKRowEquiv.rowEquiv_mk_retE _ _ o h

/-- The bridge occurrence lies on the new row. -/
theorem rowEquivK_mk_bridge
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry)
    (h : ¬IsDangling (cK).datum ((cK).newSourceEdge position.split.bridge)) :
    rowEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
        (NonDanglingEdge.stablePath (⟨(cK).newSourceEdge position.split.bridge, h⟩ :
          NonDanglingEdge (cK).datum)) = none :=
  rowEquivK_bridgeRow m wd wallStar anchorBlock hAnchor pairing position geometry hBg

/-- The bridge row is a stable row of its own: its only occurrence is the bridge. -/
theorem eq_bridge_of_bridgeRowK
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry)
    (other : NonDanglingEdge (cK).datum)
    (h : other.stablePath = bridgeRowK m wd wallStar anchorBlock hAnchor pairing position geometry
      hBg) :
    other.1 = (cK).newSourceEdge position.split.bridge :=
  GeneralKRowEquiv.eq_bridge_of_stablePath_eq _ other h

/-- The gauge's stable-row equivalence from the wall datum. -/
noncomputable abbrev gaugeRow :
    StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne) ≃ StablePath position.datum :=
  (gaugeIso wallStar position.gauge).stablePathEquiv vVal.1

/-- **The row dictionary read against the wall datum itself**: the stable rows of
the general-`K` candidate are the stable rows of the incoming wall datum
(through the gauge) together with the bridge row. -/
noncomputable def rowEquivWall
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    StablePath (cK).datum ≃ Option (StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :=
  (rowEquivK m wd wallStar anchorBlock hAnchor pairing position geometry hBg).trans
    (Equiv.optionCongr (gaugeRow m wd wallStar anchorBlock hAnchor pairing position).symm)

@[simp] theorem rowEquivWall_retained
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry)
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    rowEquivWall m wd wallStar anchorBlock hAnchor pairing position geometry hBg
        (retainedRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
          (gaugeRow m wd wallStar anchorBlock hAnchor pairing position p)) = some p := by
  show Equiv.optionCongr _ (rowEquivK m wd wallStar anchorBlock hAnchor pairing position geometry
    hBg (retainedRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg
      (gaugeRow m wd wallStar anchorBlock hAnchor pairing position p))) = _
  rw [rowEquivK_retainedRow]
  show some ((gaugeRow m wd wallStar anchorBlock hAnchor pairing position).symm
    (gaugeRow m wd wallStar anchorBlock hAnchor pairing position p)) = _
  rw [Equiv.symm_apply_apply (gaugeRow m wd wallStar anchorBlock hAnchor pairing position) p]

@[simp] theorem rowEquivWall_bridge
    (hBg : GeneralKSourceFacts.LocalCanonicalBackground m wd wallStar anchorBlock hAnchor pairing
      position geometry) :
    rowEquivWall m wd wallStar anchorBlock hAnchor pairing position geometry hBg
        (bridgeRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg) = none := by
  show Equiv.optionCongr _ (rowEquivK m wd wallStar anchorBlock hAnchor pairing position geometry
    hBg (bridgeRowK m wd wallStar anchorBlock hAnchor pairing position geometry hBg)) = _
  rw [rowEquivK_bridgeRow]
  rfl

end Wall

end DraismaVargas.Count.GeneralKRowsK
