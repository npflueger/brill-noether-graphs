import DraismaVargas.LocalCases.NonTrivalentValencyFourRowDictionary

/-!
# The row equivalence of the `K = 0` candidate at a four-valent wall

Source: Vargas, Part II (arXiv:2609.09109), §5.1: the lemma on rigidity above
`w_0` (`lemma-above-w0`) and `lm:change-comb-type` (the wall matrix as the
common minor `A_{\varphi_0}`).

`NonTrivalentValencyFourRowDictionary` proves `ordinaryBlockDescent` and the
unconditional `retainedRow`, and states every labelling theorem with the row
equivalence `rowEquiv` and its compatibility `hRowRetained` as explicit
arguments.  This module constructs both, under the single hypothesis
`Function.Injective retainedRow`, which
`NonTrivalentValencyFourRetainedInjective` discharges.

## What is proved

* **The gauge transport of the census (Section 1).**  `activeLabels_gaugedBlock`,
  `gauged_sourceVertex_eq_block`, `nonDanglingValency_gaugedBlock` and
  `nonDanglingStarInjective_gaugedBlock` are
  `NonTrivalentValencyFourRows.activeLabels_gauged`, `gauged_sourceVertex_eq`
  and the injectivity step of `gaugedSource` with the anchor block replaced by
  an arbitrary wall block.  The block-preserving sheet gauge permutes sheets
  only inside wall blocks, so it changes neither the active label set, nor the
  wall-block source vertex, nor the surviving valency, at *any* block.

* **The occurrence census of a wall block (Section 2).**  `eq_of_same_target`
  is target-direction injectivity in occurrence form, and `eq_of_three_on_side`
  is the counting fact everything below turns on: a `2 + 2` target pairing has
  exactly two labels per side
  (`W4TargetPairings.Pairing.card_labelsOnSide`), so **at most two surviving
  occurrences of one wall block are assigned to one side**.

* **`newSourceEdge_absorbed` (Section 3).**  *Every surviving new occurrence
  over a non-anchor wall block lies on the stable row of a retained survivor of
  that block.*  The proof is a trichotomy on the number of surviving
  occurrences of the block in the fine class of the sheet:
  - none: `newSourceEdge_dangling_of_no_fine_survivor` contradicts survival;
  - exactly one: `stablePath_newSourceEdge_eq` absorbs the new occurrence into
    that survivor's row;
  - two or more: then every fine-side survivor of the block already lies in
    that class (`eq_of_three_on_side`), so all surviving new occurrences at the
    retaining endpoint coincide with this one, and the block carries at most
    one retaining-side survivor -- four survivors would give the block
    surviving valency four.  With no retaining survivor the retaining endpoint
    would be a singleton, so the new occurrence is dangling
    (`isDangling_of_subset_singleton`), contradiction; with one it is divalent
    and absorbs the new occurrence into *that* survivor's row.

  The third case is exactly the degeneracy `NonTrivalentValencyFourRowEquiv`'s
  `retSide` cannot see: on a singleton wall block `splitBlock` is the coarse
  partition, and both endpoints of the block resolution retain it.  No side
  condition on `blockCard` is needed: the counting argument covers it.

* **The row map and its surjectivity (Section 4).**  `rowMap` is
  `retained ⊔ bridge`; `rowMap_surjective` is `stablePath_cases` together with
  `newSourceEdge_anchor_eq_bridge` at the anchor and `newSourceEdge_absorbed`
  elsewhere, and `rowMap_injective` is `retainedRow_ne_bridgeRow` together with
  injectivity of `retainedRow`.  `rowEquiv` is the resulting equivalence,
  `rowEquiv_retainedRow` its compatibility and `rowEquiv_bridgeRow` the extra
  row.

* **The census at an actual wall (Section 5).**
  `ordinaryBlockProfile_of_single_row_active` exposes the census's active
  finset as the literal `W4StableSource.activeLabels` of the wall datum, and
  `wall_starInjective` exposes `NonTrivalentValencyFourAnchor.targetInjective`
  at *every* wall block; `gauged_starInjective_of_single_row` and
  `gauged_valency_of_single_row` transport both to the gauged datum, so the two
  hypotheses of Section 3 hold with no receipt beyond those of
  `NonTrivalentValencyFourAnchor.fourBranchAnchor_of_single_zero_row`.

* **The instantiated corollaries (Section 6).**  `rowEquiv_of_single_row`,
  `chartLabelling_of_single_row` and `matrix_chartLabelling_eq_incoming_of_single_row`
  are `NonTrivalentValencyFourRowDictionary`'s statements at an actual
  four-valent wall, with `NoContractedReturn` discharged by
  `StablePathFacetContraction.noContractedReturn_of_fourStar`.

## What is not proved here

`Function.Injective (NonTrivalentValencyFourRowDictionary.retainedRow …)` --
that two distinct stable rows of the gauged wall datum stay distinct in the
candidate.  It is carried as an explicit hypothesis `hRetInj` by
`rowMap_injective`, `rowEquiv` and every Section 6 corollary, and it is
discharged in `NonTrivalentValencyFourRetainedInjective`; **nothing else about
the candidate is assumed**, and in particular no arbitrary `rowEquiv` with a
compatibility `hRowRetained` is taken as input.

`newSourceEdge_absorbed` alone does **not** give it: it produces *some*
absorbing survivor, and identifying two absorbing survivors of one new
occurrence through `retainedRow` is the very statement being proved.  The
injectivity proof is therefore an inverse `Quot.lift` -- a map
`rowOfEdge : NonDanglingEdge C.datum → Option (StablePath G)` constant on
consecutive pairs, sending a retained occurrence to its wall row and the bridge
to `none`; `Quot.lift rowOfEdge` is then a literal left inverse of `retainedRow`
(`Option.some` is injective).  Constancy is a surviving-star census at every
vertex of the candidate, and the vertices are enumerated exactly as in
`LimitChainCore.rowOfEdge_eq_of_consecutive`: `cases vertex.1.1` splits into
`oldVertex place`, `oldVertex wall` and `freshVertex`, and
`ResolutionAwayFromWall.exists_retainedVertex_of_target` turns the first into a
retained vertex while the other two are `endpointVertex false/true vertex.1.2`.
Then:

1. off the wall, `ResolutionAwayFromWall.nonDanglingIncident_retainedVertex`
   and `not_incident_newSourceEdge` make both partners retained and the
   valencies agree (`nonDanglingValency_retainedVertex`);
2. at an anchor endpoint there are no consecutive pairs at all, so the case is
   vacuous: on the non-smaller side `endpointForSide_not_smaller` makes
   `endpointForSide` the coarse partition, so `endpointVertex_eq` moves the
   sheet to `selectedRepresentative`, where
   `nonDanglingValency_endpointVertex` is three; on the smaller side either the
   sheet is `finePartition`-related to it and the same applies, or
   `NonTrivalentValencyFourKZero.finePartition_rel_or_singleton` makes its fine
   block a singleton and `nonDanglingIncident_singleton_subset` bounds the
   surviving star by one occurrence;
3. at a non-anchor block, `nonDanglingIncident_ret_dichotomy` and
   `nonDanglingIncident_fine_cases` list the survivors at the two endpoints,
   and the counting of Section 2 decides each pair.  The one case needing the
   count is *two retained survivors at a fine endpoint*: `eq_of_three_on_side`
   makes them the only fine-side survivors of the block, a retaining-side
   survivor would leave the retaining endpoint with surviving valency one
   (every other new occurrence of the block is dangling by
   `newSourceEdge_dangling_of_no_fine_survivor`), so the block has surviving
   valency two and the two are already consecutive in the wall datum.  The same
   count settles the other pairs, including the one case where a new occurrence
   has *both* endpoints divalent: its two retained partners are then the only
   two survivors of the block, so they carry one wall row.

## Consumers

The boundary dispatcher for Part II case `{v4-nd4}`
(`NonTrivalentValencyFourDispatcher`) and the nonsingularity/exit package built
on `NonTrivalentLinkMatrix`, whose `AgreeOffColumn` input is
`matrix_chartLabelling_eq_incoming_of_single_row`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyFourRowEquivFinal

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.LocalCases.NonTrivalentValencyFourBackground
open DraismaVargas.LocalCases.NonTrivalentValencyFourRows
open DraismaVargas.LocalCases.NonTrivalentValencyFourDictionary
open DraismaVargas.LocalCases.NonTrivalentValencyFourRowEquiv
open DraismaVargas.LocalCases.NonTrivalentValencyFourDescent
open DraismaVargas.LocalCases.NonTrivalentValencyFourRowDictionary

/-! ## 1.  The census across the block-preserving sheet gauge -/

section Gauge

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall} {anchor : WallBlock data wall}
  (source : FourBranchAnchor data star anchor) (pairing : Fin 3)
  (hNoGlue : DanglingEdgeNoGlue data)
  (hRamification : data.localRamification wall anchor = 0)

/-- The gauged copy of a wall block.  The gauge does not move wall blocks, so
this is the same sheet representative read in the gauged datum. -/
noncomputable def gaugedBlock (block : WallBlock data wall) :
    WallBlock (gaugedData source pairing hNoGlue hRamification) wall :=
  ⟨block.1, by
    rw [gaugedData_vertexPartition_wall source pairing hNoGlue hRamification]
    exact block.2⟩

@[simp] theorem gaugedBlock_ofSheet (sheet : Fin degree) :
    gaugedBlock source pairing hNoGlue hRamification
        (WallBlock.ofSheet data wall sheet) =
      WallBlock.ofSheet (gaugedData source pairing hNoGlue hRamification) wall
        sheet := by
  apply Subtype.ext
  show (data.vertexPartition wall).repr sheet =
    ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).repr
      sheet
  rw [gaugedData_vertexPartition_wall source pairing hNoGlue hRamification]

/-- **The gauge changes no active target branch at any wall block.**  This is
`NonTrivalentValencyFourRows.activeLabels_gauged` with the anchor block
replaced by an arbitrary one; the proof never used the anchor. -/
theorem activeLabels_gaugedBlock (hDataValid : data.Valid)
    (block : WallBlock data wall) :
    activeLabels (gaugedData source pairing hNoGlue hRamification) star
        (gaugedBlock source pairing hNoGlue hRamification block) =
      activeLabels data star block := by
  classical
  ext label
  rw [mem_activeLabels_iff, mem_activeLabels_iff]
  set π := (relabeling source pairing hNoGlue hRamification).edgePermutation
    (star.edge label) with hπ
  constructor
  · rintro ⟨sheet, hRel, hSurv⟩
    have hRel' : (data.vertexPartition wall).Rel block.1 sheet :=
      (gauged_rel_iff source pairing hNoGlue hRamification block.1 sheet).mp hRel
    refine ⟨π.symm sheet, ?_, ?_⟩
    · refine hRel'.trans ?_
      have := gauge_edgePermutation_rel source pairing hNoGlue hRamification
        (star.edge label) (π.symm sheet)
      rw [← hπ, Equiv.apply_symm_apply] at this
      exact this
    · intro hDangling
      apply hSurv
      have := (gauged_isDangling_iff source pairing hNoGlue hRamification
        hDataValid (star.edge label) (π.symm sheet)).mpr hDangling
      rwa [← hπ, Equiv.apply_symm_apply] at this
  · rintro ⟨sheet, hRel, hSurv⟩
    refine ⟨π sheet, ?_, ?_⟩
    · refine (gauged_rel_iff source pairing hNoGlue hRamification block.1
        (π sheet)).mpr ?_
      exact hRel.trans (gauge_edgePermutation_rel source pairing hNoGlue
        hRamification (star.edge label) sheet).symm
    · intro hDangling
      exact hSurv ((gauged_isDangling_iff source pairing hNoGlue hRamification
        hDataValid (star.edge label) sheet).mp hDangling)

/-- The gauge is the identity on wall-block source vertices. -/
theorem gauged_sourceVertex_eq_block (block : WallBlock data wall) :
    (relabeling source pairing hNoGlue hRamification).sourceVertexEquiv
        (WallBlock.sourceVertex data wall block) =
      WallBlock.sourceVertex (gaugedData source pairing hNoGlue hRamification)
        wall (gaugedBlock source pairing hNoGlue hRamification block) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · show (relabeling source pairing hNoGlue hRamification).vertexPermutation wall
        ((data.vertexPartition wall).repr block.1) =
      ((gaugedData source pairing hNoGlue hRamification).vertexPartition
        wall).repr block.1
    rw [gauge_vertexPermutation_wall source pairing hNoGlue hRamification,
      gaugedData_vertexPartition_wall source pairing hNoGlue hRamification]
    rfl

/-- The surviving valency of a wall block is unchanged by the gauge. -/
theorem nonDanglingValency_gaugedBlock (hDataValid : data.Valid)
    (block : WallBlock data wall) :
    nonDanglingValency (gaugedData source pairing hNoGlue hRamification)
        (WallBlock.sourceVertex (gaugedData source pairing hNoGlue hRamification)
          wall (gaugedBlock source pairing hNoGlue hRamification block)) =
      nonDanglingValency data (WallBlock.sourceVertex data wall block) := by
  rw [← gauged_sourceVertex_eq_block source pairing hNoGlue hRamification block]
  exact SheetRelabelStable.nonDanglingValency_map
    (relabeling source pairing hNoGlue hRamification) hDataValid.1
    (WallBlock.sourceVertex data wall block)

/-- **Target-direction injectivity survives the block-preserving gauge**, at
every wall block. -/
theorem nonDanglingStarInjective_gaugedBlock (hDataValid : data.Valid)
    (block : WallBlock data wall)
    (hInjective : NonDanglingStarInjective data star block) :
    NonDanglingStarInjective (gaugedData source pairing hNoGlue hRamification)
      star (gaugedBlock source pairing hNoGlue hRamification block) := by
  apply nonDanglingStarInjective_of_card_activeLabels_eq_nonDanglingValency
  rw [activeLabels_gaugedBlock source pairing hNoGlue hRamification hDataValid
      block,
    nonDanglingValency_gaugedBlock source pairing hNoGlue hRamification
      hDataValid block]
  exact card_activeLabels_eq_nonDanglingValency data star block hInjective

end Gauge

/-! ## 2.  The occurrence census of one wall block -/

section Block

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall} {anchor : WallBlock data wall}
  (source : FourBranchAnchor data star anchor) (pairing : Fin 3)
  (hNoGlue : DanglingEdgeNoGlue data)
  (hRamification : data.localRamification wall anchor = 0)
  (profile : OrdinaryBlockProfile data star anchor.1)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (hValid : data.Valid)

local notation "cand" =>
  (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
    hRamification profile hConnected hGenus hValid)
local notation "gauged" => (gaugedData source pairing hNoGlue hRamification)
local notation "coarse" =>
  (GluingDatum.vertexPartition
    (gaugedData source pairing hNoGlue hRamification) wall)
local notation "blockRes" =>
  (W4Assembly.blockwiseResolution
    (gaugedData source pairing hNoGlue hRamification) star profile.pattern
    pairing)

/-- A surviving occurrence at a wall block belongs to the block's surviving
star. -/
theorem mem_nonDanglingIncident_block {y : Fin degree}
    {w : (gauged).SourceEdge} (hSurv : ¬ IsDangling (gauged) w)
    (hAt : w.1.1 ∈ GluingDatum.incidentEdges wall)
    (hRel : (coarse).Rel y w.1.2) :
    w ∈ nonDanglingIncident (gauged)
      (WallBlock.sourceVertex (gauged) wall
        (WallBlock.ofSheet (gauged) wall y)) := by
  refine (mem_nonDanglingIncident _ _ _).mpr ⟨hSurv, ?_⟩
  refine (incident_wallBlock_sourceVertex_iff (gauged) _ w).mpr ⟨hAt, ?_⟩
  exact (WallBlock.ofSheet_eq_iff_rel (gauged) wall _ w.1.2).mpr
    (((coarse).rel_repr_left y).trans hRel)

/-- Two surviving occurrences of one wall block over the same target occurrence
coincide, by target-direction injectivity. -/
theorem eq_of_same_target {y : Fin degree}
    (hInjY : NonDanglingStarInjective (gauged) star
      (WallBlock.ofSheet (gauged) wall y))
    {o₁ o₂ : (gauged).SourceEdge} (h₁ : ¬ IsDangling (gauged) o₁)
    (h₂ : ¬ IsDangling (gauged) o₂)
    (hAt₁ : o₁.1.1 ∈ GluingDatum.incidentEdges wall)
    (hRel₁ : (coarse).Rel y o₁.1.2) (hRel₂ : (coarse).Rel y o₂.1.2)
    (hTarget : o₁.1.1 = o₂.1.1) : o₁ = o₂ := by
  obtain ⟨label, hLabel⟩ := star.exists_edge_eq o₁.1.1 hAt₁
  exact hInjY.unique label o₁ o₂
    ((WallBlock.ofSheet_eq_iff_rel (gauged) wall _ o₁.1.2).mpr
      (((coarse).rel_repr_left y).trans hRel₁))
    ((WallBlock.ofSheet_eq_iff_rel (gauged) wall _ o₂.1.2).mpr
      (((coarse).rel_repr_left y).trans hRel₂))
    hLabel.symm (hTarget.symm.trans hLabel.symm) h₁ h₂

/-- **At most two surviving occurrences of a wall block are assigned to one
side of the prescribed pairing.**  A `2 + 2` target pairing has two labels per
side, and target-direction injectivity makes distinct survivors of one block
carry distinct labels. -/
theorem eq_of_three_on_side {y : Fin degree} {sideValue : Bool}
    (hInjY : NonDanglingStarInjective (gauged) star
      (WallBlock.ofSheet (gauged) wall y))
    (o₁ o₂ o₃ : (gauged).SourceEdge)
    (h₁ : ¬ IsDangling (gauged) o₁) (h₂ : ¬ IsDangling (gauged) o₂)
    (h₃ : ¬ IsDangling (gauged) o₃)
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
  · exact Or.inl (eq_of_same_target source pairing hNoGlue hRamification hInjY
      h₁ h₂ hAt₁ hRel₁ hRel₂ (by rw [← hl₁, ← hl₂, h₁₂]))
  by_cases h₁₃ : l₁ = l₃
  · exact Or.inr (Or.inl (eq_of_same_target source pairing hNoGlue hRamification
      hInjY h₁ h₃ hAt₁ hRel₁ hRel₃ (by rw [← hl₁, ← hl₃, h₁₃])))
  by_cases h₂₃ : l₂ = l₃
  · exact Or.inr (Or.inr (eq_of_same_target source pairing hNoGlue hRamification
      hInjY h₂ h₃ hAt₂ hRel₂ hRel₃ (by rw [← hl₂, ← hl₃, h₂₃])))
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

/-! ## 3.  Every surviving new occurrence of a non-anchor block is absorbed -/

/-- **Every surviving new occurrence over a non-anchor wall block lies on the
stable row of a retained survivor of that block.**  This is the uniqueness
statement the two counting engines of `NonTrivalentValencyFourRowEquiv` need,
with the degenerate blocks -- where `retSide` cannot distinguish the two
endpoints because both retain the wall partition -- handled by the surviving
valency bound rather than by a `blockCard` side condition. -/
theorem newSourceEdge_absorbed
    (hInj : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      NonDanglingStarInjective (gauged) star (WallBlock.ofSheet (gauged) wall y))
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3)
    {x : Fin degree} (hb : ¬ (coarse).Rel anchor.1 x)
    (hSurv : ¬ IsDangling (cand).datum ((cand).newSourceEdge x)) :
    ∃ (old : (gauged).SourceEdge) (hOld : ¬ IsDangling (gauged) old),
      NonDanglingEdge.stablePath
          (⟨(cand).newSourceEdge x, hSurv⟩ : NonDanglingEdge (cand).datum) =
        NonTrivalentValencyFourRowDictionary.retainedRow source pairing hNoGlue
          hRamification profile hConnected hGenus hValid
          (NonDanglingEdge.stablePath
            (⟨old, hOld⟩ : NonDanglingEdge (gauged))) := by
  classical
  by_cases hNone : ∀ old : (gauged).SourceEdge, ¬ IsDangling (gauged) old →
      old.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing old.1.1 =
        !retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x) →
      ¬ (blockRes ((coarse).repr x)).newEdge.Rel x old.1.2
  · exact absurd (newSourceEdge_dangling_of_no_fine_survivor source pairing
      hNoGlue hRamification profile hConnected hGenus hValid hb hNone) hSurv
  push Not at hNone
  obtain ⟨old, hOldSurv, hOldAt, hOldSide, hOldRel⟩ := hNone
  by_cases hUniq : ∀ other : (gauged).SourceEdge, ¬ IsDangling (gauged) other →
      other.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing other.1.1 =
        !retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x) →
      (blockRes ((coarse).repr x)).newEdge.Rel x other.1.2 → other = old
  · refine ⟨old, hOldSurv, ?_⟩
    rw [retainedRow_mk source pairing hNoGlue hRamification profile hConnected
      hGenus hValid ⟨old, hOldSurv⟩]
    exact stablePath_newSourceEdge_eq source pairing hNoGlue hRamification
      profile hConnected hGenus hValid hb hOldSurv hOldAt hOldSide hOldRel hUniq
  push Not at hUniq
  obtain ⟨other, hOtherSurv, hOtherAt, hOtherSide, hOtherRel, hOtherNe⟩ := hUniq
  have hOldCoarse : (coarse).Rel x old.1.2 :=
    (blockRes_newEdge_refines source pairing hNoGlue hRamification profile
      ((coarse).repr x)).rel hOldRel
  have hOtherCoarse : (coarse).Rel x other.1.2 :=
    (blockRes_newEdge_refines source pairing hNoGlue hRamification profile
      ((coarse).repr x)).rel hOtherRel
  have hSideNe : ∀ u v : (gauged).SourceEdge,
      star.right pairing u.1.1 =
        (!retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x)) →
      star.right pairing v.1.1 =
        retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x) →
      u ≠ v := by
    intro u v hu hv hEq
    rw [hEq, hv] at hu
    exact absurd hu (by simp)
  have hFineBlock : ∀ z : (gauged).SourceEdge, ¬ IsDangling (gauged) z →
      z.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing z.1.1 =
        (!retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x)) →
      (coarse).Rel x z.1.2 →
      (blockRes ((coarse).repr x)).newEdge.Rel x z.1.2 := by
    intro z hzS hzAt hzSide hzRel
    rcases eq_of_three_on_side source pairing hNoGlue hRamification (hInj x hb)
      old other z hOldSurv hOtherSurv hzS hOldAt hOtherAt hzAt hOldCoarse
      hOtherCoarse hzRel hOldSide hOtherSide hzSide with h | h | h
    · exact absurd h.symm hOtherNe
    · exact h ▸ hOldRel
    · exact h ▸ hOtherRel
  have hNewEq : ∀ z : (gauged).SourceEdge, ¬ IsDangling (gauged) z →
      z.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing z.1.1 =
        (!retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x)) →
      (coarse).Rel x z.1.2 →
      (cand).newSourceEdge z.1.2 = (cand).newSourceEdge x := by
    intro z hzS hzAt hzSide hzRel
    refine (newSourceEdge_eq_of_rel source pairing hNoGlue hRamification profile
      hConnected hGenus hValid ?_).symm
    rw [candidate_newEdge_rel_block source pairing hNoGlue hRamification profile
      hConnected hGenus hValid hb z.1.2]
    exact hFineBlock z hzS hzAt hzSide hzRel
  have hIncNew : Incident (cand).datum ((cand).newSourceEdge x)
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x)) x) :=
    bridgeEdge_incident source pairing hNoGlue hRamification profile hConnected
      hGenus hValid _ x
  by_cases hRet : ∃ r : (gauged).SourceEdge, ¬ IsDangling (gauged) r ∧
      r.1.1 ∈ GluingDatum.incidentEdges wall ∧
      star.right pairing r.1.1 =
        retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x) ∧
      (coarse).Rel x r.1.2
  · obtain ⟨r, hrS, hrAt, hrSide, hrRel⟩ := hRet
    have hRetUniq : ∀ z : (gauged).SourceEdge, ¬ IsDangling (gauged) z →
        z.1.1 ∈ GluingDatum.incidentEdges wall →
        star.right pairing z.1.1 =
          retSide source pairing hNoGlue hRamification profile
            ((coarse).repr x) →
        (coarse).Rel x z.1.2 → z = r := by
      intro z hzS hzAt hzSide hzRel
      by_contra hzr
      have hSub4 : ({old, other, r, z} : Finset (gauged).SourceEdge) ⊆
          nonDanglingIncident (gauged)
            (WallBlock.sourceVertex (gauged) wall
              (WallBlock.ofSheet (gauged) wall x)) := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact mem_nonDanglingIncident_block source pairing hNoGlue
            hRamification hOldSurv hOldAt hOldCoarse
        · exact mem_nonDanglingIncident_block source pairing hNoGlue
            hRamification hOtherSurv hOtherAt hOtherCoarse
        · exact mem_nonDanglingIncident_block source pairing hNoGlue
            hRamification hrS hrAt hrRel
        · exact mem_nonDanglingIncident_block source pairing hNoGlue
            hRamification hzS hzAt hzRel
      have h₁ : old ≠ other := fun h ↦ hOtherNe h.symm
      have h₂ : old ≠ r := hSideNe old r hOldSide hrSide
      have h₃ : old ≠ z := hSideNe old z hOldSide hzSide
      have h₄ : other ≠ r := hSideNe other r hOtherSide hrSide
      have h₅ : other ≠ z := hSideNe other z hOtherSide hzSide
      have h₆ : r ≠ z := fun h ↦ hzr h.symm
      have hCard4 : ({old, other, r, z} :
          Finset (gauged).SourceEdge).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [h₁, h₂, h₃]),
          Finset.card_insert_of_notMem (by simp [h₄, h₅]),
          Finset.card_insert_of_notMem (by simp [h₆]), Finset.card_singleton]
      have hLe := Finset.card_le_card hSub4
      rw [hCard4, card_nonDanglingIncident] at hLe
      have hThree := hValency x hb
      omega
    have hSubset : nonDanglingIncident (cand).datum
        (endpointVertex source pairing hNoGlue hRamification profile hConnected
          hGenus hValid
          (retSide source pairing hNoGlue hRamification profile
            ((coarse).repr x)) x) ⊆
        {(cand).oldSourceEdge r, (cand).newSourceEdge x} := by
      intro f hf
      obtain ⟨hfS, hfI⟩ := (mem_nonDanglingIncident _ _ _).mp hf
      rcases nonDanglingIncident_ret_dichotomy source pairing hNoGlue
        hRamification profile hConnected hGenus hValid hb hfS hfI with
        ⟨z, hzS, hzAt, hzSide, hzRel, rfl⟩ | ⟨z, hzS, hzAt, hzSide, hzRel, rfl⟩
      · rw [hRetUniq z hzS hzAt hzSide hzRel]
        exact Finset.mem_insert_self _ _
      · rw [hNewEq z hzS hzAt hzSide hzRel]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hIncOldR : Incident (cand).datum ((cand).oldSourceEdge r)
        (endpointVertex source pairing hNoGlue hRamification profile hConnected
          hGenus hValid
          (retSide source pairing hNoGlue hRamification profile
            ((coarse).repr x)) x) := by
      have h := retainedEdge_incident source pairing hNoGlue hRamification
        profile hConnected hGenus hValid r.1.1 hrAt _ hrSide r.1.2
      rw [GluingDatum.sourceEdge_self,
        endpointVertex_ret_eq source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hb hrRel] at h
      exact h
    have hSurvOldR : ¬ IsDangling (cand).datum ((cand).oldSourceEdge r) :=
      ResolutionSurvival.not_isDangling_oldSourceEdge _
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1 _ hrS
    have hNeOldNew : (cand).oldSourceEdge r ≠ (cand).newSourceEdge x :=
      new_ne_old source pairing hNoGlue hRamification profile hConnected hGenus
        hValid x r
    have hVal2 := nonDanglingValency_eq_two_of_pair source pairing hNoGlue
      hRamification profile hConnected hGenus hValid hNeOldNew hSubset
      ((mem_nonDanglingIncident _ _ _).mpr ⟨hSurvOldR, hIncOldR⟩)
      ((mem_nonDanglingIncident _ _ _).mpr ⟨hSurv, hIncNew⟩)
    refine ⟨r, hrS, ?_⟩
    rw [retainedRow_mk source pairing hNoGlue hRamification profile hConnected
      hGenus hValid ⟨r, hrS⟩]
    exact stablePath_eq_of_consecutive
      ⟨fun h ↦ hNeOldNew (congrArg Subtype.val h).symm, _, hIncNew, hIncOldR,
        hVal2⟩
  · exfalso
    refine hSurv (isDangling_of_subset_singleton source pairing hNoGlue
      hRamification profile hConnected hGenus hValid ?_ hIncNew)
    intro f hf
    obtain ⟨hfS, hfI⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    rcases nonDanglingIncident_ret_dichotomy source pairing hNoGlue
      hRamification profile hConnected hGenus hValid hb hfS hfI with
      ⟨z, hzS, hzAt, hzSide, hzRel, rfl⟩ | ⟨z, hzS, hzAt, hzSide, hzRel, rfl⟩
    · exact absurd ⟨z, hzS, hzAt, hzSide, hzRel⟩ hRet
    · rw [hNewEq z hzS hzAt hzSide hzRel]
      exact Finset.mem_singleton_self _

/-! ## 4.  The row map, its bijectivity and the row equivalence -/

/-- The bridge occurrence of the `K = 0` candidate, as a surviving
occurrence. -/
noncomputable def bridge : NonDanglingEdge (cand).datum :=
  ⟨bridgeEdge source pairing hNoGlue hRamification profile hConnected hGenus
      hValid (selectedRepresentative source pairing),
    bridgeEdge_survives source pairing hNoGlue hRamification profile hConnected
      hGenus hValid⟩

/-- The bridge row of the `K = 0` candidate: the extra stable row created by
the wall crossing. -/
noncomputable def bridgeRow : StablePath (cand).datum :=
  NonDanglingEdge.stablePath
    (bridge source pairing hNoGlue hRamification profile hConnected hGenus
      hValid)

/-- **The row map `retained ⊔ bridge`.** -/
noncomputable def rowMap :
    Option (StablePath (gauged)) → StablePath (cand).datum
  | none =>
      bridgeRow source pairing hNoGlue hRamification profile hConnected hGenus
        hValid
  | some r =>
      NonTrivalentValencyFourRowDictionary.retainedRow source pairing hNoGlue
        hRamification profile hConnected hGenus hValid r

@[simp] theorem rowMap_none :
    rowMap source pairing hNoGlue hRamification profile hConnected hGenus hValid
        none =
      bridgeRow source pairing hNoGlue hRamification profile hConnected hGenus
        hValid := rfl

@[simp] theorem rowMap_some (r : StablePath (gauged)) :
    rowMap source pairing hNoGlue hRamification profile hConnected hGenus hValid
        (some r) =
      NonTrivalentValencyFourRowDictionary.retainedRow source pairing hNoGlue
        hRamification profile hConnected hGenus hValid r := rfl

/-- **The row map is surjective.**  `stablePath_cases` reduces a stable row of
the candidate to a retained row or a surviving new occurrence;
`newSourceEdge_anchor_eq_bridge` identifies the anchor ones with the bridge and
`newSourceEdge_absorbed` absorbs the rest. -/
theorem rowMap_surjective
    (hInj : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      NonDanglingStarInjective (gauged) star (WallBlock.ofSheet (gauged) wall y))
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3) :
    Function.Surjective (rowMap source pairing hNoGlue hRamification profile
      hConnected hGenus hValid) := by
  intro row
  rcases stablePath_cases source pairing hNoGlue hRamification profile
    hConnected hGenus hValid row with ⟨r, rfl⟩ | ⟨s, hs, rfl⟩
  · exact ⟨some r, rfl⟩
  · by_cases hAnchorRel : (coarse).Rel anchor.1 s
    · exact ⟨none, congrArg NonDanglingEdge.stablePath (Subtype.ext
        (newSourceEdge_anchor_eq_bridge source pairing hNoGlue hRamification
          profile hConnected hGenus hValid hAnchorRel hs).symm)⟩
    · obtain ⟨old, hOld, hEq⟩ := newSourceEdge_absorbed source pairing hNoGlue
        hRamification profile hConnected hGenus hValid hInj hValency hAnchorRel
        hs
      exact ⟨some (NonDanglingEdge.stablePath ⟨old, hOld⟩), hEq.symm⟩

/-- **The row map is injective** as soon as the retained-row map is: the bridge
row is not a retained row (`retainedRow_ne_bridgeRow`). -/
theorem rowMap_injective
    (hRetInj : Function.Injective
      (NonTrivalentValencyFourRowDictionary.retainedRow source pairing hNoGlue
        hRamification profile hConnected hGenus hValid)) :
    Function.Injective (rowMap source pairing hNoGlue hRamification profile
      hConnected hGenus hValid) := by
  intro o₁ o₂ hEq
  cases o₁ with
  | none =>
      cases o₂ with
      | none => rfl
      | some r₂ =>
          exact absurd (hEq.symm : rowMap source pairing hNoGlue hRamification
            profile hConnected hGenus hValid (some r₂) = _)
            (retainedRow_ne_bridgeRow source pairing hNoGlue hRamification
              profile hConnected hGenus hValid r₂)
  | some r₁ =>
      cases o₂ with
      | none =>
          exact absurd (hEq : rowMap source pairing hNoGlue hRamification profile
            hConnected hGenus hValid (some r₁) = _)
            (retainedRow_ne_bridgeRow source pairing hNoGlue hRamification
              profile hConnected hGenus hValid r₁)
      | some r₂ => exact congrArg some (hRetInj hEq)

/-- **The row equivalence of the `K = 0` candidate.**  The only hypothesis
about the candidate is injectivity of the retained-row map. -/
noncomputable def rowEquiv
    (hInj : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      NonDanglingStarInjective (gauged) star (WallBlock.ofSheet (gauged) wall y))
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3)
    (hRetInj : Function.Injective
      (NonTrivalentValencyFourRowDictionary.retainedRow source pairing hNoGlue
        hRamification profile hConnected hGenus hValid)) :
    StablePath (cand).datum ≃ Option (StablePath (gauged)) :=
  (Equiv.ofBijective
    (rowMap source pairing hNoGlue hRamification profile hConnected hGenus
      hValid)
    ⟨rowMap_injective source pairing hNoGlue hRamification profile hConnected
        hGenus hValid hRetInj,
      rowMap_surjective source pairing hNoGlue hRamification profile hConnected
        hGenus hValid hInj hValency⟩).symm

/-- **The compatibility `hRowRetained`**: the row equivalence sends each
retained row to its wall row. -/
theorem rowEquiv_retainedRow
    (hInj : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      NonDanglingStarInjective (gauged) star (WallBlock.ofSheet (gauged) wall y))
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3)
    (hRetInj : Function.Injective
      (NonTrivalentValencyFourRowDictionary.retainedRow source pairing hNoGlue
        hRamification profile hConnected hGenus hValid))
    (r : StablePath (gauged)) :
    rowEquiv source pairing hNoGlue hRamification profile hConnected hGenus
        hValid hInj hValency hRetInj
        (NonTrivalentValencyFourRowDictionary.retainedRow source pairing hNoGlue
          hRamification profile hConnected hGenus hValid r) =
      some r :=
  Equiv.symm_apply_eq _ |>.mpr rfl

/-- **The extra row.**  The bridge is the row that the wall crossing creates;
it is the one the equivalence sends to `Option.none`. -/
theorem rowEquiv_bridgeRow
    (hInj : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      NonDanglingStarInjective (gauged) star (WallBlock.ofSheet (gauged) wall y))
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3)
    (hRetInj : Function.Injective
      (NonTrivalentValencyFourRowDictionary.retainedRow source pairing hNoGlue
        hRamification profile hConnected hGenus hValid)) :
    rowEquiv source pairing hNoGlue hRamification profile hConnected hGenus
        hValid hInj hValency hRetInj
        (bridgeRow source pairing hNoGlue hRamification profile hConnected
          hGenus hValid) =
      none :=
  Equiv.symm_apply_eq _ |>.mpr rfl

end Block


/-! ## 5.  The census at an actual four-valent wall -/

section ActualWall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.StablePathFacetContraction

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (cover : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation cover coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (wallStar : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)
  (hForest : ContractionForest cover a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (anchorBlock : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩)
  (hAnchor : nonDanglingValency (contractDatum cover hc hab hOne)
    (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩
      anchorBlock) = 4)
  (pairing : Fin 3)

/-- **The guarded census supplied at an actual wall is the literal
active-label census of the wall datum.**  `OrdinaryBlockProfile.active` is an
abstract finset of labels; `ordinaryBlockProfile_of_single_row` in fact chooses
`W4StableSource.activeLabels`, and this exposes that choice. -/
theorem ordinaryBlockProfile_of_single_row_active :
    (NonTrivalentUniqueFourValent.ordinaryBlockProfile_of_single_row cover fd hc
      hab hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock
      hAnchor).active =
      activeLabels (contractDatum cover hc hab hOne) wallStar := rfl

include fd hForest in
/-- **Target-direction injectivity at every wall block of an actual four-valent
wall.**  `ordinaryBlockProfile_of_single_row` feeds
`NonTrivalentValencyFourAnchor.targetInjective` to
`ordinaryBlockProfile_of_valency_le_three` but does not expose it; this does. -/
theorem wall_starInjective
    (block : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩) :
    NonDanglingStarInjective (contractDatum cover hc hab hOne) wallStar block :=
  NonTrivalentValencyFourAnchor.targetInjective cover fd hc hab hOne wallStar
    (WallAdmissibility.danglingPreserved_of_contractionForest cover hc hab hOne
      hForest) block

local notation "wSrc" =>
  (NonTrivalentUniqueFourValent.wallFourBranchAnchor cover fd hc hab hOne
    wallStar hForest anchorBlock hAnchor)
local notation "wNG" =>
  (NonTrivalentUniqueFourValent.wall_noGlue cover fd hc hab hOne hForest)
local notation "wRam" =>
  (NonTrivalentUniqueFourValent.wall_ramification cover fd hc hab hOne wallStar
    hForest anchorBlock)
local notation "wProf" =>
  (NonTrivalentUniqueFourValent.ordinaryBlockProfile_of_single_row cover fd hc
    hab hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock
    hAnchor)
local notation "wConn" =>
  (NonTrivalentUniqueFourValent.wall_target_connected cover fd hab hOne)
local notation "wGen" =>
  (NonTrivalentUniqueFourValent.wall_target_genus cover fd hab hOne)
local notation "wVal" =>
  (NonTrivalentUniqueFourValent.wall_valid cover fd hc hab hOne hForest)

/-- **Census (2) at the gauged wall datum**: target-direction injectivity at
every block of the gauged datum. -/
theorem gauged_starInjective_of_single_row (y : Fin degree) :
    NonDanglingStarInjective (gaugedData wSrc pairing wNG wRam) wallStar
      (WallBlock.ofSheet (gaugedData wSrc pairing wNG wRam) ⟨a, hab⟩ y) := by
  rw [← gaugedBlock_ofSheet wSrc pairing wNG wRam y]
  exact nonDanglingStarInjective_gaugedBlock wSrc pairing wNG wRam wVal _
    (wall_starInjective cover fd hc hab hOne wallStar hForest _)

include hRows hZeroCoord in
/-- **The trivalence bound at the gauged wall datum**: every non-anchor block of
the gauged datum has surviving valency at most three. -/
theorem gauged_valency_of_single_row (y : Fin degree)
    (hy : ¬ ((gaugedData wSrc pairing wNG wRam).vertexPartition ⟨a, hab⟩).Rel
      anchorBlock.1 y) :
    nonDanglingValency (gaugedData wSrc pairing wNG wRam)
        (WallBlock.sourceVertex (gaugedData wSrc pairing wNG wRam) ⟨a, hab⟩
          (WallBlock.ofSheet (gaugedData wSrc pairing wNG wRam) ⟨a, hab⟩ y)) ≤
      3 := by
  rw [← gaugedBlock_ofSheet wSrc pairing wNG wRam y,
    nonDanglingValency_gaugedBlock wSrc pairing wNG wRam wVal _]
  refine NonTrivalentUniqueFourValent.nonDanglingValency_wallBlock_le_three cover
    fd hc hab hOne wallStar
    (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
      hForest)
    coordinates facet hRows hZeroCoord anchorBlock hAnchor _ ?_
  intro hRel
  refine hy ?_
  rw [gaugedData_vertexPartition_wall wSrc pairing wNG wRam]
  exact hRel.trans
    (((contractDatum cover hc hab hOne).vertexPartition ⟨a, hab⟩).rel_repr_left y)

/-! ## 6.  The unconditional chart and the common minor at an actual wall -/

/-- **The row equivalence at an actual four-valent wall.**  The hypotheses are
exactly those of
`NonTrivalentValencyFourAnchor.fourBranchAnchor_of_single_zero_row` together
with the wall metric, plus the injectivity hypothesis `hRetInj`, discharged in
`NonTrivalentValencyFourRetainedInjective`. -/
noncomputable def rowEquiv_of_single_row
    (hRetInj : Function.Injective
      (NonTrivalentValencyFourRowDictionary.retainedRow wSrc pairing wNG wRam
        wProf wConn wGen wVal)) :
    StablePath (NonTrivalentValencyFourBackground.candidate wSrc pairing wNG wRam
        wProf wConn wGen wVal).datum ≃
      Option (StablePath (gaugedData wSrc pairing wNG wRam)) :=
  rowEquiv wSrc pairing wNG wRam wProf wConn wGen wVal
    (fun y _ ↦ gauged_starInjective_of_single_row cover fd hc hab hOne wallStar
      hForest anchorBlock hAnchor pairing y)
    (fun y hy ↦ gauged_valency_of_single_row cover fd hc hab hOne wallStar
      hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing y
      hy)
    hRetInj

theorem rowEquiv_of_single_row_retainedRow
    (hRetInj : Function.Injective
      (NonTrivalentValencyFourRowDictionary.retainedRow wSrc pairing wNG wRam
        wProf wConn wGen wVal))
    (r : StablePath (gaugedData wSrc pairing wNG wRam)) :
    rowEquiv_of_single_row cover fd hc hab hOne wallStar hForest coordinates
        facet hRows hZeroCoord anchorBlock hAnchor pairing hRetInj
        (NonTrivalentValencyFourRowDictionary.retainedRow wSrc pairing wNG wRam
          wProf wConn wGen wVal r) =
      some r :=
  rowEquiv_retainedRow wSrc pairing wNG wRam wProf wConn wGen wVal _ _ hRetInj r

variable (hCompat : DanglingCompatible cover hc hab hOne)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)

/-- **The outgoing honest chart at an actual four-valent wall**, with no
supplied row equivalence: the candidate's square honest stable length-matrix
labelling, indexed by the incoming chart, with `Option.none` -- the new target
occurrence and the bridge row -- in the contracted column. -/
noncomputable def chartLabelling_of_single_row
    (hRetInj : Function.Injective
      (NonTrivalentValencyFourRowDictionary.retainedRow wSrc pairing wNG wRam
        wProf wConn wGen wVal))
    (chart : Option {column : coordinate //
      column ≠ fd.labelling.targetEdge.symm contracted} ≃ coordinate) :
    StableLengthMatrixLabelling
      (NonTrivalentValencyFourBackground.candidate wSrc pairing wNG wRam wProf
        wConn wGen wVal).datum coordinate :=
  NonTrivalentValencyFourRowDictionary.chartLabelling wSrc pairing wNG wRam wProf
    wConn wGen wVal
    (wallLabelling cover fd hc hab hOne hCompat hForest
      (noContractedReturn_of_fourStar cover fd hc hab hOne wallStar) coordinates
      facet hRows hZeroCoord hPosCoord hFacetZero)
    (rowEquiv_of_single_row cover fd hc hab hOne wallStar hForest coordinates
      facet hRows hZeroCoord anchorBlock hAnchor pairing hRetInj)
    chart

/-- **The common minor `A_{φ₀}` at an actual four-valent wall, entry by
entry.**  The outgoing honest matrix agrees with the incoming
full-dimensional cover's off the contracted column.  `NoContractedReturn` is
free at valency four (`noContractedReturn_of_fourStar`), and the only
hypothesis about the candidate is `hRetInj`. -/
theorem matrix_chartLabelling_eq_incoming_of_single_row
    (hRetInj : Function.Injective
      (NonTrivalentValencyFourRowDictionary.retainedRow wSrc pairing wNG wRam
        wProf wConn wGen wVal))
    (chart : Option {column : coordinate //
      column ≠ fd.labelling.targetEdge.symm contracted} ≃ coordinate)
    (p : StablePath (contractDatum cover hc hab hOne))
    (column : {column : coordinate //
      column ≠ fd.labelling.targetEdge.symm contracted}) :
    GluingDatum.LengthMatrixPresentation.matrix
        (chartLabelling_of_single_row cover fd hc hab hOne wallStar hForest
          coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing hCompat
          hPosCoord hFacetZero hRetInj chart).presentation
        (chart (some (wallRowIndex cover fd hc hab hOne hCompat hForest
          (noContractedReturn_of_fourStar cover fd hc hab hOne wallStar)
          coordinates facet hRows hZeroCoord hPosCoord hFacetZero p)))
        (chart (some column)) =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
        (fd.labelling.row
          (incomingRow cover fd hc hab hOne hCompat hForest p))
        column.1 :=
  NonTrivalentValencyFourRowDictionary.matrix_chartLabelling_eq_incoming cover fd
    hc hab hOne hCompat hForest
    (noContractedReturn_of_fourStar cover fd hc hab hOne wallStar) coordinates
    facet hRows hZeroCoord hPosCoord hFacetZero wSrc pairing wNG wRam wProf wConn
    wGen wVal
    (rowEquiv_of_single_row cover fd hc hab hOne wallStar hForest coordinates
      facet hRows hZeroCoord anchorBlock hAnchor pairing hRetInj)
    (rowEquiv_of_single_row_retainedRow cover fd hc hab hOne wallStar hForest
      coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing hRetInj)
    chart p column

end ActualWall

end DraismaVargas.LocalCases.NonTrivalentValencyFourRowEquivFinal
