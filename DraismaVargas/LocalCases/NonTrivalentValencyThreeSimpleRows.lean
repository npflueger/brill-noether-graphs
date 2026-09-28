import DraismaVargas.LocalCases.NonTrivalentValencyThreeRowEquiv
import DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleCandidate

/-!
# Stable rows of the prescribed Type I / Type II candidates above a three-valent wall

Source: Vargas, Part II, Section 5.3, case `{v3-nd4}` (base trees `T_alpha`
with `alpha` a *simple* direction), read through the labelling convention (1)
of Section 5.1 and, for the wall blocks other than the anchor, the rigidity
statements of Section 5.1.

This module does for `NonTrivalentValencyThreeSimpleCandidate.validCandidate`
what `NonTrivalentValencyThreeRows` and `NonTrivalentValencyThreeDescent` do
for the Type III candidate, at the **three-vertex** resolution.  Unlike the
Type III candidate, the Type I / Type II candidate lives over the
two-fold branch gauge `SimpleBase.gaugedData`, and the anchor block resolves
into three outgoing vertices rather than two:

* `A_u` above the divalent subdivision point `u`, of size `k_alpha`, with the
  exact surviving star `{e_alpha, e_1, e'}` and `nd = 3`;
* `A'` above `v`, of size `k_delta`, with star `{e', e_delta}` and `nd = 2`, so
  `e'` and `e_delta` are consecutive and the stable edge `h_delta` runs
  `A_u -> A' -> e_delta`;
* `A_v` above `v`, of size `|A| - k_delta`, with star `{e_1, e_beta, e_gamma}`
  and `nd = 3`.

So the bridge `e_1` alone is the new stable row, while the second occurrence
`e'` above `t_1` is absorbed into the retained row of `e_delta`.

## What is proved

* Section 1: the two branch gauges sheet by sheet
  (`first_edgePermutation_doubled`, `second_edgePermutation_beta`, ...), the
  transport of pruning and surviving valency across them
  (`gauged_isDangling_alpha/beta/doubled`, `gauged_nonDanglingValency_anchor`:
  the gauged anchor still has `nd = 4`), and the resulting census of the gauged
  anchor: the four named survivors survive
  (`gauged_alpha_survives`, `gauged_beta_survives`, `gauged_doubled_survives`)
  and every other occurrence of a star direction there is dangling
  (`gauged_alpha_isDangling_of_not_mem` and companions).
* Section 2: `candidate_sourceGenus` (and `candidate_sourceGenus_incoming`),
  with no receipt.  The three-vertex resolution is **not** a star in the sense
  of `NonTrivalentValencyFourRows.IsStar`, so the blockwise Euler identity is
  proved directly (`selected_euler`) from the three representative images
  `leftPick_image`, `rightPick_image`, `newEdgePick_image`; off the anchor the
  background resolution is a `fineResolution`, hence a star.
* Sections 3--4: the endpoint census.  `nonDanglingIncident_hubLeft`,
  `nonDanglingIncident_deltaRight`, `nonDanglingIncident_hubRight` give the
  three exact stars, `nonDanglingValency_hubLeft/deltaRight/hubRight` give
  `3, 2, 3`, `bridgeEdge_isolated` puts the bridge alone in its stable class,
  and `newSourceEdge_stablePath_eq_retained` puts `e'` on the retained row of
  `e_delta`.
* Sections 5--6: the ordinary-block census at the **alpha** direction
  (`newSourceEdge_survives_iff_ordinary`,
  `nonDanglingValency_endpointVertex_false_ordinary`,
  `nonDanglingIncident_endpointVertex_true_ordinary`,
  `nonDanglingValency_endpointVertex_true_ordinary`: `nd(B_v) = nd(B)`), the
  named predicate `OrdinaryBlockDescent` and its discharge
  `ordinaryBlockDescent`, so `retainedRow` is unconditional.

## What is NOT proved here

* The row *equivalence*, the instantiated labelling and the actual-wall
  headline; those are `NonTrivalentValencyThreeSimpleRowEquiv`.
* The `AgreeOffColumn` / common-minor identity against the incoming matrix.
* `data.Valid` is an explicit argument of every statement about the candidate;
  `SimpleBase` itself carries `DanglingEdgeNoGlue data`, `graph_connected
  target` and `genus target = 0`, and through `ThreeBranchAnchor` the anchor's
  `nd(A) = 4` -- all of which `NonTrivalentValencyThreeSimpleRowEquiv` discharges
  at an actual wall.

## Used by

`NonTrivalentValencyThreeSimpleRowEquiv` and the boundary dispatcher for Part II
case `{v3-nd4}`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRows

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.W3R1SourceProfile
open DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleCandidate
open DraismaVargas.LocalCases.BlockPreservingBranchSwap

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (datum : GluingDatum target degree)
    (vertex : datum.SourceVertex) : DecidableEq (IncidentSourceEdge datum vertex) :=
  Classical.decEq _

variable {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall} (base : SimpleBase data star anchor)

/-! ## 1.  The two branch gauges, sheet by sheet -/

theorem first_vertexPermutation_wall :
    base.firstRelabeling.vertexPermutation wall = Equiv.refl (Fin degree) := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.vertexMoved wall _ _ wall) base.deltaPerm = _
  rw [TargetBranchRegion.vertexMoved_wall]
  rfl

theorem second_vertexPermutation_wall :
    base.secondRelabeling.vertexPermutation wall = Equiv.refl (Fin degree) := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.vertexMoved wall _ _ wall) base.betaPerm = _
  rw [TargetBranchRegion.vertexMoved_wall]
  rfl

theorem first_edgePermutation_doubled :
    base.firstRelabeling.edgePermutation (Prescribed.doubledEdge base.source) =
      base.deltaPerm := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall _ _ (Prescribed.doubledEdge base.source))
      base.deltaPerm = _
  rw [TargetSeparation.edgeMoved_self_eq_true base.doubledEdge_incident]
  rfl

theorem first_edgePermutation_simple (label : Fin 3)
    (hLabel : label ≠ Prescribed.doubled base.source) :
    base.firstRelabeling.edgePermutation (directionEdge star label) =
      Equiv.refl (Fin degree) := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall _ _ (directionEdge star label))
      base.deltaPerm = _
  rw [TargetSeparation.edgeMoved_eq_false base.connected base.genusZero
    base.doubledEdge_incident (SimpleBase.directionEdge_incident (star := star) label)
    (base.doubledEdge_ne_direction label hLabel)]
  rfl

theorem second_edgePermutation_beta :
    base.secondRelabeling.edgePermutation (directionEdge star base.betaLabel) =
      base.betaPerm := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall _ _ (directionEdge star base.betaLabel))
      base.betaPerm = _
  rw [TargetSeparation.edgeMoved_self_eq_true
    (SimpleBase.directionEdge_incident (star := star) base.betaLabel)]
  rfl

theorem second_edgePermutation_alpha :
    base.secondRelabeling.edgePermutation (directionEdge star base.alphaLabel) =
      Equiv.refl (Fin degree) := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall _ _ (directionEdge star base.alphaLabel))
      base.betaPerm = _
  rw [TargetSeparation.edgeMoved_eq_false base.connected base.genusZero
    (SimpleBase.directionEdge_incident (star := star) base.betaLabel)
    (SimpleBase.directionEdge_incident (star := star) base.alphaLabel)
    (fun hEq ↦ base.beta_ne_alpha (directionEdge_injective star hEq))]
  rfl

theorem second_edgePermutation_doubled :
    base.secondRelabeling.edgePermutation (Prescribed.doubledEdge base.source) =
      Equiv.refl (Fin degree) := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall _ _ (Prescribed.doubledEdge base.source))
      base.betaPerm = _
  rw [TargetSeparation.edgeMoved_eq_false base.connected base.genusZero
    (SimpleBase.directionEdge_incident (star := star) base.betaLabel)
    base.doubledEdge_incident
    (fun hEq ↦ base.doubledEdge_ne_direction base.betaLabel base.beta_ne hEq.symm)]
  rfl

/-! ### Transport of pruning and surviving valency across the two gauges -/

private theorem isDangling_step {datum : GluingDatum target degree}
    (relabeling : datum.SheetRelabeling) (hConnected : datum.Connected)
    (edge : target.edges) (sheet : Fin degree) :
    IsDangling relabeling.apply
        (relabeling.apply.sourceEdge edge (relabeling.edgePermutation edge sheet)) ↔
      IsDangling datum (datum.sourceEdge edge sheet) := by
  have h := SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff relabeling hConnected
    (datum.sourceEdge edge sheet)
  rwa [SheetRelabelPruning.sourceEdgeEquiv_sourceEdge] at h

private theorem nonDanglingValency_step {datum : GluingDatum target degree}
    (relabeling : datum.SheetRelabeling) (hConnected : datum.Connected)
    (vertex : target.V) (sheet : Fin degree) :
    nonDanglingValency relabeling.apply
        (relabeling.apply.sourceEndpoint vertex
          (relabeling.vertexPermutation vertex sheet)) =
      nonDanglingValency datum (datum.sourceEndpoint vertex sheet) := by
  have h := SheetRelabelStable.nonDanglingValency_map relabeling hConnected
    (datum.sourceEndpoint vertex sheet)
  rwa [SheetRelabelPruning.sourceVertexEquiv_sourceEndpoint] at h

theorem middleData_connected (hValid : data.Valid) : base.middleData.Connected :=
  (base.middleData_valid hValid).1

/-- The gauge leaves the occurrences of `t_alpha` alone. -/
theorem gauged_isDangling_alpha (hValid : data.Valid) (sheet : Fin degree) :
    IsDangling base.gaugedData
        (base.gaugedData.sourceEdge (directionEdge star base.alphaLabel) sheet) ↔
      IsDangling data (data.sourceEdge (directionEdge star base.alphaLabel) sheet) := by
  have h2 := isDangling_step base.secondRelabeling (middleData_connected base hValid)
    (directionEdge star base.alphaLabel) sheet
  rw [second_edgePermutation_alpha base, Equiv.refl_apply] at h2
  have h1 := isDangling_step base.firstRelabeling hValid.1
    (directionEdge star base.alphaLabel) sheet
  rw [first_edgePermutation_simple base base.alphaLabel base.alpha_ne,
    Equiv.refl_apply] at h1
  exact h2.trans h1

/-- The occurrences of `t_beta` are carried by `betaPerm`. -/
theorem gauged_isDangling_beta (hValid : data.Valid) (sheet : Fin degree) :
    IsDangling base.gaugedData
        (base.gaugedData.sourceEdge (directionEdge star base.betaLabel)
          (base.betaPerm sheet)) ↔
      IsDangling data (data.sourceEdge (directionEdge star base.betaLabel) sheet) := by
  have h2 := isDangling_step base.secondRelabeling (middleData_connected base hValid)
    (directionEdge star base.betaLabel) sheet
  rw [second_edgePermutation_beta base] at h2
  have h1 := isDangling_step base.firstRelabeling hValid.1
    (directionEdge star base.betaLabel) sheet
  rw [first_edgePermutation_simple base base.betaLabel base.beta_ne,
    Equiv.refl_apply] at h1
  exact h2.trans h1

/-- The occurrences of the doubled direction are carried by `deltaPerm`. -/
theorem gauged_isDangling_doubled (hValid : data.Valid) (sheet : Fin degree) :
    IsDangling base.gaugedData
        (base.gaugedData.sourceEdge (Prescribed.doubledEdge base.source)
          (base.deltaPerm sheet)) ↔
      IsDangling data
        (data.sourceEdge (Prescribed.doubledEdge base.source) sheet) := by
  have h2 := isDangling_step base.secondRelabeling (middleData_connected base hValid)
    (Prescribed.doubledEdge base.source) (base.deltaPerm sheet)
  rw [second_edgePermutation_doubled base, Equiv.refl_apply] at h2
  have h1 := isDangling_step base.firstRelabeling hValid.1
    (Prescribed.doubledEdge base.source) sheet
  rw [first_edgePermutation_doubled base] at h1
  exact h2.trans h1

/-- **The gauged anchor has the same surviving valency.** -/
theorem gauged_nonDanglingValency_wall (hValid : data.Valid) (sheet : Fin degree) :
    nonDanglingValency base.gaugedData (base.gaugedData.sourceEndpoint wall sheet) =
      nonDanglingValency data (data.sourceEndpoint wall sheet) := by
  have h2 := nonDanglingValency_step base.secondRelabeling
    (middleData_connected base hValid) wall sheet
  rw [second_vertexPermutation_wall base, Equiv.refl_apply] at h2
  have h1 := nonDanglingValency_step base.firstRelabeling hValid.1 wall sheet
  rw [first_vertexPermutation_wall base, Equiv.refl_apply] at h1
  exact h2.trans h1

/-! ### The four named survivors of the gauged anchor -/

theorem directionSurvivors_doubled_pair :
    directionSurvivors data star anchor (Prescribed.doubled base.source) =
      {base.deltaSurvivor, base.gammaSurvivor} := by
  rw [Prescribed.directionSurvivors_doubled_eq_pair]
  show _ = ({doubledSurvivor base.source base.swapDoubled,
    doubledSurvivor base.source (!base.swapDoubled)} : Finset _)
  cases base.swapDoubled
  · rfl
  · exact Finset.pair_comm _ _

/-- The contrapositive of `Prescribed.mem_survivorBlock_or_singleton`: an
occurrence of a star direction at the anchor which lies in no surviving class
is dangling. -/
private theorem data_isDangling_of_not_survivor (label : Fin 3) {sheet : Fin degree}
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet)
    (hNot : ∀ edge ∈ directionSurvivors data star anchor label,
      sheet ∉ occurrenceBlock data edge) :
    IsDangling data (data.sourceEdge (directionEdge star label) sheet) := by
  classical
  by_contra hSurvives
  have hWall' : (data.vertexPartition wall).Rel anchor.1
      (data.sourceEdge (directionEdge star label) sheet).1.2 :=
    hWall.trans ((Prescribed.directionEdge_refines (data := data) (star := star) label).rel
      ((data.edgePartition (directionEdge star label)).rel_repr_right sheet))
  obtain ⟨edge, hEdge, hEq⟩ := NonTrivalentValencyThreeRows.exists_directionSurvivor_eq
    label (data.sourceEdge (directionEdge star label) sheet) rfl hWall' hSurvives
  refine hNot edge hEdge ?_
  refine (mem_occurrenceBlock_iff hEdge sheet).mpr ?_
  have hSheet : Prescribed.occurrenceSheet edge =
      (data.edgePartition (directionEdge star label)).repr sheet :=
    congrArg (fun e : data.SourceEdge ↦ e.1.2) hEq
  rw [hSheet]
  exact (data.edgePartition (directionEdge star label)).rel_repr_left sheet

/-- Off `A_u` every occurrence of `t_alpha` at the anchor is dangling. -/
theorem gauged_alpha_isDangling_of_not_mem (hValid : data.Valid) {sheet : Fin degree}
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet)
    (hNot : sheet ∉ base.alphaBlock) :
    IsDangling base.gaugedData
      (base.gaugedData.sourceEdge (directionEdge star base.alphaLabel) sheet) := by
  classical
  rw [gauged_isDangling_alpha base hValid]
  refine data_isDangling_of_not_survivor base.alphaLabel hWall ?_
  intro edge hEdge
  rw [directionSurvivors_simple_eq base.source base.alphaLabel base.alpha_ne,
    Finset.mem_singleton] at hEdge
  subst hEdge
  exact hNot

/-- Off the gauged class of `e_beta` every occurrence of `t_beta` at the anchor
is dangling. -/
theorem gauged_beta_isDangling_of_not_mem (hValid : data.Valid) {sheet : Fin degree}
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet)
    (hNot : sheet ∉ base.newBetaBlock) :
    IsDangling base.gaugedData
      (base.gaugedData.sourceEdge (directionEdge star base.betaLabel) sheet) := by
  classical
  have hEq : base.betaPerm (base.betaPerm.symm sheet) = sheet := by simp
  have hWall0 : (data.vertexPartition wall).Rel anchor.1 (base.betaPerm.symm sheet) := by
    refine hWall.trans ?_
    have := rel_of_stabilizes_block (data.vertexPartition wall) anchor.1 base.betaPerm
      base.betaPerm_inside base.betaPerm_outside (base.betaPerm.symm sheet)
    rwa [hEq] at this
  have hData : IsDangling data
      (data.sourceEdge (directionEdge star base.betaLabel) (base.betaPerm.symm sheet)) := by
    refine data_isDangling_of_not_survivor base.betaLabel hWall0 ?_
    intro edge hEdge
    rw [directionSurvivors_simple_eq base.source base.betaLabel base.beta_ne,
      Finset.mem_singleton] at hEdge
    subst hEdge
    intro hMem
    exact hNot (hEq ▸ Finset.mem_image.mpr ⟨_, hMem, rfl⟩)
  have := (gauged_isDangling_beta base hValid (base.betaPerm.symm sheet)).mpr hData
  rwa [hEq] at this

/-- Off `A'` and the gauged class of `e_gamma` every occurrence of the doubled
direction at the anchor is dangling. -/
theorem gauged_doubled_isDangling_of_not_mem (hValid : data.Valid) {sheet : Fin degree}
    (hWall : (data.vertexPartition wall).Rel anchor.1 sheet)
    (hDelta : sheet ∉ base.newDeltaBlock) (hGamma : sheet ∉ base.newGammaBlock) :
    IsDangling base.gaugedData
      (base.gaugedData.sourceEdge (Prescribed.doubledEdge base.source) sheet) := by
  classical
  have hEq : base.deltaPerm (base.deltaPerm.symm sheet) = sheet := by simp
  have hWall0 : (data.vertexPartition wall).Rel anchor.1 (base.deltaPerm.symm sheet) := by
    refine hWall.trans ?_
    have := rel_of_stabilizes_block (data.vertexPartition wall) anchor.1 base.deltaPerm
      base.deltaPerm_inside base.deltaPerm_outside (base.deltaPerm.symm sheet)
    rwa [hEq] at this
  have hData : IsDangling data
      (data.sourceEdge (Prescribed.doubledEdge base.source) (base.deltaPerm.symm sheet)) := by
    refine data_isDangling_of_not_survivor (Prescribed.doubled base.source) hWall0 ?_
    intro edge hEdge
    rw [directionSurvivors_doubled_pair base, Finset.mem_insert, Finset.mem_singleton] at hEdge
    intro hMem
    rcases hEdge with rfl | rfl
    · exact hDelta (hEq ▸ Finset.mem_image.mpr ⟨_, hMem, rfl⟩)
    · exact hGamma (hEq ▸ Finset.mem_image.mpr ⟨_, hMem, rfl⟩)
  have := (gauged_isDangling_doubled base hValid (base.deltaPerm.symm sheet)).mpr hData
  rwa [hEq] at this

private theorem sourceEdge_eq_of_rel {datum : GluingDatum target degree}
    {edge : target.edges} {a b : Fin degree}
    (h : (datum.edgePartition edge).Rel a b) :
    datum.sourceEdge edge a = datum.sourceEdge edge b := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact h

/-- `e_alpha` survives at every sheet of `A_u`. -/
theorem gauged_alpha_survives (hValid : data.Valid) {sheet : Fin degree}
    (hMem : sheet ∈ base.alphaBlock) :
    ¬ IsDangling base.gaugedData
      (base.gaugedData.sourceEdge (directionEdge star base.alphaLabel) sheet) := by
  rw [gauged_isDangling_alpha base hValid,
    sourceEdge_eq_of_rel
      ((mem_occurrenceBlock_iff base.alphaSurvivor_mem sheet).mp hMem).symm,
    NonTrivalentValencyThreeRows.sourceEdge_occurrenceSheet base.alphaSurvivor_mem]
  exact NonTrivalentValencyThreeRows.survivor_not_isDangling base.alphaSurvivor_mem

/-- `e_beta` survives at every sheet of its gauged class. -/
theorem gauged_beta_survives (hValid : data.Valid) {sheet : Fin degree}
    (hMem : sheet ∈ base.newBetaBlock) :
    ¬ IsDangling base.gaugedData
      (base.gaugedData.sourceEdge (directionEdge star base.betaLabel) sheet) := by
  classical
  obtain ⟨original, hOriginal, rfl⟩ := Finset.mem_image.mp hMem
  rw [gauged_isDangling_beta base hValid original,
    sourceEdge_eq_of_rel
      ((mem_occurrenceBlock_iff base.betaSurvivor_mem original).mp hOriginal).symm,
    NonTrivalentValencyThreeRows.sourceEdge_occurrenceSheet base.betaSurvivor_mem]
  exact NonTrivalentValencyThreeRows.survivor_not_isDangling base.betaSurvivor_mem

/-- `e_delta` and `e_gamma` survive at every sheet of their gauged classes. -/
theorem gauged_doubled_survives (hValid : data.Valid) {sheet : Fin degree}
    (hMem : sheet ∈ base.newDeltaBlock ∨ sheet ∈ base.newGammaBlock) :
    ¬ IsDangling base.gaugedData
      (base.gaugedData.sourceEdge (Prescribed.doubledEdge base.source) sheet) := by
  classical
  rcases hMem with hMem | hMem
  · obtain ⟨original, hOriginal, rfl⟩ := Finset.mem_image.mp hMem
    rw [gauged_isDangling_doubled base hValid original]
    show ¬ IsDangling data (data.sourceEdge
      (directionEdge star (Prescribed.doubled base.source)) original)
    rw [sourceEdge_eq_of_rel
        ((mem_occurrenceBlock_iff base.deltaSurvivor_mem original).mp hOriginal).symm,
      NonTrivalentValencyThreeRows.sourceEdge_occurrenceSheet base.deltaSurvivor_mem]
    exact NonTrivalentValencyThreeRows.survivor_not_isDangling base.deltaSurvivor_mem
  · obtain ⟨original, hOriginal, rfl⟩ := Finset.mem_image.mp hMem
    rw [gauged_isDangling_doubled base hValid original]
    show ¬ IsDangling data (data.sourceEdge
      (directionEdge star (Prescribed.doubled base.source)) original)
    rw [sourceEdge_eq_of_rel
        ((mem_occurrenceBlock_iff base.gammaSurvivor_mem original).mp hOriginal).symm,
      NonTrivalentValencyThreeRows.sourceEdge_occurrenceSheet base.gammaSurvivor_mem]
    exact NonTrivalentValencyThreeRows.survivor_not_isDangling base.gammaSurvivor_mem

/-- **The gauged anchor still has surviving valency four.** -/
theorem gauged_nonDanglingValency_anchor (hValid : data.Valid) :
    nonDanglingValency base.gaugedData
      (base.gaugedData.sourceEndpoint wall anchor.1) = 4 := by
  rw [gauged_nonDanglingValency_wall base hValid anchor.1]
  exact NonTrivalentValencyThreeRows.nonDanglingValency_anchor base.source

/-! ## 2.  The three-vertex resolution preserves the source genus -/

private theorem blockRefine_blockCountWithin_of_rel (coarse : SheetPartition degree)
    (a : Fin degree) (pick : Fin degree → Fin degree)
    (hPick : ∀ sheet, coarse.Rel a sheet → coarse.Rel a (pick sheet))
    (hIdem : ∀ sheet, coarse.Rel a sheet → pick (pick sheet) = pick sheet)
    {sheet : Fin degree} (hSheet : coarse.Rel a sheet) :
    (blockRefine coarse a pick hPick hIdem).blockCountWithin coarse sheet =
      ((coarse.block a).image pick).card := by
  classical
  show (((coarse.block sheet).image
    (blockRefine coarse a pick hPick hIdem).repr).card) = _
  rw [← coarse.block_eq_of_rel hSheet]
  refine congrArg Finset.card (Finset.image_congr ?_)
  intro other hOther
  exact blockRefine.repr_of_rel coarse a pick hPick hIdem
    ((coarse.mem_block_iff a other).mp hOther)

private theorem blockRefine_blockCountWithin_of_not_rel (coarse : SheetPartition degree)
    (a : Fin degree) (pick : Fin degree → Fin degree)
    (hPick : ∀ sheet, coarse.Rel a sheet → coarse.Rel a (pick sheet))
    (hIdem : ∀ sheet, coarse.Rel a sheet → pick (pick sheet) = pick sheet)
    {sheet : Fin degree} (hSheet : ¬ coarse.Rel a sheet) :
    (blockRefine coarse a pick hPick hIdem).blockCountWithin coarse sheet = 1 := by
  classical
  have hImage : (coarse.block sheet).image
      (blockRefine coarse a pick hPick hIdem).repr = {coarse.repr sheet} := by
    ext other
    rw [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyRel : coarse.Rel sheet y := (coarse.mem_block_iff sheet y).mp hy
      have hyNot : ¬ coarse.Rel a y := fun h ↦ hSheet (h.trans hyRel.symm)
      rw [blockRefine.repr_of_not_rel coarse a pick hPick hIdem hyNot]
      exact hyRel.symm
    · rintro rfl
      refine ⟨sheet, coarse.self_mem_block sheet, ?_⟩
      exact blockRefine.repr_of_not_rel coarse a pick hPick hIdem hSheet
  show (((coarse.block sheet).image
    (blockRefine coarse a pick hPick hIdem).repr).card) = _
  rw [hImage, Finset.card_singleton]

theorem leftPick_image :
    base.wholeBlock.image base.leftPick =
      insert base.hubSheet (base.wholeBlock \ base.alphaBlock) := by
  classical
  ext other
  rw [Finset.mem_image, Finset.mem_insert, Finset.mem_sdiff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_cases hAlpha : y ∈ base.alphaBlock
    · exact Or.inl (base.leftPick_of_mem hAlpha)
    · rw [base.leftPick_of_not_mem hAlpha]
      exact Or.inr ⟨hy, hAlpha⟩
  · rintro (rfl | ⟨hy, hAlpha⟩)
    · exact ⟨base.hubSheet, base.alphaBlock_subset base.hubSheet_mem_alpha,
        base.leftPick_of_mem base.hubSheet_mem_alpha⟩
    · exact ⟨other, hy, base.leftPick_of_not_mem hAlpha⟩

theorem rightPick_image :
    base.wholeBlock.image base.rightPick = {base.deltaRepr, base.hubSheet} := by
  classical
  ext other
  rw [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨y, _, rfl⟩
    by_cases hDelta : y ∈ base.newDeltaBlock
    · exact Or.inl (base.rightPick_of_mem hDelta)
    · exact Or.inr (base.rightPick_of_not_mem hDelta)
  · rintro (rfl | rfl)
    · exact ⟨base.deltaRepr, base.newDeltaBlock_subset_whole base.deltaRepr_mem,
        base.rightPick_of_mem base.deltaRepr_mem⟩
    · exact ⟨base.hubSheet, base.alphaBlock_subset base.hubSheet_mem_alpha,
        base.rightPick_of_not_mem base.hubSheet_not_mem_newDelta⟩

theorem newEdgePick_image :
    base.wholeBlock.image base.newEdgePick =
      insert base.deltaRepr (insert base.hubSheet (base.wholeBlock \ base.alphaBlock)) := by
  classical
  ext other
  rw [Finset.mem_image, Finset.mem_insert, Finset.mem_insert, Finset.mem_sdiff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_cases hDelta : y ∈ base.newDeltaBlock
    · exact Or.inl (base.newEdgePick_of_mem hDelta)
    · by_cases hAlpha : y ∈ base.alphaBlock
      · exact Or.inr (Or.inl (base.newEdgePick_of_bridge hDelta hAlpha))
      · rw [base.newEdgePick_of_outside hAlpha]
        exact Or.inr (Or.inr ⟨hy, hAlpha⟩)
  · rintro (rfl | rfl | ⟨hy, hAlpha⟩)
    · exact ⟨base.deltaRepr, base.newDeltaBlock_subset_whole base.deltaRepr_mem,
        base.newEdgePick_of_mem base.deltaRepr_mem⟩
    · exact ⟨base.hubSheet, base.alphaBlock_subset base.hubSheet_mem_alpha,
        base.newEdgePick_of_bridge base.hubSheet_not_mem_newDelta
          base.hubSheet_mem_alpha⟩
    · exact ⟨other, hy, base.newEdgePick_of_outside hAlpha⟩

/-- **The blockwise Euler identity of the three-vertex resolution**: over `u`
the anchor block splits into `A_u` and `|A| - k_alpha` singletons, over `v`
into `A'` and `A_v`, and the new edge sees `A'`, the bridge and the same
singletons. -/
theorem selected_euler {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    base.selectedResolution.newEdge.blockCountWithin
          (data.vertexPartition wall) sheet + 1 =
      base.selectedResolution.left.blockCountWithin
          (data.vertexPartition wall) sheet +
        base.selectedResolution.right.blockCountWithin
          (data.vertexPartition wall) sheet := by
  classical
  have hHubNot : base.hubSheet ∉ base.wholeBlock \ base.alphaBlock := by
    rw [Finset.mem_sdiff]
    exact fun h ↦ h.2 base.hubSheet_mem_alpha
  have hDeltaNot : base.deltaRepr ∉ insert base.hubSheet
      (base.wholeBlock \ base.alphaBlock) := by
    rw [Finset.mem_insert, Finset.mem_sdiff]
    rintro (hEq | h)
    · exact base.hubSheet_ne_deltaRepr hEq.symm
    · exact h.2 base.deltaRepr_mem_alpha
  show base.newEdgePartition.blockCountWithin (data.vertexPartition wall) sheet + 1 =
    base.leftPartition.blockCountWithin (data.vertexPartition wall) sheet +
      base.rightPartition.blockCountWithin (data.vertexPartition wall) sheet
  rw [show base.newEdgePartition = blockRefine (data.vertexPartition wall) anchor.1
      base.newEdgePick base.newEdgePick_wall base.newEdgePick_idem from rfl,
    show base.leftPartition = blockRefine (data.vertexPartition wall) anchor.1
      base.leftPick base.leftPick_wall base.leftPick_idem from rfl,
    show base.rightPartition = blockRefine (data.vertexPartition wall) anchor.1
      base.rightPick base.rightPick_wall base.rightPick_idem from rfl,
    blockRefine_blockCountWithin_of_rel _ _ _ _ _ hSheet,
    blockRefine_blockCountWithin_of_rel _ _ _ _ _ hSheet,
    blockRefine_blockCountWithin_of_rel _ _ _ _ _ hSheet]
  show (base.wholeBlock.image base.newEdgePick).card + 1 =
    (base.wholeBlock.image base.leftPick).card +
      (base.wholeBlock.image base.rightPick).card
  rw [leftPick_image base, rightPick_image base, newEdgePick_image base,
    Finset.card_insert_of_notMem hDeltaNot,
    Finset.card_insert_of_notMem hHubNot,
    Finset.card_insert_of_notMem (by
      rw [Finset.mem_singleton]
      exact fun h ↦ base.hubSheet_ne_deltaRepr h.symm),
    Finset.card_singleton]

theorem isStar_ordinaryResolution :
    NonTrivalentValencyFourRows.IsStar (base.gaugedData.vertexPartition wall)
      (ordinaryResolution base) :=
  NonTrivalentValencyFourRows.isStar_fineResolution _ _ _

/-- Off the anchor block the candidate uses the single global background
resolution of `subdivisionBackground`. -/
theorem candidate_resolution_of_not_wall_rel (hValid : data.Valid) (block : Fin degree)
    (hBlock : ¬ (base.gaugedData.vertexPartition wall).Rel anchor.1 block) :
    (validCandidate base hValid).resolution block = ordinaryResolution base := by
  unfold validCandidate candidate SubdivisionBackground.background
    GlobalM11Arbitrary.Background.install
  exact LocalResolution.onBlock_of_not_rel _ _ _ _ _ hBlock

/-- **The Type I / Type II candidate does not change the source genus.**  The
anchor's three-vertex resolution is not a star, but it satisfies the same
blockwise Euler identity (`selected_euler`); off the anchor the background
resolution is a `fineResolution`, hence a star. -/
theorem candidate_sourceGenus (hValid : data.Valid) :
    genus (validCandidate base hValid).datum.sourceGraph =
      genus base.gaugedData.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_blockwise_euler
  intro block _hCanonical
  by_cases hBlock : (base.gaugedData.vertexPartition wall).Rel anchor.1 block
  · rw [validCandidate_resolution_of_wall_rel base hValid block hBlock,
      base.gaugedData_vertexPartition_wall]
    exact selected_euler base
      (by rwa [base.gaugedData_vertexPartition_wall] at hBlock)
  · rw [candidate_resolution_of_not_wall_rel base hValid block hBlock]
    exact NonTrivalentValencyFourRows.euler_of_isStar
      (isStar_ordinaryResolution base) block

/-- The gauge itself does not change the source genus, so the candidate's
source genus is the incoming one. -/
theorem gaugedData_sourceGenus :
    genus base.gaugedData.sourceGraph = genus data.sourceGraph :=
  base.secondRelabeling.sourceGraphLaplacianEquiv.genus_eq.trans
    base.firstRelabeling.sourceGraphLaplacianEquiv.genus_eq

theorem candidate_sourceGenus_incoming (hValid : data.Valid) :
    genus (validCandidate base hValid).datum.sourceGraph = genus data.sourceGraph :=
  (candidate_sourceGenus base hValid).trans (gaugedData_sourceGenus base)

/-! ## 3.  The three outgoing vertices above the anchor -/

theorem gauged_rel_iff {a b : Fin degree} :
    (base.gaugedData.vertexPartition wall).Rel a b ↔ (data.vertexPartition wall).Rel a b := by
  rw [base.gaugedData_vertexPartition_wall]

/-- The endpoint partition on one side of the new target edge `t_1`: `A_u` and
its dangling singletons over the divalent end `u`, and `A'` together with `A_v`
over the trivalent end `v`. -/
noncomputable def endpointPartition (sideValue : Bool) : SheetPartition degree :=
  if sideValue then base.rightPartition else base.leftPartition

@[simp] theorem endpointPartition_false :
    endpointPartition base false = base.leftPartition := rfl

@[simp] theorem endpointPartition_true :
    endpointPartition base true = base.rightPartition := rfl

theorem endpointPartition_refines (sideValue : Bool) :
    (endpointPartition base sideValue).Refines (data.vertexPartition wall) := by
  cases sideValue
  · exact base.leftPartition_refines
  · exact base.rightPartition_refines

/-- The actual outgoing source vertex on one side of the new target edge. -/
noncomputable def endpointVertex (hValid : data.Valid) (sideValue : Bool)
    (sheet : Fin degree) : (validCandidate base hValid).datum.SourceVertex :=
  (validCandidate base hValid).datum.sourceEndpoint
    (if sideValue then freshVertex target else oldVertex target wall) sheet

/-- A new occurrence above the new target edge `t_1`. -/
noncomputable def bridgeEdge (hValid : data.Valid) (sheet : Fin degree) :
    (validCandidate base hValid).datum.SourceEdge :=
  (validCandidate base hValid).newSourceEdge sheet

theorem sourceEnds_bridgeEdge (hValid : data.Valid) (sheet : Fin degree) :
    (validCandidate base hValid).datum.sourceEnds (bridgeEdge base hValid sheet) =
      (endpointVertex base hValid false sheet, endpointVertex base hValid true sheet) :=
  GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet

theorem bridgeEdge_incident (hValid : data.Valid) (sideValue : Bool)
    (sheet : Fin degree) :
    Incident (validCandidate base hValid).datum (bridgeEdge base hValid sheet)
      (endpointVertex base hValid sideValue sheet) := by
  cases sideValue
  · exact Or.inl (congrArg Prod.fst
      (GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet))
  · exact Or.inr (congrArg Prod.snd
      (GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet))

theorem retainedEdge_incident (hValid : data.Valid) (edge : target.edges)
    (hAt : edge ∈ GluingDatum.incidentEdges wall) (sideValue : Bool)
    (hSide : base.rightAssignment edge = sideValue) (sheet : Fin degree) :
    Incident (validCandidate base hValid).datum
      ((validCandidate base hValid).oldSourceEdge (base.gaugedData.sourceEdge edge sheet))
      (endpointVertex base hValid sideValue sheet) := by
  cases sideValue
  · exact LimitChainCore.oldSourceEdge_incident_old _ edge hAt hSide sheet
  · exact M11SplitSurvival.oldSourceEdge_incident_fresh _ edge hAt hSide sheet

/-- Inside the anchor block, two sheets name the same outgoing endpoint vertex
exactly when the endpoint partition of that side relates them. -/
theorem candidate_vertexPartition_rel_iff (hValid : data.Valid) (sideValue : Bool)
    {a b : Fin degree} (hA : (data.vertexPartition wall).Rel anchor.1 a) :
    ((validCandidate base hValid).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall)).Rel a b ↔
      (endpointPartition base sideValue).Rel a b := by
  have hReprRel : (base.gaugedData.vertexPartition wall).Rel anchor.1
      ((base.gaugedData.vertexPartition wall).repr a) := by
    rw [gauged_rel_iff base, base.gaugedData_vertexPartition_wall]
    exact hA.trans ((data.vertexPartition wall).rel_repr_right a)
  have hSelected := validCandidate_resolution_of_wall_rel base hValid _ hReprRel
  cases sideValue
  · show ((validCandidate base hValid).datum.vertexPartition
      (oldVertex target wall)).Rel a b ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
    refine Iff.trans (SheetPartition.paste_rel_iff (base.gaugedData.vertexPartition wall)
      (fun blk ↦ ((validCandidate base hValid).resolution blk).left)
      (fun blk ↦ ((validCandidate base hValid).contracts blk).left_refines) a b) ?_
    rw [hSelected]
    rfl
  · show ((validCandidate base hValid).datum.vertexPartition
      (freshVertex target)).Rel a b ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]
    refine Iff.trans (SheetPartition.paste_rel_iff (base.gaugedData.vertexPartition wall)
      (fun blk ↦ ((validCandidate base hValid).resolution blk).right)
      (fun blk ↦ ((validCandidate base hValid).contracts blk).right_refines) a b) ?_
    rw [hSelected]
    rfl

theorem endpointVertex_eq (hValid : data.Valid) (sideValue : Bool) {a b : Fin degree}
    (hA : (data.vertexPartition wall).Rel anchor.1 a)
    (hRel : (endpointPartition base sideValue).Rel a b) :
    endpointVertex base hValid sideValue a = endpointVertex base hValid sideValue b := by
  apply (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr
  refine ⟨rfl, ?_⟩
  refine Eq.trans ?_ (((validCandidate base hValid).datum.vertexPartition
    (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right b)
  exact (candidate_vertexPartition_rel_iff base hValid sideValue hA).mpr hRel

theorem mem_incidentEdges_endpoint_old (hValid : data.Valid) (sideValue : Bool)
    (edge : target.edges) :
    occurrenceEquiv target wall (validCandidate base hValid).right (some edge) ∈
        GluingDatum.incidentEdges
          (if sideValue then freshVertex target else oldVertex target wall) ↔
      (edge ∈ GluingDatum.incidentEdges wall ∧
        base.rightAssignment edge = sideValue) := by
  rw [GluingContraction.mem_incidentEdges_iff, occurrenceEquiv_some,
    GluingContraction.mem_incidentEdges_iff]
  cases sideValue
  · exact oldEnds_incident_oldVertex_iff target wall
      (validCandidate base hValid).right edge
  · exact oldEnds_incident_freshVertex_iff target wall
      (validCandidate base hValid).right edge

theorem endpointPartition_rel_of_incident (hValid : data.Valid) (sideValue : Bool)
    {t : Fin degree} (hT : (data.vertexPartition wall).Rel anchor.1 t)
    {e : (validCandidate base hValid).datum.SourceEdge}
    (hIncident : Incident (validCandidate base hValid).datum e
      (endpointVertex base hValid sideValue t)) :
    (endpointPartition base sideValue).Rel t e.1.2 := by
  rw [incident_iff_target_mem_and_rel] at hIncident
  refine (candidate_vertexPartition_rel_iff base hValid sideValue hT).mp ?_
  exact Eq.trans
    (((validCandidate base hValid).datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right t)
    hIncident.2

theorem right_eq_of_incident_old (hValid : data.Valid) (sideValue : Bool)
    {t : Fin degree} {old : base.gaugedData.SourceEdge}
    (hIncident : Incident (validCandidate base hValid).datum
      ((validCandidate base hValid).oldSourceEdge old)
      (endpointVertex base hValid sideValue t)) :
    old.1.1 ∈ GluingDatum.incidentEdges wall ∧
      base.rightAssignment old.1.1 = sideValue := by
  rw [incident_iff_target_mem_and_rel] at hIncident
  have hTargetMem := hIncident.1
  rw [BalancedGlobal.Candidate.oldSourceEdge_target] at hTargetMem
  exact (mem_incidentEdges_endpoint_old base hValid sideValue old.1.1).mp hTargetMem

theorem newSourceEdge_eq_of_rel (hValid : data.Valid) {a b : Fin degree}
    (h : (LocalResolution.paste (base.gaugedData.vertexPartition wall)
      (validCandidate base hValid).resolution
      (validCandidate base hValid).contracts).newEdge.Rel a b) :
    (validCandidate base hValid).newSourceEdge a =
      (validCandidate base hValid).newSourceEdge b := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact h

theorem newEdge_rel_iff_newEdgePartition (hValid : data.Valid) {a b : Fin degree}
    (hA : (data.vertexPartition wall).Rel anchor.1 a) :
    (LocalResolution.paste (base.gaugedData.vertexPartition wall)
        (validCandidate base hValid).resolution
        (validCandidate base hValid).contracts).newEdge.Rel a b ↔
      base.newEdgePartition.Rel a b := by
  have hReprRel : (base.gaugedData.vertexPartition wall).Rel anchor.1
      ((base.gaugedData.vertexPartition wall).repr a) := by
    rw [gauged_rel_iff base, base.gaugedData_vertexPartition_wall]
    exact hA.trans ((data.vertexPartition wall).rel_repr_right a)
  have hSelected := validCandidate_resolution_of_wall_rel base hValid _ hReprRel
  refine Iff.trans (SheetPartition.paste_rel_iff (base.gaugedData.vertexPartition wall)
    (fun blk ↦ ((validCandidate base hValid).resolution blk).newEdge)
    (fun blk ↦ ((validCandidate base hValid).resolution blk).edge_refines_left.trans
      ((validCandidate base hValid).contracts blk).left_refines) a b) ?_
  rw [hSelected]
  rfl

/-! ### Identifying the old occurrences at the three new vertices -/

theorem oldSourceEdge_eq {old : base.gaugedData.SourceEdge} {edge : target.edges}
    {sheet : Fin degree} (hTarget : old.1.1 = edge)
    (hRel : (base.gaugedData.edgePartition edge).Rel sheet old.1.2) :
    old = base.gaugedData.sourceEdge edge sheet := by
  apply Subtype.ext
  apply Prod.ext
  · exact hTarget
  · show old.1.2 = (base.gaugedData.edgePartition edge).repr sheet
    have h : (base.gaugedData.edgePartition edge).repr old.1.2 = old.1.2 := by
      have hOld := old.2
      rw [hTarget] at hOld
      exact hOld
    exact (hRel.trans h).symm

theorem alpha_rel_of_mem {a b : Fin degree} (ha : a ∈ base.alphaBlock)
    (hb : b ∈ base.alphaBlock) :
    (base.gaugedData.edgePartition (directionEdge star base.alphaLabel)).Rel a b := by
  rw [base.gaugedData_edgePartition_alpha]
  rw [base.alphaBlock_eq] at ha hb
  exact ((SheetPartition.mem_block_iff _ _ _).mp ha).symm.trans
    ((SheetPartition.mem_block_iff _ _ _).mp hb)

theorem doubled_rel_of_mem_newDelta {a b : Fin degree} (ha : a ∈ base.newDeltaBlock)
    (hb : b ∈ base.newDeltaBlock) :
    (base.gaugedData.edgePartition (Prescribed.doubledEdge base.source)).Rel a b := by
  rw [← base.gaugedDoubled_block_delta] at ha hb
  exact ((SheetPartition.mem_block_iff _ _ _).mp ha).symm.trans
    ((SheetPartition.mem_block_iff _ _ _).mp hb)

theorem doubled_rel_of_mem_newGamma {a b : Fin degree} (ha : a ∈ base.newGammaBlock)
    (hb : b ∈ base.newGammaBlock) :
    (base.gaugedData.edgePartition (Prescribed.doubledEdge base.source)).Rel a b := by
  rw [← base.gaugedDoubled_block_gamma] at ha hb
  exact ((SheetPartition.mem_block_iff _ _ _).mp ha).symm.trans
    ((SheetPartition.mem_block_iff _ _ _).mp hb)

theorem beta_rel_of_mem_newBeta {a b : Fin degree} (ha : a ∈ base.newBetaBlock)
    (hb : b ∈ base.newBetaBlock) :
    (base.gaugedData.edgePartition (directionEdge star base.betaLabel)).Rel a b := by
  rw [← base.gaugedBeta_block_beta] at ha hb
  exact ((SheetPartition.mem_block_iff _ _ _).mp ha).symm.trans
    ((SheetPartition.mem_block_iff _ _ _).mp hb)

theorem target_cases_of_rightAssignment_true {edge : target.edges}
    (hAt : edge ∈ GluingDatum.incidentEdges wall)
    (hSide : base.rightAssignment edge = true) :
    edge = Prescribed.doubledEdge base.source ∨
      edge = directionEdge star base.betaLabel := by
  classical
  rw [base.incidentEdges_eq_triple, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_singleton] at hAt
  rcases hAt with rfl | hAt | hAt
  · rw [base.rightAssignment_alpha] at hSide
    exact absurd hSide (by simp)
  · exact Or.inl hAt
  · exact Or.inr hAt

/-! ### Survival of retained occurrences -/

theorem retained_survives (hValid : data.Valid) {old : base.gaugedData.SourceEdge}
    (h : ¬ IsDangling base.gaugedData old) :
    ¬ IsDangling (validCandidate base hValid).datum
      ((validCandidate base hValid).oldSourceEdge old) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ (base.gaugedData_valid hValid).1 _ h

theorem retained_isDangling_iff (hValid : data.Valid) (old : base.gaugedData.SourceEdge) :
    IsDangling (validCandidate base hValid).datum
        ((validCandidate base hValid).oldSourceEdge old) ↔
      IsDangling base.gaugedData old :=
  ResolutionPruning.isDangling_oldSourceEdge_iff _ (base.gaugedData_valid hValid)
    (candidate_sourceGenus base hValid) old

/-! ### The block calculus of the three endpoint partitions -/

theorem left_rel_hub_iff {sheet : Fin degree} :
    base.leftPartition.Rel base.hubSheet sheet ↔ sheet ∈ base.alphaBlock := by
  rw [← base.leftPartition_block_hub, SheetPartition.mem_block_iff]

theorem newEdge_rel_delta_iff {sheet : Fin degree} :
    base.newEdgePartition.Rel base.deltaRepr sheet ↔ sheet ∈ base.newDeltaBlock := by
  rw [← base.newEdgePartition_block_delta, SheetPartition.mem_block_iff]

theorem newEdge_rel_hub_iff {sheet : Fin degree} :
    base.newEdgePartition.Rel base.hubSheet sheet ↔
      sheet ∈ base.alphaBlock \ base.newDeltaBlock := by
  rw [← base.newEdgePartition_block_hub, SheetPartition.mem_block_iff]

theorem hubSheet_wall' : (data.vertexPartition wall).Rel anchor.1 base.hubSheet :=
  base.hubSheet_wall

theorem wall_rel_of_mem_wholeBlock {sheet : Fin degree}
    (hSheet : sheet ∈ base.wholeBlock) :
    (data.vertexPartition wall).Rel anchor.1 sheet :=
  ((data.vertexPartition wall).mem_block_iff _ _).mp hSheet

theorem mem_wholeBlock_of_wall_rel {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    sheet ∈ base.wholeBlock :=
  ((data.vertexPartition wall).mem_block_iff _ _).mpr hSheet

/-- The canonical sheet of a new occurrence carries the same occurrence. -/
theorem newSourceEdge_sheet_eq_self (hValid : data.Valid) (y : Fin degree) :
    (validCandidate base hValid).newSourceEdge
        (((validCandidate base hValid).newSourceEdge y).1.2) =
      (validCandidate base hValid).newSourceEdge y :=
  (newSourceEdge_eq_of_rel base hValid
    ((LocalResolution.paste (base.gaugedData.vertexPartition wall)
      (validCandidate base hValid).resolution
      (validCandidate base hValid).contracts).newEdge.rel_repr_right y)).symm

theorem newEdge_refines_wall (hValid : data.Valid) :
    (LocalResolution.paste (base.gaugedData.vertexPartition wall)
      (validCandidate base hValid).resolution
      (validCandidate base hValid).contracts).newEdge.Refines
        (base.gaugedData.vertexPartition wall) :=
  (LocalResolution.paste (base.gaugedData.vertexPartition wall)
    (validCandidate base hValid).resolution
    (validCandidate base hValid).contracts).edge_refines_left.trans
      (LocalResolution.pasteLeft_refines (base.gaugedData.vertexPartition wall)
        (validCandidate base hValid).resolution (validCandidate base hValid).contracts)

theorem wall_rel_newSourceEdge_sheet (hValid : data.Valid) (y : Fin degree) :
    (data.vertexPartition wall).Rel y
      (((validCandidate base hValid).newSourceEdge y).1.2) := by
  rw [← gauged_rel_iff base]
  exact (newEdge_refines_wall base hValid).rel
    ((LocalResolution.paste (base.gaugedData.vertexPartition wall)
      (validCandidate base hValid).resolution
      (validCandidate base hValid).contracts).newEdge.rel_repr_right y)

theorem newSourceEdge_eq_of_newEdgePartition_rel (hValid : data.Valid)
    {a b : Fin degree} (hA : (data.vertexPartition wall).Rel anchor.1 a)
    (hRel : base.newEdgePartition.Rel a b) :
    (validCandidate base hValid).newSourceEdge a =
      (validCandidate base hValid).newSourceEdge b :=
  newSourceEdge_eq_of_rel base hValid
    ((newEdge_rel_iff_newEdgePartition base hValid hA).mpr hRel)

theorem newSourceEdge_ne_oldSourceEdge (hValid : data.Valid) (sheet : Fin degree)
    (old : base.gaugedData.SourceEdge) :
    (validCandidate base hValid).newSourceEdge sheet ≠
      (validCandidate base hValid).oldSourceEdge old := by
  intro hEq
  have h := congrArg
    (fun edge : (validCandidate base hValid).datum.SourceEdge ↦ edge.1.1) hEq
  have hNone := (occurrenceEquiv target wall (validCandidate base hValid).right).injective h
  cases hNone

/-- Inside `A_u` a new occurrence is the bridge `e_1` or the second occurrence
`e'` above `t_1`. -/
theorem newSourceEdge_eq_bridge_or_delta (hValid : data.Valid) {y : Fin degree}
    (hMem : (((validCandidate base hValid).newSourceEdge y).1.2) ∈ base.alphaBlock) :
    (validCandidate base hValid).newSourceEdge y =
        bridgeEdge base hValid base.hubSheet ∨
      (validCandidate base hValid).newSourceEdge y =
        bridgeEdge base hValid base.deltaRepr := by
  classical
  set z := ((validCandidate base hValid).newSourceEdge y).1.2 with hz
  have hSelf : (validCandidate base hValid).newSourceEdge z =
      (validCandidate base hValid).newSourceEdge y :=
    newSourceEdge_sheet_eq_self base hValid y
  by_cases hDelta : z ∈ base.newDeltaBlock
  · right
    rw [← hSelf]
    exact (newSourceEdge_eq_of_newEdgePartition_rel base hValid base.deltaRepr_wall
      (newEdge_rel_delta_iff base |>.mpr hDelta)).symm
  · left
    rw [← hSelf]
    exact (newSourceEdge_eq_of_newEdgePartition_rel base hValid base.hubSheet_wall
      (newEdge_rel_hub_iff base |>.mpr (Finset.mem_sdiff.mpr ⟨hMem, hDelta⟩))).symm

/-- Over a sheet of the anchor block outside `A_u` the divalent end carries at
most its own new occurrence. -/
theorem nonDanglingIncident_left_singleton_subset (hValid : data.Valid)
    {z : Fin degree} (hWall : (data.vertexPartition wall).Rel anchor.1 z)
    (hNot : z ∉ base.alphaBlock) :
    nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid false z) ⊆
      {(validCandidate base hValid).newSourceEdge z} := by
  classical
  intro f hf
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hf
  have hRel := endpointPartition_rel_of_incident base hValid false hWall hIncident
  have hSheet : f.1.2 = z := by
    have hMem : f.1.2 ∈ base.leftPartition.block z :=
      (base.leftPartition.mem_block_iff z f.1.2).mpr hRel
    rw [base.leftPartition_block_singleton hWall hNot] at hMem
    simpa using hMem
  rcases ResolutionPruning.sourceEdge_cases (validCandidate base hValid) f with
    ⟨old, rfl⟩ | ⟨y, rfl⟩
  · exfalso
    obtain ⟨_, hSide⟩ := right_eq_of_incident_old base hValid false hIncident
    have hTarget : old.1.1 = directionEdge star base.alphaLabel :=
      (base.rightAssignment_eq_false_iff old.1.1).mp hSide
    have hOldSheet : old.1.2 = z := hSheet
    have hOldEq : old = base.gaugedData.sourceEdge
        (directionEdge star base.alphaLabel) z := by
      refine oldSourceEdge_eq base hTarget ?_
      rw [hOldSheet]
      exact rfl
    refine hSurvives ((retained_isDangling_iff base hValid old).mpr ?_)
    rw [hOldEq]
    exact gauged_alpha_isDangling_of_not_mem base hValid hWall hNot
  · have hEq : (validCandidate base hValid).newSourceEdge y =
        (validCandidate base hValid).newSourceEdge z := by
      rw [← newSourceEdge_sheet_eq_self base hValid y, hSheet]
    rw [hEq]
    exact Finset.mem_singleton_self _

/-- **A new occurrence over a sheet of `A` outside `A_u` is dangling.**  Its
divalent end sees nothing else, and surviving valency one is impossible. -/
theorem newSourceEdge_isDangling_of_not_mem_alpha (hValid : data.Valid)
    {z : Fin degree} (hWall : (data.vertexPartition wall).Rel anchor.1 z)
    (hNot : z ∉ base.alphaBlock) :
    IsDangling (validCandidate base hValid).datum
      ((validCandidate base hValid).newSourceEdge z) := by
  classical
  by_contra hSurvives
  have hIncident := bridgeEdge_incident base hValid false z
  have hCard := Finset.card_le_card
    (nonDanglingIncident_left_singleton_subset base hValid hWall hNot)
  rw [card_nonDanglingIncident, Finset.card_singleton] at hCard
  have hNe := NonDanglingValency.nonDanglingValency_ne_one
    (validCandidate base hValid).datum (validCandidate_datum_valid base hValid).1
    (endpointVertex base hValid false z)
  have hPos := ClassInjectivity.nonDanglingValency_ne_zero_of_incident
    (validCandidate base hValid).datum hSurvives hIncident
  omega

/-! ### The four named occurrences of the gauged anchor -/

/-- `e_alpha`, above the simple direction carrying the divalent point. -/
noncomputable def alphaOccurrence : base.gaugedData.SourceEdge :=
  base.gaugedData.sourceEdge (directionEdge star base.alphaLabel) base.hubSheet

/-- `e_beta`, above the other simple direction. -/
noncomputable def betaOccurrence : base.gaugedData.SourceEdge :=
  base.gaugedData.sourceEdge (directionEdge star base.betaLabel) base.betaRepr

/-- `e_delta`, the doubled survivor carried by the divalent vertex `A'`. -/
noncomputable def deltaOccurrence : base.gaugedData.SourceEdge :=
  base.gaugedData.sourceEdge (Prescribed.doubledEdge base.source) base.deltaRepr

/-- `e_gamma`, the other doubled survivor. -/
noncomputable def gammaOccurrence : base.gaugedData.SourceEdge :=
  base.gaugedData.sourceEdge (Prescribed.doubledEdge base.source) base.gammaRepr

theorem alphaOccurrence_survives (hValid : data.Valid) :
    ¬ IsDangling base.gaugedData (alphaOccurrence base) :=
  gauged_alpha_survives base hValid base.hubSheet_mem_alpha

theorem betaOccurrence_survives (hValid : data.Valid) :
    ¬ IsDangling base.gaugedData (betaOccurrence base) :=
  gauged_beta_survives base hValid base.betaRepr_mem

theorem deltaOccurrence_survives (hValid : data.Valid) :
    ¬ IsDangling base.gaugedData (deltaOccurrence base) :=
  gauged_doubled_survives base hValid (Or.inl base.deltaRepr_mem)

theorem gammaOccurrence_survives (hValid : data.Valid) :
    ¬ IsDangling base.gaugedData (gammaOccurrence base) :=
  gauged_doubled_survives base hValid (Or.inr base.gammaRepr_mem)

theorem betaRepr_mem_sdiff : base.betaRepr ∈ base.wholeBlock \ base.newDeltaBlock :=
  base.newBetaBlock_subset_sdiff base.betaRepr_mem

theorem gammaRepr_mem_sdiff : base.gammaRepr ∈ base.wholeBlock \ base.newDeltaBlock :=
  Finset.mem_sdiff.mpr ⟨base.newGammaBlock_subset_whole base.gammaRepr_mem,
    base.newGammaBlock_not_mem_delta base.gammaRepr_mem⟩

theorem endpointVertex_true_hub_eq_betaRepr (hValid : data.Valid) :
    endpointVertex base hValid true base.hubSheet =
      endpointVertex base hValid true base.betaRepr :=
  endpointVertex_eq base hValid true base.hubSheet_wall
    (base.right_rel_hub_of_mem (betaRepr_mem_sdiff base))

theorem endpointVertex_true_hub_eq_gammaRepr (hValid : data.Valid) :
    endpointVertex base hValid true base.hubSheet =
      endpointVertex base hValid true base.gammaRepr :=
  endpointVertex_eq base hValid true base.hubSheet_wall
    (base.right_rel_hub_of_mem (gammaRepr_mem_sdiff base))

theorem alphaOccurrence_incident (hValid : data.Valid) :
    Incident (validCandidate base hValid).datum
      ((validCandidate base hValid).oldSourceEdge (alphaOccurrence base))
      (endpointVertex base hValid false base.hubSheet) :=
  retainedEdge_incident base hValid _
    (directionEdge_mem_incidentEdges star base.alphaLabel) false
    base.rightAssignment_alpha base.hubSheet

theorem deltaOccurrence_incident (hValid : data.Valid) :
    Incident (validCandidate base hValid).datum
      ((validCandidate base hValid).oldSourceEdge (deltaOccurrence base))
      (endpointVertex base hValid true base.deltaRepr) :=
  retainedEdge_incident base hValid _
    (Prescribed.doubledEdge_mem_incidentEdges base.source) true
    (base.rightAssignment_of_ne (Ne.symm base.alphaEdge_ne_doubledEdge)) base.deltaRepr

theorem betaOccurrence_incident (hValid : data.Valid) :
    Incident (validCandidate base hValid).datum
      ((validCandidate base hValid).oldSourceEdge (betaOccurrence base))
      (endpointVertex base hValid true base.hubSheet) := by
  rw [endpointVertex_true_hub_eq_betaRepr base hValid]
  exact retainedEdge_incident base hValid _
    (directionEdge_mem_incidentEdges star base.betaLabel) true
    (base.rightAssignment_of_ne (Ne.symm base.alphaEdge_ne_betaEdge)) base.betaRepr

theorem gammaOccurrence_incident (hValid : data.Valid) :
    Incident (validCandidate base hValid).datum
      ((validCandidate base hValid).oldSourceEdge (gammaOccurrence base))
      (endpointVertex base hValid true base.hubSheet) := by
  rw [endpointVertex_true_hub_eq_gammaRepr base hValid]
  exact retainedEdge_incident base hValid _
    (Prescribed.doubledEdge_mem_incidentEdges base.source) true
    (base.rightAssignment_of_ne (Ne.symm base.alphaEdge_ne_doubledEdge)) base.gammaRepr

/-! ### The exact surviving star at each of the three new vertices -/

/-- **`A_u`**: the divalent point sees `e_alpha`, the bridge `e_1` and the
second occurrence `e'` above `t_1`. -/
theorem nonDanglingIncident_hubLeft_subset (hValid : data.Valid) :
    nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid false base.hubSheet) ⊆
      {bridgeEdge base hValid base.hubSheet, bridgeEdge base hValid base.deltaRepr,
        (validCandidate base hValid).oldSourceEdge (alphaOccurrence base)} := by
  classical
  intro e he
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp he
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hRel := endpointPartition_rel_of_incident base hValid false base.hubSheet_wall
    hIncident
  rcases ResolutionPruning.sourceEdge_cases (validCandidate base hValid) e with
    ⟨old, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨_, hSide⟩ := right_eq_of_incident_old base hValid false hIncident
    have hTarget : old.1.1 = directionEdge star base.alphaLabel :=
      (base.rightAssignment_eq_false_iff old.1.1).mp hSide
    have hMem : old.1.2 ∈ base.alphaBlock := (left_rel_hub_iff base).mp hRel
    refine Or.inr (Or.inr (congrArg (validCandidate base hValid).oldSourceEdge ?_))
    exact oldSourceEdge_eq base hTarget
      (alpha_rel_of_mem base base.hubSheet_mem_alpha hMem)
  · rcases newSourceEdge_eq_bridge_or_delta base hValid
      ((left_rel_hub_iff base).mp hRel) with hEq | hEq
    · exact Or.inl hEq
    · exact Or.inr (Or.inl hEq)

/-- **`A'`**: the divalent vertex over `v` sees only `e'` and `e_delta`. -/
theorem nonDanglingIncident_deltaRight_subset (hValid : data.Valid) :
    nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid true base.deltaRepr) ⊆
      {bridgeEdge base hValid base.deltaRepr,
        (validCandidate base hValid).oldSourceEdge (deltaOccurrence base)} := by
  classical
  intro e he
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp he
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hRel := endpointPartition_rel_of_incident base hValid true base.deltaRepr_wall
    hIncident
  rcases ResolutionPruning.sourceEdge_cases (validCandidate base hValid) e with
    ⟨old, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old base hValid true hIncident
    have hMem : old.1.2 ∈ base.newDeltaBlock :=
      base.mem_newDeltaBlock_of_right_rel hRel
    rcases target_cases_of_rightAssignment_true base hAt hSide with hTarget | hTarget
    · refine Or.inr (congrArg (validCandidate base hValid).oldSourceEdge ?_)
      exact oldSourceEdge_eq base hTarget
        (doubled_rel_of_mem_newDelta base base.deltaRepr_mem hMem)
    · exfalso
      have hNotBeta : old.1.2 ∉ base.newBetaBlock := by
        intro hBeta
        exact (Finset.mem_sdiff.mp (base.newBetaBlock_subset_sdiff hBeta)).2 hMem
      have hWallOld : (data.vertexPartition wall).Rel anchor.1 old.1.2 :=
        wall_rel_of_mem_wholeBlock base (base.newDeltaBlock_subset_whole hMem)
      refine hSurvives ((retained_isDangling_iff base hValid old).mpr ?_)
      rw [oldSourceEdge_eq base hTarget
        (rfl : (base.gaugedData.edgePartition
          (directionEdge star base.betaLabel)).Rel old.1.2 old.1.2)]
      exact gauged_beta_isDangling_of_not_mem base hValid hWallOld hNotBeta
  · left
    have hMem : (((validCandidate base hValid).newSourceEdge y).1.2) ∈
        base.newDeltaBlock := base.mem_newDeltaBlock_of_right_rel hRel
    rw [← newSourceEdge_sheet_eq_self base hValid y]
    exact (newSourceEdge_eq_of_newEdgePartition_rel base hValid base.deltaRepr_wall
      ((newEdge_rel_delta_iff base).mpr hMem)).symm

/-- **`A_v`**: the trivalent vertex over `v` sees the bridge, `e_beta` and
`e_gamma`. -/
theorem nonDanglingIncident_hubRight_subset (hValid : data.Valid) :
    nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid true base.hubSheet) ⊆
      {bridgeEdge base hValid base.hubSheet,
        (validCandidate base hValid).oldSourceEdge (betaOccurrence base),
        (validCandidate base hValid).oldSourceEdge (gammaOccurrence base)} := by
  classical
  intro e he
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp he
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hRel := endpointPartition_rel_of_incident base hValid true base.hubSheet_wall
    hIncident
  rcases ResolutionPruning.sourceEdge_cases (validCandidate base hValid) e with
    ⟨old, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old base hValid true hIncident
    have hMem : old.1.2 ∈ base.wholeBlock \ base.newDeltaBlock :=
      base.mem_sdiff_of_right_hub_rel hRel
    have hWallOld : (data.vertexPartition wall).Rel anchor.1 old.1.2 :=
      wall_rel_of_mem_wholeBlock base (Finset.mem_sdiff.mp hMem).1
    have hOldSurv : ¬ IsDangling base.gaugedData old := fun h ↦
      hSurvives ((retained_isDangling_iff base hValid old).mpr h)
    rcases target_cases_of_rightAssignment_true base hAt hSide with hTarget | hTarget
    · refine Or.inr (Or.inr (congrArg (validCandidate base hValid).oldSourceEdge ?_))
      have hGamma : old.1.2 ∈ base.newGammaBlock := by
        by_contra hNot
        refine hOldSurv ?_
        rw [oldSourceEdge_eq base hTarget
          (rfl : (base.gaugedData.edgePartition
            (Prescribed.doubledEdge base.source)).Rel old.1.2 old.1.2)]
        exact gauged_doubled_isDangling_of_not_mem base hValid hWallOld
          (Finset.mem_sdiff.mp hMem).2 hNot
      exact oldSourceEdge_eq base hTarget
        (doubled_rel_of_mem_newGamma base base.gammaRepr_mem hGamma)
    · refine Or.inr (Or.inl (congrArg (validCandidate base hValid).oldSourceEdge ?_))
      have hBeta : old.1.2 ∈ base.newBetaBlock := by
        by_contra hNot
        refine hOldSurv ?_
        rw [oldSourceEdge_eq base hTarget
          (rfl : (base.gaugedData.edgePartition
            (directionEdge star base.betaLabel)).Rel old.1.2 old.1.2)]
        exact gauged_beta_isDangling_of_not_mem base hValid hWallOld hNot
      exact oldSourceEdge_eq base hTarget
        (beta_rel_of_mem_newBeta base base.betaRepr_mem hBeta)
  · left
    have hMem : (((validCandidate base hValid).newSourceEdge y).1.2) ∈
        base.wholeBlock \ base.newDeltaBlock := base.mem_sdiff_of_right_hub_rel hRel
    by_cases hAlpha : (((validCandidate base hValid).newSourceEdge y).1.2) ∈
        base.alphaBlock
    · rw [← newSourceEdge_sheet_eq_self base hValid y]
      exact (newSourceEdge_eq_of_newEdgePartition_rel base hValid base.hubSheet_wall
        ((newEdge_rel_hub_iff base).mpr
          (Finset.mem_sdiff.mpr ⟨hAlpha, (Finset.mem_sdiff.mp hMem).2⟩))).symm
    · exfalso
      refine hSurvives ?_
      rw [← newSourceEdge_sheet_eq_self base hValid y]
      exact newSourceEdge_isDangling_of_not_mem_alpha base hValid
        (wall_rel_of_mem_wholeBlock base (Finset.mem_sdiff.mp hMem).1) hAlpha

theorem newSourceEdge_eq_iff_anchor (hValid : data.Valid) {a b : Fin degree}
    (hA : (data.vertexPartition wall).Rel anchor.1 a) :
    (validCandidate base hValid).newSourceEdge a =
        (validCandidate base hValid).newSourceEdge b ↔
      base.newEdgePartition.Rel a b := by
  constructor
  · intro hEq
    refine (newEdge_rel_iff_newEdgePartition base hValid hA).mp ?_
    exact congrArg
      (fun e : (validCandidate base hValid).datum.SourceEdge ↦ e.1.2) hEq
  · exact newSourceEdge_eq_of_newEdgePartition_rel base hValid hA

theorem endpointVertex_false_hub_eq_deltaRepr (hValid : data.Valid) :
    endpointVertex base hValid false base.hubSheet =
      endpointVertex base hValid false base.deltaRepr :=
  endpointVertex_eq base hValid false base.hubSheet_wall
    ((left_rel_hub_iff base).mpr base.deltaRepr_mem_alpha)

theorem nonDanglingValency_hubLeft_ne_zero (hValid : data.Valid) :
    nonDanglingValency (validCandidate base hValid).datum
      (endpointVertex base hValid false base.hubSheet) ≠ 0 :=
  ClassInjectivity.nonDanglingValency_ne_zero_of_incident _
    (retained_survives base hValid (alphaOccurrence_survives base hValid))
    (alphaOccurrence_incident base hValid)

theorem nonDanglingValency_deltaRight_ne_zero (hValid : data.Valid) :
    nonDanglingValency (validCandidate base hValid).datum
      (endpointVertex base hValid true base.deltaRepr) ≠ 0 :=
  ClassInjectivity.nonDanglingValency_ne_zero_of_incident _
    (retained_survives base hValid (deltaOccurrence_survives base hValid))
    (deltaOccurrence_incident base hValid)

theorem nonDanglingValency_hubRight_ne_zero (hValid : data.Valid) :
    nonDanglingValency (validCandidate base hValid).datum
      (endpointVertex base hValid true base.hubSheet) ≠ 0 :=
  ClassInjectivity.nonDanglingValency_ne_zero_of_incident _
    (retained_survives base hValid (betaOccurrence_survives base hValid))
    (betaOccurrence_incident base hValid)

private theorem newSourceEdge_survives_of_ends (hValid : data.Valid) (sheet : Fin degree)
    (hFalse : nonDanglingValency (validCandidate base hValid).datum
      (endpointVertex base hValid false sheet) ≠ 0)
    (hTrue : nonDanglingValency (validCandidate base hValid).datum
      (endpointVertex base hValid true sheet) ≠ 0) :
    ¬ IsDangling (validCandidate base hValid).datum (bridgeEdge base hValid sheet) := by
  have hEnds := sourceEnds_bridgeEdge base hValid sheet
  intro hDangling
  rcases hDangling with hSide | hSide
  · obtain ⟨cut⟩ := hSide
    apply hFalse
    have hFst := congrArg Prod.fst hEnds
    have hZero := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side
      _ cut cut.left_mem
    rwa [hFst] at hZero
  · obtain ⟨cut⟩ := hSide
    apply hTrue
    have hSnd := congrArg Prod.snd hEnds
    have hZero := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side
      _ cut cut.left_mem
    rwa [hSnd] at hZero

/-- **The bridge `e_1` survives.** -/
theorem bridgeEdge_hub_survives (hValid : data.Valid) :
    ¬ IsDangling (validCandidate base hValid).datum
      (bridgeEdge base hValid base.hubSheet) :=
  newSourceEdge_survives_of_ends base hValid base.hubSheet
    (nonDanglingValency_hubLeft_ne_zero base hValid)
    (nonDanglingValency_hubRight_ne_zero base hValid)

/-- **The second occurrence `e'` above `t_1` survives.** -/
theorem bridgeEdge_delta_survives (hValid : data.Valid) :
    ¬ IsDangling (validCandidate base hValid).datum
      (bridgeEdge base hValid base.deltaRepr) := by
  refine newSourceEdge_survives_of_ends base hValid base.deltaRepr ?_
    (nonDanglingValency_deltaRight_ne_zero base hValid)
  rw [← endpointVertex_false_hub_eq_deltaRepr base hValid]
  exact nonDanglingValency_hubLeft_ne_zero base hValid

theorem bridge_hub_ne_bridge_delta (hValid : data.Valid) :
    bridgeEdge base hValid base.hubSheet ≠ bridgeEdge base hValid base.deltaRepr := by
  intro hEq
  have hRel := (newSourceEdge_eq_iff_anchor base hValid base.hubSheet_wall).mp hEq
  exact (Finset.mem_sdiff.mp ((newEdge_rel_hub_iff base).mp hRel)).2 base.deltaRepr_mem

theorem betaOccurrence_ne_gammaOccurrence :
    betaOccurrence base ≠ gammaOccurrence base := by
  intro hEq
  exact base.betaEdge_ne_doubledEdge
    (congrArg (fun e : base.gaugedData.SourceEdge ↦ e.1.1) hEq)

theorem hubLeft_subset_nonDanglingIncident (hValid : data.Valid) :
    ({bridgeEdge base hValid base.hubSheet, bridgeEdge base hValid base.deltaRepr,
        (validCandidate base hValid).oldSourceEdge (alphaOccurrence base)} :
          Finset (validCandidate base hValid).datum.SourceEdge) ⊆
      nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid false base.hubSheet) := by
  classical
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨bridgeEdge_hub_survives base hValid,
        bridgeEdge_incident base hValid false base.hubSheet⟩
  · refine (mem_nonDanglingIncident _ _ _).mpr
      ⟨bridgeEdge_delta_survives base hValid, ?_⟩
    rw [endpointVertex_false_hub_eq_deltaRepr base hValid]
    exact bridgeEdge_incident base hValid false base.deltaRepr
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨retained_survives base hValid (alphaOccurrence_survives base hValid),
        alphaOccurrence_incident base hValid⟩

theorem deltaRight_subset_nonDanglingIncident (hValid : data.Valid) :
    ({bridgeEdge base hValid base.deltaRepr,
        (validCandidate base hValid).oldSourceEdge (deltaOccurrence base)} :
          Finset (validCandidate base hValid).datum.SourceEdge) ⊆
      nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid true base.deltaRepr) := by
  classical
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨bridgeEdge_delta_survives base hValid,
        bridgeEdge_incident base hValid true base.deltaRepr⟩
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨retained_survives base hValid (deltaOccurrence_survives base hValid),
        deltaOccurrence_incident base hValid⟩

theorem hubRight_subset_nonDanglingIncident (hValid : data.Valid) :
    ({bridgeEdge base hValid base.hubSheet,
        (validCandidate base hValid).oldSourceEdge (betaOccurrence base),
        (validCandidate base hValid).oldSourceEdge (gammaOccurrence base)} :
          Finset (validCandidate base hValid).datum.SourceEdge) ⊆
      nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid true base.hubSheet) := by
  classical
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨bridgeEdge_hub_survives base hValid,
        bridgeEdge_incident base hValid true base.hubSheet⟩
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨retained_survives base hValid (betaOccurrence_survives base hValid),
        betaOccurrence_incident base hValid⟩
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨retained_survives base hValid (gammaOccurrence_survives base hValid),
        gammaOccurrence_incident base hValid⟩

/-- **The surviving star at `A_u`**: `{e_alpha, e_1, e'}`. -/
theorem nonDanglingIncident_hubLeft (hValid : data.Valid) :
    nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid false base.hubSheet) =
      {bridgeEdge base hValid base.hubSheet, bridgeEdge base hValid base.deltaRepr,
        (validCandidate base hValid).oldSourceEdge (alphaOccurrence base)} :=
  Finset.Subset.antisymm (nonDanglingIncident_hubLeft_subset base hValid)
    (hubLeft_subset_nonDanglingIncident base hValid)

/-- **The surviving star at `A'`**: `{e', e_delta}`. -/
theorem nonDanglingIncident_deltaRight (hValid : data.Valid) :
    nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid true base.deltaRepr) =
      {bridgeEdge base hValid base.deltaRepr,
        (validCandidate base hValid).oldSourceEdge (deltaOccurrence base)} :=
  Finset.Subset.antisymm (nonDanglingIncident_deltaRight_subset base hValid)
    (deltaRight_subset_nonDanglingIncident base hValid)

/-- **The surviving star at `A_v`**: `{e_1, e_beta, e_gamma}`. -/
theorem nonDanglingIncident_hubRight (hValid : data.Valid) :
    nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid true base.hubSheet) =
      {bridgeEdge base hValid base.hubSheet,
        (validCandidate base hValid).oldSourceEdge (betaOccurrence base),
        (validCandidate base hValid).oldSourceEdge (gammaOccurrence base)} :=
  Finset.Subset.antisymm (nonDanglingIncident_hubRight_subset base hValid)
    (hubRight_subset_nonDanglingIncident base hValid)

/-- **`A_u` is trivalent.** -/
theorem nonDanglingValency_hubLeft (hValid : data.Valid) :
    nonDanglingValency (validCandidate base hValid).datum
      (endpointVertex base hValid false base.hubSheet) = 3 := by
  classical
  rw [← card_nonDanglingIncident, nonDanglingIncident_hubLeft base hValid]
  refine Finset.card_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
  · exact bridge_hub_ne_bridge_delta base hValid
  · exact newSourceEdge_ne_oldSourceEdge base hValid _ _
  · exact newSourceEdge_ne_oldSourceEdge base hValid _ _

/-- **`A'` is divalent**: `e'` and `e_delta` are consecutive there. -/
theorem nonDanglingValency_deltaRight (hValid : data.Valid) :
    nonDanglingValency (validCandidate base hValid).datum
      (endpointVertex base hValid true base.deltaRepr) = 2 := by
  classical
  rw [← card_nonDanglingIncident, nonDanglingIncident_deltaRight base hValid,
    Finset.card_insert_of_notMem (by
      rw [Finset.mem_singleton]
      exact newSourceEdge_ne_oldSourceEdge base hValid _ _), Finset.card_singleton]

/-- **`A_v` is trivalent.** -/
theorem nonDanglingValency_hubRight (hValid : data.Valid) :
    nonDanglingValency (validCandidate base hValid).datum
      (endpointVertex base hValid true base.hubSheet) = 3 := by
  classical
  rw [← card_nonDanglingIncident, nonDanglingIncident_hubRight base hValid]
  refine Finset.card_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
  · exact newSourceEdge_ne_oldSourceEdge base hValid _ _
  · exact newSourceEdge_ne_oldSourceEdge base hValid _ _
  · exact fun hEq ↦ betaOccurrence_ne_gammaOccurrence base
      (ResolutionCut.oldSourceEdge_injective (validCandidate base hValid) hEq)

/-! ## 4.  The new stable row is the bridge alone, and `e'` joins `e_delta` -/

/-- **The bridge is alone in its stable class**: both of its ends are
trivalent, so `e_1` really is the one new row. -/
theorem bridgeEdge_isolated (hValid : data.Valid)
    (other : NonDanglingEdge (validCandidate base hValid).datum)
    (hPath : other.stablePath =
      NonDanglingEdge.stablePath
        ⟨bridgeEdge base hValid base.hubSheet, bridgeEdge_hub_survives base hValid⟩) :
    other.1 = bridgeEdge base hValid base.hubSheet := by
  have hEnds := sourceEnds_bridgeEdge base hValid base.hubSheet
  refine congrArg Subtype.val
    (NonTrivalentUniqueFourValent.eq_of_stablePath_eq_of_ends_ne_two _ ?_ ?_
      other hPath)
  · rw [congrArg Prod.fst hEnds, nonDanglingValency_hubLeft base hValid]
    omega
  · rw [congrArg Prod.snd hEnds, nonDanglingValency_hubRight base hValid]
    omega

/-- **`e'` lies on the retained row of `e_delta`.**  The stable edge `h_delta`
runs `A_u -> A' -> e_delta`: at the divalent vertex `A'` the second occurrence
above `t_1` and the retained `e_delta` are consecutive. -/
theorem newSourceEdge_stablePath_eq_retained (hValid : data.Valid) :
    NonDanglingEdge.stablePath
        (⟨bridgeEdge base hValid base.deltaRepr, bridgeEdge_delta_survives base hValid⟩ :
          NonDanglingEdge (validCandidate base hValid).datum) =
      (ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
        (base.gaugedData_valid hValid).1
        ⟨deltaOccurrence base, deltaOccurrence_survives base hValid⟩).stablePath := by
  refine stablePath_eq_of_consecutive
    ⟨?_, endpointVertex base hValid true base.deltaRepr, ?_, ?_, ?_⟩
  · intro hEq
    exact newSourceEdge_ne_oldSourceEdge base hValid base.deltaRepr
      (deltaOccurrence base) (congrArg Subtype.val hEq)
  · exact bridgeEdge_incident base hValid true base.deltaRepr
  · exact deltaOccurrence_incident base hValid
  · exact nonDanglingValency_deltaRight base hValid

/-! ## 5.  The ordinary-block census

At a wall block other than the anchor the candidate installs
`ordinaryResolution base`, the fine resolution of the wall partition along the
**alpha** direction.  The block is split on the `u` side only, exactly as in
`NonTrivalentValencyThreeDescent` with `alphaLabel` in place of the doubled
direction. -/

@[simp] theorem ordinaryResolution_left :
    (ordinaryResolution base).left =
      base.gaugedData.edgePartition (directionEdge star base.alphaLabel) := rfl

@[simp] theorem ordinaryResolution_right :
    (ordinaryResolution base).right = base.gaugedData.vertexPartition wall := rfl

@[simp] theorem ordinaryResolution_newEdge :
    (ordinaryResolution base).newEdge =
      base.gaugedData.edgePartition (directionEdge star base.alphaLabel) := rfl

theorem alphaEdge_refines :
    (base.gaugedData.edgePartition (directionEdge star base.alphaLabel)).Refines
      (base.gaugedData.vertexPartition wall) :=
  edgePartition_refines_of_mem_incidentEdges base.gaugedData wall _
    (directionEdge_mem_incidentEdges star base.alphaLabel)

/-- The candidate's endpoint partition over an ordinary wall block. -/
noncomputable def ordinaryPartition (sideValue : Bool) : SheetPartition degree :=
  if sideValue then base.gaugedData.vertexPartition wall
  else base.gaugedData.edgePartition (directionEdge star base.alphaLabel)

@[simp] theorem ordinaryPartition_false :
    ordinaryPartition base false =
      base.gaugedData.edgePartition (directionEdge star base.alphaLabel) := rfl

@[simp] theorem ordinaryPartition_true :
    ordinaryPartition base true = base.gaugedData.vertexPartition wall := rfl

private theorem not_gauged_rel_repr {a : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    ¬ (base.gaugedData.vertexPartition wall).Rel anchor.1
      ((base.gaugedData.vertexPartition wall).repr a) := by
  rw [base.gaugedData_vertexPartition_wall]
  exact fun h ↦ hA (h.trans ((data.vertexPartition wall).rel_repr_right a).symm)

theorem candidate_vertexPartition_rel_ordinary (hValid : data.Valid) (sideValue : Bool)
    {a b : Fin degree} (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    ((validCandidate base hValid).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall)).Rel a b ↔
      (ordinaryPartition base sideValue).Rel a b := by
  have hOrd := candidate_resolution_of_not_wall_rel base hValid
    ((base.gaugedData.vertexPartition wall).repr a) (not_gauged_rel_repr base hA)
  cases sideValue
  · show ((validCandidate base hValid).datum.vertexPartition
      (oldVertex target wall)).Rel a b ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
    refine Iff.trans (SheetPartition.paste_rel_iff (base.gaugedData.vertexPartition wall)
      (fun blk ↦ ((validCandidate base hValid).resolution blk).left)
      (fun blk ↦ ((validCandidate base hValid).contracts blk).left_refines) a b) ?_
    rw [hOrd]
    rfl
  · show ((validCandidate base hValid).datum.vertexPartition
      (freshVertex target)).Rel a b ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]
    refine Iff.trans (SheetPartition.paste_rel_iff (base.gaugedData.vertexPartition wall)
      (fun blk ↦ ((validCandidate base hValid).resolution blk).right)
      (fun blk ↦ ((validCandidate base hValid).contracts blk).right_refines) a b) ?_
    rw [hOrd]
    rfl

theorem newEdge_rel_ordinary (hValid : data.Valid) {a b : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    (LocalResolution.paste (base.gaugedData.vertexPartition wall)
        (validCandidate base hValid).resolution
        (validCandidate base hValid).contracts).newEdge.Rel a b ↔
      (base.gaugedData.edgePartition (directionEdge star base.alphaLabel)).Rel a b := by
  have hOrd := candidate_resolution_of_not_wall_rel base hValid
    ((base.gaugedData.vertexPartition wall).repr a) (not_gauged_rel_repr base hA)
  refine Iff.trans (SheetPartition.paste_rel_iff (base.gaugedData.vertexPartition wall)
    (fun blk ↦ ((validCandidate base hValid).resolution blk).newEdge)
    (fun blk ↦ ((validCandidate base hValid).resolution blk).edge_refines_left.trans
      ((validCandidate base hValid).contracts blk).left_refines) a b) ?_
  rw [hOrd]
  rfl

/-! ### The alpha-direction occurrence of a sheet -/

theorem incident_sourceEndpoint_wall_iff (x : Fin degree)
    (old : base.gaugedData.SourceEdge) :
    Incident base.gaugedData old (base.gaugedData.sourceEndpoint wall x) ↔
      (old.1.1 ∈ GluingDatum.incidentEdges wall ∧
        (base.gaugedData.vertexPartition wall).Rel x old.1.2) := by
  constructor
  · intro hIncident
    obtain ⟨hMem, hRel⟩ := (incident_iff_target_mem_and_rel _ _ _).mp hIncident
    exact ⟨hMem, Eq.trans ((base.gaugedData.vertexPartition wall).rel_repr_right x) hRel⟩
  · rintro ⟨hMem, hRel⟩
    exact (incident_iff_target_mem_and_rel _ _ _).mpr
      ⟨hMem, Eq.trans ((base.gaugedData.vertexPartition wall).rel_repr_right x).symm hRel⟩

theorem sourceEndpoint_eq_of_rel {a b : Fin degree}
    (hRel : (base.gaugedData.vertexPartition wall).Rel a b) :
    base.gaugedData.sourceEndpoint wall a = base.gaugedData.sourceEndpoint wall b := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hRel

/-- The alpha-direction occurrence carried by a sheet: over an ordinary wall
block this is the only old occurrence the base tree `T_alpha` sends to `u`. -/
noncomputable def alphaOccurrenceAt (x : Fin degree) : base.gaugedData.SourceEdge :=
  base.gaugedData.sourceEdge (directionEdge star base.alphaLabel) x

@[simp] theorem alphaOccurrenceAt_target (x : Fin degree) :
    (alphaOccurrenceAt base x).1.1 = directionEdge star base.alphaLabel := rfl

theorem rightAssignment_alphaOccurrenceAt (x : Fin degree) :
    base.rightAssignment (alphaOccurrenceAt base x).1.1 = false :=
  base.rightAssignment_alpha

theorem incident_alphaOccurrenceAt (x : Fin degree) :
    Incident base.gaugedData (alphaOccurrenceAt base x)
      (base.gaugedData.sourceEndpoint wall x) :=
  (incident_sourceEndpoint_wall_iff base x _).mpr
    ⟨directionEdge_mem_incidentEdges star base.alphaLabel,
      (alphaEdge_refines base).rel
        ((base.gaugedData.edgePartition
          (directionEdge star base.alphaLabel)).rel_repr_right x)⟩

theorem alphaOccurrenceAt_eq_of_rel {a b : Fin degree}
    (hRel : (base.gaugedData.edgePartition (directionEdge star base.alphaLabel)).Rel a b) :
    alphaOccurrenceAt base a = alphaOccurrenceAt base b :=
  sourceEdge_eq_of_rel hRel

theorem eq_alphaOccurrenceAt {x : Fin degree} {old : base.gaugedData.SourceEdge}
    (hSide : base.rightAssignment old.1.1 = false)
    (hRel : (base.gaugedData.edgePartition
      (directionEdge star base.alphaLabel)).Rel x old.1.2) :
    old = alphaOccurrenceAt base x :=
  oldSourceEdge_eq base ((base.rightAssignment_eq_false_iff old.1.1).mp hSide) hRel

theorem eq_alphaOccurrenceAt_self {old : base.gaugedData.SourceEdge}
    (hSide : base.rightAssignment old.1.1 = false) :
    old = alphaOccurrenceAt base old.1.2 :=
  eq_alphaOccurrenceAt base hSide rfl

/-! ### Incidence at the two ordinary endpoint vertices -/

theorem incident_endpointVertex_iff (hValid : data.Valid) (sideValue : Bool)
    (x : Fin degree) (e : (validCandidate base hValid).datum.SourceEdge) :
    Incident (validCandidate base hValid).datum e
        (endpointVertex base hValid sideValue x) ↔
      (e.1.1 ∈ GluingDatum.incidentEdges
          (if sideValue then freshVertex target else oldVertex target wall) ∧
        ((validCandidate base hValid).datum.vertexPartition
          (if sideValue then freshVertex target else oldVertex target wall)).Rel
            x e.1.2) := by
  constructor
  · intro hIncident
    obtain ⟨hMem, hRel⟩ := (incident_iff_target_mem_and_rel _ _ _).mp hIncident
    exact ⟨hMem, Eq.trans (((validCandidate base hValid).datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right x)
      hRel⟩
  · rintro ⟨hMem, hRel⟩
    refine (incident_iff_target_mem_and_rel _ _ _).mpr ⟨hMem, ?_⟩
    exact Eq.trans (((validCandidate base hValid).datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right
      x).symm hRel

theorem endpointVertex_eq_ordinary (hValid : data.Valid) (sideValue : Bool)
    {a b : Fin degree} (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a)
    (hRel : (ordinaryPartition base sideValue).Rel a b) :
    endpointVertex base hValid sideValue a = endpointVertex base hValid sideValue b := by
  apply (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr
  refine ⟨rfl, ?_⟩
  refine Eq.trans ?_ (((validCandidate base hValid).datum.vertexPartition
    (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right b)
  exact (candidate_vertexPartition_rel_ordinary base hValid sideValue hA).mpr hRel

theorem incident_oldSourceEdge_endpointVertex_iff (hValid : data.Valid)
    (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (old : base.gaugedData.SourceEdge) :
    Incident (validCandidate base hValid).datum
        ((validCandidate base hValid).oldSourceEdge old)
        (endpointVertex base hValid sideValue x) ↔
      ((old.1.1 ∈ GluingDatum.incidentEdges wall ∧
          (ordinaryPartition base sideValue).Rel x old.1.2) ∧
        base.rightAssignment old.1.1 = sideValue) := by
  rw [incident_endpointVertex_iff, BalancedGlobal.Candidate.oldSourceEdge_target,
    mem_incidentEdges_endpoint_old, BalancedGlobal.Candidate.oldSourceEdge_sheet,
    candidate_vertexPartition_rel_ordinary base hValid sideValue hX]
  tauto

theorem newSourceEdge_eq_iff_ordinary (hValid : data.Valid) {a b : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    (validCandidate base hValid).newSourceEdge a =
        (validCandidate base hValid).newSourceEdge b ↔
      (base.gaugedData.edgePartition (directionEdge star base.alphaLabel)).Rel a b := by
  constructor
  · intro hEq
    refine (newEdge_rel_ordinary base hValid hA).mp ?_
    exact congrArg
      (fun e : (validCandidate base hValid).datum.SourceEdge ↦ e.1.2) hEq
  · intro hRel
    exact newSourceEdge_eq_of_rel base hValid
      ((newEdge_rel_ordinary base hValid hA).mpr hRel)

theorem newSourceEdge_eq_of_incident_false (hValid : data.Valid) {x y : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hIncident : Incident (validCandidate base hValid).datum
      ((validCandidate base hValid).newSourceEdge y)
      (endpointVertex base hValid false x)) :
    (validCandidate base hValid).newSourceEdge y =
      (validCandidate base hValid).newSourceEdge x := by
  have hRel := ((incident_endpointVertex_iff base hValid false x _).mp hIncident).2
  rw [candidate_vertexPartition_rel_ordinary base hValid false hX] at hRel
  have hSheet : ((validCandidate base hValid).newSourceEdge y).1.2 =
      (LocalResolution.paste (base.gaugedData.vertexPartition wall)
        (validCandidate base hValid).resolution
        (validCandidate base hValid).contracts).newEdge.repr y := rfl
  rw [hSheet] at hRel
  have hRelD : (base.gaugedData.edgePartition
      (directionEdge star base.alphaLabel)).Rel x
      ((LocalResolution.paste (base.gaugedData.vertexPartition wall)
        (validCandidate base hValid).resolution
        (validCandidate base hValid).contracts).newEdge.repr y) := hRel
  have hBack : (base.gaugedData.vertexPartition wall).Rel
      ((LocalResolution.paste (base.gaugedData.vertexPartition wall)
        (validCandidate base hValid).resolution
        (validCandidate base hValid).contracts).newEdge.repr y) y :=
    (newEdge_refines_wall base hValid).rel
      ((LocalResolution.paste (base.gaugedData.vertexPartition wall)
        (validCandidate base hValid).resolution
        (validCandidate base hValid).contracts).newEdge.rel_repr_left y)
  have hY : ¬ (data.vertexPartition wall).Rel anchor.1 y := by
    intro h
    refine hX ?_
    rw [← gauged_rel_iff base] at h ⊢
    exact h.trans ((((alphaEdge_refines base).rel hRelD).trans hBack).symm)
  refine (newSourceEdge_eq_iff_ordinary base hValid hY).mpr ?_
  refine Eq.trans ?_ hRelD.symm
  exact (newEdge_rel_ordinary base hValid hY).mp
    (((LocalResolution.paste (base.gaugedData.vertexPartition wall)
      (validCandidate base hValid).resolution
      (validCandidate base hValid).contracts).newEdge.rel_repr_left y).symm)

theorem wall_rel_of_incident_true (hValid : data.Valid) {x y : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hIncident : Incident (validCandidate base hValid).datum
      ((validCandidate base hValid).newSourceEdge y)
      (endpointVertex base hValid true x)) :
    (base.gaugedData.vertexPartition wall).Rel x y := by
  have hRel := ((incident_endpointVertex_iff base hValid true x _).mp hIncident).2
  rw [candidate_vertexPartition_rel_ordinary base hValid true hX] at hRel
  have hSheet : ((validCandidate base hValid).newSourceEdge y).1.2 =
      (LocalResolution.paste (base.gaugedData.vertexPartition wall)
        (validCandidate base hValid).resolution
        (validCandidate base hValid).contracts).newEdge.repr y := rfl
  rw [hSheet] at hRel
  refine hRel.trans ?_
  exact (newEdge_refines_wall base hValid).rel
    ((LocalResolution.paste (base.gaugedData.vertexPartition wall)
      (validCandidate base hValid).resolution
      (validCandidate base hValid).contracts).newEdge.rel_repr_left y)

/-! ### The gauged datum's star at an ordinary block, split by side -/

/-- The gauged datum's surviving occurrences at one ordinary block, on one side
of the outgoing base tree `T_alpha`.  The `false` side carries only `t_alpha`,
the `true` side the doubled direction and `t_beta`. -/
noncomputable def ordinaryStar (x : Fin degree) (sideValue : Bool) :
    Finset base.gaugedData.SourceEdge := by
  classical
  exact (nonDanglingIncident base.gaugedData
    (base.gaugedData.sourceEndpoint wall x)).filter
      (fun old ↦ base.rightAssignment old.1.1 = sideValue)

theorem mem_ordinaryStar {x : Fin degree} {sideValue : Bool}
    (old : base.gaugedData.SourceEdge) :
    old ∈ ordinaryStar base x sideValue ↔
      ((¬ IsDangling base.gaugedData old ∧
          Incident base.gaugedData old (base.gaugedData.sourceEndpoint wall x)) ∧
        base.rightAssignment old.1.1 = sideValue) := by
  classical
  rw [ordinaryStar, Finset.mem_filter, mem_nonDanglingIncident]

theorem ordinaryStar_disjoint (x : Fin degree) :
    Disjoint (ordinaryStar base x false) (ordinaryStar base x true) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro old hFalse hTrue
  rw [mem_ordinaryStar] at hFalse hTrue
  rw [hFalse.2] at hTrue
  exact Bool.false_ne_true hTrue.2

theorem ordinaryStar_union (x : Fin degree) :
    ordinaryStar base x false ∪ ordinaryStar base x true =
      nonDanglingIncident base.gaugedData (base.gaugedData.sourceEndpoint wall x) := by
  classical
  ext old
  rw [Finset.mem_union, mem_ordinaryStar, mem_ordinaryStar, mem_nonDanglingIncident]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    cases base.rightAssignment old.1.1
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr ⟨h, rfl⟩

theorem card_ordinaryStar_add (x : Fin degree) :
    (ordinaryStar base x false).card + (ordinaryStar base x true).card =
      nonDanglingValency base.gaugedData (base.gaugedData.sourceEndpoint wall x) := by
  classical
  rw [← Finset.card_union_of_disjoint (ordinaryStar_disjoint base x),
    ordinaryStar_union, card_nonDanglingIncident]

theorem wall_rel_of_mem_ordinaryStar {x : Fin degree} {sideValue : Bool}
    {old : base.gaugedData.SourceEdge} (hOld : old ∈ ordinaryStar base x sideValue) :
    (base.gaugedData.vertexPartition wall).Rel x old.1.2 :=
  ((incident_sourceEndpoint_wall_iff base x old).mp
    ((mem_ordinaryStar base old).mp hOld).1.2).2

theorem mem_incidentEdges_of_mem_ordinaryStar {x : Fin degree} {sideValue : Bool}
    {old : base.gaugedData.SourceEdge} (hOld : old ∈ ordinaryStar base x sideValue) :
    old.1.1 ∈ GluingDatum.incidentEdges wall :=
  ((incident_sourceEndpoint_wall_iff base x old).mp
    ((mem_ordinaryStar base old).mp hOld).1.2).1

theorem not_rel_anchor_of_mem_ordinaryStar {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) {sideValue : Bool}
    {old : base.gaugedData.SourceEdge} (hOld : old ∈ ordinaryStar base x sideValue) :
    ¬ (data.vertexPartition wall).Rel anchor.1 old.1.2 := by
  intro h
  refine hX ?_
  rw [← gauged_rel_iff base] at h ⊢
  exact h.trans (wall_rel_of_mem_ordinaryStar base hOld).symm

/-! ### The census at the divalent end `C_u` of an ordinary block -/

theorem incident_oldSourceEdge_alphaOccurrenceAt (hValid : data.Valid)
    {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    Incident (validCandidate base hValid).datum
      ((validCandidate base hValid).oldSourceEdge (alphaOccurrenceAt base x))
      (endpointVertex base hValid false x) :=
  (incident_oldSourceEdge_endpointVertex_iff base hValid false hX _).mpr
    ⟨⟨directionEdge_mem_incidentEdges star base.alphaLabel,
      (base.gaugedData.edgePartition
        (directionEdge star base.alphaLabel)).rel_repr_right x⟩,
      base.rightAssignment_alpha⟩

/-- **The census at a divalent ordinary endpoint.** -/
theorem mem_nonDanglingIncident_endpointVertex_false_ordinary (hValid : data.Valid)
    {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (e : (validCandidate base hValid).datum.SourceEdge) :
    e ∈ nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid false x) ↔
      ((e = (validCandidate base hValid).oldSourceEdge (alphaOccurrenceAt base x) ∧
          ¬ IsDangling base.gaugedData (alphaOccurrenceAt base x)) ∨
        (e = (validCandidate base hValid).newSourceEdge x ∧
          ¬ IsDangling (validCandidate base hValid).datum
            ((validCandidate base hValid).newSourceEdge x))) := by
  classical
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases (validCandidate base hValid) e with
      ⟨old, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨⟨-, hRel⟩, hSide⟩ :=
        (incident_oldSourceEdge_endpointVertex_iff base hValid false hX old).mp hIncident
      have hEq : old = alphaOccurrenceAt base x := eq_alphaOccurrenceAt base hSide hRel
      refine Or.inl ⟨congrArg (validCandidate base hValid).oldSourceEdge hEq, ?_⟩
      intro hDangling
      exact hSurvives ((retained_isDangling_iff base hValid old).mpr (hEq ▸ hDangling))
    · have hEq := newSourceEdge_eq_of_incident_false base hValid hX hIncident
      exact Or.inr ⟨hEq, hEq ▸ hSurvives⟩
  · rintro (⟨rfl, hSurv⟩ | ⟨rfl, hSurv⟩)
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨retained_survives base hValid hSurv,
          incident_oldSourceEdge_alphaOccurrenceAt base hValid hX⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨hSurv, bridgeEdge_incident base hValid false x⟩

theorem nonDanglingValency_candidate_ne_one (hValid : data.Valid)
    (vertex : (validCandidate base hValid).datum.SourceVertex) :
    nonDanglingValency (validCandidate base hValid).datum vertex ≠ 1 :=
  NonDanglingValency.nonDanglingValency_ne_one (validCandidate base hValid).datum
    (validCandidate_datum_valid base hValid).1 vertex

/-- **The new occurrence of a fine class survives exactly when the class
carries an alpha-direction survivor.** -/
theorem newSourceEdge_survives_iff_ordinary (hValid : data.Valid) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    ¬ IsDangling (validCandidate base hValid).datum
        ((validCandidate base hValid).newSourceEdge x) ↔
      ¬ IsDangling base.gaugedData (alphaOccurrenceAt base x) := by
  classical
  constructor
  · intro hNew hOldDangling
    refine nonDanglingValency_candidate_ne_one base hValid
      (endpointVertex base hValid false x) ?_
    have hEq : nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid false x) =
          {(validCandidate base hValid).newSourceEdge x} := by
      refine Finset.Subset.antisymm ?_ ?_
      · intro e he
        rcases (mem_nonDanglingIncident_endpointVertex_false_ordinary base hValid
          hX e).mp he with ⟨-, hSurv⟩ | ⟨rfl, -⟩
        · exact absurd hOldDangling hSurv
        · exact Finset.mem_singleton_self _
      · intro e he
        rw [Finset.mem_singleton] at he
        subst he
        exact (mem_nonDanglingIncident_endpointVertex_false_ordinary base hValid
          hX _).mpr (Or.inr ⟨rfl, hNew⟩)
    rw [← card_nonDanglingIncident, hEq, Finset.card_singleton]
  · intro hOld hNewDangling
    refine nonDanglingValency_candidate_ne_one base hValid
      (endpointVertex base hValid false x) ?_
    have hEq : nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid false x) =
          {(validCandidate base hValid).oldSourceEdge (alphaOccurrenceAt base x)} := by
      refine Finset.Subset.antisymm ?_ ?_
      · intro e he
        rcases (mem_nonDanglingIncident_endpointVertex_false_ordinary base hValid
          hX e).mp he with ⟨rfl, -⟩ | ⟨-, hSurv⟩
        · exact Finset.mem_singleton_self _
        · exact absurd hNewDangling hSurv
      · intro e he
        rw [Finset.mem_singleton] at he
        subst he
        exact (mem_nonDanglingIncident_endpointVertex_false_ordinary base hValid
          hX _).mpr (Or.inl ⟨rfl, hOld⟩)
    rw [← card_nonDanglingIncident, hEq, Finset.card_singleton]

/-- **The divalent end over a class with a survivor is divalent.** -/
theorem nonDanglingValency_endpointVertex_false_ordinary (hValid : data.Valid)
    {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hOld : ¬ IsDangling base.gaugedData (alphaOccurrenceAt base x)) :
    nonDanglingValency (validCandidate base hValid).datum
      (endpointVertex base hValid false x) = 2 := by
  classical
  have hNew : ¬ IsDangling (validCandidate base hValid).datum
      ((validCandidate base hValid).newSourceEdge x) :=
    (newSourceEdge_survives_iff_ordinary base hValid hX).mpr hOld
  have hEq : nonDanglingIncident (validCandidate base hValid).datum
      (endpointVertex base hValid false x) =
        {(validCandidate base hValid).oldSourceEdge (alphaOccurrenceAt base x),
          (validCandidate base hValid).newSourceEdge x} := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro e he
      rcases (mem_nonDanglingIncident_endpointVertex_false_ordinary base hValid
        hX e).mp he with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · intro e he
      rw [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact (mem_nonDanglingIncident_endpointVertex_false_ordinary base hValid
          hX _).mpr (Or.inl ⟨rfl, hOld⟩)
      · exact (mem_nonDanglingIncident_endpointVertex_false_ordinary base hValid
          hX _).mpr (Or.inr ⟨rfl, hNew⟩)
  have hNotMem : (validCandidate base hValid).oldSourceEdge (alphaOccurrenceAt base x) ∉
      ({(validCandidate base hValid).newSourceEdge x} :
        Finset (validCandidate base hValid).datum.SourceEdge) := by
    rw [Finset.mem_singleton]
    intro h
    exact newSourceEdge_ne_oldSourceEdge base hValid x (alphaOccurrenceAt base x) h.symm
  rw [← card_nonDanglingIncident, hEq, Finset.card_insert_of_notMem hNotMem,
    Finset.card_singleton]

/-! ### The census at the trivalent end `B_v` of an ordinary block -/

theorem newSourceEdge_survives_of_mem_ordinaryStar (hValid : data.Valid)
    {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    {old : base.gaugedData.SourceEdge} (hOld : old ∈ ordinaryStar base x false) :
    ¬ IsDangling (validCandidate base hValid).datum
      ((validCandidate base hValid).newSourceEdge old.1.2) := by
  refine (newSourceEdge_survives_iff_ordinary base hValid
    (not_rel_anchor_of_mem_ordinaryStar base hX hOld)).mpr ?_
  rw [← eq_alphaOccurrenceAt_self base ((mem_ordinaryStar base old).mp hOld).2]
  exact ((mem_ordinaryStar base old).mp hOld).1.1

theorem incident_newSourceEdge_endpointVertex_true (hValid : data.Valid)
    {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    {sideValue : Bool} {old : base.gaugedData.SourceEdge}
    (hOld : old ∈ ordinaryStar base x sideValue) :
    Incident (validCandidate base hValid).datum
      ((validCandidate base hValid).newSourceEdge old.1.2)
      (endpointVertex base hValid true x) := by
  have hRel : (ordinaryPartition base true).Rel x old.1.2 :=
    wall_rel_of_mem_ordinaryStar base hOld
  rw [endpointVertex_eq_ordinary base hValid true hX hRel]
  exact bridgeEdge_incident base hValid true old.1.2

theorem newSourceEdge_alphaOccurrenceAt_sheet (hValid : data.Valid) {y : Fin degree}
    (hY : ¬ (data.vertexPartition wall).Rel anchor.1 y) :
    (validCandidate base hValid).newSourceEdge (alphaOccurrenceAt base y).1.2 =
      (validCandidate base hValid).newSourceEdge y := by
  refine (newSourceEdge_eq_of_rel base hValid ?_).symm
  exact (newEdge_rel_ordinary base hValid hY).mpr
    ((base.gaugedData.edgePartition
      (directionEdge star base.alphaLabel)).rel_repr_right y)

/-- **The census at a trivalent ordinary endpoint.** -/
theorem nonDanglingIncident_endpointVertex_true_ordinary (hValid : data.Valid)
    {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid true x) =
      (ordinaryStar base x true).image (validCandidate base hValid).oldSourceEdge ∪
        (ordinaryStar base x false).image
          (fun old : base.gaugedData.SourceEdge ↦
            (validCandidate base hValid).newSourceEdge old.1.2) := by
  classical
  ext e
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases (validCandidate base hValid) e with
      ⟨old, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨⟨hTargetMem, hRel⟩, hSide⟩ :=
        (incident_oldSourceEdge_endpointVertex_iff base hValid true hX old).mp hIncident
      refine Or.inl ⟨old, (mem_ordinaryStar base old).mpr ⟨⟨?_, ?_⟩, hSide⟩, rfl⟩
      · intro hDangling
        exact hSurvives ((retained_isDangling_iff base hValid old).mpr hDangling)
      · exact (incident_sourceEndpoint_wall_iff base x old).mpr ⟨hTargetMem, hRel⟩
    · have hWallRel : (base.gaugedData.vertexPartition wall).Rel x y :=
        wall_rel_of_incident_true base hValid hX hIncident
      have hY : ¬ (data.vertexPartition wall).Rel anchor.1 y := by
        intro h
        refine hX ?_
        rw [← gauged_rel_iff base] at h ⊢
        exact h.trans hWallRel.symm
      refine Or.inr ⟨alphaOccurrenceAt base y, (mem_ordinaryStar base _).mpr
        ⟨⟨(newSourceEdge_survives_iff_ordinary base hValid hY).mp hSurvives, ?_⟩,
          base.rightAssignment_alpha⟩,
        newSourceEdge_alphaOccurrenceAt_sheet base hValid hY⟩
      rw [sourceEndpoint_eq_of_rel base hWallRel]
      exact incident_alphaOccurrenceAt base y
  · rintro (⟨old, hOld, rfl⟩ | ⟨old, hOld, rfl⟩)
    · refine (mem_nonDanglingIncident _ _ _).mpr
        ⟨retained_survives base hValid ((mem_ordinaryStar base old).mp hOld).1.1, ?_⟩
      refine (incident_oldSourceEdge_endpointVertex_iff base hValid true hX old).mpr
        ⟨⟨mem_incidentEdges_of_mem_ordinaryStar base hOld,
          wall_rel_of_mem_ordinaryStar base hOld⟩,
          ((mem_ordinaryStar base old).mp hOld).2⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨newSourceEdge_survives_of_mem_ordinaryStar base hValid hX hOld,
          incident_newSourceEdge_endpointVertex_true base hValid hX hOld⟩

theorem newSourceEdge_sheet_injOn (hValid : data.Valid) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    Set.InjOn (fun old : base.gaugedData.SourceEdge ↦
        (validCandidate base hValid).newSourceEdge old.1.2)
      (ordinaryStar base x false : Set base.gaugedData.SourceEdge) := by
  classical
  intro a ha b hb hEq
  have hA : a ∈ ordinaryStar base x false := ha
  have hB : b ∈ ordinaryStar base x false := hb
  have hRel : (base.gaugedData.edgePartition
      (directionEdge star base.alphaLabel)).Rel a.1.2 b.1.2 :=
    (newSourceEdge_eq_iff_ordinary base hValid
      (not_rel_anchor_of_mem_ordinaryStar base hX hA)).mp hEq
  rw [eq_alphaOccurrenceAt_self base ((mem_ordinaryStar base a).mp hA).2,
    eq_alphaOccurrenceAt_self base ((mem_ordinaryStar base b).mp hB).2]
  exact alphaOccurrenceAt_eq_of_rel base hRel

/-- **The trivalent end of an ordinary block has the block's own surviving
valency.** -/
theorem nonDanglingValency_endpointVertex_true_ordinary (hValid : data.Valid)
    {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    nonDanglingValency (validCandidate base hValid).datum
        (endpointVertex base hValid true x) =
      nonDanglingValency base.gaugedData (base.gaugedData.sourceEndpoint wall x) := by
  classical
  have hDisj : Disjoint
      ((ordinaryStar base x true).image (validCandidate base hValid).oldSourceEdge)
      ((ordinaryStar base x false).image
        (fun old : base.gaugedData.SourceEdge ↦
          (validCandidate base hValid).newSourceEdge old.1.2)) := by
    refine Finset.disjoint_left.mpr ?_
    intro e heOld heNew
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp heOld
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp heNew
    exact newSourceEdge_ne_oldSourceEdge base hValid b.1.2 a hb
  have hSum := card_ordinaryStar_add base x
  rw [← card_nonDanglingIncident,
    nonDanglingIncident_endpointVertex_true_ordinary base hValid hX,
    Finset.card_union_of_disjoint hDisj,
    Finset.card_image_of_injective _
      (ResolutionCut.oldSourceEdge_injective (validCandidate base hValid)),
    Finset.card_image_of_injOn (newSourceEdge_sheet_injOn base hValid hX)]
  omega

/-! ## 6.  The retained-row descent -/

/-- A retained survivor of the alpha direction and the new occurrence of its own
fine class are consecutive at the divalent endpoint over that class. -/
theorem stablePath_retainedEdge_eq_newSourceEdge (hValid : data.Valid) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    {old : NonDanglingEdge base.gaugedData}
    (hOld : old.1 ∈ ordinaryStar base x false) :
    (ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
        (base.gaugedData_valid hValid).1 old).stablePath =
      NonDanglingEdge.stablePath
        (⟨(validCandidate base hValid).newSourceEdge old.1.1.2,
          newSourceEdge_survives_of_mem_ordinaryStar base hValid hX hOld⟩ :
            NonDanglingEdge (validCandidate base hValid).datum) := by
  classical
  have hY : ¬ (data.vertexPartition wall).Rel anchor.1 old.1.1.2 :=
    not_rel_anchor_of_mem_ordinaryStar base hX hOld
  have hSide : base.rightAssignment old.1.1.1 = false :=
    ((mem_ordinaryStar base old.1).mp hOld).2
  have hAlpha : old.1 = alphaOccurrenceAt base old.1.1.2 :=
    eq_alphaOccurrenceAt_self base hSide
  have hOldSurv : ¬ IsDangling base.gaugedData (alphaOccurrenceAt base old.1.1.2) := by
    rw [← hAlpha]
    exact old.2
  refine stablePath_eq_of_consecutive
    ⟨?_, endpointVertex base hValid false old.1.1.2, ?_, ?_, ?_⟩
  · intro hEq
    exact newSourceEdge_ne_oldSourceEdge base hValid old.1.1.2 old.1
      (congrArg Subtype.val hEq).symm
  · refine (incident_oldSourceEdge_endpointVertex_iff base hValid false hY old.1).mpr
      ⟨⟨mem_incidentEdges_of_mem_ordinaryStar base hOld, ?_⟩, hSide⟩
    exact (rfl : (ordinaryPartition base false).Rel old.1.1.2 old.1.1.2)
  · exact bridgeEdge_incident base hValid false old.1.1.2
  · exact nonDanglingValency_endpointVertex_false_ordinary base hValid hY hOldSurv

/-- **Every survivor of an ordinary block has a representative at the trivalent
end** carrying the same row of the candidate. -/
theorem exists_trivalentEndEdge (hValid : data.Valid) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    {old : NonDanglingEdge base.gaugedData} {sideValue : Bool}
    (hOld : old.1 ∈ ordinaryStar base x sideValue) :
    ∃ e : NonDanglingEdge (validCandidate base hValid).datum,
      Incident (validCandidate base hValid).datum e.1
        (endpointVertex base hValid true x) ∧
      e.stablePath = (ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
        (base.gaugedData_valid hValid).1 old).stablePath ∧
      ((sideValue = true ∧ e.1 = (validCandidate base hValid).oldSourceEdge old.1) ∨
        (sideValue = false ∧
          e.1 = (validCandidate base hValid).newSourceEdge old.1.1.2)) := by
  classical
  cases sideValue
  · refine ⟨⟨(validCandidate base hValid).newSourceEdge old.1.1.2,
      newSourceEdge_survives_of_mem_ordinaryStar base hValid hX hOld⟩, ?_,
      (stablePath_retainedEdge_eq_newSourceEdge base hValid hX hOld).symm,
      Or.inr ⟨rfl, rfl⟩⟩
    exact incident_newSourceEdge_endpointVertex_true base hValid hX hOld
  · refine ⟨ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
      (base.gaugedData_valid hValid).1 old, ?_, rfl, Or.inl ⟨rfl, rfl⟩⟩
    refine (incident_oldSourceEdge_endpointVertex_iff base hValid true hX old.1).mpr
      ⟨⟨mem_incidentEdges_of_mem_ordinaryStar base hOld,
        wall_rel_of_mem_ordinaryStar base hOld⟩,
        ((mem_ordinaryStar base old.1).mp hOld).2⟩

/-- The remaining geometric input for the retained-row descent: at every wall
block other than the anchor, two surviving occurrences meeting at a divalent
quotient-source vertex still lie on one stable path of the candidate.  It is
discharged by `ordinaryBlockDescent` below. -/
def OrdinaryBlockDescent (hValid : data.Valid) : Prop :=
  ∀ (first second : NonDanglingEdge base.gaugedData)
    (vertex : base.gaugedData.SourceVertex),
    vertex.1.1 = wall →
    ¬ (data.vertexPartition wall).Rel anchor.1 vertex.1.2 →
    first ≠ second →
    Incident base.gaugedData first.1 vertex →
    Incident base.gaugedData second.1 vertex →
    nonDanglingValency base.gaugedData vertex = 2 →
    (ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
        (base.gaugedData_valid hValid).1 first).stablePath =
      (ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
        (base.gaugedData_valid hValid).1 second).stablePath

/-- **The ordinary-block descent, discharged.** -/
theorem ordinaryBlockDescent (hValid : data.Valid) : OrdinaryBlockDescent base hValid := by
  classical
  intro first second vertex hAt hX hNe hFirst hSecond hValency
  have hVertex : base.gaugedData.sourceEndpoint wall vertex.1.2 = vertex :=
    (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
  have hFirst' : Incident base.gaugedData first.1
      (base.gaugedData.sourceEndpoint wall vertex.1.2) := by
    rw [hVertex]; exact hFirst
  have hSecond' : Incident base.gaugedData second.1
      (base.gaugedData.sourceEndpoint wall vertex.1.2) := by
    rw [hVertex]; exact hSecond
  have hMemFirst : first.1 ∈ ordinaryStar base vertex.1.2
      (base.rightAssignment first.1.1.1) :=
    (mem_ordinaryStar base first.1).mpr ⟨⟨first.2, hFirst'⟩, rfl⟩
  have hMemSecond : second.1 ∈ ordinaryStar base vertex.1.2
      (base.rightAssignment second.1.1.1) :=
    (mem_ordinaryStar base second.1).mpr ⟨⟨second.2, hSecond'⟩, rfl⟩
  obtain ⟨e1, hInc1, hRow1, hCase1⟩ :=
    exists_trivalentEndEdge base hValid hX hMemFirst
  obtain ⟨e2, hInc2, hRow2, hCase2⟩ :=
    exists_trivalentEndEdge base hValid hX hMemSecond
  have hNeVal : first.1 ≠ second.1 := fun h ↦ hNe (Subtype.ext h)
  have hNd : nonDanglingValency (validCandidate base hValid).datum
      (endpointVertex base hValid true vertex.1.2) = 2 := by
    rw [nonDanglingValency_endpointVertex_true_ordinary base hValid hX, hVertex]
    exact hValency
  have hNe12 : e1 ≠ e2 := by
    intro hEq
    have hVal : e1.1 = e2.1 := congrArg Subtype.val hEq
    rcases hCase1 with ⟨hs1, h1⟩ | ⟨hs1, h1⟩ <;> rcases hCase2 with ⟨hs2, h2⟩ | ⟨hs2, h2⟩
    · exact hNeVal (ResolutionCut.oldSourceEdge_injective (validCandidate base hValid)
        (by rw [← h1, ← h2, hVal]))
    · exact newSourceEdge_ne_oldSourceEdge base hValid second.1.1.2 first.1
        (by rw [← h2, ← h1, hVal])
    · exact newSourceEdge_ne_oldSourceEdge base hValid first.1.1.2 second.1
        (by rw [← h1, ← h2, hVal])
    · refine hNeVal ?_
      have hStarFirst : first.1 ∈ ordinaryStar base vertex.1.2 false := by
        rw [← hs1]; exact hMemFirst
      have hStarSecond : second.1 ∈ ordinaryStar base vertex.1.2 false := by
        rw [← hs2]; exact hMemSecond
      refine newSourceEdge_sheet_injOn base hValid hX hStarFirst hStarSecond ?_
      show (validCandidate base hValid).newSourceEdge first.1.1.2 =
        (validCandidate base hValid).newSourceEdge second.1.1.2
      rw [← h1, ← h2, hVal]
  rw [← hRow1, ← hRow2]
  exact stablePath_eq_of_consecutive
    ⟨hNe12, endpointVertex base hValid true vertex.1.2, hInc1, hInc2, hNd⟩

theorem stablePath_retained_eq_of_consecutive (hValid : data.Valid)
    {first second : NonDanglingEdge base.gaugedData}
    (h : Consecutive base.gaugedData first second) :
    (ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
        (base.gaugedData_valid hValid).1 first).stablePath =
      (ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
        (base.gaugedData_valid hValid).1 second).stablePath := by
  obtain ⟨hNe, vertex, hFirst, hSecond, hValency⟩ := h
  by_cases hAt : vertex.1.1 = wall
  · by_cases hAnchorRel : (data.vertexPartition wall).Rel anchor.1 vertex.1.2
    · exfalso
      have hVertex : base.gaugedData.sourceEndpoint wall anchor.1 = vertex :=
        (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr
          ⟨hAt.symm, (gauged_rel_iff base).mpr hAnchorRel⟩
      rw [← hVertex, gauged_nonDanglingValency_anchor base hValid] at hValency
      omega
    · exact ordinaryBlockDescent base hValid first second vertex hAt hAnchorRel hNe
        hFirst hSecond hValency
  · exact stablePath_eq_of_consecutive
      (ResolutionAwayFromWall.consecutive_retained_of_away (validCandidate base hValid)
        (base.gaugedData_valid hValid) (candidate_sourceGenus base hValid)
        first second hNe vertex hAt hFirst hSecond hValency)

/-- **The retained-row map, unconditionally.**  Every stable row of the gauged
incoming datum descends to a stable row of the outgoing candidate. -/
noncomputable def retainedRow (hValid : data.Valid) :
    StablePath base.gaugedData → StablePath (validCandidate base hValid).datum :=
  Quot.lift
    (fun e ↦ (ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
      (base.gaugedData_valid hValid).1 e).stablePath)
    (fun _ _ h ↦ stablePath_retained_eq_of_consecutive base hValid h)

@[simp] theorem retainedRow_mk (hValid : data.Valid)
    (e : NonDanglingEdge base.gaugedData) :
    retainedRow base hValid e.stablePath =
      (ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
        (base.gaugedData_valid hValid).1 e).stablePath := rfl

end DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRows
