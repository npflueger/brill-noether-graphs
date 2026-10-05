module

public import DraismaVargasCount.FacetParityPilot
public import DraismaVargasCount.MemberSeedExists
public import DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneLink
public import DraismaVargasCount.SheetLayerMatching
public import DraismaVargasCount.DiagonalClassificationEndgame
public import Utilities.CubicGraphs.CubicDartsTransport

@[expose] public section

/-!
# The facet adapter, and valency-three uniqueness at the caterpillar step

**Source.**  Vargas, Part II, the wall crossing `proposition-walking-through-II` at a
non-trivalent limit, and the valency-three case `{v3-nd4}` (`subsec-case-v3`: exactly
one member of each type at a valency-three limit); the facet arrival of
`DraismaVargas.LocalCases.OuterWalk` and the facet genericity of
`DraismaVargas.LocalCases.FacetGenericity`.  Builds on `FacetMachine` and
`FacetParityPilot`.  The adapter feeds the type changes (step 3 of `Assembly`), through
`LinkReceiptExport`.

## The statement, and what is proved of it

`FacetParity catCubicCore.core catLoopCore.core 4 y₀` at one facet datum of
`FacetMachine.cat_step`.  It is **not** proved here.  What is proved is the generic
adapter (Stage A) in both directions, which discharges the two *existence* halves of
`FacetParityPilot.facetParity_of_unique` at every Whitehead step and every valency,
modulo one precisely named property of Part I's type-change links (`LinkLimitReceipt`),
plus the reduction of the *near-side uniqueness* half at the caterpillar step to one
finite fact.  The far-side uniqueness half (the valency-three uniqueness of Part II,
`subsec-case-v3`) is not treated here.

## Stage A -- the facet adapter (generic)

* **Forward** (§1--§3, §5).  `facetGeneric_comp`: facet genericity
  (`FacetGenericity.FacetGeneric`) is invariant under relabelling base coordinates.
  `exists_facetPoint_general_generic`, `exists_facetDatum_generic`: a facet datum at the
  move's base slot whose point is *also* facet-generic.  `facetArrival`, `wallData`: from
  a facet datum and any facet regrowth, an actual `OuterWalk.FacetArrival` / `WallData`
  -- a synthetic one-chart march state (the pattern of `MemberCertifiedPencil.seedState`)
  whose payload is the frame's own `MemberSeed` candidate (unconditional at degree ≥ 3,
  `MemberSeedExists.nonempty_memberSeed_of_member`), incoming matrix the frame's matrix,
  wall metric the frame's coordinates at `y₀`, zero column the regrowth's column.
  **No march is constructed.**  `pulledMove`, `slot_label_pulledMove_base`: the step's
  move pulled back to the seed's stable graph contracts exactly the row reading `e₀`.  `moveLink`:
  Part I's `TypeChangeLink` there, from `link_all` (all valencies, no hypothesis).
* **Reverse** (§4--§9).  `identOfIso`: a `CoreIdentification` from a dart-graph
  isomorphism (converse of `MemberCoreDarts.coreIso`).  `farFrame`, `farRegrowth`: the
  link's outgoing cover as a frame over the far core, identification read off its
  `Tracks`; `farFrame_slot` (same slot dictionary as the regrowth), `farFrame_coordsAt`
  (same coordinates at `y₀`), `farFrame_degenerateAt` (degenerates in the same column),
  `farFrame_absMult`, `farFrame_isOdd_iff` (same multiplicity, via
  `signedMult_eq_of_typeChangeLink`).  `candidateLimitIso`: **the limit of any
  `BalancedGlobal.Candidate` at its regrown occurrence is its base**, geometrically
  (with `blockSwap`, a block-preserving sheet permutation repairing representatives,
  which `W4LimitContraction.limitIso` cannot do).  `limitIsoWallDatum`: the regrowth's
  limit is the synthetic arrival's wall datum.  `ofLeft_eq_ofRight_farRegrowth`: the far
  regrowth has the regrowth's facet limit, **given `LinkLimitReceipt`**.
  `exists_odd_specializesRight_of_receipts` / `exists_odd_specializesLeft_of_receipts`:
  `hLR` / `hRL` of `facetParity_of_unique`; `revMove`, `farCore_revMove`,
  `facetDatum_rev`, `FacetLimitSwap`: the reverse direction by the reversed move.
  `facetParity_of_uniqueness_and_receipts`: `FacetParity` at a step from the two
  uniqueness halves and the receipts.

## Stage B -- ident pinning: not needed for the adapter

The far frame is well defined without any choice among ident orbits, because the link's
`Tracks` is an actual dart isomorphism onto the moved graph, which the pulled-back move
carries onto the far core's graph (`farIso`); the identification it induces reads slots
exactly as the regrowth does (`farFrame_slot`), and the frame is degenerate at `y₀`
automatically (`farFrame_degenerateAt`) -- the degenerate orbit is produced rather than
selected.  Ident pinning is a statement about *uniqueness* (two far classes with
isomorphic data), and it belongs to the far-side uniqueness, below.

## Stage C -- uniqueness at the caterpillar step

* `cat_exists_odd_far`: at a facet-generic facet datum of `cat_step`, an odd frame over
  `catLoopCore`, open at the facet request.
* `ballotClassification_facet` (the ballot classification of the caterpillar fibre at the
  facet request, with no hypothesis), `ballot_of_specializesLeft`,
  `cat_huniqL_of_limit_injective`: near-side uniqueness reduces to the finite fact that
  two ballot members specialising to one facet limit are equal.
* `cat_obligation_of_residues`: the per-step obligation of
  `TypeChangeSupplyPositive 4 10 15` at `cat_step` from the hypotheses below.

## What is NOT proved -- every surviving hypothesis

* **`FacetParity` at `cat_step` is not proved.**  `cat_obligation_of_residues` takes:
  * `huniqL` -- near-side uniqueness; reduced by `cat_huniqL_of_limit_injective` to
    `hinj` (limits of distinct ballot members differ), not proved;
  * `huniqR` -- far-side uniqueness over `catLoopCore`: the valency-three uniqueness of
    Part II (`subsec-case-v3`) plus ident pinning, not treated here;
  * `hrec`, `hrec'` : `FacetLinkReceipts` in both directions (proved in
    `LinkReceiptExport`: `facetLinkReceipts`, `facetLinkReceipts_rev`).
* **`LinkLimitReceipt`** (two fields: the outgoing vanishing column is the regrown
  occurrence; the link's base is geometrically the wall datum) holds **by construction
  at Part I's type-change exits** -- proved here at the valency-three Type III exit,
  `linkLimitReceipt_valencyThreeTypeIII` -- but is not recorded by the link:
  `TypeChangeLink` has no such fields and `link_all` / `typeChangeLink_three'` return
  `Nonempty.some`, so it cannot be read off the link `moveLink` produces.
  `LinkReceiptExport` threads the two fields through the dispatchers (valency 4 exit +
  swap; valency 3 Type III, Types I/II, mirror, swap; valency 2 exits) and proves
  `FacetLinkReceipts`.
* `exists_odd_farRegrowth` needs no receipt, but says nothing about limits.
* `3 ≤ degree` is explicit (the `MemberSeed` receipt); harmless at degree 4.
* The far core is taken literally as `farCore m' = CubicCore.ofGraph (c.graph.move m')`;
  `FacetMachine.catLoopCore` is that term (`catLoopCore_eq_farCore`, `rfl`); a step given
  only as `Step c c'` needs `CubicCore.graph_injective` to reach this form.
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no `#eval`.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.FacetAdapterPilot

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame NFFrame)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open DraismaVargas.Count.FacetMachine

variable {n p degree : ℕ}

/-! ## 1.  Part I's facet genericity at a facet datum -/

section Generic

open FacetGenericity FiniteAtlasMarch

/-- Row-permuting an atlas matrix gives an atlas matrix. -/
theorem isAtlasMatrix_submatrix {degree : ℕ} {M : Matrix (Fin p) (Fin p) ℚ}
    (h : MatrixAtlas.IsAtlasMatrix degree M) (σ : Fin p ≃ Fin p) :
    MatrixAtlas.IsAtlasMatrix degree (M.submatrix σ id) :=
  fun i j ↦ h (σ i) j

/-- **Facet genericity is invariant under relabelling the base coordinates.**  The universal
atlas is closed under row permutations, so facet genericity of `y` gives facet
genericity of `y ∘ σ`. -/
theorem facetGeneric_comp {y : Fin p → ℚ} (h : FacetGeneric degree y) (σ : Fin p ≃ Fin p) :
    FacetGeneric degree (y ∘ σ) := by
  classical
  intro label first second hfirst hsecond
  set M := MatrixAtlas.atlasMatrix label with hM
  have hdet : M.det ≠ 0 := MatrixAtlas.atlasMatrix_det_ne_zero label
  let M' : Matrix (Fin p) (Fin p) ℚ := M.submatrix σ.symm id
  have hdet' : M'.det ≠ 0 := by
    have := Matrix.det_permute σ.symm M
    rw [show M' = M.submatrix σ.symm id from rfl, this]
    refine mul_ne_zero ?_ hdet
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h]
  have hatlas : MatrixAtlas.IsAtlasMatrix degree M' :=
    isAtlasMatrix_submatrix (MatrixAtlas.atlasMatrix_isAtlasMatrix label) σ.symm
  set z := chartCoordinates M (y ∘ σ) with hz
  have hMz : M.mulVec z = y ∘ σ := mulVec_chartCoordinates M hdet _
  have hM'z : M'.mulVec z = y := by
    funext i
    have := congrFun hMz (σ.symm i)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
    rw [← this]
    rfl
  have hchart : chartCoordinates (MatrixAtlas.atlasMatrix (MatrixAtlas.encode M' hatlas hdet')) y
      = z := by
    rw [MatrixAtlas.atlasMatrix_encode]
    exact chartCoordinates_eq_of_mulVec_eq M' hdet' hM'z
  exact h (MatrixAtlas.encode M' hatlas hdet') first second (by rw [hchart]; exact hfirst)
    (by rw [hchart]; exact hsecond)

/-- **Both genericity conditions at once**: a facet point general on the facet for both
cores (`FacetMachine.FacetGeneral`) and facet-generic for the universal atlas
(`FacetGenericity.FacetGeneric`).  One finite avoidance over the union of the two
exceptional families. -/
theorem exists_facetPoint_general_generic (c c' : Core n p) (degree : ℕ) (e₀ : Fin p) :
    ∃ y₀ : Fin p → ℚ, FacetPoint e₀ y₀ ∧ FacetGeneral c degree e₀ y₀ ∧
      FacetGeneral c' degree e₀ y₀ ∧ FacetGeneric degree y₀ := by
  classical
  let _ : Fintype (NFFrame c degree) := Fintype.ofFinite _
  let _ : Fintype (NFFrame c' degree) := Fintype.ofFinite _
  let W : ((NFFrame c degree × Fin p) ⊕ (NFFrame c' degree × Fin p)) ⊕
      (MatrixAtlas.chart (Fin p) degree × Fin p) → RationalAffineWall (Fin p) :=
    Sum.elim (Sum.elim (fun x ↦ facetWall (NFFrame.toFrame x.1) e₀ x.2)
      (fun x ↦ facetWall (NFFrame.toFrame x.1) e₀ x.2))
      (fun x ↦ facetRowWall (MatrixAtlas.atlasMatrix x.1) e₀ x.2)
  obtain ⟨z, hpos, havoid⟩ :=
    RationalAffineWall.exists_avoids_preserving_positive
      (fun x : {x // (W x).Proper} ↦ W x.1) SegmentWalls.coordinateWall (fun _ ↦ 1)
      (fun x ↦ x.2) (by intro l; rw [SegmentWalls.eval_coordinateWall]; norm_num)
  refine ⟨Function.update z e₀ 0, ⟨Function.update_self e₀ 0 z, fun e he ↦ ?_⟩,
    ?_, ?_, ?_⟩
  · rw [Function.update_of_ne he]
    have h := hpos e
    rwa [SegmentWalls.eval_coordinateWall] at h
  · exact facetGeneral_of_avoid c degree e₀ z fun r col hprop ↦
      havoid ⟨Sum.inl (Sum.inl (r, col)), hprop⟩
  · exact facetGeneral_of_avoid c' degree e₀ z fun r col hprop ↦
      havoid ⟨Sum.inl (Sum.inr (r, col)), hprop⟩
  · refine facetGeneric_of_avoids degree e₀ _ (Function.update_self _ _ _) ?_
    intro event
    rw [eval_update_of_coefficient_eq_zero _ e₀ (facetRowWall_coefficient_facet _ e₀ event.2)]
    exact havoid ⟨Sum.inr event, facetRowWall_proper _ e₀ event.2⟩

end Generic

/-! ## 2.  A facet datum at the contracted slot of a named move -/

section NamedMove

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.CubicCoreDarts (vertex opposite)
open TypeChangePositiveProbe (contractVertex contractVertex_fst contractVertex_snd
  ends_of_vertex)

/-- **The slot a named Whitehead move contracts is a shared contraction slot.**  This
is `TypeChangePositiveProbe.exists_shared_contraction_core` with the move fixed, so
that the facet datum's slot is the move's base slot `m.base.1`. -/
theorem sharedContractionSlot_of_move {c c' : CubicCore n p} (m : c.graph.MoveData)
    (hm : c'.graph = c.graph.move m) :
    SharedContractionSlot c.core c'.core m.base.1 := by
  have hvc : vertex c.core = c.graph.vert := CoreOfDarts.vertex_coreOf c.graph
  have hvc' : vertex c'.core = c'.graph.vert := CoreOfDarts.vertex_coreOf c'.graph
  have hall : ∀ d : Fin p × Bool, contractVertex (c.graph.vert m.base)
      (c.graph.vert (c.graph.op m.base)) (vertex c'.core d) =
        contractVertex (c.graph.vert m.base) (c.graph.vert (c.graph.op m.base))
          (vertex c.core d) := by
    intro d
    rw [hvc, hvc', hm]
    show contractVertex _ _ (c.graph.vert (m.perm d)) = _
    by_cases hl : d = m.left
    · subst hl
      rw [m.perm_left, m.right_vert, m.left_vert]
      exact (contractVertex_snd _ _).trans (contractVertex_fst _ _).symm
    · by_cases hr : d = m.right
      · subst hr
        rw [m.perm_right, m.left_vert, m.right_vert]
        exact (contractVertex_fst _ _).trans (contractVertex_snd _ _).symm
      · rw [m.perm_of_ne hl hr]
  have h₀ : vertex c.core m.base = c.graph.vert m.base := by rw [hvc]
  have h₁ : vertex c.core (opposite m.base) = c.graph.vert (c.graph.op m.base) := by
    rw [hvc]; rfl
  refine ⟨c.graph.vert m.base, c.graph.vert (c.graph.op m.base), m.nonloop.symm, ?_,
    fun e ↦ hall (e, false), fun e ↦ hall (e, true)⟩
  rcases ends_of_vertex c.core m.base with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · exact Or.inl ⟨ht.trans h₀, hh.trans h₁⟩
  · exact Or.inr ⟨ht.trans h₁, hh.trans h₀⟩

/-- **A facet datum at the move's base slot whose facet point is also facet-generic**
(`FacetGenericity.FacetGeneric`).  This is `FacetMachine.exists_facetDatum` with the slot
named by the move and the facet point chosen by `exists_facetPoint_general_generic`. -/
theorem exists_facetDatum_generic {c c' : CubicCore n p} (m : c.graph.MoveData)
    (hm : c'.graph = c.graph.move m) (degree : ℕ) :
    ∃ (y₀ : Fin p → ℚ) (ε : ℚ), FacetDatum c.core c'.core degree m.base.1 y₀ ε ∧
      FacetGenericity.FacetGeneric degree y₀ := by
  obtain ⟨y₀, hpt, hgen, hgen', hG⟩ :=
    exists_facetPoint_general_generic c.core c'.core degree m.base.1
  obtain ⟨ε₀, hε₀, hst⟩ := exists_facetStable c.core degree hpt.1 hgen
  obtain ⟨ε₁, hε₁, hst'⟩ := exists_facetStable c'.core degree hpt.1 hgen'
  have hmin : 0 < min ε₀ ε₁ := lt_min hε₀ hε₁
  exact ⟨y₀, min ε₀ ε₁, ⟨sharedContractionSlot_of_move m hm, hpt, hgen, hgen', hmin,
    hst _ hmin (min_le_left _ _), hst' _ hmin (min_le_right _ _)⟩, hG⟩

end NamedMove

/-! ## 3.  Stage A, forward: a facet regrowth is a Part I facet arrival -/

section Forward

open FiniteAtlasMarch MemberCertifiedPencil InteriorGraphTracking

variable {c c' : Core n p} {e₀ : Fin p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- The chart of a member seed's presentation in the universal atlas. -/
noncomputable def seedChart {core : Core n p} {y : Fin p → ℚ}
    {member : FibreMember core y degree} (ms : MemberSeed member) :
    MatrixAtlas.chart (Fin p) degree :=
  MatrixAtlas.encodePresentation ms.fullDim.labelling.presentation
    (fun row ↦ A04MoreTags.nodup_labelling_path _ row) ms.fullDim.det_ne_zero

theorem atlasMatrix_seedChart {core : Core n p} {y : Fin p → ℚ}
    {member : FibreMember core y degree} (ms : MemberSeed member) :
    MatrixAtlas.atlasMatrix (seedChart ms) =
      GluingDatum.LengthMatrixPresentation.matrix ms.fullDim.labelling.presentation :=
  MatrixAtlas.atlasMatrix_encodePresentation _ _ _

/-- The seed chart displays the regrowth frame's own length matrix. -/
theorem atlasMatrix_seedChart_frame (w : Regrowth c y₀ degree)
    (ms : MemberSeed (w.frame.member y₀)) :
    MatrixAtlas.atlasMatrix (seedChart ms) = w.frame.matrix :=
  (atlasMatrix_seedChart ms).trans ms.matrix_eq

theorem mulVec_seedChart (w : Regrowth c y₀ degree) (ms : MemberSeed (w.frame.member y₀))
    (y : Fin p → ℚ) :
    (MatrixAtlas.atlasMatrix (seedChart ms)).mulVec (w.frame.coordsAt y) = y ∘ w.frame.slot := by
  rw [atlasMatrix_seedChart_frame, w.frame.mulVec_coordsAt]
  rfl

/-- The synthetic one-chart march state at a facet regrowth: chart the frame's own
matrix, restart at time zero, start the frame's coordinates at the facet request,
finish its coordinates at the facet point.  No step is ever taken (the pattern of
`MemberCertifiedPencil.seedState`). -/
noncomputable def facetState (hd : FacetDatum c c' degree e₀ y₀ ε)
    (w : Regrowth c y₀ degree) (ms : MemberSeed (w.frame.member y₀)) :
    State (MatrixAtlas.atlasMatrix (coordinate := Fin p) (degree := degree))
      ((MatrixAtlas.atlasMatrix (seedChart ms)).mulVec
        (w.frame.coordsAt (facetRequest e₀ y₀ ε)))
      (y₀ ∘ w.frame.slot) :=
  State.initial (seedChart ms) (w.frame.coordsAt (facetRequest e₀ y₀ ε))
    (w.frame.coordsAt y₀)
    (openAt_of_degenerateAt hd.point hd.general hd.stable hd.pos w.degenerate) rfl
    (mulVec_seedChart w ms y₀)

/-- **Stage A, forward: the facet arrival of a facet regrowth.**  The arrival's graph
and labels are the seed's own constructed stable graph and literal row labels
(`TrackedPencil.seedGraph`/`seedLabel`), its facet is the matrix row that reads the
contracted slot `e₀`, and its finish is the facet point read through the frame's
slot dictionary, which is facet-generic by `facetGeneric_comp`. -/
noncomputable def facetArrival (hd : FacetDatum c c' degree e₀ y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c y₀ degree) (ms : MemberSeed (w.frame.member y₀))
    (facet : Fin p) (hfacet : w.frame.slot facet = e₀) :
    OuterWalk.FacetArrival degree (TrackedPencil.seedGraph ms.seed ms.fullDim)
      (TrackedPencil.seedLabel ms.seed ms.fullDim) facet where
  baseStart := (MatrixAtlas.atlasMatrix (seedChart ms)).mulVec
    (w.frame.coordsAt (facetRequest e₀ y₀ ε))
  baseFinish := y₀ ∘ w.frame.slot
  start_pos i := by
    rw [mulVec_seedChart]
    exact hd.positiveGeneral_left.1 _
  finish_facet := by
    show y₀ (w.frame.slot facet) = 0
    rw [hfacet]
    exact hd.point.1
  finish_pos t ht := by
    show 0 < y₀ (w.frame.slot t)
    refine hd.point.2 _ fun h ↦ ht ?_
    rw [← hfacet] at h
    exact w.frame.slot.injective h
  facetGeneric := facetGeneric_comp hG _
  final := TrackedState.initial (facetState hd w ms) (by
    show TrackedPencil degree _ _ (MatrixAtlas.atlasMatrix (seedChart ms))
      (w.frame.coordsAt (facetRequest e₀ y₀ ε))
    rw [atlasMatrix_seedChart]
    exact TrackedPencil.ofSeed hDegree ms.seed ms.fullDim _
      (openAt_of_degenerateAt hd.point hd.general hd.stable hd.pos w.degenerate))
  terminal := by
    intro i
    show 0 ≤ w.frame.coordsAt y₀ i
    by_cases hi : i = w.column
    · rw [hi, w.degenerate.1]
    · exact (w.degenerate.2 i hi).le
  restart_nonneg := le_refl 0

/-- **Stage A, forward: the wall data of a facet regrowth.**  The terminal payload is
the seed's candidate itself, tracked by its own graph; the incoming matrix is the
regrowth frame's matrix, the wall metric is the frame's coordinates at the facet
point, and the zero column is the regrowth's column. -/
noncomputable def wallData (hd : FacetDatum c c' degree e₀ y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c y₀ degree) (ms : MemberSeed (w.frame.member y₀))
    (facet : Fin p) (hfacet : w.frame.slot facet = e₀) :
    OuterWalk.WallData (facetArrival hd hG hDegree w ms facet hfacet) where
  target := ms.seed.target
  data := ms.seed.data
  wall := ms.seed.wall
  candidate := ms.seed.candidate
  fullDim := ms.fullDim
  matrix_eq := (atlasMatrix_seedChart ms).symm
  tracks := Tracks.self ms.fullDim
  column := w.column
  column_zero := w.degenerate.1
  column_unique c hc := by
    by_contra hne
    exact (w.degenerate.2 c hne).ne' hc

section WallDataFacts

variable (hd : FacetDatum c c' degree e₀ y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c y₀ degree) (ms : MemberSeed (w.frame.member y₀))
    (facet : Fin p) (hfacet : w.frame.slot facet = e₀)

@[simp] theorem wallData_column : (wallData hd hG hDegree w ms facet hfacet).column = w.column :=
  rfl

theorem wallData_coordinates :
    (wallData hd hG hDegree w ms facet hfacet).coordinates = w.frame.coordsAt y₀ := rfl

theorem wallData_incomingMatrix :
    (wallData hd hG hDegree w ms facet hfacet).incomingMatrix = w.frame.matrix :=
  ms.matrix_eq

end WallDataFacts

end Forward

/-! ## 4.  A core identification from a dart-graph isomorphism

The converse of `MemberCoreDarts.coreIso`: an isomorphism from a datum's constructed
stable graph onto a core's dart graph is a `Count.CoreIdentification`.  This is what
turns a Part I `Tracks` of the moved graph into a frame over the far core. -/

section IdentOfIso

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.StableSourceDarts
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StablePathCount (incidenceCount)
open DraismaVargas.Count.MemberCoreDarts (firstDart row_firstDart incidenceCount_eq_card_darts)

variable {target : CFGraph.{0}} {data : GluingDatum target degree}
  (hConnected : data.Connected) (hTrivalent : ∀ v, nonDanglingValency data v ≤ 3)
  (hEnds : HasPathEnds data)
  {G : CubicDartGraph (Fin p × Bool) (Fin n)} (hop : G.op = CubicCoreDarts.opposite)
  (i : CubicDartGraph.Iso (ofDatum data hConnected hTrivalent hEnds) G)

include hop in
/-- The slot of a dart's image depends only on the dart's stable row. -/
theorem slot_opposite (d : Dart data) :
    (i.dart (opposite data hConnected hEnds d)).1 = (i.dart d).1 := by
  have h := i.op_map d
  rw [hop] at h
  rw [← show (ofDatum data hConnected hTrivalent hEnds).op d = opposite data hConnected hEnds d
    from rfl, ← h]
  rfl

include hop in
theorem slot_eq_of_row_eq {d e : Dart data} (h : row data d = row data e) :
    (i.dart d).1 = (i.dart e).1 := by
  rcases (row_eq_iff data hConnected hEnds d e).mp h with rfl | rfl
  · rfl
  · exact (slot_opposite hConnected hTrivalent hEnds hop i d).symm

/-- The stable rows are the core slots, through the dart isomorphism. -/
noncomputable def rowEquivOfIso : StablePath data ≃ Fin p where
  toFun r := (i.dart (firstDart hConnected hEnds r)).1
  invFun s := row data (i.dart.symm (s, false))
  left_inv r := by
    set x := i.dart (firstDart hConnected hEnds r) with hx
    rcases hb : x.2 with _ | _
    · have hxe : (x.1, false) = x := by rw [← hb]
      show row data (i.dart.symm (x.1, false)) = r
      rw [hxe, hx, Equiv.symm_apply_apply, row_firstDart]
    · have hxe : (x.1, false) = G.op x := by
        rw [hop]
        show (x.1, false) = (x.1, !x.2)
        rw [hb]; rfl
      show row data (i.dart.symm (x.1, false)) = r
      rw [hxe, hx, i.op_map, Equiv.symm_apply_apply]
      show row data (opposite data hConnected hEnds _) = r
      rw [row_opposite, row_firstDart]
  right_inv s := by
    show (i.dart (firstDart hConnected hEnds (row data (i.dart.symm (s, false))))).1 = s
    rw [slot_eq_of_row_eq hConnected hTrivalent hEnds hop i
      (row_firstDart hConnected hEnds _), Equiv.apply_symm_apply]

theorem rowEquivOfIso_row (d : Dart data) :
    rowEquivOfIso hConnected hTrivalent hEnds hop i (row data d) = (i.dart d).1 :=
  slot_eq_of_row_eq hConnected hTrivalent hEnds hop i (row_firstDart hConnected hEnds _)

/-- **A core identification from a dart-graph isomorphism** onto the dart graph of
the core `CoreOfDarts.coreOf G`. -/
noncomputable def identOfIso : CoreIdentification (CoreOfDarts.coreOf G) data where
  vertex := i.vtx
  row := rowEquivOfIso hConnected hTrivalent hEnds hop i
  incidence b s := by
    classical
    rw [incidenceCount_eq_card_darts b]
    have hrow : ∀ d : Dart data, row data d = (rowEquivOfIso hConnected hTrivalent hEnds hop i).symm s ↔
        (i.dart d).1 = s := by
      intro d
      rw [Equiv.eq_symm_apply, rowEquivOfIso_row]
    have hvert : ∀ d : Dart data, vertex data d = b ↔ G.vert (i.dart d) = i.vtx b := by
      intro d
      rw [i.vert_map]
      exact ⟨fun h ↦ by rw [show (ofDatum data hConnected hTrivalent hEnds).vert d = vertex data d
        from rfl, h], fun h ↦ i.vtx.injective h⟩
    have hcard : (Finset.univ.filter fun d : Dart data ↦
        row data d = (rowEquivOfIso hConnected hTrivalent hEnds hop i).symm s ∧ vertex data d = b).card =
        (Finset.univ.filter fun x : Fin p × Bool ↦ x.1 = s ∧ G.vert x = i.vtx b).card := by
      refine Finset.card_nbij' (fun d ↦ i.dart d) (fun x ↦ i.dart.symm x) ?_ ?_ ?_ ?_
      · intro d hd
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hd ⊢
        exact ⟨(hrow d).mp hd.1, (hvert d).mp hd.2⟩
      · intro x hx
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
        refine ⟨(hrow _).mpr ?_, (hvert _).mpr ?_⟩
        · rw [Equiv.apply_symm_apply]; exact hx.1
        · rw [Equiv.apply_symm_apply]; exact hx.2
      · intro d _
        exact Equiv.symm_apply_apply _ _
      · intro x _
        exact Equiv.apply_symm_apply _ _
    rw [hcard]
    have hset : (Finset.univ.filter fun x : Fin p × Bool ↦ x.1 = s ∧ G.vert x = i.vtx b) =
        ({(s, false), (s, true)} : Finset (Fin p × Bool)).filter
          (fun x ↦ G.vert x = i.vtx b) := by
      ext ⟨e, t⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, h⟩
        cases t <;> simp [h]
      · rintro ⟨h | h, hv⟩ <;> exact ⟨h.1, hv⟩
    rw [hset, Finset.card_filter, Finset.sum_pair (by simp)]
    rfl

end IdentOfIso

/-! ## 5.  Stage A, reverse: the Part I link over the step, and the far-side frame -/

section Reverse

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.CubicDartsTransport
open MemberCertifiedPencil InteriorGraphTracking OuterWalk
open DraismaVargas.LocalCases.StableSourceDarts (row)

variable {c : CubicCore n p} {c' : Core n p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- The far core of a named move, literally (as `FacetMachine.catLoopCore` is). -/
abbrev farCore (m' : c.graph.MoveData) : CubicCore n p :=
  CubicCore.ofGraph (c.graph.move m') rfl

/-- The seed's stable graph is the near core's dart graph: `MemberCoreDarts.coreIso`
at the seed's own identification. -/
noncomputable def seedIso (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀)) :
    CubicDartGraph.Iso (TrackedPencil.seedGraph ms.seed ms.fullDim) c.graph :=
  MemberCoreDarts.coreIso ms.fullDim.connected ms.fullDim.pathEnds ms.ident ms.fullDim.trivalent
    c.cubic c.connected

/-- **The seed's row labels read the near core's slots through the regrowth's slot
dictionary.** -/
theorem slot_seedLabel (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀))
    (d : StableSourceDarts.Dart ms.seed.candidate.datum) :
    w.frame.slot (TrackedPencil.seedLabel ms.seed ms.fullDim d) = ((seedIso w ms).dart d).1 := by
  show w.frame.slot (ms.fullDim.labelling.row (row _ d)) = ms.ident.row (row _ d)
  have h := ms.ident_row (ms.fullDim.labelling.row (row _ d))
  rw [Equiv.symm_apply_apply] at h
  rw [h]
  rfl

/-- The step's move, pulled back to the seed's stable graph. -/
noncomputable def pulledMove (w : Regrowth c.core y₀ degree)
    (ms : MemberSeed (w.frame.member y₀)) (m' : c.graph.MoveData) :
    (TrackedPencil.seedGraph ms.seed ms.fullDim).MoveData :=
  m'.transport (seedIso w ms).symm

/-- **The pulled-back move contracts the matrix row reading the step's slot.** -/
theorem slot_label_pulledMove_base (w : Regrowth c.core y₀ degree)
    (ms : MemberSeed (w.frame.member y₀)) (m' : c.graph.MoveData) :
    w.frame.slot (TrackedPencil.seedLabel ms.seed ms.fullDim (pulledMove w ms m').base) =
      m'.base.1 := by
  rw [slot_seedLabel]
  show ((seedIso w ms).dart ((seedIso w ms).dart.symm m'.base)).1 = m'.base.1
  rw [Equiv.apply_symm_apply]

/-- **Stage A: Part I's arrival at a facet regrowth, at the pulled-back move.** -/
noncomputable def moveArrival (m' : c.graph.MoveData)
    (hd : FacetDatum c.core c' degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀)) :
    FacetArrival degree (TrackedPencil.seedGraph ms.seed ms.fullDim)
      (TrackedPencil.seedLabel ms.seed ms.fullDim)
      (TrackedPencil.seedLabel ms.seed ms.fullDim (pulledMove w ms m').base) :=
  facetArrival hd hG hDegree w ms _ (slot_label_pulledMove_base w ms m')

/-- Its wall data. -/
noncomputable def moveWallData (m' : c.graph.MoveData)
    (hd : FacetDatum c.core c' degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀)) :
    WallData (moveArrival m' hd hG hDegree w ms) :=
  wallData hd hG hDegree w ms _ (slot_label_pulledMove_base w ms m')

/-- **Stage A: the Part I type-change link at every facet regrowth**, of every
valency: `NonTrivalentValencyTwoBaseOneLink.link_all` (valencies two, three, four;
no hypothesis) at the synthetic arrival. -/
noncomputable def moveLink (m' : c.graph.MoveData)
    (hd : FacetDatum c.core c' degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀)) :
    TypeChangeLink (pulledMove w ms m') (moveWallData m' hd hG hDegree w ms) :=
  NonTrivalentValencyTwoBaseOneLink.link_all _ Relation.ReflTransGen.refl _ _ _

section Frame

variable (m' : c.graph.MoveData) (hd : FacetDatum c.core c' degree m'.base.1 y₀ ε)
  (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
  (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀))
  (link : TypeChangeLink (pulledMove w ms m') (moveWallData m' hd hG hDegree w ms))

/-- The link's tracking, composed with the pulled-back move isomorphism, lands on the
far core's dart graph. -/
noncomputable def farIso :
    CubicDartGraph.Iso (StableSourceDarts.ofDatum link.candidate.datum
      link.outgoingFD.connected link.outgoingFD.trivalent link.outgoingFD.pathEnds)
      (c.graph.move m') :=
  link.tracks.iso.trans (Iso.movePullback (seedIso w ms) m')

/-- **The far-side frame of a link**: the link's outgoing cover and presentation, with
the core identification read off its tracking.  The identification is pinned by the
link -- no choice among ident orbits is made. -/
noncomputable def farFrame : Frame (farCore m').core degree where
  target := _
  data := link.candidate.datum
  fullDim := link.outgoingFD
  ident := identOfIso link.outgoingFD.connected link.outgoingFD.trivalent
    link.outgoingFD.pathEnds rfl (farIso m' hd hG hDegree w ms link)

/-- **The far frame reads the slots exactly as the regrowth does.** -/
theorem farFrame_slot : (farFrame m' hd hG hDegree w ms link).slot = w.frame.slot := by
  refine Equiv.ext fun q ↦ ?_
  set d := MemberCoreDarts.firstDart link.outgoingFD.connected link.outgoingFD.pathEnds
    (link.outgoingFD.labelling.row.symm q) with hd'
  have key := rowEquivOfIso_row link.outgoingFD.connected link.outgoingFD.trivalent
    link.outgoingFD.pathEnds rfl (farIso m' hd hG hDegree w ms link) d
  have hrow : row _ d = link.outgoingFD.labelling.row.symm q :=
    MemberCoreDarts.row_firstDart link.outgoingFD.connected link.outgoingFD.pathEnds _
  rw [hrow] at key
  have h2 : ((farIso m' hd hG hDegree w ms link).dart d).1 =
      w.frame.slot (link.outgoingFD.labelling.row (row _ d)) := by
    have h3 := slot_seedLabel w ms (link.tracks.iso.dart d)
    rw [link.tracks.row_map] at h3
    exact h3.symm
  rw [hrow, Equiv.apply_symm_apply] at h2
  exact key.trans h2

/-- The far frame's matrix is the link's outgoing matrix. -/
theorem farFrame_matrix :
    (farFrame m' hd hG hDegree w ms link).matrix = link.outgoingMatrix := rfl

/-- **At the facet point the far frame has the regrowth's own coordinates**: the two
matrices agree off the vanishing column, where the coordinate vector is zero. -/
theorem farFrame_coordsAt :
    (farFrame m' hd hG hDegree w ms link).coordsAt y₀ = w.frame.coordsAt y₀ := by
  have hz : w.frame.coordsAt y₀ w.column = 0 := w.degenerate.1
  have hin : (moveWallData m' hd hG hDegree w ms).incomingMatrix.mulVec (w.frame.coordsAt y₀) =
      fun r ↦ y₀ (w.frame.slot r) := by
    rw [show (moveWallData m' hd hG hDegree w ms).incomingMatrix = w.frame.matrix from
      ms.matrix_eq]
    exact w.frame.mulVec_coordsAt y₀
  have hout : link.outgoingMatrix.mulVec (w.frame.coordsAt y₀) =
      fun r ↦ y₀ (w.frame.slot r) := by
    rw [← hin]
    exact (mulVec_eq_on_wall link.agree hz).symm
  show (farFrame m' hd hG hDegree w ms link).matrix⁻¹.mulVec
    (fun r ↦ y₀ ((farFrame m' hd hG hDegree w ms link).slot r)) = _
  rw [farFrame_slot, farFrame_matrix, ← hout, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr link.outgoingMatrix_det_ne_zero),
    Matrix.one_mulVec]

/-- **The far frame degenerates at the facet point, in the regrowth's column.** -/
theorem farFrame_degenerateAt :
    (farFrame m' hd hG hDegree w ms link).DegenerateAt y₀ w.column := by
  rw [Frame.DegenerateAt, farFrame_coordsAt]
  exact w.degenerate

/-- **The far regrowth.** -/
noncomputable def farRegrowth : Regrowth (farCore m').core y₀ degree :=
  ⟨farFrame m' hd hG hDegree w ms link, w.column, farFrame_degenerateAt m' hd hG hDegree w ms link⟩

end Frame

/-- **The seed presentation carries the regrowth frame's multiplicity**: the seed's
cover is the frame's datum transported along a target isomorphism
(`MemberSeed.datumEq`), and multiplicity is a geometric invariant
(`GeometricMultiplicity.fdAbsMult_eq_of_datumIso`). -/
theorem fdAbsMult_seed (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀)) :
    fdAbsMult ms.fullDim = w.frame.absMult := by
  have iso : GeometricDatumIso w.frame.data ms.seed.candidate.datum :=
    ms.datumEq ▸ GeometricDatumIso.ofTargetIso ms.targetIso (w.frame.member y₀).data
  exact GeometricMultiplicity.fdAbsMult_eq_of_datumIso iso w.frame.fullDim ms.fullDim

/-- **The far frame has the regrowth's multiplicity** (equal signed multiplicity across a
non-trivalent limit, Part II `lm:change-comb-type`:
`NonTrivalentNonfacetDenominator.signedMult_eq_of_typeChangeLink`, no valency
hypothesis). -/
theorem farFrame_absMult (m' : c.graph.MoveData) (hd : FacetDatum c.core c' degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀))
    (link : TypeChangeLink (pulledMove w ms m') (moveWallData m' hd hG hDegree w ms)) :
    (farFrame m' hd hG hDegree w ms link).absMult = w.frame.absMult := by
  have h := NonTrivalentNonfacetDenominator.signedMult_eq_of_typeChangeLink link
  calc (farFrame m' hd hG hDegree w ms link).absMult = |fdSignedMult link.outgoingFD| := rfl
    _ = |fdSignedMult ms.fullDim| := by rw [h]; rfl
    _ = fdAbsMult ms.fullDim := rfl
    _ = w.frame.absMult := fdAbsMult_seed w ms

/-- **Oddness is carried across the link, on classes.** -/
theorem farFrame_isOdd_iff (m' : c.graph.MoveData)
    (hd : FacetDatum c.core c' degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀))
    (link : TypeChangeLink (pulledMove w ms m') (moveWallData m' hd hG hDegree w ms)) :
    (FrameClass.mk (farFrame m' hd hG hDegree w ms link)).IsOdd ↔
      (FrameClass.mk w.frame).IsOdd := by
  rw [FrameClass.isOdd_mk, FrameClass.isOdd_mk, farFrame_absMult]

end Reverse

/-! ## 6.  The limit of a candidate at its regrown occurrence is its base, geometrically

`W4LimitContraction.limitIso` needs the join of the two restored wall partitions to be
the base wall partition *as a structure*; a `BalancedGlobal.Candidate` only gives it as a
relation (`LocalResolution.paste_contracts`: `IsJoin`).  Sheet partitions carry chosen
representatives, so the two may differ; a block-preserving sheet permutation at the
merged vertex (`blockSwap`) repairs the representatives, which a geometric isomorphism
allows. -/

section CandidateLimit

open GraphContraction GluingContraction TargetExpansion
open DraismaVargas.Count.W4LimitContraction (vertexEquiv edgeEquiv ends_edgeEquiv
  edgePartition_eq fst_eq snd_eq vertexEquiv_apply)

section BlockSwap

variable {d : ℕ} (P Q : SheetPartition d)

/-- Exchange, in every block, the representative `P` chooses with the one `Q` chooses. -/
def blockSwapFun (i : Fin d) : Fin d :=
  if i = P.repr i then Q.repr i else if i = Q.repr i then P.repr i else i

variable {P Q} (h : ∀ i j, P.Rel i j ↔ Q.Rel i j)
include h

theorem blockSwapFun_rel (i : Fin d) : P.Rel (blockSwapFun P Q i) i := by
  unfold blockSwapFun
  split_ifs with h1 h2
  · exact (h _ _).mpr (Q.rel_repr_left i)
  · exact P.rel_repr_left i
  · rfl

theorem blockSwapFun_involutive : Function.Involutive (blockSwapFun P Q) := by
  intro i
  have hPQ : ∀ j, Q.repr (P.repr j) = Q.repr j := fun j ↦ (h _ _).mp (P.rel_repr_left j)
  have hQP : ∀ j, P.repr (Q.repr j) = P.repr j := fun j ↦ (h _ _).mpr (Q.rel_repr_left j)
  unfold blockSwapFun
  by_cases hp : i = P.repr i
  · rw [ite_eq_left hp]
    by_cases hq : Q.repr i = P.repr (Q.repr i)
    · rw [ite_eq_left hq, Q.repr_idem]
      rw [hQP] at hq
      exact hq.trans hp.symm
    · rw [ite_eq_right hq, ite_eq_left (Q.repr_idem i).symm, hQP, ← hp]
  · rw [ite_eq_right hp]
    by_cases hq : i = Q.repr i
    · rw [ite_eq_left hq, ite_eq_left (P.repr_idem i).symm, hPQ, ← hq]
    · rw [ite_eq_right hq, ite_eq_right hp, ite_eq_right hq]

/-- The block swap, as a permutation. -/
def blockSwap : Equiv.Perm (Fin d) := (blockSwapFun_involutive h).toPerm

theorem blockSwap_apply (i : Fin d) : blockSwap h i = blockSwapFun P Q i := rfl

theorem blockSwap_symm_apply (i : Fin d) : (blockSwap h).symm i = blockSwapFun P Q i := rfl

/-- **Relabelling by the block swap turns `P`'s representatives into `Q`'s.** -/
theorem relabel_blockSwap : P.relabel (blockSwap h) = Q := by
  refine SheetPartition.ext_repr _ _ (funext fun i ↦ ?_)
  show blockSwapFun P Q (P.repr (blockSwapFun P Q i)) = Q.repr i
  have hr : P.repr (blockSwapFun P Q i) = P.repr i := blockSwapFun_rel h i
  rw [hr]
  unfold blockSwapFun
  rw [ite_eq_left (P.repr_idem i).symm]
  exact (h _ _).mp (P.rel_repr_left i)

end BlockSwap

variable {T : CFGraph} {D : GluingDatum T degree} {wall : T.V}
  (C : BalancedGlobal.Candidate T degree D wall)
  {a b : (graph T wall C.right).V} {contracted : (graph T wall C.right).edges}
  (hc : (contracted : (graph T wall C.right).V × (graph T wall C.right).V) = (a, b))
  (hab : a ≠ b) (hOne : num_edges (graph T wall C.right) a b = 1)
  (hcontract : contracted = occurrenceEquiv T wall C.right none)

include hc hcontract in
/-- The merged partition of the contracted candidate and the base wall partition have the
same blocks. -/
theorem candidate_merge_rel (i j : Fin degree) :
    (SheetPartition.join (C.datum.vertexPartition a) (C.datum.vertexPartition b)).Rel i j ↔
      (D.vertexPartition wall).Rel i j := by
  rw [fst_eq hc hcontract, snd_eq hc hcontract,
    W3Nd2IncomingMemberMatching.candidate_vertexPartition_old_wall,
    W3Nd2IncomingMemberMatching.candidate_vertexPartition_fresh]
  exact ((ResolutionM11.LocalResolution.paste_contracts (D.vertexPartition wall) C.resolution
    C.contracts).rel_iff_join_rel i j).symm

include hc hcontract in
/-- The sheet permutation used at the merged vertex. -/
noncomputable def mergePerm : Equiv.Perm (Fin degree) :=
  blockSwap (candidate_merge_rel C hc hcontract)

open Classical in
/-- **The limit of a candidate at its regrown occurrence is its base datum**, as a
geometric gluing datum: the literal contraction dictionaries, the identity sheet
permutation everywhere except at the merged vertex, where the block swap repairs the
representatives. -/
noncomputable def candidateLimitIso :
    GeometricDatumIso (contractDatum C.datum hc hab hOne) D where
  targetVertex := vertexEquiv hc hab hOne hcontract
  targetEdge := edgeEquiv hc hab hOne hcontract
  ends edge := Or.inl (ends_edgeEquiv hc hab hOne hcontract edge)
  vertexPerm v := if v.1 = a then mergePerm C hc hcontract else Equiv.refl _
  edgePerm _ := Equiv.refl _
  vertexPartition vertex := by
    rw [contractDatum_vertexPartition]
    by_cases hv : vertex.1 = a
    · have hvertex : vertex = ⟨a, hab⟩ := Subtype.ext hv
      subst hvertex
      rw [ite_eq_left rfl, contractVertexPartition_merge, mergePerm, relabel_blockSwap]
      change D.vertexPartition (contractVertex T wall a) = _
      rw [fst_eq hc hcontract]
      rfl
    · rw [ite_eq_right hv, Transport.DatumIso.relabel_refl, contractVertexPartition_of_ne _ a b hv]
      have hvb : vertex.1 ≠ freshVertex T := by
        rw [← snd_eq hc hcontract]
        exact vertex.2
      rw [fst_eq hc hcontract] at hv
      obtain ⟨u, hu⟩ : ∃ u : T.V, vertex.1 = oldVertex T u := by
        rcases hvv : vertex.1 with u | u
        · exact ⟨u, rfl⟩
        · cases u
          exact absurd hvv hvb
      have hune : u ≠ wall := by
        intro hEq
        exact hv (hu.trans (congrArg (oldVertex T) hEq))
      rw [vertexEquiv_apply, hu, contract_oldVertex]
      exact (W3Nd2IncomingMemberMatching.candidate_vertexPartition_old_of_ne C u hune).symm
  edgePartition edge := by
    rw [Transport.DatumIso.relabel_refl]
    exact edgePartition_eq hc hab hOne hcontract D C.datum
      (W3Nd2IncomingMemberMatching.candidate_edgePartition_old C) edge
  compatible edge vertex _ sheet := by
    by_cases hv : vertex.1 = a
    · rw [ite_eq_left hv]
      show (contractVertexPartition C.datum a b vertex).Rel
        ((mergePerm C hc hcontract).symm sheet) sheet
      have hvertex : vertex = ⟨a, hab⟩ := Subtype.ext hv
      subst hvertex
      rw [contractVertexPartition_merge, mergePerm, blockSwap_symm_apply]
      exact blockSwapFun_rel (candidate_merge_rel C hc hcontract) sheet
    · rw [ite_eq_right hv]
      rfl

end CandidateLimit

/-! ## 7.  Stage A, reverse: the far regrowth has the regrowth's facet limit, given
the two facts of `LinkLimitReceipt` -/

section LimitAgreement

open GraphContraction GluingContraction TargetExpansion
open MemberCertifiedPencil OuterWalk

section Cast

variable {T T' : CFGraph.{0}} {D₀ : GluingDatum T degree} {d₁ d₂ : GluingDatum T' degree}

theorem cast_iso_targetEdge (h : d₁ = d₂) (iso : GeometricDatumIso D₀ d₁) :
    (h ▸ iso : GeometricDatumIso D₀ d₂).targetEdge = iso.targetEdge := by
  subst h; rfl

theorem cast_fullDim_targetEdge (h : d₁ = d₂)
    (fd : FullDimensionalSource.FullDimensionalSourcePresentation d₁ (Fin p)) :
    (h ▸ fd).labelling.targetEdge = fd.labelling.targetEdge := by
  subst h; rfl

end Cast

variable {core : Core n p} {y₀ : Fin p → ℚ}

/-- The seed's cover is the regrowth frame's datum, geometrically. -/
noncomputable def seedDatumIso (w : Regrowth core y₀ degree)
    (ms : MemberSeed (w.frame.member y₀)) :
    GeometricDatumIso w.frame.data ms.seed.candidate.datum :=
  ms.datumEq ▸ GeometricDatumIso.ofTargetIso ms.targetIso (w.frame.member y₀).data

theorem seedDatumIso_targetEdge (w : Regrowth core y₀ degree)
    (ms : MemberSeed (w.frame.member y₀)) (col : Fin p) :
    (seedDatumIso w ms).targetEdge (w.frame.edgeOf col) = ms.fullDim.labelling.targetEdge col := by
  have h1 := congrFun (congrArg DFunLike.coe (cast_iso_targetEdge ms.datumEq
    (GeometricDatumIso.ofTargetIso ms.targetIso (w.frame.member y₀).data))) (w.frame.edgeOf col)
  have h2 := congrFun (congrArg DFunLike.coe
    (cast_fullDim_targetEdge ms.datumEq ms.transportedFullDim)) col
  exact h1.trans h2.symm

/-- **The regrowth's limit is the wall datum of its synthetic arrival.** -/
noncomputable def limitIsoWallDatum {c : CubicCore n p} {c' : Core n p} {ε : ℚ}
    (m' : c.graph.MoveData) (hd : FacetDatum c.core c' degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀)) :
    GeometricDatumIso w.limit (moveWallData m' hd hG hDegree w ms).wallDatum :=
  GeometricLimitTransport.contractDatumIsoOfEdgeEq (seedDatumIso w ms)
    (w.frame.edgeOf w.column) (ms.fullDim.labelling.targetEdge w.column)
    (seedDatumIso_targetEdge w ms w.column) (w.frame.numEdges_edgeOf w.column)
    (moveWallData m' hd hG hDegree w ms).hOne

/-- **The two facts Part I's type-change exits establish by construction.**  Every exit
builds its outgoing labelling so that the vanishing column is the regrown occurrence
(e.g. `NonTrivalentValencyThreeExit.outLabelling`: "the new target occurrence into the
vanishing column"), and its base is the wall datum (valencies two and three) or a sheet
gauge of it (valency four, `PrescribedPairing.gaugedData`).  Neither is a field of
`OuterWalk.TypeChangeLink`, and `link_all` returns `Nonempty.some` of the dispatchers,
so neither can be read off an arbitrary link: this is the one hypothesis Stage A leaves.
`LinkReceiptExport` proves that some link at every wall datum carries both. -/
structure LinkLimitReceipt {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate} {m : graph.MoveData}
    {arrival : FacetArrival degree graph label (label m.base)} {wd : WallData arrival}
    (link : TypeChangeLink m wd) : Prop where
  column_new : link.outgoingFD.labelling.targetEdge wd.column =
    occurrenceEquiv (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      link.candidate.right none
  base_iso : Nonempty (GeometricDatumIso link.base wd.wallDatum)

/-- **Stage A, reverse, closed modulo the receipt: the far regrowth has the regrowth's
facet limit.** -/
theorem ofLeft_eq_ofRight_farRegrowth {c : CubicCore n p} {ε : ℚ}
    (m' : c.graph.MoveData) (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀))
    (link : TypeChangeLink (pulledMove w ms m') (moveWallData m' hd hG hDegree w ms))
    (hrec : LinkLimitReceipt link) :
    FacetLimit.ofLeft (c' := (farCore m').core) w =
      FacetLimit.ofRight (farRegrowth m' hd hG hDegree w ms link) := by
  obtain ⟨hbase⟩ := hrec.base_iso
  have far : GeometricDatumIso (farRegrowth m' hd hG hDegree w ms link).limit link.base :=
    candidateLimitIso link.candidate rfl (fst_ne_snd _)
      ((farRegrowth m' hd hG hDegree w ms link).frame.numEdges_edgeOf w.column) hrec.column_new
  exact Quotient.sound ⟨((limitIsoWallDatum m' hd hG hDegree w ms).trans hbase.symm).trans far.symm⟩

end LimitAgreement

section ReceiptWitness

open OuterWalk InteriorGraphTracking
open DraismaVargas.Infrastructure.CubicDarts
open GraphContraction GluingContraction TargetExpansion

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  {wallStar : ThirdEquation.ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : W4Assembly.WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : NonTrivalentValencyThreeAnchor.ThreeBranchAnchor
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hNoGlue : W4StableSource.DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))
  (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
  (hPathEnds : W4StableSource.HasPathEnds
    (NonTrivalentValencyThreeCandidate.Prescribed.validCandidate src hNoGlue hValid).datum)

/-- **The receipt holds at an exit, by construction**: at the valency-three Type III exit
`NonTrivalentValencyThreeExit.typeChangeLink_of_receipts` the vanishing column is the
regrown occurrence (the column chart sends it to `none`) and the base is the wall datum
itself.  The dispatchers, which return `Nonempty` links, do not record it. -/
theorem linkLimitReceipt_valencyThreeTypeIII
    (tracks : Tracks (NonTrivalentValencyThreeExit.wallOutgoingFD m wd src hNoGlue hValid
      hPathEnds) (graph.move m) label) :
    LinkLimitReceipt (NonTrivalentValencyThreeExit.typeChangeLink_of_receipts m wd src hNoGlue
      hValid hPathEnds tracks) := by
  refine ⟨?_, ⟨GeometricDatumIso.refl _⟩⟩
  have h2 : (NonTrivalentValencyTwoExit.colChart wd.cover wd.fullDim
      (contracted := wd.contracted)).symm wd.column = none := by
    rw [← wd.targetEdge_symm_contracted]
    exact Equiv.optionSubtypeNe_symm_self _
  exact congrArg (NonTrivalentValencyThreeRowEquiv.labelling src hNoGlue hValid
    (NonTrivalentValencyTwoExit.wallLab wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m)
      (NonTrivalentValencyThreeExit.noContractedReturn_of_valency_three m wd wallStar)
      wd.coordinates (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord wd.hFacetZero)).targetEdge h2

end ReceiptWitness

/-! ## 8.  Existence transfer (`facetParity_of_unique`'s `hLR`), modulo the receipt -/

section Transfer

open MemberCertifiedPencil OuterWalk

variable {c : CubicCore n p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- **The hypothesis Stage A leaves, at one facet datum**: every facet regrowth over the
near core admits a Part I link carrying the two facts of `LinkLimitReceipt`.

Not an interface for `FacetParity`: it is a statement about Part I's type-change exits
alone (their outgoing labelling and base), true by construction in each exit and not
recorded by `OuterWalk.TypeChangeLink`; `LinkReceiptExport.facetLinkReceipts` proves it.
It is used by `exists_odd_specializesRight_of_receipts` (the `hLR` half of
`FacetParityPilot.facetParity_of_unique`). -/
def FacetLinkReceipts (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree) : Prop :=
  ∀ (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀)),
    ∃ link : TypeChangeLink (pulledMove w ms m') (moveWallData m' hd hG hDegree w ms),
      LinkLimitReceipt link

/-- **Stage A, assembled: an odd class specialising on the near side has an odd partner
specialising to the same facet limit on the far side**, given the receipts. -/
theorem exists_odd_specializesRight_of_receipts (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (hrec : FacetLinkReceipts m' hd hG (by omega))
    (l : FacetLimit c.core (farCore m').core y₀ degree) (x : FrameClass c.core degree)
    (hx : x.IsOdd) (hs : SpecializesLeft x l) :
    ∃ x' : FrameClass (farCore m').core degree, x'.IsOdd ∧ SpecializesRight x' l := by
  obtain ⟨w, rfl, rfl⟩ := hs
  obtain ⟨ms⟩ := MemberSeedExists.nonempty_memberSeed_of_member (w.frame.member y₀) hDegree
  obtain ⟨link, hlink⟩ := hrec w ms
  refine ⟨FrameClass.mk (farFrame m' hd hG (by omega) w ms link),
    (farFrame_isOdd_iff m' hd hG (by omega) w ms link).mpr hx,
    farRegrowth m' hd hG (by omega) w ms link, rfl, ?_⟩
  exact (ofLeft_eq_ofRight_farRegrowth m' hd hG (by omega) w ms link hlink).symm

/-- **Without any receipt**: every odd facet regrowth over the near core has an odd far
regrowth at the same facet point, in the same column (the Part I link `moveLink`, read as
a frame).  Only the identification of the two facet limits is missing. -/
theorem exists_odd_farRegrowth (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (w : Regrowth c.core y₀ degree) (hw : (FrameClass.mk w.frame).IsOdd) :
    ∃ w' : Regrowth (farCore m').core y₀ degree,
      w'.column = w.column ∧ w'.frame.slot = w.frame.slot ∧
        w'.frame.coordsAt y₀ = w.frame.coordsAt y₀ ∧ (FrameClass.mk w'.frame).IsOdd := by
  obtain ⟨ms⟩ := MemberSeedExists.nonempty_memberSeed_of_member (w.frame.member y₀) hDegree
  let link := moveLink m' hd hG (by omega) w ms
  exact ⟨farRegrowth m' hd hG (by omega) w ms link, rfl,
    farFrame_slot m' hd hG (by omega) w ms link, farFrame_coordsAt m' hd hG (by omega) w ms link,
    (farFrame_isOdd_iff m' hd hG (by omega) w ms link).mpr hw⟩

end Transfer

/-! ## 9.  Both directions: the reversed move, and swapping the two sides of a facet
limit -/

section Symmetry

open DraismaVargas.Infrastructure.CubicDarts

namespace FacetLimitSwap

variable {c c' : Core n p} {y₀ : Fin p → ℚ}

/-- Exchange the two sides of a facet limit. -/
def swap : FacetLimit c c' y₀ degree → FacetLimit c' c y₀ degree :=
  Quotient.map Sum.swap (by
    rintro (a | a) (b | b) h <;> exact h)

@[simp] theorem swap_ofLeft (w : Regrowth c y₀ degree) :
    swap (FacetLimit.ofLeft (c' := c') w) = FacetLimit.ofRight w := rfl

@[simp] theorem swap_ofRight (w : Regrowth c' y₀ degree) :
    swap (FacetLimit.ofRight (c := c) w) = FacetLimit.ofLeft w := rfl

theorem swap_swap (l : FacetLimit c c' y₀ degree) : swap (swap l) = l := by
  induction l using Quotient.inductionOn with
  | h a => rcases a with a | a <;> rfl

theorem specializesLeft_iff {x : FrameClass c degree} {l : FacetLimit c c' y₀ degree} :
    SpecializesLeft x l ↔ SpecializesRight x (swap l) := by
  constructor
  · rintro ⟨w, hx, rfl⟩
    exact ⟨w, hx, rfl⟩
  · rintro ⟨w, hx, hl⟩
    refine ⟨w, hx, ?_⟩
    have := congrArg swap hl
    rwa [swap_ofRight, swap_swap] at this

theorem specializesRight_iff {x : FrameClass c' degree} {l : FacetLimit c c' y₀ degree} :
    SpecializesRight x l ↔ SpecializesLeft x (swap l) := by
  constructor
  · rintro ⟨w, hx, rfl⟩
    exact ⟨w, hx, rfl⟩
  · rintro ⟨w, hx, hl⟩
    refine ⟨w, hx, ?_⟩
    have := congrArg swap hl
    rwa [swap_ofLeft, swap_swap] at this

end FacetLimitSwap

variable {c : CubicCore n p}

theorem farCore_graph (m' : c.graph.MoveData) : (farCore m').graph = c.graph.move m' :=
  CubicCore.graph_ofGraph _ rfl

theorem cast_moveData_base {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] {G H : CubicDartGraph D V} (h : G = H) (m : G.MoveData) :
    (h ▸ m : H.MoveData).base = m.base := by
  subst h; rfl

theorem move_cast {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] {G H : CubicDartGraph D V} (h : G = H) (m : G.MoveData) :
    H.move (h ▸ m) = G.move m := by
  subst h; rfl

/-- The reversed move, on the far core's own dart graph. -/
def revMove (m' : c.graph.MoveData) : (farCore m').graph.MoveData :=
  (farCore_graph m').symm ▸ m'.reverse

theorem revMove_base (m' : c.graph.MoveData) : (revMove m').base = m'.base :=
  cast_moveData_base _ _

theorem move_revMove (m' : c.graph.MoveData) : (farCore m').graph.move (revMove m') = c.graph :=
  (move_cast _ _).trans (CubicDartGraph.move_reverse c.graph m')

/-- The reversed move lands back on the near core. -/
theorem farCore_revMove (m' : c.graph.MoveData) : farCore (revMove m') = c :=
  CubicCore.graph_injective ((farCore_graph _).trans (move_revMove m'))

/-- **A facet datum of a named move is a facet datum of the reversed move.** -/
theorem facetDatum_rev {y₀ : Fin p → ℚ} {ε : ℚ} (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε) :
    FacetDatum (farCore m').core (farCore (revMove m')).core degree (revMove m').base.1 y₀ ε := by
  have hshared := sharedContractionSlot_of_move (revMove m') (farCore_graph (revMove m'))
  rw [farCore_revMove, revMove_base] at hshared ⊢
  exact ⟨hshared, hd.point, hd.general', hd.general, hd.pos, hd.stable', hd.stable⟩

end Symmetry

section Reverse2

open MemberCertifiedPencil

variable {y₀ : Fin p → ℚ} {ε : ℚ}

/-- **`hRL` from the reversed move's receipts**, stated for an arbitrary name `c₂` of the
core the reversed move lands on. -/
theorem exists_odd_specializesLeft_of_receipts {c₁ c₂ : CubicCore n p}
    (m'' : c₁.graph.MoveData) (hback : farCore m'' = c₂)
    (hd : FacetDatum c₁.core (farCore m'').core degree m''.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (hrec : FacetLinkReceipts m'' hd hG (by omega))
    (l : FacetLimit c₂.core c₁.core y₀ degree) (x' : FrameClass c₁.core degree)
    (hx : x'.IsOdd) (hs : SpecializesRight x' l) :
    ∃ x : FrameClass c₂.core degree, x.IsOdd ∧ SpecializesLeft x l := by
  subst hback
  obtain ⟨x, hxo, hxs⟩ := exists_odd_specializesRight_of_receipts m'' hd hG hDegree hrec
    (FacetLimitSwap.swap l) x' hx (FacetLimitSwap.specializesRight_iff.mp hs)
  refine ⟨x, hxo, ?_⟩
  have := FacetLimitSwap.specializesRight_iff.mp hxs
  rwa [FacetLimitSwap.swap_swap] at this

/-! **Remark: the per-coarse-limit uniqueness hypotheses of the next theorem need not
hold, at valency three as well as four.**  A coarse (unlabelled, metric-free) facet limit
is a union of labelled metric limits, and it can carry two odd classes on each side.  The
implication stands; `ValencyThreeGeneral.facetParity_of_metricUniqueness` uses uniqueness
per labelled metric limit instead. -/
/-- **FacetParity at a valency-two/three facet datum from the two uniqueness halves and
the Part I receipts in both directions.**  This is `FacetParityPilot.facetParity_of_unique`
with its two existence halves (`hLR`, `hRL`) discharged by Stage A. -/
theorem facetParity_of_uniqueness_and_receipts {c : CubicCore n p} (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (huniqL : ∀ (l : FacetLimit c.core (farCore m').core y₀ degree)
      (x x' : FrameClass c.core degree),
      x.IsOdd → SpecializesLeft x l → x'.IsOdd → SpecializesLeft x' l → x = x')
    (huniqR : ∀ (l : FacetLimit c.core (farCore m').core y₀ degree)
      (x x' : FrameClass (farCore m').core degree),
      x.IsOdd → SpecializesRight x l → x'.IsOdd → SpecializesRight x' l → x = x')
    (hrec : FacetLinkReceipts m' hd hG (by omega))
    (hrec' : FacetLinkReceipts (revMove m') (facetDatum_rev m' hd) hG (by omega)) :
    FacetParity c.core (farCore m').core degree y₀ :=
  FacetParityPilot.facetParity_of_unique huniqL huniqR
    (exists_odd_specializesRight_of_receipts m' hd hG hDegree hrec)
    (exists_odd_specializesLeft_of_receipts (revMove m') (farCore_revMove m')
      (facetDatum_rev m' hd) hG hDegree hrec')

end Reverse2

/-! ## 10.  At the genus-six caterpillar step -/

section GenusSix

open DraismaVargas.Count.StepSupplyGenusSix (catCubicCore)
open DraismaVargas.Count.SegmentWalls (catFrame)

/-- `FacetMachine.catLoopCore` is literally the far core of `catLoopMove`. -/
theorem catLoopCore_eq_farCore : catLoopCore = farCore catLoopMove := rfl

/-- **A facet datum at `cat_step`'s contracted slot whose facet point is also
facet-generic** -- the datum the Stage A adapter runs at. -/
theorem cat_exists_facetDatum_generic :
    ∃ (y₀ : Fin (6 * 2 + 3) → ℚ) (ε : ℚ),
      FacetDatum catCubicCore.core catLoopCore.core (2 + 2) catLoopMove.base.1 y₀ ε ∧
        FacetGenericity.FacetGeneric (2 + 2) y₀ :=
  exists_facetDatum_generic catLoopMove (farCore_graph catLoopMove) (2 + 2)

/-- The caterpillar frame, as a regrowth at a facet point of any slot. -/
noncomputable def catRegrowth {e₀ : Fin (6 * 2 + 3)} {y₀ : Fin (6 * 2 + 3) → ℚ}
    (hpt : FacetPoint e₀ y₀) : Regrowth catCubicCore.core y₀ (2 + 2) :=
  ⟨catFrame 2, e₀, catFrame_degenerateAt_facet hpt⟩

/-- **Non-vacuity on the far side of `cat_step`.**  At a facet-generic facet datum of
`cat_step`, the Part I link at the caterpillar's regrowth is a frame over `catLoopCore`,
of odd multiplicity, open at the facet request and degenerating at the facet point in the
caterpillar's own column.  (`FacetMachine.cat_facetParity_domain` exhibits the near
side.) -/
theorem cat_exists_odd_far :
    ∃ (y₀ : Fin (6 * 2 + 3) → ℚ) (ε : ℚ),
      FacetDatum catCubicCore.core catLoopCore.core (2 + 2) catLoopMove.base.1 y₀ ε ∧
        FacetGenericity.FacetGeneric (2 + 2) y₀ ∧
        ∃ w' : Regrowth catLoopCore.core y₀ (2 + 2),
          w'.column = catLoopMove.base.1 ∧ (FrameClass.mk w'.frame).IsOdd ∧
            (FrameClass.mk w'.frame).OpenAt (facetRequest catLoopMove.base.1 y₀ ε) := by
  obtain ⟨y₀, ε, hd, hG⟩ := cat_exists_facetDatum_generic
  obtain ⟨w', hcol, -, -, hodd⟩ := exists_odd_farRegrowth catLoopMove hd hG (by norm_num)
    (catRegrowth hd.point) catFrame_isOdd
  exact ⟨y₀, ε, hd, hG, w', hcol, hodd,
    openAt_of_degenerateAt hd.point hd.general' hd.stable' hd.pos w'.degenerate⟩

/-- **The caterpillar step's obligation from the remaining hypotheses**: the two
uniqueness halves at the facet-generic facet datum (for the far side, the valency-three
uniqueness of Part II, `subsec-case-v3`) and the Part I receipts in both directions give
the per-step obligation of `TypeChangeSupplyPositive 4 10 15` at `cat_step`. -/
theorem cat_obligation_of_residues {y₀ : Fin (6 * 2 + 3) → ℚ} {ε : ℚ}
    (hd : FacetDatum catCubicCore.core catLoopCore.core (2 + 2) catLoopMove.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric (2 + 2) y₀)
    (huniqL : ∀ (l : FacetLimit catCubicCore.core catLoopCore.core y₀ (2 + 2))
      (x x' : FrameClass catCubicCore.core (2 + 2)),
      x.IsOdd → SpecializesLeft x l → x'.IsOdd → SpecializesLeft x' l → x = x')
    (huniqR : ∀ (l : FacetLimit catCubicCore.core catLoopCore.core y₀ (2 + 2))
      (x x' : FrameClass catLoopCore.core (2 + 2)),
      x.IsOdd → SpecializesRight x l → x'.IsOdd → SpecializesRight x' l → x = x')
    (hrec : FacetLinkReceipts catLoopMove hd hG (by norm_num))
    (hrec' : FacetLinkReceipts (revMove catLoopMove) (facetDatum_rev catLoopMove hd) hG
      (by norm_num)) :
    ∃ y y' : Fin (6 * 2 + 3) → ℚ, SimpleWallSupply.PositiveGeneral catCubicCore.core (2 + 2) y ∧
      SimpleWallSupply.PositiveGeneral catLoopCore.core (2 + 2) y' ∧
        CountTransportLink.CountLink (2 + 2) catCubicCore.core y catLoopCore.core y' :=
  FacetParityPilot.cat_obligation_of_facetParity_at hd
    (facetParity_of_uniqueness_and_receipts catLoopMove hd hG (by norm_num) huniqL huniqR
      hrec hrec')

end GenusSix

/-! ## 11.  Near-side uniqueness at the caterpillar step -/

section BallotTest

open DraismaVargas.Count.StepSupplyGenusSix (catCubicCore)

variable {c' : Core (4 * 2 + 2) (6 * 2 + 3)} {e₀ : Fin (6 * 2 + 3)} {y₀ : Fin (6 * 2 + 3) → ℚ}
  {ε : ℚ}

/-- **Every odd class specialising on the caterpillar side is a ballot member**, given a
ballot classification at the facet request (the upper bound of the base count at that
request; `ballotClassification_facet` below supplies it). -/
theorem ballot_of_specializesLeft
    (hd : FacetDatum catCubicCore.core c' (2 + 2) e₀ y₀ ε)
    (hBC : CaterpillarBallot.BallotClassification 2 (facetRequest e₀ y₀ ε))
    {l : FacetLimit catCubicCore.core c' y₀ (2 + 2)} {x : FrameClass catCubicCore.core (2 + 2)}
    (hx : x.IsOdd) (hs : SpecializesLeft x l) :
    ∃ s, x = FrameClass.mk (Frame.of (hBC.member s)) := by
  have hopen := openAt_of_specializesLeft hd.point hd.general hd.stable hd.pos hs
  obtain ⟨k, rfl⟩ := FrameClass.mk_surjective x
  obtain ⟨s, hs'⟩ := hBC.member_surjective (k.member (facetRequest e₀ y₀ ε)) hopen hx
  refine ⟨s, (CrossCoreTransport.fibreEquiv catCubicCore.core (2 + 2)
    (facetRequest e₀ y₀ ε)).injective ?_⟩
  change GeometricFibre.cls (k.member (facetRequest e₀ y₀ ε)) =
    GeometricFibre.cls ((Frame.of (hBC.member s)).member (facetRequest e₀ y₀ ε))
  rw [Frame.member_of]
  exact hs'.symm

/-- **Near-side uniqueness at the caterpillar step** follows from a ballot classification
at the facet request together with a finite fact: two ballot members specialising to one
facet limit are equal. -/
theorem cat_huniqL_of_ballot
    (hd : FacetDatum catCubicCore.core c' (2 + 2) e₀ y₀ ε)
    (hBC : CaterpillarBallot.BallotClassification 2 (facetRequest e₀ y₀ ε))
    (hinj : ∀ (s s' : Slopes (2 * (2 + 1))) (l : FacetLimit catCubicCore.core c' y₀ (2 + 2)),
      SpecializesLeft (FrameClass.mk (Frame.of (hBC.member s))) l →
      SpecializesLeft (FrameClass.mk (Frame.of (hBC.member s'))) l → s = s') :
    ∀ (l : FacetLimit catCubicCore.core c' y₀ (2 + 2)) (x x' : FrameClass catCubicCore.core (2 + 2)),
      x.IsOdd → SpecializesLeft x l → x'.IsOdd → SpecializesLeft x' l → x = x' := by
  intro l x x' hx hs hx' hs'
  obtain ⟨t, rfl⟩ := ballot_of_specializesLeft hd hBC hx hs
  obtain ⟨t', rfl⟩ := ballot_of_specializesLeft hd hBC hx' hs'
  rw [hinj t t' l hs hs']

/-- **The ballot classification at the facet request, with no hypothesis**
(`SheetLayerMatching.hSupply_genusSix` and
`TrivalentFibreUnique.diagonalClassification_genusSix_of_supply`): the facet request of
a facet datum is positive and general for the caterpillar, so the ballot classification
holds there. -/
noncomputable def ballotClassification_facet
    (hd : FacetDatum catCubicCore.core c' (2 + 2) e₀ y₀ ε) :
    CaterpillarBallot.BallotClassification 2 (facetRequest e₀ y₀ ε) :=
  BallotCoreIdentification.ballotClassification' 2 hd.positiveGeneral_left.1
    (TrivalentFibreUnique.diagonalClassification_genusSix_of_supply
      (SheetLayerMatching.hSupply_genusSix _ hd.positiveGeneral_left))

/-- **Near-side uniqueness at the caterpillar step, reduced to one finite fact**: two
ballot members specialising to one facet limit are equal.  The ballot classification is
supplied by `ballotClassification_facet`. -/
theorem cat_huniqL_of_limit_injective
    (hd : FacetDatum catCubicCore.core c' (2 + 2) e₀ y₀ ε)
    (hinj : ∀ (s s' : Slopes (2 * (2 + 1))) (l : FacetLimit catCubicCore.core c' y₀ (2 + 2)),
      SpecializesLeft (FrameClass.mk (Frame.of ((ballotClassification_facet hd).member s))) l →
      SpecializesLeft (FrameClass.mk (Frame.of ((ballotClassification_facet hd).member s'))) l →
        s = s') :
    ∀ (l : FacetLimit catCubicCore.core c' y₀ (2 + 2)) (x x' : FrameClass catCubicCore.core (2 + 2)),
      x.IsOdd → SpecializesLeft x l → x'.IsOdd → SpecializesLeft x' l → x = x' :=
  cat_huniqL_of_ballot hd (ballotClassification_facet hd) hinj

end BallotTest

end DraismaVargas.Count.FacetAdapterPilot
