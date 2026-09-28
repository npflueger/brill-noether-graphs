import DraismaVargasCount.GeneralKExitSetup

/-!
# The general-`K` background at a four-valent wall

Vargas, Part II (arXiv:2609.09109), the valency-4 limits of the section on changing
combinatorial type (Case `{v4-nd4}`): at a four-valent wall the members are indexed by
an integer `K`.  This module builds, for general `K`, the background resolution on which
the member of index `K` is constructed; it is an input of the type-change parity at
valency-four limits (step 3 of `Assembly`).

## What is proved

* **The census survives the gauge** (`gauged_blockDangling`): the guarded census
  survives the general-`K` gauge on every non-anchor block.  It needs no tree
  hypothesis: `datum_blockCard_eq_of_not_rel'` shows that every swap step relabels an
  edge partition by a block-preserving permutation or not at all
  (`swapStep_edgePartition_cases`), for *any* target edge.
* **The literal background is impossible in general** (`refines_of_literalBackground`,
  `gaugedBlock_subset_of_refines`, `not_exists_literalBackground`,
  `not_exists_literalBackground_of_K_zero`).  `PairingBackground.exterior` is a
  *global* refinement, and the canonical r0-nd3 resolution of an ordinary block
  puts the whole edge partition of that block's singleton branch `s` on its
  side.  So the literal equality `geometry.resolution block =
  blockwiseResolution … block` forces the partner `t` of `s` to refine `s`
  everywhere, in particular on the anchor block, where it forces the gauged class
  of `t` inside that of `s` once `k_t ≥ 2`.  At `K = 0` with `s, t` on the
  minus side this contradicts `|A₋| = |gB_t ∪ gB_s|` (`K + 1 = k_t` would be
  forced).  This is exactly why the `K = 0` background
  (`KZero.BlockLocalBackground.pairingBackground`) *localizes* each canonical
  resolution to its own wall block.
* **The background, in its true shape** (`canonicalLocal`, `localBackground`,
  `exists_pairingBackground`): the background exists with, on every non-anchor
  block, the canonical W4 resolution *localized* to that block (`localize`, the
  generic form of `KZero.BlockLocalBackground.localizedResolution`).
* **Source genus** (`candidate_sourceGenus_of_local`): over the localized
  background the candidate keeps the source genus of the gauged datum.
* **The candidate** (`exists_valid_candidate`): the general-`K` candidate exists
  with no background hypothesis.

## What is NOT proved

* The impossibility of the literal background is **conditional**: its premise is an
  ordinary r0-nd3 block above the same four-valent wall vertex whose singleton
  branch has a same-side partner of index at least two (and, for the `K = 0`
  corollary, a position from `exists_position`).  No concrete gluing datum
  realising that configuration is built here.
* The hypotheses of the main theorems are those of the `K = 0` construction: a
  connected genus-zero target (`hConnected`, `hGenus`, for the branch swaps),
  `hNoGlue`, incoming validity `hValid`, and the guarded census `profile`.  At an
  actual wall all are discharged by `NonTrivalentUniqueFourValent` (see
  `GeneralKSourceFacts`).
* Nothing here is about trivalence, path ends or danglingness of the candidate;
  those are in `GeneralKSourceFacts`.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.GeneralKBackground

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.Count.GeneralKReceipts

/-! ## 0.  Swap steps change an edge partition by relabelling or not at all -/

section Steps

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

theorem swapStep_edgePartition_cases (star : W4TargetPairings.FourStar target wall)
    (current : GluingDatum target degree) (label : Fin 4)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (current.vertexPartition wall).Rel (permutation sheet) sheet)
    (edge : target.edges) :
    (swapStep star current label permutation hFix).edgePartition edge =
        current.edgePartition edge ∨
      (swapStep star current label permutation hFix).edgePartition edge =
        (current.edgePartition edge).relabel permutation := by
  unfold swapStep
  cases hMoved : TargetBranchRegion.edgeMoved wall
      (TargetSeparation.farEndpoint wall (star.edge label))
      (TargetSeparation.farEndpoint_ne (selectedEdge_incident (star := star) label)) edge
  · exact Or.inl (BlockPreservingBranchSwap.branchSwapOfPerm_edgePartition_of_fixed _ _ _ _ _ _
      _ hMoved)
  · exact Or.inr (BlockPreservingBranchSwap.branchSwapOfPerm_edgePartition_of_moved _ _ _ _ _ _
      _ hMoved)

theorem blockCard_swapStep_of_fixed (star : W4TargetPairings.FourStar target wall)
    (current : GluingDatum target degree) (label : Fin 4)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (current.vertexPartition wall).Rel (permutation sheet) sheet)
    (edge : target.edges) (sheet : Fin degree) (hSheet : permutation sheet = sheet) :
    ((swapStep star current label permutation hFix).edgePartition edge).blockCard sheet =
      (current.edgePartition edge).blockCard sheet := by
  rcases swapStep_edgePartition_cases star current label permutation hFix edge with h | h
  · rw [h]
  · rw [h]
    have hCard := SheetPartition.relabel_blockCard (current.edgePartition edge) permutation sheet
    rw [hSheet] at hCard
    exact hCard

end Steps

/-! ## 0b.  Localizing a block resolution to its own wall block

This is `NonTrivalentValencyFourKZero.PrescribedPairing.BlockLocalBackground`'s
`localizedResolution`, stated for an arbitrary coarse partition: paste the
resolution on its own wall block and the joined resolution everywhere else. -/

section Localize

variable {degree : ℕ}

/-- The resolution `R` localized to the wall block of `block`. -/
noncomputable def localize (coarse : SheetPartition degree) (block : Fin degree)
    (R : LocalResolution degree) (hR : R.ContractsTo coarse) : LocalResolution degree :=
  LocalResolution.paste coarse
    (LocalResolution.onBlock coarse block R (fun _ ↦ joinedResolutionAt coarse))
    (LocalResolution.onBlock_contracts coarse block R (fun _ ↦ joinedResolutionAt coarse) hR
      (fun _ ↦ joinedResolutionAt_contracts coarse))

variable (coarse : SheetPartition degree) (block : Fin degree) (R : LocalResolution degree)
  (hR : R.ContractsTo coarse)

theorem localize_contracts : (localize coarse block R hR).ContractsTo coarse :=
  LocalResolution.paste_contracts _ _ _

/-- Block-local refinement of the left endpoint becomes global refinement of
the localized left endpoint. -/
theorem refines_localize_left (fine : SheetPartition degree) (hFine : fine.Refines coarse)
    (hLocal : fine.RefinesOnBlock R.left coarse block) :
    fine.Refines (localize coarse block R hR).left := by
  intro first second hRel
  change (coarse.paste (fun other ↦
      (LocalResolution.onBlock coarse block R (fun _ ↦ joinedResolutionAt coarse) other).left)
      (fun other ↦ (LocalResolution.onBlock_contracts coarse block R
        (fun _ ↦ joinedResolutionAt coarse) hR
        (fun _ ↦ joinedResolutionAt_contracts coarse) other).left_refines)).Rel first second
  rw [coarse.paste_rel_iff]
  by_cases hOther : coarse.Rel block (coarse.repr first)
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hOther]
    exact hLocal.rel (hOther.trans (coarse.rel_repr_left first)) hRel
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hOther]
    exact hFine.rel hRel

theorem refines_localize_right (fine : SheetPartition degree) (hFine : fine.Refines coarse)
    (hLocal : fine.RefinesOnBlock R.right coarse block) :
    fine.Refines (localize coarse block R hR).right := by
  intro first second hRel
  change (coarse.paste (fun other ↦
      (LocalResolution.onBlock coarse block R (fun _ ↦ joinedResolutionAt coarse) other).right)
      (fun other ↦ (LocalResolution.onBlock_contracts coarse block R
        (fun _ ↦ joinedResolutionAt coarse) hR
        (fun _ ↦ joinedResolutionAt_contracts coarse) other).right_refines)).Rel first second
  rw [coarse.paste_rel_iff]
  by_cases hOther : coarse.Rel block (coarse.repr first)
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hOther]
    exact hLocal.rel (hOther.trans (coarse.rel_repr_left first)) hRel
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hOther]
    exact hFine.rel hRel

/-- On a sheet of its own block the localized resolution is `R`. -/
theorem localize_onBlock_repr (sheet : Fin degree) (hSheet : coarse.Rel block sheet) :
    LocalResolution.onBlock coarse block R (fun _ ↦ joinedResolutionAt coarse)
        (coarse.repr sheet) = R :=
  LocalResolution.onBlock_of_rel _ _ _ _ _ (hSheet.trans (coarse.rel_repr_right sheet))

theorem localize_left_riemannHurwitz (external : List (SheetPartition degree))
    (hLocal : LocalResolution.RiemannHurwitzAtBlock coarse R.left (R.newEdge :: external) block) :
    LocalResolution.RiemannHurwitzAtBlock coarse (localize coarse block R hR).left
      ((localize coarse block R hR).newEdge :: external) block := by
  classical
  intro sheet hSheet
  have hLoc := hLocal sheet hSheet
  have hOn := localize_onBlock_repr coarse block R sheet hSheet
  simp only [List.map_cons, List.sum_cons, List.length_cons] at hLoc ⊢
  unfold localize
  rw [LocalResolution.paste_newEdge_blockCountWithin_left,
    LocalResolution.paste_left_blockCard]
  simp_rw [LocalResolution.blockCountWithin_paste_left]
  rw [hOn]
  exact hLoc

theorem localize_right_riemannHurwitz (external : List (SheetPartition degree))
    (hLocal : LocalResolution.RiemannHurwitzAtBlock coarse R.right (R.newEdge :: external)
      block) :
    LocalResolution.RiemannHurwitzAtBlock coarse (localize coarse block R hR).right
      ((localize coarse block R hR).newEdge :: external) block := by
  classical
  intro sheet hSheet
  have hLoc := hLocal sheet hSheet
  have hOn := localize_onBlock_repr coarse block R sheet hSheet
  simp only [List.map_cons, List.sum_cons, List.length_cons] at hLoc ⊢
  unfold localize
  rw [LocalResolution.paste_newEdge_blockCountWithin_right,
    LocalResolution.paste_right_blockCard]
  simp_rw [LocalResolution.blockCountWithin_paste_right]
  rw [hOn]
  exact hLoc

/-- The blockwise Euler identity transfers from `R` to its localization on
`R`'s own (canonical) block. -/
theorem localize_euler (hEuler : R.newEdge.blockCountWithin coarse block + 1 =
      R.left.blockCountWithin coarse block + R.right.blockCountWithin coarse block)
    (hCanonical : coarse.repr block = block) :
    (localize coarse block R hR).newEdge.blockCountWithin coarse block + 1 =
      (localize coarse block R hR).left.blockCountWithin coarse block +
        (localize coarse block R hR).right.blockCountWithin coarse block := by
  unfold localize
  rw [LocalResolution.pasteNewEdge_blockCountWithin,
    LocalResolution.pasteLeft_blockCountWithin,
    LocalResolution.pasteRight_blockCountWithin, hCanonical,
    LocalResolution.onBlock_of_rel _ _ _ _ _ (rfl : coarse.Rel block block)]
  exact hEuler

end Localize

/-! ## A.  The background over the general-`K` gauge -/

section Background

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : W4TargetPairings.FourStar target wall}
  {anchor : W4Assembly.WallBlock data wall}
  {source : FourBranchAnchor data star anchor} {pairing : Fin 3} {side : Bool}
  (position : Position source pairing side)
  (profile : NonTrivalentValencyFourBackground.OrdinaryBlockProfile data star anchor.1)

/-- Off the anchor block the general-`K` gauge does not change any edge class
cardinality, for *any* target edge and without a tree hypothesis: every swap
step relabels by a block-preserving permutation, which fixes the sheet. -/
theorem datum_blockCard_eq_of_not_rel' (edge : target.edges) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel anchor.1 sheet) :
    (position.datum.edgePartition edge).blockCard sheet =
      (data.edgePartition edge).blockCard sheet := by
  have hFixed : ∀ label, position.gauge.perm label sheet = sheet := fun label ↦
    (position.gauge.preserving label).2 sheet
      (fun hMem ↦ hSheet (((data.vertexPartition wall).mem_block_iff _ _).mp hMem))
  have h3 := blockCard_swapStep_of_fixed star (position.gauge.stage3 star) 3
    (position.gauge.perm 3) (fun sheet ↦ by
      rw [LabelGauge.stage3_wall]; exact position.gauge.fix 3 sheet) edge sheet (hFixed 3)
  have h2 := blockCard_swapStep_of_fixed star (position.gauge.stage2 star) 2
    (position.gauge.perm 2) (fun sheet ↦ by
      rw [LabelGauge.stage2_wall]; exact position.gauge.fix 2 sheet) edge sheet (hFixed 2)
  have h1 := blockCard_swapStep_of_fixed star (position.gauge.stage1 star) 1
    (position.gauge.perm 1) (fun sheet ↦ by
      rw [LabelGauge.stage1_wall]; exact position.gauge.fix 1 sheet) edge sheet (hFixed 1)
  have h0 := blockCard_swapStep_of_fixed star data 0
    (position.gauge.perm 0) (position.gauge.fix 0) edge sheet (hFixed 0)
  exact h3.trans (h2.trans (h1.trans h0))

/-- **The census survives the gauge.**  The guarded census survives the general-`K` gauge on every block
that is not the anchor's. -/
theorem gauged_blockDangling (block : Fin degree)
    (hBlock : ¬(data.vertexPartition wall).Rel anchor.1 block) :
    NonTrivalentValencyFourBackground.BlockDangling position.datum star profile.pattern
      block := by
  have hBase := profile.blockDangling block hBlock
  have hWall := position.datum_vertexPartition_wall
  have hTransfer : ∀ (label : Fin 4) (sheet : Fin degree),
      (position.datum.vertexPartition wall).Rel block sheet →
        (position.datum.edgePartition (star.edge label)).blockCard sheet =
          (data.edgePartition (star.edge label)).blockCard sheet ∧
          (data.vertexPartition wall).Rel block sheet := by
    intro label sheet hRel
    rw [hWall] at hRel
    have hNot : ¬(data.vertexPartition wall).Rel anchor.1 sheet := by
      intro hAnchor
      exact hBlock (hAnchor.trans hRel.symm)
    exact ⟨datum_blockCard_eq_of_not_rel' position (star.edge label) sheet hNot, hRel⟩
  constructor
  · intro nd2block hPattern label hFirst hSecond sheet hSheet
    obtain ⟨hCard, hRel⟩ := hTransfer label sheet hSheet
    rw [hCard]
    exact hBase.nd2_singleton nd2block hPattern label hFirst hSecond sheet hRel
  · intro nd3block hPattern label hFirst hSecond hThird sheet hSheet
    obtain ⟨hCard, hRel⟩ := hTransfer label sheet hSheet
    rw [hCard]
    exact hBase.nd3_singleton nd3block hPattern label hFirst hSecond hThird sheet hRel

/-! ### The literal background is impossible in general

A natural candidate is a `PairingBackground` whose resolution *is*
`W4Assembly.blockwiseResolution` on every non-anchor block.  The field
`PairingBackground.exterior` is a **global** refinement, while the canonical
r0-nd3 resolution of an ordinary block puts the *whole* edge partition of that
block's singleton branch on the singleton's side.  So the literal equality
forces the partner branch on that side to refine the singleton branch
everywhere -- in particular on the anchor block, where the gauge has just
placed the two classes with a prescribed overlap.  This is exactly why the
`K = 0` background (`KZero.BlockLocalBackground.pairingBackground`)
*localizes* each canonical resolution to its own wall block. -/

/-- The literal background forces a global refinement between the two
branches on the singleton side of every ordinary r0-nd3 block. -/
theorem refines_of_literalBackground
    (geometry : PairingBackground position.datum star pairing anchor.1)
    (hLit : ∀ block, ¬(position.datum.vertexPartition wall).Rel anchor.1 block →
      geometry.resolution block =
        W4Assembly.blockwiseResolution position.datum star profile.pattern pairing block)
    (block : Fin degree) (hBlock : ¬(position.datum.vertexPartition wall).Rel anchor.1 block)
    (nd3 : W4Assembly.Nd3Block) (hPattern : profile.pattern block = .nd3 nd3)
    (label : Fin 4)
    (hSide : W4TargetPairings.Pairing.labelRight pairing label =
      W4TargetPairings.Pairing.labelRight pairing (nd3.singletonLabel pairing)) :
    (position.datum.edgePartition (star.edge label)).Refines
      (position.datum.edgePartition (star.edge (nd3.singletonLabel pairing))) := by
  have h := geometry.exterior (star.edge label)
    ((GluingContraction.mem_incidentEdges_iff wall _).mp (star.edge_mem_incidentEdges label))
    block hBlock
  rw [hLit block hBlock] at h
  unfold W4Assembly.blockwiseResolution at h
  rw [hPattern] at h
  simp only [W4Assembly.resolutionAt, ResolutionW4.nd3ResolutionForPairing,
    W4TargetPairings.FourStar.right_edge] at h
  rwa [ResolutionW4.nd3Resolution_endpoint_of_same_side _ _ _ _ _ hSide] at h

variable (hConnected : graph_connected target) (hGenus : genus target = 0)
  (hNoGlue : W4StableSource.DanglingEdgeNoGlue data)

include hConnected hGenus hNoGlue in
/-- On the anchor block, a relabelled branch occurrence that refines another
one with a class of at least two sheets has its gauged class *inside* the
other's gauged class. -/
theorem gaugedBlock_subset_of_refines {label other : Fin 4}
    (hRefines : (position.datum.edgePartition (star.edge label)).Refines
      (position.datum.edgePartition (star.edge other)))
    (hTwo : 2 ≤ source.index label) :
    gaugedBlock source position.gauge label ⊆ gaugedBlock source position.gauge other := by
  classical
  intro x hx
  have hCard : (gaugedBlock source position.gauge label).card = source.index label := by
    unfold gaugedBlock
    rw [Finset.card_image_of_injective _ (position.gauge.perm label).injective]
    rfl
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ gaugedBlock source position.gauge label, y ≠ x := by
    by_contra hNone
    simp only [not_exists, not_and, not_not] at hNone
    have hSub : gaugedBlock source position.gauge label ⊆ {x} := fun z hz ↦
      Finset.mem_singleton.mpr (hNone z hz)
    have := Finset.card_le_card hSub
    rw [Finset.card_singleton] at this
    omega
  have hRelLabel : (gaugedEdge star position.gauge label).Rel x y :=
    ((gaugedEdge_rel_of_mem source position.gauge label hx).symm).trans
      (gaugedEdge_rel_of_mem source position.gauge label hy)
  have hRelLabel' : (position.datum.edgePartition (star.edge label)).Rel x y := by
    show ((position.gauge.gaugedData star).edgePartition (star.edge label)).Rel x y
    rw [position.gauge.gaugedData_edgePartition star hConnected hGenus label]
    exact hRelLabel
  have hRelOther' := hRefines.rel hRelLabel'
  have hRelOther : (gaugedEdge star position.gauge other).Rel x y := by
    have h : ((position.gauge.gaugedData star).edgePartition (star.edge other)).Rel x y :=
      hRelOther'
    rw [position.gauge.gaugedData_edgePartition star hConnected hGenus other] at h
    exact h
  have hWall : (data.vertexPartition wall).Rel anchor.1 x :=
    ((data.vertexPartition wall).mem_block_iff _ _).mp
      (gaugedBlock_subset_wall source position.gauge label hx)
  rcases gaugedEdge_shape source position.gauge hNoGlue other x hWall with hIn | hSingle
  · exact hIn
  · exfalso
    have hyMem : y ∈ (gaugedEdge star position.gauge other).block x :=
      ((gaugedEdge star position.gauge other).mem_block_iff _ _).mpr hRelOther
    rw [hSingle, Finset.mem_singleton] at hyMem
    exact hyx hyMem

include hConnected hGenus hNoGlue in
/-- **The literal background is impossible.**  If some ordinary block carries the
r0-nd3 pattern, its singleton branch `s` has a partner `t` on the same side of
the prescribed pairing with `k_t ≥ 2`, and the gauge did not place the class of
`t` inside that of `s`, then **no** `PairingBackground` over the gauged datum
is the canonical blockwise resolution on every non-anchor block. -/
theorem not_exists_literalBackground
    (block : Fin degree) (hBlock : ¬(position.datum.vertexPartition wall).Rel anchor.1 block)
    (nd3 : W4Assembly.Nd3Block) (hPattern : profile.pattern block = .nd3 nd3)
    (label : Fin 4)
    (hSide : W4TargetPairings.Pairing.labelRight pairing label =
      W4TargetPairings.Pairing.labelRight pairing (nd3.singletonLabel pairing))
    (hTwo : 2 ≤ source.index label)
    (hNotSub : ¬gaugedBlock source position.gauge label ⊆
      gaugedBlock source position.gauge (nd3.singletonLabel pairing)) :
    ¬∃ geometry : PairingBackground position.datum star pairing anchor.1,
      ∀ block, ¬(position.datum.vertexPartition wall).Rel anchor.1 block →
        geometry.resolution block =
          W4Assembly.blockwiseResolution position.datum star profile.pattern pairing block := by
  rintro ⟨geometry, hLit⟩
  exact hNotSub (gaugedBlock_subset_of_refines position hConnected hGenus hNoGlue
    (refines_of_literalBackground position profile geometry hLit block hBlock nd3 hPattern
      label hSide) hTwo)

omit hConnected hGenus hNoGlue in
/-- The numerical form at the positions produced by `exists_position`, whose
minus side is exactly the union of its two gauged classes: if one minus class
lies inside the other, then `K + 1` is the smaller index.  So at `K = 0` (always
admissible) the literal background fails as soon as the partner has index at least two. -/
theorem K_succ_eq_of_subset {first second : Fin 4}
    (hFirst : W4TargetPairings.Pairing.labelRight pairing first = side)
    (hSecond : W4TargetPairings.Pairing.labelRight pairing second = side)
    (hNe : first ≠ second)
    (hMinus : position.split.minusSheets =
      gaugedBlock source position.gauge first ∪ gaugedBlock source position.gauge second)
    (hSub : gaugedBlock source position.gauge first ⊆ gaugedBlock source position.gauge second) :
    position.split.K + 1 = source.index first := by
  have hCard : ∀ label, (gaugedBlock source position.gauge label).card = source.index label := by
    intro label
    unfold gaugedBlock
    rw [Finset.card_image_of_injective _ (position.gauge.perm label).injective]
    rfl
  have hUnion : position.split.minusSheets.card = source.index second := by
    rw [hMinus, Finset.union_eq_right.mpr hSub, hCard]
  have hSideSum : sideIndex source pairing side = source.index first + source.index second := by
    rw [sideIndex_eq_add source pairing side]
    rcases eq_first_or_second pairing first with h1 | h1 <;>
      rcases eq_first_or_second pairing second with h2 | h2 <;>
      rw [hFirst] at h1 <;> rw [hSecond] at h2
    · exact absurd (h1.trans h2.symm) hNe
    · rw [h1, h2]
    · rw [h1, h2, add_comm]
    · exact absurd (h1.trans h2.symm) hNe
  have := position.minus_card
  omega


include hConnected hGenus hNoGlue in
/-- **The literal background is impossible at the bottom of the range.**  At a position
whose minus side is the union of its two gauged classes (every position produced
by `exists_position`) with `K = 0` (always admissible, `admissible_zero`), if an
ordinary block carries the r0-nd3 pattern whose singleton branch lies on the
minus side, and its partner there has index at least two, then no
`PairingBackground` is literally the canonical blockwise resolution on every
non-anchor block. -/
theorem not_exists_literalBackground_of_K_zero
    (hMinus : position.split.minusSheets =
      gaugedBlock source position.gauge (firstLabel pairing side) ∪
        gaugedBlock source position.gauge (secondLabel pairing side))
    (hK : position.split.K = 0)
    (block : Fin degree) (hBlock : ¬(position.datum.vertexPartition wall).Rel anchor.1 block)
    (nd3 : W4Assembly.Nd3Block) (hPattern : profile.pattern block = .nd3 nd3)
    (hSingletonSide : W4TargetPairings.Pairing.labelRight pairing (nd3.singletonLabel pairing) =
      side)
    (label : Fin 4) (hLabelSide : W4TargetPairings.Pairing.labelRight pairing label = side)
    (hNe : label ≠ nd3.singletonLabel pairing) (hTwo : 2 ≤ source.index label) :
    ¬∃ geometry : PairingBackground position.datum star pairing anchor.1,
      ∀ block, ¬(position.datum.vertexPartition wall).Rel anchor.1 block →
        geometry.resolution block =
          W4Assembly.blockwiseResolution position.datum star profile.pattern pairing block := by
  rintro ⟨geometry, hLit⟩
  have hSub := gaugedBlock_subset_of_refines position hConnected hGenus hNoGlue
    (refines_of_literalBackground position profile geometry hLit block hBlock nd3 hPattern
      label (hLabelSide.trans hSingletonSide.symm)) hTwo
  have hMinus' : position.split.minusSheets =
      gaugedBlock source position.gauge label ∪
        gaugedBlock source position.gauge (nd3.singletonLabel pairing) := by
    rw [hMinus]
    rcases eq_first_or_second pairing label with h1 | h1 <;>
      rcases eq_first_or_second pairing (nd3.singletonLabel pairing) with h2 | h2 <;>
      rw [hLabelSide] at h1 <;> rw [hSingletonSide] at h2
    · exact absurd (h1.trans h2.symm) hNe
    · rw [← h1, ← h2]
    · rw [← h1, ← h2, Finset.union_comm]
    · exact absurd (h1.trans h2.symm) hNe
  have hEq := K_succ_eq_of_subset position hLabelSide hSingletonSide hNe hMinus' hSub
  omega

/-! ### The background in its true shape: the localized canonical background -/

/-- The canonical W4 resolution of `block`, localized to its own wall block
(the shape of the `K = 0` background). -/
noncomputable def canonicalLocal (gData : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → W4Assembly.BlockPattern) (pairing : Fin 3) (block : Fin degree) :
    LocalResolution degree :=
  localize (gData.vertexPartition wall) block
    (W4Assembly.blockwiseResolution gData star pattern pairing block)
    (W4Assembly.blockwiseResolution_contracts gData star pattern pairing block)

omit hConnected hGenus hNoGlue in
theorem canonicalLocal_euler (gData : GluingDatum target degree)
    (pattern : Fin degree → W4Assembly.BlockPattern) (block : Fin degree)
    (hCanonical : (gData.vertexPartition wall).repr block = block) :
    (canonicalLocal gData star pattern pairing block).newEdge.blockCountWithin
        (gData.vertexPartition wall) block + 1 =
      (canonicalLocal gData star pattern pairing block).left.blockCountWithin
          (gData.vertexPartition wall) block +
        (canonicalLocal gData star pattern pairing block).right.blockCountWithin
          (gData.vertexPartition wall) block :=
  localize_euler _ _ _ _
    (NonTrivalentValencyFourRows.euler_of_isStar
      (NonTrivalentValencyFourRows.isStar_blockwiseResolution (star := star) pairing
        pattern block) block) hCanonical

/-- The localized canonical background over the general-`K` gauged datum. -/
noncomputable def localBackground (hValid : data.Valid) :
    PairingBackground position.datum star pairing anchor.1 where
  resolution := fun block ↦
    if (position.datum.vertexPartition wall).Rel anchor.1 block then
      joinedResolutionAt (position.datum.vertexPartition wall)
    else canonicalLocal position.datum star profile.pattern pairing block
  contracts := by
    intro block hBlock
    simp only [hBlock, if_false]
    exact localize_contracts _ _ _ _
  exterior := by
    intro edge hIncident block hBlock
    simp only [hBlock, if_false]
    have hBlock' : ¬(data.vertexPartition wall).Rel anchor.1 block := by
      rwa [position.datum_vertexPartition_wall] at hBlock
    have hLocal := (gauged_blockDangling position profile block hBlock').exterior pairing edge
      hIncident
    have hFine : (position.datum.edgePartition edge).Refines
        (position.datum.vertexPartition wall) :=
      W4StableSource.edgePartition_refines_of_mem_incidentEdges _ wall edge
        ((GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident)
    cases hSide : star.right pairing edge
    · rw [hSide] at hLocal
      exact refines_localize_left _ _ _ _ _ hFine hLocal
    · rw [hSide] at hLocal
      exact refines_localize_right _ _ _ _ _ hFine hLocal
  left_riemannHurwitz := by
    intro block _hCanonical hBlock
    simp only [hBlock, if_false]
    have hBlock' : ¬(data.vertexPartition wall).Rel anchor.1 block := by
      rwa [position.datum_vertexPartition_wall] at hBlock
    apply localize_left_riemannHurwitz
    intro sheet hSheet
    have hCounts :
        (((W4Assembly.blockwiseResolution position.datum star profile.pattern pairing
              block).newEdge ::
            (star.leftEdges pairing).map position.datum.edgePartition).map
          (fun edge ↦ (edge.blockCountWithin
            (W4Assembly.blockwiseResolution position.datum star profile.pattern pairing
              block).left sheet : ℤ))).sum ≥
          ((W4Assembly.blockwiseResolution position.datum star profile.pattern pairing
            block).left.blockCard sheet : ℤ) + 2 := by
      simpa [W4Assembly.oldEdgesAtSide, W4Assembly.endpointAtSide] using
        (gauged_blockDangling position profile block hBlock').countAtSide
          ((position.datum_valid hValid).2 wall) pairing sheet hSheet false
    have hLength :
        ((W4Assembly.blockwiseResolution position.datum star profile.pattern pairing
            block).newEdge ::
          (star.leftEdges pairing).map position.datum.edgePartition).length = 3 := by
      simp
    rw [hLength]
    omega
  right_riemannHurwitz := by
    intro block _hCanonical hBlock
    simp only [hBlock, if_false]
    have hBlock' : ¬(data.vertexPartition wall).Rel anchor.1 block := by
      rwa [position.datum_vertexPartition_wall] at hBlock
    apply localize_right_riemannHurwitz
    intro sheet hSheet
    have hCounts :
        (((W4Assembly.blockwiseResolution position.datum star profile.pattern pairing
              block).newEdge ::
            (star.rightEdges pairing).map position.datum.edgePartition).map
          (fun edge ↦ (edge.blockCountWithin
            (W4Assembly.blockwiseResolution position.datum star profile.pattern pairing
              block).right sheet : ℤ))).sum ≥
          ((W4Assembly.blockwiseResolution position.datum star profile.pattern pairing
            block).right.blockCard sheet : ℤ) + 2 := by
      simpa [W4Assembly.oldEdgesAtSide, W4Assembly.endpointAtSide] using
        (gauged_blockDangling position profile block hBlock').countAtSide
          ((position.datum_valid hValid).2 wall) pairing sheet hSheet true
    have hLength :
        ((W4Assembly.blockwiseResolution position.datum star profile.pattern pairing
            block).newEdge ::
          (star.rightEdges pairing).map position.datum.edgePartition).length = 3 := by
      simp
    rw [hLength]
    omega

omit hConnected hGenus hNoGlue in
/-- **The background, in its true shape.**  The rigid background exists over the general-`K`
gauged datum, and on every non-anchor block it is the canonical W4 resolution
*localized to that block* -- exactly the shape of the `K = 0` background.
(The literal equality with `blockwiseResolution` is false in general:
`not_exists_literalBackground`.) -/
theorem exists_pairingBackground (hValid : data.Valid) :
    ∃ geometry : PairingBackground position.datum star pairing anchor.1,
      ∀ block, ¬(position.datum.vertexPartition wall).Rel anchor.1 block →
        geometry.resolution block =
          canonicalLocal position.datum star profile.pattern pairing block :=
  ⟨localBackground position profile hValid, fun _ hBlock ↦ if_neg hBlock⟩

include hConnected hGenus hNoGlue in
/-- **Source genus.**  Over the *localized* canonical background the
general-`K` candidate keeps the source genus of the gauged datum. -/
theorem candidate_sourceGenus_of_local
    (geometry : PairingBackground position.datum star pairing anchor.1)
    (hBg : ∀ block, ¬(position.datum.vertexPartition wall).Rel anchor.1 block →
      geometry.resolution block = canonicalLocal position.datum star profile.pattern pairing block) :
    genus (position.candidate hConnected hGenus hNoGlue geometry).datum.sourceGraph =
      genus position.datum.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_blockwise_euler
  intro block hCanonical
  by_cases hBlock : (position.datum.vertexPartition wall).Rel anchor.1 block
  · rw [position.candidate_resolution_of_wall_rel hConnected hGenus hNoGlue geometry block
      hBlock, position.datum_vertexPartition_wall]
    rw [position.datum_vertexPartition_wall] at hBlock
    exact position.selected_euler block hBlock
  · have hRes : (position.candidate hConnected hGenus hNoGlue geometry).resolution block =
        geometry.resolution block := by
      unfold Position.candidate GeneralKReceipts.PairingBackground.background
        GlobalM11Arbitrary.Background.install
      exact LocalResolution.onBlock_of_not_rel _ _ _ _ _ hBlock
    rw [hRes, hBg block hBlock]
    exact canonicalLocal_euler position.datum profile.pattern block hCanonical

include profile hConnected hGenus hNoGlue in
/-- **The candidate.**  With the background, the general-`K` candidate exists with no background
hypothesis.  It is valid, it keeps the source genus of the gauged datum, and it
records `K`. -/
theorem exists_valid_candidate (hValid : data.Valid) :
    ∃ geometry : PairingBackground position.datum star pairing anchor.1,
      (position.candidate hConnected hGenus hNoGlue geometry).datum.Valid ∧
      genus (position.candidate hConnected hGenus hNoGlue geometry).datum.sourceGraph =
        genus position.datum.sourceGraph ∧
      ((position.candidate hConnected hGenus hNoGlue geometry).resolution
          anchor.1).newEdge.blockCountWithin (position.endpoint side) position.split.bridge =
        position.split.K + 1 ∧
      (position.candidate hConnected hGenus hNoGlue geometry).datum.sourceEdgeIndex
          ((position.candidate hConnected hGenus hNoGlue geometry).newSourceEdge
            position.split.bridge) + 2 * position.split.K + 1 =
        sideIndex source pairing side := by
  obtain ⟨geometry, hGeometry⟩ := exists_pairingBackground position profile hValid
  exact ⟨geometry, position.candidate_datum_valid hConnected hGenus hNoGlue geometry hValid,
    candidate_sourceGenus_of_local position profile hConnected hGenus hNoGlue geometry hGeometry,
    (position.candidate_K_receipts hConnected hGenus hNoGlue geometry).1,
    position.candidate_newSourceEdge_index hConnected hGenus hNoGlue geometry⟩

end Background

end DraismaVargas.Count.GeneralKBackground
