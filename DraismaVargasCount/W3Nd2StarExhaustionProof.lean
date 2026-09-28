import DraismaVargasCount.M11StarExhaustionProof
import DraismaVargasCount.W3Nd2StarCensusProof

/-!
# W3 nd2 star exhaustion: the `w3Nd2CoarseFine` clause with no hypothesis

Source: Draisma--Vargas Part I (arXiv:1909.12924), Case `{w3-r1-nd2}`, Figure 31 and
Equation (5), and `lemma-dangling-no-glue`; Vargas, Part II (arXiv:2609.09109), the star of a
wall.  The argument follows `M11StarExhaustionProof`; the census reduction it completes is
`W3Nd2StarCensusProof`.

## The result, in one paragraph

`W3Nd2StarCensusProof` reduces `FamilyStarParity (2+2) (4*2+2) (6*2+3) .w3Nd2CoarseFine` to
`W3Nd2StarExhaustion`, and that to one `PositionTransport` per star member.  Here every
member receives one.  The wall's W3 input and nd2 profile pull back along the member's
limit isomorphism (§1); Part I's identification (`W3Nd2IncomingMemberMatching`) read at the
member then says its local resolution has the **coarse** or the **fine** shape of Figure 31
(§5), each written as a relation piecewise on the distinguished block (§2, §3).  The
relational builder `M11StarExhaustionProof.nonempty_transportFree_of_rel` turns shapes into a
`ResolutionExpansionFree.TransportFree` (§4).  A
coarse-type member needs nothing more.  A fine-type member needs one more thing, which is
**not** automatic: the fine position's trivalent end carries the small direction's partition
`{A^(q), {x}}` of the distinguished block, and the third direction is discrete and entirely
dangling there, so the limit isomorphism's third-direction occurrence permutation must agree
with the small direction's modulo that partition (`Coherent`; necessary, by
`coherent_of_transportFree`).  A given limit isomorphism need not be coherent, but one can
always be re-chosen: by Part I's dangling-no-glue (proved for full-dimensional data, and
carried to the limit away from the wall through the contraction forest) every sheet of the
distinguished block is a singleton, dangling sheet over the whole third branch (§10, §11),
so permuting those sheets on that branch is a limit automorphism fixing every branch vertex
and stable path (§9); composing with the right one makes any isomorphism coherent (§12).
Hence `w3Nd2StarExhaustion`, `w3Nd2StarCensus` and `familyStarParity_w3Nd2` with no
hypothesis (§13).

## What is proved

* §1 `pullbackThreeStar`, `input_pullback`, `distinguishedBlock_pullback`, `profile_pullback`:
  the W3 input and the nd2 profile along an arbitrary `GeometricDatumIso`.
* §2 `Piece` (a partition piecewise on a wall block), `piece_of_blocks`, `piece_transport`.
  §3 `coarse_left/right/newEdge`, `fine_left/right/newEdge`: Figure 31's two pasted
  resolutions as pieces.
* §4 (**family-generic**, directions `L`, `G`, `T` at any trivalent wall):
  `nonempty_transportFree_coarse` (no coherence), `Coherent`, `nonempty_transportFree_fine`,
  and `coherent_of_transportFree` (coherence is necessary).
* §5 `member_cases`, `member_coarseShape`, `member_fineShape`: an arbitrary star member.
  §6 `transport_zero`, `transport_one`, `fineCoherent_of_positionTransport`.
  §7–§8 exhaustion and the family clause modulo `FineCoherenceAt` (discharged in §13).
* §9 `Pendant`, `relabel_eq_self_of_singleton`, `pendantIso`, `pendantLimitIso`: a
  permutation of pendant sheets on a target branch is a `GeometricStar.LimitIso` from a
  regrowth to itself.  §10 `farEnd`, `edgeMoved_self`, `edgeMoved_other` (tree separation),
  `adjacent_same_sheet`, `mem_side_of_moved`.  §11 `exists_branch_cut`, **`pendant_at_wall`**.
  §12 **`exists_coherent`** (family-generic).
* §13 `fineCoherenceAt`, `exhausts`, `w3Nd2FineCoherence`, **`w3Nd2StarExhaustion`**,
  **`w3Nd2StarCensus`**, **`familyStarParity_w3Nd2`**.

## What is NOT proved (every surviving hypothesis, explicitly)

* Nothing is assumed: the three headlines have no hypothesis beyond their binders, and
  `exhausts` does not use the `w3Nd2CoarseFine` tag (it holds at every regrowth carrying a
  W3 input and an nd2 profile).
* **Non-vacuity is not shown**: no `w3Nd2CoarseFine` regrowth, W3 input or nd2 profile is
  constructed in this library, so no `example` at a concrete instance is given.  The clause
  is proved at every such wall that exists.
* `ResolutionExpansion.Transport` (the strict transport) is not produced; the
  receipts are decoupled `TransportFree`s, which is what `exhausts_of_transports` consumes.

## Remarks

* The approach of `M11StarExhaustionProof` (pull back the input and profile, read the
  member's shape from Part I's censuses, feed the builder) **works for the coarse position,
  but not as it stands for the fine one.**  The pullback (§1) and the shapes (§2–§5) go
  through unchanged.  But the fine receipt needs `Coherent` for the third, all-dangling
  direction, which the builder cannot supply and which a given limit isomorphism need not
  satisfy (`coherent_of_transportFree` shows it is necessary).  The argument instead
  re-chooses the limit isomorphism by a pendant automorphism (§9–§12).  As
  `W3Nd2StarCensusProof` records, there is no coherence dichotomy between positions (there is
  no remote position); there is nevertheless a coherence requirement, met by changing the
  isomorphism, not the position.
* The W3 nd3 family is treated in `W3Nd3StarExhaustionProof`.
* §2 (`Piece`), §4 (the `L/G/T` transports and `Coherent`), §9–§12 (pendant automorphisms,
  branch geometry, `pendant_at_wall`, `exists_coherent`) are family-free; W3Nd3 consumes them
  from here.  From `M11StarExhaustionProof`, `nonempty_transportFree_of_rel`, `exists_gauge`,
  `blockPre`, `sourceVertexEquiv_blockPre`, `localRamification_blockPre` and
  `incidentEquivOf` are used verbatim.
* The mechanism that would break the census is a free sheet glued into a third-direction
  dangling tree, which would give a third, non-isomorphic fine class.  It is excluded
  exactly by dangling-no-glue, stated in Lean as `pendant_at_wall`.

## Endpoint compatibility, at this family

As in `M11StarExhaustionProof`, endpoint compatibility of a `TransportFree` is not derivable
from the isomorphism alone.  At a coarse position it is automatic (the trivalent end is
joined; the divalent end has one occurrence).  At the fine position it is `Coherent`, and it
is achieved by *choosing* the isomorphism, which the receipt (`∃ ψ`) permits: the needed
freedom is exactly the dangling occurrences, which lie outside the reach of `overCore_row`.

## Consumers

`StarSupplyAssembly`, through `familyStarParity_w3Nd2` (the `w3Nd2CoarseFine` clause of
`FamilyStarParity`), and so the star parity of step 2 (trivalent walls) of
`DraismaVargasCount/Assembly.lean`; `W3Nd3StarExhaustionProof` reuses §2, §4 and §9–§12.
-/

namespace DraismaVargas.Count.W3Nd2StarExhaustionProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open ThirdEquation W3R1SourceProfile
open M11StarExhaustionProof (blockPre blockPre_rel sourceVertexEquiv_blockPre blockCard_blockPre
  localRamification_blockPre nonDanglingValency_blockPre sourceVertexEquiv_block incidentEquivOf
  incidentEquivOf_target incidentEquivOf_val)

/-! ## 1.  The W3 input and the nd2 profile, pulled back along a limit isomorphism -/

section Pullback

open W4Assembly

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

/-- The three-star at the member's wall, pulled back along a limit isomorphism. -/
noncomputable def pullbackThreeStar (iso : GeometricDatumIso first second) (vertex : target₁.V)
    (otherVertex : target₂.V) (hVertex : iso.targetVertex vertex = otherVertex)
    (star : ThreeStar target₂ otherVertex) : ThreeStar target₁ vertex where
  label := star.label.trans (Equiv.subtypeEquiv iso.targetEdge (fun edge ↦ by
    rw [← hVertex]
    exact (iso.mem_incidentEdges_map vertex edge).symm)).symm

/-- **The W3 input pulls back along a limit isomorphism.** -/
theorem input_pullback (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star' : ThreeStar target₂ wall'} (input : W3SourceInput second star') :
    W3SourceInput first (pullbackThreeStar iso wall wall' hWall star') := by
  have hConnected : first.Connected := iso.symm.connected input.valid.1
  refine { valid := iso.symm.valid_map input.valid
           stablePath_card := ?_
           dangling_no_glue := iso.symm.danglingEdgeNoGlue_map input.valid.1 input.dangling_no_glue
           nonDangling_valency := ?_
           equation_c := ?_ }
  · rw [Fintype.card_congr (iso.stablePathEquiv hConnected), input.stablePath_card]
    congr 1
    exact iso.targetEdgeCard_map
  · intro block
    have h := input.nonDangling_valency (WallBlock.ofSheet second wall' (iso.vertexPerm wall block.1))
    rwa [← sourceVertexEquiv_block iso hWall block, iso.nonDanglingValency_map hConnected] at h
  · rw [← MergePinning.targetExcess_map iso wall, hWall]
    exact input.equation_c

/-- The pulled-back distinguished block is the pull-back of the distinguished block. -/
theorem distinguishedBlock_pullback (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star' : ThreeStar target₂ wall'} (input : W3SourceInput second star') :
    (input_pullback iso hWall input).distinguishedBlock =
      blockPre iso wall input.distinguishedBlock.1 := by
  by_contra hNe
  have h0 := (input_pullback iso hWall input).localRamification_eq_zero_of_ne (Ne.symm hNe)
  rw [localRamification_blockPre iso hWall input.distinguishedBlock,
    input.localRamification_distinguishedBlock] at h0
  exact one_ne_zero h0

theorem sourceVertexEquiv_distinguished (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star' : ThreeStar target₂ wall'} (input : W3SourceInput second star') :
    iso.sourceVertexEquiv (WallBlock.sourceVertex first wall
        (input_pullback iso hWall input).distinguishedBlock) =
      WallBlock.sourceVertex second wall' input.distinguishedBlock := by
  rw [distinguishedBlock_pullback iso hWall input]
  exact sourceVertexEquiv_blockPre iso hWall input.distinguishedBlock

theorem blockCard_distinguished (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star' : ThreeStar target₂ wall'} (input : W3SourceInput second star') :
    (first.vertexPartition wall).blockCard
        (input_pullback iso hWall input).distinguishedBlock.1 =
      (second.vertexPartition wall').blockCard input.distinguishedBlock.1 := by
  rw [distinguishedBlock_pullback iso hWall input]
  exact blockCard_blockPre iso hWall _

/-- Incident occurrences at the two distinguished source vertices correspond. -/
noncomputable abbrev distinguishedIncident (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star' : ThreeStar target₂ wall'} (input : W3SourceInput second star') :=
  incidentEquivOf iso (sourceVertexEquiv_distinguished iso hWall input)

/-- **The nd2 profile pulls back along a limit isomorphism.** -/
noncomputable def profile_pullback (iso : GeometricDatumIso first second)
    (hConnected : first.Connected)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star' : ThreeStar target₂ wall'} (input : W3SourceInput second star')
    (profile : Nd2Profile second input.distinguishedBlock) :
    Nd2Profile first (input_pullback iso hWall input).distinguishedBlock where
  small := (distinguishedIncident iso hWall input).symm profile.small
  large := (distinguishedIncident iso hWall input).symm profile.large
  distinct := fun h ↦ profile.distinct ((distinguishedIncident iso hWall input).symm.injective h)
  surviving := by
    classical
    ext e
    rw [mem_survivors, ← iso.isDangling_map_iff hConnected e.1]
    change ¬ IsDangling second ((distinguishedIncident iso hWall input) e).1 ↔ _
    rw [← mem_survivors, profile.surviving]
    simp only [Finset.mem_insert, Finset.mem_singleton, Equiv.eq_symm_apply]
  target_ne := by
    intro h
    apply profile.target_ne
    have h1 := incidentEquivOf_target iso (sourceVertexEquiv_distinguished iso hWall input)
      ((distinguishedIncident iso hWall input).symm profile.small)
    have h2 := incidentEquivOf_target iso (sourceVertexEquiv_distinguished iso hWall input)
      ((distinguishedIncident iso hWall input).symm profile.large)
    rw [Equiv.apply_symm_apply] at h1 h2
    rw [h1, h2, h]
  small_index := by
    have h := iso.sourceEdgeIndex_map ((distinguishedIncident iso hWall input).symm profile.small).1
    change second.sourceEdgeIndex ((distinguishedIncident iso hWall input)
      ((distinguishedIncident iso hWall input).symm profile.small)).1 = _ at h
    rw [Equiv.apply_symm_apply] at h
    rw [← h, blockCard_distinguished iso hWall input]
    exact profile.small_index
  large_index := by
    have h := iso.sourceEdgeIndex_map ((distinguishedIncident iso hWall input).symm profile.large).1
    change second.sourceEdgeIndex ((distinguishedIncident iso hWall input)
      ((distinguishedIncident iso hWall input).symm profile.large)).1 = _ at h
    rw [Equiv.apply_symm_apply] at h
    rw [← h, blockCard_distinguished iso hWall input]
    exact profile.large_index

end Pullback

/-! ## 2.  Shapes of local resolutions, as relations: a partition piecewise on the
distinguished block -/

section Shapes

variable {d : ℕ}

/-- `R` is `X` on the wall block of `b` and `Y` on every other wall block (both read
inside the wall partition `W`). -/
def Piece (W : SheetPartition d) (b : Fin d) (X Y R : SheetPartition d) : Prop :=
  ∀ x y, R.Rel x y ↔ W.Rel x y ∧ (W.Rel b x → X.Rel x y) ∧ (¬ W.Rel b x → Y.Rel x y)

theorem piece_of_blocks {W : SheetPartition d} {b : Fin d} {X Y R : SheetPartition d}
    (hX : X.Refines W) (hY : Y.Refines W)
    (hSel : ∀ s, W.Rel b s → R.block s = X.block s)
    (hOff : ∀ s, ¬ W.Rel b s → R.block s = Y.block s) : Piece W b X Y R := by
  intro x y
  have hR : ∀ P : SheetPartition d, P.Rel x y ↔ y ∈ P.block x :=
    fun P ↦ (P.mem_block_iff x y).symm
  by_cases hx : W.Rel b x
  · rw [hR R, hSel x hx, ← hR X]
    exact ⟨fun h ↦ ⟨hX.rel h, fun _ ↦ h, fun h' ↦ (h' hx).elim⟩, fun h ↦ h.2.1 hx⟩
  · rw [hR R, hOff x hx, ← hR Y]
    exact ⟨fun h ↦ ⟨hY.rel h, fun h' ↦ (hx h').elim, fun _ ↦ h⟩, fun h ↦ h.2.2 hx⟩

theorem Piece.refines {W : SheetPartition d} {b : Fin d} {X Y R : SheetPartition d}
    (h : Piece W b X Y R) : R.Refines W :=
  fun x y hxy ↦ ((h x y).mp hxy).1

theorem Piece.of_sameBlocks {W : SheetPartition d} {b : Fin d} {X Y R R' : SheetPartition d}
    (h : Piece W b X Y R') (hR : R.SameBlocks R') : Piece W b X Y R :=
  fun x y ↦ (hR x y).trans (h x y)

theorem Piece.congr_anchor {W : SheetPartition d} {b b' : Fin d} {X Y R : SheetPartition d}
    (h : Piece W b X Y R) (hb : W.Rel b b') : Piece W b' X Y R := by
  intro x y
  rw [h x y]
  have hiff : W.Rel b x ↔ W.Rel b' x := ⟨fun h' ↦ hb.symm.trans h', fun h' ↦ hb.trans h'⟩
  rw [hiff]

theorem Piece.rel_of_sel {W : SheetPartition d} {b : Fin d} {X Y R : SheetPartition d}
    (h : Piece W b X Y R) (hX : X.Refines W) {x y : Fin d} (hb : W.Rel b x)
    (hxy : X.Rel x y) : R.Rel x y :=
  (h x y).mpr ⟨hX.rel hxy, fun _ ↦ hxy, fun h' ↦ (h' hb).elim⟩

theorem Piece.rel_of_off {W : SheetPartition d} {b : Fin d} {X Y R : SheetPartition d}
    (h : Piece W b X Y R) (hY : Y.Refines W) {x y : Fin d} (hb : ¬ W.Rel b x)
    (hxy : Y.Rel x y) : R.Rel x y :=
  (h x y).mpr ⟨hY.rel hxy, fun h' ↦ (hb h').elim, fun _ ↦ hxy⟩

/-- **Transport of a piecewise shape** by one permutation that carries the wall
partition, the distinguished block, and each piece on its own region. -/
theorem piece_transport {W W' : SheetPartition d} {b b' : Fin d}
    {X Y R X' Y' R' : SheetPartition d} (τ : Equiv.Perm (Fin d))
    (hW : ∀ x y, W.Rel x y ↔ W'.Rel (τ x) (τ y))
    (hb : ∀ x, W.Rel b x ↔ W'.Rel b' (τ x))
    (hX : ∀ x y, W.Rel b x → (X.Rel x y ↔ X'.Rel (τ x) (τ y)))
    (hY : ∀ x y, ¬ W.Rel b x → (Y.Rel x y ↔ Y'.Rel (τ x) (τ y)))
    (hR : Piece W b X Y R) (hR' : Piece W' b' X' Y' R') :
    ∀ x y, R.Rel x y ↔ R'.Rel (τ x) (τ y) := by
  intro x y
  rw [hR, hR', hW, ← hb]
  by_cases hx : W.Rel b x
  · rw [hX x y hx]
    exact ⟨fun h ↦ ⟨h.1, h.2.1, fun h' ↦ (h' hx).elim⟩,
      fun h ↦ ⟨h.1, h.2.1, fun h' ↦ (h' hx).elim⟩⟩
  · rw [hY x y hx]
    exact ⟨fun h ↦ ⟨h.1, fun h' ↦ (hx h').elim, h.2.2⟩,
      fun h ↦ ⟨h.1, fun h' ↦ (hx h').elim, h.2.2⟩⟩

theorem piece_self (W : SheetPartition d) (b : Fin d) : Piece W b W W W :=
  fun _ _ ↦ ⟨fun h ↦ ⟨h, fun _ ↦ h, fun _ ↦ h⟩, fun h ↦ h.1⟩

end Shapes

/-! ## 3.  The two positions' shapes (Figure 31, read off the block lemmas) -/

section CandidateShapes

open W3Nd2SourceCandidates W3Nd2FineCandidates W3Nd2FineRefinement

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  (input : W3SourceInput data star) (profile : Nd2Profile data input.distinguishedBlock)

theorem small_refines_wall :
    (data.edgePartition (smallTarget input profile)).Refines (data.vertexPartition wall) :=
  fine_refines_wall input profile

/-- The coarse position: the left end is the small partition off the distinguished block
and the wall block on it. -/
theorem coarse_left :
    Piece (data.vertexPartition wall) input.distinguishedBlock.1 (data.vertexPartition wall)
      (data.edgePartition (smallTarget input profile))
      (M11StarCensusProof.pasted (coarseCandidate input profile)).left :=
  piece_of_blocks (SheetPartition.Refines.refl _) (small_refines_wall input profile)
    (fun s hs ↦ W3Nd2Survival.coarse_pasted_left_block_selected input profile s hs)
    (fun s hs ↦ W3Nd2Background.coarse_background_left_block input profile s hs)

theorem coarse_right :
    Piece (data.vertexPartition wall) input.distinguishedBlock.1 (data.vertexPartition wall)
      (data.vertexPartition wall)
      (M11StarCensusProof.pasted (coarseCandidate input profile)).right :=
  piece_of_blocks (SheetPartition.Refines.refl _) (SheetPartition.Refines.refl _)
    (fun s hs ↦ W3Nd2Survival.coarse_pasted_right_block_selected input profile s hs)
    (fun s hs ↦ W3Nd2StableLift.coarse_background_right_block input profile s hs)

theorem coarse_newEdge :
    Piece (data.vertexPartition wall) input.distinguishedBlock.1 (data.vertexPartition wall)
      (data.edgePartition (smallTarget input profile))
      (M11StarCensusProof.pasted (coarseCandidate input profile)).newEdge :=
  piece_of_blocks (SheetPartition.Refines.refl _) (small_refines_wall input profile)
    (fun s hs ↦ W3Nd2Survival.coarse_pasted_newEdge_block_selected input profile s hs)
    (fun s hs ↦ W3Nd2Background.coarse_background_newEdge_block input profile s hs)

/-- The fine position: the left end is the large partition off the distinguished block;
the right end is the small partition on it. -/
theorem fine_left :
    Piece (data.vertexPartition wall) input.distinguishedBlock.1 (data.vertexPartition wall)
      (data.edgePartition (largeTarget input profile))
      (M11StarCensusProof.pasted (fineCandidate input profile)).left :=
  piece_of_blocks (SheetPartition.Refines.refl _) (large_refines_wall input profile)
    (fun s hs ↦ pasted_left_block_selected input profile s hs)
    (fun s hs ↦ W3Nd2Background.fine_background_left_block input profile s hs)

theorem fine_right :
    Piece (data.vertexPartition wall) input.distinguishedBlock.1
      (data.edgePartition (smallTarget input profile)) (data.vertexPartition wall)
      (M11StarCensusProof.pasted (fineCandidate input profile)).right :=
  piece_of_blocks (small_refines_wall input profile) (SheetPartition.Refines.refl _)
    (fun s hs ↦ pasted_right_block_selected input profile s hs)
    (fun s hs ↦ W3Nd2StableLift.fine_background_right_block input profile s hs)

theorem fine_newEdge :
    Piece (data.vertexPartition wall) input.distinguishedBlock.1
      (data.edgePartition (smallTarget input profile))
      (data.edgePartition (largeTarget input profile))
      (M11StarCensusProof.pasted (fineCandidate input profile)).newEdge :=
  piece_of_blocks (small_refines_wall input profile) (large_refines_wall input profile)
    (fun s hs ↦ pasted_newEdge_block_selected input profile s hs)
    (fun s hs ↦ W3Nd2Background.fine_background_newEdge_block input profile s hs)

end CandidateShapes

/-! ## 4.  Transports onto the two positions, from shapes (family-generic)

Everything in this section is stated for an arbitrary limit isomorphism and an arbitrary
trivalent wall whose three incident occurrences are named `L` (the coarse position's
divalent-side direction), `G` (the fine position's) and `T` (the third, all-dangling one),
with an arbitrary wall-side distinguished sheet `b`.  Both W3 families instantiate it:
nd2 with `L, G = small, large` and nd3 with `L, G = shared, largest`. -/

section Transport

open ResolutionExpansionFree W4Assembly
open W3Nd2SourceCandidates (rightOf)
open ResolutionM11 (LocalResolution)

variable {d : ℕ}

/-- **A piecewise permutation**: `σ` on a region, `ρ` off it, when each respects the
region and its image. -/
noncomputable def piecewisePerm (p q : Fin d → Prop) [DecidablePred p]
    (σ ρ : Equiv.Perm (Fin d)) (hσ : ∀ x, p x → q (σ x)) (hρ : ∀ x, ¬ p x → ¬ q (ρ x)) :
    Equiv.Perm (Fin d) :=
  Equiv.ofBijective (fun x ↦ if p x then σ x else ρ x) (Finite.injective_iff_bijective.mp (by
    intro x y hxy
    by_cases hx : p x <;> by_cases hy : p y <;> simp only [hx, hy, if_true, if_false] at hxy
    · exact σ.injective hxy
    · exact ((hρ y hy) (hxy ▸ hσ x hx)).elim
    · exact ((hρ x hx) (hxy.symm ▸ hσ y hy)).elim
    · exact ρ.injective hxy))

theorem piecewisePerm_of_pos {p q : Fin d → Prop} [DecidablePred p]
    {σ ρ : Equiv.Perm (Fin d)} {hσ : ∀ x, p x → q (σ x)} {hρ : ∀ x, ¬ p x → ¬ q (ρ x)}
    {x : Fin d} (hx : p x) : piecewisePerm p q σ ρ hσ hρ x = σ x := by
  change (if p x then σ x else ρ x) = σ x
  rw [if_pos hx]

theorem piecewisePerm_of_neg {p q : Fin d → Prop} [DecidablePred p]
    {σ ρ : Equiv.Perm (Fin d)} {hσ : ∀ x, p x → q (σ x)} {hρ : ∀ x, ¬ p x → ¬ q (ρ x)}
    {x : Fin d} (hx : ¬ p x) : piecewisePerm p q σ ρ hσ hρ x = ρ x := by
  change (if p x then σ x else ρ x) = ρ x
  rw [if_neg hx]

theorem rightOf_pullback {T₁ T₂ : CFGraph} (f : T₁.edges ≃ T₂.edges) (e₂ : T₂.edges)
    (edge : T₁.edges) : rightOf e₂ (f edge) = rightOf (f.symm e₂) edge := by
  unfold rightOf
  exact decide_eq_decide.mpr (not_congr (Equiv.eq_symm_apply f).symm)

theorem rightOf_eq_false {T₂ : CFGraph} {e₂ edge : T₂.edges} (h : rightOf e₂ edge = false) :
    edge = e₂ := by
  simpa [rightOf] using h

theorem rightOf_eq_true {T₂ : CFGraph} {e₂ edge : T₂.edges} (h : edge ≠ e₂) :
    rightOf e₂ edge = true := by
  simpa [rightOf] using h

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
  (iso : GeometricDatumIso first second) {wall : target₁.V} {wall' : target₂.V}
  (hWall : iso.targetVertex wall = wall')

theorem edge_rel_iff (edge : target₁.edges) (x y : Fin degree) :
    (first.edgePartition edge).Rel x y ↔
      (second.edgePartition (iso.targetEdge edge)).Rel (iso.edgePerm edge x) (iso.edgePerm edge y) := by
  rw [iso.edgePartition edge, SheetPartition.relabel_rel_iff]

theorem edge_rel_iff_symm (edge : target₂.edges) (x y : Fin degree) :
    (first.edgePartition (iso.targetEdge.symm edge)).Rel x y ↔
      (second.edgePartition edge).Rel (iso.edgePerm (iso.targetEdge.symm edge) x)
        (iso.edgePerm (iso.targetEdge.symm edge) y) := by
  rw [edge_rel_iff iso, Equiv.apply_symm_apply]

include hWall in
theorem incident_iff (edge : target₁.edges) :
    ((edge : target₁.V × target₁.V).1 = wall ∨ (edge : target₁.V × target₁.V).2 = wall) ↔
      iso.targetEdge edge ∈ GluingDatum.incidentEdges wall' := by
  rw [← hWall, iso.mem_incidentEdges_map wall edge]
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]

include hWall in
/-- Every incident occurrence permutation agrees with the wall permutation modulo the
merged partition. -/
theorem edgePerm_agree (edge : target₁.edges)
    (hInc : iso.targetEdge edge ∈ GluingDatum.incidentEdges wall') (s : Fin degree) :
    (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (iso.edgePerm edge s)) s :=
  iso.compatible edge wall ((incident_iff iso hWall edge).mpr hInc) s

include hWall in
theorem edgePerm_agree_symm (edge : target₂.edges) (hInc : edge ∈ GluingDatum.incidentEdges wall')
    (s : Fin degree) :
    (first.vertexPartition wall).Rel
      ((iso.vertexPerm wall).symm (iso.edgePerm (iso.targetEdge.symm edge) s)) s :=
  edgePerm_agree iso hWall _ (by rw [Equiv.apply_symm_apply]; exact hInc) s

/-- Two permutations agreeing with the wall permutation agree with each other. -/
theorem agree_symm_apply (σ ρ : Equiv.Perm (Fin degree))
    (hσ : ∀ s, (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (σ s)) s)
    (hρ : ∀ s, (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (ρ s)) s)
    (s : Fin degree) : (first.vertexPartition wall).Rel (σ.symm (ρ s)) s := by
  have h1 := hσ (σ.symm (ρ s))
  rw [Equiv.apply_symm_apply] at h1
  exact h1.symm.trans (hρ s)

include hWall in
/-- A permutation agreeing with the wall permutation carries the pulled-back block. -/
theorem sel_iff (b : Fin degree) (τ : Equiv.Perm (Fin degree))
    (hτ : ∀ s, (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (τ s)) s)
    (x : Fin degree) :
    (first.vertexPartition wall).Rel (blockPre iso wall b).1 x ↔
      (second.vertexPartition wall').Rel b (τ x) := by
  rw [M11StarExhaustionProof.wall_rel_iff iso hWall]
  have hb := blockPre_rel iso wall b
  constructor
  · intro h
    exact hb.symm.trans (h.trans (hτ x).symm)
  · intro h
    exact hb.trans (h.trans (hτ x))

variable (b : Fin degree) (L G T : target₂.edges)
  (hEdges : ∀ e, e ∈ GluingDatum.incidentEdges wall' ↔ e = L ∨ e = G ∨ e = T)

include hEdges in
theorem mem_L : L ∈ GluingDatum.incidentEdges wall' := (hEdges L).mpr (Or.inl rfl)
include hEdges in
theorem mem_G : G ∈ GluingDatum.incidentEdges wall' := (hEdges G).mpr (Or.inr (Or.inl rfl))
include hEdges in
theorem mem_T : T ∈ GluingDatum.incidentEdges wall' := (hEdges T).mpr (Or.inr (Or.inr rfl))

include hEdges in
/-- The incident occurrences at the member's wall are the three pulled-back directions. -/
theorem incident_cases (edge : target₁.edges)
    (hInc : iso.targetEdge edge ∈ GluingDatum.incidentEdges wall') :
    edge = iso.targetEdge.symm L ∨ edge = iso.targetEdge.symm G ∨ edge = iso.targetEdge.symm T := by
  rcases (hEdges _).mp hInc with h | h | h
  · exact Or.inl ((Equiv.eq_symm_apply _).mpr h)
  · exact Or.inr (Or.inl ((Equiv.eq_symm_apply _).mpr h))
  · exact Or.inr (Or.inr ((Equiv.eq_symm_apply _).mpr h))

include hWall hEdges in
/-- **The coarse transport, with no coherence condition.**  All three permutations are the
occurrence permutation of the coarse position's divalent-side direction `L`. -/
theorem nonempty_transportFree_coarse (right : target₁.edges → Bool)
    (res res' : LocalResolution degree)
    (hSide : ∀ edge, rightOf L (iso.targetEdge edge) = right edge)
    (hLeft : Piece (first.vertexPartition wall) (blockPre iso wall b).1 (first.vertexPartition wall)
      (first.edgePartition (iso.targetEdge.symm L)) res.left)
    (hRight : Piece (first.vertexPartition wall) (blockPre iso wall b).1
      (first.vertexPartition wall) (first.vertexPartition wall) res.right)
    (hNew : Piece (first.vertexPartition wall) (blockPre iso wall b).1 (first.vertexPartition wall)
      (first.edgePartition (iso.targetEdge.symm L)) res.newEdge)
    (hLeft' : Piece (second.vertexPartition wall') b (second.vertexPartition wall')
      (second.edgePartition L) res'.left)
    (hRight' : Piece (second.vertexPartition wall') b (second.vertexPartition wall')
      (second.vertexPartition wall') res'.right)
    (hNew' : Piece (second.vertexPartition wall') b (second.vertexPartition wall')
      (second.edgePartition L) res'.newEdge) :
    Nonempty (TransportFree iso wall wall' right (rightOf L) res res') := by
  set τ := iso.edgePerm (iso.targetEdge.symm L)
  have hτ := edgePerm_agree_symm iso hWall L (mem_L L G T hEdges)
  have hW := M11StarExhaustionProof.wall_rel_iff_of_agree iso hWall τ hτ
  have hb := sel_iff iso hWall b τ hτ
  have hP := edge_rel_iff_symm iso L
  refine M11StarExhaustionProof.nonempty_transportFree_of_rel iso wall wall' right _ res _ hWall
    hSide hLeft.refines hRight.refines τ τ τ hτ hτ ?_ ?_ ?_ ?_ ?_ ?_
  · exact piece_transport τ hW hb (fun x y _ ↦ hW x y) (fun x y _ ↦ hP x y) hLeft hLeft'
  · exact piece_transport τ hW hb (fun x y _ ↦ hW x y) (fun x y _ ↦ hW x y) hRight hRight'
  · exact piece_transport τ hW hb (fun x y _ ↦ hW x y) (fun x y _ ↦ hP x y) hNew hNew'
  · intro s; rw [Equiv.symm_apply_apply]; rfl
  · intro s; rw [Equiv.symm_apply_apply]; rfl
  · intro edge hInc s
    have hInc' := (incident_iff iso hWall edge).mp hInc
    by_cases hr : right edge = true
    · rw [if_pos hr, if_pos hr]
      have hAg := agree_symm_apply iso τ _ hτ (edgePerm_agree iso hWall edge hInc') s
      exact (hRight _ _).mpr ⟨hAg, fun _ ↦ hAg, fun _ ↦ hAg⟩
    · rw [if_neg hr, if_neg hr]
      have hEq : iso.targetEdge edge = L :=
        rightOf_eq_false (by rw [hSide edge]; simpa using hr)
      have hEdge : edge = iso.targetEdge.symm L := (Equiv.eq_symm_apply _).mpr hEq
      subst hEdge
      rw [Equiv.symm_apply_apply]; rfl

/-- **Fine coherence along an isomorphism**: on the pulled-back distinguished block, the
third direction's occurrence permutation agrees with the direction `L`'s modulo `L`'s
partition. -/
def Coherent (v : target₁.V) : Prop :=
  ∀ s, (first.vertexPartition v).Rel (blockPre iso v b).1 s →
    (second.edgePartition L).Rel (iso.edgePerm (iso.targetEdge.symm T) s)
      (iso.edgePerm (iso.targetEdge.symm L) s)

include hWall hEdges in
/-- **The fine transport, given coherence.**  The left permutation is `G`'s, the right one
is `L`'s, and the regrown one is `L`'s on the distinguished block and `G`'s off it. -/
theorem nonempty_transportFree_fine (right : target₁.edges → Bool)
    (res res' : LocalResolution degree)
    (hSide : ∀ edge, rightOf G (iso.targetEdge edge) = right edge)
    (hLeft : Piece (first.vertexPartition wall) (blockPre iso wall b).1 (first.vertexPartition wall)
      (first.edgePartition (iso.targetEdge.symm G)) res.left)
    (hRight : Piece (first.vertexPartition wall) (blockPre iso wall b).1
      (first.edgePartition (iso.targetEdge.symm L)) (first.vertexPartition wall) res.right)
    (hNew : Piece (first.vertexPartition wall) (blockPre iso wall b).1
      (first.edgePartition (iso.targetEdge.symm L))
      (first.edgePartition (iso.targetEdge.symm G)) res.newEdge)
    (hLeft' : Piece (second.vertexPartition wall') b (second.vertexPartition wall')
      (second.edgePartition G) res'.left)
    (hRight' : Piece (second.vertexPartition wall') b (second.edgePartition L)
      (second.vertexPartition wall') res'.right)
    (hNew' : Piece (second.vertexPartition wall') b (second.edgePartition L)
      (second.edgePartition G) res'.newEdge)
    (hCoh : Coherent iso b L T wall) :
    Nonempty (TransportFree iso wall wall' right (rightOf G) res res') := by
  classical
  set W := first.vertexPartition wall
  set σ := iso.edgePerm (iso.targetEdge.symm L)
  set ρ := iso.edgePerm (iso.targetEdge.symm G)
  have hσ := edgePerm_agree_symm iso hWall L (mem_L L G T hEdges)
  have hρ := edgePerm_agree_symm iso hWall G (mem_G L G T hEdges)
  have hbσ := sel_iff iso hWall b σ hσ
  have hbρ := sel_iff iso hWall b ρ hρ
  set τN := piecewisePerm (fun x ↦ W.Rel (blockPre iso wall b).1 x)
    (fun x ↦ (second.vertexPartition wall').Rel b x) σ ρ
    (fun x hx ↦ (hbσ x).mp hx) (fun x hx h ↦ hx ((hbρ x).mpr h))
  have hτN : ∀ s, W.Rel ((iso.vertexPerm wall).symm (τN s)) s := by
    intro s
    by_cases hs : W.Rel (blockPre iso wall b).1 s
    · rw [piecewisePerm_of_pos hs]; exact hσ s
    · rw [piecewisePerm_of_neg hs]; exact hρ s
  have hWσ := M11StarExhaustionProof.wall_rel_iff_of_agree iso hWall σ hσ
  have hWρ := M11StarExhaustionProof.wall_rel_iff_of_agree iso hWall ρ hρ
  have hWN := M11StarExhaustionProof.wall_rel_iff_of_agree iso hWall τN hτN
  have hbN := sel_iff iso hWall b τN hτN
  have hPs := edge_rel_iff_symm iso L
  have hPl := edge_rel_iff_symm iso G
  have hSref := StableLocalProperties.refines_of_mem_incidentEdges second (mem_L L G T hEdges)
  have hSref₁ : (first.edgePartition (iso.targetEdge.symm L)).Refines W := by
    intro x y h
    exact (hWσ x y).mpr (hSref.rel ((hPs x y).mp h))
  have hLref := StableLocalProperties.refines_of_mem_incidentEdges second (mem_G L G T hEdges)
  have hLref₁ : (first.edgePartition (iso.targetEdge.symm G)).Refines W := by
    intro x y h
    exact (hWρ x y).mpr (hLref.rel ((hPl x y).mp h))
  refine M11StarExhaustionProof.nonempty_transportFree_of_rel iso wall wall' right _ res _ hWall
    hSide hLeft.refines hRight.refines ρ σ τN hρ hσ ?_ ?_ ?_ ?_ ?_ ?_
  · exact piece_transport ρ hWρ hbρ (fun x y _ ↦ hWρ x y) (fun x y _ ↦ hPl x y) hLeft hLeft'
  · exact piece_transport σ hWσ hbσ (fun x y _ ↦ hPs x y) (fun x y _ ↦ hWσ x y) hRight hRight'
  · refine piece_transport τN hWN hbN ?_ ?_ hNew hNew'
    · intro x y hx
      rw [piecewisePerm_of_pos hx]
      by_cases hy : W.Rel (blockPre iso wall b).1 y
      · rw [piecewisePerm_of_pos hy]; exact hPs x y
      · rw [piecewisePerm_of_neg hy]
        constructor
        · intro h; exact (hy (hx.trans (hSref₁.rel h))).elim
        · intro h
          exact (hy ((hbρ y).mpr (((hbσ x).mp hx).trans (hSref.rel h)))).elim
    · intro x y hx
      rw [piecewisePerm_of_neg hx]
      by_cases hy : W.Rel (blockPre iso wall b).1 y
      · rw [piecewisePerm_of_pos hy]
        constructor
        · intro h; exact (hx (hy.trans (hLref₁.rel h).symm)).elim
        · intro h
          exact (hx ((hbρ x).mpr (((hbσ y).mp hy).trans (hLref.rel h).symm))).elim
      · rw [piecewisePerm_of_neg hy]; exact hPl x y
  · intro s
    by_cases hs : W.Rel (blockPre iso wall b).1 s
    · rw [piecewisePerm_of_pos hs]
      exact hLeft.rel_of_sel (SheetPartition.Refines.refl _)
        ((hbρ _).mpr (by rw [Equiv.apply_symm_apply]; exact (hbσ s).mp hs))
        (agree_symm_apply iso ρ σ hρ hσ s)
    · rw [piecewisePerm_of_neg hs, Equiv.symm_apply_apply]; rfl
  · intro s
    by_cases hs : W.Rel (blockPre iso wall b).1 s
    · rw [piecewisePerm_of_pos hs, Equiv.symm_apply_apply]; rfl
    · rw [piecewisePerm_of_neg hs]
      exact hRight.rel_of_off (SheetPartition.Refines.refl _)
        (fun h ↦ hs (h.trans (agree_symm_apply iso σ ρ hσ hρ s)))
        (agree_symm_apply iso σ ρ hσ hρ s)
  · intro edge hInc s
    have hInc' := (incident_iff iso hWall edge).mp hInc
    by_cases hr : right edge = true
    · rw [if_pos hr, if_pos hr]
      have hNotG : edge ≠ iso.targetEdge.symm G := by
        rintro rfl
        rw [← hSide, Equiv.apply_symm_apply] at hr
        simp [rightOf] at hr
      rcases incident_cases iso L G T hEdges edge hInc' with h | h | h
      · subst h; rw [Equiv.symm_apply_apply]; rfl
      · exact (hNotG h).elim
      · subst h
        have hAg := agree_symm_apply iso σ _ hσ (edgePerm_agree_symm iso hWall T
          (mem_T L G T hEdges)) s
        by_cases hs : W.Rel (blockPre iso wall b).1 s
        · refine (hRight _ _).mpr ⟨hAg, fun _ ↦ ?_, fun h' ↦ (h' (hs.trans hAg.symm)).elim⟩
          rw [hPs, Equiv.apply_symm_apply]
          exact hCoh s hs
        · exact hRight.rel_of_off (SheetPartition.Refines.refl _)
            (fun h ↦ hs (h.trans hAg)) hAg
    · rw [if_neg hr, if_neg hr]
      have hEq : iso.targetEdge edge = G :=
        rightOf_eq_false (by rw [hSide edge]; simpa using hr)
      have hEdge : edge = iso.targetEdge.symm G := (Equiv.eq_symm_apply _).mpr hEq
      subst hEdge
      rw [Equiv.symm_apply_apply]; rfl

include hWall hEdges in
/-- **Coherence is necessary**: any decoupled transport onto a fine-shaped position, from
any resolution at any placement, forces it along its isomorphism. -/
theorem coherent_of_transportFree (hTG : T ≠ G) (hLG : L ≠ G) (right : target₁.edges → Bool)
    (res res' : LocalResolution degree)
    (hRight' : Piece (second.vertexPartition wall') b (second.edgePartition L)
      (second.vertexPartition wall') res'.right)
    (t : TransportFree iso wall wall' right (rightOf G) res res') :
    Coherent iso b L T wall := by
  intro s hs
  have hRightOf : ∀ e, e ≠ G → right (iso.targetEdge.symm e) = true := by
    intro e he
    rw [← t.side_map, Equiv.apply_symm_apply]
    exact rightOf_eq_true he
  have hInc : ∀ e ∈ GluingDatum.incidentEdges wall',
      ((iso.targetEdge.symm e : target₁.edges) : target₁.V × target₁.V).1 = wall ∨
        ((iso.targetEdge.symm e : target₁.edges) : target₁.V × target₁.V).2 = wall := by
    intro e he
    rw [incident_iff iso hWall, Equiv.apply_symm_apply]; exact he
  have hT := t.endpoint_compatible _ (hInc _ (mem_T L G T hEdges)) s
  have hS := t.endpoint_compatible _ (hInc _ (mem_L L G T hEdges)) s
  rw [if_pos (hRightOf _ hTG), if_pos (hRightOf _ hTG)] at hT
  rw [if_pos (hRightOf _ hLG), if_pos (hRightOf _ hLG)] at hS
  have hRel : res'.right.Rel (iso.edgePerm (iso.targetEdge.symm T) s)
      (iso.edgePerm (iso.targetEdge.symm L) s) := by
    rw [t.right_relabel, M11StarExhaustionProof.relabel_rel_iff']
    exact hT.trans hS.symm
  have hSel : (second.vertexPartition wall').Rel b (iso.edgePerm (iso.targetEdge.symm T) s) :=
    (sel_iff iso hWall b _ (edgePerm_agree_symm iso hWall T (mem_T L G T hEdges)) s).mp hs
  exact ((hRight' _ _).mp hRel).2.1 hSel

end Transport

section Nd2Transport

open W3Nd2FineRefinement

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
  {wall' : target₂.V} {star' : ThreeStar target₂ wall'}

/-- **Fine coherence at an nd2 wall**: the third direction against the small one. -/
abbrev FineCoherent (iso : GeometricDatumIso first second) (input : W3SourceInput second star')
    (profile : Nd2Profile second input.distinguishedBlock) (v : target₁.V) : Prop :=
  Coherent iso input.distinguishedBlock.1 (smallTarget input profile) (thirdTarget input profile) v

theorem incident_nd2 (input : W3SourceInput second star')
    (profile : Nd2Profile second input.distinguishedBlock) (e : target₂.edges) :
    e ∈ GluingDatum.incidentEdges wall' ↔
      e = smallTarget input profile ∨ e = largeTarget input profile ∨
        e = thirdTarget input profile := by
  rw [incidentEdges_eq input profile]
  simp only [Finset.mem_insert, Finset.mem_singleton]

end Nd2Transport

/-! ## 5.  An arbitrary star member, read through its limit isomorphism

Part I's identification (`W3Nd2IncomingMemberMatching.coarse_sameBlocks`/`fine_sameBlocks`),
run at the member's own contraction with the pulled-back input and profile, says the
member's read-off resolution has the coarse or the fine shape. -/

section Member

open W4Assembly W3Nd2SourceCandidates W3Nd2FineCandidates W3Nd2FineRefinement
open W3Nd2IncomingTargetPlacement W3Nd2IncomingDirection

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd2Profile w.limit input.distinguishedBlock)
  (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)

/-- The isomorphism a `PositionTransport` is stated along. -/
noncomputable abbrev isoOf : GeometricDatumIso other.limit w.limit :=
  ψ.datum.trans (GeometricDatumIso.refl w.limit).symm

include input in
theorem isoOf_wall : (isoOf w hy other ψ).targetVertex (mergeVertex other) = mergeVertex w :=
  M11WallExhaustion.pinned_of_targetExcess_eq_one input.equation_c other ψ

/-- The member's pulled-back star, input and profile. -/
noncomputable abbrev star₁ : ThreeStar (other.frame.limitTarget other.column) (mergeVertex other) :=
  pullbackThreeStar (isoOf w hy other ψ) (mergeVertex other) (mergeVertex w)
    (isoOf_wall w hy input other ψ) star

noncomputable abbrev input₁ : W3SourceInput other.limit (star₁ w hy input other ψ) :=
  input_pullback (isoOf w hy other ψ) (isoOf_wall w hy input other ψ) input

noncomputable abbrev profile₁ :
    Nd2Profile other.limit (input₁ w hy input other ψ).distinguishedBlock :=
  profile_pullback (isoOf w hy other ψ) (InheritedLimitRows.limit_connected other)
    (isoOf_wall w hy input other ψ) input profile

theorem smallTarget₁ :
    smallTarget (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ) =
      (isoOf w hy other ψ).targetEdge.symm (W3Nd2FineRefinement.smallTarget input profile) := by
  refine (Equiv.eq_symm_apply _).mpr ?_
  have h := incidentEquivOf_target (isoOf w hy other ψ)
    (sourceVertexEquiv_distinguished (isoOf w hy other ψ) (isoOf_wall w hy input other ψ) input)
    ((distinguishedIncident (isoOf w hy other ψ) (isoOf_wall w hy input other ψ) input).symm
      profile.small)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem largeTarget₁ :
    largeTarget (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ) =
      (isoOf w hy other ψ).targetEdge.symm (W3Nd2FineRefinement.largeTarget input profile) := by
  refine (Equiv.eq_symm_apply _).mpr ?_
  have h := incidentEquivOf_target (isoOf w hy other ψ)
    (sourceVertexEquiv_distinguished (isoOf w hy other ψ) (isoOf_wall w hy input other ψ) input)
    ((distinguishedIncident (isoOf w hy other ψ) (isoOf_wall w hy input other ψ) input).symm
      profile.large)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem sel₁_eq : (input₁ w hy input other ψ).distinguishedBlock.1 =
    (blockPre (isoOf w hy other ψ) (mergeVertex other) input.distinguishedBlock.1).1 :=
  congrArg Subtype.val
    (distinguishedBlock_pullback (isoOf w hy other ψ) (isoOf_wall w hy input other ψ) input)

/-- The member's divalent occurrence, pulled through the member's own star. -/
noncomputable abbrev divalent₁ : (other.frame.limitTarget other.column).edges :=
  divalentOccurrence other.frame.data (contracted := other.frame.edgeOf other.column) rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim (star₁ w hy input other ψ)

/-- **The member-type dichotomy** (Part I's orientation dichotomy at the member). -/
theorem member_cases :
    divalent₁ w hy input other ψ = smallTarget (input₁ w hy input other ψ)
        (profile₁ w hy input profile other ψ) ∨
      divalent₁ w hy input other ψ = largeTarget (input₁ w hy input other ψ)
        (profile₁ w hy input profile other ψ) :=
  divalentOccurrence_eq_small_or_large other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim (InheritedLimitRows.forest other hy)
    (WallAdmissibility.danglingCompatible_of_contractionForest other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
      (InheritedLimitRows.forest other hy))
    (star₁ w hy input other ψ) (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)

/-- The coarse placement of a coarse-type member. -/
theorem coarsePlacement (hSmall : divalent₁ w hy input other ψ =
      smallTarget (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)) :
    W3Nd2StarCensusProof.PlacementSpec other
      (coarseCandidate (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)).right :=
  coarse_placement_of_eq_small other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim (star₁ w hy input other ψ) (input₁ w hy input other ψ)
    (profile₁ w hy input profile other ψ) hSmall

/-- The fine placement of a fine-type member. -/
theorem finePlacement (hLarge : divalent₁ w hy input other ψ =
      largeTarget (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)) :
    W3Nd2StarCensusProof.PlacementSpec other
      (fineCandidate (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)).right :=
  fine_placement_of_eq_large other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim (star₁ w hy input other ψ) (input₁ w hy input other ψ)
    (profile₁ w hy input profile other ψ) hLarge

/-- **A coarse-type member has the coarse shape**, around the pulled-back block and the
pulled-back small direction. -/
theorem member_coarseShape (hSmall : divalent₁ w hy input other ψ =
      smallTarget (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)) :
    Piece (other.limit.vertexPartition (mergeVertex other))
        ((blockPre (isoOf w hy other ψ) (mergeVertex other) input.distinguishedBlock.1).1)
        (other.limit.vertexPartition (mergeVertex other))
        (other.limit.edgePartition
          ((isoOf w hy other ψ).targetEdge.symm (W3Nd2FineRefinement.smallTarget input profile)))
        (W3Nd2StarCensusProof.memberResolution other _
          (coarsePlacement w hy input profile other ψ hSmall)).left ∧
      Piece (other.limit.vertexPartition (mergeVertex other))
        ((blockPre (isoOf w hy other ψ) (mergeVertex other) input.distinguishedBlock.1).1)
        (other.limit.vertexPartition (mergeVertex other))
        (other.limit.vertexPartition (mergeVertex other))
        (W3Nd2StarCensusProof.memberResolution other _
          (coarsePlacement w hy input profile other ψ hSmall)).right ∧
      Piece (other.limit.vertexPartition (mergeVertex other))
        ((blockPre (isoOf w hy other ψ) (mergeVertex other) input.distinguishedBlock.1).1)
        (other.limit.vertexPartition (mergeVertex other))
        (other.limit.edgePartition
          ((isoOf w hy other ψ).targetEdge.symm (W3Nd2FineRefinement.smallTarget input profile)))
        (W3Nd2StarCensusProof.memberResolution other _
          (coarsePlacement w hy input profile other ψ hSmall)).newEdge := by
  set C := coarseCandidate (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
  have hV := W3Nd2IncomingMemberMatching.coarse_vertexPartitions_sameBlocks other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim (InheritedLimitRows.forest other hy)
    (WallAdmissibility.danglingCompatible_of_contractionForest other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
      (InheritedLimitRows.forest other hy))
    (star₁ w hy input other ψ) (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    hSmall
  have hE := W3Nd2IncomingMemberMatching.coarse_edgePartitions_sameBlocks other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim (InheritedLimitRows.forest other hy)
    (WallAdmissibility.danglingCompatible_of_contractionForest other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
      (InheritedLimitRows.forest other hy))
    (star₁ w hy input other ψ) (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    hSmall
  have hL := coarse_left (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
  have hR := coarse_right (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
  have hN := coarse_newEdge (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
  rw [sel₁_eq, smallTarget₁] at hL hN
  rw [sel₁_eq] at hR
  refine ⟨hL.of_sameBlocks ?_, hR.of_sameBlocks ?_, hN.of_sameBlocks ?_⟩
  · have h := hV (oldVertex (other.frame.limitTarget other.column) (mergeVertex other))
    have h2 := M11StarCensusProof.candidate_oldWall C
    exact fun x y ↦ (h x y).trans (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) h2))
  · have h := hV (freshVertex (other.frame.limitTarget other.column))
    have h2 := M11StarCensusProof.candidate_fresh C
    exact fun x y ↦ (h x y).trans (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) h2))
  · have h := hE (occurrenceEquiv (other.frame.limitTarget other.column) (mergeVertex other)
      C.right none)
    have h2 := W3Nd2IncomingMemberMatching.candidate_edgePartition_new C
    exact fun x y ↦ (h x y).trans (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) h2))

/-- **A fine-type member has the fine shape.** -/
theorem member_fineShape (hLarge : divalent₁ w hy input other ψ =
      largeTarget (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)) :
    Piece (other.limit.vertexPartition (mergeVertex other))
        ((blockPre (isoOf w hy other ψ) (mergeVertex other) input.distinguishedBlock.1).1)
        (other.limit.vertexPartition (mergeVertex other))
        (other.limit.edgePartition
          ((isoOf w hy other ψ).targetEdge.symm (W3Nd2FineRefinement.largeTarget input profile)))
        (W3Nd2StarCensusProof.memberResolution other _
          (finePlacement w hy input profile other ψ hLarge)).left ∧
      Piece (other.limit.vertexPartition (mergeVertex other))
        ((blockPre (isoOf w hy other ψ) (mergeVertex other) input.distinguishedBlock.1).1)
        (other.limit.edgePartition
          ((isoOf w hy other ψ).targetEdge.symm (W3Nd2FineRefinement.smallTarget input profile)))
        (other.limit.vertexPartition (mergeVertex other))
        (W3Nd2StarCensusProof.memberResolution other _
          (finePlacement w hy input profile other ψ hLarge)).right ∧
      Piece (other.limit.vertexPartition (mergeVertex other))
        ((blockPre (isoOf w hy other ψ) (mergeVertex other) input.distinguishedBlock.1).1)
        (other.limit.edgePartition
          ((isoOf w hy other ψ).targetEdge.symm (W3Nd2FineRefinement.smallTarget input profile)))
        (other.limit.edgePartition
          ((isoOf w hy other ψ).targetEdge.symm (W3Nd2FineRefinement.largeTarget input profile)))
        (W3Nd2StarCensusProof.memberResolution other _
          (finePlacement w hy input profile other ψ hLarge)).newEdge := by
  set C := fineCandidate (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
  have hV := W3Nd2IncomingMemberMatching.fine_vertexPartitions_sameBlocks other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim (InheritedLimitRows.forest other hy)
    (WallAdmissibility.danglingCompatible_of_contractionForest other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
      (InheritedLimitRows.forest other hy))
    (star₁ w hy input other ψ) (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    hLarge
  have hE := W3Nd2IncomingMemberMatching.fine_edgePartitions_sameBlocks other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim (InheritedLimitRows.forest other hy)
    (WallAdmissibility.danglingCompatible_of_contractionForest other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
      (InheritedLimitRows.forest other hy))
    (star₁ w hy input other ψ) (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    hLarge
  have hL := fine_left (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
  have hR := fine_right (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
  have hN := fine_newEdge (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
  rw [sel₁_eq, largeTarget₁] at hL
  rw [sel₁_eq, smallTarget₁] at hR
  rw [sel₁_eq, smallTarget₁, largeTarget₁] at hN
  refine ⟨hL.of_sameBlocks ?_, hR.of_sameBlocks ?_, hN.of_sameBlocks ?_⟩
  · have h := hV (oldVertex (other.frame.limitTarget other.column) (mergeVertex other))
    have h2 := M11StarCensusProof.candidate_oldWall C
    exact fun x y ↦ (h x y).trans (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) h2))
  · have h := hV (freshVertex (other.frame.limitTarget other.column))
    have h2 := M11StarCensusProof.candidate_fresh C
    exact fun x y ↦ (h x y).trans (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) h2))
  · have h := hE (occurrenceEquiv (other.frame.limitTarget other.column) (mergeVertex other)
      C.right none)
    have h2 := W3Nd2IncomingMemberMatching.candidate_edgePartition_new C
    exact fun x y ↦ (h x y).trans (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) h2))

end Member

/-! ## 6.  The two receipts, and the coherence they need -/

section Receipts

open W4Assembly W3Nd2SourceCandidates W3Nd2FineCandidates W3Nd2FineRefinement

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd2Profile w.limit input.distinguishedBlock)
  (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)

/-- **Position `0` receives every coarse-type member**, with no coherence condition. -/
theorem transport_zero (hSmall : divalent₁ w hy input other ψ =
      smallTarget (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)) :
    Nonempty (W3Nd2StarCensusProof.PositionTransport w hy input profile other ψ _
      (coarsePlacement w hy input profile other ψ hSmall) ⟨0, by decide⟩) := by
  obtain ⟨hL, hR, hN⟩ := member_coarseShape w hy input profile other ψ hSmall
  refine nonempty_transportFree_coarse (isoOf w hy other ψ) (isoOf_wall w hy input other ψ)
    input.distinguishedBlock.1 _ _ _ (incident_nd2 input profile) _ _ _ ?_ hL hR hN
    (coarse_left input profile) (coarse_right input profile) (coarse_newEdge input profile)
  intro edge
  change rightOf (smallTarget input profile) _ =
    rightOf (smallTarget (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)) edge
  rw [smallTarget₁, rightOf_pullback]

/-- **Position `1` receives every fine-type member along a coherent isomorphism.** -/
theorem transport_one (hLarge : divalent₁ w hy input other ψ =
      largeTarget (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ))
    (hCoh : FineCoherent (isoOf w hy other ψ) input profile (mergeVertex other)) :
    Nonempty (W3Nd2StarCensusProof.PositionTransport w hy input profile other ψ _
      (finePlacement w hy input profile other ψ hLarge) ⟨1, by decide⟩) := by
  obtain ⟨hL, hR, hN⟩ := member_fineShape w hy input profile other ψ hLarge
  refine nonempty_transportFree_fine (isoOf w hy other ψ) (isoOf_wall w hy input other ψ)
    input.distinguishedBlock.1 _ _ _ (incident_nd2 input profile)
    _ _ _ ?_ hL hR hN
    (fine_left input profile) (fine_right input profile) (fine_newEdge input profile) hCoh
  intro edge
  change rightOf (largeTarget input profile) _ =
    rightOf (largeTarget (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)) edge
  rw [largeTarget₁, rightOf_pullback]

/-- **Coherence is exactly what position `1` asks for**: any receipt at the fine position
along `ψ`, at any placement, forces fine coherence along `ψ`. -/
theorem fineCoherent_of_positionTransport
    (placement : (other.frame.limitTarget other.column).edges → Bool)
    (hPlacement : W3Nd2StarCensusProof.PlacementSpec other placement)
    (t : W3Nd2StarCensusProof.PositionTransport w hy input profile other ψ placement hPlacement
      ⟨1, by decide⟩) :
    FineCoherent (isoOf w hy other ψ) input profile (mergeVertex other) :=
  coherent_of_transportFree (isoOf w hy other ψ) (isoOf_wall w hy input other ψ)
    input.distinguishedBlock.1 _ _ _ (incident_nd2 input profile)
    (thirdTarget_ne_large input profile) profile.target_ne placement _ _
    (fine_right input profile) t

end Receipts

/-! ## 7.  Exhaustion from fine coherence -/

section Exhaustion

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd2Profile w.limit input.distinguishedBlock)

/-- **Fine coherence at one wall**: every star member has a limit isomorphism along which,
if it is of fine type, the third direction's occurrence permutation agrees with the small
direction's modulo the small partition on the distinguished block.  Proved at every wall
(`fineCoherenceAt`, §13).

*Interface*: this is exactly the condition of the receipt route at fine-type members
(`fineCoherent_of_positionTransport` is the converse half); coarse-type members need
nothing (`transport_zero`). -/
def FineCoherenceAt : Prop :=
  ∀ member : GeometricStar.StarMember hy w, ∃ ψ : GeometricStar.LimitIso hy member.member w,
    divalent₁ w hy input member.member ψ =
        W3Nd2FineRefinement.largeTarget (input₁ w hy input member.member ψ)
          (profile₁ w hy input profile member.member ψ) →
      FineCoherent (isoOf w hy member.member ψ) input profile (mergeVertex member.member)

/-- **Every star member presents a receipt**, given fine coherence. -/
theorem exists_receipt (hCoh : FineCoherenceAt w hy input profile)
    (member : GeometricStar.StarMember hy w) :
    ∃ ψ : GeometricStar.LimitIso hy member.member w,
    ∃ placement : (member.member.frame.limitTarget member.member.column).edges → Bool,
    ∃ hPlacement : W3Nd2StarCensusProof.PlacementSpec member.member placement,
    ∃ q : Fin 2, Nonempty (W3Nd2StarCensusProof.PositionTransport w hy input profile
      member.member ψ placement hPlacement q) := by
  obtain ⟨ψ, hψ⟩ := hCoh member
  rcases member_cases w hy input profile member.member ψ with hSmall | hLarge
  · exact ⟨ψ, _, _, ⟨0, by decide⟩, transport_zero w hy input profile member.member ψ hSmall⟩
  · exact ⟨ψ, _, _, ⟨1, by decide⟩,
      transport_one w hy input profile member.member ψ hLarge (hψ hLarge)⟩

/-- **Stage 2 at one wall, modulo fine coherence.** -/
theorem exhausts_of_fineCoherence {incoming : Fin 2}
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd2CommonBalance.candidates input profile incoming).datum (Fin p))
    (hCoh : FineCoherenceAt w hy input profile) :
    W3Nd2StarCensusProof.Exhausts w hy input profile incomingFD :=
  W3Nd2StarCensusProof.exhausts_of_transports w hy input profile incomingFD
    (exists_receipt w hy input profile hCoh)

end Exhaustion

/-! ## 8.  The family clause from fine coherence -/

section Family

/-- **Fine coherence, family-wide** (proved: `w3Nd2FineCoherence`). -/
def W3Nd2FineCoherence (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w3Nd2CoarseFine →
    ∀ (star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : W3SourceInput w.limit star)
      (profile : Nd2Profile w.limit input.distinguishedBlock),
      FineCoherenceAt w hy input profile

variable {degree n p : ℕ}

/-- **The W3 nd2 star exhaustion, modulo fine coherence.** -/
theorem w3Nd2StarExhaustion_of_fineCoherence (h : W3Nd2FineCoherence degree n p) :
    W3Nd2StarCensusProof.W3Nd2StarExhaustion degree n p :=
  fun core y hy w cls htag star input profile _ incomingFD ↦
    exhausts_of_fineCoherence w hy input profile incomingFD
      (h core y hy w cls htag star input profile)

/-- **The W3 nd2 star census, modulo fine coherence.** -/
theorem w3Nd2StarCensus_of_fineCoherence (h : W3Nd2FineCoherence degree n p) :
    W3Nd2StarCensusProof.W3Nd2StarCensus degree n p :=
  W3Nd2StarCensusProof.w3Nd2StarCensus_of_exhaustion (w3Nd2StarExhaustion_of_fineCoherence h)

/-- **The `w3Nd2CoarseFine` clause of `FamilyStarParity` at genus six and degree four,
modulo fine coherence alone.** -/
theorem familyStarParity_w3Nd2_of_fineCoherence
    (h : W3Nd2FineCoherence (2 + 2) (4 * 2 + 2) (6 * 2 + 3)) :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w3Nd2CoarseFine :=
  W3Nd2StarCensusProof.familyStarParity_w3Nd2_of_exhaustion
    (w3Nd2StarExhaustion_of_fineCoherence h)

end Family

/-! ## 9.  Pendant sheet permutations: a limit automorphism on a dangling branch

On a target tree, delete the wall and take the component of a neighbour `root`.  If every
sheet of a set `D` (inside one wall block) is a singleton, and dangling, at every vertex and
occurrence of that branch, then any permutation of `D` applied on the branch alone is an
automorphism of the datum fixing every branch vertex and every stable path. -/

section PendantSwap

open TargetBranchRegion

variable {d : ℕ}

theorem relabel_refl' (P : SheetPartition d) : P.relabel (Equiv.refl _) = P := by
  apply SheetPartition.ext_repr
  funext x
  rfl

/-- A permutation supported on `D` and preserving it leaves invariant every partition in
which each sheet of `D` is a singleton. -/
theorem relabel_eq_self_of_singleton (P : SheetPartition d) (D : Fin d → Prop)
    (π : Equiv.Perm (Fin d)) (hπ : ∀ x, ¬ D x → π x = x)
    (hSingle : ∀ s, D s → ∀ t, P.Rel s t → t = s) : P.relabel π = P := by
  have hRepr : ∀ s, D s → P.repr s = s := fun s hs ↦ hSingle s hs _ (P.rel_repr_right s)
  have hInv : ∀ x, D x → D (π.symm x) := by
    intro x hx
    by_contra h
    have := hπ _ h
    rw [Equiv.apply_symm_apply] at this
    exact h (this ▸ hx)
  have hInvFix : ∀ x, ¬ D x → π.symm x = x := by
    intro x hx
    rw [Equiv.symm_apply_eq]
    exact (hπ x hx).symm
  apply SheetPartition.ext_repr
  funext x
  change π (P.repr (π.symm x)) = P.repr x
  by_cases hx : D x
  · rw [hRepr _ (hInv x hx), Equiv.apply_symm_apply, hRepr x hx]
  · rw [hInvFix x hx]
    have hr : ¬ D (P.repr x) := by
      intro h
      have := hSingle _ h x (P.rel_repr_left x)
      exact hx (this ▸ h)
    exact hπ _ hr

variable {T : CFGraph} {degree : ℕ} (M : GluingDatum T degree) (wall root : T.V)
  (hRoot : root ≠ wall) (D : Fin degree → Prop)

/-- **The pendant hypothesis on a branch**: every sheet of `D` is a singleton and dangling
at every vertex and every occurrence of the branch. -/
structure Pendant : Prop where
  vertex_single : ∀ v, vertexMoved wall root hRoot v = true → ∀ s, D s → ∀ t,
    (M.vertexPartition v).Rel s t → t = s
  edge_single : ∀ e, edgeMoved wall root hRoot e = true → ∀ s, D s → ∀ t,
    (M.edgePartition e).Rel s t → t = s
  vertex_dangling : ∀ v, vertexMoved wall root hRoot v = true → ∀ s, D s →
    nonDanglingValency M (M.sourceEndpoint v s) = 0
  edge_dangling : ∀ e, edgeMoved wall root hRoot e = true → ∀ s, D s →
    IsDangling M (M.sourceEdge e s)

variable {M wall root hRoot D}

/-- The permutation used on the branch and the identity elsewhere. -/
def branchPerm (moved : Bool) (π : Equiv.Perm (Fin degree)) : Equiv.Perm (Fin degree) :=
  if moved then π else Equiv.refl _

/-- **The pendant automorphism.** -/
def pendantIso (hP : Pendant M wall root hRoot D)
    (hD : ∀ s t, D s → D t → (M.vertexPartition wall).Rel s t)
    (π : Equiv.Perm (Fin degree)) (hπ : ∀ x, ¬ D x → π x = x) (hπD : ∀ x, D x → D (π x)) :
    GeometricDatumIso M M where
  targetVertex := Equiv.refl _
  targetEdge := Equiv.refl _
  ends _ := Or.inl rfl
  vertexPerm v := branchPerm (vertexMoved wall root hRoot v) π
  edgePerm e := branchPerm (edgeMoved wall root hRoot e) π
  vertexPartition v := by
    change M.vertexPartition v = (M.vertexPartition v).relabel _
    unfold branchPerm
    split_ifs with h
    · exact (relabel_eq_self_of_singleton _ D π hπ (hP.vertex_single v h)).symm
    · exact (relabel_refl' _).symm
  edgePartition e := by
    change M.edgePartition e = (M.edgePartition e).relabel _
    unfold branchPerm
    split_ifs with h
    · exact (relabel_eq_self_of_singleton _ D π hπ (hP.edge_single e h)).symm
    · exact (relabel_refl' _).symm
  compatible e v hv s := by
    unfold branchPerm
    by_cases he : edgeMoved wall root hRoot e = true <;>
      by_cases hvm : vertexMoved wall root hRoot v = true
    · rw [if_pos he, if_pos hvm, Equiv.symm_apply_apply]; rfl
    · rw [if_pos he, if_neg hvm]
      have hWall : v = wall := by
        rcases hv with h | h
        · subst h
          exact boundary_left wall root hRoot e (by rw [he]; simpa using hvm)
        · subst h
          exact boundary_right wall root hRoot e (by rw [he]; simpa using hvm)
      subst hWall
      change (M.vertexPartition v).Rel (π s) s
      by_cases hs : D s
      · exact hD _ _ (hπD s hs) hs
      · rw [hπ s hs]; rfl
    · exfalso
      apply he
      unfold edgeMoved
      rcases hv with h | h
      · rw [h, hvm]; simp
      · rw [h, hvm]; simp
    · rw [if_neg he, if_neg hvm]
      rfl

theorem pendantIso_sourceVertexEquiv_eq (hP : Pendant M wall root hRoot D)
    (hD : ∀ s t, D s → D t → (M.vertexPartition wall).Rel s t)
    (π : Equiv.Perm (Fin degree)) (hπ : ∀ x, ¬ D x → π x = x) (hπD : ∀ x, D x → D (π x))
    (vertex : M.SourceVertex) (hPos : 0 < nonDanglingValency M vertex) :
    (pendantIso hP hD π hπ hπD).sourceVertexEquiv vertex = vertex := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change branchPerm (vertexMoved wall root hRoot vertex.1.1) π vertex.1.2 = vertex.1.2
  unfold branchPerm
  split_ifs with h
  · apply hπ
    intro hc
    have hEq : M.sourceEndpoint vertex.1.1 vertex.1.2 = vertex := Subtype.ext (Prod.ext rfl vertex.2)
    have h0 := hP.vertex_dangling _ h _ hc
    rw [hEq] at h0
    omega
  · rfl

theorem pendantIso_sourceEdgeEquiv_eq (hP : Pendant M wall root hRoot D)
    (hD : ∀ s t, D s → D t → (M.vertexPartition wall).Rel s t)
    (π : Equiv.Perm (Fin degree)) (hπ : ∀ x, ¬ D x → π x = x) (hπD : ∀ x, D x → D (π x))
    (edge : M.SourceEdge) (hSurv : ¬ IsDangling M edge) :
    (pendantIso hP hD π hπ hπD).sourceEdgeEquiv edge = edge := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change branchPerm (edgeMoved wall root hRoot edge.1.1) π edge.1.2 = edge.1.2
  unfold branchPerm
  split_ifs with h
  · apply hπ
    intro hc
    have hEq : M.sourceEdge edge.1.1 edge.1.2 = edge := Subtype.ext (Prod.ext rfl edge.2)
    have h0 := hP.edge_dangling _ h _ hc
    rw [hEq] at h0
    exact hSurv h0
  · rfl

end PendantSwap

section PendantLimit

open TargetBranchRegion

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {w : Regrowth core y degree} {hy : Nondegenerate y}
  {wall root : (w.frame.limitTarget w.column).V} {hRoot : root ≠ wall} {D : Fin degree → Prop}

/-- **The pendant automorphism is a limit automorphism**: it fixes every branch vertex and
every stable path. -/
noncomputable def pendantLimitIso (hP : Pendant w.limit wall root hRoot D)
    (hD : ∀ s t, D s → D t → (w.limit.vertexPartition wall).Rel s t)
    (π : Equiv.Perm (Fin degree)) (hπ : ∀ x, ¬ D x → π x = x) (hπD : ∀ x, D x → D (π x)) :
    GeometricStar.LimitIso hy w w where
  datum := pendantIso hP hD π hπ hπD
  overCore_vertex branch := by
    congr 1
    apply Subtype.ext
    exact pendantIso_sourceVertexEquiv_eq hP hD π hπ hπD branch.1 (by have := branch.2; omega)
  overCore_row row := by
    congr 1
    induction row using Quot.ind with
    | mk edge =>
      change ((pendantIso hP hD π hπ hπD).nonDanglingEdgeEquiv _ edge).stablePath =
        edge.stablePath
      congr 1
      apply Subtype.ext
      exact pendantIso_sourceEdgeEquiv_eq hP hD π hπ hπD edge.1 edge.2

theorem pendantLimitIso_edgePerm (hP : Pendant w.limit wall root hRoot D)
    (hD : ∀ s t, D s → D t → (w.limit.vertexPartition wall).Rel s t)
    (π : Equiv.Perm (Fin degree)) (hπ : ∀ x, ¬ D x → π x = x) (hπD : ∀ x, D x → D (π x))
    (e : (w.frame.limitTarget w.column).edges) :
    (pendantLimitIso (hy := hy) hP hD π hπ hπD).datum.edgePerm e =
      branchPerm (edgeMoved wall root hRoot e) π := rfl

theorem pendantLimitIso_targetEdge (hP : Pendant w.limit wall root hRoot D)
    (hD : ∀ s t, D s → D t → (w.limit.vertexPartition wall).Rel s t)
    (π : Equiv.Perm (Fin degree)) (hπ : ∀ x, ¬ D x → π x = x) (hπD : ∀ x, D x → D (π x)) :
    (pendantLimitIso (hy := hy) hP hD π hπ hπD).datum.targetEdge = Equiv.refl _ := rfl

end PendantLimit

/-! ## 10.  The branch of an incident occurrence, and its pendant sheets -/

section BranchGeometry

open TargetBranchRegion Utilities

variable {T : CFGraph}

/-- The endpoint of an occurrence away from a given vertex. -/
def farEnd (wall : T.V) (e : T.edges) : T.V :=
  if (e : T.V × T.V).1 = wall then (e : T.V × T.V).2 else (e : T.V × T.V).1

theorem farEnd_ends {wall : T.V} {e : T.edges}
    (hInc : (e : T.V × T.V).1 = wall ∨ (e : T.V × T.V).2 = wall) :
    (e : T.V × T.V) = (wall, farEnd wall e) ∨ (e : T.V × T.V) = (farEnd wall e, wall) := by
  unfold farEnd
  by_cases h : (e : T.V × T.V).1 = wall
  · rw [if_pos h]; exact Or.inl (Prod.ext h rfl)
  · rw [if_neg h]; exact Or.inr (Prod.ext rfl (hInc.resolve_left h))

theorem farEnd_ne {wall : T.V} {e : T.edges}
    (hInc : (e : T.V × T.V).1 = wall ∨ (e : T.V × T.V).2 = wall) : farEnd wall e ≠ wall := by
  intro hEq
  have hMem : (e : T.V × T.V) ∈ T.edges := Multiset.coe_mem
  rcases farEnd_ends hInc with h | h <;> rw [h, hEq] at hMem <;> exact T.loopless wall hMem

theorem vertexMoved_farEnd {wall : T.V} {e : T.edges}
    (hInc : (e : T.V × T.V).1 = wall ∨ (e : T.V × T.V).2 = wall) :
    vertexMoved wall (farEnd wall e) (farEnd_ne hInc) (farEnd wall e) = true :=
  (vertexMoved_eq_true_iff _ _ _ _).mpr ⟨farEnd_ne hInc, SimpleGraph.Reachable.refl _⟩

theorem edgeMoved_self {wall : T.V} {e : T.edges}
    (hInc : (e : T.V × T.V).1 = wall ∨ (e : T.V × T.V).2 = wall) :
    edgeMoved wall (farEnd wall e) (farEnd_ne hInc) e = true := by
  unfold edgeMoved
  rcases farEnd_ends hInc with h | h <;> rw [h] <;>
    simp only [vertexMoved_wall, vertexMoved_farEnd hInc, Bool.false_or, Bool.or_false]

theorem farEnd_adj {wall : T.V} {e : T.edges}
    (hInc : (e : T.V × T.V).1 = wall ∨ (e : T.V × T.V).2 = wall) :
    (underlyingSimpleGraph T).Adj (farEnd wall e) wall := by
  have h := edge_underlying_adj e
  rcases farEnd_ends hInc with hEnds | hEnds
  · rw [hEnds] at h; exact h.symm
  · rw [hEnds] at h; exact h

/-- **On a target tree the branch of one incident occurrence misses every other one.** -/
theorem edgeMoved_other (hConnected : graph_connected T) (hGenus : genus T = 0)
    {wall : T.V} {e f : T.edges}
    (he : (e : T.V × T.V).1 = wall ∨ (e : T.V × T.V).2 = wall)
    (hf : (f : T.V × T.V).1 = wall ∨ (f : T.V × T.V).2 = wall) (hNe : f ≠ e) :
    edgeMoved wall (farEnd wall e) (farEnd_ne he) f = false := by
  have hCount : T.edges.card + 1 = Fintype.card T.V := by
    unfold genus at hGenus
    omega
  have hTree := (InducedFibreTreeCount.underlying_tree_and_num_edges_le_one T hConnected hCount).1
  have hRoots : farEnd wall e ≠ farEnd wall f := by
    intro hEq
    apply hNe
    have hOne : num_edges T wall (farEnd wall e) = 1 := by
      have h := IteratedContraction.num_edges_eq_one_of_genus_zero_of_connected T hConnected
        hGenus e
      rcases farEnd_ends he with hEnds | hEnds
      · simpa only [hEnds] using h
      · simpa only [hEnds, num_edges_symmetric T (farEnd wall e) wall] using h
    refine (M11BranchSeparation.target_occurrence_unique hOne f e ?_ (farEnd_ends he)).symm.symm
    rw [hEq]; exact farEnd_ends hf
  have hNot := M11BranchSeparation.not_vertexMember_of_distinct_neighbors hTree (farEnd_ne he)
    (farEnd_ne hf) hRoots (farEnd_adj he) (farEnd_adj hf)
  have hFar : vertexMoved wall (farEnd wall e) (farEnd_ne he) (farEnd wall f) = false := by
    cases hMoved : vertexMoved wall (farEnd wall e) (farEnd_ne he) (farEnd wall f)
    · rfl
    · exact (hNot ((vertexMoved_eq_true_iff _ _ _ _).mp hMoved)).elim
  unfold edgeMoved
  rcases farEnd_ends hf with hEnds | hEnds <;> rw [hEnds] <;> simp [hFar]

variable {degree : ℕ} (M : GluingDatum T degree)

/-- Adjacent target vertices lift to adjacent source vertices through one sheet. -/
theorem adjacent_same_sheet {u u' : T.V} (hne : u ≠ u') (hAdj : 0 < num_edges T u u')
    (s : Fin degree) :
    0 < num_edges M.sourceGraph (M.sourceEndpoint u s) (M.sourceEndpoint u' s) := by
  classical
  obtain ⟨pair, hPair, hEnds⟩ := GraphContraction.exists_mem_edges_of_num_edges_pos T u u' hAdj
  let targetEdge : T.edges := ⟨pair, ⟨0, Multiset.count_pos.mpr hPair⟩⟩
  have hFirstMem : targetEdge ∈ GluingDatum.incidentEdges u := by
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    change pair.1 = u ∨ pair.2 = u
    rcases hEnds with h | h <;> simp [h]
  have hSecondMem : targetEdge ∈ GluingDatum.incidentEdges u' := by
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    change pair.1 = u' ∨ pair.2 = u'
    rcases hEnds with h | h <;> simp [h]
  have hFirst := incident_sourceEdge_sourceEndpoint M u targetEdge hFirstMem s
  have hSecond := incident_sourceEdge_sourceEndpoint M u' targetEdge hSecondMem s
  have hNe : M.sourceEndpoint u s ≠ M.sourceEndpoint u' s := fun h ↦
    hne (congrArg (fun v : M.SourceVertex ↦ v.1.1) h)
  apply num_edges_pos_of_sourceEnds M (edge := M.sourceEdge targetEdge s)
  rcases hFirst with hFirst | hFirst <;> rcases hSecond with hSecond | hSecond
  · exact (hNe (hFirst.symm.trans hSecond)).elim
  · exact Or.inl (Prod.ext hFirst hSecond)
  · exact Or.inr (Prod.ext hSecond hFirst)
  · exact (hNe (hFirst.symm.trans hSecond)).elim

/-- **A dangling side through one sheet contains that sheet over the whole branch.** -/
theorem mem_side_of_moved {wall root : T.V} (hRoot : root ≠ wall) (s : Fin degree)
    {outer : M.SourceVertex} (cut : DanglingSide M.sourceGraph (M.sourceEndpoint root s) outer)
    (hOuter : outer.1.1 = wall) {v : T.V} (hv : vertexMoved wall root hRoot v = true) :
    M.sourceEndpoint v s ∈ cut.side := by
  obtain ⟨hvw, hReach⟩ := (vertexMoved_eq_true_iff _ _ _ _).mp hv
  obtain ⟨walk⟩ := hReach
  suffices key : ∀ (x z : {v : T.V // v ≠ wall}) (_ : (deletedGraph wall).Walk x z),
      M.sourceEndpoint x.1 s ∈ cut.side → M.sourceEndpoint z.1 s ∈ cut.side from
    key _ _ walk cut.left_mem
  intro x z p
  induction p with
  | nil => exact id
  | @cons x₁ x₂ x₃ hAdj _ ih =>
    intro hx
    apply ih
    have hAdj' : (underlyingSimpleGraph T).Adj x₁.1 x₂.1 := hAdj
    have hPos : 0 < num_edges T x₁.1 x₂.1 := hAdj'
    have hLift := adjacent_same_sheet M hAdj'.ne hPos s
    by_contra hOut
    have hCross := cut.cross_num_edges _ _ hx hOut
    have hNotPair : ¬ (M.sourceEndpoint x₁.1 s = M.sourceEndpoint root s ∧
        M.sourceEndpoint x₂.1 s = outer) := by
      rintro ⟨-, h⟩
      exact x₂.2 ((congrArg (fun v : M.SourceVertex ↦ v.1.1) h).trans hOuter)
    rw [hCross] at hLift
    split_ifs at hLift with h
    · exact hNotPair h
    · omega

end BranchGeometry

/-! ## 11.  The pendant hypothesis at a regrowth wall, from full dimensionality

Draisma--Vargas `lemma-dangling-no-glue` (every dangling vertex is a single sheet) is a
theorem for a full-dimensional datum (`PendantFibre.degree_one_of_nonDanglingValency_zero`);
away from the wall a limit vertex is literally a frame vertex, with the same surviving
valency (`WallDegeneration.nonDanglingValency_sourceVertexMap`, which needs the contraction
forest).  So every sheet whose occurrence into a branch dangles is a singleton, dangling
sheet over that whole branch. -/

section PendantAtWall

open TargetBranchRegion DanglingSideStructure

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

theorem sourceEndpoint_eq_of_mem {T : CFGraph} (M : GluingDatum T degree) {u : T.V}
    {e : T.edges} (hMem : e ∈ GluingDatum.incidentEdges u) (s : Fin degree) :
    M.sourceEndpoint u ((M.edgePartition e).repr s) = M.sourceEndpoint u s :=
  M11StarExhaustionProof.sourceEndpoint_of_rel M u
    ((edgePartition_refines_of_mem_incidentEdges M u e hMem).rel
      ((M.edgePartition e).rel_repr_left s))

/-- The dangling side of a branch occurrence through a sheet of a surviving block is the
branch side. -/
theorem exists_branch_cut {T : CFGraph} (M : GluingDatum T degree) {wall : T.V}
    {e : T.edges} (hInc : (e : T.V × T.V).1 = wall ∨ (e : T.V × T.V).2 = wall)
    {b s : Fin degree} (hs : (M.vertexPartition wall).Rel b s)
    (hPos : 0 < nonDanglingValency M (M.sourceEndpoint wall b))
    (hDang : IsDangling M (M.sourceEdge e s)) :
    Nonempty (DanglingSide M.sourceGraph (M.sourceEndpoint (farEnd wall e) s)
      (M.sourceEndpoint wall b)) := by
  have hX : M.sourceEndpoint wall s = M.sourceEndpoint wall b :=
    M11StarExhaustionProof.sourceEndpoint_of_rel M wall hs.symm
  have hMemWall : e ∈ GluingDatum.incidentEdges wall := by
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      using hInc
  have hMemFar : e ∈ GluingDatum.incidentEdges (farEnd wall e) := by
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases farEnd_ends hInc with h | h <;> rw [h] <;> simp
  have hW := sourceEndpoint_eq_of_mem M hMemWall s
  have hF := sourceEndpoint_eq_of_mem M hMemFar s
  have hNotIn : ∀ {outer : M.SourceVertex}
      (cut : DanglingSide M.sourceGraph (M.sourceEndpoint wall b) outer), False := by
    intro outer cut
    have h0 := nonDanglingValency_eq_zero_of_mem_side M cut cut.left_mem
    omega
  change Nonempty (DanglingSide M.sourceGraph
      (M.sourceEndpoint (e : T.V × T.V).1 ((M.edgePartition e).repr s))
      (M.sourceEndpoint (e : T.V × T.V).2 ((M.edgePartition e).repr s))) ∨
    Nonempty (DanglingSide M.sourceGraph
      (M.sourceEndpoint (e : T.V × T.V).2 ((M.edgePartition e).repr s))
      (M.sourceEndpoint (e : T.V × T.V).1 ((M.edgePartition e).repr s))) at hDang
  rcases farEnd_ends hInc with hEnds | hEnds <;> rw [hEnds] at hDang <;>
    simp only at hDang <;> rw [hW, hF, hX] at hDang
  · rcases hDang with h | h
    · obtain ⟨cut⟩ := h; exact (hNotIn cut).elim
    · exact h
  · rcases hDang with h | h
    · exact h
    · obtain ⟨cut⟩ := h; exact (hNotIn cut).elim

/-- **The pendant hypothesis at a regrowth wall.** -/
theorem pendant_at_wall (w : Regrowth core y degree) (hy : Nondegenerate y)
    (hNoGlue : DanglingEdgeNoGlue w.limit)
    {e : (w.frame.limitTarget w.column).edges}
    (hInc : (e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).1 =
        mergeVertex w ∨
      (e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).2 =
        mergeVertex w) (b : Fin degree)
    (hDang : ∀ s, (w.limit.vertexPartition (mergeVertex w)).Rel b s →
      IsDangling w.limit (w.limit.sourceEdge e s))
    (hPos : 0 < nonDanglingValency w.limit (w.limit.sourceEndpoint (mergeVertex w) b)) :
    Pendant w.limit (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc)
      (fun s ↦ (w.limit.vertexPartition (mergeVertex w)).Rel b s) := by
  have hVD : ∀ v, vertexMoved (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) v = true →
      ∀ s, (w.limit.vertexPartition (mergeVertex w)).Rel b s →
      nonDanglingValency w.limit (w.limit.sourceEndpoint v s) = 0 := by
    intro v hv s hs
    obtain ⟨cut⟩ := exists_branch_cut w.limit hInc hs hPos (hDang s hs)
    exact nonDanglingValency_eq_zero_of_mem_side w.limit cut
      (mem_side_of_moved w.limit (farEnd_ne hInc) s cut rfl hv)
  have hED : ∀ f, edgeMoved (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) f = true →
      ∀ s, (w.limit.vertexPartition (mergeVertex w)).Rel b s →
      IsDangling w.limit (w.limit.sourceEdge f s) := by
    intro f hf s hs
    have hEnd : ∃ u, vertexMoved (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) u =
        true ∧ f ∈ GluingDatum.incidentEdges u := by
      unfold edgeMoved at hf
      rcases Bool.or_eq_true_iff.mp hf with h | h
      · exact ⟨_, h, by simp [GluingDatum.incidentEdges]⟩
      · exact ⟨_, h, by simp [GluingDatum.incidentEdges]⟩
    obtain ⟨u, hu, hMem⟩ := hEnd
    exact (nonDanglingValency_eq_zero_iff w.limit _).mp (hVD u hu s hs) _
      (incident_sourceEdge_sourceEndpoint w.limit u f hMem s)
  refine ⟨?_, ?_, hVD, hED⟩
  · -- vertex singletons, through the frame
    intro v hv s hs t hst
    have hvWall : v ≠ mergeVertex w := by
      intro h
      rw [h, vertexMoved_wall] at hv
      exact Bool.false_ne_true hv
    have hva : v.1 ≠ (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1 := by
      intro h
      exact hvWall (Subtype.ext h)
    have hvb : v.1 ≠ (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2 := v.2
    have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest w.frame.data rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
      (InheritedLimitRows.forest w hy)
    set x := w.frame.data.sourceEndpoint v.1 s
    have hMap := WallDegeneration.nonDanglingValency_sourceVertexMap w.frame.data hCompat x hva hvb
    have hPart : w.limit.vertexPartition v = w.frame.data.vertexPartition v.1 :=
      contractVertexPartition_of_ne w.frame.data _ _ hva
    have hImage : sourceVertexMap w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column) x = w.limit.sourceEndpoint v s := by
      change w.limit.sourceEndpoint (GraphContraction.fold _ _ v.1)
        ((w.frame.data.vertexPartition v.1).repr s) = _
      have hFold : GraphContraction.fold w.frame.target (fst_ne_snd (w.frame.edgeOf w.column))
          v.1 = v := GraphContraction.fold_coe _ _ v
      refine (congrArg (fun z : (w.frame.limitTarget w.column).V ↦
        w.limit.sourceEndpoint z ((w.frame.data.vertexPartition v.1).repr s)) hFold).trans ?_
      apply M11StarExhaustionProof.sourceEndpoint_of_rel
      rw [hPart]
      exact (w.frame.data.vertexPartition v.1).rel_repr_left s
    rw [hImage] at hMap
    have h0 : nonDanglingValency w.frame.data x = 0 := hMap.symm.trans (hVD v hv s hs)
    obtain ⟨hOne, -⟩ := PendantFibre.degree_one_of_nonDanglingValency_zero w.frame.fullDim x h0
    change (w.frame.data.vertexPartition v.1).blockCard
      ((w.frame.data.vertexPartition v.1).repr s) = 1 at hOne
    have hBlock := (w.frame.data.vertexPartition v.1).block_eq_of_rel
      ((w.frame.data.vertexPartition v.1).rel_repr_right s)
    unfold SheetPartition.blockCard at hOne
    rw [← hBlock] at hOne
    have hSingle := (w.frame.data.vertexPartition v.1).block_eq_singleton_of_blockCard_eq_one
      s hOne
    rw [hPart] at hst
    have hMem := ((w.frame.data.vertexPartition v.1).mem_block_iff s t).mpr hst
    rw [hSingle, Finset.mem_singleton] at hMem
    exact hMem
  · -- occurrence singletons, from no-glue
    intro f hf s hs t hst
    have hIndex := hNoGlue _ (hED f hf s hs)
    change (w.limit.edgePartition f).blockCard ((w.limit.edgePartition f).repr s) = 1 at hIndex
    have hBlock := (w.limit.edgePartition f).block_eq_of_rel
      ((w.limit.edgePartition f).rel_repr_right s)
    unfold SheetPartition.blockCard at hIndex
    rw [← hBlock] at hIndex
    have hSingle := (w.limit.edgePartition f).block_eq_singleton_of_blockCard_eq_one s hIndex
    have hMem := ((w.limit.edgePartition f).mem_block_iff s t).mpr hst
    rw [hSingle, Finset.mem_singleton] at hMem
    exact hMem

end PendantAtWall

/-! ## 12.  Coherence is always achievable: re-choose the limit isomorphism -/

section CoherenceAchieved

open TargetBranchRegion

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **Every star member has a coherent limit isomorphism.**  Compose any limit isomorphism
with the pendant automorphism that permutes the distinguished block's sheets on the third
direction's branch by `σ ∘ τ⁻¹`. -/
theorem exists_coherent (w : Regrowth core y degree) (hy : Nondegenerate y)
    {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
    (input : W3SourceInput w.limit star) (other : Regrowth core y degree)
    (ψ : GeometricStar.LimitIso hy other w) (b : Fin degree)
    (L T : (w.frame.limitTarget w.column).edges)
    (hL : L ∈ GluingDatum.incidentEdges (mergeVertex w))
    (hT : T ∈ GluingDatum.incidentEdges (mergeVertex w)) (hLT : L ≠ T)
    (hDang : ∀ s, (w.limit.vertexPartition (mergeVertex w)).Rel b s →
      IsDangling w.limit (w.limit.sourceEdge T s))
    (hPos : 0 < nonDanglingValency w.limit (w.limit.sourceEndpoint (mergeVertex w) b)) :
    ∃ ψ' : GeometricStar.LimitIso hy other w,
      Coherent (isoOf w hy other ψ') b L T (mergeVertex other) := by
  classical
  have hIncT : ((T : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).1 =
      mergeVertex w ∨
      (T : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).2 =
        mergeVertex w) := by
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hT
  have hIncL : ((L : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).1 =
      mergeVertex w ∨
      (L : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).2 =
        mergeVertex w) := by
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hL
  set iso := isoOf w hy other ψ
  have hW := isoOf_wall w hy input other ψ
  set σ := iso.edgePerm (iso.targetEdge.symm L)
  set τ := iso.edgePerm (iso.targetEdge.symm T)
  have hσ := edgePerm_agree_symm iso hW L hL
  have hτ := edgePerm_agree_symm iso hW T hT
  have hbσ := sel_iff iso hW b σ hσ
  have hbτ := sel_iff iso hW b τ hτ
  set D : Fin degree → Prop := fun x ↦ (w.limit.vertexPartition (mergeVertex w)).Rel b x
  have h1 : ∀ x, D x → D ((τ.symm.trans σ) x) := by
    intro x hx
    have : D (τ (τ.symm x)) := by rw [Equiv.apply_symm_apply]; exact hx
    exact (hbσ _).mp ((hbτ _).mpr this)
  set π := piecewisePerm D D (τ.symm.trans σ) (Equiv.refl _) h1 (fun _ hx ↦ hx)
  have hπ : ∀ x, ¬ D x → π x = x := fun x hx ↦ piecewisePerm_of_neg hx
  have hπpos : ∀ x, D x → π x = (τ.symm.trans σ) x := fun x hx ↦ piecewisePerm_of_pos hx
  have hπD : ∀ x, D x → D (π x) := fun x hx ↦ by rw [hπpos x hx]; exact h1 x hx
  have hP := pendant_at_wall w hy input.dangling_no_glue hIncT b hDang hPos
  have hD : ∀ s t, D s → D t → (w.limit.vertexPartition (mergeVertex w)).Rel s t :=
    fun s t hs ht ↦ hs.symm.trans ht
  set α := pendantLimitIso (hy := hy) hP hD π hπ hπD
  refine ⟨ψ.trans α, ?_⟩
  intro s hs
  set iso' := isoOf w hy other (ψ.trans α)
  have hW' := isoOf_wall w hy input other (ψ.trans α)
  have hTsymm : iso'.targetEdge.symm T = iso.targetEdge.symm T := rfl
  have hLsymm : iso'.targetEdge.symm L = iso.targetEdge.symm L := rfl
  have hTmap : iso'.edgePerm (iso'.targetEdge.symm T) s =
      branchPerm (edgeMoved (mergeVertex w) (farEnd (mergeVertex w) T) (farEnd_ne hIncT)
        (iso.targetEdge (iso.targetEdge.symm T))) π (τ s) := rfl
  have hLmap : iso'.edgePerm (iso'.targetEdge.symm L) s =
      branchPerm (edgeMoved (mergeVertex w) (farEnd (mergeVertex w) T) (farEnd_ne hIncT)
        (iso.targetEdge (iso.targetEdge.symm L))) π (σ s) := rfl
  rw [Equiv.apply_symm_apply, edgeMoved_self hIncT] at hTmap
  rw [Equiv.apply_symm_apply, edgeMoved_other (W4StarParity.limitTarget_connected w)
    (W4StarParity.limitTarget_genus w) hIncT hIncL hLT] at hLmap
  unfold branchPerm at hTmap hLmap
  rw [if_pos rfl] at hTmap
  rw [if_neg Bool.false_ne_true] at hLmap
  have hτ' := edgePerm_agree_symm iso' hW' T hT
  have hSel := (sel_iff iso' hW' b _ hτ' s).mp hs
  rw [hTmap] at hSel
  have hτs : D (τ s) := by
    by_contra h
    rw [hπ _ h] at hSel
    exact h hSel
  rw [hTmap, hLmap, hπpos _ hτs]
  change (w.limit.edgePartition L).Rel (σ (τ.symm (τ s))) (σ s)
  rw [Equiv.symm_apply_apply]
  rfl

end CoherenceAchieved

/-! ## 13.  The W3 nd2 star exhaustion, with no hypothesis -/

section Unconditional

open W3Nd2FineRefinement

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd2Profile w.limit input.distinguishedBlock)

/-- **Fine coherence holds at every nd2 wall.** -/
theorem fineCoherenceAt : FineCoherenceAt w hy input profile := by
  intro member
  obtain ⟨ψ₀⟩ := member.specializes
  obtain ⟨ψ, hψ⟩ := exists_coherent w hy input member.member ψ₀ input.distinguishedBlock.1
    (smallTarget input profile) (thirdTarget input profile) (smallTarget_mem input profile)
    (thirdTarget_mem input profile) (thirdTarget_ne_small input profile).symm
    (fun s hs ↦ thirdSourceEdge_isDangling input profile s hs)
    (lt_of_lt_of_eq (by decide : 0 < 2) profile.valency.symm)
  exact ⟨ψ, fun _ ↦ hψ⟩

/-- **Stage 2 at one nd2 wall.** -/
theorem exhausts {incoming : Fin 2}
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd2CommonBalance.candidates input profile incoming).datum (Fin p)) :
    W3Nd2StarCensusProof.Exhausts w hy input profile incomingFD :=
  exhausts_of_fineCoherence w hy input profile incomingFD (fineCoherenceAt w hy input profile)

end Unconditional

section UnconditionalFamily

variable (degree n p : ℕ)

/-- **Fine coherence holds at every W3 nd2 wall.** -/
theorem w3Nd2FineCoherence : W3Nd2FineCoherence degree n p :=
  fun _ _ hy w _ _ _ input profile ↦ fineCoherenceAt w hy input profile

/-- **The W3 nd2 star exhaustion, at every core, degree and request.** -/
theorem w3Nd2StarExhaustion : W3Nd2StarCensusProof.W3Nd2StarExhaustion degree n p :=
  w3Nd2StarExhaustion_of_fineCoherence (w3Nd2FineCoherence degree n p)

/-- **The W3 nd2 star census**, unconditionally. -/
theorem w3Nd2StarCensus : W3Nd2StarCensusProof.W3Nd2StarCensus degree n p :=
  W3Nd2StarCensusProof.w3Nd2StarCensus_of_exhaustion (w3Nd2StarExhaustion degree n p)

/-- **The `w3Nd2CoarseFine` clause of `FamilyStarParity` at genus six and degree four,
with no hypothesis.** -/
theorem familyStarParity_w3Nd2 :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w3Nd2CoarseFine :=
  W3Nd2StarCensusProof.familyStarParity_w3Nd2_of_exhaustion (w3Nd2StarExhaustion _ _ _)

end UnconditionalFamily

end DraismaVargas.Count.W3Nd2StarExhaustionProof
