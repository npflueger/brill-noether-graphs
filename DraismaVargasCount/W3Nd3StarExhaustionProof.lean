import DraismaVargasCount.W3Nd2StarExhaustionProof
import DraismaVargasCount.W3Nd3StarCensusProof

/-!
# W3 nd3 star exhaustion: the `w3Nd3CoarseFine` clause with no hypothesis

Source: Draisma--Vargas Part I (arXiv:1909.12924), case `{w3-r1-nd3-t3}`, Figure 30 and
Equation (4), and `lemma-dangling-no-glue`.  Where the prose of this case and Figure 30
differ (on which value of `α` gives which member), the formalization follows Figure 30.
The residue proved here is the one isolated in `W3Nd3StarCensusProof` §5; the machinery
is that of `W3Nd2StarExhaustionProof` §1–§4, §9–§12.  This completes the W3 nd3 case of
the star parity in step 2 of `Assembly`.

## The result, in one paragraph

The same argument as W3 nd2, with the doubled direction `t₃` (carrying the two smaller
survivors `e₂`, `e₃`) in the role of nd2's small direction, the largest direction `t₄` in
the role of the large one, and the third direction `t₂` -- again discrete and entirely
dangling on the distinguished block -- as the direction whose occurrence permutation must
be made coherent.  The nd3 profile pulls back along the member's limit isomorphism (§1),
Figure 30's positions are pieces (§2), Part I's identification
(`W3Nd3IncomingMatching.coarse_sameBlocks`/`fine_sameBlocks`) gives the member's shape (§3),
the family-generic transports of the nd2 file give the two receipts (§4), and
`W3Nd2StarExhaustionProof.exists_coherent` re-chooses the limit isomorphism so that the fine
receipt's coherence holds (§7).  Hence `w3Nd3StarExhaustion`, `w3Nd3StarCensus`,
`w3Nd3StarCardTwo` (every such star has exactly two classes) and `familyStarParity_w3Nd3`,
with no hypothesis.

## What is proved

* §1 `index_symm`, `target_symm`, `profile_pullback`: the nd3 profile along an arbitrary
  `GeometricDatumIso` (the W3 input pullback is the nd2 file's).
* §2 `coarse_left/right/newEdge`, `fine_left/right/newEdge`, `incident_nd3`; `FineCoherent`.
* §3 `profile₁`, `shared₁`, `largest₁`, `hSame₁` (the doubled direction pulls back),
  `member_cases`, `member_coarseShape`, `member_fineShape`.
* §4 `transport_zero`, `transport_one`, `fineCoherent_of_positionTransport` (coherence is
  necessary for the fine receipt).  §5–§6: exhaustion and the family clause from
  `FineCoherenceAt` / `W3Nd3FineCoherence`.
* §7 `fineCoherenceAt`, `exhausts`, `w3Nd3FineCoherence`, **`w3Nd3StarExhaustion`**,
  **`w3Nd3StarCensus`**, **`w3Nd3StarCardTwo`**, **`familyStarParity_w3Nd3`**.

## What is NOT proved (every hypothesis, explicitly)

* Nothing is assumed: the main theorems have no hypothesis beyond their binders;
  `exhausts` does not use the `w3Nd3CoarseFine` tag, only a W3 input, an nd3 profile and
  `hSame`.
* **Non-vacuity is not shown**: no concrete `w3Nd3CoarseFine` regrowth is constructed,
  so no `example` at a concrete instance is given.

## Tempting inferences, checked

* (i) *"Follow the M-11 exhaustion (`M11StarExhaustionProof`)"*: as for nd2 -- this holds
  for the coarse position; the fine one additionally needs coherence of the third
  direction, obtained by re-choosing the limit isomorphism (a pendant automorphism), not
  from the M-11 builder alone.
* (ii) *"W3Nd3 may have an e₂/e₃ coherence question; where the rows coincide the fine column
  is symmetric."*  **Settled in Lean, and the question does not arise.**  Figure 30's
  positions see `e₂`, `e₃` only through the doubled direction's edge partition `{F, S}` of
  the distinguished block (`fine_right`, `fine_newEdge`: the piece is
  `edgePartition profile.first.1.1.1`, and `hSame` makes it `e₃`'s too), which every limit
  isomorphism carries by its `t₃` occurrence permutation; the pulled-back profile names
  `e₂`, `e₃` by that same isomorphism (`profile_pullback`), so whether it exchanges them is
  irrelevant and no row-coincidence case split is needed.  The coherence that *is* needed
  is between `t₂` (dangling) and `t₃`, and `exists_coherent` supplies it at every wall.
* (iii) Shared patterns: see the nd2 file; this file adds nothing family-free.

## Consumers

The `w3Nd3CoarseFine` clause of the star parity (step 2 of `Assembly`).
-/

namespace DraismaVargas.Count.W3Nd3StarExhaustionProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open ThirdEquation W3R1SourceProfile
open M11StarExhaustionProof (blockPre incidentEquivOf_target)
open W3Nd2StarExhaustionProof (Piece piece_of_blocks input_pullback distinguishedBlock_pullback
  sourceVertexEquiv_distinguished blockCard_distinguished distinguishedIncident Coherent
  nonempty_transportFree_coarse nonempty_transportFree_fine coherent_of_transportFree
  rightOf_pullback isoOf isoOf_wall star₁ input₁ sel₁_eq divalent₁ exists_coherent)
open W3Nd2SourceCandidates (rightOf)

/-! ## 1.  The nd3 profile, pulled back along a limit isomorphism -/

section Pullback

open W4Assembly

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
  (iso : GeometricDatumIso first second)
  {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
  {star' : ThreeStar target₂ wall'} (input : W3SourceInput second star')

theorem index_symm (e : IncidentSourceEdge second
      (WallBlock.sourceVertex second wall' input.distinguishedBlock)) :
    first.sourceEdgeIndex ((distinguishedIncident iso hWall input).symm e).1 =
      second.sourceEdgeIndex e.1 := by
  have h := iso.sourceEdgeIndex_map ((distinguishedIncident iso hWall input).symm e).1
  change second.sourceEdgeIndex ((distinguishedIncident iso hWall input)
    ((distinguishedIncident iso hWall input).symm e)).1 = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem target_symm (e : IncidentSourceEdge second
      (WallBlock.sourceVertex second wall' input.distinguishedBlock)) :
    iso.targetEdge ((distinguishedIncident iso hWall input).symm e).1.1.1 = e.1.1.1 := by
  have h := incidentEquivOf_target iso (sourceVertexEquiv_distinguished iso hWall input)
    ((distinguishedIncident iso hWall input).symm e)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem target_symm' (e : IncidentSourceEdge second
      (WallBlock.sourceVertex second wall' input.distinguishedBlock)) :
    ((distinguishedIncident iso hWall input).symm e).1.1.1 = iso.targetEdge.symm e.1.1.1 :=
  (Equiv.eq_symm_apply _).mpr (target_symm iso hWall input e)

/-- **The nd3 profile pulls back along a limit isomorphism.** -/
noncomputable def profile_pullback (hConnected : first.Connected)
    (profile : Nd3Profile second input.distinguishedBlock) :
    Nd3Profile first (input_pullback iso hWall input).distinguishedBlock where
  first := (distinguishedIncident iso hWall input).symm profile.first
  second := (distinguishedIncident iso hWall input).symm profile.second
  largest := (distinguishedIncident iso hWall input).symm profile.largest
  first_ne_second := fun h ↦
    profile.first_ne_second ((distinguishedIncident iso hWall input).symm.injective h)
  first_ne_largest := fun h ↦
    profile.first_ne_largest ((distinguishedIncident iso hWall input).symm.injective h)
  second_ne_largest := fun h ↦
    profile.second_ne_largest ((distinguishedIncident iso hWall input).symm.injective h)
  surviving := by
    classical
    ext e
    rw [mem_survivors, ← iso.isDangling_map_iff hConnected e.1]
    change ¬ IsDangling second ((distinguishedIncident iso hWall input) e).1 ↔ _
    rw [← mem_survivors, profile.surviving]
    simp only [Finset.mem_insert, Finset.mem_singleton, Equiv.eq_symm_apply]
  first_le := by
    rw [index_symm iso hWall input, index_symm iso hWall input]; exact profile.first_le
  second_le := by
    rw [index_symm iso hWall input, index_symm iso hWall input]; exact profile.second_le
  first_target_ne := by
    rw [target_symm' iso hWall input, target_symm' iso hWall input]
    exact fun h ↦ profile.first_target_ne (iso.targetEdge.symm.injective h)
  second_target_ne := by
    rw [target_symm' iso hWall input, target_symm' iso hWall input]
    exact fun h ↦ profile.second_target_ne (iso.targetEdge.symm.injective h)
  index_sum := by
    rw [index_symm iso hWall input, index_symm iso hWall input, index_symm iso hWall input,
      blockCard_distinguished iso hWall input]
    exact profile.index_sum

end Pullback

/-! ## 2.  Figure 30's two positions as shapes -/

section CandidateShapes

open W3Nd3SourceCandidates W3Nd3StableGraph W3Nd3LimitMatrix

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  (input : W3SourceInput data star) (profile : Nd3Profile data input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)

theorem coarse_left :
    Piece (data.vertexPartition wall) input.distinguishedBlock.1 (data.vertexPartition wall)
      (data.edgePartition profile.first.1.1.1)
      (M11StarCensusProof.pasted (coarseCandidate input profile hSame)).left :=
  piece_of_blocks (SheetPartition.Refines.refl _) (fine_refines_wall input profile)
    (fun s hs ↦ coarse_pasted_left_block_selected input profile hSame s hs)
    (fun s hs ↦ coarse_background_left_block input profile hSame s hs)

theorem coarse_right :
    Piece (data.vertexPartition wall) input.distinguishedBlock.1 (data.vertexPartition wall)
      (data.vertexPartition wall)
      (M11StarCensusProof.pasted (coarseCandidate input profile hSame)).right :=
  piece_of_blocks (SheetPartition.Refines.refl _) (SheetPartition.Refines.refl _)
    (fun s hs ↦ coarse_pasted_right_block_selected input profile hSame s hs)
    (fun s hs ↦ coarse_background_right_block input profile hSame s hs)

theorem coarse_newEdge :
    Piece (data.vertexPartition wall) input.distinguishedBlock.1 (data.vertexPartition wall)
      (data.edgePartition profile.first.1.1.1)
      (M11StarCensusProof.pasted (coarseCandidate input profile hSame)).newEdge :=
  piece_of_blocks (SheetPartition.Refines.refl _) (fine_refines_wall input profile)
    (fun s hs ↦ coarse_pasted_newEdge_block_selected input profile hSame s hs)
    (fun s hs ↦ coarse_background_newEdge_block input profile hSame s hs)

theorem fine_left :
    Piece (data.vertexPartition wall) input.distinguishedBlock.1 (data.vertexPartition wall)
      (data.edgePartition (largestTarget input profile))
      (M11StarCensusProof.pasted (fineCandidate input profile hSame)).left :=
  piece_of_blocks (SheetPartition.Refines.refl _) (largest_refines_wall input profile)
    (fun s hs ↦ fine_pasted_left_block_selected input profile hSame s hs)
    (fun s hs ↦ fine_background_left_block input profile hSame s hs)

theorem fine_right :
    Piece (data.vertexPartition wall) input.distinguishedBlock.1
      (data.edgePartition profile.first.1.1.1) (data.vertexPartition wall)
      (M11StarCensusProof.pasted (fineCandidate input profile hSame)).right :=
  piece_of_blocks (fine_refines_wall input profile) (SheetPartition.Refines.refl _)
    (fun s hs ↦ fine_pasted_right_block_selected input profile hSame s hs)
    (fun s hs ↦ fine_background_right_block input profile hSame s hs)

theorem fine_newEdge :
    Piece (data.vertexPartition wall) input.distinguishedBlock.1
      (data.edgePartition profile.first.1.1.1)
      (data.edgePartition (largestTarget input profile))
      (M11StarCensusProof.pasted (fineCandidate input profile hSame)).newEdge :=
  piece_of_blocks (fine_refines_wall input profile) (largest_refines_wall input profile)
    (fun s hs ↦ fine_pasted_newEdge_block_selected input profile hSame s hs)
    (fun s hs ↦ fine_background_newEdge_block input profile hSame s hs)

omit hSame in
theorem incident_nd3 (e : target.edges) :
    e ∈ GluingDatum.incidentEdges wall ↔
      e = profile.first.1.1.1 ∨ e = largestTarget input profile ∨
        e = thirdTarget input profile := by
  rw [incidentEdges_eq input profile]
  simp only [Finset.mem_insert, Finset.mem_singleton]

end CandidateShapes

/-- **Fine coherence at an nd3 wall**: the third direction against the doubled one. -/
abbrev FineCoherent {target₁ target₂ : CFGraph} {degree : ℕ}
    {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
    {wall' : target₂.V} {star' : ThreeStar target₂ wall'}
    (iso : GeometricDatumIso first second) (input : W3SourceInput second star')
    (profile : Nd3Profile second input.distinguishedBlock) (v : target₁.V) : Prop :=
  Coherent iso input.distinguishedBlock.1 profile.first.1.1.1
    (W3Nd3SourceCandidates.thirdTarget input profile) v

/-! ## 3.  An arbitrary star member, read through its limit isomorphism -/

section Member

open W4Assembly W3Nd3SourceCandidates W3Nd2IncomingTargetPlacement

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd3Profile w.limit input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)
  (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)

/-- The member's pulled-back nd3 profile. -/
noncomputable abbrev profile₁ :
    Nd3Profile other.limit (input₁ w hy input other ψ).distinguishedBlock :=
  profile_pullback (isoOf w hy other ψ) (isoOf_wall w hy input other ψ) input
    (InheritedLimitRows.limit_connected other) profile

theorem shared₁ : (profile₁ w hy input profile other ψ).first.1.1.1 =
    (isoOf w hy other ψ).targetEdge.symm profile.first.1.1.1 :=
  target_symm' (isoOf w hy other ψ) (isoOf_wall w hy input other ψ) input profile.first

theorem largest₁ : largestTarget (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ) =
    (isoOf w hy other ψ).targetEdge.symm (largestTarget input profile) :=
  target_symm' (isoOf w hy other ψ) (isoOf_wall w hy input other ψ) input profile.largest

include hSame in
/-- The doubled direction pulls back. -/
theorem hSame₁ : (profile₁ w hy input profile other ψ).first.1.1.1 =
    (profile₁ w hy input profile other ψ).second.1.1.1 := by
  have h2 : (profile₁ w hy input profile other ψ).second.1.1.1 =
      (isoOf w hy other ψ).targetEdge.symm profile.second.1.1.1 :=
    target_symm' (isoOf w hy other ψ) (isoOf_wall w hy input other ψ) input profile.second
  rw [shared₁, h2, hSame]

include hSame in
/-- **The member-type dichotomy** (Part I's orientation dichotomy at the member). -/
theorem member_cases :
    divalent₁ w hy input other ψ = (profile₁ w hy input profile other ψ).first.1.1.1 ∨
      divalent₁ w hy input other ψ = (profile₁ w hy input profile other ψ).largest.1.1.1 :=
  W3Nd3IncomingCensus.divalentOccurrence_eq_shared_or_largest other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim (InheritedLimitRows.forest other hy)
    (WallAdmissibility.danglingCompatible_of_contractionForest other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
      (InheritedLimitRows.forest other hy))
    (star₁ w hy input other ψ) (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    (hSame₁ w hy input profile hSame other ψ)

/-- The resolution a member reads off at a placement. -/
noncomputable abbrev res (placement : (other.frame.limitTarget other.column).edges → Bool)
    (hP : W3Nd3StarCensusProof.PlacementSpec other placement) :=
  M11WallExhaustion.incomingResolution other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    placement hP

/-- **A shared-type member has the coarse shape.** -/
theorem member_coarseShape
    (hShared : divalent₁ w hy input other ψ = (profile₁ w hy input profile other ψ).first.1.1.1) :
    let C := coarseCandidate (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
      (hSame₁ w hy input profile hSame other ψ)
    ∃ hP : W3Nd3StarCensusProof.PlacementSpec other C.right,
    Piece (other.limit.vertexPartition (mergeVertex other))
        (blockPre (isoOf w hy other ψ) (mergeVertex other) input.distinguishedBlock.1).1
        (other.limit.vertexPartition (mergeVertex other))
        (other.limit.edgePartition ((isoOf w hy other ψ).targetEdge.symm profile.first.1.1.1))
        (res other C.right hP).left ∧
      Piece (other.limit.vertexPartition (mergeVertex other))
        (blockPre (isoOf w hy other ψ) (mergeVertex other) input.distinguishedBlock.1).1
        (other.limit.vertexPartition (mergeVertex other))
        (other.limit.vertexPartition (mergeVertex other))
        (res other C.right hP).right ∧
      Piece (other.limit.vertexPartition (mergeVertex other))
        (blockPre (isoOf w hy other ψ) (mergeVertex other) input.distinguishedBlock.1).1
        (other.limit.vertexPartition (mergeVertex other))
        (other.limit.edgePartition ((isoOf w hy other ψ).targetEdge.symm profile.first.1.1.1))
        (res other C.right hP).newEdge := by
  intro C
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    (InheritedLimitRows.forest other hy)
  refine ⟨W3Nd3IncomingMatching.coarse_placement_of_eq_shared other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim (star₁ w hy input other ψ) (input₁ w hy input other ψ)
    (profile₁ w hy input profile other ψ) (hSame₁ w hy input profile hSame other ψ) hShared, ?_⟩
  have hV := W3Nd3IncomingMatching.coarse_vertexPartitions_sameBlocks other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim (InheritedLimitRows.forest other hy) hCompat
    (star₁ w hy input other ψ) (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    (hSame₁ w hy input profile hSame other ψ) hShared
  have hE := W3Nd3IncomingMatching.coarse_edgePartitions_sameBlocks other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim (InheritedLimitRows.forest other hy) hCompat
    (star₁ w hy input other ψ) (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    (hSame₁ w hy input profile hSame other ψ) hShared
  have hL := coarse_left (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    (hSame₁ w hy input profile hSame other ψ)
  have hR := coarse_right (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    (hSame₁ w hy input profile hSame other ψ)
  have hN := coarse_newEdge (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    (hSame₁ w hy input profile hSame other ψ)
  rw [sel₁_eq, shared₁] at hL hN
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

/-- **A largest-type member has the fine shape.** -/
theorem member_fineShape
    (hLargest : divalent₁ w hy input other ψ = (profile₁ w hy input profile other ψ).largest.1.1.1) :
    let C := fineCandidate (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
      (hSame₁ w hy input profile hSame other ψ)
    ∃ hP : W3Nd3StarCensusProof.PlacementSpec other C.right,
    Piece (other.limit.vertexPartition (mergeVertex other))
        (blockPre (isoOf w hy other ψ) (mergeVertex other) input.distinguishedBlock.1).1
        (other.limit.vertexPartition (mergeVertex other))
        (other.limit.edgePartition ((isoOf w hy other ψ).targetEdge.symm (largestTarget input profile)))
        (res other C.right hP).left ∧
      Piece (other.limit.vertexPartition (mergeVertex other))
        (blockPre (isoOf w hy other ψ) (mergeVertex other) input.distinguishedBlock.1).1
        (other.limit.edgePartition ((isoOf w hy other ψ).targetEdge.symm profile.first.1.1.1))
        (other.limit.vertexPartition (mergeVertex other))
        (res other C.right hP).right ∧
      Piece (other.limit.vertexPartition (mergeVertex other))
        (blockPre (isoOf w hy other ψ) (mergeVertex other) input.distinguishedBlock.1).1
        (other.limit.edgePartition ((isoOf w hy other ψ).targetEdge.symm profile.first.1.1.1))
        (other.limit.edgePartition ((isoOf w hy other ψ).targetEdge.symm (largestTarget input profile)))
        (res other C.right hP).newEdge := by
  intro C
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    (InheritedLimitRows.forest other hy)
  refine ⟨W3Nd3IncomingMatching.fine_placement_of_eq_largest other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim (star₁ w hy input other ψ) (input₁ w hy input other ψ)
    (profile₁ w hy input profile other ψ) (hSame₁ w hy input profile hSame other ψ) hLargest, ?_⟩
  have hV := W3Nd3IncomingMatching.fine_vertexPartitions_sameBlocks other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim (InheritedLimitRows.forest other hy) hCompat
    (star₁ w hy input other ψ) (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    (hSame₁ w hy input profile hSame other ψ) hLargest
  have hE := W3Nd3IncomingMatching.fine_edgePartitions_sameBlocks other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim (InheritedLimitRows.forest other hy) hCompat
    (star₁ w hy input other ψ) (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    (hSame₁ w hy input profile hSame other ψ) hLargest
  have hL := fine_left (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    (hSame₁ w hy input profile hSame other ψ)
  have hR := fine_right (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    (hSame₁ w hy input profile hSame other ψ)
  have hN := fine_newEdge (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    (hSame₁ w hy input profile hSame other ψ)
  rw [sel₁_eq, largest₁] at hL
  rw [sel₁_eq, shared₁] at hR
  rw [sel₁_eq, shared₁, largest₁] at hN
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

/-! ## 4.  The two receipts, and the coherence they need -/

section Receipts

open W3Nd3SourceCandidates

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd3Profile w.limit input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)
  (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)

/-- **Position `0` receives every shared-type member**, with no coherence condition. -/
theorem transport_zero
    (hShared : divalent₁ w hy input other ψ = (profile₁ w hy input profile other ψ).first.1.1.1) :
    Nonempty (W3Nd3StarCensusProof.PositionTransport w hy input profile hSame other ψ
      ⟨0, by decide⟩) := by
  obtain ⟨hP₁, hL, hR, hN⟩ := member_coarseShape w hy input profile hSame other ψ hShared
  set C := coarseCandidate (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    (hSame₁ w hy input profile hSame other ψ)
  have hEq : W3Nd3StarCensusProof.pulledPlacement w hy input profile hSame other ψ ⟨0, by decide⟩ =
      C.right := by
    funext e
    change rightOf profile.first.1.1.1 ((isoOf w hy other ψ).targetEdge e) =
      rightOf (profile₁ w hy input profile other ψ).first.1.1.1 e
    rw [shared₁, rightOf_pullback]
  have key : ∀ (pl : (other.frame.limitTarget other.column).edges → Bool) (hpl : pl = C.right)
      (hP : W3Nd3StarCensusProof.PlacementSpec other pl),
      Nonempty (ResolutionExpansionFree.TransportFree (isoOf w hy other ψ) (mergeVertex other)
        (mergeVertex w) pl (rightOf profile.first.1.1.1) (res other pl hP)
        (M11StarCensusProof.pasted (coarseCandidate input profile hSame))) := by
    intro pl hpl hP
    subst hpl
    refine nonempty_transportFree_coarse (isoOf w hy other ψ) (isoOf_wall w hy input other ψ)
      input.distinguishedBlock.1 _ _ _ (incident_nd3 input profile) _ _ _ ?_ hL hR hN
      (coarse_left input profile hSame) (coarse_right input profile hSame)
      (coarse_newEdge input profile hSame)
    intro e
    rw [rightOf_pullback, ← shared₁]
    rfl
  obtain ⟨t⟩ := key _ hEq (hEq ▸ hP₁)
  exact ⟨⟨hEq ▸ hP₁, t⟩⟩

/-- **Position `1` receives every largest-type member along a coherent isomorphism.** -/
theorem transport_one
    (hLargest : divalent₁ w hy input other ψ = (profile₁ w hy input profile other ψ).largest.1.1.1)
    (hCoh : FineCoherent (isoOf w hy other ψ) input profile (mergeVertex other)) :
    Nonempty (W3Nd3StarCensusProof.PositionTransport w hy input profile hSame other ψ
      ⟨1, by decide⟩) := by
  obtain ⟨hP₁, hL, hR, hN⟩ := member_fineShape w hy input profile hSame other ψ hLargest
  set C := fineCandidate (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    (hSame₁ w hy input profile hSame other ψ)
  have hEq : W3Nd3StarCensusProof.pulledPlacement w hy input profile hSame other ψ ⟨1, by decide⟩ =
      C.right := by
    funext e
    change rightOf (largestTarget input profile) ((isoOf w hy other ψ).targetEdge e) =
      rightOf (largestTarget (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)) e
    rw [largest₁, rightOf_pullback]
  have key : ∀ (pl : (other.frame.limitTarget other.column).edges → Bool) (hpl : pl = C.right)
      (hP : W3Nd3StarCensusProof.PlacementSpec other pl),
      Nonempty (ResolutionExpansionFree.TransportFree (isoOf w hy other ψ) (mergeVertex other)
        (mergeVertex w) pl (rightOf (largestTarget input profile)) (res other pl hP)
        (M11StarCensusProof.pasted (fineCandidate input profile hSame))) := by
    intro pl hpl hP
    subst hpl
    refine nonempty_transportFree_fine (isoOf w hy other ψ) (isoOf_wall w hy input other ψ)
      input.distinguishedBlock.1 _ _ _ (incident_nd3 input profile) _ _ _ ?_ hL hR hN
      (fine_left input profile hSame) (fine_right input profile hSame)
      (fine_newEdge input profile hSame) hCoh
    intro e
    rw [rightOf_pullback]
    change rightOf _ e = rightOf (largestTarget (input₁ w hy input other ψ)
      (profile₁ w hy input profile other ψ)) e
    rw [largest₁]
  obtain ⟨t⟩ := key _ hEq (hEq ▸ hP₁)
  exact ⟨⟨hEq ▸ hP₁, t⟩⟩

/-- **Coherence is exactly what position `1` asks for**: any receipt at the fine position
along `ψ` forces fine coherence along `ψ`. -/
theorem fineCoherent_of_positionTransport
    (t : W3Nd3StarCensusProof.PositionTransport w hy input profile hSame other ψ
      ⟨1, by decide⟩) :
    FineCoherent (isoOf w hy other ψ) input profile (mergeVertex other) :=
  coherent_of_transportFree (isoOf w hy other ψ) (isoOf_wall w hy input other ψ)
    input.distinguishedBlock.1 _ _ _ (incident_nd3 input profile)
    (thirdTarget_ne_largest input profile) profile.first_target_ne _ _ _
    (fine_right input profile hSame) t.2

end Receipts

/-! ## 5.  Exhaustion from fine coherence -/

section Exhaustion

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd3Profile w.limit input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)

/-- **Fine coherence at one nd3 wall**: every star member has a limit isomorphism along
which, if it is of largest type, the third direction's occurrence permutation agrees with
the doubled direction's modulo the doubled partition on the distinguished block.  Proved at
every wall (`fineCoherenceAt`, §7).  *Interface*: exactly the receipt route's condition at
largest-type members (`fineCoherent_of_positionTransport`); shared-type members need
nothing. -/
def FineCoherenceAt : Prop :=
  ∀ member : GeometricStar.StarMember hy w, ∃ ψ : GeometricStar.LimitIso hy member.member w,
    divalent₁ w hy input member.member ψ =
        (profile₁ w hy input profile member.member ψ).largest.1.1.1 →
      FineCoherent (isoOf w hy member.member ψ) input profile (mergeVertex member.member)

/-- **Stage 2 at one nd3 wall, modulo fine coherence.** -/
theorem exhausts_of_fineCoherence (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd3CommonBalance.candidates input profile hSame incoming).datum (Fin p))
    (hCoh : FineCoherenceAt w hy input profile) :
    W3Nd3StarCensusProof.Exhausts w hy input profile hSame incoming incomingFD := by
  refine W3Nd3StarCensusProof.exhausts_of_transports w hy input profile hSame incoming
    incomingFD ?_
  intro member
  obtain ⟨ψ, hψ⟩ := hCoh member
  rcases member_cases w hy input profile hSame member.member ψ with hShared | hLargest
  · exact ⟨ψ, ⟨0, by decide⟩, W3Nd3StarCensusProof.nonsingular input profile hSame incoming
      incomingFD _, transport_zero w hy input profile hSame member.member ψ hShared⟩
  · exact ⟨ψ, ⟨1, by decide⟩, W3Nd3StarCensusProof.nonsingular input profile hSame incoming
      incomingFD _, transport_one w hy input profile hSame member.member ψ hLargest (hψ hLargest)⟩

end Exhaustion

/-! ## 6.  The family clause from fine coherence -/

section Family

/-- **Nd3 fine coherence, family-wide** (proved: `w3Nd3FineCoherence`). -/
def W3Nd3FineCoherence (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w3Nd3CoarseFine →
    ∀ (star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : W3SourceInput w.limit star)
      (profile : Nd3Profile w.limit input.distinguishedBlock),
      profile.first.1.1.1 = profile.second.1.1.1 →
      FineCoherenceAt w hy input profile

variable {degree n p : ℕ}

/-- **The W3 nd3 star exhaustion, modulo fine coherence.** -/
theorem w3Nd3StarExhaustion_of_fineCoherence (h : W3Nd3FineCoherence degree n p) :
    W3Nd3StarCensusProof.W3Nd3StarExhaustion degree n p :=
  fun core y hy w cls htag star input profile hSame incoming incomingFD ↦
    exhausts_of_fineCoherence w hy input profile hSame incoming incomingFD
      (h core y hy w cls htag star input profile hSame)

/-- **The `w3Nd3CoarseFine` clause of `FamilyStarParity` at genus six and degree four,
modulo fine coherence alone.** -/
theorem familyStarParity_w3Nd3_of_fineCoherence
    (h : W3Nd3FineCoherence (2 + 2) (4 * 2 + 2) (6 * 2 + 3)) :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w3Nd3CoarseFine :=
  W3Nd3StarCensusProof.familyStarParity_w3Nd3_of_exhaustion
    (w3Nd3StarExhaustion_of_fineCoherence h)

end Family

/-! ## 7.  The W3 nd3 star exhaustion, with no hypothesis -/

section Unconditional

open W3Nd3SourceCandidates

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd3Profile w.limit input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)

include hSame in
/-- **Fine coherence holds at every nd3 wall.** -/
theorem fineCoherenceAt : FineCoherenceAt w hy input profile := by
  intro member
  obtain ⟨ψ₀⟩ := member.specializes
  have hPos : 0 < nonDanglingValency w.limit
      (w.limit.sourceEndpoint (mergeVertex w) input.distinguishedBlock.1) := by
    change 0 < nonDanglingValency w.limit
      (W4StableSource.WallBlock.sourceVertex w.limit (mergeVertex w) input.distinguishedBlock)
    rw [← card_survivors]
    exact Finset.card_pos.mpr ⟨profile.first, by rw [profile.surviving]; simp⟩
  obtain ⟨ψ, hψ⟩ := exists_coherent w hy input member.member ψ₀ input.distinguishedBlock.1
    profile.first.1.1.1 (thirdTarget input profile) (incident_target_mem input profile.first)
    (thirdTarget_mem input profile) (thirdTarget_ne_shared input profile).symm
    (fun s hs ↦ thirdSourceEdge_isDangling input profile hSame s hs) hPos
  exact ⟨ψ, fun _ ↦ hψ⟩

/-- **Stage 2 at one nd3 wall.** -/
theorem exhausts (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd3CommonBalance.candidates input profile hSame incoming).datum (Fin p)) :
    W3Nd3StarCensusProof.Exhausts w hy input profile hSame incoming incomingFD :=
  exhausts_of_fineCoherence w hy input profile hSame incoming incomingFD
    (fineCoherenceAt w hy input profile hSame)

end Unconditional

section UnconditionalFamily

variable (degree n p : ℕ)

/-- **The W3 nd3 fine-coherence residue holds.** -/
theorem w3Nd3FineCoherence : W3Nd3FineCoherence degree n p :=
  fun _ _ hy w _ _ _ input profile hSame ↦ fineCoherenceAt w hy input profile hSame

/-- **The W3 nd3 star exhaustion, at every core, degree and request.** -/
theorem w3Nd3StarExhaustion : W3Nd3StarCensusProof.W3Nd3StarExhaustion degree n p :=
  w3Nd3StarExhaustion_of_fineCoherence (w3Nd3FineCoherence degree n p)

/-- **The W3 nd3 star census**, unconditionally. -/
theorem w3Nd3StarCensus : W3Nd3StarCensusProof.W3Nd3StarCensus degree n p :=
  W3Nd3StarCensusProof.w3Nd3StarCensus_of_exhaustion (w3Nd3StarExhaustion degree n p)

/-- **Every `w3Nd3CoarseFine` star has exactly two classes.** -/
theorem w3Nd3StarCardTwo : W3Nd3StarCensusProof.W3Nd3StarCardTwo degree n p :=
  W3Nd3StarCensusProof.w3Nd3StarExhaustion_iff_cardTwo.mp (w3Nd3StarExhaustion degree n p)

/-- **The `w3Nd3CoarseFine` clause of `FamilyStarParity` at genus six and degree four,
with no hypothesis.** -/
theorem familyStarParity_w3Nd3 :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w3Nd3CoarseFine :=
  W3Nd3StarCensusProof.familyStarParity_w3Nd3_of_exhaustion (w3Nd3StarExhaustion _ _ _)

end UnconditionalFamily

end DraismaVargas.Count.W3Nd3StarExhaustionProof
