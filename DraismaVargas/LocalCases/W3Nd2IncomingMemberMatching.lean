module

public import DraismaVargas.LocalCases.W3Nd2IncomingNormalization
public import DraismaVargas.LocalCases.W3Nd2StableLift
public import DraismaVargas.LocalCases.M11IncomingOuterPartitions

@[expose] public section

/-!
# Identifying the incoming W3 nd2 datum with a named Figure 31 member

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{w3-r1-nd2}` and Figure 31.  That case refers to "case `{w3-nd3-t2}`" for an
analogous argument; this development reads the reference as Case
`{w3-r1-nd3-t2}`.

## Which member

`W3Nd2IncomingNormalization` proves the stored-representative normalization as
a *general* theorem, without instantiating it at `coarseCandidate` /
`fineCandidate`.  At first sight the coarse candidate's selected-block
resolution `thirdResolution` (left = right = newEdge = the whole merged wall
class) does not match the incoming selected-block picture, if `vertexPartition`
at the unramified endpoint is taken to be the strictly smaller class `A^{(q)}`.

**That is not the incoming picture.**
`W3R1SourceProfile.Nd2Profile` records two *different* indices:
`small_index : |e| + 1 = |A_0|` and `large_index : |e'| = |A_0|`.  That is the
source's own `|A_0| = |e'| = k+1` with `k = |e|` (Part I, Case `{w3-r1-nd2}`).
So the strictly
smaller class `A^{(q)}` is the **small** survivor's flag class, and the **large**
survivor's flag class fills its whole wall class -- `large_flag_block_eq_local`
proves exactly this, from the index equality plus refinement, as an equality of
`Finset`s.

Which survivor the unramified (trivalent) endpoint keeps is therefore what
decides the member, and that is precisely the orientation dichotomy
`W3Nd2IncomingDirection.divalentOccurrence_eq_small_or_large`:

* `divalentOccurrence = smallTarget` (the paper's `M^{(1)}`): the ramified
  divalent endpoint carries `A_0`, the unramified trivalent endpoint keeps the
  *large* flag, whose class is also `A_0`, and the forest identity then makes the
  contracted occurrence joined as well.  All three selected partitions are the
  whole wall class -- literally `thirdResolution`, i.e. the **coarse** member.
* `divalentOccurrence = largeTarget` (the paper's `M^{(2)}`): the unramified
  endpoint keeps the *small* flag `A^{(q)}`, and so does the contracted
  occurrence, while the ramified divalent endpoint still carries `A_0`.  That is
  `(fineResolution ...).reverse`, i.e. `W3Nd2FineCandidates.selectedResolution`
  -- the **fine** member.

So both members occur, one per orientation; what decides the member is only
the identification of which of `A^{(q)}`, `A_0` sits at the unramified
endpoint.

## What is proved here

* `large_flag_block_eq_local` -- the large flag class is the entire merged wall
  class; `fine_blockCard_succ_local` -- the small one misses exactly one sheet.
* `background_edge_block_eq_of_left_divalent` and its three companions -- the
  whole-block census of `W3Nd2IncomingNormalization` read as literal block
  equalities: on a background class every occurrence at the divalent endpoint
  has that endpoint's block, and the trivalent endpoint has the whole class.
* `coarse_selected_endpoints_joined`, `coarse_selected_contracted_joined` and
  `fine_selected_blocks` -- the selected block in each orientation.
* `transported_endpoints_of_left_divalent` and its mirror -- the candidate's
  `left` end is always the *divalent* original endpoint, whichever of `a`, `b`
  that is: the normalization swap is decided by the side census, not chosen.
* `sameBlocks_of_wall_blocks` -- the vertex/occurrence exhaustion, so each member
  only supplies three wall comparisons.
* `coarse_sameBlocks` / `fine_sameBlocks` and their split forms -- the pointwise
  `SameBlocks` families against the named member.
* `exists_member_normalization` -- the exit: the incoming datum is one of the two
  named Figure 31 members, with the literal Option column dictionary and the
  normalization receipt `NormalizedAgainst`, whose recorded clauses (original
  target-edge labelling, unchanged length matrix, occurrence-for-occurrence
  source map, preserved stable-row matrix entries) are what forbid a hidden
  incoming classification or count-based row bijection.

The hypothesis bundle is the one already shown jointly satisfiable by
`W3Nd2IncomingSelectedCensus.selected_fibre_census`: an actual full-dimensional
incoming presentation whose contraction of the single edge between `a` and `b`
is a forest with dangling compatibility, a genuine trivalent star at the
contracted wall, a W3 source input for it, and a Figure 31 nd2 profile of its
distinguished block.  Nothing forces the two surviving directions to coincide or
the selected fibre to be empty, and both branches of the conclusion genuinely
occur.

No FourStar theorem is applied to this ThreeStar case; the star-free copies
needed are the `_local` ones of `W3Nd2IncomingSheetClasses`, reused here.

The original-coordinate arbitrary-incoming exit -- combining this identification
with `W3Nd2PositiveExit.exists_positive_exit_with_pencil` -- is a separate step
and is **not** proved here.
-/

namespace DraismaVargas.LocalCases.W3Nd2IncomingMemberMatching

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties NonDanglingValency
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open TargetExpansion ResolutionM11 ResolutionM1k ResolutionCoarseFine
open M11IncomingPartitions M11IncomingTargetNormalization
open W3Nd2SourceCandidates W3Nd2FineRefinement W3Nd2FineCandidates
open W3Nd2IncomingTargetPlacement W3Nd2IncomingDirection
open W3Nd2IncomingSelectedCensus

/-! ## Generic sheet-partition lemmas -/

section Partitions

variable {d : ℕ}

/-- Pointwise equality of blocks is `SameBlocks`. -/
theorem sameBlocks_of_block_eq_local {first second : SheetPartition d}
    (hBlock : ∀ sheet, first.block sheet = second.block sheet) :
    first.SameBlocks second := by
  intro i j
  rw [← SheetPartition.mem_block_iff, ← SheetPartition.mem_block_iff, hBlock i]

/-- On a coarse block that a refinement joins, the fine block is the whole
coarse block. -/
theorem block_eq_of_joinedOnBlock_local (fine coarse : SheetPartition d) (root : Fin d)
    (hRefines : fine.Refines coarse) (hJoined : JoinedOnBlock fine coarse root)
    (sheet : Fin d) (hSheet : coarse.Rel root sheet) :
    fine.block sheet = coarse.block sheet := by
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact ⟨fun h ↦ hRefines.rel h, fun h ↦ hJoined sheet other hSheet (hSheet.trans h)⟩

/-- A refinement whose block at one sheet misses exactly one sheet of the
ambient coarse block is a singleton at that missing sheet. -/
theorem block_eq_singleton_of_notMem_local (coarse fine : SheetPartition d)
    (root sheet other : Fin d) (hRefines : fine.Refines coarse)
    (hRoot : coarse.Rel root sheet)
    (hCard : fine.blockCard sheet + 1 = coarse.blockCard root)
    (hOther : coarse.Rel root other) (hNot : other ∉ fine.block sheet) :
    fine.block other = {other} := by
  classical
  have hSub : fine.block sheet ⊆ coarse.block root := by
    intro j hj
    exact (coarse.mem_block_iff root j).mpr
      (hRoot.trans (hRefines.rel ((fine.mem_block_iff sheet j).mp hj)))
  have hOtherSub : fine.block other ⊆ coarse.block root \ fine.block sheet := by
    intro j hj
    have hRel : fine.Rel other j := (fine.mem_block_iff other j).mp hj
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact (coarse.mem_block_iff root j).mpr (hOther.trans (hRefines.rel hRel))
    · intro hMem
      exact hNot ((fine.mem_block_iff sheet other).mpr
        (((fine.mem_block_iff sheet j).mp hMem).trans hRel.symm))
  have hCardDiff : (coarse.block root \ fine.block sheet).card = 1 := by
    rw [Finset.card_sdiff_of_subset hSub]
    unfold SheetPartition.blockCard at hCard
    omega
  obtain ⟨point, hPoint⟩ := Finset.card_eq_one.mp hCardDiff
  have hOtherMem : other ∈ coarse.block root \ fine.block sheet :=
    hOtherSub (fine.self_mem_block other)
  have hSingle : coarse.block root \ fine.block sheet = {other} := by
    rw [hPoint] at hOtherMem ⊢
    rw [Finset.mem_singleton.mp hOtherMem]
  apply Finset.Subset.antisymm
  · rw [← hSingle]
    exact hOtherSub
  · exact Finset.singleton_subset_iff.mpr (fine.self_mem_block other)

/-- Two refinements of one coarse partition that agree at a sheet whose block
misses exactly one sheet of its coarse block agree on that whole coarse
block. -/
theorem block_eq_of_block_eq_of_card_succ_local (coarse first second : SheetPartition d)
    (root sheet : Fin d)
    (hFirst : first.Refines coarse) (hSecond : second.Refines coarse)
    (hRoot : coarse.Rel root sheet)
    (hBlock : first.block sheet = second.block sheet)
    (hCard : first.blockCard sheet + 1 = coarse.blockCard root)
    (other : Fin d) (hOther : coarse.Rel root other) :
    first.block other = second.block other := by
  classical
  have hCardSecond : second.blockCard sheet + 1 = coarse.blockCard root := by
    unfold SheetPartition.blockCard at hCard ⊢
    rw [← hBlock]
    exact hCard
  by_cases hMem : other ∈ first.block sheet
  · have hFirstRel : first.Rel sheet other := (first.mem_block_iff sheet other).mp hMem
    have hSecondRel : second.Rel sheet other :=
      (second.mem_block_iff sheet other).mp (hBlock ▸ hMem)
    rw [← first.block_eq_of_rel hFirstRel, ← second.block_eq_of_rel hSecondRel]
    exact hBlock
  · have hMemSecond : other ∉ second.block sheet := by
      rw [← hBlock]
      exact hMem
    rw [block_eq_singleton_of_notMem_local coarse first root sheet other hFirst hRoot
        hCard hOther hMem,
      block_eq_singleton_of_notMem_local coarse second root sheet other hSecond hRoot
        hCardSecond hOther hMemSecond]

end Partitions


/-! ## The candidate's datum, read off its pasted local resolution -/

section CandidateDatum

variable {wallTarget : CFGraph} {wallDegree : ℕ} {wall : wallTarget.V}
  {wallData : GluingDatum wallTarget wallDegree}

/-- The globally pasted local resolution carried by one assembled candidate. -/
noncomputable abbrev pasted
    (C : BalancedGlobal.Candidate wallTarget wallDegree wallData wall) :
    LocalResolution wallDegree :=
  LocalResolution.paste (wallData.vertexPartition wall) C.resolution C.contracts

/-- The retained wall end of an assembled candidate carries its pasted left
endpoint partition. -/
theorem candidate_vertexPartition_old_wall
    (C : BalancedGlobal.Candidate wallTarget wallDegree wallData wall) :
    C.datum.vertexPartition (oldVertex wallTarget wall) = (pasted C).left := by
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_vertexPartition_old_wall]

/-- Away from the wall the candidate keeps the original vertex partition. -/
theorem candidate_vertexPartition_old_of_ne
    (C : BalancedGlobal.Candidate wallTarget wallDegree wallData wall)
    (vertex : wallTarget.V) (hNe : vertex ≠ wall) :
    C.datum.vertexPartition (oldVertex wallTarget vertex) = wallData.vertexPartition vertex := by
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_vertexPartition_old_of_ne _ _ _ _ _ _ hNe]

/-- The fresh end carries the pasted right endpoint partition. -/
theorem candidate_vertexPartition_fresh
    (C : BalancedGlobal.Candidate wallTarget wallDegree wallData wall) :
    C.datum.vertexPartition (freshVertex wallTarget) = (pasted C).right := by
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_vertexPartition_fresh]

/-- The new occurrence carries the pasted new-edge partition. -/
theorem candidate_edgePartition_new
    (C : BalancedGlobal.Candidate wallTarget wallDegree wallData wall) :
    C.datum.edgePartition (occurrenceEquiv wallTarget wall C.right none) =
      (pasted C).newEdge := by
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_edgePartition_new]

/-- Every retained occurrence keeps the original edge partition. -/
theorem candidate_edgePartition_old
    (C : BalancedGlobal.Candidate wallTarget wallDegree wallData wall)
    (edge : wallTarget.edges) :
    C.datum.edgePartition (occurrenceEquiv wallTarget wall C.right (some edge)) =
      wallData.edgePartition edge := by
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_edgePartition_old]

end CandidateDatum


/-! ## Assembling pointwise matching from the three wall partitions -/

section Assembly

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-- **The whole-cover assembly step.**  Away from the contracted wall every
transported partition is literally the contracted datum's own partition, and so
is the candidate's; at the wall there are exactly three partitions to compare.
This lemma performs the vertex/occurrence exhaustion once, so that each member
only has to supply the three wall comparisons. -/
theorem sameBlocks_of_wall_blocks
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (C : BalancedGlobal.Candidate (contract target hab hOne) degree
      (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hPlacement : Placement hc hab hOne C.right)
    (hLeft : ∀ sheet,
      ((GluingTransport.transport (incomingIso hc hab hOne C.right hPlacement)
          data).vertexPartition
        (oldVertex (contract target hab hOne) ⟨a, hab⟩)).block sheet =
          (pasted C).left.block sheet)
    (hRight : ∀ sheet,
      ((GluingTransport.transport (incomingIso hc hab hOne C.right hPlacement)
          data).vertexPartition
        (freshVertex (contract target hab hOne))).block sheet =
          (pasted C).right.block sheet)
    (hNew : ∀ sheet,
      (data.edgePartition contracted).block sheet = (pasted C).newEdge.block sheet) :
    (∀ vertex, ((GluingTransport.transport (incomingIso hc hab hOne C.right hPlacement)
          data).vertexPartition vertex).SameBlocks (C.datum.vertexPartition vertex)) ∧
      (∀ edge, ((GluingTransport.transport (incomingIso hc hab hOne C.right hPlacement)
          data).edgePartition edge).SameBlocks (C.datum.edgePartition edge)) := by
  classical
  constructor
  · intro vertex
    rcases vertex with vertex | _
    · by_cases hWall : vertex = (⟨a, hab⟩ : (contract target hab hOne).V)
      · subst hWall
        change ((GluingTransport.transport (incomingIso hc hab hOne C.right hPlacement)
            data).vertexPartition
            (oldVertex (contract target hab hOne) ⟨a, hab⟩)).SameBlocks
          (C.datum.vertexPartition (oldVertex (contract target hab hOne) ⟨a, hab⟩))
        rw [candidate_vertexPartition_old_wall C]
        exact sameBlocks_of_block_eq_local hLeft
      · change ((GluingTransport.transport (incomingIso hc hab hOne C.right hPlacement)
            data).vertexPartition
            (oldVertex (contract target hab hOne) vertex)).SameBlocks
          (C.datum.vertexPartition (oldVertex (contract target hab hOne) vertex))
        rw [M11IncomingOuterPartitions.transported_vertexPartition_of_ne data hc hab hOne
            C.right hPlacement vertex hWall,
          candidate_vertexPartition_old_of_ne C vertex hWall]
        exact SheetPartition.SameBlocks.refl _
    · cases ‹Unit›
      change ((GluingTransport.transport (incomingIso hc hab hOne C.right hPlacement)
          data).vertexPartition (freshVertex (contract target hab hOne))).SameBlocks
        (C.datum.vertexPartition (freshVertex (contract target hab hOne)))
      rw [candidate_vertexPartition_fresh C]
      exact sameBlocks_of_block_eq_local hRight
  · intro edge
    obtain ⟨column, rfl⟩ :=
      (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ C.right).surjective edge
    cases column with
    | none =>
      rw [M11IncomingOuterPartitions.transported_edgePartition_new data hc hab hOne
          C.right hPlacement hConnected hGenus,
        candidate_edgePartition_new C]
      exact sameBlocks_of_block_eq_local hNew
    | some place =>
      rw [M11IncomingOuterPartitions.transported_edgePartition_retained data hc hab hOne
          C.right hPlacement hConnected hGenus place,
        candidate_edgePartition_old C place]
      exact SheetPartition.SameBlocks.refl _

end Assembly


/-! ## Which original endpoint the candidate's two ends restore -/

section Endpoints

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- At a `(2,3)` wall with `a` divalent, the isolated retained direction is
restored to `a`. -/
theorem divalentOccurrence_right_eq_false
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2) :
    IncomingTargetExpansion.right hc hab hOne
      (divalentOccurrence data hc hab hOne fullDim star) = false := by
  rcases (divalentOccurrence_spec data hc hab hOne fullDim star).2 with hLeft | hRight
  · exact hLeft.2
  · exfalso
    rcases endpoint_valencies data hc hab hOne fullDim star with
      ⟨_, hThree, _, _⟩ | ⟨hThree, _, _, _⟩
    · have := hRight.1
      omega
    · omega

/-- The mirror: with `b` divalent the isolated direction is restored to `b`. -/
theorem divalentOccurrence_right_eq_true
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2) :
    IncomingTargetExpansion.right hc hab hOne
      (divalentOccurrence data hc hab hOne fullDim star) = true := by
  rcases (divalentOccurrence_spec data hc hab hOne fullDim star).2 with hLeft | hRight
  · exfalso
    rcases endpoint_valencies data hc hab hOne fullDim star with
      ⟨_, hThree, _, _⟩ | ⟨hThree, _, _, _⟩
    · omega
    · have := hLeft.1
      omega
  · exact hRight.2

/-- **The candidate's `left` end is the divalent original endpoint.**  When `a`
is the divalent endpoint, the isolated direction is restored to `a`, so the
incoming side predicate literally agrees with the candidate's and normalization
does not exchange the two ends. -/
theorem transported_endpoints_of_left_divalent
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (side : (contract target hab hOne).edges → Bool)
    (hPlacement : Placement hc hab hOne side)
    (hSide : ∀ edge, side edge =
      rightOf (divalentOccurrence data hc hab hOne fullDim star) edge)
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2) :
    (GluingTransport.transport (incomingIso hc hab hOne side hPlacement) data).vertexPartition
        (oldVertex (contract target hab hOne) ⟨a, hab⟩) = data.vertexPartition a ∧
      (GluingTransport.transport (incomingIso hc hab hOne side hPlacement) data).vertexPartition
        (freshVertex (contract target hab hOne)) = data.vertexPartition b := by
  classical
  have hSpec := divalentOccurrence_spec data hc hab hOne fullDim star
  have hFalse := divalentOccurrence_right_eq_false data hc hab hOne fullDim star hLeftDivalent
  have hSupport : ∀ edge ∈ GluingDatum.incidentEdges
      (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = side edge := by
    rcases hPlacement with hSame | hSwap
    · exact hSame
    · exfalso
      have hValue := hSwap (divalentOccurrence data hc hab hOne fullDim star) hSpec.1
      rw [hFalse, hSide] at hValue
      simp [rightOf] at hValue
  have hPair := M11IncomingOuterPartitions.transported_endpointPartitions data hc hab hOne
    side hPlacement
  rw [ite_eq_left hSupport] at hPair
  exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩

/-- The mirror: when `b` is the divalent endpoint the normalization exchanges
the two expanded ends, so the candidate's `left` end is again divalent. -/
theorem transported_endpoints_of_right_divalent
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (side : (contract target hab hOne).edges → Bool)
    (hPlacement : Placement hc hab hOne side)
    (hSide : ∀ edge, side edge =
      rightOf (divalentOccurrence data hc hab hOne fullDim star) edge)
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2) :
    (GluingTransport.transport (incomingIso hc hab hOne side hPlacement) data).vertexPartition
        (oldVertex (contract target hab hOne) ⟨a, hab⟩) = data.vertexPartition b ∧
      (GluingTransport.transport (incomingIso hc hab hOne side hPlacement) data).vertexPartition
        (freshVertex (contract target hab hOne)) = data.vertexPartition a := by
  classical
  have hSpec := divalentOccurrence_spec data hc hab hOne fullDim star
  have hTrue := divalentOccurrence_right_eq_true data hc hab hOne fullDim star hRightDivalent
  have hNotSupport : ¬ ∀ edge ∈ GluingDatum.incidentEdges
      (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = side edge := by
    intro hSupport
    have hValue := hSupport (divalentOccurrence data hc hab hOne fullDim star) hSpec.1
    rw [hTrue, hSide] at hValue
    simp [rightOf] at hValue
  have hPair := M11IncomingOuterPartitions.transported_endpointPartitions data hc hab hOne
    side hPlacement
  rw [ite_eq_right hNotSupport] at hPair
  exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩

end Endpoints


/-! ## The r0 background blocks, read as literal block equalities -/

section Background

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  {star : ThreeStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W3SourceInput (contractDatum data hc hab hOne) star)

include fullDim hForest input

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
/-- A sheet off the distinguished class lies in a background wall block. -/
private theorem background_wallBlock_ne
    (sheet : Fin degree)
    (hOff : ¬ (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet) :
    WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ sheet ≠
      input.distinguishedBlock := by
  intro hEq
  apply hOff
  rw [← contractDatum_vertexPartition_merge data hc hab hOne]
  exact (WallBlock.ofSheet_eq_iff_rel (contractDatum data hc hab hOne) ⟨a, hab⟩ _ sheet).mp hEq

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest input in
/-- Every sheet is merged-related to the root of its own wall block. -/
private theorem background_wallBlock_rel (sheet : Fin degree) :
    (mergedPartition data a b).Rel
      (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ sheet).1 sheet := by
  rw [← contractDatum_vertexPartition_merge data hc hab hOne]
  exact ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).rel_repr_left sheet

/-- **Background, left-divalent orientation.**  Every occurrence at the divalent
original endpoint has that endpoint's own literal block on a background
class. -/
theorem background_edge_block_eq_of_left_divalent
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges a)
    (sheet : Fin degree)
    (hOff : ¬ (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition edge).block sheet = (data.vertexPartition a).block sheet := by
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact W3Nd2IncomingNormalization.background_edge_rel_iff_of_left_divalent data hc hab hOne
    fullDim hForest input hLeftDivalent
    (background_wallBlock_ne data hc hab hOne input sheet hOff)
    edge hEdge sheet other
    (background_wallBlock_rel data hc hab hOne sheet)

/-- **Background, left-divalent orientation.**  The trivalent original endpoint
carries the whole background class. -/
theorem background_trivalent_block_eq_of_left_divalent
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    (sheet : Fin degree)
    (hOff : ¬ (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet) :
    (data.vertexPartition b).block sheet = (mergedPartition data a b).block sheet :=
  block_eq_of_joinedOnBlock_local (data.vertexPartition b) (mergedPartition data a b)
    (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ sheet).1
    (vertexPartition_refines_mergedPartition_right data a b)
    (W3Nd2IncomingNormalization.background_trivalent_joined_of_left_divalent data hc hab hOne
      fullDim hForest input hLeftDivalent
      (background_wallBlock_ne data hc hab hOne input sheet hOff)).2
    sheet (background_wallBlock_rel data hc hab hOne sheet)

/-- The mirror of `background_edge_block_eq_of_left_divalent`. -/
theorem background_edge_block_eq_of_right_divalent
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges b)
    (sheet : Fin degree)
    (hOff : ¬ (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition edge).block sheet = (data.vertexPartition b).block sheet := by
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact W3Nd2IncomingNormalization.background_edge_rel_iff_of_right_divalent data hc hab hOne
    fullDim hForest input hRightDivalent
    (background_wallBlock_ne data hc hab hOne input sheet hOff)
    edge hEdge sheet other
    (background_wallBlock_rel data hc hab hOne sheet)

/-- The mirror of `background_trivalent_block_eq_of_left_divalent`. -/
theorem background_trivalent_block_eq_of_right_divalent
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2)
    (sheet : Fin degree)
    (hOff : ¬ (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet) :
    (data.vertexPartition a).block sheet = (mergedPartition data a b).block sheet :=
  block_eq_of_joinedOnBlock_local (data.vertexPartition a) (mergedPartition data a b)
    (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ sheet).1
    (vertexPartition_refines_mergedPartition data a b)
    (W3Nd2IncomingNormalization.background_trivalent_joined_of_right_divalent data hc hab hOne
      fullDim hForest input hRightDivalent
      (background_wallBlock_ne data hc hab hOne input sheet hOff)).2
    sheet (background_wallBlock_rel data hc hab hOne sheet)

end Background


/-! ## The larger survivor's flag class is the whole wall class

This is the point the identification turns on.  `Nd2Profile`
records `small_index + 1 = |A_0|` but `large_index = |A_0|`: the *strictly
smaller* class `A^{(q)}` belongs to the **small** survivor, and the large
survivor's retained flag fills its whole wall class. -/

section FlagClass

variable {wallTarget : CFGraph} {wallDegree : ℕ} {wall : wallTarget.V}
  {wallData : GluingDatum wallTarget wallDegree} {star : ThreeStar wallTarget wall}

/-- The large survivor's canonical sheet lies in the distinguished wall class. -/
theorem large_wall_rel_local (input : W3SourceInput wallData star)
    (profile : Nd2Profile wallData input.distinguishedBlock) :
    (wallData.vertexPartition wall).Rel input.distinguishedBlock.1
      profile.large.1.1.2 := by
  have hBlock := (incident_wallBlock_sourceVertex_iff wallData input.distinguishedBlock
    profile.large.1).mp profile.large.2 |>.2
  have hValue := congrArg Subtype.val hBlock
  change (wallData.vertexPartition wall).repr profile.large.1.1.2 =
    input.distinguishedBlock.1 at hValue
  change (wallData.vertexPartition wall).repr input.distinguishedBlock.1 =
    (wallData.vertexPartition wall).repr profile.large.1.1.2
  rw [input.distinguishedBlock.2, hValue]

/-- **The large flag class is the entire distinguished wall class.**  Its index
is `large_index = |A_0|`, and it is contained in `A_0` by refinement, so the two
finite sets coincide. -/
theorem large_flag_block_eq_local (input : W3SourceInput wallData star)
    (profile : Nd2Profile wallData input.distinguishedBlock) :
    (wallData.edgePartition (largeTarget input profile)).block profile.large.1.1.2 =
      (wallData.vertexPartition wall).block input.distinguishedBlock.1 := by
  classical
  have hRel := large_wall_rel_local input profile
  have hRefines : (wallData.edgePartition (largeTarget input profile)).Refines
      (wallData.vertexPartition wall) :=
    refines_of_mem_incidentEdges wallData (largeTarget_mem input profile)
  have hSub : (wallData.edgePartition (largeTarget input profile)).block
      profile.large.1.1.2 ⊆ (wallData.vertexPartition wall).block
        input.distinguishedBlock.1 := by
    intro sheet hSheet
    exact ((wallData.vertexPartition wall).mem_block_iff _ sheet).mpr
      (hRel.trans (hRefines.rel
        (((wallData.edgePartition (largeTarget input profile)).mem_block_iff _ sheet).mp hSheet)))
  have hCard : ((wallData.vertexPartition wall).block input.distinguishedBlock.1).card ≤
      ((wallData.edgePartition (largeTarget input profile)).block
        profile.large.1.1.2).card := by
    have hIndex : (wallData.edgePartition (largeTarget input profile)).blockCard
        profile.large.1.1.2 =
          (wallData.vertexPartition wall).blockCard input.distinguishedBlock.1 :=
      profile.large_index
    unfold SheetPartition.blockCard at hIndex
    omega
  exact Finset.eq_of_subset_of_card_le hSub hCard

/-- The small survivor's flag class misses exactly one sheet of the
distinguished wall class. -/
theorem fine_blockCard_succ_local (input : W3SourceInput wallData star)
    (profile : Nd2Profile wallData input.distinguishedBlock) :
    (finePartition input profile).blockCard (anchor input profile) + 1 =
      (wallData.vertexPartition wall).blockCard input.distinguishedBlock.1 :=
  profile.small_index

end FlagClass


/-! ## The selected block in the `M^{(1)}` orientation (the coarse member) -/

section SelectedCoarse

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd2Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

include hForest hCompat

/-- **Both endpoint partitions are joined on the selected block, in the
`M^{(1)}` orientation.**  The ramified endpoint carries `A_0` by
`selected_sheet_classes_of_small`; the unramified one carries the *large*
survivor's retained flag, whose class is all of `A_0` by
`large_flag_block_eq_local`.  This is exactly `thirdResolution`'s selected
picture, and it is why the coarse candidate is the right member here. -/
theorem coarse_selected_endpoints_joined
    (hSmall : divalentOccurrence data hc hab hOne fullDim star = smallTarget input profile) :
    JoinedOnBlock (data.vertexPartition a) (mergedPartition data a b)
        input.distinguishedBlock.1 ∧
      JoinedOnBlock (data.vertexPartition b) (mergedPartition data a b)
        input.distinguishedBlock.1 := by
  classical
  obtain ⟨_, _, _, _, _, _, hFlag, hRamClass⟩ :=
    W3Nd2IncomingSheetClasses.selected_sheet_classes_of_small data hc hab hOne fullDim hForest
      hCompat star input profile hSmall
  have hSmallJoined : JoinedOnBlock
      (data.vertexPartition (smallEndpoint data hc hab hOne star input profile).1.1)
      (mergedPartition data a b) input.distinguishedBlock.1 :=
    W3Nd2IncomingNormalization.joinedOnBlock_of_block_eq_local _ _ _ _ hRamClass
  have hLargeFlag : (data.vertexPartition
        (largeEndpoint data hc hab hOne star input profile).1.1).block
        (largeEndpoint data hc hab hOne star input profile).1.2 =
      (mergedPartition data a b).block input.distinguishedBlock.1 := by
    have hMerge : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block
        (input.distinguishedBlock.1 : Fin degree) =
        (mergedPartition data a b).block (input.distinguishedBlock.1 : Fin degree) :=
      congrArg (fun partition : SheetPartition degree ↦
          partition.block (input.distinguishedBlock.1 : Fin degree))
        (contractDatum_vertexPartition_merge data hc hab hOne)
    exact hFlag.trans ((large_flag_block_eq_local input profile).trans hMerge)
  have hLargeJoined : JoinedOnBlock
      (data.vertexPartition (largeEndpoint data hc hab hOne star input profile).1.1)
      (mergedPartition data a b) input.distinguishedBlock.1 :=
    W3Nd2IncomingNormalization.joinedOnBlock_of_block_eq_local _ _ _ _ hLargeFlag
  have hSideNe := small_large_side_ne data hc hab hOne fullDim star input profile (Or.inl hSmall)
  cases hSide : IncomingTargetExpansion.right hc hab hOne (smallTarget input profile) with
  | false =>
    have hLargeSide : IncomingTargetExpansion.right hc hab hOne
        (largeTarget input profile) = true := by
      cases hValue : IncomingTargetExpansion.right hc hab hOne (largeTarget input profile)
      · exact absurd (hSide.trans hValue.symm) hSideNe
      · rfl
    have hSmallAt := W3Nd2IncomingSheetClasses.endpoint_target_of_false data hc hab hOne
      profile.small.1 hSide
    have hLargeAt := W3Nd2IncomingSheetClasses.endpoint_target_of_true data hc hab hOne
      profile.large.1 hLargeSide
    rw [congrArg data.vertexPartition hSmallAt] at hSmallJoined
    rw [congrArg data.vertexPartition hLargeAt] at hLargeJoined
    exact ⟨hSmallJoined, hLargeJoined⟩
  | true =>
    have hLargeSide : IncomingTargetExpansion.right hc hab hOne
        (largeTarget input profile) = false := by
      cases hValue : IncomingTargetExpansion.right hc hab hOne (largeTarget input profile)
      · rfl
      · exact absurd (hSide.trans hValue.symm) hSideNe
    have hSmallAt := W3Nd2IncomingSheetClasses.endpoint_target_of_true data hc hab hOne
      profile.small.1 hSide
    have hLargeAt := W3Nd2IncomingSheetClasses.endpoint_target_of_false data hc hab hOne
      profile.large.1 hLargeSide
    rw [congrArg data.vertexPartition hSmallAt] at hSmallJoined
    rw [congrArg data.vertexPartition hLargeAt] at hLargeJoined
    exact ⟨hLargeJoined, hSmallJoined⟩

/-- Hence the contracted occurrence is joined there too: the forest identity
turns two unit endpoint counts into a unit occurrence count. -/
theorem coarse_selected_contracted_joined
    (hSmall : divalentOccurrence data hc hab hOne fullDim star = smallTarget input profile) :
    JoinedOnBlock (data.edgePartition contracted) (mergedPartition data a b)
      input.distinguishedBlock.1 := by
  obtain ⟨hLeft, hRight⟩ := coarse_selected_endpoints_joined data hc hab hOne fullDim hForest
    hCompat star input profile hSmall
  have hTree := contractionForest_count data hc hForest
    (selectedMergedBlock data hc hab hOne input.distinguishedBlock)
  have hCountLeft := blockCountWithin_eq_one_of_joinedOnBlock _ _ _ hLeft
  have hCountRight := blockCountWithin_eq_one_of_joinedOnBlock _ _ _ hRight
  have hTree' : ((data.edgePartition contracted).blockCountWithin
        (mergedPartition data a b) input.distinguishedBlock.1 : ℤ) + 1 =
      ((data.vertexPartition a).blockCountWithin
          (mergedPartition data a b) input.distinguishedBlock.1 : ℤ) +
        ((data.vertexPartition b).blockCountWithin
          (mergedPartition data a b) input.distinguishedBlock.1 : ℤ) := hTree
  rw [hCountLeft, hCountRight] at hTree'
  have hCount : (data.edgePartition contracted).blockCountWithin
      (mergedPartition data a b) input.distinguishedBlock.1 = 1 := by
    have : ((data.edgePartition contracted).blockCountWithin
        (mergedPartition data a b) input.distinguishedBlock.1 : ℤ) = 1 := by omega
    exact_mod_cast this
  exact joinedOnBlock_of_blockCountWithin_eq_one _ _ _
    (edgePartition_refines_mergedPartition data hc) hCount

end SelectedCoarse


/-! ## The selected block in the `M^{(2)}` orientation (the fine member) -/

section SelectedFine

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd2Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest hCompat star input profile in
private theorem merged_eq_wall :
    mergedPartition data a b =
      (contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩ :=
  (contractDatum_vertexPartition_merge data hc hab hOne).symm

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest hCompat star input profile in
private theorem merged_block_eq_wall_block (sheet : Fin degree) :
    (mergedPartition data a b).block sheet =
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block sheet :=
  congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
    (merged_eq_wall data hc hab hOne)

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest hCompat profile in
private theorem merged_rel_eq_wall_rel (sheet : Fin degree) :
    ((mergedPartition data a b).Rel (input.distinguishedBlock.1 : Fin degree) sheet) =
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet) :=
  congrArg (fun partition : SheetPartition degree ↦
      partition.Rel (input.distinguishedBlock.1 : Fin degree) sheet)
    (merged_eq_wall data hc hab hOne)

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest hCompat in
private theorem fine_refines_merged :
    (finePartition input profile).Refines (mergedPartition data a b) := by
  rw [merged_eq_wall data hc hab hOne]
  exact fine_refines_wall input profile

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest hCompat in
private theorem anchor_merged_rel :
    (mergedPartition data a b).Rel (input.distinguishedBlock.1 : Fin degree)
      (anchor input profile) := by
  rw [merged_eq_wall data hc hab hOne]
  exact anchor_wall_rel input profile

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest hCompat in
private theorem fine_blockCard_succ_merged :
    (finePartition input profile).blockCard (anchor input profile) + 1 =
      (mergedPartition data a b).blockCard (input.distinguishedBlock.1 : Fin degree) := by
  rw [merged_eq_wall data hc hab hOne]
  exact fine_blockCard_succ_local input profile

include hForest hCompat

/-- **The selected block in the `M^{(2)}` orientation.**  The ramified endpoint
`u` carries the whole merged class `A_0`; the unramified endpoint `v` and the
contracted occurrence both carry the *small* survivor's class `A^{(q)}`, which
misses exactly one sheet of `A_0`.  That is literally the reversed
`fineResolution` of `W3Nd2FineCandidates.selectedResolution`. -/
theorem fine_selected_blocks
    (hLarge : divalentOccurrence data hc hab hOne fullDim star = largeTarget input profile)
    (u v : target.V)
    (hU : (largeEndpoint data hc hab hOne star input profile).1.1 = u)
    (hV : (smallEndpoint data hc hab hOne star input profile).1.1 = v)
    (hVRefines : (data.vertexPartition v).Refines (mergedPartition data a b)) :
    JoinedOnBlock (data.vertexPartition u) (mergedPartition data a b)
        (input.distinguishedBlock.1 : Fin degree) ∧
      (∀ sheet, (mergedPartition data a b).Rel
          (input.distinguishedBlock.1 : Fin degree) sheet →
        (data.vertexPartition v).block sheet = (finePartition input profile).block sheet) ∧
      (∀ sheet, (mergedPartition data a b).Rel
          (input.distinguishedBlock.1 : Fin degree) sheet →
        (data.edgePartition contracted).block sheet =
          (finePartition input profile).block sheet) := by
  classical
  obtain ⟨internal, hInternal, _, _, _, hInternalClass, hFlag, hRamClass⟩ :=
    W3Nd2IncomingSheetClasses.selected_sheet_classes_of_large data hc hab hOne fullDim hForest
      hCompat star input profile hLarge
  have hFineRefines := fine_refines_merged data hc hab hOne star input profile
  have hAnchorRel := anchor_merged_rel data hc hab hOne star input profile
  have hCardSucc := fine_blockCard_succ_merged data hc hab hOne star input profile
  -- the ramified endpoint
  have hJoined : JoinedOnBlock (data.vertexPartition u) (mergedPartition data a b)
      (input.distinguishedBlock.1 : Fin degree) := by
    rw [← hU]
    exact W3Nd2IncomingNormalization.joinedOnBlock_of_block_eq_local _ _ _ _ hRamClass
  -- the unramified endpoint carries the small survivor's class
  have hFlagV : (data.vertexPartition v).block
      (smallEndpoint data hc hab hOne star input profile).1.2 =
      (finePartition input profile).block (anchor input profile) := by
    rw [← hV]
    exact hFlag
  have hMem : (smallEndpoint data hc hab hOne star input profile).1.2 ∈
      (finePartition input profile).block (anchor input profile) := by
    rw [← hFlagV]
    exact (data.vertexPartition v).self_mem_block _
  have hRelFine : (finePartition input profile).Rel (anchor input profile)
      (smallEndpoint data hc hab hOne star input profile).1.2 :=
    ((finePartition input profile).mem_block_iff _ _).mp hMem
  have hSheetRel : (mergedPartition data a b).Rel (input.distinguishedBlock.1 : Fin degree)
      (smallEndpoint data hc hab hOne star input profile).1.2 :=
    hAnchorRel.trans (hFineRefines.rel hRelFine)
  have hBlockV : (data.vertexPartition v).block
      (smallEndpoint data hc hab hOne star input profile).1.2 =
      (finePartition input profile).block
        (smallEndpoint data hc hab hOne star input profile).1.2 := by
    rw [hFlagV, (finePartition input profile).block_eq_of_rel hRelFine]
  have hCardV : (data.vertexPartition v).blockCard
      (smallEndpoint data hc hab hOne star input profile).1.2 + 1 =
      (mergedPartition data a b).blockCard (input.distinguishedBlock.1 : Fin degree) := by
    have hStep : (data.vertexPartition v).blockCard
        (smallEndpoint data hc hab hOne star input profile).1.2 =
        (finePartition input profile).blockCard (anchor input profile) := by
      unfold SheetPartition.blockCard
      rw [hFlagV]
    rw [hStep]
    exact hCardSucc
  -- the contracted occurrence carries the same class
  have hInternalMem : internal ∈ PrunedFibreValency.internalEdges data hc hab hOne
      (selectedVertex data hc hab hOne star input) := by
    rw [hInternal]
    exact Finset.mem_singleton_self internal
  have hInternalTarget : internal.1.1 = contracted :=
    ((PrunedFibreTree.mem_internalEdges data hc hab hOne _ internal).mp hInternalMem).2.1
  have hFlagInternal : (data.edgePartition contracted).block internal.1.2 =
      (finePartition input profile).block (anchor input profile) := by
    have hStep : (data.edgePartition contracted).block internal.1.2 =
        (data.edgePartition internal.1.1).block internal.1.2 :=
      congrArg (fun partition : SheetPartition degree ↦ partition.block internal.1.2)
        (congrArg data.edgePartition hInternalTarget).symm
    exact hStep.trans (hInternalClass.trans hFlag)
  have hMemInternal : internal.1.2 ∈
      (finePartition input profile).block (anchor input profile) := by
    rw [← hFlagInternal]
    exact (data.edgePartition contracted).self_mem_block _
  have hRelInternal : (finePartition input profile).Rel (anchor input profile) internal.1.2 :=
    ((finePartition input profile).mem_block_iff _ _).mp hMemInternal
  have hSheetInternal : (mergedPartition data a b).Rel
      (input.distinguishedBlock.1 : Fin degree) internal.1.2 :=
    hAnchorRel.trans (hFineRefines.rel hRelInternal)
  have hBlockInternal : (data.edgePartition contracted).block internal.1.2 =
      (finePartition input profile).block internal.1.2 := by
    rw [hFlagInternal, (finePartition input profile).block_eq_of_rel hRelInternal]
  have hCardInternal : (data.edgePartition contracted).blockCard internal.1.2 + 1 =
      (mergedPartition data a b).blockCard (input.distinguishedBlock.1 : Fin degree) := by
    have hStep : (data.edgePartition contracted).blockCard internal.1.2 =
        (finePartition input profile).blockCard (anchor input profile) := by
      unfold SheetPartition.blockCard
      rw [hFlagInternal]
    rw [hStep]
    exact hCardSucc
  refine ⟨hJoined, ?_, ?_⟩
  · intro sheet hSheet
    exact block_eq_of_block_eq_of_card_succ_local (mergedPartition data a b)
      (data.vertexPartition v) (finePartition input profile)
      (input.distinguishedBlock.1 : Fin degree)
      (smallEndpoint data hc hab hOne star input profile).1.2
      hVRefines hFineRefines hSheetRel hBlockV hCardV sheet hSheet
  · intro sheet hSheet
    exact block_eq_of_block_eq_of_card_succ_local (mergedPartition data a b)
      (data.edgePartition contracted) (finePartition input profile)
      (input.distinguishedBlock.1 : Fin degree) internal.1.2
      (edgePartition_refines_mergedPartition data hc) hFineRefines hSheetInternal
      hBlockInternal hCardInternal sheet hSheet

end SelectedFine


/-! ## The three wall comparisons, member by member -/

section WallBlocks

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd2Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

/-- **The coarse member's three wall partitions.**  `u` is the divalent
original endpoint and `v` the trivalent one. -/
theorem coarse_wall_blocks
    (hSmall : divalentOccurrence data hc hab hOne fullDim star = smallTarget input profile)
    (u v : target.V)
    (hBgEdge : ∀ edge ∈ GluingDatum.incidentEdges u, ∀ sheet : Fin degree,
      ¬ (mergedPartition data a b).Rel (input.distinguishedBlock.1 : Fin degree) sheet →
      (data.edgePartition edge).block sheet = (data.vertexPartition u).block sheet)
    (hBgTri : ∀ sheet : Fin degree,
      ¬ (mergedPartition data a b).Rel (input.distinguishedBlock.1 : Fin degree) sheet →
      (data.vertexPartition v).block sheet = (mergedPartition data a b).block sheet)
    (hFlagAt : unfoldEdge hc hab hOne (divalentOccurrence data hc hab hOne fullDim star) ∈
      GluingDatum.incidentEdges u)
    (hContractedAt : contracted ∈ GluingDatum.incidentEdges u)
    (hURefines : (data.vertexPartition u).Refines (mergedPartition data a b))
    (hVRefines : (data.vertexPartition v).Refines (mergedPartition data a b))
    (hUJoined : JoinedOnBlock (data.vertexPartition u) (mergedPartition data a b)
      (input.distinguishedBlock.1 : Fin degree))
    (hVJoined : JoinedOnBlock (data.vertexPartition v) (mergedPartition data a b)
      (input.distinguishedBlock.1 : Fin degree))
    (hNewJoined : JoinedOnBlock (data.edgePartition contracted) (mergedPartition data a b)
      (input.distinguishedBlock.1 : Fin degree)) :
    (∀ sheet, (data.vertexPartition u).block sheet =
        (pasted (coarseCandidate input profile)).left.block sheet) ∧
      (∀ sheet, (data.vertexPartition v).block sheet =
        (pasted (coarseCandidate input profile)).right.block sheet) ∧
      (∀ sheet, (data.edgePartition contracted).block sheet =
        (pasted (coarseCandidate input profile)).newEdge.block sheet) := by
  classical
  have hFlagEq : (data.edgePartition (unfoldEdge hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star))).block =
      (finePartition input profile).block := by
    rw [hSmall]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet
    · exact (block_eq_of_joinedOnBlock_local _ _ _ hURefines hUJoined sheet hSel).trans
        ((merged_block_eq_wall_block data hc hab hOne sheet).trans
          (W3Nd2Survival.coarse_pasted_left_block_selected input profile sheet
            (cast (merged_rel_eq_wall_rel data hc hab hOne star input sheet) hSel)).symm)
    · have hOffWall : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          (input.distinguishedBlock.1 : Fin degree) sheet :=
        fun h ↦ hSel (cast (merged_rel_eq_wall_rel data hc hab hOne star input sheet).symm h)
      exact ((hBgEdge _ hFlagAt sheet hSel).symm.trans (congrFun hFlagEq sheet)).trans
        (W3Nd2Background.coarse_background_left_block input profile sheet hOffWall).symm
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet
    · exact (block_eq_of_joinedOnBlock_local _ _ _ hVRefines hVJoined sheet hSel).trans
        ((merged_block_eq_wall_block data hc hab hOne sheet).trans
          (W3Nd2Survival.coarse_pasted_right_block_selected input profile sheet
            (cast (merged_rel_eq_wall_rel data hc hab hOne star input sheet) hSel)).symm)
    · have hOffWall : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          (input.distinguishedBlock.1 : Fin degree) sheet :=
        fun h ↦ hSel (cast (merged_rel_eq_wall_rel data hc hab hOne star input sheet).symm h)
      exact (hBgTri sheet hSel).trans
        ((merged_block_eq_wall_block data hc hab hOne sheet).trans
          (W3Nd2StableLift.coarse_background_right_block input profile sheet hOffWall).symm)
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet
    · exact (block_eq_of_joinedOnBlock_local _ _ _
        (edgePartition_refines_mergedPartition data hc) hNewJoined sheet hSel).trans
        ((merged_block_eq_wall_block data hc hab hOne sheet).trans
          (W3Nd2Survival.coarse_pasted_newEdge_block_selected input profile sheet
            (cast (merged_rel_eq_wall_rel data hc hab hOne star input sheet) hSel)).symm)
    · have hOffWall : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          (input.distinguishedBlock.1 : Fin degree) sheet :=
        fun h ↦ hSel (cast (merged_rel_eq_wall_rel data hc hab hOne star input sheet).symm h)
      exact ((hBgEdge _ hContractedAt sheet hSel).trans
        ((hBgEdge _ hFlagAt sheet hSel).symm.trans (congrFun hFlagEq sheet))).trans
        (W3Nd2Background.coarse_background_newEdge_block input profile sheet hOffWall).symm

/-- **The fine member's three wall partitions.**  Here the trivalent endpoint
and the contracted occurrence carry the strictly smaller class `A^{(q)}`. -/
theorem fine_wall_blocks
    (hLarge : divalentOccurrence data hc hab hOne fullDim star = largeTarget input profile)
    (u v : target.V)
    (hBgEdge : ∀ edge ∈ GluingDatum.incidentEdges u, ∀ sheet : Fin degree,
      ¬ (mergedPartition data a b).Rel (input.distinguishedBlock.1 : Fin degree) sheet →
      (data.edgePartition edge).block sheet = (data.vertexPartition u).block sheet)
    (hBgTri : ∀ sheet : Fin degree,
      ¬ (mergedPartition data a b).Rel (input.distinguishedBlock.1 : Fin degree) sheet →
      (data.vertexPartition v).block sheet = (mergedPartition data a b).block sheet)
    (hFlagAt : unfoldEdge hc hab hOne (divalentOccurrence data hc hab hOne fullDim star) ∈
      GluingDatum.incidentEdges u)
    (hContractedAt : contracted ∈ GluingDatum.incidentEdges u)
    (hURefines : (data.vertexPartition u).Refines (mergedPartition data a b))
    (hUJoined : JoinedOnBlock (data.vertexPartition u) (mergedPartition data a b)
      (input.distinguishedBlock.1 : Fin degree))
    (hVSelected : ∀ sheet, (mergedPartition data a b).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet →
      (data.vertexPartition v).block sheet = (finePartition input profile).block sheet)
    (hNewSelected : ∀ sheet, (mergedPartition data a b).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet →
      (data.edgePartition contracted).block sheet = (finePartition input profile).block sheet) :
    (∀ sheet, (data.vertexPartition u).block sheet =
        (pasted (fineCandidate input profile)).left.block sheet) ∧
      (∀ sheet, (data.vertexPartition v).block sheet =
        (pasted (fineCandidate input profile)).right.block sheet) ∧
      (∀ sheet, (data.edgePartition contracted).block sheet =
        (pasted (fineCandidate input profile)).newEdge.block sheet) := by
  classical
  have hFlagEq : (data.edgePartition (unfoldEdge hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star))).block =
      (largePartition input profile).block := by
    rw [hLarge]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet
    · exact (block_eq_of_joinedOnBlock_local _ _ _ hURefines hUJoined sheet hSel).trans
        ((merged_block_eq_wall_block data hc hab hOne sheet).trans
          (W3Nd2FineCandidates.pasted_left_block_selected input profile sheet
            (cast (merged_rel_eq_wall_rel data hc hab hOne star input sheet) hSel)).symm)
    · have hOffWall : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          (input.distinguishedBlock.1 : Fin degree) sheet :=
        fun h ↦ hSel (cast (merged_rel_eq_wall_rel data hc hab hOne star input sheet).symm h)
      exact ((hBgEdge _ hFlagAt sheet hSel).symm.trans (congrFun hFlagEq sheet)).trans
        (W3Nd2Background.fine_background_left_block input profile sheet hOffWall).symm
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet
    · exact (hVSelected sheet hSel).trans
        (W3Nd2FineCandidates.pasted_right_block_selected input profile sheet
          (cast (merged_rel_eq_wall_rel data hc hab hOne star input sheet) hSel)).symm
    · have hOffWall : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          (input.distinguishedBlock.1 : Fin degree) sheet :=
        fun h ↦ hSel (cast (merged_rel_eq_wall_rel data hc hab hOne star input sheet).symm h)
      exact (hBgTri sheet hSel).trans
        ((merged_block_eq_wall_block data hc hab hOne sheet).trans
          (W3Nd2StableLift.fine_background_right_block input profile sheet hOffWall).symm)
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel
        (input.distinguishedBlock.1 : Fin degree) sheet
    · exact (hNewSelected sheet hSel).trans
        (W3Nd2FineCandidates.pasted_newEdge_block_selected input profile sheet
          (cast (merged_rel_eq_wall_rel data hc hab hOne star input sheet) hSel)).symm
    · have hOffWall : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          (input.distinguishedBlock.1 : Fin degree) sheet :=
        fun h ↦ hSel (cast (merged_rel_eq_wall_rel data hc hab hOne star input sheet).symm h)
      exact ((hBgEdge _ hContractedAt sheet hSel).trans
        ((hBgEdge _ hFlagAt sheet hSel).symm.trans (congrFun hFlagEq sheet))).trans
        (W3Nd2Background.fine_background_newEdge_block input profile sheet hOffWall).symm

end WallBlocks


/-! ## Pointwise matching against the named member -/

section Matching

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd2Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

include hForest hCompat

/-- **`M^{(1)}` matches the coarse Figure 31 member, pointwise.** -/
theorem coarse_sameBlocks
    (hSmall : divalentOccurrence data hc hab hOne fullDim star = smallTarget input profile) :
    (∀ vertex, ((GluingTransport.transport
          (coarseTargetIso data hc hab hOne fullDim star input profile hSmall)
          data).vertexPartition vertex).SameBlocks
        ((coarseCandidate input profile).datum.vertexPartition vertex)) ∧
      (∀ edge, ((GluingTransport.transport
          (coarseTargetIso data hc hab hOne fullDim star input profile hSmall)
          data).edgePartition edge).SameBlocks
        ((coarseCandidate input profile).datum.edgePartition edge)) := by
  classical
  have hSide : ∀ edge, (coarseCandidate input profile).right edge =
      rightOf (divalentOccurrence data hc hab hOne fullDim star) edge := fun edge ↦
    (W3Nd2IncomingSelectedCensus.coarseCandidate_right input profile edge).trans
      (congrArg (fun place ↦ rightOf place edge) hSmall).symm
  obtain ⟨hJoinedA, hJoinedB⟩ := coarse_selected_endpoints_joined data hc hab hOne fullDim
    hForest hCompat star input profile hSmall
  have hNewJoined := coarse_selected_contracted_joined data hc hab hOne fullDim hForest hCompat
    star input profile hSmall
  rcases endpoint_valencies data hc hab hOne fullDim star with
    ⟨hLeftDiv, _, _, _⟩ | ⟨_, hRightDiv, _, _⟩
  · have hFlagAt : unfoldEdge hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) ∈ GluingDatum.incidentEdges a :=
      (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
        (divalentOccurrence_spec data hc hab hOne fullDim star).1).mp
        (divalentOccurrence_right_eq_false data hc hab hOne fullDim star hLeftDiv)
    obtain ⟨hBlockLeft, hBlockRight, hBlockNew⟩ := coarse_wall_blocks data hc hab hOne fullDim
      star input profile hSmall a b
      (fun edge hEdge sheet hOff ↦ background_edge_block_eq_of_left_divalent data hc hab hOne
        fullDim hForest input hLeftDiv edge hEdge sheet hOff)
      (fun sheet hOff ↦ background_trivalent_block_eq_of_left_divalent data hc hab hOne
        fullDim hForest input hLeftDiv sheet hOff)
      hFlagAt (contracted_mem_incidentEdges_left hc)
      (vertexPartition_refines_mergedPartition data a b)
      (vertexPartition_refines_mergedPartition_right data a b)
      hJoinedA hJoinedB hNewJoined
    obtain ⟨hTransLeft, hTransRight⟩ := transported_endpoints_of_left_divalent data hc hab hOne
      fullDim star (coarseCandidate input profile).right
      (coarse_placement_of_eq_small data hc hab hOne fullDim star input profile hSmall)
      hSide hLeftDiv
    exact sameBlocks_of_wall_blocks data hc hab hOne fullDim.targetConnected fullDim.targetGenus
      (coarseCandidate input profile)
      (coarse_placement_of_eq_small data hc hab hOne fullDim star input profile hSmall)
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransLeft).trans (hBlockLeft sheet))
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransRight).trans (hBlockRight sheet))
      hBlockNew
  · have hFlagAt : unfoldEdge hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) ∈ GluingDatum.incidentEdges b :=
      (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp
        (divalentOccurrence_right_eq_true data hc hab hOne fullDim star hRightDiv)
    obtain ⟨hBlockLeft, hBlockRight, hBlockNew⟩ := coarse_wall_blocks data hc hab hOne fullDim
      star input profile hSmall b a
      (fun edge hEdge sheet hOff ↦ background_edge_block_eq_of_right_divalent data hc hab hOne
        fullDim hForest input hRightDiv edge hEdge sheet hOff)
      (fun sheet hOff ↦ background_trivalent_block_eq_of_right_divalent data hc hab hOne
        fullDim hForest input hRightDiv sheet hOff)
      hFlagAt (contracted_mem_incidentEdges_right hc)
      (vertexPartition_refines_mergedPartition_right data a b)
      (vertexPartition_refines_mergedPartition data a b)
      hJoinedB hJoinedA hNewJoined
    obtain ⟨hTransLeft, hTransRight⟩ := transported_endpoints_of_right_divalent data hc hab hOne
      fullDim star (coarseCandidate input profile).right
      (coarse_placement_of_eq_small data hc hab hOne fullDim star input profile hSmall)
      hSide hRightDiv
    exact sameBlocks_of_wall_blocks data hc hab hOne fullDim.targetConnected fullDim.targetGenus
      (coarseCandidate input profile)
      (coarse_placement_of_eq_small data hc hab hOne fullDim star input profile hSmall)
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransLeft).trans (hBlockLeft sheet))
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransRight).trans (hBlockRight sheet))
      hBlockNew


/-- **`M^{(2)}` matches the oppositely oriented fine Figure 31 member,
pointwise.** -/
theorem fine_sameBlocks
    (hLarge : divalentOccurrence data hc hab hOne fullDim star = largeTarget input profile) :
    (∀ vertex, ((GluingTransport.transport
          (fineTargetIso data hc hab hOne fullDim star input profile hLarge)
          data).vertexPartition vertex).SameBlocks
        ((fineCandidate input profile).datum.vertexPartition vertex)) ∧
      (∀ edge, ((GluingTransport.transport
          (fineTargetIso data hc hab hOne fullDim star input profile hLarge)
          data).edgePartition edge).SameBlocks
        ((fineCandidate input profile).datum.edgePartition edge)) := by
  classical
  have hSide : ∀ edge, (fineCandidate input profile).right edge =
      rightOf (divalentOccurrence data hc hab hOne fullDim star) edge := fun edge ↦
    (W3Nd2IncomingSelectedCensus.fineCandidate_right input profile edge).trans
      (congrArg (fun place ↦ rightOf place edge) hLarge).symm
  have hSideNe := small_large_side_ne data hc hab hOne fullDim star input profile (Or.inr hLarge)
  rcases endpoint_valencies data hc hab hOne fullDim star with
    ⟨hLeftDiv, _, _, _⟩ | ⟨_, hRightDiv, _, _⟩
  · have hDiv := divalentOccurrence_right_eq_false data hc hab hOne fullDim star hLeftDiv
    have hLargeSide : IncomingTargetExpansion.right hc hab hOne
        (largeTarget input profile) = false :=
      (congrArg (IncomingTargetExpansion.right hc hab hOne) hLarge).symm.trans hDiv
    have hSmallSide : IncomingTargetExpansion.right hc hab hOne
        (smallTarget input profile) = true := by
      cases hValue : IncomingTargetExpansion.right hc hab hOne (smallTarget input profile)
      · exact absurd (hValue.trans hLargeSide.symm) hSideNe
      · rfl
    have hFlagAt : unfoldEdge hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) ∈ GluingDatum.incidentEdges a :=
      (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
        (divalentOccurrence_spec data hc hab hOne fullDim star).1).mp hDiv
    obtain ⟨hUJoined, hVSelected, hNewSelected⟩ := fine_selected_blocks data hc hab hOne fullDim
      hForest hCompat star input profile hLarge a b
      (W3Nd2IncomingSheetClasses.endpoint_target_of_false data hc hab hOne profile.large.1
        hLargeSide)
      (W3Nd2IncomingSheetClasses.endpoint_target_of_true data hc hab hOne profile.small.1
        hSmallSide)
      (vertexPartition_refines_mergedPartition_right data a b)
    obtain ⟨hBlockLeft, hBlockRight, hBlockNew⟩ := fine_wall_blocks data hc hab hOne fullDim
      star input profile hLarge a b
      (fun edge hEdge sheet hOff ↦ background_edge_block_eq_of_left_divalent data hc hab hOne
        fullDim hForest input hLeftDiv edge hEdge sheet hOff)
      (fun sheet hOff ↦ background_trivalent_block_eq_of_left_divalent data hc hab hOne
        fullDim hForest input hLeftDiv sheet hOff)
      hFlagAt (contracted_mem_incidentEdges_left hc)
      (vertexPartition_refines_mergedPartition data a b)
      hUJoined hVSelected hNewSelected
    obtain ⟨hTransLeft, hTransRight⟩ := transported_endpoints_of_left_divalent data hc hab hOne
      fullDim star (fineCandidate input profile).right
      (fine_placement_of_eq_large data hc hab hOne fullDim star input profile hLarge)
      hSide hLeftDiv
    exact sameBlocks_of_wall_blocks data hc hab hOne fullDim.targetConnected fullDim.targetGenus
      (fineCandidate input profile)
      (fine_placement_of_eq_large data hc hab hOne fullDim star input profile hLarge)
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransLeft).trans (hBlockLeft sheet))
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransRight).trans (hBlockRight sheet))
      hBlockNew
  · have hDiv := divalentOccurrence_right_eq_true data hc hab hOne fullDim star hRightDiv
    have hLargeSide : IncomingTargetExpansion.right hc hab hOne
        (largeTarget input profile) = true :=
      (congrArg (IncomingTargetExpansion.right hc hab hOne) hLarge).symm.trans hDiv
    have hSmallSide : IncomingTargetExpansion.right hc hab hOne
        (smallTarget input profile) = false := by
      cases hValue : IncomingTargetExpansion.right hc hab hOne (smallTarget input profile)
      · rfl
      · exact absurd (hValue.trans hLargeSide.symm) hSideNe
    have hFlagAt : unfoldEdge hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) ∈ GluingDatum.incidentEdges b :=
      (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp hDiv
    obtain ⟨hUJoined, hVSelected, hNewSelected⟩ := fine_selected_blocks data hc hab hOne fullDim
      hForest hCompat star input profile hLarge b a
      (W3Nd2IncomingSheetClasses.endpoint_target_of_true data hc hab hOne profile.large.1
        hLargeSide)
      (W3Nd2IncomingSheetClasses.endpoint_target_of_false data hc hab hOne profile.small.1
        hSmallSide)
      (vertexPartition_refines_mergedPartition data a b)
    obtain ⟨hBlockLeft, hBlockRight, hBlockNew⟩ := fine_wall_blocks data hc hab hOne fullDim
      star input profile hLarge b a
      (fun edge hEdge sheet hOff ↦ background_edge_block_eq_of_right_divalent data hc hab hOne
        fullDim hForest input hRightDiv edge hEdge sheet hOff)
      (fun sheet hOff ↦ background_trivalent_block_eq_of_right_divalent data hc hab hOne
        fullDim hForest input hRightDiv sheet hOff)
      hFlagAt (contracted_mem_incidentEdges_right hc)
      (vertexPartition_refines_mergedPartition_right data a b)
      hUJoined hVSelected hNewSelected
    obtain ⟨hTransLeft, hTransRight⟩ := transported_endpoints_of_right_divalent data hc hab hOne
      fullDim star (fineCandidate input profile).right
      (fine_placement_of_eq_large data hc hab hOne fullDim star input profile hLarge)
      hSide hRightDiv
    exact sameBlocks_of_wall_blocks data hc hab hOne fullDim.targetConnected fullDim.targetGenus
      (fineCandidate input profile)
      (fine_placement_of_eq_large data hc hab hOne fullDim star input profile hLarge)
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransLeft).trans (hBlockLeft sheet))
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransRight).trans (hBlockRight sheet))
      hBlockNew


/-- The vertex half of `coarse_sameBlocks`, named for the exit statement. -/
theorem coarse_vertexPartitions_sameBlocks
    (hSmall : divalentOccurrence data hc hab hOne fullDim star = smallTarget input profile) :
    ∀ vertex, ((GluingTransport.transport
        (coarseTargetIso data hc hab hOne fullDim star input profile hSmall)
        data).vertexPartition vertex).SameBlocks
      ((coarseCandidate input profile).datum.vertexPartition vertex) :=
  (coarse_sameBlocks data hc hab hOne fullDim hForest hCompat star input profile hSmall).1

/-- The occurrence half of `coarse_sameBlocks`. -/
theorem coarse_edgePartitions_sameBlocks
    (hSmall : divalentOccurrence data hc hab hOne fullDim star = smallTarget input profile) :
    ∀ edge, ((GluingTransport.transport
        (coarseTargetIso data hc hab hOne fullDim star input profile hSmall)
        data).edgePartition edge).SameBlocks
      ((coarseCandidate input profile).datum.edgePartition edge) :=
  (coarse_sameBlocks data hc hab hOne fullDim hForest hCompat star input profile hSmall).2

/-- The vertex half of `fine_sameBlocks`. -/
theorem fine_vertexPartitions_sameBlocks
    (hLarge : divalentOccurrence data hc hab hOne fullDim star = largeTarget input profile) :
    ∀ vertex, ((GluingTransport.transport
        (fineTargetIso data hc hab hOne fullDim star input profile hLarge)
        data).vertexPartition vertex).SameBlocks
      ((fineCandidate input profile).datum.vertexPartition vertex) :=
  (fine_sameBlocks data hc hab hOne fullDim hForest hCompat star input profile hLarge).1

/-- The occurrence half of `fine_sameBlocks`. -/
theorem fine_edgePartitions_sameBlocks
    (hLarge : divalentOccurrence data hc hab hOne fullDim star = largeTarget input profile) :
    ∀ edge, ((GluingTransport.transport
        (fineTargetIso data hc hab hOne fullDim star input profile hLarge)
        data).edgePartition edge).SameBlocks
      ((fineCandidate input profile).datum.edgePartition edge) :=
  (fine_sameBlocks data hc hab hOne fullDim hForest hCompat star input profile hLarge).2

end Matching

/-! ## The certified exit: the incoming datum IS a named Figure 31 member -/

section Exit

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- The literal normalization receipt against a named comparison datum: a sheet
relabelling carrying the transported incoming datum onto it, an honest
full-dimensional presentation in the original coordinates, the original
target-edge labelling composed with the actual occurrence map, every entry of
the length matrix unchanged, each surviving occurrence sent to the occurrence
with the *same* target occurrence and the *same* sheet, and every stable-row
matrix entry preserved.  The last two clauses are what forbid a hidden
incoming classification or a count-based row bijection. -/
def NormalizedAgainst {outgoing : CFGraph}
    (data : GluingDatum target degree)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (iso : Utilities.CFGraphIso target outgoing) (other : GluingDatum outgoing degree)
    (hVertices : ∀ vertex,
      ((GluingTransport.transport iso data).vertexPartition vertex).SameBlocks
        (other.vertexPartition vertex))
    (hEdges : ∀ edge,
      ((GluingTransport.transport iso data).edgePartition edge).SameBlocks
        (other.edgePartition edge)) : Prop :=
  ∃ relabeling : (GluingTransport.transport iso data).SheetRelabeling,
    relabeling.apply = other ∧
    ∃ presentation : FullDimensionalSourcePresentation other coordinate,
      presentation.labelling.targetEdge =
          fullDim.labelling.targetEdge.trans (GluingTransport.edgeEquiv iso) ∧
        GluingDatum.LengthMatrixPresentation.matrix presentation.labelling.presentation =
          GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation ∧
        (∀ edge : NonDanglingEdge data,
          (TargetPartitionNormalization.nonDanglingEdgeEquiv iso data other hVertices hEdges
            fullDim.valid.1 edge).1.1 =
            (GluingTransport.edgeEquiv iso edge.1.1.1,
              (other.edgePartition (GluingTransport.edgeEquiv iso edge.1.1.1)).repr
                edge.1.1.2)) ∧
        ∀ (path : StablePath data) (edge : target.edges),
          StableSourceMatrix.matrix other
              (TargetPartitionNormalization.stablePathEquiv iso data other hVertices hEdges
                fullDim.valid.1 path) (GluingTransport.edgeEquiv iso edge) =
            StableSourceMatrix.matrix data path edge

/-- `W3Nd2IncomingNormalization.exists_normalized_presentation`, packaged. -/
theorem normalizedAgainst {outgoing : CFGraph}
    (data : GluingDatum target degree)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (iso : Utilities.CFGraphIso target outgoing) (other : GluingDatum outgoing degree)
    (hVertices : ∀ vertex,
      ((GluingTransport.transport iso data).vertexPartition vertex).SameBlocks
        (other.vertexPartition vertex))
    (hEdges : ∀ edge,
      ((GluingTransport.transport iso data).edgePartition edge).SameBlocks
        (other.edgePartition edge)) :
    NormalizedAgainst data fullDim iso other hVertices hEdges :=
  W3Nd2IncomingNormalization.exists_normalized_presentation data fullDim iso other
    hVertices hEdges

end Exit


section Identification

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd2Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

include hForest hCompat

/-- **The incoming-member identification.**  An arbitrary incoming W3 nd2 datum
whose
contraction of the single edge between `a` and `b` is a forest with dangling
compatibility, over a genuine trivalent contracted wall with a Figure 31 nd2
profile, *is* one of the two named Figure 31 members: the orientation
dichotomy `divalentOccurrence_eq_small_or_large` decides which, the literal
Option column dictionary is the actual one, and the stored representative
tables agree after the within-block transpositions of
`Infrastructure.PartitionNormalization`.

The two branches are `M^{(1)}` and `M^{(2)}` and both genuinely occur; the
hypothesis bundle is exactly the one already shown jointly satisfiable by
`W3Nd2IncomingSelectedCensus.selected_fibre_census`. -/
theorem exists_member_normalization :
    (∃ hSmall : divalentOccurrence data hc hab hOne fullDim star = smallTarget input profile,
      (∀ column : Option (contract target hab hOne).edges,
          GluingTransport.edgeEquiv
              (coarseTargetIso data hc hab hOne fullDim star input profile hSmall)
              (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
            occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
              (coarseCandidate input profile).right column) ∧
        NormalizedAgainst data fullDim
          (coarseTargetIso data hc hab hOne fullDim star input profile hSmall)
          (coarseCandidate input profile).datum
          (coarse_vertexPartitions_sameBlocks data hc hab hOne fullDim hForest hCompat star
            input profile hSmall)
          (coarse_edgePartitions_sameBlocks data hc hab hOne fullDim hForest hCompat star
            input profile hSmall)) ∨
      (∃ hLarge : divalentOccurrence data hc hab hOne fullDim star = largeTarget input profile,
        (∀ column : Option (contract target hab hOne).edges,
            GluingTransport.edgeEquiv
                (fineTargetIso data hc hab hOne fullDim star input profile hLarge)
                (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
              occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
                (fineCandidate input profile).right column) ∧
          NormalizedAgainst data fullDim
            (fineTargetIso data hc hab hOne fullDim star input profile hLarge)
            (fineCandidate input profile).datum
            (fine_vertexPartitions_sameBlocks data hc hab hOne fullDim hForest hCompat star
              input profile hLarge)
            (fine_edgePartitions_sameBlocks data hc hab hOne fullDim hForest hCompat star
              input profile hLarge)) := by
  rcases divalentOccurrence_eq_small_or_large data hc hab hOne fullDim hForest hCompat star
      input profile with hSmall | hLarge
  · exact Or.inl ⟨hSmall,
      coarseTargetIso_occurrence data hc hab hOne fullDim star input profile hSmall,
      normalizedAgainst data fullDim _ _ _ _⟩
  · exact Or.inr ⟨hLarge,
      fineTargetIso_occurrence data hc hab hOne fullDim star input profile hLarge,
      normalizedAgainst data fullDim _ _ _ _⟩

end Identification

end DraismaVargas.LocalCases.W3Nd2IncomingMemberMatching
