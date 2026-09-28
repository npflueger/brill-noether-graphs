import DraismaVargas.LocalCases.W3ShiftShrinkExistence
import DraismaVargas.LocalCases.W3ShiftSourceCandidates
import DraismaVargas.LocalCases.W3FourClosure

/-!
# Figure 29's `(k−1, k+1)` pair, and Equation (3) as a gauge family

Source: Draisma--Vargas Part I, Case {w3-r1-nd3-t2-(a>k4)} (the `w3Shift`
case), whose Positions I / II.a / II.b are defined once for the whole
`{w3-r1-nd3-t2}` subtree; Figure 29 and Equation (3).  Part I works with
isomorphism classes of gluing datums (`definition-gd-iso` and the tree-swap and
branch-swap before it); a Lean `GluingDatum` is a fixed value, and the
branch swaps below are how the two are reconciled.

## What this file settles

**The pair.**  `exists_gauge_shift_pair` is the unconditional form of
`W3ShiftSourceCandidates.exists_shift_pair_of_shrinkSheet`.  From a datum of the
case and any one of Figure 29's three orientations it produces a **gauge copy of
the whole shift datum** -- the `GluingDatum`, its `ThirdEquation.W3SourceInput`
and its `W3ShiftSourceCandidates.ShiftProfile` -- carrying both members of
Equation (3)'s pair on the moving direction: the Position II.b shrink member of
new-edge index `k − 1` and the Position II.a grow member of new-edge index
`k + 1`, both valid, both preserving the **original** datum's source genus, with
`A₀` and `eₐ` literally unchanged and the moving index `k` literally the
incoming one.  No `HasShrinkSheet` hypothesis is carried.

**The gauge family.**  `equationThreeGaugeFamily` assembles the pair into a
`W3FourClosure.GaugeFamily` with weights `(k − 1, k + 1)` and
`BalancingRemaining.balance_shift_pair` as its `PositiveBalance`, and
`exists_equationThree_positive_exit` runs `GaugeFamily`'s certified exit on it.

## Why a gauge family, and why two members rather than six

Position II.b really does need a sheet of `eₐ` lying outside `e_b ∪ e_c` (read
line by line in `W3ShiftShrinkExistence`), and at a **fixed** `GluingDatum`
value the case's arithmetic does not supply one:
`W3ShiftShrinkExistence.no_private_sheet_forces_double_cover` shows the
shrink-sheet-free data are exactly the "theta" configurations.  But that is not
an invariant of the wall datum.  Part I's *branch*-swap permutes sheets above
**one** component of `T ∖ {w₀}` only, and its notion of isomorphism allows one
permutation per target element, so at a trivalent `w₀` the three classes move
independently inside `A₀` and only `k₂, k₃, k₄` are invariant.  Two branch
swaps therefore put Position II.b's sheet on any prescribed direction.

What remains is that the pair does not live over one `GluingDatum` **value**
(as for Figure 28), so the family must carry one `base` per member.  A branch
swap is free in the determinant computation, since it leaves the length matrix
literally equal (`RelabelFullDimensional.sheet_matrix_eq`,
`W3FourDisjointness.fullDimensional_gauge`).

Equation (3) is three *independently* balancing pairs,
`(k_α − 1)c⁽ᵠ⁾ + (k_α + 1)c⁽ᵠ⁺¹⁾ = 0`, one per direction, and a
`BalancingValencyTwo.PositiveBalance` needs only positive weights summing the
determinants to zero.  So **one pair suffices**, provided it is the pair on the
incoming member's own direction: every member of Figure 29 shifts exactly one
direction by `±1`, so the incoming member lies in the pair for that direction,
as its `k − 1` member if it shrinks and its `k + 1` member if it grows.  The
exit theorem quantifies over `incoming : Fin 2`, so both alternatives are
served; which of the two it is, and which direction it sits on, is the
incoming-member identification, which is **not** done here.  Both weights are
positive because `min(k₂,k₃,k₄) ≥ 2`, which is *derived*, not assumed:
`W3R1SourceProfile.Nd3Profile.indices_two_le_of_largest_lt` gets it from
`k₂ + k₃ + k₄ = 2|A₀|` together with `|A₀| > k₄`, exactly as Part I does, and
it reaches this file as `ShiftProfile.two_le_moving`
(`one_lt_movingIndex` is its rational form).

## Two shapes of the shrink resolution agree

`shrinkResolution_eq_bothDetachedResolution` checks by `rfl` that
`W3ShiftSourceCandidates.shrinkResolution` and
`ResolutionMkk.bothDetachedResolution` are the **same term**: same `left`, same
`right`, same `newEdge`, same two refinement receipts, with the hypotheses in
the same order.  (`ResolutionMkk.bothDetachedResolution` is the
genus-preserving shape; `ResolutionMkk.detachedResolution`, which sets
`right := wall` while refining `newEdge`, raises the source genus by one.)
Nothing in this file uses `ResolutionMkk.detachedResolution`.

## What a branch swap moves, and what it does not

`W3FourDisjointness.BranchGauge` records the datum-level invariants of a swap,
and it deliberately omits `nonDangling_valency`, so there is no *free*
transported `W3SourceInput`.  `branchSwapInput` supplies exactly that missing
field, from `SheetRelabelStable.nonDanglingValency_map` plus the observation
that the swap's permutation **at the wall** is the identity
(`branchSwap_vertexPermutation_wall`), so a wall block of the swapped datum
names the same wall block of the original.  `branchSwapProfile` then carries the
three surviving occurrences across by `sourceEdgeEquiv`, which keeps each one's
target direction and its source index.  `GaugeCopy` is the list of what the two
members read off the wall and the swap leaves alone.

## What is not proved here

**The honest length-matrix presentations.**  `LimitRows` isolates them as one
named structure, the way `W3FourStableGraph.LimitRows` does for Figure 28: the
two presentations, the wall column, Figure 29's displayed determinants
`c(e_α)/(k_α ∓ 1) + σ₀(J₀,α)` and the common off-wall columns.  No model is
supplied for it here; `W3ShiftHonestBalance` supplies one
(`W3ShiftHonestBalance.limitRows`).  Also not here: the stable-graph transport
(`W3ShiftGraphData`), the incoming-member identification, and the restatement
of the exit in the incoming cover's original coordinates.
-/

namespace DraismaVargas.LocalCases.W3ShiftClosure

open DraismaVargas.Infrastructure
open ThirdEquation W3FourDisjointness W4StableSource W4Assembly W3R1SourceProfile
open StableLocalProperties W3ShiftSourceCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

/-! ## `shrinkResolution` is `bothDetachedResolution` -/

/-- **The two shrink shapes are the same term.**
`ResolutionMkk.bothDetachedResolution` -- the genus-preserving shape, beside
the genus-raising `detachedResolution` -- and
`W3ShiftSourceCandidates.shrinkResolution`, which Figure 29's `k − 1` member is
built on, agree on every field and take their hypotheses in the same order, so
this is `rfl`.  So `shrinkResolution` duplicates
`ResolutionMkk.bothDetachedResolution`, which is reachable without importing
the shift case. -/
theorem shrinkResolution_eq_bothDetachedResolution {d : ℕ}
    (wallPartition endpoint : SheetPartition d) (transfer remainder : Fin d)
    (hNe : transfer ≠ remainder)
    (hWallTogether : wallPartition.Rel transfer remainder)
    (hEndpointTogether : endpoint.Rel transfer remainder)
    (hRefines : endpoint.Refines wallPartition) :
    shrinkResolution wallPartition endpoint transfer remainder hNe hWallTogether
        hEndpointTogether hRefines =
      ResolutionMkk.bothDetachedResolution wallPartition endpoint transfer remainder
        hNe hWallTogether hEndpointTogether hRefines := rfl

/-! ## What a branch swap does at the wall

`W3FourDisjointness.branchSwapOfPerm` relabels every gluing relation above one
component of `T ∖ {w₀}`.  The wall itself is outside that component, so the
swap's permutation at `wall` is the identity and a wall block of the swapped
datum names the same wall block of the original. -/

/-- The wall's own sheet permutation under a branch swap is the identity:
`TargetBranchRegion.vertexMoved_wall` says the wall is never in the moved
branch. -/
theorem branchSwap_vertexPermutation_wall (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).vertexPermutation wall =
      Equiv.refl _ := by
  change GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.vertexMoved wall root hRoot wall) permutation = _
  rw [TargetBranchRegion.vertexMoved_wall]
  rfl

/-- Every target edge outside the moved branch keeps its sheet permutation. -/
theorem branchSwap_edgePermutation_of_fixed (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (edge : target.edges)
    (hFixed : TargetBranchRegion.edgeMoved wall root hRoot edge = false) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).edgePermutation edge =
      Equiv.refl _ := by
  change GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall root hRoot edge) permutation = _
  rw [hFixed]
  rfl

/-- Every target edge inside the moved branch carries the permutation. -/
theorem branchSwap_edgePermutation_of_moved (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (edge : target.edges)
    (hMoved : TargetBranchRegion.edgeMoved wall root hRoot edge = true) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).edgePermutation edge =
      permutation := by
  change GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall root hRoot edge) permutation = _
  rw [hMoved]
  rfl

/-- An occurrence at the wall has the wall as one of its ends. -/
theorem mem_incidentEdges_ends {edge : target.edges}
    (hEdge : edge ∈ GluingDatum.incidentEdges wall) :
    (edge : target.V × target.V).1 = wall ∨ (edge : target.V × target.V).2 = wall := by
  simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
    true_and] using hEdge

/-- A wall block of the swapped datum names the same wall-block source vertex of
the original: the wall partition is unchanged as a term and the swap's
permutation there is the identity. -/
theorem branchSwap_sourceVertex (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (block : WallBlock data wall)
    (swappedBlock : WallBlock (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply wall) (hVal : swappedBlock.1 = block.1) :
    WallBlock.sourceVertex (branchSwapOfPerm data wall root hRoot permutation
        hFix).apply wall swappedBlock =
      (branchSwapOfPerm data wall root hRoot permutation hFix).sourceVertexEquiv
        (WallBlock.sourceVertex data wall block) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · show ((branchSwapOfPerm data wall root hRoot permutation hFix).apply.vertexPartition
        wall).repr swappedBlock.1 =
      (branchSwapOfPerm data wall root hRoot permutation hFix).vertexPermutation wall
        ((data.vertexPartition wall).repr block.1)
    rw [branchSwap_vertexPermutation_wall (data := data) (wall := wall) root hRoot
      permutation hFix, swappedBlock.2, block.2, hVal]
    rfl

/-- Incident source occurrences at a wall block transport across a branch swap,
by the swap's own source-edge equivalence. -/
noncomputable def branchSwapIncident (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (block : WallBlock data wall)
    (swappedBlock : WallBlock (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply wall) (hVal : swappedBlock.1 = block.1) :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall block) ≃
      IncidentSourceEdge (branchSwapOfPerm data wall root hRoot permutation hFix).apply
        (WallBlock.sourceVertex (branchSwapOfPerm data wall root hRoot permutation
          hFix).apply wall swappedBlock) :=
  (branchSwapOfPerm data wall root hRoot permutation hFix).sourceEdgeEquiv.subtypeEquiv
    fun edge ↦ by
      rw [branchSwap_sourceVertex root hRoot permutation hFix block swappedBlock hVal]
      exact (SheetRelabelPruning.incident_sourceEdgeEquiv_iff _ edge _).symm

theorem branchSwapIncident_val (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (block : WallBlock data wall)
    (swappedBlock : WallBlock (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply wall) (hVal : swappedBlock.1 = block.1)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    (branchSwapIncident root hRoot permutation hFix block swappedBlock hVal edge).1 =
      (branchSwapOfPerm data wall root hRoot permutation hFix).sourceEdgeEquiv edge.1 :=
  rfl

/-- The transported occurrence lies above the same target direction. -/
theorem branchSwapIncident_target (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (block : WallBlock data wall)
    (swappedBlock : WallBlock (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply wall) (hVal : swappedBlock.1 = block.1)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    (branchSwapIncident root hRoot permutation hFix block swappedBlock hVal
      edge).1.1.1 = edge.1.1.1 := rfl

/-- The transported occurrence keeps its source index. -/
theorem branchSwapIncident_index (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (block : WallBlock data wall)
    (swappedBlock : WallBlock (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply wall) (hVal : swappedBlock.1 = block.1)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).apply.sourceEdgeIndex
        (branchSwapIncident root hRoot permutation hFix block swappedBlock hVal
          edge).1 = data.sourceEdgeIndex edge.1 :=
  SheetRelabelStable.sourceEdgeIndex_map _ edge.1

/-- Survivors transport across a branch swap: pruning is preserved in both
directions by `SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff`. -/
theorem branchSwap_survivors (hConnected : data.Connected) (root : target.V)
    (hRoot : root ≠ wall) (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (block : WallBlock data wall)
    (swappedBlock : WallBlock (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply wall) (hVal : swappedBlock.1 = block.1) :
    survivors (branchSwapOfPerm data wall root hRoot permutation hFix).apply
        swappedBlock =
      (survivors data block).image
        (branchSwapIncident root hRoot permutation hFix block swappedBlock hVal) := by
  classical
  ext edge
  constructor
  · intro hEdge
    obtain ⟨pre, rfl⟩ :=
      (branchSwapIncident root hRoot permutation hFix block swappedBlock hVal).surjective
        edge
    refine Finset.mem_image.mpr ⟨pre, ?_, rfl⟩
    rw [mem_survivors] at hEdge ⊢
    intro hDangling
    exact hEdge ((SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff _ hConnected
      pre.1).mpr hDangling)
  · intro hEdge
    obtain ⟨pre, hPre, rfl⟩ := Finset.mem_image.mp hEdge
    rw [mem_survivors] at hPre ⊢
    intro hDangling
    exact hPre ((SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff _ hConnected
      pre.1).mp hDangling)

/-- Local ramification at the wall is a branch-swap invariant: it depends only on
the wall partition and on the induced block counts of the incident edge
partitions, and `W3FourDisjointness` fixes both. -/
theorem branchSwap_localRamification (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (block : WallBlock data wall)
    (swappedBlock : WallBlock (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply wall) (hVal : swappedBlock.1 = block.1) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).apply.localRamification
        wall swappedBlock = data.localRamification wall block := by
  have hCount : ∀ edge : target.edges,
      ((branchSwapOfPerm data wall root hRoot permutation hFix).apply.edgePartition
          edge).blockCountWithin ((branchSwapOfPerm data wall root hRoot permutation
            hFix).apply.vertexPartition wall) swappedBlock.1 =
        (data.edgePartition edge).blockCountWithin (data.vertexPartition wall)
          block.1 := by
    intro edge
    rw [hVal]
    exact branchSwapOfPerm_blockCountWithin_wall data wall root hRoot permutation hFix
      edge block.1
  have hCard : ((branchSwapOfPerm data wall root hRoot permutation
        hFix).apply.vertexPartition wall).blockCard swappedBlock.1 =
      (data.vertexPartition wall).blockCard block.1 := by
    rw [hVal]
    exact congrArg (fun partition ↦ SheetPartition.blockCard partition block.1)
      (branchSwapOfPerm_vertexPartition_wall data wall root hRoot permutation hFix)
  unfold GluingDatum.localRamification
  rw [hCard, Finset.sum_congr rfl (fun edge _ ↦ by rw [hCount edge])]

/-- A branch swap preserves the quotient-source genus: its source-edge and
source-vertex equivalences are bijections. -/
theorem branchSwap_sourceGenus (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet) :
    genus (branchSwapOfPerm data wall root hRoot permutation hFix).apply.sourceGraph =
      genus data.sourceGraph := by
  have hEdges := Fintype.card_congr
    (branchSwapOfPerm data wall root hRoot permutation hFix).sourceEdgeEquiv
  have hVertices := Fintype.card_congr
    (branchSwapOfPerm data wall root hRoot permutation hFix).sourceVertexEquiv
  simp only [genus, GluingDatum.sourceGraph_edges_card]
  change
    ((Fintype.card (branchSwapOfPerm data wall root hRoot permutation
        hFix).apply.SourceEdge : ℤ) -
      (Fintype.card (branchSwapOfPerm data wall root hRoot permutation
        hFix).apply.SourceVertex : ℤ) + 1 =
      (Fintype.card data.SourceEdge : ℤ) - (Fintype.card data.SourceVertex : ℤ) + 1)
  omega

/-! ## The source input and the shift profile transport across a branch swap -/

/-- **A trivalent source input transports across a branch swap.**  Four of
its five fields are `W3FourDisjointness.BranchGauge`'s own -- `valid`,
`stablePathCard`, `noGlue`, `targetExcess`.  The fifth, `nonDangling_valency`,
is precisely the one that gauge does **not** record, which is why
`W3FourDisjointness` states that there is no transported `W3SourceInput` for
free; it is supplied here by `SheetRelabelStable.nonDanglingValency_map`
together with `branchSwap_sourceVertex`. -/
theorem branchSwapInput (input : W3SourceInput data star) (root : target.V)
    (hRoot : root ≠ wall) (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet) :
    W3SourceInput (branchSwapOfPerm data wall root hRoot permutation hFix).apply
      star := by
  have gauge := branchSwapOfPerm_branchGauge data wall root hRoot permutation hFix
  refine { valid := gauge.valid input.valid
           stablePath_card := ?_
           dangling_no_glue := gauge.noGlue input.valid input.dangling_no_glue
           nonDangling_valency := ?_
           equation_c := by rw [gauge.targetExcess]; exact input.equation_c }
  · rw [gauge.stablePathCard input.valid]; exact input.stablePath_card
  · intro sourceBlock
    have hIdem : (data.vertexPartition wall).repr sourceBlock.1 = sourceBlock.1 := by
      rw [← gauge.wallPartition]; exact sourceBlock.2
    rw [branchSwap_sourceVertex root hRoot permutation hFix ⟨sourceBlock.1, hIdem⟩
        sourceBlock rfl,
      SheetRelabelStable.nonDanglingValency_map _ input.valid.1]
    exact input.nonDangling_valency ⟨sourceBlock.1, hIdem⟩

/-- The swapped datum has the same distinguished wall block.  `W3SourceInput` is
a proposition, so the swapped input may be taken as an arbitrary proof rather
than as `branchSwapInput`'s own. -/
theorem branchSwap_distinguishedBlock (input : W3SourceInput data star)
    (root : target.V) (hRoot : root ≠ wall) (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (swappedInput : W3SourceInput (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply star) :
    swappedInput.distinguishedBlock.1 = input.distinguishedBlock.1 := by
  have gauge := branchSwapOfPerm_branchGauge data wall root hRoot permutation hFix
  have hIdem : (data.vertexPartition wall).repr swappedInput.distinguishedBlock.1 =
      swappedInput.distinguishedBlock.1 := by
    rw [← gauge.wallPartition]; exact swappedInput.distinguishedBlock.2
  by_contra hNe
  have hBlockNe : (⟨swappedInput.distinguishedBlock.1, hIdem⟩ : WallBlock data wall) ≠
      input.distinguishedBlock := fun h ↦ hNe (congrArg Subtype.val h)
  have hZero := input.localRamification_eq_zero_of_ne hBlockNe
  have hOne := swappedInput.localRamification_distinguishedBlock
  rw [branchSwap_localRamification root hRoot permutation hFix
    ⟨swappedInput.distinguishedBlock.1, hIdem⟩ swappedInput.distinguishedBlock rfl,
    hZero] at hOne
  exact absurd hOne (by norm_num)

/-- The distinguished wall block keeps its cardinality `|A₀|`. -/
theorem branchSwap_blockCard (input : W3SourceInput data star) (root : target.V)
    (hRoot : root ≠ wall) (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (swappedInput : W3SourceInput (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply star) :
    ((branchSwapOfPerm data wall root hRoot permutation hFix).apply.vertexPartition
        wall).blockCard swappedInput.distinguishedBlock.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 := by
  rw [branchSwap_distinguishedBlock input root hRoot permutation hFix swappedInput]
  exact congrArg
    (fun partition ↦ SheetPartition.blockCard partition input.distinguishedBlock.1)
    (branchSwapOfPerm_vertexPartition_wall data wall root hRoot permutation hFix)

/-- The case hypothesis `k_α < |A₀|`, read on the transported moving
occurrence.  This is what lets `branchSwapProfile` fill in Position II.a's
transferred sheet with `exists_transferSheet`. -/
theorem branchSwap_moving_lt (input : W3SourceInput data star)
    (shift : ShiftProfile input) (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (swappedInput : W3SourceInput (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply star) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).apply.sourceEdgeIndex
        (branchSwapIncident root hRoot permutation hFix input.distinguishedBlock
          swappedInput.distinguishedBlock
          (branchSwap_distinguishedBlock input root hRoot permutation hFix swappedInput)
          shift.moving).1 <
      ((branchSwapOfPerm data wall root hRoot permutation hFix).apply.vertexPartition
        wall).blockCard swappedInput.distinguishedBlock.1 := by
  rw [branchSwapIncident_index,
    branchSwap_blockCard input root hRoot permutation hFix swappedInput]
  exact shift.moving_lt

/-- **Figure 29's shift profile transports across a branch swap.**  The three
surviving occurrences are carried by `sourceEdgeEquiv`, which keeps each one's
target direction and its source index; the wall block, its cardinality and the
case's arithmetic `k + k' + k'' = 2|A₀|`, `k < |A₀|`, `2 ≤ k` are literally
unchanged. -/
noncomputable def branchSwapProfile (input : W3SourceInput data star)
    (shift : ShiftProfile input) (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (swappedInput : W3SourceInput (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply star) :
    ShiftProfile swappedInput where
  moving := branchSwapIncident root hRoot permutation hFix input.distinguishedBlock
    swappedInput.distinguishedBlock
    (branchSwap_distinguishedBlock input root hRoot permutation hFix swappedInput)
    shift.moving
  firstRest := branchSwapIncident root hRoot permutation hFix input.distinguishedBlock
    swappedInput.distinguishedBlock
    (branchSwap_distinguishedBlock input root hRoot permutation hFix swappedInput)
    shift.firstRest
  secondRest := branchSwapIncident root hRoot permutation hFix input.distinguishedBlock
    swappedInput.distinguishedBlock
    (branchSwap_distinguishedBlock input root hRoot permutation hFix swappedInput)
    shift.secondRest
  moving_ne_first := fun h ↦ shift.moving_ne_first ((branchSwapIncident root hRoot
    permutation hFix _ _ _).injective h)
  moving_ne_second := fun h ↦ shift.moving_ne_second ((branchSwapIncident root hRoot
    permutation hFix _ _ _).injective h)
  first_ne_second := fun h ↦ shift.first_ne_second ((branchSwapIncident root hRoot
    permutation hFix _ _ _).injective h)
  surviving := by
    rw [branchSwap_survivors input.valid.1 root hRoot permutation hFix
      input.distinguishedBlock swappedInput.distinguishedBlock
      (branchSwap_distinguishedBlock input root hRoot permutation hFix swappedInput),
      shift.surviving]
    simp only [Finset.image_insert, Finset.image_singleton]
  moving_target_ne_first := shift.moving_target_ne_first
  moving_target_ne_second := shift.moving_target_ne_second
  first_target_ne_second := shift.first_target_ne_second
  index_sum := by
    rw [branchSwapIncident_index, branchSwapIncident_index, branchSwapIncident_index,
      branchSwap_blockCard input root hRoot permutation hFix swappedInput]
    exact shift.index_sum
  moving_lt := by
    rw [branchSwapIncident_index,
      branchSwap_blockCard input root hRoot permutation hFix swappedInput]
    exact shift.moving_lt
  two_le_moving := by
    rw [branchSwapIncident_index]
    exact shift.two_le_moving
  extra := (exists_transferSheet swappedInput _
    (branchSwap_moving_lt input shift root hRoot permutation hFix swappedInput)).choose
  extra_wall_rel := (exists_transferSheet swappedInput _
    (branchSwap_moving_lt input shift root hRoot permutation hFix
      swappedInput)).choose_spec.1
  extra_separate := (exists_transferSheet swappedInput _
    (branchSwap_moving_lt input shift root hRoot permutation hFix
      swappedInput)).choose_spec.2

theorem branchSwapProfile_movingTarget (input : W3SourceInput data star)
    (shift : ShiftProfile input) (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (swappedInput : W3SourceInput (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply star) :
    (branchSwapProfile input shift root hRoot permutation hFix
      swappedInput).movingTarget = shift.movingTarget := rfl

theorem branchSwapProfile_firstTarget (input : W3SourceInput data star)
    (shift : ShiftProfile input) (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (swappedInput : W3SourceInput (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply star) :
    (branchSwapProfile input shift root hRoot permutation hFix
      swappedInput).firstTarget = shift.firstTarget := rfl

theorem branchSwapProfile_secondTarget (input : W3SourceInput data star)
    (shift : ShiftProfile input) (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (swappedInput : W3SourceInput (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply star) :
    (branchSwapProfile input shift root hRoot permutation hFix
      swappedInput).secondTarget = shift.secondTarget := rfl

theorem branchSwapProfile_movingAnchor (input : W3SourceInput data star)
    (shift : ShiftProfile input) (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (swappedInput : W3SourceInput (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply star) :
    (branchSwapProfile input shift root hRoot permutation hFix
        swappedInput).movingAnchor =
      (branchSwapOfPerm data wall root hRoot permutation hFix).edgePermutation
        shift.movingTarget shift.movingAnchor := rfl

theorem branchSwapProfile_firstAnchor (input : W3SourceInput data star)
    (shift : ShiftProfile input) (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (swappedInput : W3SourceInput (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply star) :
    (branchSwapProfile input shift root hRoot permutation hFix
        swappedInput).firstAnchor =
      (branchSwapOfPerm data wall root hRoot permutation hFix).edgePermutation
        shift.firstTarget shift.firstAnchor := rfl

theorem branchSwapProfile_secondAnchor (input : W3SourceInput data star)
    (shift : ShiftProfile input) (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (swappedInput : W3SourceInput (branchSwapOfPerm data wall root hRoot permutation
      hFix).apply star) :
    (branchSwapProfile input shift root hRoot permutation hFix
        swappedInput).secondAnchor =
      (branchSwapOfPerm data wall root hRoot permutation hFix).edgePermutation
        shift.secondTarget shift.secondAnchor := rfl

/-! ## The two clearing swaps -/

/-- **One branch swap clears a chosen sheet out of one class**, with the
permutation exposed so that `W3FourDisjointness.BranchGauge` -- and hence the
transport of a `ThirdEquation.W3SourceInput` -- is still available.  This is
`W3ShiftShrinkExistence.exists_branchSwap_clearing` in the `branchSwapOfPerm`
form; that theorem returns an anonymous datum, which no source input can be
carried onto. -/
theorem exists_branchSwapPerm_clearing (data : GluingDatum target degree)
    (wall root : target.V) (hRoot : root ≠ wall) (movedTarget : target.edges)
    (anchor movedAnchor chosen : Fin degree)
    (hChosen : (data.vertexPartition wall).Rel anchor chosen)
    (hMovedRel : (data.vertexPartition wall).Rel anchor movedAnchor)
    (hRefines : (data.edgePartition movedTarget).Refines (data.vertexPartition wall))
    (hLt : (data.edgePartition movedTarget).blockCard movedAnchor <
      (data.vertexPartition wall).blockCard anchor)
    (hMoved : TargetBranchRegion.edgeMoved wall root hRoot movedTarget = true) :
    ∃ (permutation : Equiv.Perm (Fin degree))
      (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet),
      ¬((branchSwapOfPerm data wall root hRoot permutation hFix).apply.edgePartition
        movedTarget).Rel (permutation movedAnchor) chosen := by
  classical
  obtain ⟨free, hFreeMem, hAvoid⟩ := W3ShiftShrinkExistence.exists_swap_avoiding
    ((data.vertexPartition wall).block anchor)
    ((data.edgePartition movedTarget).block movedAnchor)
    (block_subset_wallBlock data wall movedTarget anchor movedAnchor hRefines hMovedRel)
    hLt chosen
  have hFreeRel : (data.vertexPartition wall).Rel anchor free :=
    ((data.vertexPartition wall).mem_block_iff anchor free).mp hFreeMem
  have hFix := (data.vertexPartition wall).swap_apply_rel_self_of_rel
    (hChosen.symm.trans hFreeRel)
  refine ⟨Equiv.swap chosen free, hFix, ?_⟩
  rw [branchSwapOfPerm_edgePartition_of_moved data wall root hRoot _ hFix movedTarget
    hMoved]
  intro hRel
  have hMem : chosen ∈
      ((data.edgePartition movedTarget).relabel (Equiv.swap chosen free)).block
        ((Equiv.swap chosen free) movedAnchor) :=
    (((data.edgePartition movedTarget).relabel
      (Equiv.swap chosen free)).mem_block_iff _ _).mpr hRel
  rw [(data.edgePartition movedTarget).relabel_block (Equiv.swap chosen free)
    movedAnchor] at hMem
  exact hAvoid hMem

/-! ## The clearing swaps at a finer endpoint partition -/

/-- **The clearing swap chosen inside a block of a finer endpoint partition.**

`exists_branchSwapPerm_clearing` returns a permutation preserving the blocks of
the wall partition `A₀`.  Relabelling the **incoming** datum one level up --
which is what `W3ShiftIncomingTransport.EndsCompatible` asks for -- needs the
blocks of an *endpoint* partition preserved instead, and `vp a` is strictly
finer than the merged `A₀` whenever the contracted occurrence's fibre is not a
single class.  This is the same proof, run against `endpoint.block anchor`
rather than `(data.vertexPartition wall).block anchor`; the arithmetic input is
correspondingly `k < endpoint.blockCard anchor` in place of `k < |A₀|`, and the
wall-level `hFix` the branch swap itself consumes is recovered from
`hEndpointRefines`. -/
theorem exists_branchSwapPerm_clearing_endpoint (data : GluingDatum target degree)
    (wall root : target.V) (hRoot : root ≠ wall) (movedTarget : target.edges)
    (anchor movedAnchor chosen : Fin degree)
    (endpoint : SheetPartition degree)
    (hEndpointRefines : endpoint.Refines (data.vertexPartition wall))
    (hChosen : endpoint.Rel anchor chosen)
    (hMovedRel : endpoint.Rel anchor movedAnchor)
    (hRefines : (data.edgePartition movedTarget).Refines endpoint)
    (hLt : (data.edgePartition movedTarget).blockCard movedAnchor <
      endpoint.blockCard anchor)
    (hMoved : TargetBranchRegion.edgeMoved wall root hRoot movedTarget = true) :
    ∃ (permutation : Equiv.Perm (Fin degree))
      (hFixEnd : ∀ sheet, endpoint.Rel (permutation sheet) sheet),
      ¬((branchSwapOfPerm data wall root hRoot permutation
          (fun sheet ↦ hEndpointRefines.rel (hFixEnd sheet))).apply.edgePartition
        movedTarget).Rel (permutation movedAnchor) chosen := by
  classical
  obtain ⟨free, hFreeMem, hAvoid⟩ := W3ShiftShrinkExistence.exists_swap_avoiding
    (endpoint.block anchor)
    ((data.edgePartition movedTarget).block movedAnchor)
    (fun sheet hSheet ↦ (endpoint.mem_block_iff anchor sheet).mpr
      (hMovedRel.trans (hRefines.rel
        (((data.edgePartition movedTarget).mem_block_iff movedAnchor sheet).mp hSheet))))
    hLt chosen
  have hFreeRel : endpoint.Rel anchor free :=
    (endpoint.mem_block_iff anchor free).mp hFreeMem
  have hFixEnd := endpoint.swap_apply_rel_self_of_rel (hChosen.symm.trans hFreeRel)
  refine ⟨Equiv.swap chosen free, hFixEnd, ?_⟩
  rw [branchSwapOfPerm_edgePartition_of_moved data wall root hRoot _ _ movedTarget
    hMoved]
  intro hRel
  have hMem : chosen ∈
      ((data.edgePartition movedTarget).relabel (Equiv.swap chosen free)).block
        ((Equiv.swap chosen free) movedAnchor) :=
    (((data.edgePartition movedTarget).relabel
      (Equiv.swap chosen free)).mem_block_iff _ _).mpr hRel
  rw [(data.edgePartition movedTarget).relabel_block (Equiv.swap chosen free)
    movedAnchor] at hMem
  exact hAvoid hMem

/-- **What a branch swap leaves intact on a shift datum.**  Everything
Figure 29's two members read off the wall: validity, the wall block, the source
genus, the three surviving directions, the moving anchor, the moving class as a
term, and all three source indices.  `W3FourDisjointness.BranchGauge` is the
datum-level half; `branchSwapProfile` is the profile-level half. -/
structure GaugeCopy {data : GluingDatum target degree} {star : ThreeStar target wall}
    (input : W3SourceInput data star) (shift : ShiftProfile input)
    {gaugeData : GluingDatum target degree}
    (gaugeInput : W3SourceInput gaugeData star)
    (gaugeShift : ShiftProfile gaugeInput) : Prop where
  /-- The copy is valid whenever the incoming datum is. -/
  valid_of_old : data.Valid → gaugeData.Valid
  /-- `A₀` is the same partition, as a term. -/
  wallPartition : gaugeData.vertexPartition wall = data.vertexPartition wall
  /-- The quotient-source genus is unchanged. -/
  sourceGenus : genus gaugeData.sourceGraph = genus data.sourceGraph
  /-- The moving direction `t_α` is the same target edge. -/
  movingTarget : gaugeShift.movingTarget = shift.movingTarget
  /-- The first retained direction `t_β` is the same target edge. -/
  firstTarget : gaugeShift.firstTarget = shift.firstTarget
  /-- The second retained direction `t_γ` is the same target edge. -/
  secondTarget : gaugeShift.secondTarget = shift.secondTarget
  /-- The moving anchor is the same sheet. -/
  movingAnchor : gaugeShift.movingAnchor = shift.movingAnchor
  /-- `eₐ` is the same partition, as a term. -/
  movingEdge : gaugeData.edgePartition shift.movingTarget =
    data.edgePartition shift.movingTarget
  /-- `k_α` is unchanged. -/
  movingIndex : gaugeData.sourceEdgeIndex gaugeShift.moving.1 =
    data.sourceEdgeIndex shift.moving.1
  /-- `k_β` is unchanged. -/
  firstIndex : gaugeData.sourceEdgeIndex gaugeShift.firstRest.1 =
    data.sourceEdgeIndex shift.firstRest.1
  /-- `k_γ` is unchanged. -/
  secondIndex : gaugeData.sourceEdgeIndex gaugeShift.secondRest.1 =
    data.sourceEdgeIndex shift.secondRest.1

/-- **One gauge step on the first retained direction.**  A single branch swap
along the branch through `t_β` -- rooted at that occurrence's far endpoint, so
that `TargetSeparation` discharges all three branch flags from
`graph_connected target` and `genus target = 0` -- carries `e_β` off the moving
anchor and leaves `A₀`, `eₐ`, `e_γ` and every index alone. -/
theorem exists_gaugeCopy_clear_first (input : W3SourceInput data star)
    (shift : ShiftProfile input)
    (hLt : data.sourceEdgeIndex shift.firstRest.1 <
      (data.vertexPartition wall).blockCard shift.movingAnchor)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ∃ (gaugeData : GluingDatum target degree) (gaugeInput : W3SourceInput gaugeData star)
      (gaugeShift : ShiftProfile gaugeInput),
      GaugeCopy input shift gaugeInput gaugeShift ∧
      gaugeData.edgePartition shift.secondTarget =
        data.edgePartition shift.secondTarget ∧
      gaugeShift.secondAnchor = shift.secondAnchor ∧
      ¬(gaugeData.edgePartition gaugeShift.firstTarget).Rel gaugeShift.firstAnchor
        gaugeShift.movingAnchor := by
  classical
  have hMovingAt := mem_incidentEdges_ends shift.movingTarget_mem
  have hFirstAt := mem_incidentEdges_ends shift.firstTarget_mem
  have hSecondAt := mem_incidentEdges_ends shift.secondTarget_mem
  have hMovingFixed := TargetSeparation.edgeMoved_eq_false hConnected hGenus hFirstAt
    hMovingAt (Ne.symm shift.moving_target_ne_first)
  have hSecondFixed := TargetSeparation.edgeMoved_eq_false hConnected hGenus hFirstAt
    hSecondAt shift.first_target_ne_second
  obtain ⟨permutation, hFix, hClear⟩ := exists_branchSwapPerm_clearing data wall
    (TargetSeparation.farEndpoint wall shift.firstTarget)
    (TargetSeparation.farEndpoint_ne hFirstAt) shift.firstTarget shift.movingAnchor
    shift.firstAnchor shift.movingAnchor rfl
    (shift.movingAnchor_wall_rel.symm.trans shift.firstAnchor_wall_rel)
    (refines_of_mem_incidentEdges data shift.firstTarget_mem) hLt
    (TargetSeparation.edgeMoved_self_eq_true hFirstAt)
  refine ⟨_,
    branchSwapInput input (TargetSeparation.farEndpoint wall shift.firstTarget)
      (TargetSeparation.farEndpoint_ne hFirstAt) permutation hFix,
    branchSwapProfile input shift (TargetSeparation.farEndpoint wall shift.firstTarget)
      (TargetSeparation.farEndpoint_ne hFirstAt) permutation hFix _,
    ⟨(branchSwapOfPerm_branchGauge data wall _ _ permutation hFix).valid,
      branchSwapOfPerm_vertexPartition_wall data wall _ _ permutation hFix,
      branchSwap_sourceGenus _ _ permutation hFix, rfl, rfl, rfl, ?_,
      branchSwapOfPerm_edgePartition_of_fixed data wall _ _ permutation hFix
        shift.movingTarget hMovingFixed,
      branchSwapIncident_index _ _ permutation hFix _ _ _ shift.moving,
      branchSwapIncident_index _ _ permutation hFix _ _ _ shift.firstRest,
      branchSwapIncident_index _ _ permutation hFix _ _ _ shift.secondRest⟩,
    branchSwapOfPerm_edgePartition_of_fixed data wall _ _ permutation hFix
      shift.secondTarget hSecondFixed, ?_, ?_⟩
  · rw [branchSwapProfile_movingAnchor, branchSwap_edgePermutation_of_fixed _ _
      permutation hFix shift.movingTarget hMovingFixed]
    rfl
  · rw [branchSwapProfile_secondAnchor, branchSwap_edgePermutation_of_fixed _ _
      permutation hFix shift.secondTarget hSecondFixed]
    rfl
  · rw [branchSwapProfile_firstAnchor, branchSwap_edgePermutation_of_moved _ _
      permutation hFix shift.firstTarget
      (TargetSeparation.edgeMoved_self_eq_true hFirstAt),
      branchSwapProfile_movingAnchor, branchSwap_edgePermutation_of_fixed _ _
      permutation hFix shift.movingTarget hMovingFixed]
    exact hClear

/-! ### The same two gauge steps, preserving a finer endpoint partition -/

/-- The wall datum after one clearing branch swap along the branch through a
chosen incident direction, the permutation preserving a finer endpoint
partition.  Naming it lets the endpoint variants below **expose the
permutation**, which is what a relabelling of the incoming datum one level up
needs (`W3ShiftIncomingTransport.branchRelabel`). -/
noncomputable def clearData (data : GluingDatum target degree)
    (direction : target.edges) (hDirection : direction ∈ GluingDatum.incidentEdges wall)
    (endpoint : SheetPartition degree)
    (hEndpointRefines : endpoint.Refines (data.vertexPartition wall))
    (permutation : Equiv.Perm (Fin degree))
    (hFixEnd : ∀ sheet, endpoint.Rel (permutation sheet) sheet) :
    GluingDatum target degree :=
  (branchSwapOfPerm data wall (TargetSeparation.farEndpoint wall direction)
    (TargetSeparation.farEndpoint_ne (mem_incidentEdges_ends hDirection))
    permutation (fun sheet ↦ hEndpointRefines.rel (hFixEnd sheet))).apply

theorem clearData_vertexPartition_wall (data : GluingDatum target degree)
    (direction : target.edges) (hDirection : direction ∈ GluingDatum.incidentEdges wall)
    (endpoint : SheetPartition degree)
    (hEndpointRefines : endpoint.Refines (data.vertexPartition wall))
    (permutation : Equiv.Perm (Fin degree))
    (hFixEnd : ∀ sheet, endpoint.Rel (permutation sheet) sheet) :
    (clearData data direction hDirection endpoint hEndpointRefines permutation
        hFixEnd).vertexPartition wall = data.vertexPartition wall :=
  branchSwapOfPerm_vertexPartition_wall data wall _ _ permutation _

/-- The endpoint partition still refines the wall partition of the cleared
datum, since the branch swap leaves `A₀` alone as a term. -/
theorem refines_clearData_wall (data : GluingDatum target degree)
    (direction : target.edges) (hDirection : direction ∈ GluingDatum.incidentEdges wall)
    (endpoint : SheetPartition degree)
    (hEndpointRefines : endpoint.Refines (data.vertexPartition wall))
    (permutation : Equiv.Perm (Fin degree))
    (hFixEnd : ∀ sheet, endpoint.Rel (permutation sheet) sheet) :
    endpoint.Refines ((clearData data direction hDirection endpoint hEndpointRefines
      permutation hFixEnd).vertexPartition wall) := by
  rw [clearData_vertexPartition_wall]
  exact hEndpointRefines

/-- **One endpoint-preserving gauge step on the first retained direction.**
`exists_gaugeCopy_clear_first` with `exists_branchSwapPerm_clearing_endpoint` in
place of `exists_branchSwapPerm_clearing`: the same single branch swap
through `t_β`, with the permutation and its endpoint-level fixing property
threaded out, and with the arithmetic read in the endpoint partition
(`k_β < endpoint.blockCard movingAnchor`) rather than against `|A₀|`. -/
theorem exists_gaugeCopy_clear_first_endpoint (input : W3SourceInput data star)
    (shift : ShiftProfile input) (endpoint : SheetPartition degree)
    (hEndpointRefines : endpoint.Refines (data.vertexPartition wall))
    (hFirstRefines : (data.edgePartition shift.firstTarget).Refines endpoint)
    (hFirstRel : endpoint.Rel shift.movingAnchor shift.firstAnchor)
    (hLt : data.sourceEdgeIndex shift.firstRest.1 <
      endpoint.blockCard shift.movingAnchor)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ∃ (permutation : Equiv.Perm (Fin degree))
      (hFixEnd : ∀ sheet, endpoint.Rel (permutation sheet) sheet)
      (gaugeInput : W3SourceInput (clearData data shift.firstTarget
        shift.firstTarget_mem endpoint hEndpointRefines permutation hFixEnd) star)
      (gaugeShift : ShiftProfile gaugeInput),
      GaugeCopy input shift gaugeInput gaugeShift ∧
      (clearData data shift.firstTarget shift.firstTarget_mem endpoint
          hEndpointRefines permutation hFixEnd).edgePartition shift.secondTarget =
        data.edgePartition shift.secondTarget ∧
      gaugeShift.secondAnchor = shift.secondAnchor ∧
      ¬((clearData data shift.firstTarget shift.firstTarget_mem endpoint
          hEndpointRefines permutation hFixEnd).edgePartition
        gaugeShift.firstTarget).Rel gaugeShift.firstAnchor gaugeShift.movingAnchor := by
  classical
  have hMovingAt := mem_incidentEdges_ends shift.movingTarget_mem
  have hFirstAt := mem_incidentEdges_ends shift.firstTarget_mem
  have hSecondAt := mem_incidentEdges_ends shift.secondTarget_mem
  have hMovingFixed := TargetSeparation.edgeMoved_eq_false hConnected hGenus hFirstAt
    hMovingAt (Ne.symm shift.moving_target_ne_first)
  have hSecondFixed := TargetSeparation.edgeMoved_eq_false hConnected hGenus hFirstAt
    hSecondAt shift.first_target_ne_second
  obtain ⟨permutation, hFixEnd, hClear⟩ := exists_branchSwapPerm_clearing_endpoint data
    wall (TargetSeparation.farEndpoint wall shift.firstTarget)
    (TargetSeparation.farEndpoint_ne hFirstAt) shift.firstTarget shift.movingAnchor
    shift.firstAnchor shift.movingAnchor endpoint hEndpointRefines rfl hFirstRel
    hFirstRefines hLt (TargetSeparation.edgeMoved_self_eq_true hFirstAt)
  refine ⟨permutation, hFixEnd,
    branchSwapInput input (TargetSeparation.farEndpoint wall shift.firstTarget)
      (TargetSeparation.farEndpoint_ne hFirstAt) permutation _,
    branchSwapProfile input shift (TargetSeparation.farEndpoint wall shift.firstTarget)
      (TargetSeparation.farEndpoint_ne hFirstAt) permutation _ _,
    ⟨(branchSwapOfPerm_branchGauge data wall _ _ permutation _).valid,
      branchSwapOfPerm_vertexPartition_wall data wall _ _ permutation _,
      branchSwap_sourceGenus _ _ permutation _, rfl, rfl, rfl, ?_,
      branchSwapOfPerm_edgePartition_of_fixed data wall _ _ permutation _
        shift.movingTarget hMovingFixed,
      branchSwapIncident_index _ _ permutation _ _ _ _ shift.moving,
      branchSwapIncident_index _ _ permutation _ _ _ _ shift.firstRest,
      branchSwapIncident_index _ _ permutation _ _ _ _ shift.secondRest⟩,
    branchSwapOfPerm_edgePartition_of_fixed data wall _ _ permutation _
      shift.secondTarget hSecondFixed, ?_, ?_⟩
  · rw [branchSwapProfile_movingAnchor, branchSwap_edgePermutation_of_fixed _ _
      permutation _ shift.movingTarget hMovingFixed]
    rfl
  · rw [branchSwapProfile_secondAnchor, branchSwap_edgePermutation_of_fixed _ _
      permutation _ shift.secondTarget hSecondFixed]
    rfl
  · rw [branchSwapProfile_firstAnchor, branchSwap_edgePermutation_of_moved _ _
      permutation _ shift.firstTarget
      (TargetSeparation.edgeMoved_self_eq_true hFirstAt),
      branchSwapProfile_movingAnchor, branchSwap_edgePermutation_of_fixed _ _
      permutation _ shift.movingTarget hMovingFixed]
    exact hClear

/-- **One gauge step on the second retained direction.**  The mirror of
`exists_gaugeCopy_clear_first`, along the branch through `t_γ`. -/
theorem exists_gaugeCopy_clear_second (input : W3SourceInput data star)
    (shift : ShiftProfile input)
    (hLt : data.sourceEdgeIndex shift.secondRest.1 <
      (data.vertexPartition wall).blockCard shift.movingAnchor)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ∃ (gaugeData : GluingDatum target degree) (gaugeInput : W3SourceInput gaugeData star)
      (gaugeShift : ShiftProfile gaugeInput),
      GaugeCopy input shift gaugeInput gaugeShift ∧
      gaugeData.edgePartition shift.firstTarget = data.edgePartition shift.firstTarget ∧
      gaugeShift.firstAnchor = shift.firstAnchor ∧
      ¬(gaugeData.edgePartition gaugeShift.secondTarget).Rel gaugeShift.secondAnchor
        gaugeShift.movingAnchor := by
  classical
  have hMovingAt := mem_incidentEdges_ends shift.movingTarget_mem
  have hFirstAt := mem_incidentEdges_ends shift.firstTarget_mem
  have hSecondAt := mem_incidentEdges_ends shift.secondTarget_mem
  have hMovingFixed := TargetSeparation.edgeMoved_eq_false hConnected hGenus hSecondAt
    hMovingAt (Ne.symm shift.moving_target_ne_second)
  have hFirstFixed := TargetSeparation.edgeMoved_eq_false hConnected hGenus hSecondAt
    hFirstAt (Ne.symm shift.first_target_ne_second)
  obtain ⟨permutation, hFix, hClear⟩ := exists_branchSwapPerm_clearing data wall
    (TargetSeparation.farEndpoint wall shift.secondTarget)
    (TargetSeparation.farEndpoint_ne hSecondAt) shift.secondTarget shift.movingAnchor
    shift.secondAnchor shift.movingAnchor rfl
    (shift.movingAnchor_wall_rel.symm.trans shift.secondAnchor_wall_rel)
    (refines_of_mem_incidentEdges data shift.secondTarget_mem) hLt
    (TargetSeparation.edgeMoved_self_eq_true hSecondAt)
  refine ⟨_,
    branchSwapInput input (TargetSeparation.farEndpoint wall shift.secondTarget)
      (TargetSeparation.farEndpoint_ne hSecondAt) permutation hFix,
    branchSwapProfile input shift (TargetSeparation.farEndpoint wall shift.secondTarget)
      (TargetSeparation.farEndpoint_ne hSecondAt) permutation hFix _,
    ⟨(branchSwapOfPerm_branchGauge data wall _ _ permutation hFix).valid,
      branchSwapOfPerm_vertexPartition_wall data wall _ _ permutation hFix,
      branchSwap_sourceGenus _ _ permutation hFix, rfl, rfl, rfl, ?_,
      branchSwapOfPerm_edgePartition_of_fixed data wall _ _ permutation hFix
        shift.movingTarget hMovingFixed,
      branchSwapIncident_index _ _ permutation hFix _ _ _ shift.moving,
      branchSwapIncident_index _ _ permutation hFix _ _ _ shift.firstRest,
      branchSwapIncident_index _ _ permutation hFix _ _ _ shift.secondRest⟩,
    branchSwapOfPerm_edgePartition_of_fixed data wall _ _ permutation hFix
      shift.firstTarget hFirstFixed, ?_, ?_⟩
  · rw [branchSwapProfile_movingAnchor, branchSwap_edgePermutation_of_fixed _ _
      permutation hFix shift.movingTarget hMovingFixed]
    rfl
  · rw [branchSwapProfile_firstAnchor, branchSwap_edgePermutation_of_fixed _ _
      permutation hFix shift.firstTarget hFirstFixed]
    rfl
  · rw [branchSwapProfile_secondAnchor, branchSwap_edgePermutation_of_moved _ _
      permutation hFix shift.secondTarget
      (TargetSeparation.edgeMoved_self_eq_true hSecondAt),
      branchSwapProfile_movingAnchor, branchSwap_edgePermutation_of_fixed _ _
      permutation hFix shift.movingTarget hMovingFixed]
    exact hClear

/-- **One endpoint-preserving gauge step on the second retained direction.**
The mirror of `exists_gaugeCopy_clear_first_endpoint`, along the branch through
`t_γ`. -/
theorem exists_gaugeCopy_clear_second_endpoint (input : W3SourceInput data star)
    (shift : ShiftProfile input) (direction : target.edges)
    (hDirection : direction ∈ GluingDatum.incidentEdges wall)
    (hDir : shift.secondTarget = direction) (endpoint : SheetPartition degree)
    (hEndpointRefines : endpoint.Refines (data.vertexPartition wall))
    (hSecondRefines : (data.edgePartition shift.secondTarget).Refines endpoint)
    (hSecondRel : endpoint.Rel shift.movingAnchor shift.secondAnchor)
    (hLt : data.sourceEdgeIndex shift.secondRest.1 <
      endpoint.blockCard shift.movingAnchor)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ∃ (permutation : Equiv.Perm (Fin degree))
      (hFixEnd : ∀ sheet, endpoint.Rel (permutation sheet) sheet)
      (gaugeInput : W3SourceInput (clearData data direction hDirection endpoint
        hEndpointRefines permutation hFixEnd) star)
      (gaugeShift : ShiftProfile gaugeInput),
      GaugeCopy input shift gaugeInput gaugeShift ∧
      (clearData data direction hDirection endpoint
          hEndpointRefines permutation hFixEnd).edgePartition shift.firstTarget =
        data.edgePartition shift.firstTarget ∧
      gaugeShift.firstAnchor = shift.firstAnchor ∧
      ¬((clearData data direction hDirection endpoint
          hEndpointRefines permutation hFixEnd).edgePartition
        gaugeShift.secondTarget).Rel gaugeShift.secondAnchor gaugeShift.movingAnchor := by
  classical
  subst hDir
  have hMovingAt := mem_incidentEdges_ends shift.movingTarget_mem
  have hFirstAt := mem_incidentEdges_ends shift.firstTarget_mem
  have hSecondAt := mem_incidentEdges_ends shift.secondTarget_mem
  have hMovingFixed := TargetSeparation.edgeMoved_eq_false hConnected hGenus hSecondAt
    hMovingAt (Ne.symm shift.moving_target_ne_second)
  have hFirstFixed := TargetSeparation.edgeMoved_eq_false hConnected hGenus hSecondAt
    hFirstAt (Ne.symm shift.first_target_ne_second)
  obtain ⟨permutation, hFixEnd, hClear⟩ := exists_branchSwapPerm_clearing_endpoint data
    wall (TargetSeparation.farEndpoint wall shift.secondTarget)
    (TargetSeparation.farEndpoint_ne hSecondAt) shift.secondTarget shift.movingAnchor
    shift.secondAnchor shift.movingAnchor endpoint hEndpointRefines rfl hSecondRel
    hSecondRefines hLt (TargetSeparation.edgeMoved_self_eq_true hSecondAt)
  refine ⟨permutation, hFixEnd,
    branchSwapInput input (TargetSeparation.farEndpoint wall shift.secondTarget)
      (TargetSeparation.farEndpoint_ne hSecondAt) permutation _,
    branchSwapProfile input shift (TargetSeparation.farEndpoint wall shift.secondTarget)
      (TargetSeparation.farEndpoint_ne hSecondAt) permutation _ _,
    ⟨(branchSwapOfPerm_branchGauge data wall _ _ permutation _).valid,
      branchSwapOfPerm_vertexPartition_wall data wall _ _ permutation _,
      branchSwap_sourceGenus _ _ permutation _, rfl, rfl, rfl, ?_,
      branchSwapOfPerm_edgePartition_of_fixed data wall _ _ permutation _
        shift.movingTarget hMovingFixed,
      branchSwapIncident_index _ _ permutation _ _ _ _ shift.moving,
      branchSwapIncident_index _ _ permutation _ _ _ _ shift.firstRest,
      branchSwapIncident_index _ _ permutation _ _ _ _ shift.secondRest⟩,
    branchSwapOfPerm_edgePartition_of_fixed data wall _ _ permutation _
      shift.firstTarget hFirstFixed, ?_, ?_⟩
  · rw [branchSwapProfile_movingAnchor, branchSwap_edgePermutation_of_fixed _ _
      permutation _ shift.movingTarget hMovingFixed]
    rfl
  · rw [branchSwapProfile_firstAnchor, branchSwap_edgePermutation_of_fixed _ _
      permutation _ shift.firstTarget hFirstFixed]
    rfl
  · rw [branchSwapProfile_secondAnchor, branchSwap_edgePermutation_of_moved _ _
      permutation _ shift.secondTarget
      (TargetSeparation.edgeMoved_self_eq_true hSecondAt),
      branchSwapProfile_movingAnchor, branchSwap_edgePermutation_of_fixed _ _
      permutation _ shift.movingTarget hMovingFixed]
    exact hClear

/-- The wall block's cardinality `|A₀|`, read at the moving anchor. -/
theorem shift_blockCard_movingAnchor (input : W3SourceInput data star)
    (shift : ShiftProfile input) :
    (data.vertexPartition wall).blockCard shift.movingAnchor =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 :=
  (SheetPartition.blockCard_congr _ shift.movingAnchor_wall_rel).symm

/-- The case hypothesis `|A₀| > k₄`, read on one orientation: both
retained classes are proper subsets of the wall block. -/
def RetainedBelow {input : W3SourceInput data star} (shift : ShiftProfile input) :
    Prop :=
  data.sourceEdgeIndex shift.firstRest.1 <
      (data.vertexPartition wall).blockCard shift.movingAnchor ∧
    data.sourceEdgeIndex shift.secondRest.1 <
      (data.vertexPartition wall).blockCard shift.movingAnchor

/-- **All three of Figure 29's orientations satisfy the case hypothesis.**  The
only input is `|A₀| > k₄` at the profile's *largest* survivor, which is exactly
the `{w3-r1-nd3-t2-(a>k₄)}` selector; `W3R1SourceProfile.Nd3Profile.first_le`
and `second_le` do the rest.  Nothing is assumed per direction. -/
theorem retainedBelow_of_largest_lt {input : W3SourceInput data star}
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_lt : data.sourceEdgeIndex profile.largest.1 <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    RetainedBelow (shiftProfileLargest profile directions largest_lt) ∧
      RetainedBelow (shiftProfileFirst profile directions largest_lt) ∧
      RetainedBelow (shiftProfileSecond profile directions largest_lt) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;>
    rw [shift_blockCard_movingAnchor]
  · exact lt_of_le_of_lt profile.first_le largest_lt
  · exact lt_of_le_of_lt profile.second_le largest_lt
  · exact lt_of_le_of_lt profile.second_le largest_lt
  · exact largest_lt
  · exact lt_of_le_of_lt profile.first_le largest_lt
  · exact largest_lt

/-- **The shrink sheet, in the form Figure 29's shrink member consumes.**  Two
branch swaps -- one through `t_β`, one through `t_γ` -- produce a gauge copy of
the whole shift datum on which Position II.b's sheet is available in the moving
direction.  Each swap fixes the other two directions, so the first clearing
survives the second.  The only arithmetic consumed is `k_β, k_γ < |A₀|`. -/
theorem exists_gaugeCopy_shrinkSheet (input : W3SourceInput data star)
    (shift : ShiftProfile input) (hRetained : RetainedBelow shift)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ∃ (gaugeData : GluingDatum target degree) (gaugeInput : W3SourceInput gaugeData star)
      (gaugeShift : ShiftProfile gaugeInput),
      GaugeCopy input shift gaugeInput gaugeShift ∧ HasShrinkSheet gaugeShift := by
  obtain ⟨dataOne, inputOne, shiftOne, copyOne, hSecondEdge, hSecondAnchor,
    hClearFirst⟩ :=
    exists_gaugeCopy_clear_first input shift hRetained.1 hConnected hGenus
  have hLtOne : dataOne.sourceEdgeIndex shiftOne.secondRest.1 <
      (dataOne.vertexPartition wall).blockCard shiftOne.movingAnchor := by
    rw [copyOne.secondIndex, copyOne.movingAnchor, copyOne.wallPartition]
    exact hRetained.2
  obtain ⟨dataTwo, inputTwo, shiftTwo, copyTwo, hFirstEdge, hFirstAnchor,
    hClearSecond⟩ :=
    exists_gaugeCopy_clear_second inputOne shiftOne hLtOne hConnected hGenus
  have hMovingEdge : dataTwo.edgePartition shift.movingTarget =
      data.edgePartition shift.movingTarget := by
    have hStep := copyTwo.movingEdge
    rw [copyOne.movingTarget] at hStep
    exact hStep.trans copyOne.movingEdge
  refine ⟨dataTwo, inputTwo, shiftTwo,
    ⟨fun hValid ↦ copyTwo.valid_of_old (copyOne.valid_of_old hValid),
      copyTwo.wallPartition.trans copyOne.wallPartition,
      copyTwo.sourceGenus.trans copyOne.sourceGenus,
      copyTwo.movingTarget.trans copyOne.movingTarget,
      copyTwo.firstTarget.trans copyOne.firstTarget,
      copyTwo.secondTarget.trans copyOne.secondTarget,
      copyTwo.movingAnchor.trans copyOne.movingAnchor, hMovingEdge,
      copyTwo.movingIndex.trans copyOne.movingIndex,
      copyTwo.firstIndex.trans copyOne.firstIndex,
      copyTwo.secondIndex.trans copyOne.secondIndex⟩,
    shiftTwo.movingAnchor, rfl, ?_, hClearSecond⟩
  rw [copyTwo.firstTarget, hFirstEdge, hFirstAnchor, copyTwo.movingAnchor]
  exact hClearFirst

/-- The wall datum after **both** endpoint-preserving clearing swaps: one
through `t_β`, one through `t_γ`.  The two branches are disjoint, so each swap
fixes the other two directions and the first clearing survives the second. -/
noncomputable def clearPairData {input : W3SourceInput data star}
    (shift : ShiftProfile input) (endpoint : SheetPartition degree)
    (hEndpointRefines : endpoint.Refines (data.vertexPartition wall))
    (permFirst : Equiv.Perm (Fin degree))
    (hFixFirst : ∀ sheet, endpoint.Rel (permFirst sheet) sheet)
    (permSecond : Equiv.Perm (Fin degree))
    (hFixSecond : ∀ sheet, endpoint.Rel (permSecond sheet) sheet) :
    GluingDatum target degree :=
  clearData (clearData data shift.firstTarget shift.firstTarget_mem endpoint
      hEndpointRefines permFirst hFixFirst)
    shift.secondTarget shift.secondTarget_mem endpoint
    (refines_clearData_wall data shift.firstTarget shift.firstTarget_mem endpoint
      hEndpointRefines permFirst hFixFirst) permSecond hFixSecond

/-- **The shrink sheet at a finer endpoint partition.**  `exists_gaugeCopy_shrinkSheet`
with both swaps chosen inside blocks of `endpoint`: the two permutations are
threaded out together with their endpoint-level fixing properties, so that the
same two swaps can be performed one level up on the incoming datum
(`W3ShiftIncomingTransport`).  The arithmetic consumed is
`k_β, k_γ < endpoint.blockCard movingAnchor` -- the endpoint form of
`RetainedBelow`, which in Figure 29's Position II.a is exactly `RetainedBelow`
itself, since the selected-block census puts `A₀` on the trivalent endpoint. -/
theorem exists_gaugeCopy_shrinkSheet_endpoint (input : W3SourceInput data star)
    (shift : ShiftProfile input) (endpoint : SheetPartition degree)
    (hEndpointRefines : endpoint.Refines (data.vertexPartition wall))
    (hFirstRefines : (data.edgePartition shift.firstTarget).Refines endpoint)
    (hSecondRefines : (data.edgePartition shift.secondTarget).Refines endpoint)
    (hFirstRel : endpoint.Rel shift.movingAnchor shift.firstAnchor)
    (hSecondRel : endpoint.Rel shift.movingAnchor shift.secondAnchor)
    (hFirstLt : data.sourceEdgeIndex shift.firstRest.1 <
      endpoint.blockCard shift.movingAnchor)
    (hSecondLt : data.sourceEdgeIndex shift.secondRest.1 <
      endpoint.blockCard shift.movingAnchor)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ∃ (permFirst : Equiv.Perm (Fin degree))
      (hFixFirst : ∀ sheet, endpoint.Rel (permFirst sheet) sheet)
      (permSecond : Equiv.Perm (Fin degree))
      (hFixSecond : ∀ sheet, endpoint.Rel (permSecond sheet) sheet)
      (gaugeInput : W3SourceInput (clearPairData shift endpoint hEndpointRefines
        permFirst hFixFirst permSecond hFixSecond) star)
      (gaugeShift : ShiftProfile gaugeInput),
      GaugeCopy input shift gaugeInput gaugeShift ∧ HasShrinkSheet gaugeShift := by
  obtain ⟨permFirst, hFixFirst, inputOne, shiftOne, copyOne, hSecondEdge, hSecondAnchor,
    hClearFirst⟩ :=
    exists_gaugeCopy_clear_first_endpoint input shift endpoint hEndpointRefines
      hFirstRefines hFirstRel hFirstLt hConnected hGenus
  have hSecondRefines' : ((clearData data shift.firstTarget shift.firstTarget_mem
      endpoint hEndpointRefines permFirst hFixFirst).edgePartition
        shiftOne.secondTarget).Refines endpoint := by
    rw [copyOne.secondTarget, hSecondEdge]
    exact hSecondRefines
  have hSecondRel' : endpoint.Rel shiftOne.movingAnchor shiftOne.secondAnchor := by
    rw [copyOne.movingAnchor, hSecondAnchor]
    exact hSecondRel
  have hLtOne : (clearData data shift.firstTarget shift.firstTarget_mem endpoint
      hEndpointRefines permFirst hFixFirst).sourceEdgeIndex shiftOne.secondRest.1 <
      endpoint.blockCard shiftOne.movingAnchor := by
    rw [copyOne.secondIndex, copyOne.movingAnchor]
    exact hSecondLt
  obtain ⟨permSecond, hFixSecond, inputTwo, shiftTwo, copyTwo, hFirstEdge, hFirstAnchor,
    hClearSecond⟩ :=
    exists_gaugeCopy_clear_second_endpoint inputOne shiftOne shift.secondTarget
      shift.secondTarget_mem copyOne.secondTarget endpoint
      (refines_clearData_wall data shift.firstTarget shift.firstTarget_mem endpoint
        hEndpointRefines permFirst hFixFirst)
      hSecondRefines' hSecondRel' hLtOne hConnected hGenus
  have hMovingEdge : (clearPairData shift endpoint hEndpointRefines permFirst hFixFirst
      permSecond hFixSecond).edgePartition shift.movingTarget =
      data.edgePartition shift.movingTarget := by
    have hStep := copyTwo.movingEdge
    rw [copyOne.movingTarget] at hStep
    exact hStep.trans copyOne.movingEdge
  refine ⟨permFirst, hFixFirst, permSecond, hFixSecond, inputTwo, shiftTwo,
    ⟨fun hValid ↦ copyTwo.valid_of_old (copyOne.valid_of_old hValid),
      copyTwo.wallPartition.trans copyOne.wallPartition,
      copyTwo.sourceGenus.trans copyOne.sourceGenus,
      copyTwo.movingTarget.trans copyOne.movingTarget,
      copyTwo.firstTarget.trans copyOne.firstTarget,
      copyTwo.secondTarget.trans copyOne.secondTarget,
      copyTwo.movingAnchor.trans copyOne.movingAnchor, hMovingEdge,
      copyTwo.movingIndex.trans copyOne.movingIndex,
      copyTwo.firstIndex.trans copyOne.firstIndex,
      copyTwo.secondIndex.trans copyOne.secondIndex⟩,
    shiftTwo.movingAnchor, rfl, ?_, hClearSecond⟩
  have hGoal : ¬((clearData (clearData data shift.firstTarget shift.firstTarget_mem
        endpoint hEndpointRefines permFirst hFixFirst) shift.secondTarget
        shift.secondTarget_mem endpoint
        (refines_clearData_wall data shift.firstTarget shift.firstTarget_mem endpoint
          hEndpointRefines permFirst hFixFirst) permSecond
        hFixSecond).edgePartition shiftTwo.firstTarget).Rel
      shiftTwo.firstAnchor shiftTwo.movingAnchor := by
    rw [copyTwo.firstTarget, hFirstEdge, hFirstAnchor, copyTwo.movingAnchor]
    exact hClearFirst
  exact hGoal

/-! ## Equation (3)'s `(k − 1, k + 1)` pair, unconditionally -/

/-- **The pair, over a gauge copy.**  From a datum of case `{w3-r1-nd3-t2-(a>k₄)}` and any one
of Figure 29's three orientations, a gauge copy of the whole shift datum -- the
gluing datum, its `ThirdEquation.W3SourceInput` and its `ShiftProfile` --
carrying **both** of Equation (3)'s members on the moving direction: the
Position II.b shrink member with new-edge index `k − 1` and the Position II.a
grow member with new-edge index `k + 1`, both valid and both preserving the
*original* datum's source genus, with `A₀` and `eₐ` literally unchanged and the
moving index `k` literally the incoming one.

This is the unconditional form of
`W3ShiftSourceCandidates.exists_shift_pair_of_shrinkSheet`, whose
`HasShrinkSheet` hypothesis is a matter of sheet-labelling gauge and not an
obstruction (see the module docstring).  The two members live over one
copy, so the `GaugeFamily` this feeds has a constant `base`; what makes it a
gauge family rather than a `BalancedGlobal.PresentedFamily` is that the copy is
not `data`. -/
theorem exists_gauge_shift_pair (input : W3SourceInput data star)
    (shift : ShiftProfile input) (hRetained : RetainedBelow shift)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ∃ (gaugeData : GluingDatum target degree) (gaugeInput : W3SourceInput gaugeData star)
      (gaugeShift : ShiftProfile gaugeInput)
      (minusCandidate : BalancedGlobal.Candidate target degree gaugeData wall)
      (remainder : Fin degree),
      (data.Valid → gaugeData.Valid) ∧
      gaugeData.vertexPartition wall = data.vertexPartition wall ∧
      gaugeData.edgePartition shift.movingTarget =
        data.edgePartition shift.movingTarget ∧
      gaugeShift.movingTarget = shift.movingTarget ∧
      gaugeShift.movingAnchor = shift.movingAnchor ∧
      minusCandidate.datum.Valid ∧
      genus minusCandidate.datum.sourceGraph = genus data.sourceGraph ∧
      (minusCandidate.resolution gaugeShift.movingAnchor).newEdge.blockCard remainder +
          1 = data.sourceEdgeIndex shift.moving.1 ∧
      gaugeShift.growCandidate.datum.Valid ∧
      genus gaugeShift.growCandidate.datum.sourceGraph = genus data.sourceGraph ∧
      (gaugeShift.growCandidate.resolution gaugeShift.movingAnchor).newEdge.blockCard
          gaugeShift.movingAnchor = data.sourceEdgeIndex shift.moving.1 + 1 := by
  obtain ⟨gaugeData, gaugeInput, gaugeShift, copy, hSheet⟩ :=
    exists_gaugeCopy_shrinkSheet input shift hRetained hConnected hGenus
  obtain ⟨shrink⟩ := exists_shrinkData gaugeShift hSheet
  obtain ⟨hValidMinus, hGenusMinus, hIndexMinus, hValidPlus, hGenusPlus, hIndexPlus⟩ :=
    shift_pair_valid_genus_index gaugeShift shrink
  exact ⟨gaugeData, gaugeInput, gaugeShift, shrink.shrinkCandidate, shrink.remainder,
    copy.valid_of_old, copy.wallPartition, copy.movingEdge, copy.movingTarget,
    copy.movingAnchor, hValidMinus, hGenusMinus.trans copy.sourceGenus,
    hIndexMinus.trans copy.movingIndex, hValidPlus,
    hGenusPlus.trans copy.sourceGenus,
    hIndexPlus.trans (congrArg (fun index ↦ index + 1) copy.movingIndex)⟩

/-- **The pair, with the gauge copy's two permutations exposed.**
`exists_gauge_shift_pair` run through `exists_gaugeCopy_shrinkSheet_endpoint`:
Equation (3)'s `(k_α − 1, k_α + 1)` pair over the same copy, with both clearing
permutations and their endpoint-level fixing properties threaded out, so that
the identical pair of swaps can be performed one level up on an incoming datum
before the contraction.  Nothing else changes: `A₀`, `e_α`, the moving direction
and the moving anchor are still literally the incoming ones. -/
theorem exists_gauge_shift_pair_endpoint (input : W3SourceInput data star)
    (shift : ShiftProfile input) (endpoint : SheetPartition degree)
    (hEndpointRefines : endpoint.Refines (data.vertexPartition wall))
    (hFirstRefines : (data.edgePartition shift.firstTarget).Refines endpoint)
    (hSecondRefines : (data.edgePartition shift.secondTarget).Refines endpoint)
    (hFirstRel : endpoint.Rel shift.movingAnchor shift.firstAnchor)
    (hSecondRel : endpoint.Rel shift.movingAnchor shift.secondAnchor)
    (hFirstLt : data.sourceEdgeIndex shift.firstRest.1 <
      endpoint.blockCard shift.movingAnchor)
    (hSecondLt : data.sourceEdgeIndex shift.secondRest.1 <
      endpoint.blockCard shift.movingAnchor)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ∃ (permFirst : Equiv.Perm (Fin degree))
      (hFixFirst : ∀ sheet, endpoint.Rel (permFirst sheet) sheet)
      (permSecond : Equiv.Perm (Fin degree))
      (hFixSecond : ∀ sheet, endpoint.Rel (permSecond sheet) sheet)
      (gaugeInput : W3SourceInput (clearPairData shift endpoint hEndpointRefines
        permFirst hFixFirst permSecond hFixSecond) star)
      (gaugeShift : ShiftProfile gaugeInput)
      (minusCandidate : BalancedGlobal.Candidate target degree
        (clearPairData shift endpoint hEndpointRefines permFirst hFixFirst permSecond
          hFixSecond) wall)
      (remainder : Fin degree),
      (data.Valid → (clearPairData shift endpoint hEndpointRefines permFirst hFixFirst
        permSecond hFixSecond).Valid) ∧
      (clearPairData shift endpoint hEndpointRefines permFirst hFixFirst permSecond
        hFixSecond).vertexPartition wall = data.vertexPartition wall ∧
      (clearPairData shift endpoint hEndpointRefines permFirst hFixFirst permSecond
        hFixSecond).edgePartition shift.movingTarget =
        data.edgePartition shift.movingTarget ∧
      gaugeShift.movingTarget = shift.movingTarget ∧
      gaugeShift.movingAnchor = shift.movingAnchor ∧
      minusCandidate.datum.Valid ∧
      genus minusCandidate.datum.sourceGraph = genus data.sourceGraph ∧
      (minusCandidate.resolution gaugeShift.movingAnchor).newEdge.blockCard remainder +
          1 = data.sourceEdgeIndex shift.moving.1 ∧
      gaugeShift.growCandidate.datum.Valid ∧
      genus gaugeShift.growCandidate.datum.sourceGraph = genus data.sourceGraph ∧
      (gaugeShift.growCandidate.resolution gaugeShift.movingAnchor).newEdge.blockCard
          gaugeShift.movingAnchor = data.sourceEdgeIndex shift.moving.1 + 1 := by
  obtain ⟨permFirst, hFixFirst, permSecond, hFixSecond, gaugeInput, gaugeShift, copy,
    hSheet⟩ :=
    exists_gaugeCopy_shrinkSheet_endpoint input shift endpoint hEndpointRefines
      hFirstRefines hSecondRefines hFirstRel hSecondRel hFirstLt hSecondLt hConnected
      hGenus
  obtain ⟨shrink⟩ := exists_shrinkData gaugeShift hSheet
  obtain ⟨hValidMinus, hGenusMinus, hIndexMinus, hValidPlus, hGenusPlus, hIndexPlus⟩ :=
    shift_pair_valid_genus_index gaugeShift shrink
  exact ⟨permFirst, hFixFirst, permSecond, hFixSecond, gaugeInput, gaugeShift,
    shrink.shrinkCandidate, shrink.remainder,
    copy.valid_of_old, copy.wallPartition, copy.movingEdge, copy.movingTarget,
    copy.movingAnchor, hValidMinus, hGenusMinus.trans copy.sourceGenus,
    hIndexMinus.trans copy.movingIndex, hValidPlus,
    hGenusPlus.trans copy.sourceGenus,
    hIndexPlus.trans (congrArg (fun index ↦ index + 1) copy.movingIndex)⟩

/-! ## Equation (3) as a gauge family, and its certified exit -/

/-- `min(k₂,k₃,k₄) ≥ 2` in the rational form the weights need.  The natural-number
statement is `ShiftProfile.two_le_moving`, which
`W3R1SourceProfile.Nd3Profile.indices_two_le_of_largest_lt` derives from
`k₂ + k₃ + k₄ = 2|A₀|` and `|A₀| > k₄`, exactly as Part I does. -/
theorem one_lt_movingIndex {input : W3SourceInput data star}
    (shift : ShiftProfile input) :
    (1 : ℚ) < (data.sourceEdgeIndex shift.moving.1 : ℚ) := by
  have hTwo : (2 : ℚ) ≤ (data.sourceEdgeIndex shift.moving.1 : ℚ) := by
    exact_mod_cast shift.two_le_moving
  linarith

section GaugeExit

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The one thing Equation (3)'s exit is not given here**, isolated as a single
named structure the way `W3FourStableGraph.LimitRows` is for Figure 28: an
honest length-matrix presentation of each of the pair's two members, a wall
column they agree off, and Figure 29's displayed determinants

`c⁽¹⁾ = c(e_α)/(k_α − 1) + σ₀(J₀,α)`,  `c⁽²⁾ = c(e_α)/(k_α + 1) + σ₀(J₀,α)`,

together with the limit's own wall relation `c(e_α)/k_α + σ₀(J₀,α) = 0`
(Figure 29).  No model is supplied for this here; `W3ShiftHonestBalance.limitRows`
supplies one.  It is the limit-matrix half of the case, the analogue of Figure
28's `LimitRows`, and it is stated so that it can be discharged in one place.

`movingIndex` is `k_α` as a rational; `one_lt_movingIndex` above is what a
caller uses for `one_lt_movingIndex'`, and it is derived from the case, not
assumed. -/
structure LimitRows {base : GluingDatum target degree}
    (member : Fin 2 → BalancedGlobal.Candidate target degree base wall)
    (coordinate : Type*) [Fintype coordinate] [DecidableEq coordinate] where
  /-- A length-matrix presentation of each member. -/
  presentation : ∀ i, (member i).datum.LengthMatrixPresentation coordinate
  /-- The column of the collapsing wall occurrence. -/
  wallColumn : coordinate
  /-- `k_α`, the moving direction's index. -/
  movingIndex : ℚ
  /-- `c(e_α)`, the moving class's contribution. -/
  wallContribution : ℚ
  /-- `σ₀(J₀,α)`, the limit's own sum on that direction. -/
  wallSum : ℚ
  /-- `min(k₂,k₃,k₄) ≥ 2`, the source's own bound in this case. -/
  one_lt_movingIndex' : 1 < movingIndex
  /-- The limit's wall relation. -/
  wallRelation : wallContribution / movingIndex + wallSum = 0
  /-- Figure 29's two displayed determinants. -/
  det : ∀ i, (GluingDatum.LengthMatrixPresentation.matrix (presentation i)).det =
    ![wallContribution / (movingIndex - 1) + wallSum,
      wallContribution / (movingIndex + 1) + wallSum] i
  /-- The two members share every column off the wall. -/
  agreeOffWall : ∀ first second,
    AgreeOffColumn
      (GluingDatum.LengthMatrixPresentation.matrix (presentation first))
      (GluingDatum.LengthMatrixPresentation.matrix (presentation second))
      wallColumn

/-- **Equation (3) as a two-member gauge family.**  The shift analogue of
`W3FourClosure.equationTwoGaugeFamily`: one `base` per member -- here the single
gauge copy `exists_gauge_shift_pair` produces, since both members of a pair live
over it -- `valid_of_old` from `W3FourDisjointness.BranchGauge.valid`, one
presentation per member, unit-free weights `(k_α − 1, k_α + 1)`, and
`BalancingRemaining.balance_shift_pair` as the `PositiveBalance`.

**Two members, not six.**  Equation (3) is three independently balancing pairs
and a `PositiveBalance` needs only positive weights summing the
determinants to zero, so the pair on the incoming member's own direction
suffices; every Figure 29 member shifts exactly one direction by `±1`, so the
incoming one lies in that pair, as its `k_α − 1` member if it shrinks and its
`k_α + 1` member if it grows.  The exit below quantifies over `incoming : Fin 2`,
so both alternatives are served; identifying which, and which direction, is the
incoming-member problem and is not solved here. -/
noncomputable def equationThreeGaugeFamily (base : GluingDatum target degree)
    (gauge : data.Valid → base.Valid)
    (member : Fin 2 → BalancedGlobal.Candidate target degree base wall)
    (rows : LimitRows member coordinate) :
    W3FourClosure.GaugeFamily (coordinate := coordinate) 2 data wall where
  base := fun _ ↦ base
  valid_of_old := fun _ ↦ gauge
  candidate := member
  presentation := rows.presentation
  wallColumn := rows.wallColumn
  weight := ![rows.movingIndex - 1, rows.movingIndex + 1]
  positiveBalance := by
    rw [funext rows.det]
    exact BalancingRemaining.balance_shift_pair rows.one_lt_movingIndex'
      rows.wallRelation
  agreeOffWall := rows.agreeOffWall

/-- **The certified exit of Equation (3).**  `W3FourClosure.GaugeFamily`'s positive exit, run
on Equation (3)'s pair: from the incoming member's nonsingular presentation and
a wall-crossing velocity there is an outgoing member of opposite determinant
sign, valid, reached along a segment that stays in the positive cone and
matching the incoming metric, with a cleared pencil at every point of it.  The
nonsingularity gate is the same one as in the four-member case and for the same
reason: `BalancingValencyTwo.PositiveBalance` is a *signed* balance. -/
theorem exists_equationThree_positive_exit (base : GluingDatum target degree)
    (gauge : data.Valid → base.Valid)
    (member : Fin 2 → BalancedGlobal.Candidate target degree base wall)
    (rows : LimitRows member coordinate)
    (hValid : data.Valid) (hTargetConnected : graph_connected target)
    (hTargetGenus : genus target = 0) (root : target.V) (incoming : Fin 2)
    (hincoming : (GluingDatum.LengthMatrixPresentation.matrix
      (rows.presentation incoming)).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin 2 → coordinate → ℚ)
    (hz : z rows.wallColumn = 0) (hzpos : ∀ i, i ≠ rows.wallColumn → 0 < z i)
    (hSystems : ∀ outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        (rows.presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        (rows.presentation incoming)).mulVec incomingVelocity =
      (GluingDatum.LengthMatrixPresentation.matrix
        (rows.presentation outgoing)).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity rows.wallColumn < 0) :
    ∃ outgoing,
      (member outgoing).datum.Valid ∧
      (GluingDatum.LengthMatrixPresentation.matrix (rows.presentation incoming)).det *
        (GluingDatum.LengthMatrixPresentation.matrix
          (rows.presentation outgoing)).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            (rows.presentation outgoing)).mulVec (z + t • outgoingVelocity outgoing) =
          (GluingDatum.LengthMatrixPresentation.matrix
            (rows.presentation incoming)).mulVec z +
            t • (GluingDatum.LengthMatrixPresentation.matrix
              (rows.presentation incoming)).mulVec incomingVelocity ∧
        Nonempty (BalancedGlobal.Candidate.ClearedPencil (member outgoing)
          (rows.presentation outgoing) (z + t • outgoingVelocity outgoing)) :=
  (equationThreeGaugeFamily base gauge member rows).exists_valid_positive_exit_with_pencil
    hValid hTargetConnected hTargetGenus root incoming hincoming z incomingVelocity
    outgoingVelocity hz hzpos hSystems hIncomingDirection

end GaugeExit

end DraismaVargas.LocalCases.W3ShiftClosure
