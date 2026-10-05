module

public import DraismaVargasCount.BallotSpineReversalSheetIso
public import DraismaVargasCount.SlopesGeometric
public import DraismaVargasCount.BranchSharedDirection
public import DraismaVargasCount.LoopAdjacentDiagonal

@[expose] public section

/-!
# The residues of the genus-six exhaustion package, and `hSpine` at every genus

`BallotSpineReversalSheetIso.diagonalClassification_genusSix_of_three_residues`
rests `BallotSlopes.DiagonalClassification 2 request` on three hypotheses:

* `hSep` -- `SpineSingleColumn.LeafAvoidingSeparated`: distinct leaf-avoiding rows
  of an open odd member never meet a common column, so that every open odd
  member's `A_φ` is monomial (which is what `DiagonalFromSeparation` uses it for);
* `hSpine` -- on the non-leaf slots, the core diagonal of a diagonal open odd member
  agrees with the ballot diagonal of a slope sequence;
* `hSupply` -- a diagonal open odd member whose core diagonal is the ballot diagonal
  of `s` has a gluing datum isomorphic to that of the ballot member of `s`.

This module proves `hSpine` **with no hypothesis at all and at every genus**:
`diagonalExtract m request : BallotSlopes.DiagonalExtract m request`, the `extract`
field of `DiagonalClassification`.  It is the geometric content of
`prop-caterpillar-ballot`(1) in Vargas, Part II (arXiv:2609.09109): at every interior
spine vertex the slopes satisfy the step condition `s_{i-1} + s_i = 2 m(B_i) - 1`,
hence `s_i - s_{i-1} = ±1`.

The other two residues are proved elsewhere: `hSep` by
`TrivalentFibreUnique.leafAvoidingSeparated`, and `hSupply` from the sheet-layer
matching (`SheetLayerMatching.sheetLayerSupply`, through
`DiagonalTargetIso.hSupply_of_sheetLayerSupply`).  Here they are checked at the
caterpillar member (§7).

## The ingredients of `hSpine`

`NonTrivalentCorner.corner_eq_reciprocal_of_nonleaf` (a diagonal
non-leaf row is one source occurrence and its entry is `1 / m(e)`),
`SpineRowLengthWitness.exists_loopSlot_of_passesAboveLeaf` (a non-loop row is
leaf-avoiding), `member.ident.incidence` and `fullDim.trivalent` (the three
surviving occurrences at the branch vertex `B` over an interior spine vertex are
the rows of its three slots), `BranchSharedDirection.incidentEdges_card_eq_three_of_branch_of_ne`
+ `SlopesGeometric.localRamification_eq_zero_of_trivalent_target` (`B` is
unramified), `StableLocalProperties.sourceEdgeIndex_le_blockCard` (balancing),
`LoopAdjacentDiagonal.coreDiag_eq_half_of_loopAdjacent` (stem and extreme spine
slots read `1/2`), `SlopesGeometric.slopeStepRel_of_trivalent_unramified` and
`BallotSlopes.exists_ballotCoreDiag_of_values`.  The hypothesis `mem.Diagonal`
supplies, for free, the two things the step condition needs: each row lies over
one column, so `s_i` is defined; and the bridge index `2` at `B_i` (the stem row of a
diagonal member is a single source occurrence, so its index at `B_i` is the
`2` that the loop-adjacent reading gives at the other end).

## The residues at the caterpillar member

All three residues hold at `FibreCaterpillar.caterpillarMember`, proved below
(§7): `hSpine_caterpillarMember` (its slope sequence is the zig-zag),
`leafAvoidingSeparated_caterpillarMember`, `supply_caterpillarMember` (the only
`s` is the zig-zag, and `BallotDatum.ballotDatum_zig` makes the identity the
isomorphism).  Sharper, for `hSep`: `leafAvoidingSeparated_of_diagonal` --
**every diagonal member satisfies `LeafAvoidingSeparated`**, with the
leaf-avoiding hypotheses unused, because in a diagonal member a row meets only
its own column.  So `hSep`'s content lives entirely on the non-diagonal members.

`hSupply` has a target layer and a sheet layer.  For a diagonal member the rows
biject with the target edges (`labelling.targetEdge ∘ slotMap.symm`), each non-loop
row is one occurrence joining the branch vertices of its two core ends (the §4
dictionary here), each loop row the leaf hairpin (`LollipopLeafRow`, `LeafFibre`),
and an edge-bijective, vertex-surjective map from a tree with `6m+4` vertices onto a
tree with `6m+3` edges is an isomorphism, so `T ≅ catTree m`
(`DiagonalTargetIso.targetLayer`).  The sheet layer derives every vertex and edge
partition of the member's **whole** datum, dangling sheets included, and matches it
to `ballotDatum m s` with per-vertex and per-edge permutations
(`SheetLayerCensus`, `SheetLayerMatching`).  A diagonal member's datum does not see
the request, so genericity cannot bear on it.

## What is proved

* §1 `coreDiag_eq_inv_sourceEdgeIndex` -- at a diagonal member, any surviving
  occurrence on the row of a non-leaf slot has index `1 / coreDiag`.
* §2 `spineVertex`, `spineSlot`, `stemSlot`, `coreIncidence_spineVertex`,
  `tail_ne_spineVertex_of_loop` -- the interior spine vertices of `catCore m`
  and their incidences, as arithmetic.
* §3 `survivingIndexSum_eq_sum_incidentEdges`.
* §4 `exists_incident_of_coreIncidence_pos`, `coreIncidence_pos_of_incident`,
  **`exists_slopeStepRel_spineVertex`** -- the step condition at every interior
  spine vertex of every diagonal member.
* §5 `exists_edge_row_eq`, `exists_coreDiag_eq_inv_nat`, `slopeFun`,
  `slopeFun_eq`, `coreDiag_spineSlot_end`,
  **`exists_coreDiag_eq_ballotCoreDiag`**, **`diagonalExtract`** -- the
  `extract` field of `DiagonalClassification`, at every `m`, unconditionally.
* §6 **`hSpine_genusSix`** (the binder shape of the three-residue theorem) and
  `diagonalClassification_genusSix_of_two_residues`.
* §7 `leafAvoidingSeparated_of_diagonal`,
  `leafAvoidingSeparated_caterpillarMember`, `supply_caterpillarMember`,
  `hSpine_caterpillarMember`, and an `example` inhabiting `hSpine`'s antecedent.

## What is NOT proved here (every hypothesis, explicitly)

* **`hSep` is not proved here** for any non-diagonal member, and `hSupply` for no
  member but the caterpillar member.  Both remain hypotheses of
  `diagonalClassification_genusSix_of_two_residues`.
* `diagonalExtract` uses neither `Open` nor `HasOddMult`; it says nothing about
  non-diagonal members (the unrestricted form fails,
  `ColumnTwist.not_forall_extract`).
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no
  `decide`, no `#eval`.
-/

namespace DraismaVargas.Count.BallotResidues

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.EdgeDenominator

variable {m : ℕ} {request : Fin (6 * m + 3) → ℚ}

/-! ## 1.  A diagonal member reads `1 / m(e)` on every non-leaf slot -/

/-- **The reciprocal reading.**  At a diagonal member, a surviving occurrence on
the row of a non-leaf slot of `catCore m` has index `1 / coreDiag`: the row is
supported on its own column, which is not a leaf column (a non-loop row is
leaf-avoiding, `SpineRowLengthWitness.exists_loopSlot_of_passesAboveLeaf`), so
`NonTrivalentCorner.corner_eq_reciprocal_of_nonleaf` makes the row a single
occurrence and the entry its reciprocal index. -/
theorem coreDiag_eq_inv_sourceEdgeIndex (member : FibreMember (catCore m) request (m + 2))
    (hD : member.Diagonal) (edge : NonDanglingEdge member.data)
    (hNotLeaf : ¬ IsLeafEdge m (member.ident.row edge.stablePath)) :
    member.coreDiag (member.ident.row edge.stablePath) =
      1 / (member.data.sourceEdgeIndex edge.1 : ℚ) := by
  classical
  set r := member.fullDim.labelling.row edge.stablePath with hr
  have hmem : edge.1 ∈ rowEdges member.fullDim.labelling r :=
    (mem_rowEdges _ _ _).mpr ⟨edge.2, rfl⟩
  have hSupport : ∀ j, j ≠ r → GluingDatum.LengthMatrixPresentation.matrix
      member.fullDim.labelling.presentation r j = 0 := fun j hj ↦ hD r j hj
  have hTarget : edge.1.1.1 = member.fullDim.labelling.targetEdge r :=
    NonTrivalentCorner.target_eq_of_supported member.fullDim.labelling hSupport hmem
  have hSlot : member.slotMap r = member.ident.row edge.stablePath := by
    rw [FibreMember.slotMap_apply, hr, Equiv.symm_apply_apply]
  have hNonleaf : r ∉ leafColumns member.fullDim.labelling.presentation := by
    intro hcol
    obtain ⟨v, hv, hincid⟩ := (mem_leafColumns _ _).mp hcol
    have hPasses : PassesAboveLeaf member.fullDim.labelling r :=
      ⟨edge.1, hmem, v, hv, by rw [hTarget]; exact hincid⟩
    obtain ⟨slot, hLoop, hEq⟩ :=
      SpineRowLengthWitness.exists_loopSlot_of_passesAboveLeaf member hPasses
    apply hNotLeaf
    have hIs : member.ident.row edge.stablePath = slot := by
      rw [← hSlot, hEq, FibreMember.slotMap_apply, Equiv.symm_apply_apply,
        Equiv.apply_symm_apply]
    rw [hIs]
    exact (LollipopLeafRow.catCore_tail_eq_head_iff m slot).mp hLoop
  obtain ⟨e, _he, hfibre, hval⟩ :=
    NonTrivalentCorner.corner_eq_reciprocal_of_nonleaf member.fullDim hSupport hNonleaf
  have hbf : edge.1 ∈ LeafFibre.rowFibre member.fullDim.labelling r
      (member.fullDim.labelling.targetEdge r) :=
    (EdgeDenominator.mem_rowFibre_iff _ _ _ _).mpr ⟨hmem, hTarget⟩
  rw [hfibre, Finset.mem_singleton] at hbf
  rw [← hSlot]
  show GluingDatum.LengthMatrixPresentation.matrix member.fullDim.labelling.presentation
      (member.slotMap.symm (member.slotMap r)) (member.slotMap.symm (member.slotMap r)) = _
  rw [Equiv.symm_apply_apply, hval, hbf]

/-! ## 2.  The interior spine vertices of `catCore m` -/

section Arith

open DraismaVargas.Count.SlopeRigidity (catCore_tail_val coreIncidence_catCore_val)
open DraismaVargas.Infrastructure.CaterpillarTree (parentIndex)

/-- The interior spine vertex `p_{i+1}` of `catCore m`, for `1 ≤ i ≤ 2m`: the core
vertex `2i - 1`, where the spine slots `3i - 2` and `3i + 1` meet the stem
`3i - 1`. -/
def spineVertex (m i : ℕ) (hi : i ≤ 2 * m) : Fin (4 * m + 2) := ⟨2 * i - 1, by omega⟩

/-- The spine slot `3i - 2` (Part II's `h_i`). -/
def spineSlot (m i : ℕ) (hi : i ≤ 2 * m + 1) : Fin (6 * m + 3) := ⟨3 * i - 2, by omega⟩

/-- The stem slot `3i - 1`. -/
def stemSlot (m i : ℕ) (hi : i ≤ 2 * m) : Fin (6 * m + 3) := ⟨3 * i - 1, by omega⟩

/-- **The incidences at an interior spine vertex.**  The core vertex `2i - 1`
meets exactly the three slots `3i - 2`, `3i - 1`, `3i + 1`, each once. -/
theorem coreIncidence_spineVertex (m i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ 2 * m)
    (t : Fin (6 * m + 3)) :
    coreIncidence (catCore m) (spineVertex m i hi2) t =
      if t.val = 3 * i - 2 ∨ t.val = 3 * i - 1 ∨ t.val = 3 * i + 1 then 1 else 0 := by
  have ht := t.isLt
  rw [coreIncidence_catCore_val]
  simp only [spineVertex]
  unfold catTailVal catHeadVal branchIdx parentIndex IsLeafEdge
  split_ifs <;> omega

/-- **An interior spine vertex carries no self-loop.** -/
theorem tail_ne_spineVertex_of_loop (m i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ 2 * m)
    {t : Fin (6 * m + 3)} (hLoop : (catCore m).tail t = (catCore m).head t) :
    (catCore m).tail t ≠ spineVertex m i hi2 := by
  have hLeaf : IsLeafEdge m t := (LollipopLeafRow.catCore_tail_eq_head_iff m t).mp hLoop
  have ht := t.isLt
  intro hEq
  have hv := congrArg Fin.val hEq
  rw [catCore_tail_val] at hv
  simp only [spineVertex] at hv
  unfold catTailVal branchIdx parentIndex at hv
  unfold IsLeafEdge at hLeaf
  split_ifs at hv <;> omega

end Arith

/-! ## 3.  The surviving index sum, read on the surviving occurrences -/

section IndexSum

variable {target : CFGraph} {degree : ℕ}

/-- `SlopesGeometric.survivingIndexSum` sums over the incident source occurrences
that survive; `StablePathCount.incidentEdges` lists the same occurrences in the
subtype of surviving ones.  The two sums agree. -/
theorem survivingIndexSum_eq_sum_incidentEdges (data : GluingDatum target degree)
    (vertex : data.SourceVertex) :
    SlopesGeometric.survivingIndexSum data vertex =
      ∑ edge ∈ StablePathCount.incidentEdges data vertex,
        (data.sourceEdgeIndex edge.1 : ℤ) := by
  classical
  unfold SlopesGeometric.survivingIndexSum
  refine Finset.sum_bij' (fun edge hEdge ↦ (⟨edge.1, (Finset.mem_filter.mp hEdge).2⟩ :
      NonDanglingEdge data))
    (fun edge hEdge ↦ (⟨edge.1,
      (StablePathCount.mem_incidentEdges data vertex edge).mp hEdge⟩ :
        IncidentSourceEdge data vertex)) ?_ ?_ ?_ ?_ ?_
  · intro edge _
    exact (StablePathCount.mem_incidentEdges data vertex _).mpr edge.2
  · intro edge _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, edge.2⟩
  · intro edge _
    rfl
  · intro edge _
    rfl
  · intro edge _
    rfl

end IndexSum

/-! ## 4.  The step condition at an interior spine vertex -/

section Step

variable {m : ℕ} {request : Fin (6 * m + 3) → ℚ}

/-- A slot incident to a core vertex carries a surviving occurrence at the branch
vertex over it (`member.ident.incidence`). -/
theorem exists_incident_of_coreIncidence_pos
    (member : FibreMember (catCore m) request (m + 2))
    (c : Fin (4 * m + 2)) (t : Fin (6 * m + 3))
    (ht : 0 < coreIncidence (catCore m) c t) :
    ∃ edge : NonDanglingEdge member.data,
      Incident member.data edge.1 (member.ident.vertex.symm c).1 ∧
        member.ident.row edge.stablePath = t := by
  have hinc := member.ident.incidence (member.ident.vertex.symm c) t
  rw [Equiv.apply_symm_apply] at hinc
  rw [← hinc] at ht
  obtain ⟨edge, hI, hP⟩ := (StablePathCount.incidenceCount_pos_iff _ _ _).mp ht
  exact ⟨edge, hI, by rw [hP, Equiv.apply_symm_apply]⟩

/-- Conversely, a surviving occurrence at the branch vertex over `c` lies on the
row of a slot incident to `c`. -/
theorem coreIncidence_pos_of_incident
    (member : FibreMember (catCore m) request (m + 2))
    (c : Fin (4 * m + 2)) (edge : NonDanglingEdge member.data)
    (hI : Incident member.data edge.1 (member.ident.vertex.symm c).1) :
    0 < coreIncidence (catCore m) c (member.ident.row edge.stablePath) := by
  have hinc := member.ident.incidence (member.ident.vertex.symm c)
    (member.ident.row edge.stablePath)
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply] at hinc
  rw [← hinc]
  exact (StablePathCount.incidenceCount_pos_iff _ _ _).mpr ⟨edge, hI, rfl⟩

/-- **The step condition at a diagonal member.**  At the interior spine vertex `p_{i+1}`
(`1 ≤ i ≤ 2m`) the two spine slots `3i - 2` and `3i + 1` read `1 / a` and `1 / b`
with `SlopeStepRel a b`.

The branch vertex `X` over `p_{i+1}` has surviving valency three (it is a branch,
and the stable graph is trivalent), and its three surviving occurrences are the
ones on the rows of the three incident slots (`member.ident.incidence`).  It is no
lollipop branch, so its image is trivalent
(`BranchSharedDirection.incidentEdges_card_eq_three_of_branch_of_ne`) and it is
unramified.  Diagonality reads each occurrence's index off the core diagonal
(`coreDiag_eq_inv_sourceEdgeIndex`), which pins the stem's at `2`
(`LoopAdjacentDiagonal.coreDiag_eq_half_of_loopAdjacent`); balancing bounds the
other two; `SlopesGeometric.slopeStepRel_of_trivalent_unramified` concludes. -/
theorem exists_slopeStepRel_spineVertex
    (member : FibreMember (catCore m) request (m + 2)) (hD : member.Diagonal)
    (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ 2 * m) :
    ∃ a b : ℕ, member.coreDiag (spineSlot m i (by omega)) = 1 / (a : ℚ) ∧
      member.coreDiag (spineSlot m (i + 1) (by omega)) = 1 / (b : ℚ) ∧
        SlopeStepRel a b := by
  classical
  set c := spineVertex m i hi2 with hc
  have hInc := coreIncidence_spineVertex m i hi1 hi2
  have hv1 : (spineSlot m i (by omega)).val = 3 * i - 2 := rfl
  have hv2 : (spineSlot m (i + 1) (by omega)).val = 3 * (i + 1) - 2 := rfl
  have hv3 : (stemSlot m i hi2).val = 3 * i - 1 := rfl
  obtain ⟨e1, hI1, hr1⟩ := exists_incident_of_coreIncidence_pos member c
    (spineSlot m i (by omega)) (by rw [hInc, ite_eq_left (by rw [hv1]; omega)]; norm_num)
  obtain ⟨e2, hI2, hr2⟩ := exists_incident_of_coreIncidence_pos member c
    (spineSlot m (i + 1) (by omega)) (by rw [hInc, ite_eq_left (by rw [hv2]; omega)]; norm_num)
  obtain ⟨e3, hI3, hr3⟩ := exists_incident_of_coreIncidence_pos member c
    (stemSlot m i hi2) (by rw [hInc, ite_eq_left (by rw [hv3]; omega)]; norm_num)
  set X := (member.ident.vertex.symm c).1 with hX
  -- the three occurrences are distinct, because their slots are
  have h12 : e1 ≠ e2 := by
    intro h; subst h; have := congrArg Fin.val (hr1.symm.trans hr2); rw [hv1, hv2] at this; omega
  have h13 : e1 ≠ e3 := by
    intro h; subst h; have := congrArg Fin.val (hr1.symm.trans hr3); rw [hv1, hv3] at this; omega
  have h23 : e2 ≠ e3 := by
    intro h; subst h; have := congrArg Fin.val (hr2.symm.trans hr3); rw [hv2, hv3] at this; omega
  -- surviving valency three, and they are all of it
  have hVal : nonDanglingValency member.data X = 3 :=
    le_antisymm (member.fullDim.trivalent X) (member.ident.vertex.symm c).2
  have hSub : ({e1, e2, e3} : Finset (NonDanglingEdge member.data)) ⊆
      StablePathCount.incidentEdges member.data X := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact (StablePathCount.mem_incidentEdges _ _ _).mpr hI1
    · exact (StablePathCount.mem_incidentEdges _ _ _).mpr hI2
    · exact (StablePathCount.mem_incidentEdges _ _ _).mpr hI3
  have hCard3 : ({e1, e2, e3} : Finset (NonDanglingEdge member.data)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
  have hEq : StablePathCount.incidentEdges member.data X = {e1, e2, e3} :=
    (Finset.eq_of_subset_of_card_le hSub
      (by rw [StablePathCount.card_incidentEdges, hVal, hCard3])).symm
  -- the stem occurrence has index two
  have hStemAdj : BallotOrbit.LoopAdjacent (catCore m) (stemSlot m i hi2) :=
    (BallotOrbit.loopAdjacent_catCore m _).mpr (by rw [hv3]; omega)
  have hStemLeaf : ¬ IsLeafEdge m (stemSlot m i hi2) := by
    unfold IsLeafEdge; rw [hv3]; omega
  have h3 := coreDiag_eq_inv_sourceEdgeIndex member hD e3 (by rw [hr3]; exact hStemLeaf)
  rw [hr3, LoopAdjacentDiagonal.coreDiag_eq_half_of_loopAdjacent member hD hStemAdj
    hStemLeaf] at h3
  have hIdx3 : member.data.sourceEdgeIndex e3.1 = 2 := by
    have h := inv_injective (by simpa only [one_div] using h3.symm :
      ((member.data.sourceEdgeIndex e3.1 : ℚ))⁻¹ = (2 : ℚ)⁻¹)
    exact_mod_cast h
  -- the spine readings
  have hLeaf1 : ¬ IsLeafEdge m (spineSlot m i (by omega)) := by
    unfold IsLeafEdge; rw [hv1]; omega
  have hLeaf2 : ¬ IsLeafEdge m (spineSlot m (i + 1) (by omega)) := by
    unfold IsLeafEdge; rw [hv2]; omega
  have hd1 := coreDiag_eq_inv_sourceEdgeIndex member hD e1 (by rw [hr1]; exact hLeaf1)
  have hd2 := coreDiag_eq_inv_sourceEdgeIndex member hD e2 (by rw [hr2]; exact hLeaf2)
  rw [hr1] at hd1
  rw [hr2] at hd2
  refine ⟨member.data.sourceEdgeIndex e1.1, member.data.sourceEdgeIndex e2.1, hd1, hd2, ?_⟩
  -- the vertex is unramified
  have hNe : ∀ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      X ≠ LollipopDivalent.loopBranch member hLoop := by
    intro slot hLoop hXeq
    have h' : member.ident.vertex.symm c = member.ident.vertex.symm ((catCore m).tail slot) :=
      Subtype.ext hXeq
    exact tail_ne_spineVertex_of_loop m i hi1 hi2 hLoop
      (member.ident.vertex.symm.injective h').symm
  have hTri := BranchSharedDirection.incidentEdges_card_eq_three_of_branch_of_ne member hVal hNe
  have hZero := SlopesGeometric.localRamification_eq_zero_of_trivalent_target member.data
    member.fullDim.valid X.1.1 (member.fullDim.changeMinimal _) hTri ⟨X.1.2, X.2⟩
  refine SlopesGeometric.slopeStepRel_of_trivalent_unramified member.data
    member.fullDim.danglingEdgeNoGlue X hVal hZero ?_
    (StableLocalProperties.sourceEdgeIndex_le_blockCard member.data X ⟨e1.1, hI1⟩)
    (StableLocalProperties.sourceEdgeIndex_le_blockCard member.data X ⟨e2.1, hI2⟩)
  rw [survivingIndexSum_eq_sum_incidentEdges, hEq, Finset.sum_insert (by simp [h12, h13]),
    Finset.sum_pair h23, hIdx3]
  push_cast
  ring

end Step

/-! ## 5.  The slope sequence of a diagonal member, and `extract` -/

section Extract

variable {m : ℕ} {request : Fin (6 * m + 3) → ℚ}

/-- Every slot carries a surviving occurrence on its row. -/
theorem exists_edge_row_eq (member : FibreMember (catCore m) request (m + 2))
    (slot : Fin (6 * m + 3)) :
    ∃ edge : NonDanglingEdge member.data, member.ident.row edge.stablePath = slot := by
  obtain ⟨edge, hEdge⟩ := Quot.exists_rep (member.ident.row.symm slot)
  refine ⟨edge, ?_⟩
  rw [show edge.stablePath = member.ident.row.symm slot from hEdge, Equiv.apply_symm_apply]

/-- **A diagonal member reads the reciprocal of a positive integer at every non-leaf
slot.** -/
theorem exists_coreDiag_eq_inv_nat (member : FibreMember (catCore m) request (m + 2))
    (hD : member.Diagonal) (slot : Fin (6 * m + 3)) (hLeaf : ¬ IsLeafEdge m slot) :
    ∃ k : ℕ, 1 ≤ k ∧ member.coreDiag slot = 1 / (k : ℚ) := by
  obtain ⟨edge, hedge⟩ := exists_edge_row_eq member slot
  have h := coreDiag_eq_inv_sourceEdgeIndex member hD edge (by rw [hedge]; exact hLeaf)
  rw [hedge] at h
  refine ⟨_, ?_, h⟩
  rcases Nat.eq_zero_or_pos (member.data.sourceEdgeIndex edge.1) with h0 | hpos
  · exfalso
    apply FibreMember.coreDiag_ne_zero hD slot
    rw [h, h0]
    simp
  · exact hpos

/-- **The slope function of a member**: `σ i` is the reciprocal of the core diagonal
at the spine slot `3i - 2`, for `i ≤ 2m + 1`. -/
noncomputable def slopeFun (member : FibreMember (catCore m) request (m + 2)) (i : ℕ) : ℕ :=
  if h : i ≤ 2 * m + 1 then ⌊(member.coreDiag (spineSlot m i h))⁻¹⌋₊ else 0

theorem slopeFun_eq {member : FibreMember (catCore m) request (m + 2)} {i : ℕ}
    (h : i ≤ 2 * m + 1) {k : ℕ} (hk : member.coreDiag (spineSlot m i h) = 1 / (k : ℚ)) :
    slopeFun member i = k := by
  rw [slopeFun, dite_eq_left h, hk, one_div, inv_inv, Nat.floor_natCast]

/-- The two extreme spine slots read `1 / 2`. -/
theorem coreDiag_spineSlot_end (member : FibreMember (catCore m) request (m + 2))
    (hD : member.Diagonal) {i : ℕ} (h : i ≤ 2 * m + 1) (hi : i = 1 ∨ i = 2 * m + 1) :
    member.coreDiag (spineSlot m i h) = 1 / ((2 : ℕ) : ℚ) := by
  have hv : (spineSlot m i h).val = 3 * i - 2 := rfl
  have hAdj : BallotOrbit.LoopAdjacent (catCore m) (spineSlot m i h) :=
    (BallotOrbit.loopAdjacent_catCore m _).mpr (by rw [hv]; omega)
  have hLeaf : ¬ IsLeafEdge m (spineSlot m i h) := by
    unfold IsLeafEdge; rw [hv]; omega
  rw [LoopAdjacentDiagonal.coreDiag_eq_half_of_loopAdjacent member hD hAdj hLeaf]
  norm_num

/-- **Part II's `prop-caterpillar-ballot`(1), for a diagonal member, at every genus.**
The core diagonal of a diagonal member of the caterpillar fibre is a ballot
diagonal.  No `Open`, no `HasOddMult`, no hypothesis on the request. -/
theorem exists_coreDiag_eq_ballotCoreDiag (member : FibreMember (catCore m) request (m + 2))
    (hD : member.Diagonal) :
    ∃ s : Slopes (2 * (m + 1)), member.coreDiag = BallotSlopes.ballotCoreDiag m s := by
  refine BallotSlopes.exists_ballotCoreDiag_of_values member.coreDiag (slopeFun member)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact slopeFun_eq (by omega) (coreDiag_spineSlot_end member hD (by omega) (Or.inl rfl))
  · exact slopeFun_eq (by omega) (coreDiag_spineSlot_end member hD le_rfl (Or.inr rfl))
  · intro i hi1 hi2
    have hv : (spineSlot m i hi2).val = 3 * i - 2 := rfl
    obtain ⟨k, hk1, hk⟩ := exists_coreDiag_eq_inv_nat member hD (spineSlot m i hi2)
      (by unfold IsLeafEdge; rw [hv]; omega)
    rw [slopeFun_eq hi2 hk]
    exact hk1
  · intro i hi1 hi2
    obtain ⟨a, b, ha, hb, hab⟩ := exists_slopeStepRel_spineVertex member hD i hi1 (by omega)
    rw [slopeFun_eq (by omega) ha, slopeFun_eq (by omega) hb]
    exact hab
  · intro slot hLeaf
    exact ExtractGenusTwo.coreDiag_eq_two_of_isLeafEdge member hD hLeaf
  · intro slot hSpine
    have hlt := slot.isLt
    have hi : (slot.val + 2) / 3 ≤ 2 * m + 1 := by omega
    have hSlot : spineSlot m ((slot.val + 2) / 3) hi = slot := by
      apply Fin.ext
      show 3 * ((slot.val + 2) / 3) - 2 = slot.val
      omega
    obtain ⟨k, _hk1, hk⟩ := exists_coreDiag_eq_inv_nat member hD slot
      (by unfold IsLeafEdge; omega)
    rw [slopeFun_eq hi (by rw [hSlot]; exact hk), hk]
  · intro slot hStem hLast
    have hlt := slot.isLt
    have hAdj : BallotOrbit.LoopAdjacent (catCore m) slot :=
      (BallotOrbit.loopAdjacent_catCore m _).mpr (by omega)
    exact LoopAdjacentDiagonal.coreDiag_eq_half_of_loopAdjacent member hD hAdj
      (by unfold IsLeafEdge; omega)

/-- **`extract`, discharged at every genus.** -/
theorem diagonalExtract (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    BallotSlopes.DiagonalExtract m request :=
  fun member _ _ hD ↦ exists_coreDiag_eq_ballotCoreDiag member hD

end Extract

/-! ## 6.  `hSpine` at genus six, in the consumer's binder shape -/

section GenusSix

/-- **`hSpine`, discharged.**  The exact binder shape of
`BallotSpineReversalSheetIso.diagonalClassification_genusSix_of_three_residues`. -/
theorem hSpine_genusSix (request : Fin (6 * 2 + 3) → ℚ) :
    ∀ mem : FibreMember (catCore 2) request (2 + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ s : Slopes (2 * (2 + 1)), ∀ slot : Fin (6 * 2 + 3),
          ¬ CaterpillarPruning.IsLeafEdge 2 slot →
            mem.coreDiag slot = BallotSlopes.ballotCoreDiag 2 s slot := by
  intro mem _ _ hD
  obtain ⟨s, hs⟩ := exists_coreDiag_eq_ballotCoreDiag mem hD
  exact ⟨s, fun slot _ ↦ congrFun hs slot⟩

/-- **`DiagonalClassification 2` from two residues.** -/
theorem diagonalClassification_genusSix_of_two_residues {request : Fin (6 * 2 + 3) → ℚ}
    (hSep : ∀ mem : FibreMember (catCore 2) request (2 + 2), mem.Open → mem.HasOddMult →
      SpineSingleColumn.LeafAvoidingSeparated 2 mem)
    (hSupply : ∀ (s : Slopes (2 * (2 + 1))) (mem : FibreMember (catCore 2) request (2 + 2)),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        mem.coreDiag = BallotSlopes.ballotCoreDiag 2 s →
          Nonempty (GeometricDatumIso
            (BallotCoreIdentification.ballotFamilyMember 2 request s).data mem.data)) :
    BallotSlopes.DiagonalClassification 2 request :=
  BallotSpineReversalSheetIso.diagonalClassification_genusSix_of_three_residues hSep
    (hSpine_genusSix request) hSupply

end GenusSix

/-! ## 7.  The other two residues at the caterpillar member -/

section RefuteFirst

variable {m : ℕ} {request : Fin (6 * m + 3) → ℚ}

/-- **`hSep` holds at every diagonal member**, with no leaf-avoiding hypothesis
used: in a diagonal member a row meets only its own column
(`SpineOffDiagonal.matrix_ne_zero_iff_meets`), so two rows meeting one column are
that column.  Hence `hSep`'s whole content is about the non-diagonal members. -/
theorem leafAvoidingSeparated_of_diagonal
    (member : FibreMember (catCore m) request (m + 2)) (hD : member.Diagonal) :
    SpineSingleColumn.LeafAvoidingSeparated m member := by
  intro r r' c _ _ hMeets hMeets'
  have hc : c = r := by
    by_contra hne
    exact (SpineOffDiagonal.matrix_ne_zero_iff_meets _ r c).mpr hMeets (hD r c hne)
  have hc' : c = r' := by
    by_contra hne
    exact (SpineOffDiagonal.matrix_ne_zero_iff_meets _ r' c).mpr hMeets' (hD r' c hne)
  exact hc.symm.trans hc'

/-- `hSep` at the caterpillar member: true. -/
theorem leafAvoidingSeparated_caterpillarMember (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    SpineSingleColumn.LeafAvoidingSeparated m (caterpillarMember m request) :=
  leafAvoidingSeparated_of_diagonal _ (diagonal_caterpillarMember m request)

/-- `hSupply` at the caterpillar member: true.  The only slope sequence whose ballot
diagonal is the caterpillar member's is the zig-zag (`ballotCoreDiag_injective`),
and the zig-zag ballot datum **is** the caterpillar datum
(`BallotDatum.ballotDatum_zig`), so the identity is the isomorphism. -/
theorem supply_caterpillarMember (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (s : Slopes (2 * (m + 1)))
    (hs : (caterpillarMember m request).coreDiag = BallotSlopes.ballotCoreDiag m s) :
    Nonempty (GeometricDatumIso
      (BallotCoreIdentification.ballotFamilyMember m request s).data
      (caterpillarMember m request).data) := by
  have hzig : s = BallotDatum.zig m :=
    BallotSlopes.ballotCoreDiag_injective m
      (hs.symm.trans (BallotSlopes.coreDiag_caterpillarMember_eq_zig m request))
  subst hzig
  show Nonempty (GeometricDatumIso (BallotDatum.ballotDatum m (BallotDatum.zig m))
    (CaterpillarDatum.caterpillarDatum m))
  rw [BallotDatum.ballotDatum_zig]
  exact ⟨GeometricDatumIso.refl _⟩

/-- `hSpine` at the caterpillar member: the slope sequence it produces is the
zig-zag. -/
theorem hSpine_caterpillarMember (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (caterpillarMember m request).coreDiag = BallotSlopes.ballotCoreDiag m (BallotDatum.zig m) :=
  BallotSlopes.coreDiag_caterpillarMember_eq_zig m request

/-- The antecedent of `hSpine_genusSix` is inhabited at every positive request. -/
example {request : Fin (6 * 2 + 3) → ℚ} (hRequest : ∀ slot, 0 < request slot) :
    ∃ mem : FibreMember (catCore 2) request (2 + 2),
      mem.Open ∧ mem.HasOddMult ∧ mem.Diagonal :=
  ⟨caterpillarMember 2 request, caterpillarMember_open hRequest,
    caterpillarMember_hasOddMult 2 request, diagonal_caterpillarMember 2 request⟩

end RefuteFirst

end DraismaVargas.Count.BallotResidues
