import DraismaVargasCount.SheetLayerCensus
import DraismaVargasCount.TrivalentFibreUnique
import DraismaVargasCount.LollipopDivalent

/-!
# The partition census, proved at every `m`

This file proves the local half of the statement that every open odd diagonal member
of the fibre over the caterpillar of loops whose core diagonal is the ballot diagonal
of a slope sequence `s` is isomorphic to the ballot family member at `s` (the
statement `hSupply`, proved in `SheetLayerMatching.hSupply_genusSix`).  It builds on
`DraismaVargasCount.DiagonalTargetIso`,
`DraismaVargasCount.TrivalentFibreUnique`, `DraismaVargasCount.BallotResidues` and the
leaf and lollipop modules `DraismaVargasCount.LeafFibre`,
`DraismaVargasCount.LollipopDivalent` and `DraismaVargasCount.LollipopLeafRow`.

`SheetLayerCensus.PartitionCensus m request` asks that, over the target layer
`DiagonalTargetIso.targetLayer`, every vertex partition and every edge partition of a
diagonal open odd member be a relabelling of the ballot member's.  It is proved here
outright, at every `m` and every request, and in fact for **any two diagonal members
with equal core diagonals** (no request, openness, oddness or slope hypothesis).

## What is proved

**Every partition in play is a star** -- one anchor block, every other block a
single sheet -- and two stars with anchors of equal size are relabellings
(`DiagonalTargetIso.exists_relabel_of_star`).
* §1, vertices.  `vertex_blockCard_eq_one_off_surviving`: over any target vertex
  carrying a surviving source vertex `X`, every block other than `X`'s is a single
  sheet -- `TrivalentFibreUnique.fibreVertexUnique` (at most one surviving source
  vertex per target vertex, at every member) plus Observation I
  (`blockCard_eq_one_of_nonDanglingValency_eq_zero`).  So no per-vertex hairpin
  argument is needed at the loop vertices.
* §2--§4, the anchor sizes over the three kinds of target vertex (through the
  dictionary `absMap`, `AbsVertex m = Fin (4m+2) ⊕ LoopSlot m`):
  - `coreVertex_cases`: every core vertex of `catCore m` carries a self-loop or is
    an interior spine vertex `spineVertex m i`, `1 ≤ i ≤ 2m`;
  - interior spine vertex: `DiagonalTargetIso.spine_vertexPartition_relabel` (anchor
    `(a + b + 1)/2`, read off the core diagonal);
  - loop vertex: anchor size `2` at every member (`blockCard_loopBranch`, from
    `LollipopDivalent.blockCard_eq_two_of_incidenceCount_eq_two`);
  - tip of a loop slot: `isLeafVertex_tip` (the tip is a leaf of the member's
    target, from injectivity of `absMap`), so the anchor is `LeafFibre.coreVertex`,
    of size `2`.
  `vertexCensus` assembles these.
* §5, edges.  Over the edge of a **non-leaf** slot `t` there is exactly one
  surviving occurrence (`DiagonalTargetIso.eq_of_row_eq_of_not_leaf`;
  `row_eq_of_target_eq` pins its row), every other occurrence is dangling and so of
  index one (`danglingEdgeNoGlue`): `edge_blockCard_eq_one_off_surviving`.  The anchor
  size is `1 / coreDiag t` (`BallotResidues.coreDiag_eq_inv_sourceEdgeIndex`), equal on both
  sides (`edgeCensus_of_not_leaf`).  Over the edge of a **loop** slot every
  occurrence has index one -- it is the leaf edge of the tip
  (`LeafFibre.sourceEdgeIndex_eq_one_above_leaf`) -- so both partitions are
  discrete (`edge_blockCard_leaf`).  `edgeCensus` assembles these.
* §6, **`partitionCensus_of_coreDiag_eq`** (any two diagonal members with equal
  core diagonals), **`partitionCensus`** (`PartitionCensus m request`, every `m`,
  every request) and `partitionCensus_genusSix` (`m = 2`).

Note that the anchor sizes are read off the core diagonal only over interior spine
vertices and non-leaf slot edges; over loop vertices and tips they are the constant
`2`, and over loop-slot edges the partition is discrete (the two surviving
occurrences of a leaf row both have index one, so an edge partition never has two
non-singleton blocks).

## What is NOT proved here

* **The global matching** (`PartitionCensus → SheetLayerSupply`) is not touched
  here; it is `SheetLayerMatching.sheetLayerSupply_of_partitionCensus`.
  `DiagonalTargetIso.census_not_sufficient` shows that the census alone
  does not give a `GeometricDatumIso` in general; the permutations must be made
  compatible along every edge.  The two halves together give a sheet layer between
  any two diagonal members with equal core diagonals
  (`SheetLayerMatching.sheetLayer_of_coreDiag_eq`), which the base count
  `CaterpillarAllMembers` uses (step 1 of `DraismaVargasCount.Assembly`).
* Nothing here uses `Open` or `HasOddMult`; `partitionCensus` discards them.
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no
  `#eval`.
-/

namespace DraismaVargas.Count.PartitionCensusProof

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.DiagonalTargetIso

variable {m : ℕ} {y y₁ y₂ : Fin (6 * m + 3) → ℚ}

/-! ## 1.  Vertex partitions are stars around the surviving source vertex -/

/-- **Every vertex partition is a star around any surviving source vertex over
it**: `TrivalentFibreUnique.fibreVertexUnique` (at most one surviving source vertex
per target vertex) plus Observation I (a dangling source vertex is a single sheet). -/
theorem vertex_blockCard_eq_one_off_surviving (member : FibreMember (catCore m) y (m + 2))
    (X : member.data.SourceVertex) (hX : 0 < nonDanglingValency member.data X)
    (σ : Fin (m + 2)) (hσ : ¬ (member.data.vertexPartition X.1.1).Rel σ X.1.2) :
    (member.data.vertexPartition X.1.1).blockCard σ = 1 := by
  set Z := member.data.sourceEndpoint X.1.1 σ with hZdef
  by_cases hZero : nonDanglingValency member.data Z = 0
  · have h := blockCard_eq_one_of_nonDanglingValency_eq_zero member Z hZero
    rw [← blockCard_congr' _ ((member.data.vertexPartition X.1.1).rel_repr_left σ)]
    exact h
  · exfalso
    have hEq : Z = X := TrivalentFibreUnique.fibreVertexUnique member Z X rfl
      (Nat.pos_of_ne_zero hZero) hX
    apply hσ
    have h2 := congrArg (fun W : member.data.SourceVertex ↦ W.1.2) hEq
    simp only [hZdef, GluingDatum.sourceEndpoint] at h2
    show (member.data.vertexPartition X.1.1).repr σ =
      (member.data.vertexPartition X.1.1).repr X.1.2
    rw [h2]
    exact X.2.symm

/-- Two surviving source vertices of the same local degree have relabelled
vertex partitions above them. -/
theorem exists_relabel_of_surviving (mem₁ : FibreMember (catCore m) y₁ (m + 2))
    (mem₂ : FibreMember (catCore m) y₂ (m + 2))
    (X₁ : mem₁.data.SourceVertex) (X₂ : mem₂.data.SourceVertex)
    (hX₁ : 0 < nonDanglingValency mem₁.data X₁)
    (hX₂ : 0 < nonDanglingValency mem₂.data X₂)
    (hCard : (mem₂.data.vertexPartition X₂.1.1).blockCard X₂.1.2 =
      (mem₁.data.vertexPartition X₁.1.1).blockCard X₁.1.2) :
    ∃ π : Equiv.Perm (Fin (m + 2)),
      mem₂.data.vertexPartition X₂.1.1 = (mem₁.data.vertexPartition X₁.1.1).relabel π :=
  exists_relabel_of_star _ _ X₁.1.2 X₂.1.2 hCard
    (vertex_blockCard_eq_one_off_surviving mem₁ X₁ hX₁)
    (vertex_blockCard_eq_one_off_surviving mem₂ X₂ hX₂)

/-! ## 2.  The core vertices: loop vertices and interior spine vertices -/

/-- Every core vertex of `catCore m` carries a self-loop or is an interior spine
vertex. -/
theorem coreVertex_cases (c : Fin (4 * m + 2)) :
    (∃ t : Fin (6 * m + 3), (catCore m).tail t = (catCore m).head t ∧
        (catCore m).tail t = c) ∨
      ∃ i : ℕ, 1 ≤ i ∧ ∃ hi2 : i ≤ 2 * m, c = BallotResidues.spineVertex m i hi2 := by
  have hc := c.isLt
  by_cases hodd : c.val % 2 = 1 ∧ c.val < 4 * m
  · right
    refine ⟨(c.val + 1) / 2, by omega, by omega, ?_⟩
    apply Fin.ext
    show c.val = 2 * ((c.val + 1) / 2) - 1
    omega
  · left
    by_cases hlast : c.val = 4 * m + 1
    · refine ⟨⟨6 * m + 2, by omega⟩, ?_, ?_⟩
      · exact (LollipopLeafRow.catCore_tail_eq_head_iff m _).mpr (Or.inr rfl)
      · apply Fin.ext
        show branchIdx (catTailVal m ⟨6 * m + 2, by omega⟩) = c.val
        simp only [catTailVal, CaterpillarTree.parentIndex, branchIdx]
        split_ifs <;> omega
    · refine ⟨⟨3 * (c.val / 2), by omega⟩, ?_, ?_⟩
      · exact (LollipopLeafRow.catCore_tail_eq_head_iff m _).mpr
          (Or.inl (by show 3 * (c.val / 2) % 3 = 0; omega))
      · apply Fin.ext
        show branchIdx (catTailVal m ⟨3 * (c.val / 2), by omega⟩) = c.val
        simp only [catTailVal, CaterpillarTree.parentIndex, branchIdx]
        split_ifs <;> omega

/-- **The local degree at a loop branch vertex is two**
(`LollipopDivalent.blockCard_eq_two_of_incidenceCount_eq_two`). -/
theorem blockCard_loopBranch (member : FibreMember (catCore m) y (m + 2))
    {t : Fin (6 * m + 3)} (hLoop : (catCore m).tail t = (catCore m).head t) :
    (member.data.vertexPartition (branchVertex member ((catCore m).tail t)).1.1).blockCard
      (branchVertex member ((catCore m).tail t)).1.2 = 2 :=
  LollipopDivalent.blockCard_eq_two_of_incidenceCount_eq_two member.fullDim
    (LollipopDivalent.three_le_loopBranch member hLoop)
    (LollipopLeafRow.incidenceCount_eq_two_of_core_loop member hLoop)

theorem nonDanglingValency_branchVertex_pos (member : FibreMember (catCore m) y (m + 2))
    (c : Fin (4 * m + 2)) : 0 < nonDanglingValency member.data (branchVertex member c) := by
  have := (member.ident.vertex.symm c).2
  exact lt_of_lt_of_le (by norm_num) this

/-! ## 3.  The tips of the loop slots are leaves -/

/-- **The tip of a loop slot is a leaf of the member's target**: the only target
edge at it is the loop slot's own edge (the dictionary `absMap` is injective, and
`Sum.inr t` is an abstract end of slot `t` only). -/
theorem isLeafVertex_tip (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) (t : LoopSlot m) :
    IsLeafVertex member.target (absMap member (Sum.inr t)) := by
  classical
  have hInj := (absMap_bijective member hD).injective
  have hEnds : absEnds m t.1 = (Sum.inl ((catCore m).tail t.1), Sum.inr t) := by
    unfold absEnds
    rw [dif_pos t.2]
  unfold IsLeafVertex
  rw [Finset.card_eq_one]
  refine ⟨slotEdge member t.1, ?_⟩
  ext e
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro he
    obtain ⟨t', rfl⟩ := (slotEdge member).surjective e
    have key : (absEnds m t').1 = Sum.inr t ∨ (absEnds m t').2 = Sum.inr t := by
      rcases slotEdge_absEnds member hD t' with h | h <;> rw [h] at he <;>
        simp only at he <;> rcases he with he | he
      · exact Or.inl (hInj he)
      · exact Or.inr (hInj he)
      · exact Or.inr (hInj he)
      · exact Or.inl (hInj he)
    unfold absEnds at key
    split_ifs at key with hLoop
    · rcases key with k | k
      · simp at k
      · have k' : (⟨t', hLoop⟩ : LoopSlot m) = t := Sum.inr.inj k
        rw [← k']
    · rcases key with k | k <;> simp at k
  · rintro rfl
    rcases slotEdge_absEnds member hD t.1 with h | h <;> rw [h, hEnds]
    · exact Or.inr rfl
    · exact Or.inl rfl

/-! ## 4.  The vertex census -/

/-- **The vertex half of the census**, for any two diagonal members with the same
core diagonal (any requests; no openness or oddness). -/
theorem vertexCensus (mem₁ : FibreMember (catCore m) y₁ (m + 2))
    (mem₂ : FibreMember (catCore m) y₂ (m + 2))
    (hD₁ : mem₁.Diagonal) (hD₂ : mem₂.Diagonal)
    (hDiag : mem₁.coreDiag = mem₂.coreDiag) (v : mem₁.target.V) :
    ∃ π : Equiv.Perm (Fin (m + 2)),
      mem₂.data.vertexPartition ((targetLayer mem₁ mem₂ hD₁ hD₂).targetVertex v) =
        (mem₁.data.vertexPartition v).relabel π := by
  obtain ⟨x, rfl⟩ := (absEquiv mem₁ hD₁).surjective v
  have hT : (targetLayer mem₁ mem₂ hD₁ hD₂).targetVertex (absEquiv mem₁ hD₁ x) =
      absMap mem₂ x := by
    show absEquiv mem₂ hD₂ ((absEquiv mem₁ hD₁).symm (absEquiv mem₁ hD₁ x)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [hT, absEquiv_apply]
  rcases x with c | t
  · rcases coreVertex_cases c with ⟨t, hLoop, rfl⟩ | ⟨i, hi1, hi2, rfl⟩
    · exact exists_relabel_of_surviving mem₁ mem₂ (branchVertex mem₁ _)
        (branchVertex mem₂ _)
        (nonDanglingValency_branchVertex_pos mem₁ _)
        (nonDanglingValency_branchVertex_pos mem₂ _)
        (by rw [blockCard_loopBranch mem₁ hLoop, blockCard_loopBranch mem₂ hLoop])
    · have h := spine_vertexPartition_relabel mem₁ mem₂ hD₁ hD₂ hDiag i hi1 hi2
      rw [targetLayer_branchImage] at h
      exact h
  · have hL₁ := isLeafVertex_tip mem₁ hD₁ t
    have hL₂ := isLeafVertex_tip mem₂ hD₂ t
    exact exists_relabel_of_surviving mem₁ mem₂ (LeafFibre.coreVertex mem₁.fullDim hL₁)
      (LeafFibre.coreVertex mem₂.fullDim hL₂)
      (by rw [LeafFibre.nonDanglingValency_coreVertex]; norm_num)
      (by rw [LeafFibre.nonDanglingValency_coreVertex]; norm_num)
      ((LeafFibre.blockCard_coreBlock mem₂.fullDim hL₂).trans
        (LeafFibre.blockCard_coreBlock mem₁.fullDim hL₁).symm)

/-! ## 5.  The edge census -/

/-- A surviving occurrence lying over the target edge of slot `t` is on row `t`. -/
theorem row_eq_of_target_eq (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) (E : NonDanglingEdge member.data) {t : Fin (6 * m + 3)}
    (hE : E.1.1.1 = slotEdge member t) : member.ident.row E.stablePath = t :=
  (slotEdge member).injective ((target_eq_slotEdge member hD E).symm.trans hE)

/-- **Over a non-leaf slot's edge the partition is a star** around the one
surviving occurrence (`DiagonalTargetIso.eq_of_row_eq_of_not_leaf`); every other occurrence is
dangling, hence of index one (`danglingEdgeNoGlue`). -/
theorem edge_blockCard_eq_one_off_surviving (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) {t : Fin (6 * m + 3)} (hNotLeaf : ¬ IsLeafEdge m t)
    (E : NonDanglingEdge member.data) (hRow : member.ident.row E.stablePath = t)
    (σ : Fin (m + 2)) (hσ : ¬ (member.data.edgePartition E.1.1.1).Rel σ E.1.1.2) :
    (member.data.edgePartition E.1.1.1).blockCard σ = 1 := by
  classical
  set F := member.data.sourceEdge E.1.1.1 σ with hF
  have hIdx : member.data.sourceEdgeIndex F =
      (member.data.edgePartition E.1.1.1).blockCard σ :=
    GluingDatum.sourceEdgeIndex_sourceEdge _ _ _
  rw [← hIdx]
  by_cases hDang : IsDangling member.data F
  · exact member.fullDim.danglingEdgeNoGlue F hDang
  · exfalso
    have hFrow : member.ident.row
        (NonDanglingEdge.stablePath (⟨F, hDang⟩ : NonDanglingEdge member.data)) = t := by
      apply row_eq_of_target_eq member hD
      show E.1.1.1 = slotEdge member t
      rw [target_eq_slotEdge member hD E, hRow]
    have hFE := eq_of_row_eq_of_not_leaf member hD hNotLeaf hFrow hRow
    have h2 := congrArg (fun G : NonDanglingEdge member.data ↦ G.1.1.2) hFE
    simp only [hF, GluingDatum.sourceEdge_sheet] at h2
    apply hσ
    show (member.data.edgePartition E.1.1.1).repr σ =
      (member.data.edgePartition E.1.1.1).repr E.1.1.2
    rw [h2]
    exact E.1.2.symm

/-- The edge of a loop slot is incident to its tip. -/
theorem slotEdge_mem_incidentEdges_tip (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) (t : LoopSlot m) :
    slotEdge member t.1 ∈ GluingDatum.incidentEdges (absMap member (Sum.inr t)) := by
  classical
  have hEnds : absEnds m t.1 = (Sum.inl ((catCore m).tail t.1), Sum.inr t) := by
    unfold absEnds
    rw [dif_pos t.2]
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases slotEdge_absEnds member hD t.1 with h | h <;> rw [h, hEnds]
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **Over a loop slot's edge every occurrence has index one**: the edge is the
leaf edge of the tip (`LeafFibre.sourceEdgeIndex_eq_one_above_leaf`). -/
theorem edge_blockCard_leaf (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) (t : LoopSlot m) (σ : Fin (m + 2)) :
    (member.data.edgePartition (slotEdge member t.1)).blockCard σ = 1 := by
  have hL := isLeafVertex_tip member hD t
  have hEq := eq_leafEdge_of_mem hL (slotEdge_mem_incidentEdges_tip member hD t)
  rw [← GluingDatum.sourceEdgeIndex_sourceEdge]
  exact LeafFibre.sourceEdgeIndex_eq_one_above_leaf member.fullDim hL hEq

/-- The edge census over a non-leaf slot: the anchor sizes are the reciprocal core
diagonal entry (`BallotResidues.coreDiag_eq_inv_sourceEdgeIndex`), equal on both sides. -/
theorem edgeCensus_of_not_leaf (mem₁ : FibreMember (catCore m) y₁ (m + 2))
    (mem₂ : FibreMember (catCore m) y₂ (m + 2))
    (hD₁ : mem₁.Diagonal) (hD₂ : mem₂.Diagonal)
    (hDiag : mem₁.coreDiag = mem₂.coreDiag) {t : Fin (6 * m + 3)}
    (hNotLeaf : ¬ IsLeafEdge m t) :
    ∃ π : Equiv.Perm (Fin (m + 2)),
      mem₂.data.edgePartition (slotEdge mem₂ t) =
        (mem₁.data.edgePartition (slotEdge mem₁ t)).relabel π := by
  obtain ⟨E₁, -, hR₁⟩ := BallotResidues.exists_incident_of_coreIncidence_pos mem₁
    ((catCore m).tail t) t (coreIncidence_tail_pos t)
  obtain ⟨E₂, -, hR₂⟩ := BallotResidues.exists_incident_of_coreIncidence_pos mem₂
    ((catCore m).tail t) t (coreIncidence_tail_pos t)
  have hT₁ : E₁.1.1.1 = slotEdge mem₁ t := by rw [target_eq_slotEdge mem₁ hD₁ E₁, hR₁]
  have hT₂ : E₂.1.1.1 = slotEdge mem₂ t := by rw [target_eq_slotEdge mem₂ hD₂ E₂, hR₂]
  have hd₁ := BallotResidues.coreDiag_eq_inv_sourceEdgeIndex mem₁ hD₁ E₁
    (by rw [hR₁]; exact hNotLeaf)
  have hd₂ := BallotResidues.coreDiag_eq_inv_sourceEdgeIndex mem₂ hD₂ E₂
    (by rw [hR₂]; exact hNotLeaf)
  rw [hR₁, hDiag] at hd₁
  rw [hR₂] at hd₂
  have hIdx : (mem₁.data.sourceEdgeIndex E₁.1 : ℚ) = mem₂.data.sourceEdgeIndex E₂.1 := by
    have := hd₁.symm.trans hd₂
    simpa only [one_div, inv_inj] using this
  have hIdx' : mem₁.data.sourceEdgeIndex E₁.1 = mem₂.data.sourceEdgeIndex E₂.1 := by
    exact_mod_cast hIdx
  rw [← hT₁, ← hT₂]
  exact exists_relabel_of_star _ _ E₁.1.1.2 E₂.1.1.2 hIdx'.symm
    (edge_blockCard_eq_one_off_surviving mem₁ hD₁ hNotLeaf E₁ hR₁)
    (edge_blockCard_eq_one_off_surviving mem₂ hD₂ hNotLeaf E₂ hR₂)

/-- **The edge half of the census**, for any two diagonal members with the same
core diagonal. -/
theorem edgeCensus (mem₁ : FibreMember (catCore m) y₁ (m + 2))
    (mem₂ : FibreMember (catCore m) y₂ (m + 2))
    (hD₁ : mem₁.Diagonal) (hD₂ : mem₂.Diagonal)
    (hDiag : mem₁.coreDiag = mem₂.coreDiag) (e : mem₁.target.edges) :
    ∃ π : Equiv.Perm (Fin (m + 2)),
      mem₂.data.edgePartition ((targetLayer mem₁ mem₂ hD₁ hD₂).targetEdge e) =
        (mem₁.data.edgePartition e).relabel π := by
  obtain ⟨t, rfl⟩ := (slotEdge mem₁).surjective e
  rw [targetLayer_slotEdge]
  by_cases hLeaf : IsLeafEdge m t
  · have hLoop : (catCore m).tail t = (catCore m).head t :=
      (LollipopLeafRow.catCore_tail_eq_head_iff m t).mpr hLeaf
    exact exists_relabel_of_star _ _ 0 0
      (by rw [edge_blockCard_leaf mem₂ hD₂ ⟨t, hLoop⟩,
        edge_blockCard_leaf mem₁ hD₁ ⟨t, hLoop⟩])
      (fun σ _ ↦ edge_blockCard_leaf mem₁ hD₁ ⟨t, hLoop⟩ σ)
      (fun σ _ ↦ edge_blockCard_leaf mem₂ hD₂ ⟨t, hLoop⟩ σ)
  · exact edgeCensus_of_not_leaf mem₁ mem₂ hD₁ hD₂ hDiag hLeaf

/-! ## 6.  The headline -/

/-- **The partition census between any two diagonal members with equal core
diagonals**: over the target layer `DiagonalTargetIso.targetLayer`, every vertex
partition and every edge partition of the second is a relabelling of the first's.  No
request, openness, oddness or slope hypothesis. -/
theorem partitionCensus_of_coreDiag_eq (mem₁ : FibreMember (catCore m) y₁ (m + 2))
    (mem₂ : FibreMember (catCore m) y₂ (m + 2))
    (hD₁ : mem₁.Diagonal) (hD₂ : mem₂.Diagonal)
    (hDiag : mem₁.coreDiag = mem₂.coreDiag) :
    (∀ v, ∃ π : Equiv.Perm (Fin (m + 2)),
        mem₂.data.vertexPartition ((targetLayer mem₁ mem₂ hD₁ hD₂).targetVertex v) =
          (mem₁.data.vertexPartition v).relabel π) ∧
      (∀ e, ∃ π : Equiv.Perm (Fin (m + 2)),
        mem₂.data.edgePartition ((targetLayer mem₁ mem₂ hD₁ hD₂).targetEdge e) =
          (mem₁.data.edgePartition e).relabel π) :=
  ⟨vertexCensus mem₁ mem₂ hD₁ hD₂ hDiag, edgeCensus mem₁ mem₂ hD₁ hD₂ hDiag⟩

/-- **`PartitionCensus`, proved at every `m` and every request.** -/
theorem partitionCensus (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    SheetLayerCensus.PartitionCensus m request := by
  intro s mem _hOpen _hOdd hD hdiag
  exact partitionCensus_of_coreDiag_eq _ mem _ hD
    ((RigidityBasepoint.ballotFamilyMember_coreDiag m request s).trans hdiag.symm)

/-- The genus-six instance (`m = 2`). -/
theorem partitionCensus_genusSix (request : Fin (6 * 2 + 3) → ℚ) :
    SheetLayerCensus.PartitionCensus 2 request :=
  partitionCensus 2 request

end DraismaVargas.Count.PartitionCensusProof
