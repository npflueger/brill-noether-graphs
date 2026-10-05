module

public import DraismaVargas.LocalCases.W2PLimitMatrix
public import DraismaVargas.LocalCases.W3Nd2IncomingNormalization
public import DraismaVargas.LocalCases.IncomingMatchingCore
public import DraismaVargas.LocalCases.IncomingW2TargetPlacement

@[expose] public section

/-!
# The incoming census at a `{w2-r2-nd3-P}` wall

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-P}`, Figure 35.

`W2PSourceCandidates` .. `W2PArbitraryExit` describe the *outgoing* side of
Figure 35 at a wall of the already-contracted target.  This module starts from
the other end: an arbitrary incoming gluing datum with an honest
full-dimensional presentation, a single target edge `contracted` between `a`
and `b` whose source fibre is a forest, and the `w2P` tag that
`IncomingSourceCases.Classification` hands out for the contracted wall
`⟨a, hab⟩`.  It reads the incoming wall data off that bundle.

## What is proved

* `not_leaf_left`, `not_leaf_right` / `divalent_endpoints` — **the incoming
  wall is `(2,2)`.**  The
  two leaf orientations `(1,3)` and `(3,1)` that `IncomingW2TargetPlacement`
  leaves open are *impossible* at a `w2P` wall.  This is the one place where
  case P differs structurally from M11, whose family carries a constant-`true`
  split member for exactly those orientations; Figure 35's three members all
  carry the same side predicate `(orientedStar profile).right`, so a leaf
  orientation would have no member at all.  The proof is a counting argument:
  at a target leaf every source vertex above it carries only occurrences of
  `contracted`, the forest identity together with the single `t₃` block above
  `A₀` forces every one of those vertices to carry exactly one, surviving
  valency one is impossible (`NonDanglingValency.nonDanglingValency_ne_one`),
  so *every* occurrence of `contracted` is dangling -- contradicting
  `NoDanglingTargetFibres`, which full-dimensionality supplies.

* `retained_count`, `isolated_count`, `singleEnd_count`,
  `doubleEnd_contracted_counts` — the induced block counts above `A₀`: three
  `t₂` classes, one `t₃` class, one class of the `t₃` endpoint, and two
  classes each of the contracted occurrence and of the `t₂` endpoint.

* `contracted_block_eq_doubleEnd_block` — the contracted occurrence and the
  `t₂` endpoint induce *the same* partition above `A₀`.

* `exists_member_selected_blocks` — the selected-class census: above `A₀` the
  `t₂` endpoint induces exactly one of the three members' fine partitions.

The module takes the `w2P` payload as explicit hypotheses (`profile`, `shape`
and the `background` field of `IncomingSourceCases.W2.Classification.p`)
rather than the inductive itself, so that nothing here depends on the
classifier's constructor layout.
-/

namespace DraismaVargas.LocalCases.W2PIncomingCensus

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open W4Assembly W4StableSource StableLocalProperties NonDanglingValency
open W2R1Target SecondEquation FullDimensionalSource WallDegeneration
open TargetExpansion
open W2PSourceCandidates W2PSurvival

/-! ## §1  Counting lemmas -/

section Counting

variable {α : Type*}

/-- Natural summands bounded below by one that add up to the number of
summands are all equal to one. -/
private theorem eq_one_of_sum_eq_card {s : Finset α} {f : α → ℕ}
    (hOne : ∀ x ∈ s, 1 ≤ f x) (hSum : ∑ x ∈ s, f x = s.card)
    {x : α} (hx : x ∈ s) : f x = 1 := by
  by_contra hNe
  have hAtLeast := hOne x hx
  have hTwo : 1 < f x := by omega
  have hLt : ∑ _y ∈ s, 1 < ∑ y ∈ s, f y :=
    Finset.sum_lt_sum (fun y hy ↦ hOne y hy) ⟨x, hx, hTwo⟩
  rw [hSum, Finset.sum_const, smul_eq_mul, mul_one] at hLt
  exact lt_irrefl _ hLt

end Counting

/-! ## §2  A target leaf forces every contracted occurrence to dangle -/

section Leaf

variable {target : CFGraph} {degree : ℕ} {contracted : target.edges}
  (data : GluingDatum target degree)

/-- At a target vertex whose only occurrence is the contracted one, the number
of incident source occurrences of a source vertex is the induced count of the
contracted occurrence's partition. -/
private theorem card_incident_of_leaf (leaf : target.V)
    (hLeaf : GluingDatum.incidentEdges leaf = {contracted}) (sheet : Fin degree) :
    Fintype.card (IncidentSourceEdge data (data.sourceEndpoint leaf sheet)) =
      (data.edgePartition contracted).blockCountWithin
        (data.vertexPartition leaf) sheet := by
  classical
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin data
    (data.sourceEndpoint leaf sheet)]
  change ∑ targetEdge ∈ GluingDatum.incidentEdges leaf,
      (data.edgePartition targetEdge).blockCountWithin (data.vertexPartition leaf)
        ((data.vertexPartition leaf).repr sheet) = _
  rw [hLeaf, Finset.sum_singleton]
  exact blockCountWithin_congr _ (data.vertexPartition leaf)
    ((data.vertexPartition leaf).rel_repr_left sheet)

/-- A source vertex above a target leaf carrying a single contracted
occurrence has surviving valency zero: valency one is impossible in a
connected quotient source. -/
private theorem nonDanglingValency_eq_zero_of_leaf (leaf : target.V)
    (hLeaf : GluingDatum.incidentEdges leaf = {contracted})
    (hConnected : data.Connected) (sheet : Fin degree)
    (hCount : (data.edgePartition contracted).blockCountWithin
      (data.vertexPartition leaf) sheet = 1) :
    nonDanglingValency data (data.sourceEndpoint leaf sheet) = 0 := by
  have hCard := card_incident_of_leaf data leaf hLeaf sheet
  have hLe := nonDanglingValency_le_card_incidentSourceEdge data
    (data.sourceEndpoint leaf sheet)
  have hNe := nonDanglingValency_ne_one data hConnected
    (data.sourceEndpoint leaf sheet)
  omega

/-- The source vertex above a sheet, read as the source vertex of that
sheet's wall block. -/
private theorem sourceEndpoint_eq_sourceVertex (vertex : target.V) (sheet : Fin degree) :
    data.sourceEndpoint vertex sheet =
      WallBlock.sourceVertex data vertex (WallBlock.ofSheet data vertex sheet) := by
  apply Subtype.ext
  show (vertex, (data.vertexPartition vertex).repr sheet) =
    (vertex, (data.vertexPartition vertex).repr
      ((data.vertexPartition vertex).repr sheet))
  rw [(data.vertexPartition vertex).repr_idem sheet]

/-- Every occurrence of the contracted edge above a surviving-valency-zero
leaf fibre is dangling. -/
private theorem isDangling_of_leaf (leaf : target.V)
    (hMem : contracted ∈ GluingDatum.incidentEdges leaf)
    (hZero : ∀ sheet, nonDanglingValency data (data.sourceEndpoint leaf sheet) = 0)
    (edge : data.SourceEdge) (hTarget : edge.1.1 = contracted) :
    IsDangling data edge := by
  by_contra hSurvives
  have hIncident : Incident data edge
      (WallBlock.sourceVertex data leaf (WallBlock.ofSheet data leaf edge.1.2)) := by
    rw [← sourceEndpoint_eq_sourceVertex data leaf edge.1.2]
    refine (incident_iff_target_mem_and_rel data edge _).mpr ⟨?_, ?_⟩
    · rw [hTarget]
      exact hMem
    · exact (data.vertexPartition leaf).rel_repr_left edge.1.2
  have hCard : Fintype.card (NonDanglingIncidentEdge data leaf
      (WallBlock.ofSheet data leaf edge.1.2)) = 0 := by
    rw [card_nonDanglingIncidentEdge_eq_nonDanglingValency data leaf
      (WallBlock.ofSheet data leaf edge.1.2),
      ← sourceEndpoint_eq_sourceVertex data leaf edge.1.2]
    exact hZero edge.1.2
  exact (Fintype.card_eq_zero_iff.mp hCard).false
    (⟨edge, hSurvives, hIncident⟩ : NonDanglingIncidentEdge data leaf
      (WallBlock.ofSheet data leaf edge.1.2))

end Leaf

/-! ## §3  The leaf orientations are impossible at a `w2P` wall -/

section LeafExclusion

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)

/-- Off the distinguished wall block a leaf fibre is unramified, so its single
contracted occurrence class is forced. -/
private theorem contracted_count_off_selected (leaf : target.V)
    (hLeafEdges : GluingDatum.incidentEdges leaf = {contracted})
    (sheet : Fin degree)
    (hRam : data.localRamification leaf (WallBlock.ofSheet data leaf sheet) = 0) :
    (data.edgePartition contracted).blockCountWithin
      (data.vertexPartition leaf) sheet = 1 := by
  unfold GluingDatum.localRamification at hRam
  rw [hLeafEdges, Finset.sum_singleton, Finset.card_singleton] at hRam
  have hCount : (data.edgePartition contracted).blockCountWithin
      (data.vertexPartition leaf) (WallBlock.ofSheet data leaf sheet).1 =
      (data.edgePartition contracted).blockCountWithin
        (data.vertexPartition leaf) sheet :=
    blockCountWithin_congr _ (data.vertexPartition leaf)
      ((data.vertexPartition leaf).rel_repr_left sheet)
  have hCard : (data.vertexPartition leaf).blockCard
      (WallBlock.ofSheet data leaf sheet).1 =
      (data.vertexPartition leaf).blockCard sheet :=
    blockCard_congr _ ((data.vertexPartition leaf).rel_repr_left sheet)
  rw [hCount, hCard] at hRam
  have hPos := SheetPartition.blockCountWithin_pos (data.edgePartition contracted)
    (data.vertexPartition leaf) sheet
  have hCardPos := (data.vertexPartition leaf).blockCard_pos sheet
  omega

/-- Above the distinguished wall block the forest identity plus the single
class of the other endpoint force every leaf fibre to carry exactly one
contracted occurrence class. -/
private theorem contracted_count_on_selected
    (selected : (mergedPartition data a b).Blocks) (leaf other : target.V)
    (hLeafEdges : GluingDatum.incidentEdges leaf = {contracted})
    (hLeafRefines : (data.vertexPartition leaf).Refines (mergedPartition data a b))
    (hOtherCount : (data.vertexPartition other).blockCountWithin
      (mergedPartition data a b) selected.1 = 1)
    (hForestCount : ((data.edgePartition contracted).blockCountWithin
        (mergedPartition data a b) selected.1 : ℤ) + 1 =
      ((data.vertexPartition leaf).blockCountWithin
          (mergedPartition data a b) selected.1 : ℤ) +
        ((data.vertexPartition other).blockCountWithin
          (mergedPartition data a b) selected.1 : ℤ))
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel selected.1 sheet) :
    (data.edgePartition contracted).blockCountWithin
      (data.vertexPartition leaf) sheet = 1 := by
  classical
  have hMem : contracted ∈ GluingDatum.incidentEdges leaf := by
    rw [hLeafEdges]
    exact Finset.mem_singleton_self _
  have hEdgeRefines : (data.edgePartition contracted).Refines
    (data.vertexPartition leaf) := refines_of_mem_incidentEdges data hMem
  have hSum := sum_blockCountWithin_trans (data.edgePartition contracted)
    (data.vertexPartition leaf) (mergedPartition data a b) hEdgeRefines hLeafRefines selected
  have hCards := SheetPartition.card_blocksWithin_eq_blockCountWithin
    (data.vertexPartition leaf) (mergedPartition data a b) hLeafRefines selected
  have hSumNat : ∑ midBlock ∈ SheetPartition.blocksWithin (data.vertexPartition leaf)
        (mergedPartition data a b) selected,
      (data.edgePartition contracted).blockCountWithin
        (data.vertexPartition leaf) midBlock.1 =
      (SheetPartition.blocksWithin (data.vertexPartition leaf)
        (mergedPartition data a b) selected).card := by
    have : ((∑ midBlock ∈ SheetPartition.blocksWithin (data.vertexPartition leaf)
          (mergedPartition data a b) selected,
        (data.edgePartition contracted).blockCountWithin
          (data.vertexPartition leaf) midBlock.1 : ℕ) : ℤ) =
        ((SheetPartition.blocksWithin (data.vertexPartition leaf)
          (mergedPartition data a b) selected).card : ℤ) := by
      rw [Nat.cast_sum, hSum, hCards]
      rw [hOtherCount] at hForestCount
      push_cast at hForestCount ⊢
      linarith
    exact_mod_cast this
  have hMemBlock : (data.vertexPartition leaf).toBlock sheet ∈
      SheetPartition.blocksWithin (data.vertexPartition leaf)
        (mergedPartition data a b) selected := by
    rw [SheetPartition.mem_blocksWithin]
    refine (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel (data.vertexPartition leaf)
      (mergedPartition data a b) _ selected).mpr ?_
    exact hSheet.trans (hLeafRefines.rel
      ((data.vertexPartition leaf).rel_repr_right sheet))
  have hOne := eq_one_of_sum_eq_card
    (f := fun midBlock : (data.vertexPartition leaf).Blocks ↦
      (data.edgePartition contracted).blockCountWithin
        (data.vertexPartition leaf) midBlock.1)
    (fun midBlock _ ↦ SheetPartition.blockCountWithin_pos _ _ _)
    hSumNat hMemBlock
  rw [← hOne]
  exact blockCountWithin_congr _ (data.vertexPartition leaf)
    ((data.vertexPartition leaf).rel_repr_right sheet)

/-- **A target leaf is impossible above a wall block whose other endpoint
carries a single class.**  Every source vertex above the leaf then carries
exactly one occurrence of the contracted edge, hence has surviving valency
zero, hence *every* occurrence of the contracted edge is dangling --
contradicting `NoDanglingTargetFibres`. -/
private theorem not_leaf
    (selected : (mergedPartition data a b).Blocks) (leaf other : target.V)
    (hLeafEdges : GluingDatum.incidentEdges leaf = {contracted})
    (hLeafRefines : (data.vertexPartition leaf).Refines (mergedPartition data a b))
    (hOtherCount : (data.vertexPartition other).blockCountWithin
      (mergedPartition data a b) selected.1 = 1)
    (hForestCount : ((data.edgePartition contracted).blockCountWithin
        (mergedPartition data a b) selected.1 : ℤ) + 1 =
      ((data.vertexPartition leaf).blockCountWithin
          (mergedPartition data a b) selected.1 : ℤ) +
        ((data.vertexPartition other).blockCountWithin
          (mergedPartition data a b) selected.1 : ℤ))
    (hOffRam : ∀ sheet, ¬ (mergedPartition data a b).Rel selected.1 sheet →
      data.localRamification leaf (WallBlock.ofSheet data leaf sheet) = 0)
    (hConnected : data.Connected) (hNoDangling : NoDanglingTargetFibres data) :
    False := by
  classical
  have hMem : contracted ∈ GluingDatum.incidentEdges leaf := by
    rw [hLeafEdges]
    exact Finset.mem_singleton_self _
  have hZero : ∀ sheet, nonDanglingValency data (data.sourceEndpoint leaf sheet) = 0 := by
    intro sheet
    refine nonDanglingValency_eq_zero_of_leaf data leaf hLeafEdges hConnected sheet ?_
    by_cases hSheet : (mergedPartition data a b).Rel selected.1 sheet
    · exact contracted_count_on_selected data selected leaf other hLeafEdges hLeafRefines
        hOtherCount hForestCount sheet hSheet
    · exact contracted_count_off_selected data leaf hLeafEdges sheet (hOffRam sheet hSheet)
  obtain ⟨sourceEdge, hTarget, hSurvives⟩ := hNoDangling contracted
  exact hSurvives (isDangling_of_leaf data leaf hMem hZero sourceEdge hTarget)

end LeafExclusion

/-! ## §4  A refinement inherits a one-class block -/

section Inherit

variable {degree : ℕ}

/-- If a partition induces a single class inside a coarse block, so does every
partition it refines. -/
private theorem blockCountWithin_eq_one_of_refines
    (fine mid coarse : SheetPartition degree)
    (hFineMid : fine.Refines mid) (hMidCoarse : mid.Refines coarse)
    (coarseBlock : coarse.Blocks)
    (hCount : fine.blockCountWithin coarse coarseBlock.1 = 1) :
    mid.blockCountWithin coarse coarseBlock.1 = 1 := by
  classical
  have hSum := sum_blockCountWithin_trans fine mid coarse hFineMid hMidCoarse coarseBlock
  rw [hCount] at hSum
  have hSumNat : ∑ midBlock ∈ SheetPartition.blocksWithin mid coarse coarseBlock,
      fine.blockCountWithin mid midBlock.1 = 1 := by
    have : ((∑ midBlock ∈ SheetPartition.blocksWithin mid coarse coarseBlock,
        fine.blockCountWithin mid midBlock.1 : ℕ) : ℤ) = (1 : ℤ) := by
      rw [Nat.cast_sum]
      exact hSum
    exact_mod_cast this
  have hLower : (SheetPartition.blocksWithin mid coarse coarseBlock).card * 1 ≤
      ∑ midBlock ∈ SheetPartition.blocksWithin mid coarse coarseBlock,
        fine.blockCountWithin mid midBlock.1 := by
    rw [← smul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ 1
      (fun midBlock _ ↦ SheetPartition.blockCountWithin_pos fine mid midBlock.1)
  rw [hSumNat, mul_one,
    SheetPartition.card_blocksWithin_eq_blockCountWithin mid coarse hMidCoarse
      coarseBlock] at hLower
  have hPos := SheetPartition.blockCountWithin_pos mid coarse coarseBlock.1
  omega

/-- A refinement with the same induced count on a coarse block agrees with the
partition it refines throughout that block. -/
private theorem block_eq_of_blockCountWithin_eq
    (fine mid coarse : SheetPartition degree)
    (hFineMid : fine.Refines mid) (hMidCoarse : mid.Refines coarse)
    (coarseBlock : coarse.Blocks)
    (hEq : fine.blockCountWithin coarse coarseBlock.1 =
      mid.blockCountWithin coarse coarseBlock.1)
    (sheet : Fin degree) (hSheet : coarse.Rel coarseBlock.1 sheet) :
    fine.block sheet = mid.block sheet := by
  classical
  have hSum := sum_blockCountWithin_trans fine mid coarse hFineMid hMidCoarse coarseBlock
  have hCards := SheetPartition.card_blocksWithin_eq_blockCountWithin mid coarse
    hMidCoarse coarseBlock
  have hSumNat : ∑ midBlock ∈ SheetPartition.blocksWithin mid coarse coarseBlock,
      fine.blockCountWithin mid midBlock.1 =
      (SheetPartition.blocksWithin mid coarse coarseBlock).card := by
    have hCast : ((∑ midBlock ∈ SheetPartition.blocksWithin mid coarse coarseBlock,
        fine.blockCountWithin mid midBlock.1 : ℕ) : ℤ) =
        ((SheetPartition.blocksWithin mid coarse coarseBlock).card : ℤ) := by
      rw [Nat.cast_sum, hSum, hCards, hEq]
    exact_mod_cast hCast
  have hMem : mid.toBlock sheet ∈
      SheetPartition.blocksWithin mid coarse coarseBlock := by
    rw [SheetPartition.mem_blocksWithin]
    refine (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel mid coarse _ coarseBlock).mpr ?_
    exact hSheet.trans (hMidCoarse.rel (mid.rel_repr_right sheet))
  have hOne := eq_one_of_sum_eq_card
    (f := fun midBlock : mid.Blocks ↦ fine.blockCountWithin mid midBlock.1)
    (fun midBlock _ ↦ SheetPartition.blockCountWithin_pos _ _ _) hSumNat hMem
  have hCount : fine.blockCountWithin mid sheet = 1 := by
    rw [← hOne]
    exact blockCountWithin_congr _ mid (mid.rel_repr_right sheet)
  exact SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one fine mid hFineMid
    sheet hCount

end Inherit

/-! ## §5  A three-class induced count -/

section Three

variable {d : ℕ}

/-- A partition whose classes inside one coarse block are exactly the classes
of three named sheets contributes exactly three induced blocks there. -/
private theorem blockCountWithin_eq_three (fine wallPartition : SheetPartition d)
    (first second third anchor : Fin d)
    (hFirst : wallPartition.Rel anchor first) (hSecond : wallPartition.Rel anchor second)
    (hThird : wallPartition.Rel anchor third)
    (hCovers : ∀ sheet, wallPartition.Rel anchor sheet →
      fine.Rel first sheet ∨ fine.Rel second sheet ∨ fine.Rel third sheet)
    (hFirstSecond : ¬ fine.Rel first second) (hFirstThird : ¬ fine.Rel first third)
    (hSecondThird : ¬ fine.Rel second third) :
    fine.blockCountWithin wallPartition anchor = 3 := by
  classical
  have hImage : (wallPartition.block anchor).image fine.repr =
      {fine.repr first, fine.repr second, fine.repr third} := by
    ext value
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
      SheetPartition.mem_block_iff]
    constructor
    · rintro ⟨source, hSource, rfl⟩
      rcases hCovers source hSource with hRel | hRel | hRel
      · exact Or.inl (by rw [SheetPartition.rel_iff] at hRel; exact hRel.symm)
      · exact Or.inr (Or.inl (by rw [SheetPartition.rel_iff] at hRel; exact hRel.symm))
      · exact Or.inr (Or.inr (by rw [SheetPartition.rel_iff] at hRel; exact hRel.symm))
    · rintro (rfl | rfl | rfl)
      · exact ⟨first, hFirst, rfl⟩
      · exact ⟨second, hSecond, rfl⟩
      · exact ⟨third, hThird, rfl⟩
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact hFirstSecond (by rw [SheetPartition.rel_iff]; exact h)
      · exact hFirstThird (by rw [SheetPartition.rel_iff]; exact h)),
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      intro h
      exact hSecondThird (by rw [SheetPartition.rel_iff]; exact h)),
    Finset.card_singleton]

end Three

/-! ## §5b  Two coarsenings of one three-class fibre that merge the same pair -/

section Pattern

variable {d : ℕ}

private theorem rel_congr {Q : SheetPartition d} {x y i j : Fin d}
    (hx : Q.Rel x i) (hy : Q.Rel y j) : Q.Rel i j ↔ Q.Rel x y :=
  ⟨fun h ↦ (hx.trans h).trans hy.symm, fun h ↦ hx.symm.trans (h.trans hy)⟩

private theorem iff_symm_rel {P F : SheetPartition d} {x y : Fin d}
    (h : P.Rel x y ↔ F.Rel x y) : P.Rel y x ↔ F.Rel y x :=
  ⟨fun hr ↦ (h.mp hr.symm).symm, fun hr ↦ (h.mpr hr.symm).symm⟩

/-- Two coarsenings of a three-class fibre agree on it as soon as they merge
the same pairs of the three classes. -/
private theorem rel_iff_of_same_pattern (ep P F coarse : SheetPartition d)
    (first second extra anchor : Fin d)
    (hEpP : ep.Refines P) (hEpF : ep.Refines F)
    (hCovers : ∀ sheet, coarse.Rel anchor sheet →
      ep.Rel first sheet ∨ ep.Rel second sheet ∨ ep.Rel extra sheet)
    (h12 : P.Rel first second ↔ F.Rel first second)
    (h13 : P.Rel first extra ↔ F.Rel first extra)
    (h23 : P.Rel second extra ↔ F.Rel second extra)
    {i j : Fin d} (hi : coarse.Rel anchor i) (hj : coarse.Rel anchor j) :
    P.Rel i j ↔ F.Rel i j := by
  rcases hCovers i hi with hI | hI | hI <;> rcases hCovers j hj with hJ | hJ | hJ <;>
    rw [rel_congr (hEpP.rel hI) (hEpP.rel hJ), rel_congr (hEpF.rel hI) (hEpF.rel hJ)]
  · exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  · exact h12
  · exact h13
  · exact iff_symm_rel h12
  · exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  · exact h23
  · exact iff_symm_rel h13
  · exact iff_symm_rel h23
  · exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The block form of `rel_iff_of_same_pattern`. -/
private theorem block_eq_of_same_pattern (ep P F coarse : SheetPartition d)
    (first second extra anchor : Fin d)
    (hEpP : ep.Refines P) (hEpF : ep.Refines F)
    (hPc : P.Refines coarse) (hFc : F.Refines coarse)
    (hCovers : ∀ sheet, coarse.Rel anchor sheet →
      ep.Rel first sheet ∨ ep.Rel second sheet ∨ ep.Rel extra sheet)
    (h12 : P.Rel first second ↔ F.Rel first second)
    (h13 : P.Rel first extra ↔ F.Rel first extra)
    (h23 : P.Rel second extra ↔ F.Rel second extra)
    (sheet : Fin d) (hSheet : coarse.Rel anchor sheet) :
    P.block sheet = F.block sheet := by
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  constructor
  · intro h
    exact (rel_iff_of_same_pattern ep P F coarse first second extra anchor hEpP hEpF hCovers
      h12 h13 h23 hSheet (hSheet.trans (hPc.rel h))).mp h
  · intro h
    exact (rel_iff_of_same_pattern ep P F coarse first second extra anchor hEpP hEpF hCovers
      h12 h13 h23 hSheet (hSheet.trans (hFc.rel h))).mpr h

end Pattern

/-! ## §6  The incoming `w2P` wall -/

section W2P

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  {selected : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (profile : W2R2SourceProfile.SourceProfile (contractDatum data hc hab hOne) star selected)
  (shape : Shape profile)

/-- The incoming occurrence carrying the doubled direction `t₂`, which
Figure 35's members keep at the retained wall endpoint. -/
noncomputable def retainedOccurrence : target.edges :=
  unfoldEdge hc hab hOne (star.edge profile.doubleLabel)

/-- The incoming occurrence carrying the single direction `t₃`, which
Figure 35's members send to the fresh endpoint. -/
noncomputable def isolatedOccurrence : target.edges :=
  unfoldEdge hc hab hOne (star.edge profile.singleLabel)

theorem retainedOccurrence_ne_contracted :
    retainedOccurrence data hc hab hOne star profile ≠ contracted :=
  unfoldEdge_ne_contracted hc hab hOne _

theorem isolatedOccurrence_ne_contracted :
    isolatedOccurrence data hc hab hOne star profile ≠ contracted :=
  unfoldEdge_ne_contracted hc hab hOne _

theorem retainedOccurrence_edgePartition :
    data.edgePartition (retainedOccurrence data hc hab hOne star profile) =
      (contractDatum data hc hab hOne).edgePartition
        (star.edge profile.doubleLabel) := rfl

theorem isolatedOccurrence_edgePartition :
    data.edgePartition (isolatedOccurrence data hc hab hOne star profile) =
      (contractDatum data hc hab hOne).edgePartition
        (star.edge profile.singleLabel) := rfl

/-- Each wall occurrence unfolds to an occurrence at one of the two original
endpoints of the contracted edge. -/
theorem starOccurrence_mem_union (label : Fin 2) :
    unfoldEdge hc hab hOne (star.edge label) ∈
      GluingDatum.incidentEdges a ∪ GluingDatum.incidentEdges b :=
  unfoldEdge_mem_incidentEdges_union hc hab hOne (star.edge_mem_incidentEdges label)


/-- **`IncomingSourceCases.W2.Classification.p`'s `deleted_target` field is
`W2PSourceCandidates.Shape`.**  Cardinality P is that single field, so the
classifier's `w2P` payload is exactly this module's bundle. -/
theorem shape_of_w2P
    (hDeleted : profile.deleted.edge.1.1.1 = star.edge profile.doubleLabel) :
    Shape profile := ⟨hDeleted⟩

/-! ### The four induced counts above `A₀` -/

include fullDim hForest shape

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
/-- **`t₃` induces a single class above `A₀`.**  This is Cardinality P's
`k₃ = |A₀|`, read through `W2PSurvival.single_blockCountWithin`. -/
theorem isolated_count :
    (data.edgePartition (isolatedOccurrence data hc hab hOne star profile)).blockCountWithin
      (mergedPartition data a b) selected.1 = 1 := by
  rw [← contractDatum_vertexPartition_merge data hc hab hOne]
  exact W2PSurvival.single_blockCountWithin shape selected.1 rfl

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
/-- **`t₂` induces three classes above `A₀`**: `e₁`, `e₂` and the dangling
`e₄`, which Cardinality P puts above `t₂`. -/
theorem retained_count :
    (data.edgePartition (retainedOccurrence data hc hab hOne star profile)).blockCountWithin
      (mergedPartition data a b) selected.1 = 3 := by
  rw [← contractDatum_vertexPartition_merge data hc hab hOne]
  exact blockCountWithin_eq_three _ _ (firstSheet profile) (secondSheet profile)
    (extraSheet profile) selected.1 (firstSheet_rel profile) (secondSheet_rel profile)
    (extraSheet_rel profile) (endpointPartition_covers shape)
    (first_second_separate profile) (first_extra_separate shape)
    (second_extra_separate shape)

/-! ### Off the distinguished block both endpoints are unramified -/

omit shape in
/-- Away from `A₀` the wall carries no change, and forest additivity pushes
that down to both original endpoints. -/
theorem background_endpoints_localRamification_eq_zero
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (sheet : Fin degree)
    (hSheet : ¬ (mergedPartition data a b).Rel selected.1 sheet) :
    data.localRamification a (WallBlock.ofSheet data a sheet) = 0 ∧
      data.localRamification b (WallBlock.ofSheet data b sheet) = 0 := by
  have hRel : (mergedPartition data a b).Rel
      (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ sheet).1 sheet := by
    show (mergedPartition data a b).Rel
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) sheet
    rw [contractDatum_vertexPartition_merge data hc hab hOne]
    exact (mergedPartition data a b).rel_repr_left sheet
  have hNe : WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ sheet ≠
      selected := by
    intro hEq
    rw [hEq] at hRel
    exact hSheet hRel
  exact W3Nd2IncomingBackground.AnyBlock.background_localRamification_endpoints_eq_zero
    data hc hab hOne fullDim hForest (hBackground _ hNe) sheet hRel

/-! ### The two leaf orientations are impossible -/

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
/-- The `t₃` occurrence meets whichever original endpoint is not a leaf. -/
private theorem isolated_mem_incidentEdges (vertex other : target.V)
    (hUnion : isolatedOccurrence data hc hab hOne star profile ∈
      GluingDatum.incidentEdges vertex ∪ GluingDatum.incidentEdges other)
    (hLeaf : GluingDatum.incidentEdges vertex = {contracted}) :
    isolatedOccurrence data hc hab hOne star profile ∈
      GluingDatum.incidentEdges other := by
  rcases Finset.mem_union.mp hUnion with hLeft | hRight
  · rw [hLeaf, Finset.mem_singleton] at hLeft
    exact absurd hLeft (isolatedOccurrence_ne_contracted data hc hab hOne star profile)
  · exact hRight

/-- **`a` is not a leaf at a `w2P` wall.** -/
theorem not_leaf_left
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) : False := by
  classical
  obtain ⟨edge, hEdges⟩ := Finset.card_eq_one.mp hLeaf
  have hContracted : contracted = edge := by
    have hMem := contracted_mem_incidentEdges_left hc
    rw [hEdges, Finset.mem_singleton] at hMem
    exact hMem
  have hLeafEdges : GluingDatum.incidentEdges a = {contracted} := by
    rw [hEdges, hContracted]
  have hIsolatedAt : isolatedOccurrence data hc hab hOne star profile ∈
      GluingDatum.incidentEdges b :=
    isolated_mem_incidentEdges data hc hab hOne star profile a b
      (starOccurrence_mem_union hc hab hOne star profile.singleLabel) hLeafEdges
  refine not_leaf data (M11IncomingPartitions.selectedMergedBlock data hc hab hOne selected)
    a b hLeafEdges (vertexPartition_refines_mergedPartition data a b) ?_
    (contractionForest_count data hc hForest
      (M11IncomingPartitions.selectedMergedBlock data hc hab hOne selected)) ?_
    fullDim.valid.1 fullDim.noDanglingTargetFibres
  · exact blockCountWithin_eq_one_of_refines _ _ _
      (refines_of_mem_incidentEdges data hIsolatedAt)
      (vertexPartition_refines_mergedPartition_right data a b)
      (M11IncomingPartitions.selectedMergedBlock data hc hab hOne selected)
      (isolated_count data hc hab hOne star profile shape)
  · exact fun sheet hSheet ↦ (background_endpoints_localRamification_eq_zero data hc hab hOne
      fullDim hForest hBackground sheet hSheet).1

/-- **`b` is not a leaf at a `w2P` wall.** -/
theorem not_leaf_right
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeaf : (GluingDatum.incidentEdges b).card = 1) : False := by
  classical
  obtain ⟨edge, hEdges⟩ := Finset.card_eq_one.mp hLeaf
  have hContracted : contracted = edge := by
    have hMem := contracted_mem_incidentEdges_right hc
    rw [hEdges, Finset.mem_singleton] at hMem
    exact hMem
  have hLeafEdges : GluingDatum.incidentEdges b = {contracted} := by
    rw [hEdges, hContracted]
  have hIsolatedAt : isolatedOccurrence data hc hab hOne star profile ∈
      GluingDatum.incidentEdges a := by
    refine isolated_mem_incidentEdges data hc hab hOne star profile b a ?_ hLeafEdges
    exact Finset.mem_union.mpr
      ((Finset.mem_union.mp
        (starOccurrence_mem_union hc hab hOne star profile.singleLabel)).symm)
  refine not_leaf data (M11IncomingPartitions.selectedMergedBlock data hc hab hOne selected)
    b a hLeafEdges (vertexPartition_refines_mergedPartition_right data a b) ?_ ?_ ?_
    fullDim.valid.1 fullDim.noDanglingTargetFibres
  · exact blockCountWithin_eq_one_of_refines _ _ _
      (refines_of_mem_incidentEdges data hIsolatedAt)
      (vertexPartition_refines_mergedPartition data a b)
      (M11IncomingPartitions.selectedMergedBlock data hc hab hOne selected)
      (isolated_count data hc hab hOne star profile shape)
  · have h := contractionForest_count data hc hForest
      (M11IncomingPartitions.selectedMergedBlock data hc hab hOne selected)
    linarith
  · exact fun sheet hSheet ↦ (background_endpoints_localRamification_eq_zero data hc hab hOne
      fullDim hForest hBackground sheet hSheet).2

/-- **The incoming `w2P` wall is `(2,2)`.**  Both original endpoints of the
contracted edge are divalent; the leaf orientations `(1,3)` and `(3,1)` that
`IncomingW2TargetPlacement.placement_of_twoStar` leaves open do not occur. -/
theorem divalent_endpoints
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0) :
    (GluingDatum.incidentEdges a).card = 2 ∧ (GluingDatum.incidentEdges b).card = 2 := by
  rcases IncomingW2TargetPlacement.placement_of_twoStar data hc hab hOne fullDim.valid
      fullDim.changeMinimal star with
    ⟨hLeft, _, _, _, _, _⟩ | ⟨_, hRight, _, _, _, _⟩ | ⟨hLeft, hRight, _, _, _⟩
  · exact absurd hLeft (fun h ↦ not_leaf_left data hc hab hOne fullDim hForest star profile
      shape hBackground h)
  · exact absurd hRight (fun h ↦ not_leaf_right data hc hab hOne fullDim hForest star profile
      shape hBackground h)
  · exact ⟨hLeft, hRight⟩


/-! ### §7  Which restored endpoint carries `t₂`

Figure 35 draws `u` as the `t₂` endpoint and `v` as the `t₃` endpoint.  The
incoming cover does not know that labelling: the contracted edge's two ends are
`a` and `b`, and which of them is `u` is read off the reconstructed side
predicate.  Both branches occur, and nothing below assumes either. -/

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
/-- The support half of a placement, from the two values at the star. -/
theorem support_of_star_values
    (twoStar : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (hZero : IncomingTargetExpansion.right hc hab hOne (twoStar.edge 0) = false)
    (hOneEdge : IncomingTargetExpansion.right hc hab hOne (twoStar.edge 1) = true) :
    ∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = twoStar.right edge := by
  intro edge hAt
  obtain ⟨label, hLabel⟩ := twoStar.label.surjective ⟨edge, hAt⟩
  have hEdge : twoStar.edge label = edge := congrArg Subtype.val hLabel
  rw [← hEdge]
  have hCases : label = 0 ∨ label = 1 := by omega
  rcases hCases with rfl | rfl
  · exact hZero.trans (TwoStar.right_edge_zero twoStar).symm
  · exact hOneEdge.trans (TwoStar.right_edge_one twoStar).symm

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
/-- The `t₂` occurrence is on the retained side of every Figure 35 member. -/
theorem orientedStar_right_double :
    (orientedStar profile).right (star.edge profile.doubleLabel) = false := by
  rw [← orientedStar_edge_zero profile]
  exact TwoStar.right_edge_zero _

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
/-- The `t₃` occurrence is on the fresh side of every Figure 35 member. -/
theorem orientedStar_right_single :
    (orientedStar profile).right (star.edge profile.singleLabel) = true := by
  rw [← orientedStar_edge_one profile]
  exact TwoStar.right_edge_one _

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
/-- **Every Figure 35 member's wall-side assignment is the oriented star.**
All three members are built by `W2PSourceCandidates.pattern` over the same
`M11SourceCandidates.joinedBackground`, so none of them can distinguish the two
restored endpoints. -/
theorem members_right (position : Fin 3) :
    (W2PCommonBalance.members profile shape position).right =
      (orientedStar profile).right := by
  fin_cases position <;> rfl

/-- **The placement of every Figure 35 member.**  The incoming wall is `(2,2)`
by `divalent_endpoints`, and a `(2,2)` wall restores the two star occurrences
to opposite endpoints, which is exactly what the oriented star asks. -/
theorem member_placement
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0) :
    IncomingMatchingCore.Placement hc hab hOne (orientedStar profile).right :=
  M11IncomingTargetNormalization.joinedPlacement hc hab hOne (orientedStar profile)
    (divalent_endpoints data hc hab hOne fullDim hForest star profile shape hBackground).1
    (divalent_endpoints data hc hab hOne fullDim hForest star profile shape hBackground).2

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
/-- The restored endpoint carrying the `t₂` occurrence -- Figure 35's `u`. -/
noncomputable def doubleEnd : target.V :=
  if IncomingTargetExpansion.right hc hab hOne (star.edge profile.doubleLabel) = true
    then b else a

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
/-- The restored endpoint carrying the `t₃` occurrence -- Figure 35's `v`. -/
noncomputable def singleEnd : target.V :=
  if IncomingTargetExpansion.right hc hab hOne (star.edge profile.doubleLabel) = true
    then a else b

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
@[simp] theorem doubleEnd_of_false
    (hFalse : IncomingTargetExpansion.right hc hab hOne
      (star.edge profile.doubleLabel) = false) :
    doubleEnd data hc hab hOne star profile = a := by
  simp only [doubleEnd, hFalse, Bool.false_eq_true, ite_false]

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
@[simp] theorem singleEnd_of_false
    (hFalse : IncomingTargetExpansion.right hc hab hOne
      (star.edge profile.doubleLabel) = false) :
    singleEnd data hc hab hOne star profile = b := by
  simp only [singleEnd, hFalse, Bool.false_eq_true, ite_false]

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
@[simp] theorem doubleEnd_of_true
    (hTrue : IncomingTargetExpansion.right hc hab hOne
      (star.edge profile.doubleLabel) = true) :
    doubleEnd data hc hab hOne star profile = b := by
  simp only [doubleEnd, hTrue, ite_true]

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
@[simp] theorem singleEnd_of_true
    (hTrue : IncomingTargetExpansion.right hc hab hOne
      (star.edge profile.doubleLabel) = true) :
    singleEnd data hc hab hOne star profile = a := by
  simp only [singleEnd, hTrue, ite_true]

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
theorem ends_cases :
    (doubleEnd data hc hab hOne star profile = a ∧
        singleEnd data hc hab hOne star profile = b) ∨
      (doubleEnd data hc hab hOne star profile = b ∧
        singleEnd data hc hab hOne star profile = a) := by
  unfold doubleEnd singleEnd
  by_cases hTrue : IncomingTargetExpansion.right hc hab hOne
    (star.edge profile.doubleLabel) = true
  · exact Or.inr ⟨ite_eq_left hTrue, ite_eq_left hTrue⟩
  · exact Or.inl ⟨ite_eq_right hTrue, ite_eq_right hTrue⟩

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
/-- The `t₂` occurrence of the incoming target meets `doubleEnd`. -/
theorem retained_mem_doubleEnd :
    retainedOccurrence data hc hab hOne star profile ∈
      GluingDatum.incidentEdges (doubleEnd data hc hab hOne star profile) := by
  unfold doubleEnd retainedOccurrence
  by_cases hTrue : IncomingTargetExpansion.right hc hab hOne
    (star.edge profile.doubleLabel) = true
  · rw [ite_eq_left hTrue]
    exact (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp hTrue
  · rw [ite_eq_right hTrue]
    exact (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
      (star.edge_mem_incidentEdges profile.doubleLabel)).mp
      (by simpa using hTrue)

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
/-- The contracted occurrence meets both restored endpoints. -/
theorem contracted_mem_doubleEnd :
    contracted ∈ GluingDatum.incidentEdges (doubleEnd data hc hab hOne star profile) := by
  rcases ends_cases data hc hab hOne star profile with ⟨hDouble, _⟩ | ⟨hDouble, _⟩
  · rw [hDouble]; exact contracted_mem_incidentEdges_left hc
  · rw [hDouble]; exact contracted_mem_incidentEdges_right hc

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
theorem contracted_mem_singleEnd :
    contracted ∈ GluingDatum.incidentEdges (singleEnd data hc hab hOne star profile) := by
  rcases ends_cases data hc hab hOne star profile with ⟨_, hSingle⟩ | ⟨_, hSingle⟩
  · rw [hSingle]; exact contracted_mem_incidentEdges_right hc
  · rw [hSingle]; exact contracted_mem_incidentEdges_left hc

/-- At a `(2,2)` wall the two star occurrences are restored to opposite
endpoints: three distinct occurrences cannot meet a divalent vertex. -/
theorem star_values_ne
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0) :
    IncomingTargetExpansion.right hc hab hOne (star.edge profile.doubleLabel) ≠
      IncomingTargetExpansion.right hc hab hOne (star.edge profile.singleLabel) := by
  have hDiv := divalent_endpoints data hc hab hOne fullDim hForest star profile shape hBackground
  have h := IncomingW2TargetPlacement.right_star_ne_of_divalent hc hab hOne
    (orientedStar profile) hDiv.1 hDiv.2
  rwa [orientedStar_edge_zero profile, orientedStar_edge_one profile] at h

/-- **The `if` of `M11IncomingOuterPartitions.transported_endpointPartitions`,
decided.**  The normalization leaves the two expanded ends in place exactly
when the `t₂` occurrence is restored to `a`. -/
theorem support_iff
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0) :
    (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge =
          (orientedStar profile).right edge) ↔
      IncomingTargetExpansion.right hc hab hOne (star.edge profile.doubleLabel) = false := by
  constructor
  · intro hSupport
    have hValue := hSupport _ (star.edge_mem_incidentEdges profile.doubleLabel)
    rwa [orientedStar_right_double data hc hab hOne star profile] at hValue
  · intro hFalse
    have hNe := star_values_ne data hc hab hOne fullDim hForest star profile shape hBackground
    have hTrue : IncomingTargetExpansion.right hc hab hOne
        (star.edge profile.singleLabel) = true := by
      by_contra hContra
      have hContra' : IncomingTargetExpansion.right hc hab hOne
          (star.edge profile.singleLabel) = false := by simpa using hContra
      exact hNe (hFalse.trans hContra'.symm)
    refine support_of_star_values hc hab hOne (orientedStar profile) ?_ ?_
    · rw [orientedStar_edge_zero profile]
      exact hFalse
    · rw [orientedStar_edge_one profile]
      exact hTrue

/-- The `t₃` occurrence of the incoming target meets `singleEnd`. -/
theorem isolated_mem_singleEnd
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0) :
    isolatedOccurrence data hc hab hOne star profile ∈
      GluingDatum.incidentEdges (singleEnd data hc hab hOne star profile) := by
  have hNe := star_values_ne data hc hab hOne fullDim hForest star profile shape hBackground
  unfold singleEnd isolatedOccurrence
  by_cases hTrue : IncomingTargetExpansion.right hc hab hOne
    (star.edge profile.doubleLabel) = true
  · rw [ite_eq_left hTrue]
    have hSingleFalse : IncomingTargetExpansion.right hc hab hOne
        (star.edge profile.singleLabel) = false := by
      by_contra hContra
      have hContra' : IncomingTargetExpansion.right hc hab hOne
          (star.edge profile.singleLabel) = true := by simpa using hContra
      exact hNe (hTrue.trans hContra'.symm)
    exact (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
      (star.edge_mem_incidentEdges profile.singleLabel)).mp hSingleFalse
  · rw [ite_eq_right hTrue]
    have hFalse : IncomingTargetExpansion.right hc hab hOne
        (star.edge profile.doubleLabel) = false := by simpa using hTrue
    have hSingleTrue : IncomingTargetExpansion.right hc hab hOne
        (star.edge profile.singleLabel) = true := by
      by_contra hContra
      have hContra' : IncomingTargetExpansion.right hc hab hOne
          (star.edge profile.singleLabel) = false := by simpa using hContra
      exact hNe (hFalse.trans hContra'.symm)
    exact (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp hSingleTrue

/-- Both restored endpoints are divalent, so in particular `doubleEnd` is. -/
theorem doubleEnd_divalent
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0) :
    (GluingDatum.incidentEdges (doubleEnd data hc hab hOne star profile)).card = 2 := by
  have hDiv := divalent_endpoints data hc hab hOne fullDim hForest star profile shape hBackground
  rcases ends_cases data hc hab hOne star profile with ⟨hDouble, _⟩ | ⟨hDouble, _⟩
  · rw [hDouble]; exact hDiv.1
  · rw [hDouble]; exact hDiv.2

theorem singleEnd_divalent
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0) :
    (GluingDatum.incidentEdges (singleEnd data hc hab hOne star profile)).card = 2 := by
  have hDiv := divalent_endpoints data hc hab hOne fullDim hForest star profile shape hBackground
  rcases ends_cases data hc hab hOne star profile with ⟨_, hSingle⟩ | ⟨_, hSingle⟩
  · rw [hSingle]; exact hDiv.2
  · rw [hSingle]; exact hDiv.1


/-! ### §8  Off `A₀` every partition in sight is the whole wall block

At a `(2,2)` W2 wall **both** restored endpoints are divalent, so both
orientations of `W3Nd2IncomingNormalization.AnyBlock` apply at once and the
`r = 0` census is symmetric: `a`, `b` and the contracted occurrence are all
joined on every background block. -/

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
private theorem merged_rel_ofSheet (sheet : Fin degree) :
    (mergedPartition data a b).Rel
      (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ sheet).1 sheet := by
  show (mergedPartition data a b).Rel
    (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) sheet
  rw [contractDatum_vertexPartition_merge data hc hab hOne]
  exact (mergedPartition data a b).rel_repr_left sheet

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
private theorem ofSheet_ne_selected {sheet : Fin degree}
    (hOff : ¬ (mergedPartition data a b).Rel selected.1 sheet) :
    WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ sheet ≠ selected := by
  intro hEq
  exact hOff (hEq ▸ merged_rel_ofSheet data hc hab hOne sheet)

omit shape in
/-- **`a` carries the whole wall block off `A₀`.** -/
theorem background_joined_left
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hRight : (GluingDatum.incidentEdges b).card = 2)
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel selected.1 sheet) :
    (data.vertexPartition a).block sheet = (mergedPartition data a b).block sheet := by
  have hJoined :=
    (W3Nd2IncomingNormalization.AnyBlock.background_trivalent_joined_of_right_divalent
      data hc hab hOne fullDim hForest hRight
      (hBackground _ (ofSheet_ne_selected data hc hab hOne hOff))).2
  have hRel := merged_rel_ofSheet data hc hab hOne sheet
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact ⟨fun h ↦ (vertexPartition_refines_mergedPartition data a b).rel h,
    fun h ↦ hJoined sheet other hRel (hRel.trans h)⟩

omit shape in
/-- **`b` carries the whole wall block off `A₀`.** -/
theorem background_joined_right
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel selected.1 sheet) :
    (data.vertexPartition b).block sheet = (mergedPartition data a b).block sheet := by
  have hJoined :=
    (W3Nd2IncomingNormalization.AnyBlock.background_trivalent_joined_of_left_divalent
      data hc hab hOne fullDim hForest hLeft
      (hBackground _ (ofSheet_ne_selected data hc hab hOne hOff))).2
  have hRel := merged_rel_ofSheet data hc hab hOne sheet
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact ⟨fun h ↦ (vertexPartition_refines_mergedPartition_right data a b).rel h,
    fun h ↦ hJoined sheet other hRel (hRel.trans h)⟩

omit shape in
/-- **Every occurrence at the divalent `a` carries `a`'s own class off `A₀`.** -/
theorem background_edge_block_left
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges a)
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel selected.1 sheet) :
    (data.edgePartition edge).block sheet = (data.vertexPartition a).block sheet := by
  have hIff := W3Nd2IncomingNormalization.AnyBlock.background_edge_rel_iff_of_left_divalent
    data hc hab hOne fullDim hForest hLeft
    (hBackground _ (ofSheet_ne_selected data hc hab hOne hOff)) edge hEdge sheet
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact hIff other (merged_rel_ofSheet data hc hab hOne sheet)

/-- **Off `A₀` the `t₂` endpoint carries the whole wall block.** -/
theorem background_block_doubleEnd
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel selected.1 sheet) :
    (data.vertexPartition (doubleEnd data hc hab hOne star profile)).block sheet =
      (mergedPartition data a b).block sheet := by
  have hDiv := divalent_endpoints data hc hab hOne fullDim hForest star profile shape hBackground
  rcases ends_cases data hc hab hOne star profile with ⟨hDouble, _⟩ | ⟨hDouble, _⟩
  · rw [hDouble]
    exact background_joined_left data hc hab hOne fullDim hForest hBackground hDiv.2
      sheet hOff
  · rw [hDouble]
    exact background_joined_right data hc hab hOne fullDim hForest hBackground hDiv.1
      sheet hOff

/-- **Off `A₀` the `t₃` endpoint carries the whole wall block.** -/
theorem background_block_singleEnd
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel selected.1 sheet) :
    (data.vertexPartition (singleEnd data hc hab hOne star profile)).block sheet =
      (mergedPartition data a b).block sheet := by
  have hDiv := divalent_endpoints data hc hab hOne fullDim hForest star profile shape hBackground
  rcases ends_cases data hc hab hOne star profile with ⟨_, hSingle⟩ | ⟨_, hSingle⟩
  · rw [hSingle]
    exact background_joined_right data hc hab hOne fullDim hForest hBackground hDiv.1
      sheet hOff
  · rw [hSingle]
    exact background_joined_left data hc hab hOne fullDim hForest hBackground hDiv.2
      sheet hOff

/-- **Off `A₀` the contracted occurrence carries the whole wall block.** -/
theorem background_block_contracted
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel selected.1 sheet) :
    (data.edgePartition contracted).block sheet = (mergedPartition data a b).block sheet := by
  have hDiv := divalent_endpoints data hc hab hOne fullDim hForest star profile shape hBackground
  refine (background_edge_block_left data hc hab hOne fullDim hForest hBackground
    hDiv.1 contracted (contracted_mem_incidentEdges_left hc) sheet hOff).trans ?_
  exact background_joined_left data hc hab hOne fullDim hForest hBackground hDiv.2
    sheet hOff


/-! ### §9  The selected-class census: `A₀` splits in two at the `t₂` endpoint

`k₃ = |A₀|` gives the `t₃` endpoint a single class above `A₀`, so the forest
identity reads `c = p` with `c` the number of contracted classes and `p` the
number of `t₂`-endpoint classes.  Change-minimality puts one unit of change at
each restored endpoint of a `(2,2)` wall, and the three `t₂` classes then force
`p = 2`: `A₀` is cut in two at `u`, exactly as Figure 35's three members cut
it. -/

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
private theorem vertexPartition_refines_merged (vertex : target.V)
    (hVertex : vertex = a ∨ vertex = b) :
    (data.vertexPartition vertex).Refines (mergedPartition data a b) := by
  rcases hVertex with hEq | hEq
  · rw [hEq]
    exact vertexPartition_refines_mergedPartition data a b
  · rw [hEq]
    exact vertexPartition_refines_mergedPartition_right data a b

/-- **The `t₃` endpoint has a single class above `A₀`.** -/
theorem singleEnd_count
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0) :
    (data.vertexPartition (singleEnd data hc hab hOne star profile)).blockCountWithin
      (mergedPartition data a b) selected.1 = 1 := by
  refine blockCountWithin_eq_one_of_refines _ _ _
    (refines_of_mem_incidentEdges data
      (isolated_mem_singleEnd data hc hab hOne fullDim hForest star profile shape hBackground))
    (vertexPartition_refines_merged data _
      (by rcases ends_cases data hc hab hOne star profile with ⟨_, h⟩ | ⟨_, h⟩
          · exact Or.inr h
          · exact Or.inl h))
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne selected)
    (isolated_count data hc hab hOne star profile shape)

/-- **The `t₃` endpoint carries the whole of `A₀`.** -/
theorem singleEnd_block
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (sheet : Fin degree) (hSheet : (mergedPartition data a b).Rel selected.1 sheet) :
    (data.vertexPartition (singleEnd data hc hab hOne star profile)).block sheet =
      (mergedPartition data a b).block sheet := by
  refine SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ _
    (vertexPartition_refines_merged data _
      (by rcases ends_cases data hc hab hOne star profile with ⟨_, h⟩ | ⟨_, h⟩
          · exact Or.inr h
          · exact Or.inl h)) sheet ?_
  rw [← blockCountWithin_congr _ (mergedPartition data a b) hSheet]
  exact singleEnd_count data hc hab hOne fullDim hForest star profile shape hBackground

/-- **Change-minimality splits the wall's two units one-one.** -/
theorem targetChange_eq_one
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0) :
    data.targetChange a = 1 ∧ data.targetChange b = 1 := by
  rcases IncomingW2TargetPlacement.placement_of_twoStar data hc hab hOne fullDim.valid
      fullDim.changeMinimal star with
    ⟨hLeft, _, _, _, _, _⟩ | ⟨_, hRight, _, _, _, _⟩ | ⟨_, _, hChangeA, hChangeB, _⟩
  · exact absurd hLeft (fun h ↦ not_leaf_left data hc hab hOne fullDim hForest star profile
      shape hBackground h)
  · exact absurd hRight (fun h ↦ not_leaf_right data hc hab hOne fullDim hForest star profile
      shape hBackground h)
  · exact ⟨hChangeA, hChangeB⟩

/-- The whole unit of change at the `t₂` endpoint sits above `A₀`. -/
theorem sum_localRamification_doubleEnd
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0) :
    (∑ blockAbove ∈ SheetPartition.blocksWithin
        (data.vertexPartition (doubleEnd data hc hab hOne star profile))
        (mergedPartition data a b)
        (M11IncomingPartitions.selectedMergedBlock data hc hab hOne selected),
      data.localRamification (doubleEnd data hc hab hOne star profile) blockAbove) = 1 := by
  classical
  have hEnds : doubleEnd data hc hab hOne star profile = a ∨
      doubleEnd data hc hab hOne star profile = b := by
    rcases ends_cases data hc hab hOne star profile with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hChange : data.targetChange (doubleEnd data hc hab hOne star profile) = 1 := by
    have h := targetChange_eq_one data hc hab hOne fullDim hForest star profile shape hBackground
    rcases hEnds with hEq | hEq
    · rw [hEq]; exact h.1
    · rw [hEq]; exact h.2
  have hRamEnd : ∀ sheet : Fin degree, ¬ (mergedPartition data a b).Rel selected.1 sheet →
      data.localRamification (doubleEnd data hc hab hOne star profile)
        (WallBlock.ofSheet data (doubleEnd data hc hab hOne star profile) sheet) = 0 := by
    intro sheet hOff
    have hRam := background_endpoints_localRamification_eq_zero data hc hab hOne fullDim
      hForest hBackground sheet hOff
    rcases ends_cases data hc hab hOne star profile with ⟨hEq, _⟩ | ⟨hEq, _⟩
    · rw [hEq]; exact hRam.1
    · rw [hEq]; exact hRam.2
  have hZero : ∀ blockAbove ∈ (Finset.univ :
      Finset (data.vertexPartition (doubleEnd data hc hab hOne star profile)).Blocks),
      blockAbove ∉ SheetPartition.blocksWithin
        (data.vertexPartition (doubleEnd data hc hab hOne star profile))
        (mergedPartition data a b)
        (M11IncomingPartitions.selectedMergedBlock data hc hab hOne selected) →
      data.localRamification (doubleEnd data hc hab hOne star profile) blockAbove = 0 := by
    intro blockAbove _ hNotMem
    have hOff : ¬ (mergedPartition data a b).Rel selected.1 blockAbove.1 := by
      intro hRel
      exact hNotMem (by
        rw [SheetPartition.mem_blocksWithin]
        exact (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel _ (mergedPartition data a b)
          blockAbove (M11IncomingPartitions.selectedMergedBlock data hc hab hOne selected)).mpr
          hRel)
    have hBlock : WallBlock.ofSheet data (doubleEnd data hc hab hOne star profile)
        blockAbove.1 = blockAbove := Subtype.ext blockAbove.2
    have hRam := hRamEnd blockAbove.1 hOff
    rwa [hBlock] at hRam
  rw [Finset.sum_subset (Finset.subset_univ _) hZero]
  exact hChange


/-- **The star of the `t₂` endpoint**: the contracted occurrence and the `t₂`
occurrence, and nothing else. -/
theorem incidentEdges_doubleEnd
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0) :
    GluingDatum.incidentEdges (doubleEnd data hc hab hOne star profile) =
      {contracted, retainedOccurrence data hc hab hOne star profile} := by
  classical
  have hNe : contracted ≠ retainedOccurrence data hc hab hOne star profile :=
    fun h ↦ retainedOccurrence_ne_contracted data hc hab hOne star profile h.symm
  have hSub : ({contracted, retainedOccurrence data hc hab hOne star profile} :
      Finset target.edges) ⊆ GluingDatum.incidentEdges
        (doubleEnd data hc hab hOne star profile) := by
    intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · exact contracted_mem_doubleEnd data hc hab hOne star profile
    · rw [Finset.mem_singleton.mp hEdge]
      exact retained_mem_doubleEnd data hc hab hOne star profile
  refine (Finset.eq_of_subset_of_card_le hSub ?_).symm
  rw [doubleEnd_divalent data hc hab hOne fullDim hForest star profile shape hBackground,
    Finset.card_insert_of_notMem (by simpa using hNe), Finset.card_singleton]

/-- **`A₀` is cut in two at the `t₂` endpoint, and the contracted occurrence
cuts it the same way.**  The forest identity gives `c = p`, the one unit of
change at the `t₂` endpoint gives `c + 3 - 2p = 1`, and the two together
give `p = c = 2`. -/
theorem doubleEnd_contracted_counts
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0) :
    (data.vertexPartition (doubleEnd data hc hab hOne star profile)).blockCountWithin
        (mergedPartition data a b) selected.1 = 2 ∧
      (data.edgePartition contracted).blockCountWithin
        (mergedPartition data a b) selected.1 = 2 := by
  classical
  have hRefines : (data.vertexPartition (doubleEnd data hc hab hOne star profile)).Refines
      (mergedPartition data a b) :=
    vertexPartition_refines_merged data _
      (by rcases ends_cases data hc hab hOne star profile with ⟨h, _⟩ | ⟨h, _⟩
          · exact Or.inl h
          · exact Or.inr h)
  have hSingle := singleEnd_count data hc hab hOne fullDim hForest star profile shape hBackground
  have hForestCount : ((data.edgePartition contracted).blockCountWithin
        (mergedPartition data a b) selected.1 : ℤ) + 1 =
      ((data.vertexPartition a).blockCountWithin
          (mergedPartition data a b) selected.1 : ℤ) +
        ((data.vertexPartition b).blockCountWithin
          (mergedPartition data a b) selected.1 : ℤ) :=
    contractionForest_count data hc hForest
      (M11IncomingPartitions.selectedMergedBlock data hc hab hOne selected)
  have hPair : ((data.edgePartition contracted).blockCountWithin
        (mergedPartition data a b) selected.1 : ℤ) + 1 =
      ((data.vertexPartition (doubleEnd data hc hab hOne star profile)).blockCountWithin
          (mergedPartition data a b) selected.1 : ℤ) +
        ((data.vertexPartition (singleEnd data hc hab hOne star profile)).blockCountWithin
          (mergedPartition data a b) selected.1 : ℤ) := by
    rcases ends_cases data hc hab hOne star profile with ⟨hDouble, hSingleEq⟩ |
      ⟨hDouble, hSingleEq⟩
    · rw [hDouble, hSingleEq]
      exact hForestCount
    · rw [hDouble, hSingleEq]
      linarith
  have hNePair : contracted ≠ retainedOccurrence data hc hab hOne star profile :=
    fun h ↦ retainedOccurrence_ne_contracted data hc hab hOne star profile h.symm
  have hCardPair : (({contracted, retainedOccurrence data hc hab hOne star profile} :
      Finset target.edges).card : ℤ) = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hNePair), Finset.card_singleton]
    norm_num
  have hSum0 := sum_localRamification_blocksWithin data
    (doubleEnd data hc hab hOne star profile) (mergedPartition data a b) hRefines
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne selected)
  rw [incidentEdges_doubleEnd data hc hab hOne fullDim hForest star profile shape hBackground,
    Finset.sum_pair hNePair,
    SheetPartition.card_blocksWithin_eq_blockCountWithin _ (mergedPartition data a b)
      hRefines (M11IncomingPartitions.selectedMergedBlock data hc hab hOne selected)] at hSum0
  have hSum1 : (1 : ℤ) =
      ((data.edgePartition contracted).blockCountWithin
          (mergedPartition data a b) selected.1 : ℤ) +
        ((data.edgePartition (retainedOccurrence data hc hab hOne star profile)).blockCountWithin
          (mergedPartition data a b) selected.1 : ℤ) -
        2 * ((data.vertexPartition (doubleEnd data hc hab hOne star profile)).blockCountWithin
          (mergedPartition data a b) selected.1 : ℤ) -
        ((mergedPartition data a b).blockCard selected.1 : ℤ) *
          ((({contracted, retainedOccurrence data hc hab hOne star profile} :
            Finset target.edges).card : ℤ) - 2) := by
    rw [← sum_localRamification_doubleEnd data hc hab hOne fullDim hForest star profile shape
      hBackground]
    exact hSum0
  rw [hCardPair, retained_count data hc hab hOne star profile shape] at hSum1
  rw [hSingle] at hPair
  push_cast at hSum1 hPair
  constructor
  · have hValue : ((data.vertexPartition
        (doubleEnd data hc hab hOne star profile)).blockCountWithin
        (mergedPartition data a b) selected.1 : ℤ) = 2 := by linarith
    exact_mod_cast hValue
  · have hValue : ((data.edgePartition contracted).blockCountWithin
        (mergedPartition data a b) selected.1 : ℤ) = 2 := by linarith
    exact_mod_cast hValue

/-- **The contracted occurrence and the `t₂` endpoint induce the same partition
above `A₀`.** -/
theorem contracted_block_eq_doubleEnd_block
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (sheet : Fin degree) (hSheet : (mergedPartition data a b).Rel selected.1 sheet) :
    (data.edgePartition contracted).block sheet =
      (data.vertexPartition (doubleEnd data hc hab hOne star profile)).block sheet := by
  have hCounts := doubleEnd_contracted_counts data hc hab hOne fullDim hForest star profile
    shape hBackground
  refine block_eq_of_blockCountWithin_eq _ _ (mergedPartition data a b)
    (refines_of_mem_incidentEdges data
      (contracted_mem_doubleEnd data hc hab hOne star profile))
    (vertexPartition_refines_merged data _
      (by rcases ends_cases data hc hab hOne star profile with ⟨h, _⟩ | ⟨h, _⟩
          · exact Or.inl h
          · exact Or.inr h))
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne selected)
    (hCounts.2.trans hCounts.1.symm) sheet hSheet


/-! ### §10  The three-way selected census

`A₀` carries three `t₂` classes and exactly two classes of the `t₂` endpoint,
so exactly one pair of the three is merged there.  The three possibilities are
Figure 35's three members: `M⁽¹⁾` merges `e₁` with the dangling `e₄`, `M⁽²⁾`
merges `e₂` with it, and `M⁽³⁾` merges `e₁` with `e₂` and leaves
`e₄` alone. -/

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
/-- Figure 35's three member shapes, indexed as `W2PCommonBalance.members`. -/
noncomputable def memberShape : Fin 3 → MemberShape profile :=
  ![firstShape shape, secondShape shape, thirdShape shape]

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
@[simp] theorem memberShape_zero :
    memberShape data hc hab hOne star profile shape 0 = firstShape shape := rfl

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
@[simp] theorem memberShape_one :
    memberShape data hc hab hOne star profile shape 1 = secondShape shape := rfl

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
@[simp] theorem memberShape_two :
    memberShape data hc hab hOne star profile shape 2 = thirdShape shape := rfl

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
@[simp] theorem memberShape_candidate (position : Fin 3) :
    (memberShape data hc hab hOne star profile shape position).candidate =
      W2PCommonBalance.members profile shape position := by
  fin_cases position <;> rfl

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
theorem memberShape_fine_refines_merged (position : Fin 3) :
    (memberShape data hc hab hOne star profile shape position).fine.Refines
      (mergedPartition data a b) := by
  rw [← contractDatum_vertexPartition_merge data hc hab hOne]
  exact (memberShape data hc hab hOne star profile shape position).refines

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
private theorem wall_rel_of_merged_rel {first second : Fin degree}
    (h : (mergedPartition data a b).Rel first second) :
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel first second := by
  rw [contractDatum_vertexPartition_merge data hc hab hOne]
  exact h

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest shape in
private theorem merged_rel_of_wall_rel {first second : Fin degree}
    (h : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel first second) :
    (mergedPartition data a b).Rel first second := by
  rw [← contractDatum_vertexPartition_merge data hc hab hOne]
  exact h

/-- **The selected-class census of Figure 35.**  Above `A₀` the incoming `t₂`
endpoint induces exactly one of the three members' fine partitions, and which
one is decided by the single merged pair. -/
theorem exists_member_selected_blocks
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ selected →
        (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0) :
    ∃ position : Fin 3, ∀ sheet : Fin degree,
      (mergedPartition data a b).Rel selected.1 sheet →
        (data.vertexPartition (doubleEnd data hc hab hOne star profile)).block sheet =
          (memberShape data hc hab hOne star profile shape position).fine.block sheet := by
  classical
  have hEpP : (endpointPartition profile).Refines
      (data.vertexPartition (doubleEnd data hc hab hOne star profile)) :=
    refines_of_mem_incidentEdges data
      (retained_mem_doubleEnd data hc hab hOne star profile)
  have hPmerged : (data.vertexPartition (doubleEnd data hc hab hOne star profile)).Refines
      (mergedPartition data a b) :=
    vertexPartition_refines_merged data _
      (by rcases ends_cases data hc hab hOne star profile with ⟨h, _⟩ | ⟨h, _⟩
          · exact Or.inl h
          · exact Or.inr h)
  have hFirstMerged : (mergedPartition data a b).Rel selected.1 (firstSheet profile) :=
    merged_rel_of_wall_rel data hc hab hOne (firstSheet_rel profile)
  have hSecondMerged : (mergedPartition data a b).Rel selected.1 (secondSheet profile) :=
    merged_rel_of_wall_rel data hc hab hOne (secondSheet_rel profile)
  have hExtraMerged : (mergedPartition data a b).Rel selected.1 (extraSheet profile) :=
    merged_rel_of_wall_rel data hc hab hOne (extraSheet_rel profile)
  have hCover : ∀ sheet : Fin degree, (mergedPartition data a b).Rel selected.1 sheet →
      (endpointPartition profile).Rel (firstSheet profile) sheet ∨
        (endpointPartition profile).Rel (secondSheet profile) sheet ∨
          (endpointPartition profile).Rel (extraSheet profile) sheet :=
    fun sheet hSheet ↦ endpointPartition_covers shape sheet
      (wall_rel_of_merged_rel data hc hab hOne hSheet)
  have hCount := (doubleEnd_contracted_counts data hc hab hOne fullDim hForest star profile
    shape hBackground).1
  have hEpSecond : ¬ (endpointPartition profile).Rel (secondSheet profile)
      (firstSheet profile) := fun h ↦ first_second_separate profile h.symm
  by_cases h12 : (data.vertexPartition (doubleEnd data hc hab hOne star profile)).Rel
      (firstSheet profile) (secondSheet profile)
  · by_cases h13 : (data.vertexPartition (doubleEnd data hc hab hOne star profile)).Rel
        (firstSheet profile) (extraSheet profile)
    · exfalso
      have hBlockEq : (data.vertexPartition (doubleEnd data hc hab hOne star profile)).block
          (firstSheet profile) = (mergedPartition data a b).block (firstSheet profile) := by
        ext other
        rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
        refine ⟨fun h ↦ hPmerged.rel h, fun h ↦ ?_⟩
        rcases hCover other (hFirstMerged.trans h) with hOther | hOther | hOther
        · exact hEpP.rel hOther
        · exact h12.trans (hEpP.rel hOther)
        · exact h13.trans (hEpP.rel hOther)
      have hOneCount := blockCountWithin_eq_one_of_block_eq
        (data.vertexPartition (doubleEnd data hc hab hOne star profile))
        (mergedPartition data a b) (firstSheet profile) hBlockEq
      rw [← blockCountWithin_congr _ (mergedPartition data a b) hFirstMerged] at hOneCount
      omega
    · have h23 : ¬ (data.vertexPartition (doubleEnd data hc hab hOne star profile)).Rel
          (secondSheet profile) (extraSheet profile) := fun h ↦ h13 (h12.trans h)
      refine ⟨2, fun sheet hSheet ↦ ?_⟩
      refine block_eq_of_same_pattern (endpointPartition profile) _
        (memberShape data hc hab hOne star profile shape 2).fine
        (mergedPartition data a b) (firstSheet profile)
        (secondSheet profile) (extraSheet profile) selected.1 hEpP
        (memberShape data hc hab hOne star profile shape 2).covers hPmerged
        (memberShape_fine_refines_merged data hc hab hOne star profile shape 2) hCover ?_ ?_ ?_
        sheet hSheet
      · exact iff_of_true h12 ((thirdFine_rel_iff shape (secondSheet profile)).mpr
          ⟨wall_rel_of_merged_rel data hc hab hOne hSecondMerged,
            fun h ↦ extra_ne_second shape h.symm⟩)
      · exact iff_of_false h13 (thirdShape_fine_not_rel shape)
      · refine iff_of_false h23 (fun h ↦ thirdShape_fine_not_rel shape ?_)
        exact ((thirdFine_rel_iff shape (secondSheet profile)).mpr
          ⟨wall_rel_of_merged_rel data hc hab hOne hSecondMerged,
            fun hEq ↦ extra_ne_second shape hEq.symm⟩).trans h
  · by_cases h13 : (data.vertexPartition (doubleEnd data hc hab hOne star profile)).Rel
        (firstSheet profile) (extraSheet profile)
    · have h23 : ¬ (data.vertexPartition (doubleEnd data hc hab hOne star profile)).Rel
          (secondSheet profile) (extraSheet profile) := fun h ↦ h12 (h13.trans h.symm)
      refine ⟨0, fun sheet hSheet ↦ ?_⟩
      refine block_eq_of_same_pattern (endpointPartition profile) _
        (memberShape data hc hab hOne star profile shape 0).fine
        (mergedPartition data a b) (firstSheet profile)
        (secondSheet profile) (extraSheet profile) selected.1 hEpP
        (memberShape data hc hab hOne star profile shape 0).covers hPmerged
        (memberShape_fine_refines_merged data hc hab hOne star profile shape 0) hCover ?_ ?_ ?_
        sheet hSheet
      · exact iff_of_false h12 (mergeShape_fine_not_rel profile.first profile.second
          (first_extra_separate shape) (second_extra_separate shape)
          (first_second_separate profile))
      · exact iff_of_true h13 (mergeShape_fine_rel_extra profile.first
          (first_extra_separate shape))
      · refine iff_of_false h23 (fun h ↦ mergeShape_fine_not_rel profile.first profile.second
          (first_extra_separate shape) (second_extra_separate shape)
          (first_second_separate profile) ?_)
        exact (mergeShape_fine_rel_extra profile.first (first_extra_separate shape)).trans h.symm
    · by_cases h23 : (data.vertexPartition (doubleEnd data hc hab hOne star profile)).Rel
          (secondSheet profile) (extraSheet profile)
      · refine ⟨1, fun sheet hSheet ↦ ?_⟩
        refine block_eq_of_same_pattern (endpointPartition profile) _
          (memberShape data hc hab hOne star profile shape 1).fine
          (mergedPartition data a b) (firstSheet profile)
          (secondSheet profile) (extraSheet profile) selected.1 hEpP
          (memberShape data hc hab hOne star profile shape 1).covers hPmerged
          (memberShape_fine_refines_merged data hc hab hOne star profile shape 1) hCover ?_ ?_ ?_
          sheet hSheet
        · refine iff_of_false h12 (fun h ↦ mergeShape_fine_not_rel profile.second profile.first
            (second_extra_separate shape) (first_extra_separate shape) hEpSecond h.symm)
        · refine iff_of_false h13 (fun h ↦ mergeShape_fine_not_rel profile.second profile.first
            (second_extra_separate shape) (first_extra_separate shape) hEpSecond ?_)
          exact (mergeShape_fine_rel_extra profile.second
            (second_extra_separate shape)).trans h.symm
        · exact iff_of_true h23 (mergeShape_fine_rel_extra profile.second
            (second_extra_separate shape))
      · exfalso
        have hThree := blockCountWithin_eq_three
          (data.vertexPartition (doubleEnd data hc hab hOne star profile))
          (mergedPartition data a b) (firstSheet profile) (secondSheet profile)
          (extraSheet profile) selected.1 hFirstMerged hSecondMerged hExtraMerged
          (fun sheet hSheet ↦ by
            rcases hCover sheet hSheet with h | h | h
            · exact Or.inl (hEpP.rel h)
            · exact Or.inr (Or.inl (hEpP.rel h))
            · exact Or.inr (Or.inr (hEpP.rel h)))
          h12 h13 h23
        omega

end W2P





end DraismaVargas.LocalCases.W2PIncomingCensus
