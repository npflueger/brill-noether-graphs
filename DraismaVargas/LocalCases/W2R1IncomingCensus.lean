module

public import DraismaVargas.LocalCases.W2R1GraphData
public import DraismaVargas.LocalCases.W3Nd2IncomingMemberMatching
public import DraismaVargas.LocalCases.IncomingMatchingCore
public import DraismaVargas.LocalCases.IncomingW2TargetPlacement
public import DraismaVargas.LocalCases.IncomingSourceCases
public import DraismaVargas.LocalCases.MonovalentWall

@[expose] public section

/-!
# The incoming census at a `{w2-r1}` wall, at **both** ramification-one blocks

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case `{w2-r1}`,
sub-cases `{w2-r1-nd3}` (Figure 37) and `{w2-r1-nd2}` (Figure 38), and the
proof of the balancing identity (⋆) for Case `{w2-r1}`, whose display is
**Equation (10)**.

`W2R1SourceCandidates` .. `W2R1GraphData` describe the *outgoing* side of
Figures 37 and 38 at a wall of the already-contracted target.  This module
starts from the other end: an arbitrary incoming gluing datum with an honest
full-dimensional presentation, a single target edge `contracted` between `a`
and `b` whose source fibre is a forest, and the `w2R1` tag that
`IncomingSourceCases.Classification` hands out for the contracted wall
`⟨a, hab⟩`.  It reads the incoming wall data off that bundle.

## What is different from the one-block cases

Every other incoming census (`W3Nd2*`, `W3Nd3*`, `M11*`, `W4*`,
`W2Mkk*`, `W2P*`) has **one** distinguished wall block and a background of
unramified blocks.  Here there are **two** ramified blocks, `A₀` and `B₀`
(`pair.first`, `pair.second`), and the sentence of that proof "`ch u = ch v = 1`, so
`δ⁽ᵠ⁾(Ã) ≠ δ⁽ᵠ⁾(B̃)`" is a *coupling* between their two censuses rather than
two independent statements.  Concretely:

* `divalent_endpoints` -- the incoming wall is `(2,2)` with one unit of change
  at each restored endpoint.  The two leaf orientations are impossible; the
  proof is short and does not repeat `W2PIncomingCensus`' counting argument:
  at a leaf orientation change-minimality makes the contracted occurrence
  partition discrete (`MonovalentWall.exists_leafFibre`) and the trivalent
  endpoint changeless, which forces **both** wall directions to induce the
  same partition there -- but above `A₀` the doubled direction induces two
  classes and the single direction one.

* `blockChange_double` / `blockChange_single` -- the whole endpoint census
  above one ramification-one block, in one parameter `p` (the number of
  classes the doubled direction's endpoint induces there): the doubled
  direction's endpoint carries `2 - p` units of change above the block and the
  single direction's endpoint carries `p - 1`.  Nonnegativity alone gives
  `p ∈ {1, 2}`.

* `exists_member_selected_counts` -- **the coupling**.  `ch = 1` at each
  restored endpoint plus the background census off both blocks forces exactly
  one member index `q : Fin 2` with `p(A₀) = 1 ↔ q = δ(A₀)` **and**
  `p(B₀) = 1 ↔ other q = δ(B₀)`; that is `δ⁽ᵠ⁾(Ã) ≠ δ⁽ᵠ⁾(B̃)`, derived rather
  than assumed.  This is the two-block analogue of
  `W2PIncomingCensus.exists_member_selected_blocks`, and nothing weaker will
  do: a one-block census cannot see which member the datum is.

* `background_block_endOf` / `background_block_contracted` -- the `r = 0`
  census, with `background ∉ {A₀, B₀}` rather than `background ≠ selected`.
  This is exactly the shape the `AnyBlock` namespaces in
  `W3Nd2IncomingBackground` / `W3Nd2IncomingNormalization` are stated for;
  they are used verbatim, with `hZero` supplied by `Pair.background`.

Nothing here is hypothesised beyond the bundle: the `(2,2)` wall is proved,
the selected census is proved, and `Pair` already carries the background
field, so the classifier's `r1` payload is precisely this module's input.
-/

namespace DraismaVargas.LocalCases.W2R1IncomingCensus

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open W4Assembly W4StableSource StableLocalProperties NonDanglingValency
open W2R1Target SecondEquation FullDimensionalSource WallDegeneration
open TargetExpansion
open W2R1SourceCandidates

/-! ## §1  Counting lemmas

The three private lemmas of `W2PIncomingCensus` §1 and §4, restated here
because they are `private` there. -/

section Counting

variable {α : Type*} {degree : ℕ}

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

/-- A refinement that is joined on every block of the partition it refines has
that partition's induced counts. -/
private theorem blockCountWithin_eq_of_joined
    (fine mid coarse : SheetPartition degree)
    (hFineMid : fine.Refines mid) (hMidCoarse : mid.Refines coarse)
    (coarseBlock : coarse.Blocks)
    (hOne : ∀ sheet, fine.blockCountWithin mid sheet = 1) :
    fine.blockCountWithin coarse coarseBlock.1 =
      mid.blockCountWithin coarse coarseBlock.1 := by
  classical
  have hSum := sum_blockCountWithin_trans fine mid coarse hFineMid hMidCoarse coarseBlock
  have hCards := SheetPartition.card_blocksWithin_eq_blockCountWithin mid coarse
    hMidCoarse coarseBlock
  rw [Finset.sum_congr rfl (fun midBlock _ ↦ by rw [hOne midBlock.1]), Finset.sum_const,
    nsmul_eq_mul, Nat.cast_one, mul_one, hCards] at hSum
  exact_mod_cast hSum.symm

/-- A discrete partition induces as many blocks inside a coarse block as the
coarse block has sheets.  (`W2MkkSelectedCensus.blockCountWithin_of_discrete`,
restated: importing that module would drag the whole M-kk chain in.) -/
private theorem blockCountWithin_of_discrete {fine coarse : SheetPartition degree}
    (hDiscrete : ∀ sheet, fine.repr sheet = sheet) (sheet : Fin degree) :
    fine.blockCountWithin coarse sheet = coarse.blockCard sheet := by
  classical
  unfold SheetPartition.blockCountWithin SheetPartition.blockCard
  congr 1
  ext value
  simp only [Finset.mem_image]
  exact ⟨by rintro ⟨x, hx, rfl⟩; rwa [hDiscrete x],
    fun hValue ↦ ⟨value, hValue, hDiscrete value⟩⟩

end Counting


/-! ## §2  The incoming wall, read off the bundle -/

section Wall

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  (pair : Pair (contractDatum data hc hab hOne) star)

/-- The incoming occurrence carrying the wall direction `label`. -/
noncomputable def wallOcc (label : Fin 2) : target.edges :=
  unfoldEdge hc hab hOne (star.edge label)

theorem wallOcc_ne_contracted (label : Fin 2) :
    wallOcc hc hab hOne star label ≠ contracted :=
  unfoldEdge_ne_contracted hc hab hOne _

theorem wallOcc_injective {first second : Fin 2}
    (hEq : wallOcc hc hab hOne star first = wallOcc hc hab hOne star second) :
    first = second :=
  star.edge_injective ((foldEdgeEquiv hc hab hOne).symm.injective (Subtype.ext hEq))

/-- The incoming occurrence partition of a wall direction **is** the contracted
datum's, on the nose. -/
theorem wallOcc_edgePartition (label : Fin 2) :
    data.edgePartition (wallOcc hc hab hOne star label) =
      (contractDatum data hc hab hOne).edgePartition (star.edge label) := rfl

/-- The contracted wall partition **is** the merged partition, on the nose. -/
theorem wallPartition_eq :
    (contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩ = mergedPartition data a b :=
  contractDatum_vertexPartition_merge data hc hab hOne

theorem merged_rel_of_wall_rel {first second : Fin degree}
    (h : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel first second) :
    (mergedPartition data a b).Rel first second := by
  rwa [wallPartition_eq data hc hab hOne] at h

theorem wall_rel_of_merged_rel {first second : Fin degree}
    (h : (mergedPartition data a b).Rel first second) :
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel first second := by
  rwa [wallPartition_eq data hc hab hOne]

/-- The restored endpoint of the contracted edge at which the wall direction
`label` sits.  Figure 37 calls the two `u` and `v`; the incoming cover does not
know that labelling, so it is read off the reconstructed side predicate. -/
noncomputable def endOf (label : Fin 2) : target.V :=
  if IncomingTargetExpansion.right hc hab hOne (star.edge label) = true then b else a

@[simp] theorem endOf_of_false {label : Fin 2}
    (hFalse : IncomingTargetExpansion.right hc hab hOne (star.edge label) = false) :
    endOf hc hab hOne star label = a := by
  simp only [endOf, hFalse, Bool.false_eq_true, ite_false]

@[simp] theorem endOf_of_true {label : Fin 2}
    (hTrue : IncomingTargetExpansion.right hc hab hOne (star.edge label) = true) :
    endOf hc hab hOne star label = b := by
  simp only [endOf, hTrue, ite_true]

theorem endOf_cases (label : Fin 2) :
    endOf hc hab hOne star label = a ∨ endOf hc hab hOne star label = b := by
  unfold endOf
  by_cases hTrue : IncomingTargetExpansion.right hc hab hOne (star.edge label) = true
  · exact Or.inr (ite_eq_left hTrue)
  · exact Or.inl (ite_eq_right hTrue)

theorem endOf_refines (label : Fin 2) :
    (data.vertexPartition (endOf hc hab hOne star label)).Refines
      (mergedPartition data a b) := by
  rcases endOf_cases hc hab hOne star label with hEq | hEq
  · rw [hEq]; exact vertexPartition_refines_mergedPartition data a b
  · rw [hEq]; exact vertexPartition_refines_mergedPartition_right data a b

/-- The wall direction's occurrence meets its own restored endpoint. -/
theorem wallOcc_mem_endOf (label : Fin 2) :
    wallOcc hc hab hOne star label ∈
      GluingDatum.incidentEdges (endOf hc hab hOne star label) := by
  unfold endOf wallOcc
  by_cases hTrue : IncomingTargetExpansion.right hc hab hOne (star.edge label) = true
  · rw [ite_eq_left hTrue]
    exact (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp hTrue
  · rw [ite_eq_right hTrue]
    exact (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
      (star.edge_mem_incidentEdges label)).mp (by simpa using hTrue)

/-- The contracted occurrence meets both restored endpoints. -/
theorem contracted_mem_endOf (label : Fin 2) :
    contracted ∈ GluingDatum.incidentEdges (endOf hc hab hOne star label) := by
  rcases endOf_cases hc hab hOne star label with hEq | hEq
  · rw [hEq]; exact contracted_mem_incidentEdges_left hc
  · rw [hEq]; exact contracted_mem_incidentEdges_right hc

/-- Each wall occurrence meets one of the two original endpoints. -/
theorem wallOcc_mem_union (label : Fin 2) :
    wallOcc hc hab hOne star label ∈
      GluingDatum.incidentEdges a ∪ GluingDatum.incidentEdges b :=
  unfoldEdge_mem_incidentEdges_union hc hab hOne (star.edge_mem_incidentEdges label)

end Wall


/-! ## §3  The two induced counts above a ramification-one block

`k₁ + k₂ = |A₀| = k₃` of Case `{w2-r1}` in Part I is a *partition* statement:
above the block,
the doubled direction induces two classes and the single direction one.  Both
are `W2R1SourceCandidates`' own receipts, read at the incoming datum through
the definitional identity `wallOcc_edgePartition`. -/

section Counts

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  {blk : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (profile : W2R1SourceProfile.OccurrenceProfile (contractDatum data hc hab hOne) star blk)

theorem block_rel_self :
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel blk.1 blk.1 := rfl

/-- **The doubled direction cuts the block in two.** -/
theorem count_double :
    (data.edgePartition (wallOcc hc hab hOne star profile.doubleLabel)).blockCountWithin
      (mergedPartition data a b) blk.1 = 2 := by
  rw [wallOcc_edgePartition data hc hab hOne star, ← wallPartition_eq data hc hab hOne]
  exact doublePartition_blockCountWithin profile blk.1 (block_rel_self data hc hab hOne)

/-- **The other direction sees the block whole.** -/
theorem count_single {label : Fin 2} (hLabel : label ≠ profile.doubleLabel) :
    (data.edgePartition (wallOcc hc hab hOne star label)).blockCountWithin
      (mergedPartition data a b) blk.1 = 1 := by
  rw [wallOcc_edgePartition data hc hab hOne star, ← wallPartition_eq data hc hab hOne]
  exact blockCountWithin_eq_one_of_ne_doubleLabel profile hLabel blk.1
    (block_rel_self data hc hab hOne)

end Counts


/-! ## §4  The leaf orientations are impossible: the incoming wall is `(2,2)`

At a leaf orientation change-minimality makes the contracted occurrence
partition discrete (`MonovalentWall.exists_leafFibre`) and leaves the trivalent
endpoint changeless.  Its local ramification then reads
`|blk| + x₀ + x₁ - 2 - |blk| = 0`, so **both** wall directions are joined on
every block of that endpoint -- hence induce the *same* count above `A₀`.  But
above `A₀` the doubled direction induces two classes and the single direction
one.  That is the whole argument; unlike `W2PIncomingCensus.not_leaf` it needs
no surviving-valency count and no `NoDanglingTargetFibres` beyond the one
inside `exists_leafFibre`. -/

section LeafExclusion

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  (pair : Pair (contractDatum data hc hab hOne) star)

omit [Fintype coordinate] [DecidableEq coordinate] fullDim pair in
/-- The three occurrences at the trivalent endpoint of a leaf orientation. -/
private theorem incidentEdges_eq_triple (vertex : target.V)
    (hCard : (GluingDatum.incidentEdges vertex).card = 3)
    (hContractedAt : contracted ∈ GluingDatum.incidentEdges vertex)
    (hStarAt : ∀ label : Fin 2,
      wallOcc hc hab hOne star label ∈ GluingDatum.incidentEdges vertex) :
    GluingDatum.incidentEdges vertex =
      {contracted, wallOcc hc hab hOne star 0, wallOcc hc hab hOne star 1} := by
  classical
  have hStarNe : wallOcc hc hab hOne star 0 ≠ wallOcc hc hab hOne star 1 := by
    intro h
    exact absurd (wallOcc_injective hc hab hOne star h) (by decide)
  have hNotMemSecond : wallOcc hc hab hOne star 0 ∉
      ({wallOcc hc hab hOne star 1} : Finset target.edges) := by
    simpa using hStarNe
  have hNotMemFirst : contracted ∉
      ({wallOcc hc hab hOne star 0, wallOcc hc hab hOne star 1} : Finset target.edges) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact wallOcc_ne_contracted hc hab hOne star 0 h.symm
    · exact wallOcc_ne_contracted hc hab hOne star 1 h.symm
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · exact hContractedAt
    · rcases Finset.mem_insert.mp hEdge with rfl | hEdge
      · exact hStarAt 0
      · rw [Finset.mem_singleton.mp hEdge]
        exact hStarAt 1
  · rw [hCard, Finset.card_insert_of_notMem hNotMemFirst,
      Finset.card_insert_of_notMem hNotMemSecond, Finset.card_singleton]

include fullDim pair in
/-- **A leaf orientation cannot occur at a `{w2-r1}` wall.** -/
private theorem false_of_leaf (leaf vertex : target.V)
    (hLeafEdges : GluingDatum.incidentEdges leaf = {contracted})
    (hCard : (GluingDatum.incidentEdges vertex).card = 3)
    (hChange : data.targetChange vertex = 0)
    (hRefines : (data.vertexPartition vertex).Refines (mergedPartition data a b))
    (hContractedAt : contracted ∈ GluingDatum.incidentEdges vertex)
    (hStarAt : ∀ label : Fin 2,
      wallOcc hc hab hOne star label ∈ GluingDatum.incidentEdges vertex) :
    False := by
  classical
  obtain ⟨fibre⟩ := MonovalentWall.exists_leafFibre data fullDim leaf contracted hLeafEdges
  have hDiscrete := fibre.edgePartition_repr
  have hStarNe : wallOcc hc hab hOne star 0 ≠ wallOcc hc hab hOne star 1 := by
    intro h
    exact absurd (wallOcc_injective hc hab hOne star h) (by decide)
  have hNotMemSecond : wallOcc hc hab hOne star 0 ∉
      ({wallOcc hc hab hOne star 1} : Finset target.edges) := by
    simpa using hStarNe
  have hNotMemFirst : contracted ∉
      ({wallOcc hc hab hOne star 0, wallOcc hc hab hOne star 1} : Finset target.edges) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact wallOcc_ne_contracted hc hab hOne star 0 h.symm
    · exact wallOcc_ne_contracted hc hab hOne star 1 h.symm
  have hEdges := incidentEdges_eq_triple hc hab hOne star vertex hCard
    hContractedAt hStarAt
  have hJoined : ∀ sheet : Fin degree,
      (data.edgePartition (wallOcc hc hab hOne star 0)).blockCountWithin
          (data.vertexPartition vertex) sheet = 1 ∧
        (data.edgePartition (wallOcc hc hab hOne star 1)).blockCountWithin
          (data.vertexPartition vertex) sheet = 1 := by
    intro sheet
    have hRam := localRamification_eq_zero_of_targetChange_eq_zero data fullDim.valid vertex
      hChange ((data.vertexPartition vertex).toBlock sheet)
    unfold GluingDatum.localRamification at hRam
    rw [hEdges, Finset.sum_insert hNotMemFirst, Finset.sum_insert hNotMemSecond,
      Finset.sum_singleton, Finset.card_insert_of_notMem hNotMemFirst,
      Finset.card_insert_of_notMem hNotMemSecond, Finset.card_singleton,
      SheetPartition.toBlock_val] at hRam
    have hReprRel : (data.vertexPartition vertex).Rel
        ((data.vertexPartition vertex).repr sheet) sheet :=
      (data.vertexPartition vertex).rel_repr_left sheet
    rw [blockCountWithin_congr (data.edgePartition contracted)
        (data.vertexPartition vertex) hReprRel,
      blockCountWithin_congr (data.edgePartition (wallOcc hc hab hOne star 0))
        (data.vertexPartition vertex) hReprRel,
      blockCountWithin_congr (data.edgePartition (wallOcc hc hab hOne star 1))
        (data.vertexPartition vertex) hReprRel,
      SheetPartition.blockCard_congr (data.vertexPartition vertex) hReprRel,
      blockCountWithin_of_discrete hDiscrete] at hRam
    have hPosZero := SheetPartition.blockCountWithin_pos
      (data.edgePartition (wallOcc hc hab hOne star 0)) (data.vertexPartition vertex) sheet
    have hPosOne := SheetPartition.blockCountWithin_pos
      (data.edgePartition (wallOcc hc hab hOne star 1)) (data.vertexPartition vertex) sheet
    push_cast at hRam
    constructor <;> omega
  have hCountEq : ∀ label : Fin 2,
      (data.edgePartition (wallOcc hc hab hOne star label)).blockCountWithin
          (mergedPartition data a b) pair.first.1 =
        (data.vertexPartition vertex).blockCountWithin
          (mergedPartition data a b) pair.first.1 := by
    intro label
    refine blockCountWithin_eq_of_joined _ _ _
      (refines_of_mem_incidentEdges data (hStarAt label)) hRefines
      (M11IncomingPartitions.selectedMergedBlock data hc hab hOne pair.first) ?_
    intro sheet
    rcases (show label = 0 ∨ label = 1 by omega) with rfl | rfl
    · exact (hJoined sheet).1
    · exact (hJoined sheet).2
  have hDouble := count_double data hc hab hOne star pair.firstProfile.toOccurrenceProfile
  have hSingle := count_single data hc hab hOne star pair.firstProfile.toOccurrenceProfile
    (Ne.symm pair.firstProfile.labels_ne)
  rw [hCountEq] at hDouble hSingle
  omega

include fullDim pair in
/-- **The incoming `{w2-r1}` wall is `(2,2)`, with one unit of change at each
restored endpoint.**  This is the `ch u = ch v = 1` of Part I's proof of (⋆)
for Case `{w2-r1}`, proved rather than assumed: the leaf orientations `(1,3)`
and `(3,1)` that
`IncomingW2TargetPlacement.placement_of_twoStar` leaves open are impossible. -/
theorem divalent_endpoints :
    (GluingDatum.incidentEdges a).card = 2 ∧ (GluingDatum.incidentEdges b).card = 2 ∧
      data.targetChange a = 1 ∧ data.targetChange b = 1 := by
  classical
  rcases IncomingW2TargetPlacement.placement_of_twoStar data hc hab hOne fullDim.valid
      fullDim.changeMinimal star with
    ⟨hLeft, hRight, _, hChange, hZero, hOneEdge⟩ |
    ⟨hLeft, hRight, hChange, _, hZero, hOneEdge⟩ |
    ⟨hLeft, hRight, hChangeA, hChangeB, _⟩
  · refine absurd ?_ not_false
    refine false_of_leaf data hc hab hOne fullDim star pair a b ?_ hRight hChange
      (vertexPartition_refines_mergedPartition_right data a b)
      (contracted_mem_incidentEdges_right hc) ?_
    · refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro edge hEdge
        rw [Finset.mem_singleton.mp hEdge]
        exact contracted_mem_incidentEdges_left hc
      · rw [hLeft, Finset.card_singleton]
    · intro label
      rcases (show label = 0 ∨ label = 1 by omega) with rfl | rfl
      · exact (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp hZero
      · exact (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp hOneEdge
  · refine absurd ?_ not_false
    refine false_of_leaf data hc hab hOne fullDim star pair b a ?_ hLeft hChange
      (vertexPartition_refines_mergedPartition data a b)
      (contracted_mem_incidentEdges_left hc) ?_
    · refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro edge hEdge
        rw [Finset.mem_singleton.mp hEdge]
        exact contracted_mem_incidentEdges_right hc
      · rw [hRight, Finset.card_singleton]
    · intro label
      rcases (show label = 0 ∨ label = 1 by omega) with rfl | rfl
      · exact (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
          (star.edge_mem_incidentEdges 0)).mp hZero
      · exact (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
          (star.edge_mem_incidentEdges 1)).mp hOneEdge
  · exact ⟨hLeft, hRight, hChangeA, hChangeB⟩

include fullDim pair in
/-- The two wall directions are restored to **opposite** endpoints. -/
theorem endOf_values_ne :
    IncomingTargetExpansion.right hc hab hOne (star.edge 0) ≠
      IncomingTargetExpansion.right hc hab hOne (star.edge 1) := by
  have hDiv := divalent_endpoints data hc hab hOne fullDim star pair
  exact IncomingW2TargetPlacement.right_star_ne_of_divalent hc hab hOne star hDiv.1 hDiv.2.1

include fullDim pair in
/-- The two restored endpoints of the contracted edge are `a` and `b`, in one
order or the other. -/
theorem endOf_pair :
    (endOf hc hab hOne star 0 = a ∧ endOf hc hab hOne star 1 = b) ∨
      (endOf hc hab hOne star 0 = b ∧ endOf hc hab hOne star 1 = a) := by
  have hNe := endOf_values_ne data hc hab hOne fullDim star pair
  by_cases hZero : IncomingTargetExpansion.right hc hab hOne (star.edge 0) = true
  · have hOneEdge : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = false := by
      by_contra hContra
      have hContra' : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = true := by
        simpa using hContra
      exact hNe (hZero.trans hContra'.symm)
    exact Or.inr ⟨endOf_of_true hc hab hOne star hZero,
      endOf_of_false hc hab hOne star hOneEdge⟩
  · have hZero' : IncomingTargetExpansion.right hc hab hOne (star.edge 0) = false := by
      simpa using hZero
    have hOneEdge : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = true := by
      by_contra hContra
      have hContra' : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = false := by
        simpa using hContra
      exact hNe (hZero'.trans hContra'.symm)
    exact Or.inl ⟨endOf_of_false hc hab hOne star hZero',
      endOf_of_true hc hab hOne star hOneEdge⟩

include fullDim pair in
theorem endOf_divalent (label : Fin 2) :
    (GluingDatum.incidentEdges (endOf hc hab hOne star label)).card = 2 := by
  have hDiv := divalent_endpoints data hc hab hOne fullDim star pair
  rcases endOf_cases hc hab hOne star label with hEq | hEq
  · rw [hEq]; exact hDiv.1
  · rw [hEq]; exact hDiv.2.1

include fullDim pair in
theorem endOf_targetChange (label : Fin 2) :
    data.targetChange (endOf hc hab hOne star label) = 1 := by
  have hDiv := divalent_endpoints data hc hab hOne fullDim star pair
  rcases endOf_cases hc hab hOne star label with hEq | hEq
  · rw [hEq]; exact hDiv.2.2.1
  · rw [hEq]; exact hDiv.2.2.2

include fullDim pair in
/-- **The star of each restored endpoint**: the contracted occurrence and that
endpoint's own wall direction, and nothing else. -/
theorem incidentEdges_endOf (label : Fin 2) :
    GluingDatum.incidentEdges (endOf hc hab hOne star label) =
      {contracted, wallOcc hc hab hOne star label} := by
  classical
  have hNe : contracted ∉ ({wallOcc hc hab hOne star label} : Finset target.edges) := by
    simpa using fun h ↦ wallOcc_ne_contracted hc hab hOne star label h.symm
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · exact contracted_mem_endOf hc hab hOne star label
    · rw [Finset.mem_singleton.mp hEdge]
      exact wallOcc_mem_endOf hc hab hOne star label
  · rw [endOf_divalent data hc hab hOne fullDim star pair label,
      Finset.card_insert_of_notMem hNe, Finset.card_singleton]

end LeafExclusion


/-! ## §5  The placement of Equation (10)'s members, and the two restored ends

Both members of `W2R1SourceCandidates.Pair` carry the **star's own** side
predicate (`Pair.candidate_right` is `rfl`), so there is no oriented star to
build and no orientation transport to perform: `IncomingMatchingCore.Placement`
is `M11IncomingTargetNormalization.joinedPlacement` at the `(2,2)` wall §4
proves. -/

section Placement

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  (pair : Pair (contractDatum data hc hab hOne) star)

omit [Fintype coordinate] [DecidableEq coordinate] fullDim in
/-- **Every Equation (10) member's wall-side assignment is the star's own.** -/
theorem members_right (position : Fin 2) :
    (pair.candidate position).right = star.right := rfl

include fullDim pair in
/-- **The placement of both Equation (10) members.**  The incoming wall is
`(2,2)` by `divalent_endpoints`, and a `(2,2)` wall restores the two star
occurrences to opposite endpoints. -/
theorem member_placement : IncomingMatchingCore.Placement hc hab hOne star.right :=
  M11IncomingTargetNormalization.joinedPlacement hc hab hOne star
    (divalent_endpoints data hc hab hOne fullDim star pair).1
    (divalent_endpoints data hc hab hOne fullDim star pair).2.1

include fullDim in
/-- The same placement, at the member's own side predicate. -/
theorem members_placement (position : Fin 2) :
    IncomingMatchingCore.Placement hc hab hOne (pair.candidate position).right :=
  member_placement data hc hab hOne fullDim star pair

include fullDim pair in
/-- **The `if` of `M11IncomingOuterPartitions.transported_endpointPartitions`,
decided**: the normalization leaves the two expanded ends in place exactly when
the direction-`0` occurrence is restored to `a`. -/
theorem support_iff :
    (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = star.right edge) ↔
      IncomingTargetExpansion.right hc hab hOne (star.edge 0) = false := by
  constructor
  · intro hSupport
    have hValue := hSupport _ (star.edge_mem_incidentEdges 0)
    rwa [TwoStar.right_edge_zero star] at hValue
  · intro hFalse
    have hNe := endOf_values_ne data hc hab hOne fullDim star pair
    have hTrue : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = true := by
      by_contra hContra
      have hContra' : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = false := by
        simpa using hContra
      exact hNe (hFalse.trans hContra'.symm)
    intro edge hAt
    obtain ⟨label, hLabel⟩ := star.label.surjective ⟨edge, hAt⟩
    have hEdge : star.edge label = edge := congrArg Subtype.val hLabel
    rw [← hEdge]
    rcases (show label = 0 ∨ label = 1 by omega) with rfl | rfl
    · exact hFalse.trans (TwoStar.right_edge_zero star).symm
    · exact hTrue.trans (TwoStar.right_edge_one star).symm

include fullDim pair in
/-- **The two restored ends of a member are the two `endOf`s**, in both
orientations at once: the old wall end restores the direction-`0` endpoint and
the fresh end the direction-`1` endpoint. -/
theorem transported_endpoints (side : (contract target hab hOne).edges → Bool)
    (hSide : side = star.right)
    (hPlacement : IncomingMatchingCore.Placement hc hab hOne side) :
    (GluingTransport.transport (M11IncomingTargetNormalization.incomingIso hc hab hOne
          side hPlacement) data).vertexPartition
        (oldVertex (contract target hab hOne) ⟨a, hab⟩) =
      data.vertexPartition (endOf hc hab hOne star 0) ∧
    (GluingTransport.transport (M11IncomingTargetNormalization.incomingIso hc hab hOne
          side hPlacement) data).vertexPartition
        (freshVertex (contract target hab hOne)) =
      data.vertexPartition (endOf hc hab hOne star 1) := by
  classical
  subst hSide
  have hPair := M11IncomingOuterPartitions.transported_endpointPartitions data hc hab hOne
    star.right hPlacement
  have hNe := endOf_values_ne data hc hab hOne fullDim star pair
  by_cases hSupport : ∀ edge ∈ GluingDatum.incidentEdges
      (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = star.right edge
  · have hFalse := (support_iff data hc hab hOne fullDim star pair).mp hSupport
    have hTrue : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = true := by
      by_contra hContra
      have hContra' : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = false := by
        simpa using hContra
      exact hNe (hFalse.trans hContra'.symm)
    rw [ite_eq_left hSupport] at hPair
    rw [endOf_of_false hc hab hOne star hFalse, endOf_of_true hc hab hOne star hTrue]
    exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩
  · have hTrue : IncomingTargetExpansion.right hc hab hOne (star.edge 0) = true := by
      by_contra hContra
      have hFalse : IncomingTargetExpansion.right hc hab hOne (star.edge 0) = false := by
        simpa using hContra
      exact hSupport ((support_iff data hc hab hOne fullDim star pair).mpr hFalse)
    have hFalseOne : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = false := by
      by_contra hContra
      have hContra' : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = true := by
        simpa using hContra
      exact hNe (hTrue.trans hContra'.symm)
    rw [ite_eq_right hSupport] at hPair
    rw [endOf_of_true hc hab hOne star hTrue, endOf_of_false hc hab hOne star hFalseOne]
    exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩

end Placement


/-! ## §6  Off `A₀` **and** `B₀` every partition in sight is the whole wall block

`Pair.background` is the `background ∉ {A₀, B₀}` clause, which is exactly the
hypothesis shape the `AnyBlock` namespaces are stated for: they ask
only for vanishing local ramification of the block in question, with no star,
no source input and no distinguished block.  At a `(2,2)` W2 wall both restored
endpoints are divalent, so both orientations apply at once and the census is
symmetric in the two ends. -/

section Background

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  (pair : Pair (contractDatum data hc hab hOne) star)

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest pair in
theorem merged_rel_ofSheet (sheet : Fin degree) :
    (mergedPartition data a b).Rel
      (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ sheet).1 sheet := by
  show (mergedPartition data a b).Rel
    (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr sheet) sheet
  rw [wallPartition_eq data hc hab hOne]
  exact (mergedPartition data a b).rel_repr_left sheet

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
/-- **The background hypothesis of `Pair`, read at a sheet off both blocks.** -/
theorem background_zero_of_off {sheet : Fin degree}
    (hOffFirst : ¬ (mergedPartition data a b).Rel pair.first.1 sheet)
    (hOffSecond : ¬ (mergedPartition data a b).Rel pair.second.1 sheet) :
    (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩
      (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ sheet) = 0 := by
  refine pair.background _ (fun hEq ↦ hOffFirst ?_) (fun hEq ↦ hOffSecond ?_)
  · exact hEq ▸ merged_rel_ofSheet data hc hab hOne sheet
  · exact hEq ▸ merged_rel_ofSheet data hc hab hOne sheet

include fullDim hForest pair in
/-- **`a` carries the whole wall block off both `A₀` and `B₀`.** -/
theorem background_joined_left {sheet : Fin degree}
    (hOffFirst : ¬ (mergedPartition data a b).Rel pair.first.1 sheet)
    (hOffSecond : ¬ (mergedPartition data a b).Rel pair.second.1 sheet) :
    (data.vertexPartition a).block sheet = (mergedPartition data a b).block sheet := by
  have hDiv := divalent_endpoints data hc hab hOne fullDim star pair
  have hJoined :=
    (W3Nd2IncomingNormalization.AnyBlock.background_trivalent_joined_of_right_divalent
      data hc hab hOne fullDim hForest hDiv.2.1
      (background_zero_of_off data hc hab hOne star pair hOffFirst hOffSecond)).2
  have hRel := merged_rel_ofSheet data hc hab hOne sheet
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact ⟨fun h ↦ (vertexPartition_refines_mergedPartition data a b).rel h,
    fun h ↦ hJoined sheet other hRel (hRel.trans h)⟩

include fullDim hForest pair in
/-- **`b` carries the whole wall block off both `A₀` and `B₀`.** -/
theorem background_joined_right {sheet : Fin degree}
    (hOffFirst : ¬ (mergedPartition data a b).Rel pair.first.1 sheet)
    (hOffSecond : ¬ (mergedPartition data a b).Rel pair.second.1 sheet) :
    (data.vertexPartition b).block sheet = (mergedPartition data a b).block sheet := by
  have hDiv := divalent_endpoints data hc hab hOne fullDim star pair
  have hJoined :=
    (W3Nd2IncomingNormalization.AnyBlock.background_trivalent_joined_of_left_divalent
      data hc hab hOne fullDim hForest hDiv.1
      (background_zero_of_off data hc hab hOne star pair hOffFirst hOffSecond)).2
  have hRel := merged_rel_ofSheet data hc hab hOne sheet
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact ⟨fun h ↦ (vertexPartition_refines_mergedPartition_right data a b).rel h,
    fun h ↦ hJoined sheet other hRel (hRel.trans h)⟩

include fullDim hForest pair in
/-- **Off both blocks each restored endpoint carries the whole wall block.** -/
theorem background_block_endOf (label : Fin 2) {sheet : Fin degree}
    (hOffFirst : ¬ (mergedPartition data a b).Rel pair.first.1 sheet)
    (hOffSecond : ¬ (mergedPartition data a b).Rel pair.second.1 sheet) :
    (data.vertexPartition (endOf hc hab hOne star label)).block sheet =
      (mergedPartition data a b).block sheet := by
  rcases endOf_cases hc hab hOne star label with hEq | hEq
  · rw [hEq]
    exact background_joined_left data hc hab hOne fullDim hForest star pair hOffFirst hOffSecond
  · rw [hEq]
    exact background_joined_right data hc hab hOne fullDim hForest star pair hOffFirst hOffSecond

include fullDim hForest pair in
/-- **Off both blocks the contracted occurrence carries the whole wall
block.** -/
theorem background_block_contracted {sheet : Fin degree}
    (hOffFirst : ¬ (mergedPartition data a b).Rel pair.first.1 sheet)
    (hOffSecond : ¬ (mergedPartition data a b).Rel pair.second.1 sheet) :
    (data.edgePartition contracted).block sheet = (mergedPartition data a b).block sheet := by
  have hDiv := divalent_endpoints data hc hab hOne fullDim star pair
  have hIff := W3Nd2IncomingNormalization.AnyBlock.background_edge_rel_iff_of_left_divalent
    data hc hab hOne fullDim hForest hDiv.1
    (background_zero_of_off data hc hab hOne star pair hOffFirst hOffSecond)
    contracted (contracted_mem_incidentEdges_left hc) sheet
  have hBlock : (data.edgePartition contracted).block sheet =
      (data.vertexPartition a).block sheet := by
    ext other
    rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
    exact hIff other (merged_rel_ofSheet data hc hab hOne sheet)
  exact hBlock.trans
    (background_joined_left data hc hab hOne fullDim hForest star pair hOffFirst hOffSecond)

end Background


/-! ## §7  The endpoint census above one ramification-one block

Everything above one block is governed by a single number `p`, the count the
block's **doubled** direction's endpoint induces there.  The other endpoint's
count is `1` (its wall direction sees the block whole), the forest identity
then reads `c = p`, and the two endpoint changes above the block are `2 - p`
and `p - 1`.  Nonnegativity gives `p ∈ {1, 2}`: Figure 37's gluing I
(`p = 1`, the block stays whole -- `|e'| = k₃`) and gluing II (`p = 2`, the
block is cut in two -- `|e'| = k₁`, `|e''| = k₂`). -/

section BlockCensus

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  (pair : Pair (contractDatum data hc hab hOne) star)

/-- The change one restored endpoint carries above one merged block. -/
noncomputable def blockChange (vertex : target.V)
    (mblk : (mergedPartition data a b).Blocks) : ℤ :=
  ∑ blkv ∈ SheetPartition.blocksWithin (data.vertexPartition vertex)
      (mergedPartition data a b) mblk,
    data.localRamification vertex blkv

include fullDim pair in
/-- **The change of a restored endpoint above a block**, in the three induced
counts of its divalent star. -/
theorem blockChange_endOf (label : Fin 2) (mblk : (mergedPartition data a b).Blocks) :
    blockChange data (endOf hc hab hOne star label) mblk =
      ((data.edgePartition contracted).blockCountWithin
          (mergedPartition data a b) mblk.1 : ℤ) +
        ((data.edgePartition (wallOcc hc hab hOne star label)).blockCountWithin
          (mergedPartition data a b) mblk.1 : ℤ) -
        2 * ((data.vertexPartition (endOf hc hab hOne star label)).blockCountWithin
          (mergedPartition data a b) mblk.1 : ℤ) := by
  classical
  have hNe : contracted ≠ wallOcc hc hab hOne star label :=
    fun h ↦ wallOcc_ne_contracted hc hab hOne star label h.symm
  have hRefines := endOf_refines data hc hab hOne star label
  have hSum := sum_localRamification_blocksWithin data
    (endOf hc hab hOne star label) (mergedPartition data a b) hRefines mblk
  rw [incidentEdges_endOf data hc hab hOne fullDim star pair label,
    Finset.sum_pair hNe,
    SheetPartition.card_blocksWithin_eq_blockCountWithin _ (mergedPartition data a b)
      hRefines mblk,
    Finset.card_insert_of_notMem (by simpa using hNe), Finset.card_singleton] at hSum
  rw [blockChange]
  rw [hSum]
  ring

include fullDim hForest pair in
/-- The forest identity at a restored-endpoint pair. -/
theorem forest_count_endOf (mblk : (mergedPartition data a b).Blocks) (label : Fin 2) :
    ((data.edgePartition contracted).blockCountWithin
        (mergedPartition data a b) mblk.1 : ℤ) + 1 =
      ((data.vertexPartition (endOf hc hab hOne star label)).blockCountWithin
          (mergedPartition data a b) mblk.1 : ℤ) +
        ((data.vertexPartition (endOf hc hab hOne star (other label))).blockCountWithin
          (mergedPartition data a b) mblk.1 : ℤ) := by
  have hTree := contractionForest_count data hc hForest mblk
  have hEnds := endOf_pair data hc hab hOne fullDim star pair
  have hOtherZero : other (0 : Fin 2) = 1 := by decide
  have hOtherOne : other (1 : Fin 2) = 0 := by decide
  rcases (show label = 0 ∨ label = 1 by omega) with rfl | rfl
  · rw [hOtherZero]
    rcases hEnds with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1] <;> linarith
  · rw [hOtherOne]
    rcases hEnds with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1] <;> linarith


/-! ### The one-parameter census above one block -/

variable {blk : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (profile : W2R1SourceProfile.OccurrenceProfile (contractDatum data hc hab hOne) star blk)

/-- **`δ⁽ᵠ⁾` at one block, as a number**: how many classes the block's doubled
direction's endpoint induces above the block.  `1` is Figure 37's gluing I and
`2` its gluing II. -/
noncomputable def doubleCount : ℕ :=
  (data.vertexPartition (endOf hc hab hOne star profile.doubleLabel)).blockCountWithin
    (mergedPartition data a b) blk.1

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest pair in
/-- **The block's other endpoint sees it whole.** -/
theorem single_count :
    (data.vertexPartition (endOf hc hab hOne star (other profile.doubleLabel))).blockCountWithin
      (mergedPartition data a b) blk.1 = 1 :=
  blockCountWithin_eq_one_of_refines _ _ _
    (refines_of_mem_incidentEdges data
      (wallOcc_mem_endOf hc hab hOne star (other profile.doubleLabel)))
    (endOf_refines data hc hab hOne star (other profile.doubleLabel))
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne blk)
    (count_single data hc hab hOne star profile (other_ne profile.doubleLabel))

include fullDim hForest pair in
/-- **The forest identity above the block reads `c = p`.** -/
theorem contracted_count :
    (data.edgePartition contracted).blockCountWithin (mergedPartition data a b) blk.1 =
      doubleCount data hc hab hOne star profile := by
  have hForestCount := forest_count_endOf data hc hab hOne fullDim hForest star pair
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne blk) profile.doubleLabel
  have hSingle := single_count data hc hab hOne star profile
  rw [show (M11IncomingPartitions.selectedMergedBlock data hc hab hOne blk).1 = blk.1 from rfl,
    hSingle] at hForestCount
  have hValue : ((data.edgePartition contracted).blockCountWithin
      (mergedPartition data a b) blk.1 : ℤ) =
      (doubleCount data hc hab hOne star profile : ℤ) := by
    rw [doubleCount]
    push_cast at hForestCount ⊢
    linarith
  exact_mod_cast hValue

include fullDim hForest pair in
/-- **The doubled direction's endpoint carries `2 - p` units of change above
the block.** -/
theorem blockChange_double :
    blockChange data (endOf hc hab hOne star profile.doubleLabel)
        (M11IncomingPartitions.selectedMergedBlock data hc hab hOne blk) =
      2 - (doubleCount data hc hab hOne star profile : ℤ) := by
  rw [blockChange_endOf data hc hab hOne fullDim star pair profile.doubleLabel,
    show (M11IncomingPartitions.selectedMergedBlock data hc hab hOne blk).1 = blk.1 from rfl,
    count_double data hc hab hOne star profile,
    contracted_count data hc hab hOne fullDim hForest star pair profile]
  rw [show (data.vertexPartition (endOf hc hab hOne star profile.doubleLabel)).blockCountWithin
      (mergedPartition data a b) blk.1 = doubleCount data hc hab hOne star profile from rfl]
  push_cast
  ring

include fullDim hForest pair in
/-- **The other endpoint carries `p - 1` units of change above the block.** -/
theorem blockChange_single :
    blockChange data (endOf hc hab hOne star (other profile.doubleLabel))
        (M11IncomingPartitions.selectedMergedBlock data hc hab hOne blk) =
      (doubleCount data hc hab hOne star profile : ℤ) - 1 := by
  rw [blockChange_endOf data hc hab hOne fullDim star pair (other profile.doubleLabel),
    show (M11IncomingPartitions.selectedMergedBlock data hc hab hOne blk).1 = blk.1 from rfl,
    count_single data hc hab hOne star profile (other_ne profile.doubleLabel),
    contracted_count data hc hab hOne fullDim hForest star pair profile,
    single_count data hc hab hOne star profile]
  push_cast
  ring

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest star pair profile in
theorem blockChange_nonneg (hValid : data.Valid) (vertex : target.V)
    (mblk : (mergedPartition data a b).Blocks) : 0 ≤ blockChange data vertex mblk :=
  Finset.sum_nonneg fun sourceBlock _ ↦
    data.localRamification_nonneg vertex (hValid.2 vertex) sourceBlock

include fullDim hForest pair in
/-- **`p ∈ {1, 2}`: Figure 37's two gluings, and nothing else.** -/
theorem doubleCount_bounds :
    doubleCount data hc hab hOne star profile = 1 ∨
      doubleCount data hc hab hOne star profile = 2 := by
  have hDouble := blockChange_double data hc hab hOne fullDim hForest star pair profile
  have hSingle := blockChange_single data hc hab hOne fullDim hForest star pair profile
  have hNonnegDouble := blockChange_nonneg data fullDim.valid
    (endOf hc hab hOne star profile.doubleLabel)
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne blk)
  have hNonnegSingle := blockChange_nonneg data fullDim.valid
    (endOf hc hab hOne star (other profile.doubleLabel))
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne blk)
  rw [hDouble] at hNonnegDouble
  rw [hSingle] at hNonnegSingle
  omega


/-! ### The endpoint dictionary above one block

Four statements, and they are all the incoming side of Figures 37 and 38 at one
ramification-one block.  The first and last hold in both gluings; the middle
two are the two values of `p`. -/

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest pair in
/-- **The block's other endpoint carries the whole block** (both gluings). -/
theorem single_end_block (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel blk.1 sheet) :
    (data.vertexPartition (endOf hc hab hOne star (other profile.doubleLabel))).block sheet =
      (mergedPartition data a b).block sheet := by
  refine SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ _
    (endOf_refines data hc hab hOne star (other profile.doubleLabel)) sheet ?_
  rw [← blockCountWithin_congr _ (mergedPartition data a b) hSheet]
  exact single_count data hc hab hOne star profile

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest pair in
/-- **Gluing I (`p = 1`): the doubled direction's endpoint carries the whole
block too.** -/
theorem double_end_block_of_one (hCount : doubleCount data hc hab hOne star profile = 1)
    (sheet : Fin degree) (hSheet : (mergedPartition data a b).Rel blk.1 sheet) :
    (data.vertexPartition (endOf hc hab hOne star profile.doubleLabel)).block sheet =
      (mergedPartition data a b).block sheet := by
  refine SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ _
    (endOf_refines data hc hab hOne star profile.doubleLabel) sheet ?_
  rw [← blockCountWithin_congr _ (mergedPartition data a b) hSheet]
  exact hCount

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest pair in
/-- **Gluing II (`p = 2`): the doubled direction's endpoint carries that
direction's own occurrence partition.** -/
theorem double_end_block_of_two (hCount : doubleCount data hc hab hOne star profile = 2)
    (sheet : Fin degree) (hSheet : (mergedPartition data a b).Rel blk.1 sheet) :
    (data.vertexPartition (endOf hc hab hOne star profile.doubleLabel)).block sheet =
      (data.edgePartition (wallOcc hc hab hOne star profile.doubleLabel)).block sheet := by
  refine (block_eq_of_blockCountWithin_eq _ _ (mergedPartition data a b)
    (refines_of_mem_incidentEdges data
      (wallOcc_mem_endOf hc hab hOne star profile.doubleLabel))
    (endOf_refines data hc hab hOne star profile.doubleLabel)
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne blk) ?_ sheet hSheet).symm
  rw [show (M11IncomingPartitions.selectedMergedBlock data hc hab hOne blk).1 = blk.1 from rfl,
    count_double data hc hab hOne star profile]
  exact hCount.symm

include fullDim hForest pair in
/-- **The contracted occurrence and the doubled direction's endpoint induce
the same partition above the block** (both gluings). -/
theorem contracted_block_eq (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel blk.1 sheet) :
    (data.edgePartition contracted).block sheet =
      (data.vertexPartition (endOf hc hab hOne star profile.doubleLabel)).block sheet :=
  block_eq_of_blockCountWithin_eq _ _ (mergedPartition data a b)
    (refines_of_mem_incidentEdges data
      (contracted_mem_endOf hc hab hOne star profile.doubleLabel))
    (endOf_refines data hc hab hOne star profile.doubleLabel)
    (M11IncomingPartitions.selectedMergedBlock data hc hab hOne blk)
    (contracted_count data hc hab hOne fullDim hForest star pair profile) sheet hSheet

end BlockCensus


/-! ## §8  The coupling: `ch u = ch v = 1` determines the member

Part I's proof of (⋆) for Case `{w2-r1}`: *"in `M⁽ᵠ⁾`, `δ⁽ᵠ⁾(Ã) ≠ δ⁽ᵠ⁾(B̃)`
because `ch u = ch v = 1`.  So `δ⁽ᵠ⁾(Ã)` determines the gluing datum."*  That is
this section, and it is
derived: each restored endpoint carries exactly one unit of change (§4), the
background carries none (§6), so the two blocks' changes at one endpoint add to
one -- and §7 turned each of those into `2 - p` or `p - 1`.  The resulting
arithmetic has a unique solution `q : Fin 2` with `p(A₀) = 1 ↔ q = δ(A₀)` and
`p(B₀) = 1 ↔ other q = δ(B₀)`, which is exactly `Pair.resolution`'s own
opposite pairing. -/

section PairCensus

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  (pair : Pair (contractDatum data hc hab hOne) star)

/-- Two distinct directions of a divalent wall are opposite. -/
theorem other_of_ne {first second : Fin 2} (hNe : first ≠ second) : first = other second := by
  revert hNe
  revert first second
  decide

/-- `A₀`'s parameter: how many classes `A₀`'s doubled direction's endpoint
induces above `A₀`. -/
noncomputable def firstCount : ℕ :=
  doubleCount data hc hab hOne star pair.firstProfile.toOccurrenceProfile

/-- `B₀`'s parameter. -/
noncomputable def secondCount : ℕ :=
  doubleCount data hc hab hOne star pair.secondProfile.toOccurrenceProfile

include fullDim hForest pair in
/-- Off both blocks a restored endpoint is unramified, at every sheet. -/
theorem background_localRamification_endOf (label : Fin 2) (sheet : Fin degree)
    (hOffFirst : ¬ (mergedPartition data a b).Rel pair.first.1 sheet)
    (hOffSecond : ¬ (mergedPartition data a b).Rel pair.second.1 sheet) :
    data.localRamification (endOf hc hab hOne star label)
      ((data.vertexPartition (endOf hc hab hOne star label)).toBlock sheet) = 0 := by
  have hEnds := W3Nd2IncomingBackground.AnyBlock.background_localRamification_endpoints_eq_zero
    data hc hab hOne fullDim hForest
    (background_zero_of_off data hc hab hOne star pair hOffFirst hOffSecond) sheet
    (merged_rel_ofSheet data hc hab hOne sheet)
  rcases endOf_cases hc hab hOne star label with hEq | hEq
  · rw [hEq]; exact hEnds.1
  · rw [hEq]; exact hEnds.2

include fullDim hForest pair in
/-- **The whole change of one restored endpoint sits above `A₀` and `B₀`.** -/
theorem targetChange_split (label : Fin 2) :
    (1 : ℤ) =
      blockChange data (endOf hc hab hOne star label)
          (M11IncomingPartitions.selectedMergedBlock data hc hab hOne pair.first) +
        blockChange data (endOf hc hab hOne star label)
          (M11IncomingPartitions.selectedMergedBlock data hc hab hOne pair.second) := by
  classical
  have hChange := endOf_targetChange data hc hab hOne fullDim star pair label
  have hDisj : Disjoint
      (SheetPartition.blocksWithin
        (data.vertexPartition (endOf hc hab hOne star label)) (mergedPartition data a b)
        (M11IncomingPartitions.selectedMergedBlock data hc hab hOne pair.first))
      (SheetPartition.blocksWithin
        (data.vertexPartition (endOf hc hab hOne star label)) (mergedPartition data a b)
        (M11IncomingPartitions.selectedMergedBlock data hc hab hOne pair.second)) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxA hxB
    rw [SheetPartition.mem_blocksWithin] at hxA hxB
    have hBlocks := hxA.symm.trans hxB
    have hSheets : pair.first.1 = pair.second.1 := congrArg (fun t ↦ t.1) hBlocks
    exact pair.distinct (Subtype.ext hSheets)
  have hZero : ∀ x ∈ (Finset.univ :
      Finset (data.vertexPartition (endOf hc hab hOne star label)).Blocks),
      x ∉ SheetPartition.blocksWithin
          (data.vertexPartition (endOf hc hab hOne star label)) (mergedPartition data a b)
          (M11IncomingPartitions.selectedMergedBlock data hc hab hOne pair.first) ∪
        SheetPartition.blocksWithin
          (data.vertexPartition (endOf hc hab hOne star label)) (mergedPartition data a b)
          (M11IncomingPartitions.selectedMergedBlock data hc hab hOne pair.second) →
      data.localRamification (endOf hc hab hOne star label) x = 0 := by
    intro x _ hNotMem
    have hOffFirst : ¬ (mergedPartition data a b).Rel pair.first.1 x.1 := by
      intro hRel
      exact hNotMem (Finset.mem_union_left _ ((SheetPartition.mem_blocksWithin _ _ _ _).mpr
        ((SheetPartition.fineBlockToCoarseBlock_eq_iff_rel _ (mergedPartition data a b) x
          (M11IncomingPartitions.selectedMergedBlock data hc hab hOne pair.first)).mpr hRel)))
    have hOffSecond : ¬ (mergedPartition data a b).Rel pair.second.1 x.1 := by
      intro hRel
      exact hNotMem (Finset.mem_union_right _ ((SheetPartition.mem_blocksWithin _ _ _ _).mpr
        ((SheetPartition.fineBlockToCoarseBlock_eq_iff_rel _ (mergedPartition data a b) x
          (M11IncomingPartitions.selectedMergedBlock data hc hab hOne pair.second)).mpr hRel)))
    have hBlock : (data.vertexPartition (endOf hc hab hOne star label)).toBlock x.1 = x :=
      Subtype.ext x.2
    exact hBlock ▸ background_localRamification_endOf data hc hab hOne fullDim hForest star
      pair label x.1 hOffFirst hOffSecond
  rw [← hChange, GluingDatum.targetChange,
    ← Finset.sum_subset (Finset.subset_univ _) hZero, Finset.sum_union hDisj]
  rfl


omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
theorem firstCount_eq :
    firstCount data hc hab hOne star pair =
      doubleCount data hc hab hOne star pair.firstProfile.toOccurrenceProfile := rfl

omit [Fintype coordinate] [DecidableEq coordinate] fullDim hForest in
theorem secondCount_eq :
    secondCount data hc hab hOne star pair =
      doubleCount data hc hab hOne star pair.secondProfile.toOccurrenceProfile := rfl

include fullDim hForest pair in
/-- **`δ⁽ᵠ⁾(Ã) ≠ δ⁽ᵠ⁾(B̃)` (Part I, proof of (⋆) for Case `{w2-r1}`),
derived.**  One member index `q : Fin 2`
names the census at *both* ramification-one blocks: `A₀` stays whole exactly
when `q` is its own doubled direction, and `B₀` stays whole exactly when
`other q` is *its* doubled direction.  That is precisely the opposite pairing
`W2R1SourceCandidates.Pair.resolution` builds, and it is forced by
`ch u = ch v = 1` together with the background census. -/
theorem exists_member_selected_counts :
    ∃ q : Fin 2,
      firstCount data hc hab hOne star pair =
          (if q = pair.firstProfile.doubleLabel then 1 else 2) ∧
        secondCount data hc hab hOne star pair =
          (if other q = pair.secondProfile.doubleLabel then 1 else 2) := by
  rw [firstCount_eq, secondCount_eq] at *
  have hBounds := doubleCount_bounds data hc hab hOne fullDim hForest star pair
    pair.firstProfile.toOccurrenceProfile
  have hSplit := targetChange_split data hc hab hOne fullDim hForest star pair
    pair.firstProfile.doubleLabel
  have hFirst := blockChange_double data hc hab hOne fullDim hForest star pair
    pair.firstProfile.toOccurrenceProfile
  by_cases hSame : pair.firstProfile.doubleLabel = pair.secondProfile.doubleLabel
  · have hSecond : blockChange data (endOf hc hab hOne star pair.firstProfile.doubleLabel)
        (M11IncomingPartitions.selectedMergedBlock data hc hab hOne pair.second) =
          2 - (doubleCount data hc hab hOne star pair.secondProfile.toOccurrenceProfile : ℤ) := by
      rw [hSame]
      exact blockChange_double data hc hab hOne fullDim hForest star pair
        pair.secondProfile.toOccurrenceProfile
    rw [hFirst, hSecond] at hSplit
    rcases hBounds with hOneCase | hTwoCase
    · refine ⟨pair.firstProfile.doubleLabel, by rw [ite_eq_left rfl]; exact hOneCase, ?_⟩
      rw [ite_eq_right (by rw [← hSame]; exact other_ne pair.firstProfile.doubleLabel)]
      omega
    · refine ⟨other pair.firstProfile.doubleLabel,
        by rw [ite_eq_right (other_ne pair.firstProfile.doubleLabel)]; exact hTwoCase, ?_⟩
      rw [ite_eq_left (by rw [other_other pair.firstProfile.doubleLabel]; exact hSame)]
      omega
  · have hOpposite : pair.firstProfile.doubleLabel = other pair.secondProfile.doubleLabel :=
      other_of_ne hSame
    have hOtherEq : other pair.firstProfile.doubleLabel = pair.secondProfile.doubleLabel := by
      rw [hOpposite, other_other]
    have hSecond : blockChange data (endOf hc hab hOne star pair.firstProfile.doubleLabel)
        (M11IncomingPartitions.selectedMergedBlock data hc hab hOne pair.second) =
          (doubleCount data hc hab hOne star pair.secondProfile.toOccurrenceProfile : ℤ) - 1 := by
      rw [hOpposite]
      exact blockChange_single data hc hab hOne fullDim hForest star pair
        pair.secondProfile.toOccurrenceProfile
    rw [hFirst, hSecond] at hSplit
    rcases hBounds with hOneCase | hTwoCase
    · refine ⟨pair.firstProfile.doubleLabel, by rw [ite_eq_left rfl]; exact hOneCase, ?_⟩
      rw [ite_eq_left hOtherEq]
      omega
    · refine ⟨other pair.firstProfile.doubleLabel,
        by rw [ite_eq_right (other_ne pair.firstProfile.doubleLabel)]; exact hTwoCase, ?_⟩
      rw [ite_eq_right (by rw [other_other pair.firstProfile.doubleLabel]; exact hSame)]
      omega

end PairCensus

end DraismaVargas.LocalCases.W2R1IncomingCensus
