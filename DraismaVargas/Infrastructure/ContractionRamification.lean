module

public import DraismaVargas.Infrastructure.Change
public import DraismaVargas.Infrastructure.GluingContraction

@[expose] public section

/-!
# Ramification is additive under contraction

`DraismaVargas/Infrastructure/GluingContraction.lean` contracts a gluing datum
along one target edge occurrence and proves everything about the result except
the local Riemann--Hurwitz inequality *at the merged vertex*.  This file
supplies that last piece, which is Draisma--Vargas `prop-rphi-under-contraction`:
when the source fibre above the contracted occurrence is a forest, the local
ramification of a merged block is the sum of the local ramifications of the
blocks it merges.

## The double count

Fix the contracted occurrence with endpoints `a`, `b` and a block `A₀` of the
merged partition `mergedPartition data a b = join (vertexPartition a)
(vertexPartition b)`.  Three families of blocks live inside `A₀`:

* the `p` blocks of `vertexPartition a` inside `A₀`;
* the `q` blocks of `vertexPartition b` inside `A₀`;
* the `E` blocks of `edgePartition contracted` inside `A₀`.

Reading the first two as vertices and the third as edges of a bipartite fibre
graph, `ContractionForest` is the hypothesis `E + 1 = p + q`: the fibre graph is
connected (`A₀` is a single join class) and acyclic.  It is *not* derived here:
it is a hypothesis on the source topology, supplied at a terminal face, and it
is genuinely restrictive.

Writing `N(f)` for the number of blocks of `edgePartition f` inside `A₀`, the
two sides of the additivity are

```
∑ over the p + q fibre blocks   =  ∑_{f ∋ a} N(f) + ∑_{g ∋ b} N(g)
                                      - 2(p + q) - |A₀|(val a + val b - 4)
r₀(A₀)                          =  ∑_{f ∋ a} N(f) + ∑_{g ∋ b} N(g) - 2 N(c)
                                      - 2 - |A₀|(val a + val b - 4),
```

because the star of the merged vertex is the union of the two old stars with
the contracted occurrence removed (`sum_incidentEdges_merge`,
`card_incidentEdges_merge`), and every other occurrence is incident to exactly
one of `a`, `b` (`incidentEdges_inter`).  The two agree exactly when
`N(c) + 1 = p + q`, which is the forest hypothesis.

The bookkeeping inputs are `sum_blockCard_blocksWithin_local` (the fine blocks
inside a coarse block partition it — a local copy of the lemma of the same name
in `DraismaVargas/LocalCases/StableLocalProperties.lean`, which this
infrastructure module may not import) and the transitivity of induced block
counts along a tower of refinements (`sum_blockCountWithin_trans`), proved
here.

Main results:

* `sum_blockCountWithin_trans` — counts of fine blocks compose along a tower;
* `eq_one_of_sum_eq_card`, `blockCountWithin_mono`,
  `blockCountWithin_eq_one_of_refines`, `block_eq_of_blockCountWithin_eq`,
  `blockCountWithin_eq_two`, `blockCountWithin_of_discrete` — generic
  induced-block counting, used by the census arguments of the local cases;
* `card_incidentEdges_merge`, `sum_incidentEdges_merge` — the star of the
  merged vertex;
* `ContractionForest` — the forest hypothesis, in the plain count form;
* `localRamificationAt_contractDatum_merge`,
  `localRamification_contractDatum_merge` — the additivity;
* `riemannHurwitzAtTargetVertex_contractDatum_merge` — local Riemann--Hurwitz
  at the merged vertex;
* `valid_contractDatum`, `valid_contractDatumAt` — the contracted datum is
  valid.
-/

namespace DraismaVargas.Infrastructure

namespace ContractionRamification

open GraphContraction GluingContraction

/-! ### Borrowed bookkeeping

`DraismaVargas/LocalCases/StableLocalProperties.lean` proves both statements
below, but that module belongs to the application layer, which
`DraismaVargas/Infrastructure/` may not import.  Local copies with the `_local`
suffix keep this file inside the infrastructure layer. -/

section Borrowed

variable {degree : ℕ}

/-- A coarse block is the disjoint union of the fine blocks it contains, in the
`blocksWithin` presentation of that fibre.  Local copy of
`StableLocalProperties.sum_blockCard_blocksWithin`. -/
theorem sum_blockCard_blocksWithin_local
    (fine coarse : SheetPartition degree) (hRefines : fine.Refines coarse)
    (coarseBlock : coarse.Blocks) :
    (∑ fineBlock ∈ SheetPartition.blocksWithin fine coarse coarseBlock,
        (fine.blockCard fineBlock.1 : ℤ)) =
      (coarse.blockCard coarseBlock.1 : ℤ) := by
  classical
  have hImage :
      (SheetPartition.blocksWithin fine coarse coarseBlock).image Subtype.val =
        (Finset.univ : Finset (Fin degree)).filter fun representative ↦
          fine.repr representative = representative ∧
            coarse.Rel coarseBlock.1 representative := by
    ext representative
    constructor
    · intro hMember
      obtain ⟨fineBlock, hFineBlock, hValue⟩ := Finset.mem_image.mp hMember
      have hRel : coarse.Rel coarseBlock.1 fineBlock.1 :=
        (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel fine coarse
          fineBlock coarseBlock).mp
          ((SheetPartition.mem_blocksWithin fine coarse coarseBlock
            fineBlock).mp hFineBlock)
      subst hValue
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fineBlock.2, hRel⟩
    · intro hMember
      obtain ⟨hIdempotent, hRel⟩ := (Finset.mem_filter.mp hMember).2
      refine Finset.mem_image.mpr ⟨⟨representative, hIdempotent⟩, ?_, rfl⟩
      exact (SheetPartition.mem_blocksWithin fine coarse coarseBlock _).mpr
        ((SheetPartition.fineBlockToCoarseBlock_eq_iff_rel fine coarse _
          coarseBlock).mpr hRel)
  calc
    (∑ fineBlock ∈ SheetPartition.blocksWithin fine coarse coarseBlock,
        (fine.blockCard fineBlock.1 : ℤ)) =
        ∑ representative ∈
            (SheetPartition.blocksWithin fine coarse coarseBlock).image
              Subtype.val,
          (fine.blockCard representative : ℤ) := by
      refine (Finset.sum_image
        (s := SheetPartition.blocksWithin fine coarse coarseBlock)
        (g := (Subtype.val : fine.Blocks → Fin degree))
        (f := fun representative ↦ (fine.blockCard representative : ℤ)) ?_).symm
      intro first _ second _ hValue
      exact Subtype.ext hValue
    _ = ∑ representative ∈ (Finset.univ : Finset (Fin degree)).filter
          (fun representative ↦ fine.repr representative = representative ∧
            coarse.Rel coarseBlock.1 representative),
        (fine.blockCard representative : ℤ) := by
      rw [hImage]
    _ = ∑ representative : Fin degree,
        if fine.repr representative = representative ∧
            coarse.Rel coarseBlock.1 representative then
          (fine.blockCard representative : ℤ)
        else 0 := by
      rw [Finset.sum_filter]
    _ = (coarse.blockCard coarseBlock.1 : ℤ) :=
      SheetPartition.sum_blockCard_representatives_eq_blockCard fine coarse
        hRefines coarseBlock.1

/-- The edge partition above a target occurrence incident to a vertex refines
the vertex partition there.  Local copy of
`StableLocalProperties.refines_of_mem_incidentEdges`. -/
theorem refines_of_mem_incidentEdges_local {target : CFGraph}
    (data : GluingDatum target degree) {vertex : target.V}
    {edge : target.edges}
    (hMember : edge ∈ GluingDatum.incidentEdges vertex) :
    (data.edgePartition edge).Refines (data.vertexPartition vertex) := by
  have hEnds := (Finset.mem_filter.mp hMember).2
  rcases hEnds with hLeft | hRight
  · simpa [hLeft] using data.refines_left edge
  · simpa [hRight] using data.refines_right edge

end Borrowed

/-! ### Block counts along a tower of refinements -/

section Partitions

variable {degree : ℕ}

/-- The number of fine blocks inside a coarse block depends only on the coarse
block. -/
theorem blockCountWithin_congr (fine coarse : SheetPartition degree)
    {first second : Fin degree} (hRel : coarse.Rel first second) :
    fine.blockCountWithin coarse first = fine.blockCountWithin coarse second := by
  unfold SheetPartition.blockCountWithin
  rw [coarse.block_eq_of_rel hRel]

/-- The local degree of a block depends only on the block. -/
theorem blockCard_congr (coarse : SheetPartition degree)
    {first second : Fin degree} (hRel : coarse.Rel first second) :
    coarse.blockCard first = coarse.blockCard second := by
  unfold SheetPartition.blockCard
  rw [coarse.block_eq_of_rel hRel]

/-- The fine blocks inside a coarse block that map to a fixed intermediate
block are exactly the fine blocks inside that intermediate block. -/
theorem blocksWithin_filter_fineBlockToCoarseBlock
    (fine mid coarse : SheetPartition degree) (hMidCoarse : mid.Refines coarse)
    {coarseBlock : coarse.Blocks} {midBlock : mid.Blocks}
    (hMid : midBlock ∈ SheetPartition.blocksWithin mid coarse coarseBlock) :
    ((SheetPartition.blocksWithin fine coarse coarseBlock).filter
        fun fineBlock ↦
          SheetPartition.fineBlockToCoarseBlock fine mid fineBlock = midBlock)
      = SheetPartition.blocksWithin fine mid midBlock := by
  classical
  have hMidRel : coarse.Rel coarseBlock.1 midBlock.1 :=
    (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel mid coarse midBlock
      coarseBlock).mp
      ((SheetPartition.mem_blocksWithin mid coarse coarseBlock midBlock).mp hMid)
  ext fineBlock
  simp only [Finset.mem_filter, SheetPartition.mem_blocksWithin]
  refine ⟨fun hMember ↦ hMember.2, fun hMember ↦ ⟨?_, hMember⟩⟩
  have hRel : mid.Rel midBlock.1 fineBlock.1 :=
    (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel fine mid fineBlock
      midBlock).mp hMember
  exact (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel fine coarse fineBlock
    coarseBlock).mpr (hMidRel.trans (hMidCoarse.rel hRel))

/-- Counting fine blocks inside a coarse block by first sorting them into the
intermediate blocks. -/
theorem sum_card_blocksWithin_trans (fine mid coarse : SheetPartition degree)
    (hMidCoarse : mid.Refines coarse) (coarseBlock : coarse.Blocks) :
    (∑ midBlock ∈ SheetPartition.blocksWithin mid coarse coarseBlock,
        (SheetPartition.blocksWithin fine mid midBlock).card)
      = (SheetPartition.blocksWithin fine coarse coarseBlock).card := by
  classical
  have hMaps : ∀ fineBlock ∈ SheetPartition.blocksWithin fine coarse coarseBlock,
      SheetPartition.fineBlockToCoarseBlock fine mid fineBlock
        ∈ SheetPartition.blocksWithin mid coarse coarseBlock := by
    intro fineBlock hFineBlock
    rw [SheetPartition.mem_blocksWithin] at hFineBlock ⊢
    have hRel : coarse.Rel coarseBlock.1 fineBlock.1 :=
      (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel fine coarse fineBlock
        coarseBlock).mp hFineBlock
    refine (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel mid coarse _
      coarseBlock).mpr ?_
    exact hRel.trans (hMidCoarse.rel (mid.rel_repr_right fineBlock.1))
  rw [Finset.card_eq_sum_card_fiberwise hMaps]
  refine Finset.sum_congr rfl fun midBlock hMid ↦ ?_
  rw [blocksWithin_filter_fineBlockToCoarseBlock fine mid coarse hMidCoarse hMid]

/-- Induced block counts compose along a tower of refinements: the fine blocks
inside one coarse block are distributed among the intermediate blocks it
contains. -/
theorem sum_blockCountWithin_trans (fine mid coarse : SheetPartition degree)
    (hFineMid : fine.Refines mid) (hMidCoarse : mid.Refines coarse)
    (coarseBlock : coarse.Blocks) :
    (∑ midBlock ∈ SheetPartition.blocksWithin mid coarse coarseBlock,
        (fine.blockCountWithin mid midBlock.1 : ℤ))
      = (fine.blockCountWithin coarse coarseBlock.1 : ℤ) := by
  classical
  rw [← SheetPartition.card_blocksWithin_eq_blockCountWithin fine coarse
      (hFineMid.trans hMidCoarse) coarseBlock,
    ← sum_card_blocksWithin_trans fine mid coarse hMidCoarse coarseBlock,
    Nat.cast_sum]
  refine Finset.sum_congr rfl fun midBlock _ ↦ ?_
  rw [SheetPartition.card_blocksWithin_eq_blockCountWithin fine mid hFineMid
    midBlock]


/-! ### Generic sheet-partition counting

The six statements below are generic facts about induced block counts, used by
the census arguments of the local cases (for instance
`LocalCases.W2MkkSelectedCensus` and `LocalCases.W2PIncomingCensus`).  They
live here, and not in `Infrastructure/Change.lean` beside
`SheetPartition.card_blocks_eq_sum_blockCountWithin`, because the only
non-elementary inputs of their proofs are `sum_blockCountWithin_trans` and
`blockCountWithin_congr` just above, which are this module's; `Change` sits
strictly below it and cannot see them. -/

/-- Natural summands bounded below by one that add up to the number of
summands are all equal to one. -/
theorem eq_one_of_sum_eq_card {α : Type*} {s : Finset α} {f : α → ℕ}
    (hOne : ∀ x ∈ s, 1 ≤ f x) (hSum : ∑ x ∈ s, f x = s.card)
    {x : α} (hx : x ∈ s) : f x = 1 := by
  by_contra hNe
  have hAtLeast := hOne x hx
  have hTwo : 1 < f x := by omega
  have hLt : ∑ _y ∈ s, 1 < ∑ y ∈ s, f y :=
    Finset.sum_lt_sum (fun y hy ↦ hOne y hy) ⟨x, hx, hTwo⟩
  rw [hSum, Finset.sum_const, smul_eq_mul, mul_one] at hLt
  exact lt_irrefl _ hLt

/-- **A coarsening never has more induced blocks.**  Each of the `mid` blocks
inside the coarse block contains at least one `fine` block. -/
theorem blockCountWithin_mono (fine mid coarse : SheetPartition degree)
    (hFineMid : fine.Refines mid) (hMidCoarse : mid.Refines coarse)
    (coarseBlock : coarse.Blocks) :
    mid.blockCountWithin coarse coarseBlock.1 ≤
      fine.blockCountWithin coarse coarseBlock.1 := by
  classical
  have hSum := sum_blockCountWithin_trans fine mid coarse hFineMid hMidCoarse coarseBlock
  have hCards := SheetPartition.card_blocksWithin_eq_blockCountWithin mid coarse
    hMidCoarse coarseBlock
  have hLower : (SheetPartition.blocksWithin mid coarse coarseBlock).card * 1 ≤
      ∑ midBlock ∈ SheetPartition.blocksWithin mid coarse coarseBlock,
        fine.blockCountWithin mid midBlock.1 := by
    rw [← smul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ 1
      (fun midBlock _ ↦ SheetPartition.blockCountWithin_pos fine mid midBlock.1)
  rw [mul_one, hCards] at hLower
  have hCast : ((∑ midBlock ∈ SheetPartition.blocksWithin mid coarse coarseBlock,
      fine.blockCountWithin mid midBlock.1 : ℕ) : ℤ) =
      (fine.blockCountWithin coarse coarseBlock.1 : ℤ) := by
    rw [Nat.cast_sum]; exact hSum
  have hNat : ∑ midBlock ∈ SheetPartition.blocksWithin mid coarse coarseBlock,
      fine.blockCountWithin mid midBlock.1 =
      fine.blockCountWithin coarse coarseBlock.1 := by exact_mod_cast hCast
  omega

/-- If a partition induces a single class inside a coarse block, so does every
partition it refines. -/
theorem blockCountWithin_eq_one_of_refines
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

/-- **A refinement with the same induced count agrees throughout the block.** -/
theorem block_eq_of_blockCountWithin_eq (fine mid coarse : SheetPartition degree)
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
  have hMem : mid.toBlock sheet ∈ SheetPartition.blocksWithin mid coarse coarseBlock := by
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

/-- A partition whose classes inside one coarse block are the classes of two
named sheets contributes exactly two induced blocks there. -/
theorem blockCountWithin_eq_two (fine coarse : SheetPartition degree)
    (first second anchor : Fin degree)
    (hFirst : coarse.Rel anchor first) (hSecond : coarse.Rel anchor second)
    (hCovers : ∀ sheet, coarse.Rel anchor sheet →
      fine.Rel first sheet ∨ fine.Rel second sheet)
    (hSeparate : ¬ fine.Rel first second) :
    fine.blockCountWithin coarse anchor = 2 := by
  classical
  have hImage : (coarse.block anchor).image fine.repr =
      {fine.repr first, fine.repr second} := by
    ext value
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
      SheetPartition.mem_block_iff]
    constructor
    · rintro ⟨source, hSource, rfl⟩
      rcases hCovers source hSource with hRel | hRel
      · exact Or.inl (by rw [SheetPartition.rel_iff] at hRel; exact hRel.symm)
      · exact Or.inr (by rw [SheetPartition.rel_iff] at hRel; exact hRel.symm)
    · rintro (rfl | rfl)
      · exact ⟨first, hFirst, rfl⟩
      · exact ⟨second, hSecond, rfl⟩
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      intro h
      exact hSeparate (by rw [SheetPartition.rel_iff]; exact h)),
    Finset.card_singleton]

/-- A discrete partition induces as many blocks inside a coarse block as the
coarse block has sheets. -/
theorem blockCountWithin_of_discrete {fine coarse : SheetPartition degree}
    (hDiscrete : ∀ sheet, fine.repr sheet = sheet) (sheet : Fin degree) :
    fine.blockCountWithin coarse sheet = coarse.blockCard sheet := by
  classical
  unfold SheetPartition.blockCountWithin SheetPartition.blockCard
  congr 1
  ext value
  simp only [Finset.mem_image]
  exact ⟨by rintro ⟨x, hx, rfl⟩; rwa [hDiscrete x],
    fun hValue ↦ ⟨value, hValue, hDiscrete value⟩⟩

end Partitions

/-! ### The local ramification residual at an arbitrary sheet

`GluingDatum.localRamification` is indexed by a block of the vertex partition.
The contracted datum's vertex partition above the merged vertex is only
*propositionally* the join of the two endpoint partitions, so blocks of the two
do not have the same type.  Indexing the residual by a plain sheet avoids
transporting along that equality. -/

section Residual

variable {target : CFGraph} {degree : ℕ}

/-- The Riemann--Hurwitz residual of a gluing datum above a target vertex,
written at an arbitrary sheet instead of at a canonical block
representative. -/
def localRamificationAt (data : GluingDatum target degree) (vertex : target.V)
    (sheet : Fin degree) : ℤ :=
  (∑ edge ∈ GluingDatum.incidentEdges vertex,
    ((data.edgePartition edge).blockCountWithin
      (data.vertexPartition vertex) sheet : ℤ)) - 2 -
    ((data.vertexPartition vertex).blockCard sheet : ℤ) *
      (((GluingDatum.incidentEdges vertex).card : ℤ) - 2)

theorem localRamificationAt_block (data : GluingDatum target degree)
    (vertex : target.V) (block : (data.vertexPartition vertex).Blocks) :
    localRamificationAt data vertex block.1 =
      data.localRamification vertex block := rfl

/-- The residual depends only on the block of the sheet. -/
theorem localRamificationAt_congr (data : GluingDatum target degree)
    (vertex : target.V) {first second : Fin degree}
    (hRel : (data.vertexPartition vertex).Rel first second) :
    localRamificationAt data vertex first =
      localRamificationAt data vertex second := by
  have hCount : ∀ edge : target.edges,
      (data.edgePartition edge).blockCountWithin
          (data.vertexPartition vertex) first =
        (data.edgePartition edge).blockCountWithin
          (data.vertexPartition vertex) second :=
    fun edge ↦ blockCountWithin_congr _ _ hRel
  unfold localRamificationAt
  simp only [hCount, blockCard_congr _ hRel]

/-- The local Riemann--Hurwitz condition is the nonnegativity of the
residual. -/
theorem riemannHurwitzAtTargetVertex_iff (data : GluingDatum target degree)
    (vertex : target.V) :
    data.RiemannHurwitzAtTargetVertex vertex ↔
      ∀ sheet, 0 ≤ localRamificationAt data vertex sheet := by
  unfold GluingDatum.RiemannHurwitzAtTargetVertex localRamificationAt
  exact forall_congr' fun _ ↦ ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩

end Residual

/-! ### The star of the merged vertex -/

section Star

variable {target : CFGraph} {a b : target.V} {contracted : target.edges}

/-- The contracted occurrence is incident to its first endpoint. -/
theorem contracted_mem_incidentEdges_left
    (hc : (contracted : target.V × target.V) = (a, b)) :
    contracted ∈ GluingDatum.incidentEdges a :=
  (mem_incidentEdges_iff a contracted).mpr (Or.inl (by rw [hc]))

/-- The contracted occurrence is incident to its second endpoint. -/
theorem contracted_mem_incidentEdges_right
    (hc : (contracted : target.V × target.V) = (a, b)) :
    contracted ∈ GluingDatum.incidentEdges b :=
  (mem_incidentEdges_iff b contracted).mpr (Or.inr (by rw [hc]))

/-- No surviving occurrence meets both endpoints of the contracted occurrence:
the contracted occurrence is the only one joining them. -/
theorem incidentEdges_inter (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1) :
    GluingDatum.incidentEdges a ∩ GluingDatum.incidentEdges b = {contracted} := by
  classical
  ext edge
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hLeft, hRight⟩
    rcases (mem_incidentEdges_iff a edge).mp hLeft with h₁ | h₁ <;>
      rcases (mem_incidentEdges_iff b edge).mp hRight with h₂ | h₂
    · exact absurd (h₁.symm.trans h₂) hab
    · exact eq_contracted_of_coe_eq_pair hc hOne (Prod.ext h₁ h₂)
    · refine absurd ?_ (notMem_swapped hc hab hOne)
      have hPair : (edge : target.V × target.V) = (b, a) := Prod.ext h₂ h₁
      rw [← hPair]
      exact Multiset.coe_mem
    · exact absurd (h₁.symm.trans h₂) hab
  · rintro rfl
    exact ⟨contracted_mem_incidentEdges_left hc,
      contracted_mem_incidentEdges_right hc⟩

/-- A surviving occurrence at either endpoint becomes an occurrence at the
merged vertex. -/
theorem foldEdge_mem_incidentEdges_merge
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {edge : target.edges}
    (hne : edge ≠ contracted)
    (hMember : edge ∈
      GluingDatum.incidentEdges a ∪ GluingDatum.incidentEdges b) :
    foldEdge hc hab hOne ⟨edge, hne⟩ ∈
      GluingDatum.incidentEdges
        (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩ := by
  have hLeft : fold target hab a = (⟨a, hab⟩ : GraphContraction.Vertex target b) :=
    GraphContraction.fold_a target hab
  have hRight : fold target hab b = (⟨a, hab⟩ : GraphContraction.Vertex target b) :=
    GraphContraction.fold_self target hab
  refine (mem_incidentEdges_iff _ _).mpr ?_
  show fold target hab (edge : target.V × target.V).1
        = (⟨a, hab⟩ : GraphContraction.Vertex target b)
      ∨ fold target hab (edge : target.V × target.V).2
        = (⟨a, hab⟩ : GraphContraction.Vertex target b)
  rcases Finset.mem_union.mp hMember with hIncident | hIncident
  · rcases (mem_incidentEdges_iff a edge).mp hIncident with h | h
    · exact Or.inl (by rw [h]; exact hLeft)
    · exact Or.inr (by rw [h]; exact hLeft)
  · rcases (mem_incidentEdges_iff b edge).mp hIncident with h | h
    · exact Or.inl (by rw [h]; exact hRight)
    · exact Or.inr (by rw [h]; exact hRight)

/-- The surviving occurrence underlying an occurrence at the merged vertex
meets one of the two old endpoints. -/
theorem unfoldEdge_mem_incidentEdges_union
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {edge : (GraphContraction.contract target hab hOne).edges}
    (hMember : edge ∈ GluingDatum.incidentEdges
      (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩) :
    unfoldEdge hc hab hOne edge ∈
      GluingDatum.incidentEdges a ∪ GluingDatum.incidentEdges b := by
  have hFold := fold_unfoldEdge hc hab hOne edge
  rcases (mem_incidentEdges_iff _ _).mp hMember with hEnd | hEnd
  · have hValue : fold target hab
        (unfoldEdge hc hab hOne edge : target.V × target.V).1
        = (⟨a, hab⟩ : GraphContraction.Vertex target b) :=
      (congrArg Prod.fst hFold).trans hEnd
    rcases (GraphContraction.fold_eq_iff target hab _ _).mp hValue with h | ⟨-, h⟩
    · exact Finset.mem_union_left _ ((mem_incidentEdges_iff a _).mpr (Or.inl h))
    · exact Finset.mem_union_right _ ((mem_incidentEdges_iff b _).mpr (Or.inl h))
  · have hValue : fold target hab
        (unfoldEdge hc hab hOne edge : target.V × target.V).2
        = (⟨a, hab⟩ : GraphContraction.Vertex target b) :=
      (congrArg Prod.snd hFold).trans hEnd
    rcases (GraphContraction.fold_eq_iff target hab _ _).mp hValue with h | ⟨-, h⟩
    · exact Finset.mem_union_left _ ((mem_incidentEdges_iff a _).mpr (Or.inr h))
    · exact Finset.mem_union_right _ ((mem_incidentEdges_iff b _).mpr (Or.inr h))

/-- The star of the merged vertex is the union of the two old stars with the
contracted occurrence removed. -/
theorem sum_incidentEdges_merge {M : Type*} [AddCommMonoid M]
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (value : (GraphContraction.contract target hab hOne).edges → M)
    (source : target.edges → M)
    (hCompat : ∀ (edge : target.edges) (hne : edge ≠ contracted),
      source edge = value (foldEdge hc hab hOne ⟨edge, hne⟩)) :
    (∑ edge ∈ (GluingDatum.incidentEdges a ∪
        GluingDatum.incidentEdges b).erase contracted, source edge)
      = ∑ edge ∈ GluingDatum.incidentEdges
          (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩,
        value edge := by
  classical
  refine Finset.sum_bij
    (fun edge hEdge ↦ foldEdge hc hab hOne ⟨edge, Finset.ne_of_mem_erase hEdge⟩)
    (fun edge hEdge ↦ foldEdge_mem_incidentEdges_merge hc hab hOne _
      (Finset.mem_of_mem_erase hEdge))
    (fun _ _ _ _ hEq ↦ congrArg Subtype.val (foldEdge_injective hc hab hOne hEq))
    (fun edge hEdge ↦ ⟨unfoldEdge hc hab hOne edge,
      Finset.mem_erase.mpr ⟨unfoldEdge_ne_contracted hc hab hOne edge,
        unfoldEdge_mem_incidentEdges_union hc hab hOne hEdge⟩,
      foldEdge_unfoldEdge hc hab hOne edge _⟩)
    (fun edge hEdge ↦ hCompat edge (Finset.ne_of_mem_erase hEdge))

/-- The valency of the merged vertex is the sum of the two old valencies less
the two ends of the contracted occurrence. -/
theorem card_incidentEdges_merge
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    (GluingDatum.incidentEdges
        (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card + 2
      = (GluingDatum.incidentEdges a).card
        + (GluingDatum.incidentEdges b).card := by
  classical
  have hMember : contracted ∈
      GluingDatum.incidentEdges a ∪ GluingDatum.incidentEdges b :=
    Finset.mem_union_left _ (contracted_mem_incidentEdges_left hc)
  have hBij := sum_incidentEdges_merge (M := ℕ) hc hab hOne (fun _ ↦ 1)
    (fun _ ↦ 1) (fun _ _ ↦ rfl)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hBij
  rw [Finset.card_erase_of_mem hMember] at hBij
  have hUnion := Finset.card_union_add_card_inter
    (GluingDatum.incidentEdges a) (GluingDatum.incidentEdges b)
  rw [incidentEdges_inter hc hab hOne, Finset.card_singleton] at hUnion
  have hPos : 1 ≤ (GluingDatum.incidentEdges a ∪
      GluingDatum.incidentEdges b).card :=
    Finset.card_pos.mpr ⟨contracted, hMember⟩
  omega

/-- Summing over the two old stars double counts the contracted occurrence and
counts every surviving occurrence once. -/
theorem sum_erase_union_incidentEdges
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (source : target.edges → ℤ) :
    (∑ edge ∈ (GluingDatum.incidentEdges a ∪
        GluingDatum.incidentEdges b).erase contracted, source edge)
      = (∑ edge ∈ GluingDatum.incidentEdges a, source edge)
        + (∑ edge ∈ GluingDatum.incidentEdges b, source edge)
        - 2 * source contracted := by
  classical
  have hMember : contracted ∈
      GluingDatum.incidentEdges a ∪ GluingDatum.incidentEdges b :=
    Finset.mem_union_left _ (contracted_mem_incidentEdges_left hc)
  have hUnion := Finset.sum_union_inter (s₁ := GluingDatum.incidentEdges a)
    (s₂ := GluingDatum.incidentEdges b) (f := source)
  rw [incidentEdges_inter hc hab hOne, Finset.sum_singleton] at hUnion
  have hErase := Finset.sum_erase_add
    (GluingDatum.incidentEdges a ∪ GluingDatum.incidentEdges b) source hMember
  linarith

end Star

/-! ### The merged partition and the forest hypothesis -/

section Forest

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
variable {contracted : target.edges}

/-- The sheet partition above the merged vertex: the join of the two endpoint
partitions of the contracted occurrence. -/
noncomputable def mergedPartition (data : GluingDatum target degree)
    (a b : target.V) : SheetPartition degree :=
  SheetPartition.join (data.vertexPartition a) (data.vertexPartition b)

theorem contractDatum_vertexPartition_merge (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    (contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩
      = mergedPartition data a b :=
  contractVertexPartition_merge data a b hab

theorem vertexPartition_refines_mergedPartition
    (data : GluingDatum target degree) (a b : target.V) :
    (data.vertexPartition a).Refines (mergedPartition data a b) :=
  SheetPartition.left_refines_join _ _

theorem vertexPartition_refines_mergedPartition_right
    (data : GluingDatum target degree) (a b : target.V) :
    (data.vertexPartition b).Refines (mergedPartition data a b) :=
  SheetPartition.right_refines_join _ _

/-- The partition above the contracted occurrence refines the merged
partition. -/
theorem edgePartition_refines_mergedPartition
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) :
    (data.edgePartition contracted).Refines (mergedPartition data a b) :=
  (refines_of_mem_incidentEdges_local data (contracted_mem_incidentEdges_left hc)).trans
    (vertexPartition_refines_mergedPartition data a b)

/-- The source-topology hypothesis for the contracted occurrence, in the plain
count form: inside every block of the merged partition, the number of
blocks of the contracted occurrence's partition is one less than the total
number of blocks of the two endpoint partitions.  Reading the endpoint blocks as
vertices and the occurrence blocks as edges of the bipartite fibre graph above
the merged block, which is connected because a merged block is a single join
class, this says exactly that the fibre is a forest, hence a tree. -/
def ContractionForest (data : GluingDatum target degree) (a b : target.V)
    (contracted : target.edges) : Prop :=
  ∀ mergedBlock : (mergedPartition data a b).Blocks,
    (SheetPartition.blocksWithin (data.edgePartition contracted)
        (mergedPartition data a b) mergedBlock).card + 1
      = (SheetPartition.blocksWithin (data.vertexPartition a)
          (mergedPartition data a b) mergedBlock).card
        + (SheetPartition.blocksWithin (data.vertexPartition b)
            (mergedPartition data a b) mergedBlock).card

/-- The forest hypothesis in the induced-block-count form actually consumed by
the double count. -/
theorem contractionForest_count (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    (hForest : ContractionForest data a b contracted)
    (mergedBlock : (mergedPartition data a b).Blocks) :
    ((data.edgePartition contracted).blockCountWithin
        (mergedPartition data a b) mergedBlock.1 : ℤ) + 1
      = ((data.vertexPartition a).blockCountWithin
          (mergedPartition data a b) mergedBlock.1 : ℤ)
        + ((data.vertexPartition b).blockCountWithin
            (mergedPartition data a b) mergedBlock.1 : ℤ) := by
  have hEdge := SheetPartition.card_blocksWithin_eq_blockCountWithin
    (data.edgePartition contracted) (mergedPartition data a b)
    (edgePartition_refines_mergedPartition data hc) mergedBlock
  have hLeft := SheetPartition.card_blocksWithin_eq_blockCountWithin
    (data.vertexPartition a) (mergedPartition data a b)
    (vertexPartition_refines_mergedPartition data a b) mergedBlock
  have hRight := SheetPartition.card_blocksWithin_eq_blockCountWithin
    (data.vertexPartition b) (mergedPartition data a b)
    (vertexPartition_refines_mergedPartition_right data a b) mergedBlock
  have hCount := hForest mergedBlock
  rw [hEdge, hLeft, hRight] at hCount
  exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℤ)) hCount

end Forest

/-! ### The double count -/

section Additivity

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
variable {contracted : target.edges}

/-- One half of the additivity: the local ramifications of the blocks of one
endpoint partition inside a merged block add up to the incidence count of that
merged block, corrected by the number of blocks merged. -/
theorem sum_localRamification_blocksWithin (data : GluingDatum target degree)
    (vertex : target.V) (merged : SheetPartition degree)
    (hRefines : (data.vertexPartition vertex).Refines merged)
    (mergedBlock : merged.Blocks) :
    (∑ block ∈ SheetPartition.blocksWithin (data.vertexPartition vertex) merged
        mergedBlock, data.localRamification vertex block)
      = (∑ edge ∈ GluingDatum.incidentEdges vertex,
          ((data.edgePartition edge).blockCountWithin merged mergedBlock.1 : ℤ))
        - 2 * ((SheetPartition.blocksWithin (data.vertexPartition vertex) merged
            mergedBlock).card : ℤ)
        - (merged.blockCard mergedBlock.1 : ℤ)
          * (((GluingDatum.incidentEdges vertex).card : ℤ) - 2) := by
  classical
  have hIncidence :
      (∑ block ∈ SheetPartition.blocksWithin (data.vertexPartition vertex)
          merged mergedBlock,
        ∑ edge ∈ GluingDatum.incidentEdges vertex,
          ((data.edgePartition edge).blockCountWithin
            (data.vertexPartition vertex) block.1 : ℤ))
        = ∑ edge ∈ GluingDatum.incidentEdges vertex,
            ((data.edgePartition edge).blockCountWithin merged
              mergedBlock.1 : ℤ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun edge hEdge ↦ ?_
    exact sum_blockCountWithin_trans (data.edgePartition edge)
      (data.vertexPartition vertex) merged
      (refines_of_mem_incidentEdges_local data hEdge) hRefines mergedBlock
  have hDegree :
      (∑ block ∈ SheetPartition.blocksWithin (data.vertexPartition vertex)
          merged mergedBlock,
        ((data.vertexPartition vertex).blockCard block.1 : ℤ))
        = (merged.blockCard mergedBlock.1 : ℤ) :=
    sum_blockCard_blocksWithin_local (data.vertexPartition vertex) merged
      hRefines mergedBlock
  unfold GluingDatum.localRamification
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hIncidence,
    ← Finset.sum_mul, hDegree, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The linear identity behind the additivity: the merged residual and the sum
of the residuals of the merged blocks differ by the two counting relations. -/
private theorem merge_arith (leftStar rightStar edgeCount localDegree
    leftBlocks rightBlocks leftValency rightValency mergedValency : ℤ)
    (hValency : mergedValency + 2 = leftValency + rightValency)
    (hForest : edgeCount + 1 = leftBlocks + rightBlocks) :
    leftStar + rightStar - 2 * edgeCount - 2
        - localDegree * (mergedValency - 2)
      = (leftStar - 2 * leftBlocks - localDegree * (leftValency - 2))
        + (rightStar - 2 * rightBlocks
          - localDegree * (rightValency - 2)) := by
  linear_combination (-localDegree) * hValency - 2 * hForest

/-- Draisma--Vargas `prop-rphi-under-contraction`: if the source fibre above the
contracted occurrence is a forest, then the local ramification of a merged
block is the sum of the local ramifications of the blocks it merges. -/
theorem localRamificationAt_contractDatum_merge
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (mergedBlock : (mergedPartition data a b).Blocks) :
    localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ mergedBlock.1
      = (∑ block ∈ SheetPartition.blocksWithin (data.vertexPartition a)
            (mergedPartition data a b) mergedBlock,
          data.localRamification a block)
        + ∑ block ∈ SheetPartition.blocksWithin (data.vertexPartition b)
            (mergedPartition data a b) mergedBlock,
          data.localRamification b block := by
  classical
  have hStar :
      (∑ edge ∈ GluingDatum.incidentEdges
          (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩,
        (((contractDatum data hc hab hOne).edgePartition edge).blockCountWithin
          (mergedPartition data a b) mergedBlock.1 : ℤ))
        = (∑ edge ∈ GluingDatum.incidentEdges a,
            ((data.edgePartition edge).blockCountWithin
              (mergedPartition data a b) mergedBlock.1 : ℤ))
          + (∑ edge ∈ GluingDatum.incidentEdges b,
              ((data.edgePartition edge).blockCountWithin
                (mergedPartition data a b) mergedBlock.1 : ℤ))
          - 2 * ((data.edgePartition contracted).blockCountWithin
              (mergedPartition data a b) mergedBlock.1 : ℤ) := by
    rw [← sum_incidentEdges_merge hc hab hOne _
      (fun edge ↦ (((data.edgePartition edge).blockCountWithin
        (mergedPartition data a b) mergedBlock.1 : ℕ) : ℤ))
      (fun edge hne ↦ by rw [contractDatum_edgePartition_foldEdge])]
    exact sum_erase_union_incidentEdges hc hab hOne _
  have hValency : ((GluingDatum.incidentEdges
      (target := GraphContraction.contract target hab hOne)
        ⟨a, hab⟩).card : ℤ) + 2
      = ((GluingDatum.incidentEdges a).card : ℤ)
        + ((GluingDatum.incidentEdges b).card : ℤ) := by
    exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℤ))
      (card_incidentEdges_merge hc hab hOne)
  rw [sum_localRamification_blocksWithin data a (mergedPartition data a b)
      (vertexPartition_refines_mergedPartition data a b) mergedBlock,
    sum_localRamification_blocksWithin data b (mergedPartition data a b)
      (vertexPartition_refines_mergedPartition_right data a b) mergedBlock,
    SheetPartition.card_blocksWithin_eq_blockCountWithin
      (data.vertexPartition a) (mergedPartition data a b)
      (vertexPartition_refines_mergedPartition data a b) mergedBlock,
    SheetPartition.card_blocksWithin_eq_blockCountWithin
      (data.vertexPartition b) (mergedPartition data a b)
      (vertexPartition_refines_mergedPartition_right data a b) mergedBlock]
  unfold localRamificationAt
  rw [contractDatum_vertexPartition_merge data hc hab hOne, hStar]
  exact merge_arith _ _ _ _ _ _ _ _ _ hValency
    (contractionForest_count data hc hForest mergedBlock)

/-- The additivity, stated at a block of the contracted datum's vertex
partition above the merged vertex. -/
theorem localRamification_contractDatum_merge (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (block : ((contractDatum data hc hab hOne).vertexPartition
      ⟨a, hab⟩).Blocks) :
    (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ block
      = (∑ fibreBlock ∈ SheetPartition.blocksWithin (data.vertexPartition a)
            (mergedPartition data a b)
            ((mergedPartition data a b).toBlock block.1),
          data.localRamification a fibreBlock)
        + ∑ fibreBlock ∈ SheetPartition.blocksWithin (data.vertexPartition b)
            (mergedPartition data a b)
            ((mergedPartition data a b).toBlock block.1),
          data.localRamification b fibreBlock := by
  have hFixed : (mergedPartition data a b).repr block.1 = block.1 := by
    rw [← contractDatum_vertexPartition_merge data hc hab hOne]
    exact block.2
  have hMain := localRamificationAt_contractDatum_merge data hc hab hOne hForest
    ((mergedPartition data a b).toBlock block.1)
  rw [show ((mergedPartition data a b).toBlock block.1).1 = block.1 from hFixed]
    at hMain
  exact hMain

end Additivity

/-! ### Riemann--Hurwitz at the merged vertex, and validity -/

section Validity

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
variable {contracted : target.edges}

/-- The local Riemann--Hurwitz inequality at the merged vertex.  Each merged
block's residual is a sum of residuals of the blocks it merges, and those are
nonnegative by the Riemann--Hurwitz condition at the two old endpoints. -/
theorem riemannHurwitzAtTargetVertex_contractDatum_merge
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hLeft : data.RiemannHurwitzAtTargetVertex a)
    (hRight : data.RiemannHurwitzAtTargetVertex b) :
    (contractDatum data hc hab hOne).RiemannHurwitzAtTargetVertex
      (⟨a, hab⟩ : (GraphContraction.contract target hab hOne).V) := by
  rw [riemannHurwitzAtTargetVertex_iff] at hLeft hRight
  refine (riemannHurwitzAtTargetVertex_iff _ _).mpr ?_
  intro sheet
  have hRel : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
      sheet ((mergedPartition data a b).toBlock sheet).1 := by
    rw [contractDatum_vertexPartition_merge data hc hab hOne]
    exact (mergedPartition data a b).rel_repr_right sheet
  rw [localRamificationAt_congr _ _ hRel,
    localRamificationAt_contractDatum_merge data hc hab hOne hForest
      ((mergedPartition data a b).toBlock sheet)]
  exact add_nonneg (Finset.sum_nonneg fun block _ ↦ hLeft block.1)
    (Finset.sum_nonneg fun block _ ↦ hRight block.1)

/-- The contracted datum satisfies Riemann--Hurwitz everywhere. -/
theorem riemannHurwitz_contractDatum (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hRH : data.RiemannHurwitz) :
    (contractDatum data hc hab hOne).RiemannHurwitz := by
  rw [GluingDatum.riemannHurwitz_iff_forall_targetVertex]
  rintro ⟨vertex, hvb⟩
  by_cases hMerge : vertex = a
  · subst hMerge
    exact riemannHurwitzAtTargetVertex_contractDatum_merge data hc hab hOne
      hForest (hRH vertex) (hRH b)
  · exact riemannHurwitzAtTargetVertex_contractDatum_of_ne data hc hab hOne
      hvb hMerge (hRH vertex)

/-- Draisma--Vargas Definition 15 produces a gluing datum again: contracting a
target edge occurrence whose source fibre is a forest preserves validity. -/
theorem valid_contractDatum (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hValid : data.Valid) :
    (contractDatum data hc hab hOne).Valid :=
  ⟨connected_contractDatum data hc hab hOne hValid.1,
    riemannHurwitz_contractDatum data hc hab hOne hForest hValid.2⟩

/-- The forest hypothesis at a chosen target occurrence. -/
def ContractionForestAt (data : GluingDatum target degree)
    (edge : target.edges) : Prop :=
  ContractionForest data (edge : target.V × target.V).1
    (edge : target.V × target.V).2 edge

/-- Validity of the contraction at a chosen target occurrence. -/
theorem valid_contractDatumAt (data : GluingDatum target degree)
    (edge : target.edges)
    (hOne : num_edges target (edge : target.V × target.V).1
      (edge : target.V × target.V).2 = 1)
    (hForest : ContractionForestAt data edge) (hValid : data.Valid) :
    (contractDatumAt data edge hOne).Valid :=
  valid_contractDatum data rfl (fst_ne_snd edge) hOne hForest hValid

end Validity

end ContractionRamification

end DraismaVargas.Infrastructure
