module

public import DraismaVargas.Infrastructure.PartitionNormalization

@[expose] public section

/-!
# Realizing a bijection of blocks by a permutation of sheets

Arguments of the form "an invariant determines the class" share one
construction primitive: turning a block-level isomorphism into sheet
permutations, by building a permutation from a family of bijections between
equal-cardinality blocks that matches chosen representatives.

This file is that construction, stated for a single `SheetPartition` pair and
then lifted to a `GluingDatum`.  `DiagonalTargetIso` uses it for the sheet
layer of the datum isomorphisms of the ballot classification, which underlies
the base count over the caterpillar of loops (step 1 of
`DraismaVargasCount/Assembly.lean`).

## Relation to `PartitionNormalization`

`Infrastructure.PartitionNormalization.sheetRelabeling` is not the general
primitive.  `PartitionNormalization.permutation` re-chooses representatives
inside blocks, and `sheetRelabeling` does so with a separate permutation at
every target vertex and every occurrence, with the edge-to-vertex
compatibility checked.  On the axis that matters here — how far the blocks may
move — both are the **identity block bijection**: `SameBlocks` says the two
partitions have literally the same blocks, and the permutation only re-chooses
representatives inside each of them.

The general case — a block bijection that actually *moves* blocks — is what is
built here, as `SheetPartition.BlockMatching` and its `perm`.

## What is proved

**§1.** `SheetPartition.BlockMatching first second`: a cardinality-preserving
bijection of the blocks of `first` onto the blocks of `second`, presented as a
map on sheets naming, for each sheet, the `second`-representative of the block
matched to that sheet's `first`-block.  Four fields; surjectivity onto the
blocks of `second` is **not** one of them — it is derived (`exists_map`).

**§2.** `blockPerm`: a permutation carrying each block of `first` onto the
matched block of `second`, hence with `(first.relabel blockPerm).SameBlocks
second`.  The engine is one `Finset.equivOfCardEq` per block; injectivity
propagates from `rel_of_map_eq`, and bijectivity is then finiteness.

**§3.** `perm`, the primitive proper: `blockPerm` followed by
`PartitionNormalization.permutation`, which is exactly the
representative-matching half.  `relabel_perm : first.relabel matching.perm =
second` on the nose; `perm_repr : matching.perm (first.repr sheet) =
matching.map sheet` is "matching chosen representatives"; `repr_perm` and
`image_block` say what it does to representatives and to blocks.

**§4.** The primitive is *exact*: `exists_perm_iff_nonempty_blockMatching` —
two sheet partitions differ by a permutation **iff** there is a
cardinality-preserving bijection of their blocks.  `ofRelabel` is the reverse
construction, `refl`/`trans` the composition law, and `ofSameBlocks` the
identity block bijection, at which `PartitionNormalization.permutation` already
realizes both conclusions of §3 (`permutation_realizes_ofSameBlocks`).

**§4, witness.** `exampleMatching` is a `BlockMatching` between two partitions
of `Fin 3` that are provably *not* `SameBlocks`
(`exampleFirst_not_sameBlocks_exampleSecond`), so the structure is not a
re-spelling of blockwise agreement and §3 is not vacuous on inputs
`PartitionNormalization.permutation` cannot take.

**§5.** `GluingDatum.DatumMatching` and `DatumMatching.sheetRelabeling`: the
same construction at every target vertex and occurrence, with the
edge-to-vertex compatibility discharged from a hypothesis on the *block maps*
alone — no condition relating the chosen within-block bijections is needed,
because the compatibility is tested at the coarser vertex partition.
`DatumMatching.ofSameBlocks` exhibits `PartitionNormalization.sheetRelabeling`'s
hypotheses as the identity-matching instance, so that construction is a
special case of this one.

## Scope

* **Nothing here produces a `BlockMatching`.**  Every statement takes one as a
  hypothesis, and §4 shows why the construction cannot do more: a
  `BlockMatching` is *equivalent* to the permutation it builds, so the
  primitive never discharges the hypothesis that two candidates have the same
  combinatorial type.  It only changes the shape in which that hypothesis may
  be supplied.
* **`perm` is not canonical.**  `blockEquiv` is a `Finset.equivOfCardEq`, an
  arbitrary choice inside each block, so `perm` is noncomputable and is *not*
  equal to `PartitionNormalization.permutation` even when the matching is
  `ofSameBlocks h`.  What is proved is that both satisfy `relabel … = second`
  and agree on representatives, which is everything the consumers read.
  Consequently `DatumMatching.sheetRelabeling` and
  `PartitionNormalization.sheetRelabeling` are two witnesses, not one term.
* **No count is performed.**  Nothing about `Count.MemberIso`,
  full-dimensionality or cardinality appears in this file.
* **`DatumMatching.compatible_left`/`compatible_right` are hypotheses.**  They
  are implied by the matchings being induced by one global permutation, and by
  the identity matching (§5's `DatumMatching.ofSameBlocks`), but they are not implied by
  the vertex and edge matchings alone: a block matching at an occurrence may
  send a block outside the vertex block that the vertex matching prescribes.
-/

namespace DraismaVargas.Infrastructure

open Finset

namespace SheetPartition

variable {d : ℕ}

/-! ## 1.  Block matchings -/

/-- **A cardinality-preserving bijection of the blocks of `first` onto the
blocks of `second`.**

The bijection is presented as a map on sheets: `map sheet` is the
`second`-representative of the block matched to the `first`-block of `sheet`.
That presentation avoids quotients entirely.

Surjectivity onto the blocks of `second` is deliberately *not* a field: it
follows from the four below by counting, and is proved as `exists_map`. -/
structure BlockMatching (first second : SheetPartition d) where
  /-- The `second`-representative matched to the `first`-block of a sheet. -/
  map : Fin d → Fin d
  /-- `map` reads only the `first`-block of its argument. -/
  map_repr : ∀ sheet, map (first.repr sheet) = map sheet
  /-- `map` names a `second`-representative. -/
  repr_map : ∀ sheet, second.repr (map sheet) = map sheet
  /-- Distinct `first`-blocks are matched to distinct `second`-blocks. -/
  rel_of_map_eq : ∀ i j, map i = map j → first.Rel i j
  /-- Matched blocks have the same cardinality. -/
  blockCard_map : ∀ sheet, second.blockCard (map sheet) = first.blockCard sheet

namespace BlockMatching

variable {first second : SheetPartition d} (matching : BlockMatching first second)

theorem map_eq_of_rel {i j : Fin d} (h : first.Rel i j) :
    matching.map i = matching.map j := by
  rw [← matching.map_repr i, ← matching.map_repr j,
    show first.repr i = first.repr j from h]

@[simp] theorem rel_map_iff (i j : Fin d) :
    second.Rel (matching.map i) (matching.map j) ↔ first.Rel i j := by
  constructor
  · intro h
    refine matching.rel_of_map_eq i j ?_
    have hEq : second.repr (matching.map i) = second.repr (matching.map j) := h
    rwa [matching.repr_map, matching.repr_map] at hEq
  · intro h
    show second.repr (matching.map i) = second.repr (matching.map j)
    rw [matching.map_eq_of_rel h]

/-! ## 2.  The permutation that moves the blocks -/

/-- One chosen bijection of the `first`-block of a sheet onto the matched
`second`-block.  This is the only choice the construction makes, and it is the
reason `perm` is noncomputable. -/
noncomputable def blockEquiv (sheet : Fin d) :
    {x : Fin d // x ∈ first.block sheet} ≃
      {y : Fin d // y ∈ second.block (matching.map sheet)} :=
  Finset.equivOfCardEq
    (show (first.block sheet).card = (second.block (matching.map sheet)).card from
      (matching.blockCard_map sheet).symm)

/-- The underlying sheet map: send a sheet through the chosen bijection of its
own block. -/
noncomputable def toFun (sheet : Fin d) : Fin d :=
  (matching.blockEquiv (first.repr sheet) ⟨sheet, by simp [first.repr_idem]⟩ : Fin d)

theorem toFun_eq {anchor sheet : Fin d} (h : first.repr sheet = anchor)
    (hMem : sheet ∈ first.block anchor) :
    matching.toFun sheet = (matching.blockEquiv anchor ⟨sheet, hMem⟩ : Fin d) := by
  subst h
  rfl

theorem repr_toFun (sheet : Fin d) :
    second.repr (matching.toFun sheet) = matching.map sheet := by
  have hMem : matching.toFun sheet ∈ second.block (matching.map (first.repr sheet)) :=
    (matching.blockEquiv (first.repr sheet) ⟨sheet, by simp [first.repr_idem]⟩).2
  have hRel : second.Rel (matching.map (first.repr sheet)) (matching.toFun sheet) :=
    (second.mem_block_iff _ _).mp hMem
  have hEq : second.repr (matching.map (first.repr sheet))
      = second.repr (matching.toFun sheet) := hRel
  rw [matching.repr_map, matching.map_repr] at hEq
  exact hEq.symm

theorem toFun_injective : Function.Injective matching.toFun := by
  intro i j hij
  have hMap : matching.map i = matching.map j := by
    rw [← matching.repr_toFun i, ← matching.repr_toFun j, hij]
  have hRel : first.Rel i j := matching.rel_of_map_eq i j hMap
  have hMemI : i ∈ first.block (first.repr j) := by
    refine (first.mem_block_iff _ _).mpr ?_
    show first.repr (first.repr j) = first.repr i
    rw [first.repr_idem]
    exact hRel.symm
  have hMemJ : j ∈ first.block (first.repr j) := by simp [first.repr_idem]
  rw [matching.toFun_eq (show first.repr i = first.repr j from hRel) hMemI,
    matching.toFun_eq (show first.repr j = first.repr j from rfl) hMemJ] at hij
  have hSub := (matching.blockEquiv (first.repr j)).injective (Subtype.ext hij)
  exact congrArg Subtype.val hSub

/-- **The block-moving permutation.**  It carries each block of `first` onto
the matched block of `second`; it says nothing about representatives. -/
noncomputable def blockPerm : Equiv.Perm (Fin d) :=
  Equiv.ofBijective matching.toFun
    (Finite.injective_iff_bijective.mp matching.toFun_injective)

@[simp] theorem blockPerm_apply (sheet : Fin d) :
    matching.blockPerm sheet = matching.toFun sheet := rfl

theorem repr_blockPerm (sheet : Fin d) :
    second.repr (matching.blockPerm sheet) = matching.map sheet :=
  matching.repr_toFun sheet

theorem sameBlocks_relabel_blockPerm :
    (first.relabel matching.blockPerm).SameBlocks second := by
  intro a b
  obtain ⟨i, rfl⟩ := matching.blockPerm.surjective a
  obtain ⟨j, rfl⟩ := matching.blockPerm.surjective b
  rw [relabel_rel_iff]
  constructor
  · intro h
    show second.repr (matching.blockPerm i) = second.repr (matching.blockPerm j)
    rw [matching.repr_blockPerm, matching.repr_blockPerm, matching.map_eq_of_rel h]
  · intro h
    refine matching.rel_of_map_eq i j ?_
    rw [← matching.repr_blockPerm, ← matching.repr_blockPerm]
    exact h

/-! ## 3.  The primitive -/

/-- **The permutation realizing a block matching.**  Move the blocks, then
re-choose the representatives with `PartitionNormalization.permutation`. -/
noncomputable def perm : Equiv.Perm (Fin d) :=
  matching.blockPerm.trans
    (PartitionNormalization.permutation (first.relabel matching.blockPerm) second
      matching.sameBlocks_relabel_blockPerm)

/-- **It carries one partition to the other, on the nose** -- stored
representatives included, not merely up to `SameBlocks`. -/
theorem relabel_perm : first.relabel matching.perm = second := by
  have hStep := PartitionNormalization.relabel_eq (first.relabel matching.blockPerm)
    second matching.sameBlocks_relabel_blockPerm
  rwa [relabel_relabel] at hStep

/-- **It matches the chosen representatives**: this is the
representative-matching half of the primitive, and it is what
`PartitionNormalization` supplies. -/
theorem perm_repr (sheet : Fin d) :
    matching.perm (first.repr sheet) = matching.map sheet := by
  have hFix : (first.relabel matching.blockPerm).repr
      (matching.blockPerm (first.repr sheet)) = matching.blockPerm (first.repr sheet) := by
    show matching.blockPerm (first.repr (matching.blockPerm.symm
      (matching.blockPerm (first.repr sheet)))) = _
    rw [Equiv.symm_apply_apply, first.repr_idem]
  have hStep := PartitionNormalization.permutation_repr (first.relabel matching.blockPerm)
    second matching.sameBlocks_relabel_blockPerm (matching.blockPerm (first.repr sheet))
  rw [hFix] at hStep
  show PartitionNormalization.permutation (first.relabel matching.blockPerm) second
    matching.sameBlocks_relabel_blockPerm (matching.blockPerm (first.repr sheet)) = _
  rw [hStep, matching.repr_blockPerm, matching.map_repr]

theorem repr_perm (sheet : Fin d) :
    second.repr (matching.perm sheet) = matching.map sheet := by
  have hStep : (first.relabel matching.perm).repr (matching.perm sheet)
      = matching.perm (first.repr sheet) := by
    show matching.perm (first.repr (matching.perm.symm (matching.perm sheet))) = _
    rw [Equiv.symm_apply_apply]
  rw [matching.relabel_perm] at hStep
  rw [hStep, matching.perm_repr]

/-- **And it carries blocks to blocks.** -/
theorem image_block (sheet : Fin d) :
    (first.block sheet).image matching.perm = second.block (matching.map sheet) := by
  have hStep := first.relabel_block matching.perm sheet
  rw [matching.relabel_perm] at hStep
  rw [← hStep]
  refine second.block_eq_of_rel ?_
  show second.repr (matching.perm sheet) = second.repr (matching.map sheet)
  rw [matching.repr_perm, matching.repr_map]

/-- **Every block of `second` is matched.**  Not a field of the structure: the
four fields already force it, because the realizing permutation is onto. -/
theorem exists_map (sheet : Fin d) :
    ∃ other, matching.map other = second.repr sheet := by
  refine ⟨matching.perm.symm sheet, ?_⟩
  rw [← matching.repr_perm, Equiv.apply_symm_apply]

/-! ## 4.  The primitive is exact -/

/-- Any permutation carrying `first` to `second` *is* a block matching. -/
def ofRelabel (first second : SheetPartition d) (permutation : Equiv.Perm (Fin d))
    (h : first.relabel permutation = second) : BlockMatching first second where
  map sheet := permutation (first.repr sheet)
  map_repr sheet := by rw [first.repr_idem]
  repr_map sheet := by
    rw [← h]
    show permutation (first.repr (permutation.symm (permutation (first.repr sheet)))) = _
    rw [Equiv.symm_apply_apply, first.repr_idem]
  rel_of_map_eq i j hEq := permutation.injective hEq
  blockCard_map sheet := by
    rw [← h, relabel_blockCard]
    exact congrArg Finset.card (first.block_eq_of_rel (first.rel_repr_left sheet))

/-- **Two sheet partitions differ by a permutation exactly when their blocks
are matched.**  This is the sense in which the primitive is the whole of the
problem: nothing weaker than a block matching can be turned into a
permutation, and nothing stronger is needed. -/
theorem exists_perm_iff_nonempty_blockMatching (first second : SheetPartition d) :
    (∃ permutation : Equiv.Perm (Fin d), first.relabel permutation = second) ↔
      Nonempty (BlockMatching first second) :=
  ⟨fun ⟨permutation, h⟩ ↦ ⟨ofRelabel first second permutation h⟩,
    fun ⟨matching⟩ ↦ ⟨matching.perm, matching.relabel_perm⟩⟩

/-- The identity block matching. -/
def refl (partition : SheetPartition d) : BlockMatching partition partition where
  map := partition.repr
  map_repr sheet := by rw [partition.repr_idem]
  repr_map sheet := partition.repr_idem sheet
  rel_of_map_eq _ _ hEq := hEq
  blockCard_map sheet :=
    congrArg Finset.card (partition.block_eq_of_rel (partition.rel_repr_left sheet))

/-- Block matchings compose. -/
def trans {third : SheetPartition d} (matching : BlockMatching first second)
    (later : BlockMatching second third) : BlockMatching first third where
  map sheet := later.map (matching.map sheet)
  map_repr sheet := by rw [matching.map_repr]
  repr_map sheet := later.repr_map _
  rel_of_map_eq i j hEq :=
    (matching.rel_map_iff i j).mp (later.rel_of_map_eq _ _ hEq)
  blockCard_map sheet := by rw [later.blockCard_map, matching.blockCard_map]

/-! ### The identity block bijection is the `SameBlocks` case -/

/-- `SameBlocks` is exactly "the block bijection is the identity". -/
def ofSameBlocks {first second : SheetPartition d} (h : first.SameBlocks second) :
    BlockMatching first second where
  map := second.repr
  map_repr sheet := (h _ _).mp (first.rel_repr_left sheet)
  repr_map sheet := second.repr_idem sheet
  rel_of_map_eq _ _ hEq := (h _ _).mpr hEq
  blockCard_map sheet := by
    rw [show second.blockCard (second.repr sheet) = second.blockCard sheet from
      congrArg Finset.card (second.block_eq_of_rel (second.rel_repr_left sheet))]
    exact (h.blockCard_eq sheet).symm

@[simp] theorem ofSameBlocks_map {first second : SheetPartition d}
    (h : first.SameBlocks second) (sheet : Fin d) :
    (ofSameBlocks h).map sheet = second.repr sheet := rfl

/-- **`PartitionNormalization.permutation` is this construction at the identity
block bijection**: it satisfies both conclusions of §3 for `ofSameBlocks h`. -/
theorem permutation_realizes_ofSameBlocks {first second : SheetPartition d}
    (h : first.SameBlocks second) :
    first.relabel (PartitionNormalization.permutation first second h) = second ∧
      ∀ sheet, PartitionNormalization.permutation first second h (first.repr sheet)
        = (ofSameBlocks h).map sheet :=
  ⟨PartitionNormalization.relabel_eq first second h,
    PartitionNormalization.permutation_repr first second h⟩

end BlockMatching

/-! ### Two representative facts about `SameBlocks`

Under `SameBlocks`, each partition's representative map absorbs the other's:
the representative of a representative is the representative. -/

theorem SameBlocks.repr_second {first second : SheetPartition d}
    (h : first.SameBlocks second) (sheet : Fin d) :
    second.repr (first.repr sheet) = second.repr sheet :=
  (h _ _).mp (first.rel_repr_left sheet)

theorem SameBlocks.repr_first {first second : SheetPartition d}
    (h : first.SameBlocks second) (sheet : Fin d) :
    first.repr (second.repr sheet) = first.repr sheet :=
  (h _ _).mpr (second.rel_repr_left sheet)

/-! ### A bounded witness: the general case is not the `SameBlocks` case

Three sheets, blocks `{0,1} {2}` against `{0} {1,2}`.  The block bijection
swaps the two blocks, so the two partitions are *not* `SameBlocks`, and yet a
`BlockMatching` exists.  Everything here is decided on `Fin 3`. -/

/-- Blocks `{0,1}` and `{2}`. -/
def exampleFirst : SheetPartition 3 := ⟨![0, 0, 2], by decide⟩

/-- Blocks `{0}` and `{1,2}`. -/
def exampleSecond : SheetPartition 3 := ⟨![0, 1, 1], by decide⟩

theorem exampleFirst_not_sameBlocks_exampleSecond :
    ¬ exampleFirst.SameBlocks exampleSecond := fun h ↦
  absurd ((h 0 1).mp (by decide)) (by decide)

/-- The block bijection that exchanges the two-element block with the
one-element one. -/
def exampleMatching : BlockMatching exampleFirst exampleSecond where
  map := ![1, 1, 0]
  map_repr := by decide
  repr_map := by decide
  rel_of_map_eq := by decide
  blockCard_map := by decide

/-- So the general primitive genuinely moves blocks: `exampleFirst` and
`exampleSecond` differ by a sheet permutation although no `SameBlocks`
hypothesis relates them, and `PartitionNormalization.permutation` is not
defined on this input. -/
theorem exists_perm_exampleFirst_exampleSecond :
    ∃ permutation : Equiv.Perm (Fin 3), exampleFirst.relabel permutation = exampleSecond :=
  ⟨exampleMatching.perm, exampleMatching.relabel_perm⟩

end SheetPartition

/-! ## 5.  The same construction over a gluing datum -/

namespace GluingDatum

variable {target : CFGraph} {degree : ℕ}

/-- **A block matching at every target vertex and every occurrence.**

`compatible_left`/`compatible_right` are the only coupling between them, and
they constrain the block *maps* only: the chosen within-block bijections are
independent, because the gluing compatibility is tested at the coarser vertex
partition. -/
structure DatumMatching (data other : GluingDatum target degree) where
  /-- The matching above a target vertex. -/
  vertex : ∀ vertex, SheetPartition.BlockMatching (data.vertexPartition vertex)
    (other.vertexPartition vertex)
  /-- The matching above an occurrence. -/
  edge : ∀ edge, SheetPartition.BlockMatching (data.edgePartition edge)
    (other.edgePartition edge)
  /-- An occurrence's block goes into the block its first endpoint's does. -/
  compatible_left : ∀ (occurrence : target.edges) (sheet : Fin degree),
    (other.vertexPartition (occurrence : target.V × target.V).1).Rel
      ((edge occurrence).map sheet)
      ((vertex (occurrence : target.V × target.V).1).map sheet)
  /-- And likewise at the second endpoint. -/
  compatible_right : ∀ (occurrence : target.edges) (sheet : Fin degree),
    (other.vertexPartition (occurrence : target.V × target.V).2).Rel
      ((edge occurrence).map sheet)
      ((vertex (occurrence : target.V × target.V).2).map sheet)

namespace DatumMatching

/-- **The gluing compatibility, from the block maps alone.**  No relation
between the two chosen within-block bijections is needed. -/
theorem rel_symm_perm {degree : ℕ} {vertexSource vertexTarget edgeSource edgeTarget :
      SheetPartition degree}
    (vertexMatching : SheetPartition.BlockMatching vertexSource vertexTarget)
    (edgeMatching : SheetPartition.BlockMatching edgeSource edgeTarget)
    (hRefines : edgeTarget.Refines vertexTarget)
    (hCompatible : ∀ sheet, vertexTarget.Rel (edgeMatching.map sheet) (vertexMatching.map sheet))
    (sheet : Fin degree) :
    vertexSource.Rel (vertexMatching.perm.symm (edgeMatching.perm sheet)) sheet := by
  have hEdge : edgeTarget.Rel (edgeMatching.perm sheet) (edgeMatching.map sheet) := by
    show edgeTarget.repr (edgeMatching.perm sheet) = edgeTarget.repr (edgeMatching.map sheet)
    rw [edgeMatching.repr_perm, edgeMatching.repr_map]
  have hVertex : vertexTarget.Rel (vertexMatching.map sheet) (vertexMatching.perm sheet) := by
    show vertexTarget.repr (vertexMatching.map sheet)
      = vertexTarget.repr (vertexMatching.perm sheet)
    rw [vertexMatching.repr_map, vertexMatching.repr_perm]
  have hChain : vertexTarget.Rel (edgeMatching.perm sheet) (vertexMatching.perm sheet) :=
    (hRefines.rel hEdge).trans ((hCompatible sheet).trans hVertex)
  have hBack : (vertexSource.relabel vertexMatching.perm).Rel
      (vertexMatching.perm (vertexMatching.perm.symm (edgeMatching.perm sheet)))
      (vertexMatching.perm sheet) := by
    rw [Equiv.apply_symm_apply, vertexMatching.relabel_perm]
    exact hChain
  exact (vertexSource.relabel_rel_iff vertexMatching.perm _ _).mp hBack

variable {data other : GluingDatum target degree}

/-- **The sheet relabelling realizing a datum matching.** -/
noncomputable def sheetRelabeling (matching : DatumMatching data other) :
    data.SheetRelabeling where
  vertexPermutation vertex := (matching.vertex vertex).perm
  edgePermutation edge := (matching.edge edge).perm
  compatible_left edge sheet :=
    rel_symm_perm (matching.vertex (edge : target.V × target.V).1) (matching.edge edge)
      (other.refines_left edge) (matching.compatible_left edge) sheet
  compatible_right edge sheet :=
    rel_symm_perm (matching.vertex (edge : target.V × target.V).2) (matching.edge edge)
      (other.refines_right edge) (matching.compatible_right edge) sheet

@[simp] theorem sheetRelabeling_apply (matching : DatumMatching data other) :
    (sheetRelabeling matching).apply = other :=
  gluingDatum_ext (funext fun vertex ↦ (matching.vertex vertex).relabel_perm)
    (funext fun edge ↦ (matching.edge edge).relabel_perm)

/-- **`PartitionNormalization.sheetRelabeling`'s hypotheses are the identity
datum matching.**  So `PartitionNormalization.sheetRelabeling` is the
identity-bijection case of this construction. -/
def ofSameBlocks
    (hVertices : ∀ vertex,
      (data.vertexPartition vertex).SameBlocks (other.vertexPartition vertex))
    (hEdges : ∀ edge, (data.edgePartition edge).SameBlocks (other.edgePartition edge)) :
    DatumMatching data other where
  vertex vertex := SheetPartition.BlockMatching.ofSameBlocks (hVertices vertex)
  edge edge := SheetPartition.BlockMatching.ofSameBlocks (hEdges edge)
  compatible_left edge sheet :=
    ((other.refines_left edge).rel
      ((other.edgePartition edge).rel_repr_left sheet)).trans
      ((other.vertexPartition (edge : target.V × target.V).1).rel_repr_right sheet)
  compatible_right edge sheet :=
    ((other.refines_right edge).rel
      ((other.edgePartition edge).rel_repr_left sheet)).trans
      ((other.vertexPartition (edge : target.V × target.V).2).rel_repr_right sheet)

/-- The blockwise corollary, reproved through the general construction. -/
theorem exists_sheetRelabeling_of_sameBlocks
    (hVertices : ∀ vertex,
      (data.vertexPartition vertex).SameBlocks (other.vertexPartition vertex))
    (hEdges : ∀ edge, (data.edgePartition edge).SameBlocks (other.edgePartition edge)) :
    ∃ relabeling : data.SheetRelabeling, relabeling.apply = other :=
  ⟨sheetRelabeling (ofSameBlocks hVertices hEdges),
    sheetRelabeling_apply (ofSameBlocks hVertices hEdges)⟩

end DatumMatching

end GluingDatum

end DraismaVargas.Infrastructure
