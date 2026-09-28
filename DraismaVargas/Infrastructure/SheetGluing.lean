import DraismaVargas.Infrastructure.GraphContraction

/-!
# Gluing sheets: joining blocks, and the degree raise that survives it

The other operations on a `GluingDatum` in this library move the *target*: an
isomorphism (`GluingTransport`), a vertex expansion (`GlobalResolution`), an edge
contraction (`GluingContraction`).  Correspondingly `GluingDatum.Connected` is
otherwise concluded in four ways -- those three and a finite `decide` replay on
a concrete datum (`checkConnected_eq_true_iff`).  **All four fix `degree`, and
none of them merges sheet blocks.**  `SheetPartition` likewise is stated at a
fixed `d` and relates `SheetPartition d` to nothing at `d + 1`.

This file supplies operations in the *sheet* direction, and the connectivity
that goes with them.

## The graph engine

* `graph_connected_of_surjective`: connectedness survives a surjection carrying
  occurrences to occurrences -- a quotient of a connected graph is connected.
* `ConnectedOn`, `connectedOn_image` and `graph_connected_of_connectedOn_union`:
  the same cut argument for a *part* of a graph, and the gluing of two connected
  parts that cover the graph and share a vertex.

## Joining two blocks (the lemma)

* `GluingDatum.coarsenVertices` replaces every vertex partition by a coarser
  one, keeping the occurrence partitions, and `coarsenVertices_connected`
  transports connectedness along it.
* `GluingDatum.mergeVertexBlocks` joins the blocks of `first` and `extra` above
  one target vertex.  **`mergeVertexBlocks_connected`: joining two blocks of the
  vertex partition of a connected source keeps it connected.**
  `mergeVertexBlocks_riemannHurwitz` is the other half -- above the merged block
  the induced occurrence-block counts add
  (`SheetPartition.mergeBlocks_blockCountWithin_first`, where the refinement
  hypothesis is used), so the merged slack is the sum of the two old slacks plus
  `2` -- and `mergeVertexBlocks_valid` is both.

## Raising the degree

* `SheetPartition.addSheet` puts one more sheet alone in its own block, and
  `SheetPartition.gluedPartition` places it by an `Option`: `none` alone,
  `some old` inside the block of `old`.
* `GluingDatum.addSheetDatum` is the bare raise.  It is never connected -- the
  fresh sheet spans a disjoint copy of the target.
  `addSheetDatum_riemannHurwitz` records that the local condition is free.
* `GluingDatum.addSheetGluedOn` raises the degree and glues the fresh sheet
  where a choice function says.  **`addSheetGluedOn_valid`: one glued target
  vertex suffices** -- the glued source is covered by the image of the old
  source and by the fresh copy of the target, which share the glued vertex, and
  the target is connected for free by `graph_connected_target_of_connected`.
* `GluingDatum.addSheetGlued` is the everywhere-glued case (definitionally, by
  `addSheetGlued_eq_addSheetGluedOn`).  It is recorded separately because its
  connectedness needs no hypothesis at all: every source vertex of the glued
  datum is an old source vertex, so `connected_of_sheetMap` applies along
  `Fin.castSucc`.
* `GluingDatum.glueFreshSheetAt` is the same move written as one
  `mergeVertexBlocks` on `addSheetDatum`, for a caller that wants to glue one
  target vertex at a time: `glueFreshSheetAt_vertexPartition_of_ne` says the
  fresh sheet is still alone everywhere else, so the move composes -- three
  times, at the three arm leaves of a Cools--Draisma tripod step -- and
  `glueFreshSheetAt_riemannHurwitz` says each step is free.

## What is not claimed

* **No tripod step, and no target move.**  Everything here fixes the target;
  `TargetExpansion` is where the target moves.  A Cools--Draisma step is a
  target expansion *and* this degree raise, and composing them is not done
  here.
* **Nothing numerical.**  A bare raise leaves the length matrix alone; a
  *glued* raise does change the source blocks above the glued vertices, and
  this file computes no matrix, no stable path and no determinant.  `GluingDatum.Valid` is connectedness and local
  Riemann--Hurwitz and nothing else.
* **No genus count.**  The arithmetic a caller will want -- gluing at a set `W`
  of target vertices adds `|E(target)|` source occurrences and
  `|V(target)| - |W|` source vertices, so it raises the source genus by
  `genus(target) - 1 + |W|`, which for a tree target and three leaves is `2` --
  is *not* formalised here.  Only validity is.
* **The choice of where to glue is an input.**  It has to be: any placement of
  the fresh sheet other than alone is a choice of gluing.
-/

namespace DraismaVargas.Infrastructure

open Finset

/-! ## Connectivity along a surjection of graphs -/

/-- **Connectedness passes to a surjective image.**  If every vertex of `image`
is named by a vertex of `source`, and every occurrence of `source` produces an
occurrence of `image` between the images of its endpoints, then a connected
`source` forces a connected `image`.  A separating set of `image` pulls back to
a separating set of `source`, and the crossing occurrence found upstairs crosses
downstairs.

This is the cut-form statement that a quotient of a connected graph is
connected; no injectivity is required, so identifying two vertices is a special
case. -/
theorem graph_connected_of_surjective {source image : CFGraph}
    (vertexMap : source.V → image.V)
    (hSurjective : Function.Surjective vertexMap)
    (hEdges : ∀ first second : source.V,
      0 < num_edges source first second →
        0 < num_edges image (vertexMap first) (vertexMap second))
    (hConnected : graph_connected source) : graph_connected image := by
  intro separating hNontrivial
  obtain ⟨inside, outside, hInside, hOutside⟩ := hNontrivial
  obtain ⟨insideSource, hInsideSource⟩ := hSurjective inside
  obtain ⟨outsideSource, hOutsideSource⟩ := hSurjective outside
  set pullback : Finset source.V :=
    Finset.univ.filter fun vertex ↦ vertexMap vertex ∈ separating with hPullback
  have hMem : ∀ vertex : source.V,
      vertex ∈ pullback ↔ vertexMap vertex ∈ separating := by
    intro vertex
    rw [hPullback, Finset.mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ vertex, h⟩⟩
  obtain ⟨first, hFirst, second, hSecond, hPos⟩ :=
    hConnected pullback ⟨insideSource, outsideSource,
      (hMem insideSource).mpr (by rw [hInsideSource]; exact hInside),
      fun h ↦ hOutside (by rw [← hOutsideSource]; exact (hMem outsideSource).mp h)⟩
  exact ⟨vertexMap first, (hMem first).mp hFirst, vertexMap second,
    fun h ↦ hSecond ((hMem second).mpr h), hEdges first second hPos⟩

/-- **Cut-form connectedness of a part of a graph.**  No separating set splits
`part`: whenever `part` meets a set and its complement, some occurrence of the
whole graph crosses.  `graph_connected graph` is `ConnectedOn graph
Finset.univ`. -/
def ConnectedOn (graph : CFGraph) (part : Finset graph.V) : Prop :=
  ∀ separating : Finset graph.V,
    (∃ inside ∈ part, inside ∈ separating) →
      (∃ outside ∈ part, outside ∉ separating) →
        ∃ first ∈ separating, ∃ second ∉ separating,
          0 < num_edges graph first second

/-- **The image of a connected graph is connected on its image.**  The same
pullback argument as `graph_connected_of_surjective`, without surjectivity. -/
theorem connectedOn_image {source image : CFGraph} (vertexMap : source.V → image.V)
    (hEdges : ∀ first second : source.V,
      0 < num_edges source first second →
        0 < num_edges image (vertexMap first) (vertexMap second))
    (hConnected : graph_connected source) :
    ConnectedOn image (Finset.univ.image vertexMap) := by
  intro separating hInside hOutside
  obtain ⟨inside, hInsidePart, hInsideMem⟩ := hInside
  obtain ⟨outside, hOutsidePart, hOutsideMem⟩ := hOutside
  obtain ⟨insideSource, -, hInsideEq⟩ := Finset.mem_image.mp hInsidePart
  obtain ⟨outsideSource, -, hOutsideEq⟩ := Finset.mem_image.mp hOutsidePart
  set pullback : Finset source.V :=
    Finset.univ.filter fun vertex ↦ vertexMap vertex ∈ separating with hPullback
  have hMem : ∀ vertex : source.V,
      vertex ∈ pullback ↔ vertexMap vertex ∈ separating := by
    intro vertex
    rw [hPullback, Finset.mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ vertex, h⟩⟩
  obtain ⟨first, hFirst, second, hSecond, hPos⟩ :=
    hConnected pullback ⟨insideSource, outsideSource,
      (hMem insideSource).mpr (by rw [hInsideEq]; exact hInsideMem),
      fun h ↦ hOutsideMem (by rw [← hOutsideEq]; exact (hMem outsideSource).mp h)⟩
  exact ⟨vertexMap first, (hMem first).mp hFirst, vertexMap second,
    fun h ↦ hSecond ((hMem second).mpr h), hEdges first second hPos⟩

/-- **Two connected parts covering the graph and sharing a vertex make it
connected.**  A separating set that splits the whole graph splits one of the two
parts, because the shared vertex lies on one side and the split vertex on the
other. -/
theorem graph_connected_of_connectedOn_union {graph : CFGraph}
    {left right : Finset graph.V} (hCover : left ∪ right = Finset.univ)
    {shared : graph.V} (hSharedLeft : shared ∈ left) (hSharedRight : shared ∈ right)
    (hLeft : ConnectedOn graph left) (hRight : ConnectedOn graph right) :
    graph_connected graph := by
  have hCovered : ∀ vertex : graph.V, vertex ∈ left ∨ vertex ∈ right := by
    intro vertex
    refine Finset.mem_union.mp ?_
    rw [hCover]
    exact Finset.mem_univ vertex
  intro separating hNontrivial
  obtain ⟨inside, outside, hInside, hOutside⟩ := hNontrivial
  by_cases hShared : shared ∈ separating
  · rcases hCovered outside with hPart | hPart
    · exact hLeft separating ⟨shared, hSharedLeft, hShared⟩ ⟨outside, hPart, hOutside⟩
    · exact hRight separating ⟨shared, hSharedRight, hShared⟩ ⟨outside, hPart, hOutside⟩
  · rcases hCovered inside with hPart | hPart
    · exact hLeft separating ⟨inside, hPart, hInside⟩ ⟨shared, hSharedLeft, hShared⟩
    · exact hRight separating ⟨inside, hPart, hInside⟩ ⟨shared, hSharedRight, hShared⟩

/-- An occurrence multiset membership names an occurrence. -/
theorem exists_occurrence_of_mem_edges {graph : CFGraph} {pair : graph.V × graph.V}
    (hMem : pair ∈ graph.edges) :
    ∃ occurrence : graph.edges, (occurrence : graph.V × graph.V) = pair :=
  ⟨graph.edges.mkToType pair ⟨0, Multiset.count_pos.mpr hMem⟩, Multiset.coe_mk⟩


namespace SheetPartition

variable {d : ℕ}

/-! ## Block arithmetic of a merge

`SheetPartition.mergeBlocks` already has its block description
(`mergeBlocks_block_first`, `mergeBlocks_block_of_separate`) and the
cardinality of a merge with a *singleton*.  These are the two facts a gluing
datum needs: the general cardinality, and the induced count of a refinement. -/

/-- Block cardinality depends only on the block.

(`ContractionRamification.blockCard_congr` and
`ContractionRamification.blockCountWithin_congr` are the same two statements.
They are repeated here, in the `SheetPartition` namespace where dot notation
finds them, so that this file does not import that module for two three-line
proofs.) -/
theorem blockCard_congr (partition : SheetPartition d) {i j : Fin d}
    (h : partition.Rel i j) : partition.blockCard i = partition.blockCard j := by
  unfold blockCard
  rw [partition.block_eq_of_rel h]

/-- The induced block count depends only on the coarse block. -/
theorem blockCountWithin_congr (fine coarse : SheetPartition d) {i j : Fin d}
    (h : coarse.Rel i j) :
    fine.blockCountWithin coarse i = fine.blockCountWithin coarse j := by
  unfold blockCountWithin
  rw [coarse.block_eq_of_rel h]

/-- **A merged block has the two cardinalities added.**  The two blocks being
joined are distinct, hence disjoint. -/
theorem mergeBlocks_blockCard_first (partition : SheetPartition d)
    (first extra : Fin d) (hSeparate : ¬partition.Rel first extra) :
    (partition.mergeBlocks first extra hSeparate).blockCard first =
      partition.blockCard first + partition.blockCard extra := by
  unfold blockCard
  rw [partition.mergeBlocks_block_first first extra hSeparate]
  refine Finset.card_union_of_disjoint ?_
  rw [Finset.disjoint_left]
  intro sheet hFirst hExtra
  exact hSeparate (((partition.mem_block_iff first sheet).mp hFirst).trans
    ((partition.mem_block_iff extra sheet).mp hExtra).symm)

/-- **A merged block induces the two families of fine blocks side by side.**
Here the refinement hypothesis is essential: a fine block sits inside a single
coarse block, so no fine block is counted twice. -/
theorem mergeBlocks_blockCountWithin_first (fine partition : SheetPartition d)
    (hRefines : fine.Refines partition) (first extra : Fin d)
    (hSeparate : ¬partition.Rel first extra) :
    fine.blockCountWithin (partition.mergeBlocks first extra hSeparate) first =
      fine.blockCountWithin partition first +
        fine.blockCountWithin partition extra := by
  unfold blockCountWithin
  rw [partition.mergeBlocks_block_first first extra hSeparate,
    Finset.image_union]
  refine Finset.card_union_of_disjoint ?_
  rw [Finset.disjoint_left]
  intro representative hFirst hExtra
  obtain ⟨fromFirst, hFromFirst, hFirstEq⟩ := Finset.mem_image.mp hFirst
  obtain ⟨fromExtra, hFromExtra, hExtraEq⟩ := Finset.mem_image.mp hExtra
  refine hSeparate (((partition.mem_block_iff first fromFirst).mp hFromFirst).trans
    ((hRefines.rel (show fine.Rel fromFirst fromExtra from
        hFirstEq.trans hExtraEq.symm)).trans
      ((partition.mem_block_iff extra fromExtra).mp hFromExtra).symm))

/-- Away from the merge nothing changes. -/
theorem mergeBlocks_blockCountWithin_of_separate (fine partition : SheetPartition d)
    (first extra other : Fin d) (hSeparate : ¬partition.Rel first extra)
    (hOtherFirst : ¬partition.Rel other first)
    (hOtherExtra : ¬partition.Rel other extra) :
    fine.blockCountWithin (partition.mergeBlocks first extra hSeparate) other =
      fine.blockCountWithin partition other := by
  unfold blockCountWithin
  rw [partition.mergeBlocks_block_of_separate first extra other hSeparate
    hOtherFirst hOtherExtra]

/-! ## One more sheet

`SheetPartition` is stated at a fixed `d` throughout and contains no map
relating `SheetPartition d` to `SheetPartition (d + 1)`.  This is that map, in
the only form that needs no further input: the fresh sheet `Fin.last d` alone in
its own block.  Any other placement *is* a choice of gluing, which is what
`GluingDatum.addSheetGlued` below takes as an argument. -/

/-- **One more sheet, in a block of its own.**  Old sheets keep their blocks
along `Fin.castSucc`; the fresh sheet `Fin.last d` is alone. -/
def addSheet (partition : SheetPartition d) : SheetPartition (d + 1) where
  repr := Fin.lastCases (Fin.last d) fun i ↦ (partition.repr i).castSucc
  repr_idem := by
    intro i
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp [partition.repr_idem]

@[simp] theorem addSheet_repr_castSucc (partition : SheetPartition d)
    (i : Fin d) :
    partition.addSheet.repr i.castSucc = (partition.repr i).castSucc := by
  simp [addSheet]

@[simp] theorem addSheet_repr_last (partition : SheetPartition d) :
    partition.addSheet.repr (Fin.last d) = Fin.last d := by
  simp [addSheet]

/-- The fresh sheet is the only sheet whose representative is the fresh
sheet. -/
theorem addSheet_repr_eq_last_iff (partition : SheetPartition d)
    (i : Fin (d + 1)) :
    partition.addSheet.repr i = Fin.last d ↔ i = Fin.last d := by
  induction i using Fin.lastCases with
  | last => simp
  | cast j =>
      simp only [addSheet_repr_castSucc]
      exact ⟨fun h ↦ absurd h (Fin.castSucc_lt_last _).ne,
        fun h ↦ absurd h (Fin.castSucc_lt_last _).ne⟩

theorem addSheet_rel_castSucc_iff (partition : SheetPartition d) (i j : Fin d) :
    partition.addSheet.Rel i.castSucc j.castSucc ↔ partition.Rel i j := by
  simp [Rel]

/-- **The fresh sheet is alone**, so it is never in the block of an old
sheet: this is the separation hypothesis every merge with the fresh sheet
needs. -/
theorem addSheet_not_rel_castSucc_last (partition : SheetPartition d)
    (i : Fin d) :
    ¬partition.addSheet.Rel i.castSucc (Fin.last d) := by
  rw [rel_iff, addSheet_repr_castSucc, addSheet_repr_last]
  exact (Fin.castSucc_lt_last _).ne

theorem addSheet_block_castSucc (partition : SheetPartition d) (i : Fin d) :
    partition.addSheet.block i.castSucc = (partition.block i).image Fin.castSucc := by
  ext j
  induction j using Fin.lastCases with
  | last =>
      simp only [mem_block_iff, Finset.mem_image]
      constructor
      · intro hRel
        exact absurd ((partition.addSheet_repr_eq_last_iff _).mp
          (hRel.trans (partition.addSheet_repr_last)))
          (Fin.castSucc_lt_last i).ne
      · rintro ⟨k, -, hk⟩
        exact absurd hk (Fin.castSucc_lt_last k).ne
  | cast k =>
      simp only [mem_block_iff, Finset.mem_image, addSheet_rel_castSucc_iff]
      constructor
      · intro hRel
        exact ⟨k, hRel, rfl⟩
      · rintro ⟨m, hm, hmk⟩
        have hEq : m = k := Fin.castSucc_injective d hmk
        subst hEq
        exact hm

theorem addSheet_block_last (partition : SheetPartition d) :
    partition.addSheet.block (Fin.last d) = {Fin.last d} := by
  ext j
  simp only [mem_block_iff, Finset.mem_singleton, rel_iff, addSheet_repr_last]
  exact ⟨fun h ↦ (partition.addSheet_repr_eq_last_iff j).mp h.symm,
    fun h ↦ by rw [h, addSheet_repr_last]⟩

@[simp] theorem addSheet_blockCard_castSucc (partition : SheetPartition d)
    (i : Fin d) :
    partition.addSheet.blockCard i.castSucc = partition.blockCard i := by
  rw [blockCard, addSheet_block_castSucc,
    Finset.card_image_of_injective _ (Fin.castSucc_injective d), blockCard]

@[simp] theorem addSheet_blockCard_last (partition : SheetPartition d) :
    partition.addSheet.blockCard (Fin.last d) = 1 := by
  rw [blockCard, addSheet_block_last, Finset.card_singleton]

@[simp] theorem addSheet_blockCountWithin_castSucc (fine coarse : SheetPartition d)
    (i : Fin d) :
    fine.addSheet.blockCountWithin coarse.addSheet i.castSucc =
      fine.blockCountWithin coarse i := by
  unfold blockCountWithin
  rw [addSheet_block_castSucc, Finset.image_image]
  have hFun : fine.addSheet.repr ∘ Fin.castSucc = Fin.castSucc ∘ fine.repr := by
    funext k
    simp
  rw [hFun, ← Finset.image_image,
    Finset.card_image_of_injective _ (Fin.castSucc_injective d)]

@[simp] theorem addSheet_blockCountWithin_last (fine coarse : SheetPartition d) :
    fine.addSheet.blockCountWithin coarse.addSheet (Fin.last d) = 1 := by
  unfold blockCountWithin
  rw [addSheet_block_last, Finset.image_singleton, Finset.card_singleton]

/-- **Refinement survives.**  A fresh sheet alone in its block refines a fresh
sheet alone in its block. -/
theorem addSheet_refines {fine coarse : SheetPartition d}
    (hRefines : fine.Refines coarse) : fine.addSheet.Refines coarse.addSheet := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
      have hj : j = Fin.last d :=
        (fine.addSheet_repr_eq_last_iff j).mp
          (by rw [← hij, addSheet_repr_last])
      subst hj
      rfl
  | cast a =>
      induction j using Fin.lastCases with
      | last =>
          exact absurd ((fine.addSheet_repr_eq_last_iff _).mp
            (hij.trans fine.addSheet_repr_last)) (Fin.castSucc_lt_last a).ne
      | cast b =>
          exact (coarse.addSheet_rel_castSucc_iff a b).mpr
            (hRefines a b ((fine.addSheet_rel_castSucc_iff a b).mp hij))

/-- **The fresh sheet, placed by a choice.**  `none` leaves it alone in its own
block; `some old` joins it to the block of `old`.  This is the local form of a
degree-raising move: the fresh sheet has to go somewhere above every target
vertex, and `Option` is exactly the data of where. -/
def gluedPartition (partition : SheetPartition d) (choice : Option (Fin d)) :
    SheetPartition (d + 1) :=
  match choice with
  | none => partition.addSheet
  | some old =>
      (partition.addSheet).mergeBlocks (Fin.castSucc old) (Fin.last d)
        (partition.addSheet_not_rel_castSucc_last old)

@[simp] theorem gluedPartition_none (partition : SheetPartition d) :
    partition.gluedPartition none = partition.addSheet := rfl

@[simp] theorem gluedPartition_some (partition : SheetPartition d) (old : Fin d) :
    partition.gluedPartition (some old) =
      (partition.addSheet).mergeBlocks (Fin.castSucc old) (Fin.last d)
        (partition.addSheet_not_rel_castSucc_last old) := rfl

/-- However the fresh sheet is placed, the placement only coarsens. -/
theorem addSheet_refines_gluedPartition (partition : SheetPartition d)
    (choice : Option (Fin d)) :
    partition.addSheet.Refines (partition.gluedPartition choice) := by
  cases choice with
  | none => exact Refines.refl _
  | some old =>
      exact refines_mergeBlocks partition.addSheet (Fin.castSucc old) (Fin.last d)
        (partition.addSheet_not_rel_castSucc_last old)

end SheetPartition

namespace GluingDatum

variable {target : CFGraph} {degree newDegree : ℕ}

/-! ## Two data over one target, related on sheets -/

/-- The source vertex of `image` above the same target vertex, carrying the
sheet named by `sheetMap`. -/
def sheetVertexMap (data : GluingDatum target degree)
    (image : GluingDatum target newDegree)
    (sheetMap : Fin degree → Fin newDegree) (vertex : data.SourceVertex) :
    image.SourceVertex :=
  image.sourceEndpoint vertex.1.1 (sheetMap vertex.1.2)

/-- The sheet map read on a canonical source endpoint. -/
theorem sheetVertexMap_sourceEndpoint (data : GluingDatum target degree)
    (image : GluingDatum target newDegree)
    (sheetMap : Fin degree → Fin newDegree) (vertex : target.V)
    (sheet : Fin degree) :
    sheetVertexMap data image sheetMap (data.sourceEndpoint vertex sheet) =
      image.sourceEndpoint vertex
        (sheetMap ((data.vertexPartition vertex).repr sheet)) := rfl

/-- Two sheets in one block above a target vertex name the same source
vertex. -/
theorem sourceEndpoint_congr (data : GluingDatum target degree)
    (vertex : target.V) {first second : Fin degree}
    (h : (data.vertexPartition vertex).Rel first second) :
    data.sourceEndpoint vertex first = data.sourceEndpoint vertex second := by
  apply Subtype.ext
  exact Prod.ext rfl h

/-- **A source occurrence of `data` names one of `image`, with the mapped
endpoints.**  The occurrence partition of `image` refines its vertex partitions,
which is what lets the canonical occurrence block be read off at either end. -/
theorem sourceEnds_sourceEdge_sheetMap (data : GluingDatum target degree)
    (image : GluingDatum target newDegree)
    (sheetMap : Fin degree → Fin newDegree)
    (hSheetMap : ∀ (vertex : target.V) (first second : Fin degree),
      (data.vertexPartition vertex).Rel first second →
        (image.vertexPartition vertex).Rel (sheetMap first) (sheetMap second))
    (edge : data.SourceEdge) :
    image.sourceEnds (image.sourceEdge edge.1.1 (sheetMap edge.1.2)) =
      (sheetVertexMap data image sheetMap (data.sourceEnds edge).1,
        sheetVertexMap data image sheetMap (data.sourceEnds edge).2) := by
  have hEnd : ∀ vertex : target.V,
      (image.edgePartition edge.1.1).Refines (image.vertexPartition vertex) →
      image.sourceEndpoint vertex
          ((image.edgePartition edge.1.1).repr (sheetMap edge.1.2)) =
        image.sourceEndpoint vertex
          (sheetMap ((data.vertexPartition vertex).repr edge.1.2)) := by
    intro vertex hRefines
    apply Subtype.ext
    refine Prod.ext rfl ?_
    show (image.vertexPartition vertex).repr
        ((image.edgePartition edge.1.1).repr (sheetMap edge.1.2)) =
      (image.vertexPartition vertex).repr
        (sheetMap ((data.vertexPartition vertex).repr edge.1.2))
    have hOccurrence : (image.vertexPartition vertex).Rel
        ((image.edgePartition edge.1.1).repr (sheetMap edge.1.2))
        (sheetMap edge.1.2) :=
      hRefines.rel ((image.edgePartition edge.1.1).rel_repr_left
        (sheetMap edge.1.2))
    have hMapped : (image.vertexPartition vertex).Rel
        (sheetMap ((data.vertexPartition vertex).repr edge.1.2))
        (sheetMap edge.1.2) :=
      hSheetMap vertex ((data.vertexPartition vertex).repr edge.1.2) edge.1.2
        ((data.vertexPartition vertex).rel_repr_left edge.1.2)
    exact hOccurrence.trans hMapped.symm
  exact Prod.ext (hEnd _ (image.refines_left edge.1.1))
    (hEnd _ (image.refines_right edge.1.1))

/-- **A source occurrence maps to a source occurrence.**  The occurrence half of
`connected_of_sheetMap`, isolated because a *part* of the image is sometimes all
that is wanted. -/
theorem num_edges_sheetVertexMap_pos (data : GluingDatum target degree)
    (image : GluingDatum target newDegree)
    (sheetMap : Fin degree → Fin newDegree)
    (hSheetMap : ∀ (vertex : target.V) (first second : Fin degree),
      (data.vertexPartition vertex).Rel first second →
        (image.vertexPartition vertex).Rel (sheetMap first) (sheetMap second))
    (first second : data.SourceVertex)
    (hPos : 0 < num_edges data.sourceGraph first second) :
    0 < num_edges image.sourceGraph
      (sheetVertexMap data image sheetMap first)
      (sheetVertexMap data image sheetMap second) := by
  obtain ⟨occurrence, hMem, hEnds⟩ :=
    GraphContraction.exists_mem_edges_of_num_edges_pos data.sourceGraph first
      second hPos
  obtain ⟨block, -, hBlock⟩ := Multiset.mem_map.mp
    (show occurrence ∈
      (Finset.univ : Finset data.SourceEdge).val.map data.sourceEnds from hMem)
  have hImage : image.sourceEnds
      (image.sourceEdge block.1.1 (sheetMap block.1.2)) ∈
        image.sourceGraph.edges :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ _)
  rw [sourceEnds_sourceEdge_sheetMap data image sheetMap hSheetMap block,
    hBlock] at hImage
  rcases hEnds with rfl | rfl
  · exact GraphContraction.num_edges_pos_of_mem_edges image.sourceGraph _ _ hImage
  · exact GraphContraction.num_edges_pos_of_mem_edges' image.sourceGraph _ _ hImage

/-- **Connectedness passes along a sheet map.**  The only requirement on
`sheetMap` is that it never separates two sheets lying in one block above a
target vertex, together with surjectivity of the induced map on source
vertices.  Nothing is required of the occurrence partitions: an occurrence
partition refines the partitions at both of its endpoints, which is exactly what
makes the image occurrence land on the images of the two endpoints. -/
theorem connected_of_sheetMap (data : GluingDatum target degree)
    (image : GluingDatum target newDegree)
    (sheetMap : Fin degree → Fin newDegree)
    (hSheetMap : ∀ (vertex : target.V) (first second : Fin degree),
      (data.vertexPartition vertex).Rel first second →
        (image.vertexPartition vertex).Rel (sheetMap first) (sheetMap second))
    (hSurjective : Function.Surjective (sheetVertexMap data image sheetMap))
    (hConnected : data.Connected) : image.Connected :=
  graph_connected_of_surjective (sheetVertexMap data image sheetMap) hSurjective
    (num_edges_sheetVertexMap_pos data image sheetMap hSheetMap) hConnected

/-! ## Coarsening the vertex partitions -/

/-- **Replace every vertex partition by a coarser one.**  The occurrence
partitions are unchanged, and refinement survives because refinement is
transitive.  This is the only shape of datum change that keeps the occurrence
blocks -- and hence the dilation indices -- exactly as they were. -/
def coarsenVertices (data : GluingDatum target degree)
    (coarse : target.V → SheetPartition degree)
    (hCoarse : ∀ vertex, (data.vertexPartition vertex).Refines (coarse vertex)) :
    GluingDatum target degree where
  degree_pos := data.degree_pos
  vertexPartition := coarse
  edgePartition := data.edgePartition
  refines_left := fun edge ↦ (data.refines_left edge).trans (hCoarse _)
  refines_right := fun edge ↦ (data.refines_right edge).trans (hCoarse _)

@[simp] theorem coarsenVertices_vertexPartition (data : GluingDatum target degree)
    (coarse : target.V → SheetPartition degree)
    (hCoarse : ∀ vertex, (data.vertexPartition vertex).Refines (coarse vertex)) :
    (data.coarsenVertices coarse hCoarse).vertexPartition = coarse := rfl

@[simp] theorem coarsenVertices_edgePartition (data : GluingDatum target degree)
    (coarse : target.V → SheetPartition degree)
    (hCoarse : ∀ vertex, (data.vertexPartition vertex).Refines (coarse vertex)) :
    (data.coarsenVertices coarse hCoarse).edgePartition = data.edgePartition := rfl

/-- **Coarsening the vertex partitions of a connected source keeps it
connected.**  The quotient map sends a source vertex to the coarser block above
the same target vertex; it is surjective because the coarse representative of a
fine representative is the coarse representative. -/
theorem coarsenVertices_connected (data : GluingDatum target degree)
    (coarse : target.V → SheetPartition degree)
    (hCoarse : ∀ vertex, (data.vertexPartition vertex).Refines (coarse vertex))
    (hConnected : data.Connected) :
    (data.coarsenVertices coarse hCoarse).Connected := by
  refine connected_of_sheetMap data _ id
    (fun vertex _ _ hRel ↦ (hCoarse vertex).rel hRel) ?_ hConnected
  rintro ⟨⟨vertex, sheet⟩, hSheet⟩
  refine ⟨data.sourceEndpoint vertex sheet, ?_⟩
  apply Subtype.ext
  refine Prod.ext rfl ?_
  show (coarse vertex).repr ((data.vertexPartition vertex).repr sheet) = sheet
  exact ((hCoarse vertex).rel
    ((data.vertexPartition vertex).rel_repr_left sheet)).trans hSheet

/-! ## Joining two blocks above one target vertex -/

/-- **Glue two sheet blocks above one target vertex.**  Every other vertex
partition, and every occurrence partition, is left alone.  `SheetPartition.mergeBlocks`
supplies the local operation; this is its datum-level form. -/
def mergeVertexBlocks (data : GluingDatum target degree) (vertex : target.V)
    (first extra : Fin degree)
    (hSeparate : ¬(data.vertexPartition vertex).Rel first extra) :
    GluingDatum target degree :=
  data.coarsenVertices
    (Function.update data.vertexPartition vertex
      ((data.vertexPartition vertex).mergeBlocks first extra hSeparate))
    (by
      intro place
      by_cases hPlace : place = vertex
      · subst hPlace
        rw [Function.update_self]
        exact (data.vertexPartition place).refines_mergeBlocks first extra
          hSeparate
      · rw [Function.update_of_ne hPlace]
        exact SheetPartition.Refines.refl _)

@[simp] theorem mergeVertexBlocks_edgePartition (data : GluingDatum target degree)
    (vertex : target.V) (first extra : Fin degree)
    (hSeparate : ¬(data.vertexPartition vertex).Rel first extra) :
    (data.mergeVertexBlocks vertex first extra hSeparate).edgePartition =
      data.edgePartition := rfl

@[simp] theorem mergeVertexBlocks_vertexPartition_self
    (data : GluingDatum target degree) (vertex : target.V)
    (first extra : Fin degree)
    (hSeparate : ¬(data.vertexPartition vertex).Rel first extra) :
    (data.mergeVertexBlocks vertex first extra hSeparate).vertexPartition vertex =
      (data.vertexPartition vertex).mergeBlocks first extra hSeparate :=
  Function.update_self _ _ _

@[simp] theorem mergeVertexBlocks_vertexPartition_of_ne
    (data : GluingDatum target degree) (vertex place : target.V)
    (first extra : Fin degree)
    (hSeparate : ¬(data.vertexPartition vertex).Rel first extra)
    (hPlace : place ≠ vertex) :
    (data.mergeVertexBlocks vertex first extra hSeparate).vertexPartition place =
      data.vertexPartition place :=
  Function.update_of_ne hPlace _ _

/-- **The lemma.  Joining two blocks of the vertex partition of a connected
source keeps the source connected.**  Merging identifies two source vertices
above one target vertex and changes nothing else, so the new source is a
quotient of the old one and `graph_connected_of_surjective` applies.

The four other routes to `GluingDatum.Connected` -- a finite replay, a target
isomorphism, a target vertex expansion, a target edge contraction -- all fix
the sheet structure; this one changes it. -/
theorem mergeVertexBlocks_connected (data : GluingDatum target degree)
    (vertex : target.V) (first extra : Fin degree)
    (hSeparate : ¬(data.vertexPartition vertex).Rel first extra)
    (hConnected : data.Connected) :
    (data.mergeVertexBlocks vertex first extra hSeparate).Connected :=
  data.coarsenVertices_connected _ _ hConnected

/-- **Merging preserves the local Riemann--Hurwitz condition, with two to
spare.**  Above the merged block the occurrence-block counts add
(`SheetPartition.mergeBlocks_blockCountWithin_first`) and so do the block
cardinalities, so the merged slack is the sum of the two old slacks plus `2`;
every other block, and every other target vertex, is untouched.

Riemann--Hurwitz is therefore the *free* half of a sheet gluing, exactly as it
is the free half of a degree raise. -/
theorem mergeVertexBlocks_riemannHurwitz (data : GluingDatum target degree)
    (vertex : target.V) (first extra : Fin degree)
    (hSeparate : ¬(data.vertexPartition vertex).Rel first extra)
    (hRiemannHurwitz : data.RiemannHurwitz) :
    (data.mergeVertexBlocks vertex first extra hSeparate).RiemannHurwitz := by
  intro place sheet
  simp only [data.mergeVertexBlocks_edgePartition vertex first extra hSeparate]
  by_cases hPlace : place = vertex
  · subst hPlace
    rw [data.mergeVertexBlocks_vertexPartition_self place first extra hSeparate]
    by_cases hRel :
        ((data.vertexPartition place).mergeBlocks first extra hSeparate).Rel
          first sheet
    · have hCard :
          ((data.vertexPartition place).mergeBlocks first extra hSeparate).blockCard
              sheet =
            (data.vertexPartition place).blockCard first +
              (data.vertexPartition place).blockCard extra := by
        rw [← SheetPartition.blockCard_congr _ hRel,
          SheetPartition.mergeBlocks_blockCard_first]
      have hCount : ∀ edge ∈ incidentEdges place,
          (((data.edgePartition edge).blockCountWithin
              ((data.vertexPartition place).mergeBlocks first extra hSeparate)
              sheet : ℕ) : ℤ) =
            (((data.edgePartition edge).blockCountWithin
              (data.vertexPartition place) first : ℕ) : ℤ) +
              (((data.edgePartition edge).blockCountWithin
                (data.vertexPartition place) extra : ℕ) : ℤ) := by
        intro edge hEdge
        have hIncident : (edge : target.V × target.V).1 = place ∨
            (edge : target.V × target.V).2 = place := by
          simpa [incidentEdges] using hEdge
        have hRefines :
            (data.edgePartition edge).Refines (data.vertexPartition place) := by
          rcases hIncident with hLeft | hRight
          · exact hLeft ▸ data.refines_left edge
          · exact hRight ▸ data.refines_right edge
        rw [← SheetPartition.blockCountWithin_congr _ _ hRel,
          SheetPartition.mergeBlocks_blockCountWithin_first _ _ hRefines first
            extra hSeparate]
        push_cast
        ring
      rw [Finset.sum_congr rfl hCount, Finset.sum_add_distrib, hCard]
      have hFirst := hRiemannHurwitz place first
      have hExtra := hRiemannHurwitz place extra
      push_cast
      linarith
    · have hNotFirst : ¬(data.vertexPartition place).Rel sheet first := by
        intro hSheet
        exact hRel (((data.vertexPartition place).mergeBlocks_rel_first_iff first
          extra sheet hSeparate).mpr (Or.inl hSheet.symm))
      have hNotExtra : ¬(data.vertexPartition place).Rel sheet extra := by
        intro hSheet
        exact hRel (((data.vertexPartition place).mergeBlocks_rel_first_iff first
          extra sheet hSeparate).mpr (Or.inr hSheet.symm))
      have hCount : ∀ edge ∈ incidentEdges place,
          (((data.edgePartition edge).blockCountWithin
              ((data.vertexPartition place).mergeBlocks first extra hSeparate)
              sheet : ℕ) : ℤ) =
            (((data.edgePartition edge).blockCountWithin
              (data.vertexPartition place) sheet : ℕ) : ℤ) := by
        intro edge _
        rw [SheetPartition.mergeBlocks_blockCountWithin_of_separate _ _ first
          extra sheet hSeparate hNotFirst hNotExtra]
      rw [Finset.sum_congr rfl hCount,
        (data.vertexPartition place).mergeBlocks_blockCard_of_separate first extra
          sheet hSeparate hNotFirst hNotExtra]
      exact hRiemannHurwitz place sheet
  · rw [data.mergeVertexBlocks_vertexPartition_of_ne vertex place first extra
      hSeparate hPlace]
    exact hRiemannHurwitz place sheet

/-- **Merging two blocks above one target vertex preserves validity.**  Both
halves: connectedness by `mergeVertexBlocks_connected`, and local
Riemann--Hurwitz by `mergeVertexBlocks_riemannHurwitz`.  Neither half is assumed
of the merged datum. -/
theorem mergeVertexBlocks_valid (data : GluingDatum target degree)
    (vertex : target.V) (first extra : Fin degree)
    (hSeparate : ¬(data.vertexPartition vertex).Rel first extra)
    (hValid : data.Valid) :
    (data.mergeVertexBlocks vertex first extra hSeparate).Valid :=
  ⟨data.mergeVertexBlocks_connected vertex first extra hSeparate hValid.1,
    data.mergeVertexBlocks_riemannHurwitz vertex first extra hSeparate hValid.2⟩

/-! ## Raising the degree, and gluing the fresh sheet

`SheetPartition.addSheet` raises a single partition.  Raising a whole datum is
`addSheetDatum`; it is **never** connected, since the fresh sheet, alone in every
block, spans a disjoint copy of the target inside the source.  The fresh sheet
therefore has to be *glued*, and `addSheetGlued` takes the datum-level gluing
data: one old sheet above every target vertex, whose block the fresh sheet
joins. -/

/-- **One more sheet over the whole target**, alone in every block.  The only
degree raise that needs no further input, and the one whose source is
disconnected. -/
def addSheetDatum (data : GluingDatum target degree) :
    GluingDatum target (degree + 1) where
  degree_pos := Nat.succ_pos degree
  vertexPartition := fun vertex ↦ (data.vertexPartition vertex).addSheet
  edgePartition := fun edge ↦ (data.edgePartition edge).addSheet
  refines_left := fun edge ↦
    SheetPartition.addSheet_refines (data.refines_left edge)
  refines_right := fun edge ↦
    SheetPartition.addSheet_refines (data.refines_right edge)

@[simp] theorem addSheetDatum_vertexPartition (data : GluingDatum target degree)
    (vertex : target.V) :
    data.addSheetDatum.vertexPartition vertex =
      (data.vertexPartition vertex).addSheet := rfl

@[simp] theorem addSheetDatum_edgePartition (data : GluingDatum target degree)
    (edge : target.edges) :
    data.addSheetDatum.edgePartition edge = (data.edgePartition edge).addSheet := rfl

/-- **One more sheet, glued above every target vertex to the block of the sheet
`choice` names there.**  The occurrence partitions keep the fresh sheet alone, so
the fresh sheet still contributes one source occurrence above every target
occurrence; what the gluing does is attach both of its endpoints to old source
vertices. -/
def addSheetGlued (data : GluingDatum target degree)
    (choice : target.V → Fin degree) : GluingDatum target (degree + 1) :=
  data.addSheetDatum.coarsenVertices
    (fun vertex ↦ ((data.vertexPartition vertex).addSheet).mergeBlocks
      (Fin.castSucc (choice vertex)) (Fin.last degree)
      (SheetPartition.addSheet_not_rel_castSucc_last _ _))
    (fun _ ↦ SheetPartition.refines_mergeBlocks _ _ _ _)

@[simp] theorem addSheetGlued_vertexPartition (data : GluingDatum target degree)
    (choice : target.V → Fin degree) (vertex : target.V) :
    (data.addSheetGlued choice).vertexPartition vertex =
      ((data.vertexPartition vertex).addSheet).mergeBlocks
        (Fin.castSucc (choice vertex)) (Fin.last degree)
        (SheetPartition.addSheet_not_rel_castSucc_last _ _) := rfl

@[simp] theorem addSheetGlued_edgePartition (data : GluingDatum target degree)
    (choice : target.V → Fin degree) (edge : target.edges) :
    (data.addSheetGlued choice).edgePartition edge =
      (data.edgePartition edge).addSheet := rfl

/-- The fresh sheet lies in the glued block above every target vertex. -/
theorem addSheetGlued_rel_last (data : GluingDatum target degree)
    (choice : target.V → Fin degree) (vertex : target.V) :
    ((data.addSheetGlued choice).vertexPartition vertex).Rel
      (Fin.castSucc (choice vertex)) (Fin.last degree) :=
  (((data.vertexPartition vertex).addSheet).mergeBlocks_rel_first_iff
    (Fin.castSucc (choice vertex)) (Fin.last degree) (Fin.last degree)
    (SheetPartition.addSheet_not_rel_castSucc_last _ _)).mpr (Or.inr rfl)

/-- Old sheets keep their blocks above every target vertex. -/
theorem addSheetGlued_rel_castSucc (data : GluingDatum target degree)
    (choice : target.V → Fin degree) (vertex : target.V) {first second : Fin degree}
    (hRel : (data.vertexPartition vertex).Rel first second) :
    ((data.addSheetGlued choice).vertexPartition vertex).Rel
      (Fin.castSucc first) (Fin.castSucc second) :=
  (SheetPartition.refines_mergeBlocks ((data.vertexPartition vertex).addSheet)
      (Fin.castSucc (choice vertex)) (Fin.last degree)
      (SheetPartition.addSheet_not_rel_castSucc_last _ _)).rel
    ((SheetPartition.addSheet_rel_castSucc_iff _ first second).mpr hRel)

/-- **The fresh sheet does not disconnect the source once it is glued.**  Every
source vertex of the glued datum is an old source vertex -- the fresh sheet is
alone in no vertex block -- so the glued source is the old source with one extra
occurrence above every target occurrence, and `connected_of_sheetMap` applies
along `Fin.castSucc`.

This is what a degree-raising move needs: `addSheetDatum` alone is never
connected. -/
theorem addSheetGlued_connected (data : GluingDatum target degree)
    (choice : target.V → Fin degree) (hConnected : data.Connected) :
    (data.addSheetGlued choice).Connected := by
  refine connected_of_sheetMap data (data.addSheetGlued choice) Fin.castSucc
    (fun vertex _ _ hRel ↦ data.addSheetGlued_rel_castSucc choice vertex hRel)
    ?_ hConnected
  rintro ⟨⟨vertex, sheet⟩, hSheet⟩
  have hRepr : ∀ old : Fin degree,
      ((data.addSheetGlued choice).vertexPartition vertex).Rel
        (Fin.castSucc ((data.vertexPartition vertex).repr old))
        (Fin.castSucc old) := fun old ↦
    data.addSheetGlued_rel_castSucc choice vertex
      ((data.vertexPartition vertex).rel_repr_left old)
  induction sheet using Fin.lastCases with
  | last =>
      refine ⟨data.sourceEndpoint vertex (choice vertex), ?_⟩
      rw [sheetVertexMap_sourceEndpoint]
      exact (sourceEndpoint_eq_iff _ _ _ _).mpr
        ⟨rfl, (hRepr (choice vertex)).trans
          (data.addSheetGlued_rel_last choice vertex)⟩
  | cast old =>
      refine ⟨data.sourceEndpoint vertex old, ?_⟩
      rw [sheetVertexMap_sourceEndpoint]
      exact (sourceEndpoint_eq_iff _ _ _ _).mpr ⟨rfl, hRepr old⟩

/-- **A block glued to the fresh sheet satisfies Riemann--Hurwitz, with two to
spare.**  Above the glued block the fresh sheet contributes exactly one extra
occurrence block at every incident occurrence -- it is alone in its occurrence
block -- and exactly one extra sheet to the block cardinality.  The left side
therefore gains the valency of the vertex and the right side gains the valency
minus two.

The datum `glued` is described by its partitions at the one target vertex
concerned, so both the everywhere-glued and the partially glued raise use this
lemma. -/
theorem riemannHurwitzAt_mergeBlocks_addSheet (data : GluingDatum target degree)
    (glued : GluingDatum target (degree + 1)) (vertex : target.V)
    (old : Fin degree)
    (hVertex : glued.vertexPartition vertex =
      ((data.vertexPartition vertex).addSheet).mergeBlocks (Fin.castSucc old)
        (Fin.last degree)
        (SheetPartition.addSheet_not_rel_castSucc_last
          (data.vertexPartition vertex) old))
    (hEdge : ∀ edge : target.edges,
      glued.edgePartition edge = (data.edgePartition edge).addSheet)
    (hRiemannHurwitz : data.RiemannHurwitz) :
    (∑ edge ∈ incidentEdges vertex,
      (((glued.edgePartition edge).blockCountWithin
        (glued.vertexPartition vertex) (Fin.castSucc old) : ℕ) : ℤ)) - 2 ≥
      (((glued.vertexPartition vertex).blockCard (Fin.castSucc old) : ℕ) : ℤ) *
        (((incidentEdges vertex).card : ℤ) - 2) := by
  have hCount : ∀ edge ∈ incidentEdges vertex,
      (((glued.edgePartition edge).blockCountWithin
        (glued.vertexPartition vertex) (Fin.castSucc old) : ℕ) : ℤ) =
      (((data.edgePartition edge).blockCountWithin (data.vertexPartition vertex)
        old : ℕ) : ℤ) + 1 := by
    intro edge hEdgeMem
    have hIncident : (edge : target.V × target.V).1 = vertex ∨
        (edge : target.V × target.V).2 = vertex := by
      simpa [incidentEdges] using hEdgeMem
    have hRefines :
        (data.edgePartition edge).Refines (data.vertexPartition vertex) := by
      rcases hIncident with hLeft | hRight
      · exact hLeft ▸ data.refines_left edge
      · exact hRight ▸ data.refines_right edge
    rw [hVertex, hEdge, SheetPartition.mergeBlocks_blockCountWithin_first _ _
        (SheetPartition.addSheet_refines hRefines) _ _ _,
      SheetPartition.addSheet_blockCountWithin_castSucc,
      SheetPartition.addSheet_blockCountWithin_last]
    push_cast
    ring
  rw [Finset.sum_congr rfl hCount, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, mul_one, hVertex, SheetPartition.mergeBlocks_blockCard_first,
    SheetPartition.addSheet_blockCard_castSucc,
    SheetPartition.addSheet_blockCard_last]
  have hOld := hRiemannHurwitz vertex old
  push_cast
  linarith

/-- **Riemann--Hurwitz at a target vertex where the fresh sheet is glued.**  The
glued block is `riemannHurwitzAt_mergeBlocks_addSheet`; every other block is an
old block with the old occurrence blocks inside it. -/
theorem riemannHurwitzAtTargetVertex_glue (data : GluingDatum target degree)
    (glued : GluingDatum target (degree + 1)) (vertex : target.V)
    (old : Fin degree)
    (hVertex : glued.vertexPartition vertex =
      ((data.vertexPartition vertex).addSheet).mergeBlocks (Fin.castSucc old)
        (Fin.last degree)
        (SheetPartition.addSheet_not_rel_castSucc_last
          (data.vertexPartition vertex) old))
    (hEdge : ∀ edge : target.edges,
      glued.edgePartition edge = (data.edgePartition edge).addSheet)
    (hRiemannHurwitz : data.RiemannHurwitz) :
    glued.RiemannHurwitzAtTargetVertex vertex := by
  intro sheet
  have hTransfer : ∀ s : Fin (degree + 1),
      (glued.vertexPartition vertex).Rel (Fin.castSucc old) s →
        (∑ edge ∈ incidentEdges vertex,
          (((glued.edgePartition edge).blockCountWithin
            (glued.vertexPartition vertex) s : ℕ) : ℤ)) - 2 ≥
          (((glued.vertexPartition vertex).blockCard s : ℕ) : ℤ) *
            (((incidentEdges vertex).card : ℤ) - 2) := by
    intro s hRel
    have hCount : ∀ edge ∈ incidentEdges vertex,
        (((glued.edgePartition edge).blockCountWithin
          (glued.vertexPartition vertex) s : ℕ) : ℤ) =
        (((glued.edgePartition edge).blockCountWithin
          (glued.vertexPartition vertex) (Fin.castSucc old) : ℕ) : ℤ) := by
      intro edge _
      rw [SheetPartition.blockCountWithin_congr _ _ hRel.symm]
    rw [Finset.sum_congr rfl hCount, SheetPartition.blockCard_congr _ hRel.symm]
    exact riemannHurwitzAt_mergeBlocks_addSheet data glued vertex old hVertex
      hEdge hRiemannHurwitz
  induction sheet using Fin.lastCases with
  | last =>
      refine hTransfer _ ?_
      rw [hVertex]
      exact (((data.vertexPartition vertex).addSheet).mergeBlocks_rel_first_iff
        (Fin.castSucc old) (Fin.last degree) (Fin.last degree)
        (SheetPartition.addSheet_not_rel_castSucc_last
          (data.vertexPartition vertex) old)).mpr (Or.inr rfl)
  | cast other =>
      by_cases hOther : (data.vertexPartition vertex).Rel old other
      · refine hTransfer _ ?_
        rw [hVertex]
        exact (SheetPartition.refines_mergeBlocks _ _ _ _).rel
          ((SheetPartition.addSheet_rel_castSucc_iff _ _ _).mpr hOther)
      · have hNotFirst : ¬((data.vertexPartition vertex).addSheet).Rel
            (Fin.castSucc other) (Fin.castSucc old) := fun hRel ↦
          hOther ((SheetPartition.addSheet_rel_castSucc_iff _ _ _).mp hRel).symm
        have hNotExtra : ¬((data.vertexPartition vertex).addSheet).Rel
            (Fin.castSucc other) (Fin.last degree) :=
          SheetPartition.addSheet_not_rel_castSucc_last _ _
        simp only [hVertex, hEdge]
        have hCount : ∀ edge ∈ incidentEdges vertex,
            ((((data.edgePartition edge).addSheet).blockCountWithin
              (((data.vertexPartition vertex).addSheet).mergeBlocks
                (Fin.castSucc old) (Fin.last degree)
                (SheetPartition.addSheet_not_rel_castSucc_last
                  (data.vertexPartition vertex) old))
              (Fin.castSucc other) : ℕ) : ℤ) =
            (((data.edgePartition edge).blockCountWithin
              (data.vertexPartition vertex) other : ℕ) : ℤ) := by
          intro edge _
          rw [SheetPartition.mergeBlocks_blockCountWithin_of_separate _ _ _ _ _ _
              hNotFirst hNotExtra,
            SheetPartition.addSheet_blockCountWithin_castSucc]
        rw [Finset.sum_congr rfl hCount,
          SheetPartition.mergeBlocks_blockCard_of_separate _ _ _ _ _ hNotFirst
            hNotExtra, SheetPartition.addSheet_blockCard_castSucc]
        exact hRiemannHurwitz vertex other

/-- **Riemann--Hurwitz at a target vertex where the fresh sheet is left
alone.**  At an old sheet both sides are the old ones; at the fresh sheet, alone
in a block of size one, the inequality is an equality.  This is the *free* half
of a degree raise. -/
theorem riemannHurwitzAtTargetVertex_addSheet (data : GluingDatum target degree)
    (raised : GluingDatum target (degree + 1)) (vertex : target.V)
    (hVertex : raised.vertexPartition vertex =
      (data.vertexPartition vertex).addSheet)
    (hEdge : ∀ edge : target.edges,
      raised.edgePartition edge = (data.edgePartition edge).addSheet)
    (hRiemannHurwitz : data.RiemannHurwitz) :
    raised.RiemannHurwitzAtTargetVertex vertex := by
  intro sheet
  simp only [hVertex, hEdge]
  induction sheet using Fin.lastCases with
  | last =>
      have hTerm : ∀ edge ∈ incidentEdges vertex,
          ((((data.edgePartition edge).addSheet).blockCountWithin
            ((data.vertexPartition vertex).addSheet)
            (Fin.last degree) : ℕ) : ℤ) = 1 := by
        intro edge _
        rw [SheetPartition.addSheet_blockCountWithin_last, Nat.cast_one]
      rw [Finset.sum_congr rfl hTerm, Finset.sum_const, nsmul_eq_mul, mul_one,
        SheetPartition.addSheet_blockCard_last, Nat.cast_one, one_mul]
  | cast old =>
      have hOld := hRiemannHurwitz vertex old
      simpa only [SheetPartition.addSheet_blockCountWithin_castSucc,
        SheetPartition.addSheet_blockCard_castSucc] using hOld

/-- **Riemann--Hurwitz survives the everywhere-glued degree raise.** -/
theorem addSheetGlued_riemannHurwitz (data : GluingDatum target degree)
    (choice : target.V → Fin degree) (hRiemannHurwitz : data.RiemannHurwitz) :
    (data.addSheetGlued choice).RiemannHurwitz := fun vertex ↦
  riemannHurwitzAtTargetVertex_glue data (data.addSheetGlued choice) vertex
    (choice vertex) (data.addSheetGlued_vertexPartition choice vertex)
    (data.addSheetGlued_edgePartition choice) hRiemannHurwitz

/-- **A valid datum stays valid when the degree is raised and the fresh sheet is
glued above every target vertex.**  Both halves of `GluingDatum.Valid`: the
connectedness that a bare degree raise destroys, and the local Riemann--Hurwitz
condition that a bare degree raise leaves alone. -/
theorem addSheetGlued_valid (data : GluingDatum target degree)
    (choice : target.V → Fin degree) (hValid : data.Valid) :
    (data.addSheetGlued choice).Valid :=
  ⟨data.addSheetGlued_connected choice hValid.1,
    data.addSheetGlued_riemannHurwitz choice hValid.2⟩

/-! ### The single-vertex glue, and the target a connected source forces -/

/-- **Riemann--Hurwitz is free for a bare degree raise.** -/
theorem addSheetDatum_riemannHurwitz (data : GluingDatum target degree)
    (hRiemannHurwitz : data.RiemannHurwitz) :
    data.addSheetDatum.RiemannHurwitz := fun vertex ↦
  riemannHurwitzAtTargetVertex_addSheet data data.addSheetDatum vertex rfl
    (fun _ ↦ rfl) hRiemannHurwitz

/-- **Glue the fresh sheet to the block of `sheet` above one target vertex.**
This is the move a tripod step consumes once at each of its three arm leaves:
the degree goes up by one, and the fresh sheet is attached to an old sheet at
one chosen place. -/
def glueFreshSheetAt (data : GluingDatum target degree) (vertex : target.V)
    (sheet : Fin degree) : GluingDatum target (degree + 1) :=
  data.addSheetDatum.mergeVertexBlocks vertex (Fin.castSucc sheet)
    (Fin.last degree)
    (SheetPartition.addSheet_not_rel_castSucc_last (data.vertexPartition vertex)
      sheet)

@[simp] theorem glueFreshSheetAt_edgePartition (data : GluingDatum target degree)
    (vertex : target.V) (sheet : Fin degree) (edge : target.edges) :
    (data.glueFreshSheetAt vertex sheet).edgePartition edge =
      (data.edgePartition edge).addSheet := rfl

theorem glueFreshSheetAt_vertexPartition_self (data : GluingDatum target degree)
    (vertex : target.V) (sheet : Fin degree) :
    (data.glueFreshSheetAt vertex sheet).vertexPartition vertex =
      ((data.vertexPartition vertex).addSheet).mergeBlocks (Fin.castSucc sheet)
        (Fin.last degree)
        (SheetPartition.addSheet_not_rel_castSucc_last
          (data.vertexPartition vertex) sheet) :=
  data.addSheetDatum.mergeVertexBlocks_vertexPartition_self vertex
    (Fin.castSucc sheet) (Fin.last degree) _

/-- **The fresh sheet is still alone above every other target vertex**, so the
glue is available again there: the operation composes, once per target vertex a
caller chooses to glue at. -/
theorem glueFreshSheetAt_vertexPartition_of_ne (data : GluingDatum target degree)
    (vertex place : target.V) (sheet : Fin degree) (hPlace : place ≠ vertex) :
    (data.glueFreshSheetAt vertex sheet).vertexPartition place =
      (data.vertexPartition place).addSheet :=
  data.addSheetDatum.mergeVertexBlocks_vertexPartition_of_ne vertex place
    (Fin.castSucc sheet) (Fin.last degree) _ hPlace

/-- **The single-vertex glue keeps Riemann--Hurwitz.**  The raise is free
(`addSheetDatum_riemannHurwitz`) and the merge preserves it
(`mergeVertexBlocks_riemannHurwitz`), so any number of glues, at any number of
target vertices, is free as well. -/
theorem glueFreshSheetAt_riemannHurwitz (data : GluingDatum target degree)
    (vertex : target.V) (sheet : Fin degree)
    (hRiemannHurwitz : data.RiemannHurwitz) :
    (data.glueFreshSheetAt vertex sheet).RiemannHurwitz :=
  data.addSheetDatum.mergeVertexBlocks_riemannHurwitz vertex (Fin.castSucc sheet)
    (Fin.last degree) _ (data.addSheetDatum_riemannHurwitz hRiemannHurwitz)

/-- **A connected source forces a connected target.**  The quotient source
surjects onto the target, vertex by vertex and occurrence by occurrence, so
`graph_connected_of_surjective` applies to the projection.

This is the hypothesis bookkeeping for a *partial* glue: after gluing the fresh
sheet above some but not all target vertices, the fresh sheet still spans a copy
of the target hanging off the old source, and connectedness of that copy is
connectedness of the target.  The lemma says the target hypothesis is available
for free from `data.Connected`, so a partial glue needs no hypothesis the caller
does not already have. -/
theorem graph_connected_target_of_connected (data : GluingDatum target degree)
    (hConnected : data.Connected) : graph_connected target := by
  refine graph_connected_of_surjective
    (fun vertex : data.SourceVertex ↦ vertex.1.1)
    (fun vertex ↦ ⟨data.sourceEndpoint vertex ⟨0, data.degree_pos⟩, rfl⟩) ?_
    hConnected
  intro first second hPos
  obtain ⟨occurrence, hMem, hEnds⟩ :=
    GraphContraction.exists_mem_edges_of_num_edges_pos data.sourceGraph first
      second hPos
  obtain ⟨block, -, hBlock⟩ := Multiset.mem_map.mp
    (show occurrence ∈
      (Finset.univ : Finset data.SourceEdge).val.map data.sourceEnds from hMem)
  have hTarget : ((block.1.1 : target.V × target.V).1,
      (block.1.1 : target.V × target.V).2) ∈ target.edges := by
    rw [Prod.mk.eta]
    exact Multiset.coe_mem
  rcases hEnds with rfl | rfl
  · rw [show first = (data.sourceEnds block).1 from (congrArg Prod.fst hBlock).symm,
      show second = (data.sourceEnds block).2 from (congrArg Prod.snd hBlock).symm]
    exact GraphContraction.num_edges_pos_of_mem_edges target _ _ hTarget
  · rw [show first = (data.sourceEnds block).2 from (congrArg Prod.snd hBlock).symm,
      show second = (data.sourceEnds block).1 from (congrArg Prod.fst hBlock).symm]
    exact GraphContraction.num_edges_pos_of_mem_edges' target _ _ hTarget

/-! ### The partial glue: the fresh sheet attached at some target vertices

`addSheetGlued` glues the fresh sheet above *every* target vertex, which needs
no hypothesis but leaves the fresh sheet with no source vertex of its own.  A
Cools--Draisma tripod step glues at three leaves only, so the fresh copy of the
target keeps the rest of its vertices.  `addSheetGluedOn` is that move, at an
arbitrary set of target vertices named by an `Option`-valued choice. -/

/-- **One more sheet, glued where `choice` says.**  Above a vertex with
`choice vertex = some old` the fresh sheet joins the block of `old`; above a
vertex with `choice vertex = none` it stays alone. -/
def addSheetGluedOn (data : GluingDatum target degree)
    (choice : target.V → Option (Fin degree)) : GluingDatum target (degree + 1) :=
  data.addSheetDatum.coarsenVertices
    (fun vertex ↦ (data.vertexPartition vertex).gluedPartition (choice vertex))
    (fun vertex ↦ SheetPartition.addSheet_refines_gluedPartition
      (data.vertexPartition vertex) (choice vertex))

@[simp] theorem addSheetGluedOn_vertexPartition (data : GluingDatum target degree)
    (choice : target.V → Option (Fin degree)) (vertex : target.V) :
    (data.addSheetGluedOn choice).vertexPartition vertex =
      (data.vertexPartition vertex).gluedPartition (choice vertex) := rfl

@[simp] theorem addSheetGluedOn_edgePartition (data : GluingDatum target degree)
    (choice : target.V → Option (Fin degree)) (edge : target.edges) :
    (data.addSheetGluedOn choice).edgePartition edge =
      (data.edgePartition edge).addSheet := rfl

/-- The everywhere-glued raise is the partial glue that glues everywhere. -/
theorem addSheetGlued_eq_addSheetGluedOn (data : GluingDatum target degree)
    (choice : target.V → Fin degree) :
    data.addSheetGlued choice =
      data.addSheetGluedOn (fun vertex ↦ some (choice vertex)) := rfl

/-- Old sheets keep their blocks, wherever the fresh sheet is placed. -/
theorem addSheetGluedOn_rel_castSucc (data : GluingDatum target degree)
    (choice : target.V → Option (Fin degree)) (vertex : target.V)
    {first second : Fin degree}
    (hRel : (data.vertexPartition vertex).Rel first second) :
    ((data.addSheetGluedOn choice).vertexPartition vertex).Rel
      (Fin.castSucc first) (Fin.castSucc second) :=
  (SheetPartition.addSheet_refines_gluedPartition (data.vertexPartition vertex)
    (choice vertex)).rel
      ((SheetPartition.addSheet_rel_castSucc_iff _ first second).mpr hRel)

/-- Above a glued target vertex the fresh sheet lies in the block it was glued
to. -/
theorem addSheetGluedOn_rel_last (data : GluingDatum target degree)
    (choice : target.V → Option (Fin degree)) {vertex : target.V}
    {old : Fin degree} (hChoice : choice vertex = some old) :
    ((data.addSheetGluedOn choice).vertexPartition vertex).Rel
      (Fin.castSucc old) (Fin.last degree) := by
  show ((data.vertexPartition vertex).gluedPartition (choice vertex)).Rel _ _
  rw [hChoice, SheetPartition.gluedPartition_some]
  exact (((data.vertexPartition vertex).addSheet).mergeBlocks_rel_first_iff
    (Fin.castSucc old) (Fin.last degree) (Fin.last degree)
    (SheetPartition.addSheet_not_rel_castSucc_last
      (data.vertexPartition vertex) old)).mpr (Or.inr rfl)

/-- **The fresh sheet spans a copy of the target inside the glued source.**  Its
occurrence blocks are singletons, so every target occurrence carries exactly one
source occurrence joining the two fresh endpoints. -/
theorem num_edges_freshVertex_pos (data : GluingDatum target degree)
    (choice : target.V → Option (Fin degree)) (first second : target.V)
    (hPos : 0 < num_edges target first second) :
    0 < num_edges (data.addSheetGluedOn choice).sourceGraph
      ((data.addSheetGluedOn choice).sourceEndpoint first (Fin.last degree))
      ((data.addSheetGluedOn choice).sourceEndpoint second (Fin.last degree)) := by
  obtain ⟨pair, hPairMem, hPairEnds⟩ :=
    GraphContraction.exists_mem_edges_of_num_edges_pos target first second hPos
  obtain ⟨occurrence, hOccurrence⟩ := exists_occurrence_of_mem_edges hPairMem
  have hMem : (data.addSheetGluedOn choice).sourceEnds
      ((data.addSheetGluedOn choice).sourceEdge occurrence (Fin.last degree)) ∈
        (data.addSheetGluedOn choice).sourceGraph.edges :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ _)
  have hEnds : (data.addSheetGluedOn choice).sourceEnds
      ((data.addSheetGluedOn choice).sourceEdge occurrence (Fin.last degree)) =
        ((data.addSheetGluedOn choice).sourceEndpoint
            (occurrence : target.V × target.V).1 (Fin.last degree),
          (data.addSheetGluedOn choice).sourceEndpoint
            (occurrence : target.V × target.V).2 (Fin.last degree)) := by
    unfold sourceEnds
    rw [sourceEdge_target, sourceEdge_sheet, addSheetGluedOn_edgePartition,
      SheetPartition.addSheet_repr_last]
  rw [hEnds, hOccurrence] at hMem
  rcases hPairEnds with rfl | rfl
  · exact GraphContraction.num_edges_pos_of_mem_edges _ _ _ hMem
  · exact GraphContraction.num_edges_pos_of_mem_edges' _ _ _ hMem

/-- **The partial glue keeps the source connected**, provided the fresh sheet is
glued somewhere.  The glued source is covered by two connected parts: the image
of the old source, connected because `data` is, and the fresh copy of the
target, connected because the target is -- which
`graph_connected_target_of_connected` gets from `data.Connected` for free.  The
one glued vertex is in both parts.

This is the Cools--Draisma degree-raising move: raise the degree by one and
attach the fresh sheet at one or more target vertices. -/
theorem addSheetGluedOn_connected (data : GluingDatum target degree)
    (choice : target.V → Option (Fin degree)) {vertex : target.V}
    {old : Fin degree} (hChoice : choice vertex = some old)
    (hConnected : data.Connected) : (data.addSheetGluedOn choice).Connected := by
  have hOld : ConnectedOn (data.addSheetGluedOn choice).sourceGraph
      (Finset.univ.image
        (sheetVertexMap data (data.addSheetGluedOn choice) Fin.castSucc)) :=
    connectedOn_image _
      (num_edges_sheetVertexMap_pos data (data.addSheetGluedOn choice)
        Fin.castSucc
        (fun place _ _ hRel ↦ data.addSheetGluedOn_rel_castSucc choice place hRel))
      hConnected
  have hFresh : ConnectedOn (data.addSheetGluedOn choice).sourceGraph
      (Finset.univ.image (fun place : target.V ↦
        (data.addSheetGluedOn choice).sourceEndpoint place (Fin.last degree))) :=
    connectedOn_image _ (data.num_edges_freshVertex_pos choice)
      (data.graph_connected_target_of_connected hConnected)
  refine graph_connected_of_connectedOn_union
    (shared := (data.addSheetGluedOn choice).sourceEndpoint vertex
      (Fin.last degree)) ?_ ?_ ?_ hOld hFresh
  · refine Finset.eq_univ_iff_forall.mpr ?_
    rintro ⟨⟨place, sheet⟩, hSheet⟩
    refine Finset.mem_union.mpr ?_
    induction sheet using Fin.lastCases with
    | last =>
        exact Or.inr (Finset.mem_image.mpr ⟨place, Finset.mem_univ place,
          (sourceEndpoint_eq_iff _ _ _ _).mpr ⟨rfl, rfl⟩⟩)
    | cast other =>
        refine Or.inl (Finset.mem_image.mpr
          ⟨data.sourceEndpoint place other, Finset.mem_univ _, ?_⟩)
        rw [sheetVertexMap_sourceEndpoint]
        exact (sourceEndpoint_eq_iff _ _ _ _).mpr ⟨rfl,
          data.addSheetGluedOn_rel_castSucc choice place
            ((data.vertexPartition place).rel_repr_left other)⟩
  · refine Finset.mem_image.mpr ⟨data.sourceEndpoint vertex old,
      Finset.mem_univ _, ?_⟩
    rw [sheetVertexMap_sourceEndpoint]
    exact sourceEndpoint_congr (data.addSheetGluedOn choice) vertex
      ((data.addSheetGluedOn_rel_castSucc choice vertex
        ((data.vertexPartition vertex).rel_repr_left old)).trans
          (data.addSheetGluedOn_rel_last choice hChoice))
  · exact Finset.mem_image.mpr ⟨vertex, Finset.mem_univ vertex, rfl⟩

/-- **Riemann--Hurwitz survives the partial glue.**  At a glued vertex it is
`riemannHurwitzAtTargetVertex_glue`; at an unglued one it is
`riemannHurwitzAtTargetVertex_addSheet`, the free half of a bare raise. -/
theorem addSheetGluedOn_riemannHurwitz (data : GluingDatum target degree)
    (choice : target.V → Option (Fin degree))
    (hRiemannHurwitz : data.RiemannHurwitz) :
    (data.addSheetGluedOn choice).RiemannHurwitz := by
  intro vertex
  cases hChoice : choice vertex with
  | none =>
      refine riemannHurwitzAtTargetVertex_addSheet data
        (data.addSheetGluedOn choice) vertex ?_ (fun _ ↦ rfl) hRiemannHurwitz
      show (data.vertexPartition vertex).gluedPartition (choice vertex) = _
      rw [hChoice, SheetPartition.gluedPartition_none]
  | some old =>
      refine riemannHurwitzAtTargetVertex_glue data (data.addSheetGluedOn choice)
        vertex old ?_ (fun _ ↦ rfl) hRiemannHurwitz
      show (data.vertexPartition vertex).gluedPartition (choice vertex) = _
      rw [hChoice, SheetPartition.gluedPartition_some]

/-- **A valid datum stays valid when the degree is raised and the fresh sheet is
glued at one or more target vertices.**  Both halves of `GluingDatum.Valid`: the
connectedness a bare raise destroys, and the local Riemann--Hurwitz condition a
bare raise leaves alone. -/
theorem addSheetGluedOn_valid (data : GluingDatum target degree)
    (choice : target.V → Option (Fin degree)) {vertex : target.V}
    {old : Fin degree} (hChoice : choice vertex = some old) (hValid : data.Valid) :
    (data.addSheetGluedOn choice).Valid :=
  ⟨data.addSheetGluedOn_connected choice hChoice hValid.1,
    data.addSheetGluedOn_riemannHurwitz choice hValid.2⟩

end GluingDatum

end DraismaVargas.Infrastructure
