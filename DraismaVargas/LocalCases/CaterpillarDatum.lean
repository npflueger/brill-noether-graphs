import DraismaVargas.Infrastructure.CaterpillarTree
import DraismaVargas.Infrastructure.Change
import DraismaVargas.Infrastructure.SheetGluing

/-!
# The caterpillar-of-loops gluing datum

The seed of the construction in Vargas, Part II (arXiv:2609.09109): the
caterpillar of loops.  For even `g = 2m + 2` and degree `d = g/2 + 1 = m + 2`
this file builds the Draisma--Vargas gluing datum of the full-dimensional
tropical morphism `γ^CL_g : G^CL_g → T^CL_g` of Part II, Lemma
`lm:combinatorial-structure-caterpillar-of-loops`, over the target tree of
`Infrastructure.CaterpillarTree`, and proves it **valid uniformly in `g`** --
no `decide`, no fixed genus anywhere.

## The datum

Sheet `0` is the *spine sheet*; sheet `j` (`1 ≤ j ≤ g/2`) is the partner of the
`j`-th pair of lollipops, `(A₁,B₂), (B₃,B₄), …, (B_{g-1},A_g)`.  Writing
`pairIndex v` for the pair of the lollipop containing the target vertex `v`:

* **every** vertex partition is `pairPart m (pairIndex v)`: the block
  `{0, pairIndex v}` and singletons.  This is `B_i = A_i = {0,j}` at `p_i` and
  `u_i` and the fold `{0,j}` at `v_i` in one formula;
* an occurrence partition is `pairPart m (pairIndex (child))` over a *pair
  edge* -- a slope-two spine edge `h_{2j-1}` (`e % 6 = 1`) or one of the `g-2`
  stems (`e % 3 = 2`, excluding the exceptional leaf index `6m+2`) -- and
  discrete over everything else, i.e. over the slope-one spine edges and the
  `g` leaf edges `u_i v_i`.

The slope sequence is therefore the ballot sequence `(2,1,2,1,…,2)`
(`sourceEdgeIndex_spineSheet`), the index at every bridge is `2`
(Part II, Lemma `lm:bridge-and-loop`), the leaf edges are folded, and
`m(B_i) - 2 = 0`, so
**no dangling paths are grafted**.

## Main results

* `caterpillarDatum m : GluingDatum (catTree m) (m + 2)` -- the datum, with
  both refinement receipts proved from the single arithmetic identity
  `pairIndex_parent` ("both ends of a pair edge have the same pair index").
* `caterpillarDatum_riemannHurwitz`, `caterpillarDatum_connected`,
  `caterpillarDatum_valid` -- the two conditions of `GluingDatum.Valid`.
  Riemann--Hurwitz reduces, at every vertex, to `(B-1)(2-j) ≥ 0` where `B` is a
  block cardinality and `j ≤ 2` counts the incident occurrences carrying the
  vertex's own partition; connectedness is the union of the `d` sheet copies of
  the target, sheet `j` meeting sheet `0` at the vertex `v_{2j-1}`.
* `card_sourceVertex_caterpillarDatum`, `card_sourceEdge_caterpillarDatum`,
  `genus_sourceGraph_caterpillarDatum` -- `(6m+4)(m+1)` source vertices,
  `(6m+3)(m+1) + (3m+2)` source occurrences, **source genus `2m + 2 = g`**.
* `saturated_caterpillarDatum` -- the `saturated` field of
  `FullDimensionalSourcePresentation`, `3g - 3 = 2g + 2d - 5`, an immediate
  corollary of the Euler count.

## What is not here

The *stable* data: the dangling census, the `StableLengthMatrixLabelling`, the
`SeedDeterminant.DiagonalPattern` and the remaining four fields of
`FullDimensionalSourcePresentation` (`labelling`, `det_ne_zero`, `trivalent`,
`pathEnds`), and the `SeedCandidate.Seed` built by contracting a spine edge.
Those are in `CaterpillarStable` and `CaterpillarSeed`; this file stops at
`Valid` and the Euler count.

`connectedOn_union`, `graph_connected_of_connectedOn_full`,
`sourceEnds_sourceEdge` and `num_edges_sourceEndpoint_pos` are general
statements about `ConnectedOn` and about gluing data, of the same kind as those
in `Infrastructure.SheetGluing`.
-/

namespace DraismaVargas.LocalCases.CaterpillarDatum

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open Finset

/-! ## 1.  The pair partition -/

/-- The sheet partition of `Fin (m+2)` whose only non-singleton block is
`{0, j}`.  For `j = 0` or `j ≥ m + 2` it degenerates to the discrete
partition, so the definition needs no side condition. -/
def pairPart (m j : ℕ) : SheetPartition (m + 2) where
  repr := fun k => if k.val = j then 0 else k
  repr_idem := by
    intro k
    by_cases h : k.val = j
    · rw [if_pos h]
      by_cases h0 : (0 : Fin (m + 2)).val = j
      · rw [if_pos h0]
      · rw [if_neg h0]
    · rw [if_neg h, if_neg h]

@[simp] theorem pairPart_repr (m j : ℕ) (k : Fin (m + 2)) :
    (pairPart m j).repr k = if k.val = j then 0 else k := rfl

/-- Away from `0` and `j` the partition is the identity. -/
theorem pairPart_repr_of_ne (m j : ℕ) (k : Fin (m + 2)) (h : k.val ≠ j) :
    (pairPart m j).repr k = k := by simp [h]

theorem pairPart_rel_zero (m j : ℕ) (k : Fin (m + 2))
    (hk : k.val = j) : (pairPart m j).Rel k 0 := by
  show (pairPart m j).repr k = (pairPart m j).repr 0
  rw [pairPart_repr, pairPart_repr, if_pos hk]
  split_ifs <;> rfl

/-- The fixed points of `pairPart m j` are the sheets other than `j`. -/
theorem pairPart_fixed_iff (m j : ℕ) (hj : 1 ≤ j) (k : Fin (m + 2)) :
    (pairPart m j).repr k = k ↔ k.val ≠ j := by
  constructor
  · intro h hval
    rw [pairPart_repr, if_pos hval] at h
    have hzero : (0 : Fin (m + 2)).val = k.val := congrArg Fin.val h
    simp only [Fin.val_zero] at hzero
    omega
  · intro h; exact pairPart_repr_of_ne m j k h

/-- **`pairPart m j` has `m + 1` blocks.**  Exactly one sheet, `j`, fails to be
its own representative. -/
theorem card_blocks_pairPart (m j : ℕ) (hj : 1 ≤ j) (hjlt : j < m + 2) :
    Fintype.card (pairPart m j).Blocks = m + 1 := by
  classical
  have hEquiv : (pairPart m j).Blocks ≃ {k : Fin (m + 2) // k ≠ ⟨j, hjlt⟩} :=
    Equiv.subtypeEquivRight fun k => by
      rw [pairPart_fixed_iff m j hj k]
      constructor
      · intro h hk; exact h (congrArg Fin.val hk)
      · intro h hk; exact h (Fin.ext hk)
  rw [Fintype.card_congr hEquiv, Fintype.card_subtype, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  omega

/-- The discrete partition has one block per sheet. -/
theorem card_blocks_discrete (d : ℕ) :
    Fintype.card (SheetPartition.discrete d).Blocks = d := by
  have hAll : ∀ k : Fin d, (SheetPartition.discrete d).repr k = k := fun _ => rfl
  show Fintype.card {k : Fin d // (SheetPartition.discrete d).repr k = k} = d
  rw [Fintype.card_congr (Equiv.subtypeUnivEquiv hAll), Fintype.card_fin]

/-- Counting the fine blocks of the discrete partition inside a coarse block
is counting the sheets of that block. -/
theorem blockCountWithin_discrete (d : ℕ) (coarse : SheetPartition d)
    (k : Fin d) :
    (SheetPartition.discrete d).blockCountWithin coarse k = coarse.blockCard k := by
  show (Finset.image (SheetPartition.discrete d).repr (coarse.block k)).card = _
  rw [show (SheetPartition.discrete d).repr = id from rfl, Finset.image_id]
  rfl


/-! ## 2.  The sheet dictionary and the datum -/

/-- The *pair index* of a target vertex: the lollipops `2j - 1` and `2j` are
paired, and the partner sheet of that pair is sheet `j`. -/
def pairIndex (v : ℕ) : ℕ := (lolli v + 1) / 2

theorem pairIndex_pos (v : ℕ) : 1 ≤ pairIndex v := by
  have := lolli_pos v; unfold pairIndex; omega

theorem pairIndex_lt (m v : ℕ) (hv : v ≤ 6 * m + 3) : pairIndex v < m + 2 := by
  have := lolli_le m v hv; unfold pairIndex; omega

/-- Over a stem the two endpoints belong to one lollipop, hence to one pair. -/
theorem pairIndex_succ_of_mod (v : ℕ) (hv : v % 3 = 2) :
    pairIndex (v + 1) = pairIndex v := by
  unfold pairIndex lolli; omega

/-- The occurrences over which sheet `0` is glued to its partner: the slope-two
spine edges `h_{2j-1}` (`e % 6 = 1`) and the `g - 2` stems (`e % 3 = 2`, the
last such index `6m+2` being the exceptional leaf edge `u_g v_g`).  Every other
occurrence -- the slope-one spine edges and the `g` leaf edges -- carries the
discrete partition. -/
def IsPairEdge (m e : ℕ) : Prop := e % 6 = 1 ∨ (e % 3 = 2 ∧ e ≠ 6 * m + 2)

instance (m e : ℕ) : Decidable (IsPairEdge m e) := by
  unfold IsPairEdge; infer_instance

/-- Both endpoints of a pair edge carry the same pair index. -/
theorem pairIndex_parent (m e : ℕ) (h : IsPairEdge m e) :
    pairIndex (parentIndex (e + 1)) = pairIndex (e + 1) := by
  have hp := (parentIndex_eq_iff (e + 1) (parentIndex (e + 1))).mp rfl
  unfold IsPairEdge at h
  unfold pairIndex lolli
  omega

/-- The index of a target occurrence, read off its child endpoint. -/
def edgeIndex (m : ℕ) (e : (catTree m).edges) : ℕ :=
  ((e : (catTree m).V × (catTree m).V).2).val - 1

@[simp] theorem edgeIndex_occ (m : ℕ) (i : Fin (6 * m + 3)) :
    edgeIndex m (occ m i) = i.val := rfl

theorem occ_surj (m : ℕ) (e : (catTree m).edges) : ∃ i, e = occ m i := by
  obtain ⟨i, hi⟩ := (occ_bijective m).2 e
  exact ⟨i, hi.symm⟩

/-- The vertex partition: at every vertex of the `i`-th lollipop, sheet `0` and
the partner sheet of the pair containing `i` form the one non-singleton
block. -/
def catVertexPart (m : ℕ) (v : (catTree m).V) : SheetPartition (m + 2) :=
  pairPart m (pairIndex v.val)

/-- The occurrence partition. -/
def catEdgePart (m : ℕ) (e : (catTree m).edges) : SheetPartition (m + 2) :=
  if IsPairEdge m (edgeIndex m e) then
    pairPart m (pairIndex (edgeIndex m e + 1))
  else SheetPartition.discrete (m + 2)

theorem catEdgePart_of_pair (m : ℕ) (i : Fin (6 * m + 3))
    (h : IsPairEdge m i.val) :
    catEdgePart m (occ m i) = pairPart m (pairIndex (i.val + 1)) := by
  unfold catEdgePart; rw [edgeIndex_occ, if_pos h]

theorem catEdgePart_of_not_pair (m : ℕ) (i : Fin (6 * m + 3))
    (h : ¬ IsPairEdge m i.val) :
    catEdgePart m (occ m i) = SheetPartition.discrete (m + 2) := by
  unfold catEdgePart; rw [edgeIndex_occ, if_neg h]

theorem catVertexPart_val (m : ℕ) (v : (catTree m).V) (a : ℕ) (hv : v.val = a) :
    catVertexPart m v = pairPart m (pairIndex a) := by
  unfold catVertexPart; rw [hv]

/-- **The caterpillar gluing datum of degree `d = g/2 + 1 = m + 2`.** -/
def caterpillarDatum (m : ℕ) : GluingDatum (catTree m) (m + 2) where
  degree_pos := by omega
  vertexPartition := catVertexPart m
  edgePartition := catEdgePart m
  refines_left := by
    intro e
    obtain ⟨i, rfl⟩ := occ_surj m e
    by_cases h : IsPairEdge m i.val
    · rw [catEdgePart_of_pair m i h]
      have hval : ((occ m i : (catTree m).edges) :
          (catTree m).V × (catTree m).V).1.val = parentIndex (i.val + 1) := rfl
      rw [catVertexPart_val m _ _ hval, pairIndex_parent m i.val h]
      exact SheetPartition.Refines.refl _
    · rw [catEdgePart_of_not_pair m i h]
      exact SheetPartition.discrete_refines _
  refines_right := by
    intro e
    obtain ⟨i, rfl⟩ := occ_surj m e
    by_cases h : IsPairEdge m i.val
    · rw [catEdgePart_of_pair m i h]
      have hval : ((occ m i : (catTree m).edges) :
          (catTree m).V × (catTree m).V).2.val = i.val + 1 := rfl
      rw [catVertexPart_val m _ _ hval]
      exact SheetPartition.Refines.refl _
    · rw [catEdgePart_of_not_pair m i h]
      exact SheetPartition.discrete_refines _

@[simp] theorem caterpillarDatum_vertexPartition (m : ℕ) (v : (catTree m).V) :
    (caterpillarDatum m).vertexPartition v = catVertexPart m v := rfl

@[simp] theorem caterpillarDatum_edgePartition (m : ℕ) (e : (catTree m).edges) :
    (caterpillarDatum m).edgePartition e = catEdgePart m e := rfl


/-! ## 3.  Riemann--Hurwitz

Write `B` for the cardinality of the block of the sheet under consideration.
An incident occurrence contributes `1` if its partition *is* the vertex
partition and `B` if it is discrete, so with `j` occurrences of the first kind
among `k` the local condition reads `j + (k - j)B - 2 ≥ B(k - 2)`, i.e.
`(B - 1)(2 - j) ≥ 0`: **it holds exactly when at most two incident occurrences
carry the vertex's own partition.**  On `T^CL_g` that count is `0` at a leaf
`v_i`, `1` at a divalent `u_i` and `2` at a junction `p_i`, which is what the
three lemmas below record. -/

theorem rh_leaf (m : ℕ) (v : (catTree m).V) {a : Fin (6 * m + 3)}
    (hS : incidentIndices m v = {a})
    (hA : catEdgePart m (occ m a) = SheetPartition.discrete (m + 2)) :
    (caterpillarDatum m).RiemannHurwitzAtTargetVertex v := by
  intro sheet
  simp only [caterpillarDatum_vertexPartition, caterpillarDatum_edgePartition]
  have hpos := (catVertexPart m v).blockCard_pos sheet
  rw [card_incidentEdges_one m v hS,
    sum_incidentEdges_one m v hS
      (fun e => ((catEdgePart m e).blockCountWithin (catVertexPart m v) sheet : ℤ)),
    hA, blockCountWithin_discrete]
  push_cast
  omega

theorem rh_divalent (m : ℕ) (v : (catTree m).V) {a b : Fin (6 * m + 3)}
    (hab : a ≠ b) (hS : incidentIndices m v = {a, b})
    (hA : catEdgePart m (occ m a) = catVertexPart m v)
    (hB : catEdgePart m (occ m b) = SheetPartition.discrete (m + 2)) :
    (caterpillarDatum m).RiemannHurwitzAtTargetVertex v := by
  intro sheet
  simp only [caterpillarDatum_vertexPartition, caterpillarDatum_edgePartition]
  have hpos := (catVertexPart m v).blockCard_pos sheet
  rw [card_incidentEdges_two m v hab hS,
    sum_incidentEdges_two m v hab hS
      (fun e => ((catEdgePart m e).blockCountWithin (catVertexPart m v) sheet : ℤ)),
    hA, hB, blockCountWithin_discrete, SheetPartition.blockCountWithin_self]
  push_cast
  omega

theorem rh_junction (m : ℕ) (v : (catTree m).V) {a b c : Fin (6 * m + 3)}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hS : incidentIndices m v = {a, b, c})
    (hA : catEdgePart m (occ m a) = catVertexPart m v)
    (hrest : (catEdgePart m (occ m b) = catVertexPart m v ∧
        catEdgePart m (occ m c) = SheetPartition.discrete (m + 2)) ∨
      (catEdgePart m (occ m b) = SheetPartition.discrete (m + 2) ∧
        catEdgePart m (occ m c) = catVertexPart m v)) :
    (caterpillarDatum m).RiemannHurwitzAtTargetVertex v := by
  intro sheet
  simp only [caterpillarDatum_vertexPartition, caterpillarDatum_edgePartition]
  have hpos := (catVertexPart m v).blockCard_pos sheet
  rw [card_incidentEdges_three m v hab hac hbc hS,
    sum_incidentEdges_three m v hab hac hbc hS
      (fun e => ((catEdgePart m e).blockCountWithin (catVertexPart m v) sheet : ℤ))]
  rcases hrest with ⟨hB, hC⟩ | ⟨hB, hC⟩ <;>
    rw [hA, hB, hC, blockCountWithin_discrete,
      SheetPartition.blockCountWithin_self] <;>
    push_cast <;> omega

/-! ### The local condition at every vertex -/

/-- **Riemann--Hurwitz, uniformly in `g`.** -/
theorem caterpillarDatum_riemannHurwitz (m : ℕ) :
    (caterpillarDatum m).RiemannHurwitz := by
  rw [GluingDatum.riemannHurwitz_iff_forall_targetVertex]
  intro v
  have hlt := v.isLt
  rcases vertexClass m v with hv | hv | ⟨hv, hlo, hhi⟩ | hv | ⟨hv, hhi⟩ | hv
  · -- (a) the root `u₁`: the leaf edge `0` and the slope-two spine edge `1`
    have h0 : (0 : ℕ) < 6 * m + 3 := by omega
    have h1 : (1 : ℕ) < 6 * m + 3 := by omega
    refine rh_divalent m v (a := ⟨1, h1⟩) (b := ⟨0, h0⟩) (by simp) ?_ ?_ ?_
    · rw [incidentIndices_root m v hv, Finset.pair_comm]
    · rw [catEdgePart_of_pair m ⟨1, h1⟩ (Or.inl rfl), catVertexPart_val m v 0 hv]
      congr 1
      show pairIndex (1 + 1) = pairIndex 0
      unfold pairIndex lolli
      omega
    · exact catEdgePart_of_not_pair m ⟨0, h0⟩ (by
        show ¬ IsPairEdge m 0
        unfold IsPairEdge; omega)
  · -- (b) a leaf `v_i` with `i < g`
    refine rh_leaf m v (a := ⟨v.val - 1, by omega⟩) (incidentIndices_leaf m v hv) ?_
    exact catEdgePart_of_not_pair m _ (by
      show ¬ IsPairEdge m (v.val - 1)
      unfold IsPairEdge; omega)
  · -- (c) a divalent `u_i` with `1 < i < g`: the stem `v-1` and the leaf `v`
    refine rh_divalent m v (a := ⟨v.val - 1, by omega⟩) (b := ⟨v.val, by omega⟩)
      (by simp only [ne_eq, Fin.mk.injEq]; omega)
      (incidentIndices_stem m v hv hlo hhi) ?_ ?_
    · rw [catEdgePart_of_pair m _ (by
        show IsPairEdge m (v.val - 1)
        unfold IsPairEdge; omega), catVertexPart]
      have : v.val - 1 + 1 = v.val := by omega
      rw [show ((⟨v.val - 1, by omega⟩ : Fin (6 * m + 3)) : ℕ) = v.val - 1 from rfl,
        this]
    · exact catEdgePart_of_not_pair m _ (by
        show ¬ IsPairEdge m v.val
        unfold IsPairEdge; omega)
  · -- (d) the last leaf `v_g`
    refine rh_leaf m v (a := ⟨6 * m + 2, by omega⟩)
      (incidentIndices_lastLeaf m v hv) ?_
    exact catEdgePart_of_not_pair m _ (by
      show ¬ IsPairEdge m (6 * m + 2)
      unfold IsPairEdge; omega)
  · -- (e) a junction `p_i`: the stem `v` and the two spine edges `v-1`, `v+2`
    refine rh_junction m v (a := ⟨v.val, by omega⟩) (b := ⟨v.val - 1, by omega⟩)
      (c := ⟨v.val + 2, by omega⟩)
      (by simp only [ne_eq, Fin.mk.injEq]; omega)
      (by simp only [ne_eq, Fin.mk.injEq]; omega)
      (by simp only [ne_eq, Fin.mk.injEq]; omega) ?_ ?_ ?_
    · rw [incidentIndices_junction m v hv hhi, Finset.insert_comm]
    · rw [catEdgePart_of_pair m _ (by
        show IsPairEdge m v.val
        unfold IsPairEdge; omega), catVertexPart,
        show ((⟨v.val, by omega⟩ : Fin (6 * m + 3)) : ℕ) = v.val from rfl,
        pairIndex_succ_of_mod v.val hv]
    · by_cases hpar : v.val % 6 = 5
      · right
        constructor
        · exact catEdgePart_of_not_pair m _ (by
            show ¬ IsPairEdge m (v.val - 1)
            unfold IsPairEdge; omega)
        · rw [catEdgePart_of_pair m _ (by
            show IsPairEdge m (v.val + 2)
            unfold IsPairEdge; omega), catVertexPart,
            show ((⟨v.val + 2, by omega⟩ : Fin (6 * m + 3)) : ℕ) = v.val + 2 from rfl]
          have : pairIndex (v.val + 2 + 1) = pairIndex v.val := by
            unfold pairIndex lolli; omega
          rw [this]
      · left
        constructor
        · rw [catEdgePart_of_pair m _ (by
            show IsPairEdge m (v.val - 1)
            unfold IsPairEdge; omega), catVertexPart,
            show ((⟨v.val - 1, by omega⟩ : Fin (6 * m + 3)) : ℕ) = v.val - 1 from rfl]
          have : v.val - 1 + 1 = v.val := by omega
          rw [this]
        · exact catEdgePart_of_not_pair m _ (by
            show ¬ IsPairEdge m (v.val + 2)
            unfold IsPairEdge; omega)
  · -- (f) the last divalent vertex `u_g`
    refine rh_divalent m v (a := ⟨6 * m + 1, by omega⟩) (b := ⟨6 * m + 2, by omega⟩)
      (by simp only [ne_eq, Fin.mk.injEq]; omega)
      (incidentIndices_lastStem m v hv) ?_ ?_
    · rw [catEdgePart_of_pair m _ (by
        show IsPairEdge m (6 * m + 1)
        unfold IsPairEdge; omega), catVertexPart_val m v (6 * m + 2) hv,
        show ((⟨6 * m + 1, by omega⟩ : Fin (6 * m + 3)) : ℕ) = 6 * m + 1 from rfl]
    · exact catEdgePart_of_not_pair m _ (by
        show ¬ IsPairEdge m (6 * m + 2)
        unfold IsPairEdge; omega)

/-! ## 4.  Connectedness

The source is covered by the `d` *sheet copies* of the target: the image of
`v ↦ sourceEndpoint v s` for a fixed sheet `s`.  Each copy is a connected
image of the target tree, and for `s ≥ 1` the copy of sheet `s` meets the copy
of sheet `0` at the vertex `v_{2s-1}` of the `s`-th pair, where the block
`{0, s}` identifies them.  Running that over the sheets in order glues the
whole source together.

The first four lemmas are general statements about gluing data and about
`ConnectedOn`, of the same kind as those in `Infrastructure.SheetGluing`. -/

section General

variable {target : CFGraph} {degree : ℕ}

/-- **Two connected parts sharing a vertex are connected on their union.**  The
`ConnectedOn`-valued form of `graph_connected_of_connectedOn_union`. -/
theorem connectedOn_union {graph : CFGraph} {left right : Finset graph.V}
    {shared : graph.V} (hSharedLeft : shared ∈ left)
    (hSharedRight : shared ∈ right) (hLeft : ConnectedOn graph left)
    (hRight : ConnectedOn graph right) : ConnectedOn graph (left ∪ right) := by
  intro separating hInside hOutside
  obtain ⟨inside, hInsidePart, hInsideMem⟩ := hInside
  obtain ⟨outside, hOutsidePart, hOutsideMem⟩ := hOutside
  by_cases hShared : shared ∈ separating
  · rcases Finset.mem_union.mp hOutsidePart with hPart | hPart
    · exact hLeft separating ⟨shared, hSharedLeft, hShared⟩
        ⟨outside, hPart, hOutsideMem⟩
    · exact hRight separating ⟨shared, hSharedRight, hShared⟩
        ⟨outside, hPart, hOutsideMem⟩
  · rcases Finset.mem_union.mp hInsidePart with hPart | hPart
    · exact hLeft separating ⟨inside, hPart, hInsideMem⟩
        ⟨shared, hSharedLeft, hShared⟩
    · exact hRight separating ⟨inside, hPart, hInsideMem⟩
        ⟨shared, hSharedRight, hShared⟩

/-- Connectedness on a part containing every vertex is connectedness. -/
theorem graph_connected_of_connectedOn_full {graph : CFGraph}
    (part : Finset graph.V) (hfull : ∀ v : graph.V, v ∈ part)
    (h : ConnectedOn graph part) : graph_connected graph := by
  intro separating hNontrivial
  obtain ⟨inside, outside, hInside, hOutside⟩ := hNontrivial
  exact h separating ⟨inside, hfull inside, hInside⟩
    ⟨outside, hfull outside, hOutside⟩

/-- The canonical source occurrence over a target occurrence joins the two
canonical source endpoints of the same sheet. -/
theorem sourceEnds_sourceEdge (data : GluingDatum target degree)
    (e : target.edges) (s : Fin degree) :
    data.sourceEnds (data.sourceEdge e s) =
      (data.sourceEndpoint (e : target.V × target.V).1 s,
        data.sourceEndpoint (e : target.V × target.V).2 s) :=
  Prod.ext
    (data.sourceEndpoint_congr _
      ((data.refines_left e).rel ((data.edgePartition e).rel_repr_left s)))
    (data.sourceEndpoint_congr _
      ((data.refines_right e).rel ((data.edgePartition e).rel_repr_left s)))

/-- **A target occurrence lifts to every sheet.** -/
theorem num_edges_sourceEndpoint_pos (data : GluingDatum target degree)
    (s : Fin degree) (a b : target.V) (h : 0 < num_edges target a b) :
    0 < num_edges data.sourceGraph (data.sourceEndpoint a s)
      (data.sourceEndpoint b s) := by
  obtain ⟨pair, hMem, hEnds⟩ :=
    GraphContraction.exists_mem_edges_of_num_edges_pos target a b h
  obtain ⟨e, he⟩ := exists_occurrence_of_mem_edges hMem
  have hsrc : data.sourceEnds (data.sourceEdge e s) ∈ data.sourceGraph.edges :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ _)
  rw [sourceEnds_sourceEdge, he] at hsrc
  rcases hEnds with rfl | rfl
  · exact GraphContraction.num_edges_pos_of_mem_edges _ _ _ hsrc
  · exact GraphContraction.num_edges_pos_of_mem_edges' _ _ _ hsrc

end General

/-- The copy of the target carried by one sheet. -/
def sheetImage (m : ℕ) (s : Fin (m + 2)) :
    Finset (caterpillarDatum m).SourceVertex :=
  Finset.univ.image
    (fun v : (catTree m).V => (caterpillarDatum m).sourceEndpoint v s)

theorem connectedOn_sheetImage (m : ℕ) (s : Fin (m + 2)) :
    ConnectedOn (caterpillarDatum m).sourceGraph (sheetImage m s) := by
  rw [sheetImage]
  refine connectedOn_image (source := catTree m)
    (image := (caterpillarDatum m).sourceGraph)
    (fun v : (catTree m).V => (caterpillarDatum m).sourceEndpoint v s) ?_
    (catTree_connected m)
  intro a b h
  exact num_edges_sourceEndpoint_pos (caterpillarDatum m) s a b h

/-- The union of the first `k` sheet copies. -/
def cumSheets (m k : ℕ) : Finset (caterpillarDatum m).SourceVertex :=
  (Finset.univ.filter fun s : Fin (m + 2) => s.val < k).biUnion (sheetImage m)

theorem cumSheets_one (m : ℕ) : cumSheets m 1 = sheetImage m 0 := by
  have hfilter : (Finset.univ.filter fun s : Fin (m + 2) => s.val < 1)
      = {(0 : Fin (m + 2))} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, Fin.ext_iff, Fin.val_zero]
    omega
  rw [cumSheets, hfilter, Finset.singleton_biUnion]

theorem cumSheets_succ (m k : ℕ) (hk : k < m + 2) :
    cumSheets m (k + 1) = cumSheets m k ∪ sheetImage m ⟨k, hk⟩ := by
  have hfilter : (Finset.univ.filter fun s : Fin (m + 2) => s.val < k + 1)
      = insert (⟨k, hk⟩ : Fin (m + 2))
        (Finset.univ.filter fun s : Fin (m + 2) => s.val < k) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]
    omega
  rw [cumSheets, hfilter, Finset.biUnion_insert, cumSheets, Finset.union_comm]

/-- The vertex `v_{2s-1}` of the `s`-th pair, where sheet `s` meets sheet `0`. -/
def pairVertex (m k : ℕ) (hk : 6 * k - 5 < 6 * m + 4) : (catTree m).V :=
  ⟨6 * k - 5, hk⟩

theorem pairIndex_pairVertex (m k : ℕ) (hk1 : 1 ≤ k)
    (hk : 6 * k - 5 < 6 * m + 4) : pairIndex (pairVertex m k hk).val = k := by
  show pairIndex (6 * k - 5) = k
  unfold pairIndex lolli
  omega

/-- **Sheet `k` meets sheet `0`** at the vertex of its own pair. -/
theorem sourceEndpoint_pairVertex (m k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < m + 2)
    (hk : 6 * k - 5 < 6 * m + 4) :
    (caterpillarDatum m).sourceEndpoint (pairVertex m k hk) ⟨k, hk2⟩
      = (caterpillarDatum m).sourceEndpoint (pairVertex m k hk) 0 := by
  refine (caterpillarDatum m).sourceEndpoint_congr _ ?_
  show (catVertexPart m (pairVertex m k hk)).Rel ⟨k, hk2⟩ 0
  rw [catVertexPart, pairIndex_pairVertex m k hk1 hk]
  exact pairPart_rel_zero m k ⟨k, hk2⟩ rfl

theorem connectedOn_cumSheets (m : ℕ) :
    ∀ k, 1 ≤ k → k ≤ m + 2 →
      ConnectedOn (caterpillarDatum m).sourceGraph (cumSheets m k) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _ hle
    by_cases hk0 : k = 0
    · subst hk0
      rw [cumSheets_one]
      exact connectedOn_sheetImage m 0
    · have hk1 : 1 ≤ k := by omega
      have hklt : k < m + 2 := by omega
      have hbound : 6 * k - 5 < 6 * m + 4 := by omega
      rw [cumSheets_succ m k hklt]
      refine connectedOn_union (shared :=
        (caterpillarDatum m).sourceEndpoint (pairVertex m k hbound) ⟨k, hklt⟩)
        ?_ ?_ (ih hk1 (by omega)) (connectedOn_sheetImage m ⟨k, hklt⟩)
      · rw [sourceEndpoint_pairVertex m k hk1 hklt hbound]
        refine Finset.mem_biUnion.mpr ⟨0, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hk1
        · exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      · exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem mem_cumSheets_full (m : ℕ) (x : (caterpillarDatum m).SourceVertex) :
    x ∈ cumSheets m (m + 2) := by
  rw [cumSheets]
  refine Finset.mem_biUnion.mpr ⟨x.1.2, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact x.1.2.isLt
  · rw [sheetImage]
    exact Finset.mem_image.mpr ⟨x.1.1, Finset.mem_univ _,
      (caterpillarDatum m).sourceEndpoint_self x⟩

/-- **The source of the caterpillar datum is connected, uniformly in `g`.** -/
theorem caterpillarDatum_connected (m : ℕ) : (caterpillarDatum m).Connected :=
  graph_connected_of_connectedOn_full (cumSheets m (m + 2))
    (mem_cumSheets_full m)
    (connectedOn_cumSheets m (m + 2) (by omega) (le_refl _))

/-- **The caterpillar datum is a valid Draisma--Vargas gluing datum.** -/
theorem caterpillarDatum_valid (m : ℕ) : (caterpillarDatum m).Valid :=
  ⟨caterpillarDatum_connected m, caterpillarDatum_riemannHurwitz m⟩

/-! ## 5.  The Euler count: the source has genus `g`

Every vertex partition, and every occurrence partition over a pair edge, has
`m + 1` blocks; the remaining occurrence partitions are discrete with `m + 2`.
There are `3m + 1` pair edges (the `m + 1` slope-two spine edges and the
`2m = g - 2` stems) among the `6m + 3`, so

```
|V(G)| = (6m+4)(m+1),   |E(G)| = (6m+3)(m+1) + (3m+2),
genus  = |E| - |V| + 1 = 2m + 2 = g.
```
-/

/-- The indicator of a non-pair occurrence index, ignoring the exceptional
leaf edge `6m + 2`. -/
def nonPair (i : ℕ) : ℕ := if i % 6 = 1 ∨ i % 3 = 2 then 0 else 1

theorem sum_nonPair (m : ℕ) :
    ∑ i ∈ Finset.range (6 * m), nonPair i = 3 * m := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hw0 : nonPair (6 * k) = 1 := by unfold nonPair; rw [if_neg (by omega)]
    have hw1 : nonPair (6 * k + 1) = 0 := by unfold nonPair; rw [if_pos (by omega)]
    have hw2 : nonPair (6 * k + 2) = 0 := by unfold nonPair; rw [if_pos (by omega)]
    have hw3 : nonPair (6 * k + 3) = 1 := by unfold nonPair; rw [if_neg (by omega)]
    have hw4 : nonPair (6 * k + 4) = 1 := by unfold nonPair; rw [if_neg (by omega)]
    have hw5 : nonPair (6 * k + 5) = 0 := by unfold nonPair; rw [if_pos (by omega)]
    rw [show 6 * (k + 1) = 6 * k + 5 + 1 by ring, Finset.sum_range_succ,
      show 6 * k + 5 = 6 * k + 4 + 1 from rfl, Finset.sum_range_succ,
      show 6 * k + 4 = 6 * k + 3 + 1 from rfl, Finset.sum_range_succ,
      show 6 * k + 3 = 6 * k + 2 + 1 from rfl, Finset.sum_range_succ,
      show 6 * k + 2 = 6 * k + 1 + 1 from rfl, Finset.sum_range_succ,
      show 6 * k + 1 = 6 * k + 1 from rfl, Finset.sum_range_succ, ih,
      hw0, hw1, hw2, hw3, hw4, hw5]
    ring

theorem isPairEdge_iff_of_ne (m i : ℕ) (hi : i ≠ 6 * m + 2) :
    IsPairEdge m i ↔ (i % 6 = 1 ∨ i % 3 = 2) := by
  unfold IsPairEdge
  constructor
  · rintro (h | ⟨h, -⟩)
    exacts [Or.inl h, Or.inr h]
  · rintro (h | h)
    exacts [Or.inl h, Or.inr ⟨h, hi⟩]

/-- **There are `3m + 2` non-pair occurrences**, hence `3m + 1` pair ones. -/
theorem sum_nonPairEdge (m : ℕ) :
    (∑ i ∈ Finset.range (6 * m + 3),
      (if IsPairEdge m i then 0 else 1)) = 3 * m + 2 := by
  have hcongr : ∀ i ∈ Finset.range (6 * m),
      (if IsPairEdge m i then (0 : ℕ) else 1) = nonPair i := by
    intro i hi
    rw [Finset.mem_range] at hi
    unfold nonPair
    by_cases hp : i % 6 = 1 ∨ i % 3 = 2
    · rw [if_pos ((isPairEdge_iff_of_ne m i (by omega)).mpr hp), if_pos hp]
    · rw [if_neg (fun h => hp ((isPairEdge_iff_of_ne m i (by omega)).mp h)),
        if_neg hp]
  have h0 : (if IsPairEdge m (6 * m) then (0 : ℕ) else 1) = 1 := by
    rw [if_neg (by unfold IsPairEdge; omega)]
  have h1 : (if IsPairEdge m (6 * m + 1) then (0 : ℕ) else 1) = 0 := by
    rw [if_pos (by unfold IsPairEdge; omega)]
  have h2 : (if IsPairEdge m (6 * m + 2) then (0 : ℕ) else 1) = 1 := by
    rw [if_neg (by unfold IsPairEdge; omega)]
  rw [show 6 * m + 3 = 6 * m + 2 + 1 from rfl, Finset.sum_range_succ,
    show 6 * m + 2 = 6 * m + 1 + 1 from rfl, Finset.sum_range_succ,
    show 6 * m + 1 = 6 * m + 1 from rfl, Finset.sum_range_succ,
    Finset.sum_congr rfl hcongr, sum_nonPair, h0, h1, h2]

theorem card_blocks_catVertexPart (m : ℕ) (v : (catTree m).V) :
    Fintype.card (catVertexPart m v).Blocks = m + 1 := by
  have hv := v.isLt
  exact card_blocks_pairPart m _ (pairIndex_pos _) (pairIndex_lt m v.val (by omega))

theorem card_blocks_catEdgePart (m : ℕ) (i : Fin (6 * m + 3)) :
    Fintype.card (catEdgePart m (occ m i)).Blocks =
      if IsPairEdge m i.val then m + 1 else m + 2 := by
  have hi := i.isLt
  by_cases h : IsPairEdge m i.val
  · rw [catEdgePart_of_pair m i h, if_pos h]
    exact card_blocks_pairPart m _ (pairIndex_pos _)
      (pairIndex_lt m (i.val + 1) (by omega))
  · rw [catEdgePart_of_not_pair m i h, if_neg h]
    exact card_blocks_discrete (m + 2)

theorem card_blocks_vertexPartition (m : ℕ) (v : (catTree m).V) :
    Fintype.card ((caterpillarDatum m).vertexPartition v).Blocks = m + 1 :=
  card_blocks_catVertexPart m v

theorem card_blocks_edgePartition (m : ℕ) (i : Fin (6 * m + 3)) :
    Fintype.card ((caterpillarDatum m).edgePartition (occ m i)).Blocks =
      if IsPairEdge m i.val then m + 1 else m + 2 :=
  card_blocks_catEdgePart m i

theorem card_sourceVertex_caterpillarDatum (m : ℕ) :
    Fintype.card (caterpillarDatum m).SourceVertex = (6 * m + 4) * (m + 1) := by
  rw [GluingDatum.card_sourceVertex_eq_sum_card_blocks,
    Finset.sum_congr rfl (fun v _ => card_blocks_vertexPartition m v),
    Finset.sum_const, Finset.card_univ, card_vertices_catTree, smul_eq_mul]

theorem card_sourceEdge_caterpillarDatum (m : ℕ) :
    Fintype.card (caterpillarDatum m).SourceEdge
      = (6 * m + 3) * (m + 1) + (3 * m + 2) := by
  rw [GluingDatum.card_sourceEdge_eq_sum_card_blocks]
  have hEquiv := Fintype.sum_equiv (catEdgeEquiv m)
    (fun i : Fin (6 * m + 3) =>
      Fintype.card ((caterpillarDatum m).edgePartition (occ m i)).Blocks)
    (fun e : (catTree m).edges =>
      Fintype.card ((caterpillarDatum m).edgePartition e).Blocks)
    (fun _ => rfl)
  rw [← hEquiv, Finset.sum_congr rfl (fun i _ => card_blocks_edgePartition m i),
    Fin.sum_univ_eq_sum_range
    (fun i => if IsPairEdge m i then m + 1 else m + 2) (6 * m + 3)]
  have hsplit : ∀ i ∈ Finset.range (6 * m + 3),
      (if IsPairEdge m i then m + 1 else m + 2)
        = (m + 1) + (if IsPairEdge m i then 0 else 1) := by
    intro i _
    by_cases h : IsPairEdge m i
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, smul_eq_mul, sum_nonPairEdge]

/-- **The source of the caterpillar datum has genus `g = 2m + 2`.** -/
theorem genus_sourceGraph_caterpillarDatum (m : ℕ) :
    genus (caterpillarDatum m).sourceGraph = 2 * (m : ℤ) + 2 := by
  have hedges : Multiset.card (caterpillarDatum m).sourceGraph.edges =
      Fintype.card (caterpillarDatum m).SourceEdge :=
    GluingDatum.sourceGraph_edges_card _
  have hvertices : Fintype.card (caterpillarDatum m).sourceGraph.V =
      Fintype.card (caterpillarDatum m).SourceVertex :=
    Fintype.card_congr (Equiv.refl _)
  rw [genus, hedges, hvertices, card_sourceEdge_caterpillarDatum,
    card_sourceVertex_caterpillarDatum]
  push_cast
  ring

/-- **Full-dimensionality as a number.**  This is the `saturated` field of
`FullDimensionalSourcePresentation`: `3g - 3 = 2g + 2d - 5` with `d = g/2 + 1`.
It is the field that pays -- change-minimality, and with it dangling-no-glue,
become theorems once it is available. -/
theorem saturated_caterpillarDatum (m : ℕ) :
    ((catTree m).edges.card : ℤ)
      = 2 * genus (caterpillarDatum m).sourceGraph + 2 * ((m : ℤ) + 2) - 5 := by
  rw [card_edges_catTree, genus_sourceGraph_caterpillarDatum]
  push_cast
  ring

/-! ## 6.  The slope sequence

Part II, Proposition `prop-caterpillar-ballot` (caterpillar slopes and ballot
sequences), fixes the slopes `s_i` on the spine edges `h_i` of `H^CL_g`; this
datum realises the ballot sequence `(+,-,+,-,…)`, i.e.
`(s_1, …, s_{g-1}) = (2,1,2,1,…,2)`.  In the datum the slope of a target
occurrence is the dilation index of the source block through the spine sheet
`0`, and that index is `2` exactly over the pair edges: the slope-two spine
edges `h_{2j-1}`, and the `g - 2` stems, whose index `2` is the
`m(e_b) = 2` of Part II, Lemma `lm:bridge-and-loop`. -/

theorem block_pairPart_zero (m j : ℕ) (hj2 : j < m + 2) :
    (pairPart m j).block 0 = {0, ⟨j, hj2⟩} := by
  have hzero : (pairPart m j).repr 0 = 0 := by
    show (if ((0 : Fin (m + 2)) : ℕ) = j then (0 : Fin (m + 2)) else 0) = 0
    split_ifs <;> rfl
  ext k
  rw [SheetPartition.mem_block_iff, SheetPartition.rel_iff, hzero, pairPart_repr,
    Finset.mem_insert, Finset.mem_singleton]
  by_cases hk : (k : ℕ) = j
  · rw [if_pos hk]
    exact ⟨fun _ => Or.inr (Fin.ext hk), fun _ => rfl⟩
  · rw [if_neg hk]
    constructor
    · intro h; exact Or.inl h.symm
    · rintro (h | h)
      · exact h.symm
      · exact absurd (congrArg Fin.val h) hk

theorem blockCard_pairPart_zero (m j : ℕ) (hj1 : 1 ≤ j) (hj2 : j < m + 2) :
    (pairPart m j).blockCard 0 = 2 := by
  rw [SheetPartition.blockCard, block_pairPart_zero m j hj2,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton, Fin.ext_iff, Fin.val_zero]
      omega),
    Finset.card_singleton]

theorem blockCard_discrete (d : ℕ) (k : Fin d) :
    (SheetPartition.discrete d).blockCard k = 1 := by
  have hblock : (SheetPartition.discrete d).block k = {k} := by
    ext j
    rw [SheetPartition.mem_block_iff, Finset.mem_singleton,
      SheetPartition.discrete_rel_iff]
    exact eq_comm
  rw [SheetPartition.blockCard, hblock, Finset.card_singleton]

/-- **The slope sequence `(2,1,2,1,…,2)`.**  The dilation index of the source
block through the spine sheet is `2` over a pair edge and `1` elsewhere. -/
theorem sourceEdgeIndex_spineSheet (m : ℕ) (i : Fin (6 * m + 3)) :
    (caterpillarDatum m).sourceEdgeIndex
        ((caterpillarDatum m).sourceEdge (occ m i) 0)
      = if IsPairEdge m i.val then 2 else 1 := by
  have hi := i.isLt
  rw [GluingDatum.sourceEdgeIndex_sourceEdge]
  show (catEdgePart m (occ m i)).blockCard 0 = _
  by_cases h : IsPairEdge m i.val
  · rw [catEdgePart_of_pair m i h, if_pos h]
    exact blockCard_pairPart_zero m _ (pairIndex_pos _)
      (pairIndex_lt m (i.val + 1) (by omega))
  · rw [catEdgePart_of_not_pair m i h, if_neg h]
    exact blockCard_discrete (m + 2) 0

/-! ## 7.  Non-vacuity

Both ends of the range the Part II seed needs are real objects: `g = 2`
(`m = 0`, degree `2`) and `g = 4` (`m = 1`, degree `3`, the two morphisms of
Part II, Example `ex-chain-loops`). -/

example : GluingDatum (catTree 0) 2 := caterpillarDatum 0
example : GluingDatum (catTree 1) 3 := caterpillarDatum 1

example : (caterpillarDatum 0).Valid := caterpillarDatum_valid 0
example : (caterpillarDatum 1).Valid := caterpillarDatum_valid 1

example : Fintype.card (caterpillarDatum 0).SourceVertex = 4 :=
  card_sourceVertex_caterpillarDatum 0
example : Fintype.card (caterpillarDatum 0).SourceEdge = 5 :=
  card_sourceEdge_caterpillarDatum 0
example : Fintype.card (caterpillarDatum 1).SourceVertex = 20 :=
  card_sourceVertex_caterpillarDatum 1
example : Fintype.card (caterpillarDatum 1).SourceEdge = 23 :=
  card_sourceEdge_caterpillarDatum 1

/-- `g = 2`: the source has genus two. -/
example : genus (caterpillarDatum 0).sourceGraph = 2 := by
  have h := genus_sourceGraph_caterpillarDatum 0
  norm_num at h
  exact h

/-- `g = 4`: the source has genus four. -/
example : genus (caterpillarDatum 1).sourceGraph = 4 := by
  have h := genus_sourceGraph_caterpillarDatum 1
  norm_num at h
  exact h

/-- `g = 4`: the spine slopes are `(2, 1, 2)`. -/
example : (caterpillarDatum 1).sourceEdgeIndex
    ((caterpillarDatum 1).sourceEdge (occ 1 ⟨1, by omega⟩) 0) = 2 := by
  rw [sourceEdgeIndex_spineSheet, if_pos (by
    show IsPairEdge 1 1
    unfold IsPairEdge; omega)]

example : (caterpillarDatum 1).sourceEdgeIndex
    ((caterpillarDatum 1).sourceEdge (occ 1 ⟨4, by omega⟩) 0) = 1 := by
  rw [sourceEdgeIndex_spineSheet, if_neg (by
    show ¬ IsPairEdge 1 4
    unfold IsPairEdge; omega)]

example : (caterpillarDatum 1).sourceEdgeIndex
    ((caterpillarDatum 1).sourceEdge (occ 1 ⟨7, by omega⟩) 0) = 2 := by
  rw [sourceEdgeIndex_spineSheet, if_pos (by
    show IsPairEdge 1 7
    unfold IsPairEdge; omega)]

/-- `g = 4`: the two stems `2` and `5` carry index two (`m(e_b) = 2`). -/
example : (caterpillarDatum 1).sourceEdgeIndex
    ((caterpillarDatum 1).sourceEdge (occ 1 ⟨2, by omega⟩) 0) = 2 := by
  rw [sourceEdgeIndex_spineSheet, if_pos (by
    show IsPairEdge 1 2
    unfold IsPairEdge; omega)]

/-- `g = 4`: the four leaf edges `0, 3, 6, 8` are folded, index one each. -/
example : (caterpillarDatum 1).sourceEdgeIndex
    ((caterpillarDatum 1).sourceEdge (occ 1 ⟨8, by omega⟩) 0) = 1 := by
  rw [sourceEdgeIndex_spineSheet, if_neg (by
    show ¬ IsPairEdge 1 8
    unfold IsPairEdge; omega)]

end DraismaVargas.LocalCases.CaterpillarDatum
