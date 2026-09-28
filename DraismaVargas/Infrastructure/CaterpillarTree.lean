import DraismaVargas.Infrastructure.GluingDatum
import Utilities.Foundations.TreeFamily

/-!
# The caterpillar-of-loops target tree `T^CL_g`

Vargas, Part II (arXiv:2609.09109), the lemma on the combinatorial structure
of the caterpillar of loops (`lm:combinatorial-structure-caterpillar-of-loops`):
for even `g` the genus-`g` caterpillar of loops `H^CL_g` admits, after deleting the
dangling elements, one and only one target tree, namely

```
spine        u₁ --- p₂ --- p₃ --- … --- p_{g-1} --- u_g      (g - 1 edges)
stems        p_i --- u_i                     (2 ≤ i ≤ g-1,   g - 2 edges)
leaf edges   u_i --- v_i                     (1 ≤ i ≤ g,     g     edges)
```

`3g - 3` edges on `3g - 2` vertices, with `u_i` divalent, `p_i` trivalent and
`v_i` a leaf.  This file builds that tree **uniformly in `g`**, as a member of
`Infrastructure.TreeFamily.rootedTree`, so that connectivity, genus zero and
both cardinalities are inherited, and then provides the *edge dictionary*: an
explicit bijection `Fin (3g-3) ≃ (catTree m).edges` and, for every vertex, the
explicit list of its incident occurrences.

## Indexing

Even `g ≥ 2` is written `g = 2m + 2`, so the degree of the Part II morphism is
`d = m + 2`, the tree has `6m + 3` edges and `6m + 4` vertices, and **no
truncated subtraction appears in any size**.  Vertices are numbered

```
u_i = 3i - 3,  v_i = 3i - 2   (1 ≤ i ≤ g-1),   p_i = 3i - 4   (2 ≤ i ≤ g-1),
u_g = 6m + 2,  v_g = 6m + 3
```

which is the depth-first order from the root `u₁ = 0`.  In that order the
parent of a vertex is `parentIndex v = if v % 3 = 2 then v - 3 else v - 1`
(the truncation at `v = 2` is what attaches `p₂` to the root `u₁`), and the
*lollipop index* of a vertex is the single formula `lolli v = (v + 4) / 3`.
Edge `e` is the occurrence joining `parentIndex (e+1)` to `e+1`, so

* `e % 3 = 1`  --  the spine edge `h_i` with `i = (e+2)/3`;
* `e % 3 = 2`, `e ≠ 6m+2`  --  the stem `p_i u_i` with `i = (e+4)/3`;
* `e % 3 = 0`, or `e = 6m+2`  --  the leaf edge `u_i v_i`.

## Main results

* `catTree` -- the tree; `catTree_connected`, `catTree_genus`,
  `card_edges_catTree`, `card_vertices_catTree`.
* `occ` -- the occurrence of edge `e`, with `occ_bijective` and
  `catEdgeEquiv : Fin (6m+3) ≃ (catTree m).edges`.
* `incidentEdges_*` -- the incidence dictionary, one lemma for each of the six
  vertex classes, together with `sum_incident_*`/`card_incident_*` readers.

Nothing in this file mentions sheets, degrees or gluing data; the caterpillar
`GluingDatum` is `LocalCases.CaterpillarDatum`.
-/

namespace DraismaVargas.Infrastructure.CaterpillarTree

open Finset

/-! ## 1.  The parent function -/

/-- The parent of vertex `v` in the depth-first numbering of `T^CL_g`.  The
truncation `2 - 3 = 0` attaches `p₂` to the root `u₁ = 0`. -/
def parentIndex (v : ℕ) : ℕ := if v % 3 = 2 then v - 3 else v - 1

theorem parentIndex_le (v : ℕ) : parentIndex v + 1 ≤ v ∨ v = 0 := by
  unfold parentIndex; split_ifs <;> omega

theorem parentIndex_le_pred (v : ℕ) : parentIndex v ≤ v - 1 := by
  unfold parentIndex; split_ifs <;> omega

/-- The parent relation, as arithmetic omega can use. -/
theorem parentIndex_eq_iff (c v : ℕ) :
    parentIndex c = v ↔
      ((c % 3 = 2 ∧ c - 3 = v) ∨ (c % 3 ≠ 2 ∧ c - 1 = v)) := by
  unfold parentIndex
  split_ifs with h
  · simp [h]
  · simp [h]

/-! ## 2.  The tree -/

/-- The parent map of `T^CL_g`, in the shape `TreeFamily.rootedTree` wants. -/
def catParent (m : ℕ) (i : Fin (6 * m + 3)) : Fin (6 * m + 3 + 1) :=
  ⟨parentIndex (i.val + 1), by have := parentIndex_le_pred (i.val + 1); omega⟩

@[simp] theorem catParent_val (m : ℕ) (i : Fin (6 * m + 3)) :
    (catParent m i).val = parentIndex (i.val + 1) := rfl

theorem catParent_le (m : ℕ) (i : Fin (6 * m + 3)) :
    (catParent m i).val ≤ i.val := by
  have := parentIndex_le_pred (i.val + 1); simp only [catParent_val]; omega

/-- **The caterpillar target tree `T^CL_g` for `g = 2m + 2`.** -/
def catTree (m : ℕ) : CFGraph :=
  TreeFamily.rootedTree (6 * m + 3) (catParent m) (catParent_le m)

theorem catTree_V (m : ℕ) : (catTree m).V = Fin (6 * m + 4) := rfl

theorem catTree_connected (m : ℕ) : graph_connected (catTree m) :=
  TreeFamily.rootedTree_connected _ _ _

theorem catTree_genus (m : ℕ) : genus (catTree m) = 0 :=
  TreeFamily.rootedTree_genus _ _ _

theorem card_edges_catTree (m : ℕ) :
    Multiset.card (catTree m).edges = 6 * m + 3 :=
  TreeFamily.card_edges_rootedTree _ _ _

theorem card_vertices_catTree (m : ℕ) :
    Fintype.card (catTree m).V = 6 * m + 4 :=
  TreeFamily.card_vertices_rootedTree _ _ _

/-- The `3g - 3` count in the paper's own indexing. -/
theorem card_edges_catTree_genus (m : ℕ) :
    Multiset.card (catTree m).edges = 3 * (2 * m + 2) - 3 := by
  rw [card_edges_catTree]; omega

/-- The `3g - 2` count in the paper's own indexing. -/
theorem card_vertices_catTree_genus (m : ℕ) :
    Fintype.card (catTree m).V = 3 * (2 * m + 2) - 2 := by
  rw [card_vertices_catTree]; omega

/-- A vertex of `T^CL_g` from its index. -/
def vtx (m : ℕ) (v : ℕ) (h : v < 6 * m + 4) : (catTree m).V := ⟨v, h⟩

@[simp] theorem vtx_val (m v : ℕ) (h : v < 6 * m + 4) : (vtx m v h).val = v := rfl

/-! ## 3.  The occurrence dictionary -/

/-- The ordered endpoints of the tree edge indexed by `i`. -/
def endpoints (m : ℕ) (i : Fin (6 * m + 3)) : (catTree m).V × (catTree m).V :=
  (catParent m i, i.succ)

@[simp] theorem endpoints_fst (m : ℕ) (i : Fin (6 * m + 3)) :
    (endpoints m i).1 = catParent m i := rfl

@[simp] theorem endpoints_snd (m : ℕ) (i : Fin (6 * m + 3)) :
    (endpoints m i).2 = i.succ := rfl

/-- An occurrence multiplicity is at most the edge multiplicity of its pair. -/
theorem count_le_num_edges (G : CFGraph) (v w : G.V) :
    Multiset.count (v, w) G.edges ≤ num_edges G v w := by
  classical
  rw [Multiset.count_eq_card_filter_eq]
  exact Multiset.card_le_card
    (Multiset.monotone_filter_right _ (fun _ hx => Or.inl hx.symm))

theorem count_catTree_edges (m : ℕ) (i : Fin (6 * m + 3)) :
    Multiset.count (endpoints m i) (catTree m).edges = 1 := by
  have hOne : num_edges (catTree m) (catParent m i) i.succ = 1 :=
    TreeFamily.num_edges_rootedTree_eq_one _ _ _ i
  have hle : Multiset.count (endpoints m i) (catTree m).edges
      ≤ num_edges (catTree m) (catParent m i) i.succ :=
    count_le_num_edges (catTree m) (catParent m i) i.succ
  have hpos : 0 < Multiset.count (endpoints m i) (catTree m).edges :=
    Multiset.count_pos.mpr (TreeFamily.mem_edges_rootedTree _ _ _ i)
  omega

/-- The occurrence of the tree edge indexed by `e`: it joins `parentIndex (e+1)`
to `e + 1`. -/
def occ (m : ℕ) (i : Fin (6 * m + 3)) : (catTree m).edges :=
  ⟨endpoints m i, ⟨0, by rw [count_catTree_edges]; norm_num⟩⟩

@[simp] theorem occ_coe (m : ℕ) (i : Fin (6 * m + 3)) :
    ((occ m i : (catTree m).edges) : (catTree m).V × (catTree m).V)
      = endpoints m i := rfl

@[simp] theorem occ_fst (m : ℕ) (i : Fin (6 * m + 3)) :
    ((occ m i : (catTree m).edges) : (catTree m).V × (catTree m).V).1
      = catParent m i := rfl

@[simp] theorem occ_snd (m : ℕ) (i : Fin (6 * m + 3)) :
    ((occ m i : (catTree m).edges) : (catTree m).V × (catTree m).V).2
      = i.succ := rfl

theorem occ_injective (m : ℕ) : Function.Injective (occ m) := by
  intro i j hij
  have := congrArg
    (fun e : (catTree m).edges => (e : (catTree m).V × (catTree m).V).2) hij
  exact Fin.succ_injective _ this

theorem card_catTree_edges_type (m : ℕ) :
    Fintype.card (catTree m).edges = 6 * m + 3 := by
  rw [Multiset.card_coe, card_edges_catTree]

theorem occ_bijective (m : ℕ) : Function.Bijective (occ m) :=
  (Fintype.bijective_iff_injective_and_card (occ m)).mpr
    ⟨occ_injective m, by rw [Fintype.card_fin, card_catTree_edges_type]⟩

/-- **The edge dictionary**: the `3g - 3` occurrences of `T^CL_g` indexed by
`Fin (3g - 3)`. -/
noncomputable def catEdgeEquiv (m : ℕ) : Fin (6 * m + 3) ≃ (catTree m).edges :=
  Equiv.ofBijective (occ m) (occ_bijective m)

@[simp] theorem catEdgeEquiv_apply (m : ℕ) (i : Fin (6 * m + 3)) :
    catEdgeEquiv m i = occ m i := rfl


/-! ## 4.  The lollipop index of a vertex

`lolli v` is the index `i` of the lollipop `(p_i, u_i, v_i)` the vertex `v`
belongs to, and the single formula `(v + 4) / 3` covers all three shapes as
well as the two exceptional vertices `u_g = 6m+2`, `v_g = 6m+3`:

| `v`            | `u_i = 3i-3` | `v_i = 3i-2` | `p_i = 3i-4` | `u_g = 6m+2` | `v_g = 6m+3` |
|---|---|---|---|---|---|
| `(v+4)/3`      | `i`          | `i`          | `i`          | `2m+2 = g`   | `2m+2 = g`   |
-/

/-- The lollipop index of a target vertex. -/
def lolli (v : ℕ) : ℕ := (v + 4) / 3

theorem lolli_u (i : ℕ) (hi : 1 ≤ i) : lolli (3 * i - 3) = i := by
  unfold lolli; omega

theorem lolli_v (i : ℕ) (hi : 1 ≤ i) : lolli (3 * i - 2) = i := by
  unfold lolli; omega

theorem lolli_p (i : ℕ) (hi : 2 ≤ i) : lolli (3 * i - 4) = i := by
  unfold lolli; omega

theorem lolli_pos (v : ℕ) : 1 ≤ lolli v := by unfold lolli; omega

theorem lolli_le (m v : ℕ) (hv : v ≤ 6 * m + 3) : lolli v ≤ 2 * m + 2 := by
  unfold lolli; omega

/-! ## 5.  Incidence -/

/-- The indices of the occurrences incident to a target vertex. -/
def incidentIndices (m : ℕ) (v : (catTree m).V) : Finset (Fin (6 * m + 3)) :=
  Finset.univ.filter fun i =>
    parentIndex (i.val + 1) = v.val ∨ i.val + 1 = v.val

@[simp] theorem mem_incidentIndices (m : ℕ) (v : (catTree m).V)
    (i : Fin (6 * m + 3)) :
    i ∈ incidentIndices m v ↔
      (parentIndex (i.val + 1) = v.val ∨ i.val + 1 = v.val) := by
  simp [incidentIndices]

theorem mem_incidentEdges_occ (m : ℕ) (v : (catTree m).V)
    (i : Fin (6 * m + 3)) :
    occ m i ∈ GluingDatum.incidentEdges v ↔ i ∈ incidentIndices m v := by
  rw [GluingDatum.incidentEdges, Finset.mem_filter, mem_incidentIndices]
  simp only [Finset.mem_univ, true_and, occ_coe, endpoints_fst, endpoints_snd]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Fin.val h)
    · exact Or.inr (congrArg Fin.val h)
  · rintro (h | h)
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)

/-- The occurrence indexing as an embedding. -/
def occEmb (m : ℕ) : Fin (6 * m + 3) ↪ (catTree m).edges :=
  ⟨occ m, occ_injective m⟩

@[simp] theorem occEmb_apply (m : ℕ) (i : Fin (6 * m + 3)) :
    occEmb m i = occ m i := rfl

/-- **The incidence dictionary.**  The occurrences at a vertex are the images
of the indices whose parent or child is that vertex. -/
theorem incidentEdges_eq_map (m : ℕ) (v : (catTree m).V) :
    GluingDatum.incidentEdges v = (incidentIndices m v).map (occEmb m) := by
  ext e
  obtain ⟨i, rfl⟩ := (occ_bijective m).2 e
  rw [show occ m i = occEmb m i from rfl, Finset.mem_map' (occEmb m)]
  exact mem_incidentEdges_occ m v i

theorem card_incidentEdges (m : ℕ) (v : (catTree m).V) :
    (GluingDatum.incidentEdges v).card = (incidentIndices m v).card := by
  rw [incidentEdges_eq_map, Finset.card_map]

theorem sum_incidentEdges {β : Type*} [AddCommMonoid β] (m : ℕ)
    (v : (catTree m).V) (f : (catTree m).edges → β) :
    (∑ e ∈ GluingDatum.incidentEdges v, f e)
      = ∑ i ∈ incidentIndices m v, f (occ m i) := by
  rw [incidentEdges_eq_map, Finset.sum_map]
  rfl

/-! ### Readers for the three incidence sizes -/

theorem card_incidentEdges_one (m : ℕ) (v : (catTree m).V)
    {a : Fin (6 * m + 3)} (hS : incidentIndices m v = {a}) :
    (GluingDatum.incidentEdges v).card = 1 := by
  rw [card_incidentEdges, hS, Finset.card_singleton]

theorem sum_incidentEdges_one {β : Type*} [AddCommMonoid β] (m : ℕ)
    (v : (catTree m).V) {a : Fin (6 * m + 3)}
    (hS : incidentIndices m v = {a}) (f : (catTree m).edges → β) :
    (∑ e ∈ GluingDatum.incidentEdges v, f e) = f (occ m a) := by
  rw [sum_incidentEdges, hS, Finset.sum_singleton]

theorem card_incidentEdges_two (m : ℕ) (v : (catTree m).V)
    {a b : Fin (6 * m + 3)} (hab : a ≠ b)
    (hS : incidentIndices m v = {a, b}) :
    (GluingDatum.incidentEdges v).card = 2 := by
  rw [card_incidentEdges, hS, Finset.card_insert_of_notMem (by simpa using hab),
    Finset.card_singleton]

theorem sum_incidentEdges_two {β : Type*} [AddCommMonoid β] (m : ℕ)
    (v : (catTree m).V) {a b : Fin (6 * m + 3)} (hab : a ≠ b)
    (hS : incidentIndices m v = {a, b}) (f : (catTree m).edges → β) :
    (∑ e ∈ GluingDatum.incidentEdges v, f e) = f (occ m a) + f (occ m b) := by
  rw [sum_incidentEdges, hS, Finset.sum_insert (by simpa using hab),
    Finset.sum_singleton]

theorem card_incidentEdges_three (m : ℕ) (v : (catTree m).V)
    {a b c : Fin (6 * m + 3)} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hS : incidentIndices m v = {a, b, c}) :
    (GluingDatum.incidentEdges v).card = 3 := by
  rw [card_incidentEdges, hS,
    Finset.card_insert_of_notMem (by simp [hab, hac]),
    Finset.card_insert_of_notMem (by simpa using hbc), Finset.card_singleton]

theorem sum_incidentEdges_three {β : Type*} [AddCommMonoid β] (m : ℕ)
    (v : (catTree m).V) {a b c : Fin (6 * m + 3)} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hS : incidentIndices m v = {a, b, c})
    (f : (catTree m).edges → β) :
    (∑ e ∈ GluingDatum.incidentEdges v, f e)
      = f (occ m a) + f (occ m b) + f (occ m c) := by
  rw [sum_incidentEdges, hS, Finset.sum_insert (by simp [hab, hac]),
    Finset.sum_insert (by simpa using hbc), Finset.sum_singleton, add_assoc]

/-! ### The six vertex classes

Every vertex of `T^CL_g` falls into exactly one of six classes, and the
incident occurrences are read off from `parentIndex`:

| class | vertex | condition on `a = v.val` | incident indices | valency |
|---|---|---|---|---|
| (a) | `u₁`         | `a = 0`                         | `{0, 1}`          | 2 |
| (b) | `v_i`, `i<g` | `a % 3 = 1`                     | `{a-1}`           | 1 |
| (c) | `u_i`, `1<i<g` | `a % 3 = 0`, `3 ≤ a ≤ 6m`     | `{a-1, a}`        | 2 |
| (d) | `v_g`        | `a = 6m+3`                      | `{6m+2}`          | 1 |
| (e) | `p_i`        | `a % 3 = 2`, `a + 1 ≤ 6m`       | `{a-1, a, a+2}`   | 3 |
| (f) | `u_g`        | `a = 6m+2`                      | `{6m+1, 6m+2}`    | 2 |

`vertexClass` records that the six classes are exhaustive. -/

theorem incidentIndices_root (m : ℕ) (v : (catTree m).V) (hv : v.val = 0) :
    incidentIndices m v =
      {(⟨0, by omega⟩ : Fin (6 * m + 3)), ⟨1, by omega⟩} := by
  ext i
  simp only [mem_incidentIndices, Finset.mem_insert, Finset.mem_singleton,
    Fin.ext_iff, parentIndex_eq_iff, hv]
  omega

theorem incidentIndices_leaf (m : ℕ) (v : (catTree m).V) (hv : v.val % 3 = 1) :
    incidentIndices m v = {(⟨v.val - 1, by omega⟩ : Fin (6 * m + 3))} := by
  have hlt := v.isLt
  ext i
  simp only [mem_incidentIndices, Finset.mem_singleton, Fin.ext_iff,
    parentIndex_eq_iff]
  omega

theorem incidentIndices_lastLeaf (m : ℕ) (v : (catTree m).V)
    (hv : v.val = 6 * m + 3) :
    incidentIndices m v = {(⟨6 * m + 2, by omega⟩ : Fin (6 * m + 3))} := by
  ext i
  have := i.isLt
  simp only [mem_incidentIndices, Finset.mem_singleton, Fin.ext_iff,
    parentIndex_eq_iff, hv]
  omega

theorem incidentIndices_stem (m : ℕ) (v : (catTree m).V) (hmod : v.val % 3 = 0)
    (hlo : 3 ≤ v.val) (hhi : v.val ≤ 6 * m) :
    incidentIndices m v =
      {(⟨v.val - 1, by omega⟩ : Fin (6 * m + 3)), ⟨v.val, by omega⟩} := by
  ext i
  simp only [mem_incidentIndices, Finset.mem_insert, Finset.mem_singleton,
    Fin.ext_iff, parentIndex_eq_iff]
  omega

theorem incidentIndices_lastStem (m : ℕ) (v : (catTree m).V)
    (hv : v.val = 6 * m + 2) :
    incidentIndices m v =
      {(⟨6 * m + 1, by omega⟩ : Fin (6 * m + 3)), ⟨6 * m + 2, by omega⟩} := by
  ext i
  have := i.isLt
  simp only [mem_incidentIndices, Finset.mem_insert, Finset.mem_singleton,
    Fin.ext_iff, parentIndex_eq_iff, hv]
  omega

theorem incidentIndices_junction (m : ℕ) (v : (catTree m).V)
    (hmod : v.val % 3 = 2) (hhi : v.val + 1 ≤ 6 * m) :
    incidentIndices m v =
      {(⟨v.val - 1, by omega⟩ : Fin (6 * m + 3)), ⟨v.val, by omega⟩,
        ⟨v.val + 2, by omega⟩} := by
  ext i
  simp only [mem_incidentIndices, Finset.mem_insert, Finset.mem_singleton,
    Fin.ext_iff, parentIndex_eq_iff]
  omega

/-- **The six classes are exhaustive.** -/
theorem vertexClass (m : ℕ) (v : (catTree m).V) :
    v.val = 0 ∨ v.val % 3 = 1 ∨ (v.val % 3 = 0 ∧ 3 ≤ v.val ∧ v.val ≤ 6 * m) ∨
      v.val = 6 * m + 3 ∨ (v.val % 3 = 2 ∧ v.val + 1 ≤ 6 * m) ∨
      v.val = 6 * m + 2 := by
  have hlt := v.isLt
  omega

/-! ## 6.  Non-vacuity

The tree is a real object at both ends of the range the Part II seed needs:
`g = 2` (`m = 0`, a path `u₁ u₂` with a leaf edge at each end) and `g = 4`
(`m = 1`, two junctions `p₂ p₃`). -/

example : Multiset.card (catTree 0).edges = 3 := card_edges_catTree 0
example : Fintype.card (catTree 0).V = 4 := card_vertices_catTree 0
example : graph_connected (catTree 0) := catTree_connected 0
example : genus (catTree 0) = 0 := catTree_genus 0

example : Multiset.card (catTree 1).edges = 9 := card_edges_catTree 1
example : Fintype.card (catTree 1).V = 10 := card_vertices_catTree 1
example : graph_connected (catTree 1) := catTree_connected 1
example : genus (catTree 1) = 0 := catTree_genus 1

/-- `g = 2`: the root `u₁` carries the leaf edge `0` and the spine edge `1`. -/
example : incidentIndices 0 ⟨0, by omega⟩
    = {(⟨0, by omega⟩ : Fin 3), ⟨1, by omega⟩} :=
  incidentIndices_root 0 ⟨0, by omega⟩ rfl

/-- `g = 2`: `u₂ = u_g` carries the spine edge `1` and the leaf edge `2`. -/
example : incidentIndices 0 ⟨2, by omega⟩
    = {(⟨1, by omega⟩ : Fin 3), ⟨2, by omega⟩} :=
  incidentIndices_lastStem 0 ⟨2, by omega⟩ rfl

/-- `g = 4`: the junction `p₂ = 2` is trivalent, with the two spine edges
`1 = h₁`, `4 = h₂` and the stem `2`. -/
example : incidentIndices 1 ⟨2, by omega⟩
    = {(⟨1, by omega⟩ : Fin 9), ⟨2, by omega⟩, ⟨4, by omega⟩} :=
  incidentIndices_junction 1 ⟨2, by omega⟩ rfl (by show (2 : ℕ) + 1 ≤ 6 * 1; omega)

/-- `g = 4`: the divalent `u₂ = 3` carries the stem `2` and the leaf edge `3`. -/
example : incidentIndices 1 ⟨3, by omega⟩
    = {(⟨2, by omega⟩ : Fin 9), ⟨3, by omega⟩} :=
  incidentIndices_stem 1 ⟨3, by omega⟩ rfl (by show 3 ≤ (3 : ℕ); omega)
    (by show (3 : ℕ) ≤ 6 * 1; omega)

/-- `g = 4`: the leaf `v₂ = 4` carries only the leaf edge `3`. -/
example : incidentIndices 1 ⟨4, by omega⟩ = {(⟨3, by omega⟩ : Fin 9)} :=
  incidentIndices_leaf 1 ⟨4, by omega⟩ rfl

end DraismaVargas.Infrastructure.CaterpillarTree
