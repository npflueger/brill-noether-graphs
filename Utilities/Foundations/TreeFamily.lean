module

public import ChipFiringWithLean.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# A parametric family of trees

A `CFGraph` written as a literal `Multiset.ofList [...]` of fixed size can have
its structural facts discharged by `decide`.  Nothing of the kind is available
at a *variable* genus, and `decide` is exactly what is unavailable there.

This file supplies a family of trees indexed by a natural number `n` *and* an
arbitrary parent function, with connectivity, genus zero and the two
cardinality counts proved uniformly in the index.  No decision procedure is
used anywhere, and nothing in the file unfolds a concrete finite structure.
The family is sized for target trees of the tropical morphisms of
Draisma--Vargas Part I (arXiv:1909.12924) at an arbitrary genus; see the counts
at the stable size below.

## The family

`rootedTree n parent hparent` has vertex set `Fin (n + 1)` and one edge
`(parent i, i.succ)` for each `i : Fin n`, where `hparent` says that the parent
of `i.succ` has a strictly smaller index.  Rooting a tree at a vertex and
recording, for each non-root vertex, its neighbour towards the root is a
bijection between rooted trees on `n + 1` labelled vertices and such parent
functions, so this *is* the family of all trees, not a special case of it: the
path is `parent := Fin.castSucc` and the star is `parent := fun _ => 0`.  The
uniformity is in the pair `(n, parent)`, and every proof below is by induction
or by a rank argument, never by evaluation.

## Main results

* `rootedTree` -- the family, together with `pathGraph` and `starGraph`.
* `card_vertices_rootedTree`, `card_edges_rootedTree` -- `n + 1` and `n`.
* `rootedTree_connected` -- connectivity, from the no-separation definition
  `graph_connected` used throughout this repository.
* `rootedTree_genus` -- genus `0`, i.e. these really are trees.
* `num_edges_rootedTree_eq_one` -- no parallel occurrences: a tree edge carries
  multiplicity exactly `1`.  (This is what lets a single-edge contraction whose
  hypothesis is `num_edges G a b = 1` be applied to a member of the family.)
* `card_vertices_rootedTree_stable`, `card_edges_rootedTree_stable` -- the two
  counts at the stable size: `3 * g - 3` edges on `Fin (3 * g - 2)`.

## Local lemmas

`graph_connected_of_ranked_parent_local` proves, for an abstract `CFGraph`,
that a rank function decreasing along a parent map towards a root gives
connectivity, and `num_edges_pos_of_mem_edges_local` shows that an occurrence
in the edge multiset has positive multiplicity.  Both are proved here so that
this file's import surface stays at `ChipFiringWithLean.Basic`.
-/

universe u

namespace DraismaVargas.Infrastructure.TreeFamily

/-! ## Two local lemmas -/

/-- An occurrence of `(x, y)` in the edge multiset witnesses positive
multiplicity. -/
theorem num_edges_pos_of_mem_edges_local (G : CFGraph.{u}) (x y : G.V)
    (hmem : (x, y) ∈ G.edges) : 0 < num_edges G x y :=
  Multiset.card_pos_iff_exists_mem.mpr
    ⟨(x, y), Multiset.mem_filter.mpr ⟨hmem, Or.inl rfl⟩⟩

/-- The reversed occurrence also witnesses positive multiplicity. -/
theorem num_edges_pos_of_mem_edges_symm_local (G : CFGraph.{u}) (x y : G.V)
    (hmem : (y, x) ∈ G.edges) : 0 < num_edges G x y :=
  Multiset.card_pos_iff_exists_mem.mpr
    ⟨(y, x), Multiset.mem_filter.mpr ⟨hmem, Or.inr rfl⟩⟩

/-- A graph carrying a rank function that strictly decreases along a parent map
towards a root, with an edge at every step, is connected.

This is the no-separation form of "every vertex reaches the root": take a vertex
of least rank on whichever side of the cut misses the root; it is not the root,
so its parent has smaller rank, so the parent lies on the other side, and the
step edge crosses the cut. -/
theorem graph_connected_of_ranked_parent_local {G : CFGraph.{u}} (root : G.V)
    (parent : G.V → G.V) (rank : G.V → ℕ)
    (hstep : ∀ v : G.V, v = root ∨
      (rank (parent v) < rank v ∧ 0 < num_edges G v (parent v))) :
    graph_connected G := by
  intro S hSplit
  obtain ⟨inside, outside, hInside, hOutside⟩ := hSplit
  by_cases hRoot : root ∈ S
  · have hNonempty : (Finset.univ \ S).Nonempty :=
      ⟨outside, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hOutside⟩⟩
    obtain ⟨v, hv, hmin⟩ := (Finset.univ \ S).exists_min_image rank hNonempty
    have hvOut : v ∉ S := (Finset.mem_sdiff.mp hv).2
    have hvne : v ≠ root := fun hEq => hvOut (hEq ▸ hRoot)
    rcases hstep v with hEq | ⟨hrank, hedge⟩
    · exact absurd hEq hvne
    · have hParentIn : parent v ∈ S := by
        by_contra hParentOut
        have hMem : parent v ∈ Finset.univ \ S :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hParentOut⟩
        exact absurd (hmin _ hMem) (not_le.mpr hrank)
      refine ⟨parent v, hParentIn, v, hvOut, ?_⟩
      rw [num_edges_symmetric]
      exact hedge
  · obtain ⟨v, hv, hmin⟩ := S.exists_min_image rank ⟨inside, hInside⟩
    have hvne : v ≠ root := fun hEq => hRoot (hEq ▸ hv)
    rcases hstep v with hEq | ⟨hrank, hedge⟩
    · exact absurd hEq hvne
    · exact ⟨v, hv, parent v, fun hParentIn =>
        absurd (hmin _ hParentIn) (not_le.mpr hrank), hedge⟩

/-! ## The family -/

/-- The edge multiset of the rooted tree with parent function `parent`: one
occurrence `(parent i, i.succ)` for every `i : Fin n`. -/
def treeEdges (n : ℕ) (parent : Fin n → Fin (n + 1)) :
    Multiset (Fin (n + 1) × Fin (n + 1)) :=
  (Finset.univ : Finset (Fin n)).val.map fun i => (parent i, i.succ)

/-- The parent map extended to all of `Fin (n + 1)` by fixing the root `0`. -/
def treeParent (n : ℕ) (parent : Fin n → Fin (n + 1)) (v : Fin (n + 1)) :
    Fin (n + 1) :=
  Fin.cases (motive := fun _ => Fin (n + 1)) 0 parent v

@[simp] theorem treeParent_zero (n : ℕ) (parent : Fin n → Fin (n + 1)) :
    treeParent n parent 0 = 0 := rfl

@[simp] theorem treeParent_succ (n : ℕ) (parent : Fin n → Fin (n + 1))
    (i : Fin n) : treeParent n parent i.succ = parent i := rfl

/-- The tree on `Fin (n + 1)` determined by a parent function that always points
to a strictly smaller index.  Every tree on `n + 1` labelled vertices, rooted
anywhere, arises this way after relabelling the vertices by a breadth-first
order. -/
def rootedTree (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) : CFGraph where
  V := Fin (n + 1)
  edges := treeEdges n parent
  loopless := by
    intro v hmem
    obtain ⟨i, -, hEq⟩ := Multiset.mem_map.mp hmem
    have hFirst : parent i = v := congrArg Prod.fst hEq
    have hSecond : i.succ = v := congrArg Prod.snd hEq
    have hi := hparent i
    rw [hFirst] at hi
    rw [← hSecond] at hi
    simp only [Fin.val_succ] at hi
    omega

theorem rootedTree_V (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) :
    (rootedTree n parent hparent).V = Fin (n + 1) := rfl

theorem rootedTree_edges (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) :
    (rootedTree n parent hparent).edges = treeEdges n parent := rfl

/-- `num_edges` of a member of the family, transported to the bare `Fin` type.
Stating it once avoids rewriting under the definitional equality
`(rootedTree n parent hparent).V = Fin (n + 1)`. -/
theorem num_edges_rootedTree_eq (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) (v w : Fin (n + 1)) :
    num_edges (rootedTree n parent hparent) v w
      = Multiset.card ((treeEdges n parent).filter fun e => e = (v, w) ∨ e = (w, v)) :=
  rfl

/-- Every declared parent step is an occurrence of the edge multiset. -/
theorem mem_edges_rootedTree (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) (i : Fin n) :
    (parent i, i.succ) ∈ (rootedTree n parent hparent).edges :=
  Multiset.mem_map.mpr ⟨i, Finset.mem_val.mpr (Finset.mem_univ i), rfl⟩

/-! ## The two counts -/

theorem card_edges_rootedTree (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) :
    Multiset.card (rootedTree n parent hparent).edges = n := by
  show Multiset.card (treeEdges n parent) = n
  rw [treeEdges, Multiset.card_map, ← Finset.card_def, Finset.card_univ, Fintype.card_fin]

theorem card_vertices_rootedTree (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) :
    Fintype.card (rootedTree n parent hparent).V = n + 1 :=
  Fintype.card_fin (n + 1)

/-! ## Connectivity -/

theorem rootedTree_connected (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) :
    graph_connected (rootedTree n parent hparent) := by
  refine graph_connected_of_ranked_parent_local (G := rootedTree n parent hparent)
    (0 : Fin (n + 1)) (treeParent n parent) Fin.val ?_
  intro v
  induction v using Fin.cases with
  | zero => exact Or.inl rfl
  | succ i =>
    refine Or.inr ⟨?_, ?_⟩
    · show (parent i).val < (i.succ).val
      simp only [Fin.val_succ]
      exact Nat.lt_succ_of_le (hparent i)
    · show 0 < num_edges (rootedTree n parent hparent) i.succ (parent i)
      exact num_edges_pos_of_mem_edges_symm_local _ _ _
        (mem_edges_rootedTree n parent hparent i)

/-! ## Genus zero -/

theorem rootedTree_genus (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) :
    genus (rootedTree n parent hparent) = 0 := by
  rw [genus, card_edges_rootedTree, card_vertices_rootedTree]
  push_cast
  ring

/-! ## No parallel occurrences -/

/-- A tree edge carries multiplicity exactly one.  This is what makes a
single-edge contraction whose hypothesis is `num_edges G a b = 1` applicable
to the family. -/
theorem num_edges_rootedTree_eq_one (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) (i : Fin n) :
    num_edges (rootedTree n parent hparent) (parent i) i.succ = 1 := by
  have hkey : ∀ j : Fin n,
      ((parent j, j.succ) = (parent i, i.succ) ∨
        (parent j, j.succ) = (i.succ, parent i)) ↔ j = i := by
    intro j
    constructor
    · rintro (hEq | hEq)
      · exact Fin.succ_injective n (congrArg Prod.snd hEq)
      · exfalso
        have h1 : parent j = i.succ := congrArg Prod.fst hEq
        have h2 : j.succ = parent i := congrArg Prod.snd hEq
        have hj := hparent j
        have hi := hparent i
        rw [h1] at hj
        rw [← h2] at hi
        simp only [Fin.val_succ] at hi hj
        omega
    · rintro rfl
      exact Or.inl rfl
  have hfilter :
      Multiset.filter
          ((fun e : Fin (n + 1) × Fin (n + 1) =>
              e = (parent i, i.succ) ∨ e = (i.succ, parent i)) ∘
            fun k : Fin n => (parent k, k.succ))
          (Finset.univ : Finset (Fin n)).val
        = Multiset.filter (fun j : Fin n => j = i) (Finset.univ : Finset (Fin n)).val :=
    Multiset.filter_congr fun j _ => hkey j
  rw [num_edges_rootedTree_eq, treeEdges, Multiset.filter_map, Multiset.card_map, hfilter,
    Multiset.filter_eq', Multiset.card_replicate,
    Multiset.count_eq_one_of_mem (Finset.univ : Finset (Fin n)).nodup (Finset.mem_univ i)]

/-! ## The path -/

/-- The path on `n + 1` vertices: `0 - 1 - ... - n`. -/
def pathGraph (n : ℕ) : CFGraph :=
  rootedTree n Fin.castSucc fun i => le_of_eq (Fin.val_castSucc i)

theorem card_edges_pathGraph (n : ℕ) :
    Multiset.card (pathGraph n).edges = n :=
  card_edges_rootedTree _ _ _

theorem card_vertices_pathGraph (n : ℕ) :
    Fintype.card (pathGraph n).V = n + 1 :=
  card_vertices_rootedTree _ _ _

theorem pathGraph_connected (n : ℕ) : graph_connected (pathGraph n) :=
  rootedTree_connected _ _ _

theorem pathGraph_genus (n : ℕ) : genus (pathGraph n) = 0 :=
  rootedTree_genus _ _ _

theorem num_edges_pathGraph_eq_one (n : ℕ) (i : Fin n) :
    num_edges (pathGraph n) i.castSucc i.succ = 1 :=
  num_edges_rootedTree_eq_one _ _ _ i

/-! ## The star -/

/-- The star with `n` leaves, all attached to the vertex `0`. -/
def starGraph (n : ℕ) : CFGraph :=
  rootedTree n (fun _ => 0) fun _ => Nat.zero_le _

theorem card_edges_starGraph (n : ℕ) :
    Multiset.card (starGraph n).edges = n :=
  card_edges_rootedTree _ _ _

theorem card_vertices_starGraph (n : ℕ) :
    Fintype.card (starGraph n).V = n + 1 :=
  card_vertices_rootedTree _ _ _

theorem starGraph_connected (n : ℕ) : graph_connected (starGraph n) :=
  rootedTree_connected _ _ _

theorem starGraph_genus (n : ℕ) : genus (starGraph n) = 0 :=
  rootedTree_genus _ _ _

/-! ## The counts at the stable size

A tree with `3 * g - 3` edges, the dimension of the moduli space of genus-`g`
tropical curves, is the size of the target tree of a full-dimensional,
full-rank tropical morphism in the sense of Draisma--Vargas Part I
(arXiv:1909.12924).  Instantiating the family at `n := 3 * g - 3` gives
`3 * g - 3` edges on the vertex set `Fin (3 * g - 2)`; no morphism is
constructed here, only the counts. -/

theorem card_edges_rootedTree_stable (g : ℕ)
    (parent : Fin (3 * g - 3) → Fin (3 * g - 3 + 1))
    (hparent : ∀ i, (parent i).val ≤ i.val) :
    Multiset.card (rootedTree (3 * g - 3) parent hparent).edges = 3 * g - 3 :=
  card_edges_rootedTree _ _ _

theorem card_vertices_rootedTree_stable (g : ℕ) (hg : 1 ≤ g)
    (parent : Fin (3 * g - 3) → Fin (3 * g - 3 + 1))
    (hparent : ∀ i, (parent i).val ≤ i.val) :
    Fintype.card (rootedTree (3 * g - 3) parent hparent).V = 3 * g - 2 := by
  rw [card_vertices_rootedTree]
  omega

end DraismaVargas.Infrastructure.TreeFamily
