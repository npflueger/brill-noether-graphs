module

public import DraismaVargasCount.Transport
public import DraismaVargas.Infrastructure.CaterpillarTree

@[expose] public section

/-!
# A normal form for the target tree, with the occurrence bijection as data

**Source.**  Draisma--Vargas Part I (arXiv:1909.12924): the target of a discrete tropical
morphism is a tree, as in the quotient-source construction of a gluing datum
(`subsection-gluing-datum`), and the compatible-labelling rule of the section on inherited
properties (`section-inherited-properties`) is what `Count.Transport.DatumIso` records.
Vargas, Part II (arXiv:2609.09109): because the set of combinatorial types is finite, the
fibre over every metric graph is finite (the finiteness statement at the end of the
subsection on symmetries of `TM(d,g)`).  This file is the first of the two pieces of that
finiteness here -- the normal form for the target -- and `Count/Transport.lean` is the
second.

## What is proved

* `orientedTree` -- the family of rooted trees on `Fin (n + 1)` given by a
  parent map `parent i ≤ i` **together with an orientation bit for every tree
  edge**, with `card_edges_orientedTree`, `card_vertices_orientedTree`,
  `orientedTree_connected`, `orientedTree_genus`, and the occurrence dictionary
  `occEquiv : Fin n ≃ (orientedTree …).edges`.  Storing every occurrence
  parent-first recovers `Infrastructure.TreeFamily.rootedTree` on the nose
  (`orientedTree_false`, a `rfl`).
* `exists_rank_of_key`, `ReachIn`, `exists_reachIn`, `exists_depth`,
  `exists_rankEquiv` -- the spanning-tree/breadth-first argument on an abstract
  `CFGraph`: in a connected graph every vertex is reachable from every root
  (this is the only use of `graph_connected`), depth to the root is a rank that
  strictly decreases along some incident edge, and counting strictly smaller
  keys turns that rank into a numbering `G.V ≃ Fin (n + 1)` in which every
  vertex but `0` has a neighbour with a strictly smaller number.
* `NormalForm` and `exists_normalForm` -- **the normal form.**  Every connected
  genus-zero `CFGraph` with `n` edge occurrences carries a numbering of its
  vertices, a parent map with `parent i ≤ i`, an orientation bit per tree edge,
  and a bijection of its **edge occurrences** with those of the corresponding
  `orientedTree` respecting *both* stored endpoints.  Genus zero enters exactly
  once: it makes the `n` chosen parent occurrences exhaust the occurrence
  multiset, by a cardinality argument.
* `pushforward`, `datumIso`, `NormalForm.pushDatum`, `NormalForm.datumIso` --
  **the transport caveat of `Count/Transport.lean` discharged.**  A gluing datum on an
  arbitrary target is carried to the normal-form target, and the resulting isomorphism is
  produced as a `Count.Transport.DatumIso` whose `targetEdge` is *the
  prescribed occurrence bijection* (`NormalForm.datumIso_targetEdge`, a `rfl`),
  not one chosen inside an endpoint fibre.  All sheet permutations are the
  identity, so `DatumIso`'s compatibility conditions hold by reflexivity.

## Non-vacuity

* `catNormalForm` -- the caterpillar-of-loops target tree `T^CL_g` of Part II is
  already in normal form, with `CaterpillarTree.catParent` as its parent map and
  every occurrence stored parent-first.
* `inPath`, `inPath_exists_flip` -- **the orientation bit is not a decoration.**
  A `CFGraph` stores each occurrence as an *ordered* pair and `DatumIso`'s
  `ends_fst`/`ends_snd` pin that order, while `TreeFamily.rootedTree` stores
  every occurrence parent-first.  The concrete connected genus-zero graph
  `inPath`, whose two occurrences share their second endpoint, therefore admits
  no normal form with all orientation bits `false`.  So "isomorphic to a
  `TreeFamily.rootedTree`" must be read with the orientation decoration; the family is
  still finite, which is all the count needs.

## What is not proved here

* Nothing about multiplicities, presentations or length matrices: the transport
  of those along a `DatumIso` is `DraismaVargasCount.TransportMultiplicity`.
* `exists_normalForm` assumes exactly `graph_connected G` and `genus G = 0`,
  both explicit; no trivalence, no full-dimensionality and no gluing datum.
* No `Fintype`/`Finite` statement about the fibre: that assembly is
  `DraismaVargas.Count.FibreNormalForm`.

## Consumers

`DraismaVargas.Count.FibreNormalForm` (finiteness of `Count.Fibre`).
-/


namespace DraismaVargas.Count.TargetNormalForm

open DraismaVargas.Infrastructure
open DraismaVargas.Count.Transport

/-! ## 1. The oriented rooted-tree family -/

/-- The stored occurrence of tree edge `i`: the parent step `parent i -- i.succ`,
written in the order selected by `flip`. -/
def orientedEdge (n : ℕ) (parent : Fin n → Fin (n + 1)) (flip : Fin n → Bool)
    (i : Fin n) : Fin (n + 1) × Fin (n + 1) :=
  if flip i then (i.succ, parent i) else (parent i, i.succ)

/-- The edge multiset of the oriented rooted tree. -/
def orientedEdges (n : ℕ) (parent : Fin n → Fin (n + 1)) (flip : Fin n → Bool) :
    Multiset (Fin (n + 1) × Fin (n + 1)) :=
  (Finset.univ : Finset (Fin n)).val.map (orientedEdge n parent flip)

theorem orientedEdge_max (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) (flip : Fin n → Bool) (i : Fin n) :
    max (orientedEdge n parent flip i).1.val (orientedEdge n parent flip i).2.val
      = i.val + 1 := by
  have hi := hparent i
  unfold orientedEdge
  split_ifs <;> simp only [Fin.val_succ] <;> omega

theorem orientedEdge_min (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) (flip : Fin n → Bool) (i : Fin n) :
    min (orientedEdge n parent flip i).1.val (orientedEdge n parent flip i).2.val
      = (parent i).val := by
  have hi := hparent i
  unfold orientedEdge
  split_ifs <;> simp only [Fin.val_succ] <;> omega

theorem orientedEdge_fst_ne_snd (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) (flip : Fin n → Bool) (i : Fin n) :
    (orientedEdge n parent flip i).1 ≠ (orientedEdge n parent flip i).2 := by
  have hmax := orientedEdge_max n parent hparent flip i
  have hmin := orientedEdge_min n parent hparent flip i
  have hi := hparent i
  intro hEq
  rw [hEq] at hmax hmin
  simp only [max_self, min_self] at hmax hmin
  omega

theorem orientedEdge_injective (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) (flip : Fin n → Bool) :
    Function.Injective (orientedEdge n parent flip) := by
  intro i j hEq
  have hi := orientedEdge_max n parent hparent flip i
  have hj := orientedEdge_max n parent hparent flip j
  rw [hEq, hj] at hi
  exact Fin.ext (by omega)

/-- **The oriented rooted tree.**  Same underlying tree as
`Infrastructure.TreeFamily.rootedTree`, but each occurrence is stored in the
order chosen by `flip`. -/
def orientedTree (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) (flip : Fin n → Bool) :
    CFGraph.{0} where
  V := Fin (n + 1)
  edges := orientedEdges n parent flip
  loopless := by
    intro v hmem
    obtain ⟨i, -, hEq⟩ := Multiset.mem_map.mp hmem
    exact orientedEdge_fst_ne_snd n parent hparent flip i
      ((congrArg Prod.fst hEq).trans (congrArg Prod.snd hEq).symm)

theorem orientedTree_V (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) (flip : Fin n → Bool) :
    (orientedTree n parent hparent flip).V = Fin (n + 1) := rfl

theorem orientedTree_edges (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) (flip : Fin n → Bool) :
    (orientedTree n parent hparent flip).edges = orientedEdges n parent flip := rfl

/-- With every occurrence stored parent-first the family is literally
`TreeFamily.rootedTree`. -/
theorem orientedTree_false (n : ℕ) (parent : Fin n → Fin (n + 1))
    (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) :
    orientedTree n parent hparent (fun _ => false)
      = TreeFamily.rootedTree n parent hparent := rfl

section Family

variable (n : ℕ) (parent : Fin n → Fin (n + 1))
  (hparent : ∀ i : Fin n, (parent i).val ≤ i.val) (flip : Fin n → Bool)

theorem card_edges_orientedTree :
    Multiset.card (orientedTree n parent hparent flip).edges = n := by
  show Multiset.card (orientedEdges n parent flip) = n
  rw [orientedEdges, Multiset.card_map, ← Finset.card_def, Finset.card_univ, Fintype.card_fin]

theorem card_vertices_orientedTree :
    Fintype.card (orientedTree n parent hparent flip).V = n + 1 :=
  Fintype.card_fin (n + 1)

theorem orientedTree_genus : genus (orientedTree n parent hparent flip) = 0 := by
  rw [genus, card_edges_orientedTree, card_vertices_orientedTree]
  push_cast
  ring

theorem mem_edges_orientedTree (i : Fin n) :
    orientedEdge n parent flip i ∈ (orientedTree n parent hparent flip).edges :=
  Multiset.mem_map.mpr ⟨i, Finset.mem_val.mpr (Finset.mem_univ i), rfl⟩

theorem num_edges_orientedTree_pos (i : Fin n) :
    0 < num_edges (orientedTree n parent hparent flip) i.succ (parent i) := by
  refine Multiset.card_pos_iff_exists_mem.mpr
    ⟨orientedEdge n parent flip i, Multiset.mem_filter.mpr
      ⟨mem_edges_orientedTree n parent hparent flip i, ?_⟩⟩
  unfold orientedEdge
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem orientedTree_connected : graph_connected (orientedTree n parent hparent flip) := by
  refine TreeFamily.graph_connected_of_ranked_parent_local
    (G := orientedTree n parent hparent flip) (0 : Fin (n + 1))
    (TreeFamily.treeParent n parent) Fin.val ?_
  intro v
  induction v using Fin.cases with
  | zero => exact Or.inl rfl
  | succ i =>
    refine Or.inr ⟨?_, ?_⟩
    · show (parent i).val < (i.succ).val
      simp only [Fin.val_succ]
      exact Nat.lt_succ_of_le (hparent i)
    · exact num_edges_orientedTree_pos n parent hparent flip i

/-! ### The occurrence dictionary of the normal-form target -/

theorem count_orientedEdge (i : Fin n) :
    0 < Multiset.count (orientedEdge n parent flip i)
      (orientedTree n parent hparent flip).edges :=
  Multiset.count_pos.mpr (mem_edges_orientedTree n parent hparent flip i)

/-- The occurrence of the normal-form target carrying tree edge `i`. -/
def occ (i : Fin n) : (orientedTree n parent hparent flip).edges :=
  ⟨orientedEdge n parent flip i, ⟨0, count_orientedEdge n parent hparent flip i⟩⟩

@[simp] theorem occ_coe (i : Fin n) :
    ((occ n parent hparent flip i : (orientedTree n parent hparent flip).edges) :
        (orientedTree n parent hparent flip).V ×
          (orientedTree n parent hparent flip).V) = orientedEdge n parent flip i := rfl

theorem occ_injective : Function.Injective (occ n parent hparent flip) := by
  intro i j hEq
  exact orientedEdge_injective n parent hparent flip (congrArg Sigma.fst hEq)

theorem card_orientedTree_edges_type :
    Fintype.card (orientedTree n parent hparent flip).edges = n := by
  rw [Multiset.card_coe, card_edges_orientedTree]

theorem occ_bijective : Function.Bijective (occ n parent hparent flip) :=
  (Fintype.bijective_iff_injective_and_card (occ n parent hparent flip)).mpr
    ⟨occ_injective n parent hparent flip, by
      rw [Fintype.card_fin, card_orientedTree_edges_type]⟩

/-- **The edge dictionary of the normal-form target.** -/
noncomputable def occEquiv : Fin n ≃ (orientedTree n parent hparent flip).edges :=
  Equiv.ofBijective _ (occ_bijective n parent hparent flip)

@[simp] theorem occEquiv_apply (i : Fin n) :
    occEquiv n parent hparent flip i = occ n parent hparent flip i := rfl

end Family

/-! ## 2. Ranking a finite set by an injective key -/

/-- Counting the strictly smaller keys turns an injective `ℕ`-valued key on a
finite type into a rank function: injective, bounded by the cardinality,
strictly monotone in the key, and vanishing at the key-minimal element. -/
theorem exists_rank_of_key {V : Type} [Fintype V] [DecidableEq V] (key : V → ℕ)
    (hinj : Function.Injective key) (root : V)
    (hroot : ∀ w, w ≠ root → key root < key w) :
    ∃ rk : V → ℕ, (∀ v, rk v < Fintype.card V) ∧ Function.Injective rk ∧
      (∀ u v, key u < key v → rk u < rk v) ∧ rk root = 0 := by
  classical
  refine ⟨fun v => (Finset.univ.filter fun w => key w < key v).card, ?_, ?_, ?_, ?_⟩
  · intro v
    have hlt : (Finset.univ.filter fun w => key w < key v).card
        < (Finset.univ : Finset V).card := by
      refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
      have hv := hsub (Finset.mem_univ v)
      simp only [Finset.mem_filter] at hv
      exact absurd hv.2 (lt_irrefl _)
    simpa [Finset.card_univ] using hlt
  · intro u v hEq
    by_contra hne
    rcases lt_trichotomy (key u) (key v) with h | h | h
    · exact absurd hEq (Nat.ne_of_lt (by
        refine Finset.card_lt_card ⟨?_, fun hsub => ?_⟩
        · intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          omega
        · have hu := hsub (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
          simp only [Finset.mem_filter] at hu
          exact absurd hu.2 (lt_irrefl _)))
    · exact hne (hinj h)
    · exact absurd hEq.symm (Nat.ne_of_lt (by
        refine Finset.card_lt_card ⟨?_, fun hsub => ?_⟩
        · intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          omega
        · have hv := hsub (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
          simp only [Finset.mem_filter] at hv
          exact absurd hv.2 (lt_irrefl _)))
  · intro u v huv
    refine Finset.card_lt_card ⟨?_, fun hsub => ?_⟩
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      omega
    · have hu := hsub (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact huv)
      simp only [Finset.mem_filter] at hu
      exact absurd hu.2 (lt_irrefl _)
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w _
    by_cases hw : w = root
    · subst hw
      exact lt_irrefl _
    · exact Nat.not_lt.mpr (hroot w hw).le

/-! ## 3. The spanning enumeration of a connected `CFGraph` -/

/-- Reachability from `root` in at most `k` edge steps. -/
def ReachIn (G : CFGraph.{0}) (root : G.V) : ℕ → G.V → Prop
  | 0 => fun v => v = root
  | k + 1 => fun v => ReachIn G root k v ∨ ∃ w, ReachIn G root k w ∧ 0 < num_edges G w v

/-- In a connected graph every vertex is reachable from every root.  This is the
only use of `graph_connected`: the reachable set is closed under edges and
contains the root, so the no-separation condition forces it to be everything. -/
theorem exists_reachIn {G : CFGraph.{0}} (hConn : graph_connected G) (root v : G.V) :
    ∃ k, ReachIn G root k v := by
  classical
  by_contra hv
  obtain ⟨a, haS, b, hbS, hab⟩ :=
    hConn (Finset.univ.filter fun w => ∃ k, ReachIn G root k w)
      ⟨root, v, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨0, rfl⟩, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hv⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at haS hbS
  obtain ⟨k, hk⟩ := haS
  exact hbS ⟨k + 1, Or.inr ⟨a, hk, hab⟩⟩

/-- **The depth function of a connected graph.**  Every vertex but the root has
a neighbour of strictly smaller depth: the distance to the root, produced
without any path type. -/
theorem exists_depth {G : CFGraph.{0}} (hConn : graph_connected G) (root : G.V) :
    ∃ depth : G.V → ℕ, (∀ v, depth v = 0 ↔ v = root) ∧
      ∀ v, v ≠ root → ∃ w, 0 < num_edges G w v ∧ depth w < depth v := by
  classical
  refine ⟨fun v => Nat.find (exists_reachIn hConn root v), fun v => ⟨?_, ?_⟩, ?_⟩
  · intro hv
    have hv' : Nat.find (exists_reachIn hConn root v) = 0 := hv
    have hspec := Nat.find_spec (exists_reachIn hConn root v)
    rw [hv'] at hspec
    exact hspec
  · intro hv
    show Nat.find (exists_reachIn hConn root v) = 0
    refine Nat.le_zero.mp (Nat.find_le ?_)
    show ReachIn G root 0 v
    exact hv
  · intro v hv
    have hspec := Nat.find_spec (exists_reachIn hConn root v)
    obtain ⟨j, hj⟩ : ∃ j, Nat.find (exists_reachIn hConn root v) = j + 1 := by
      rcases Nat.eq_zero_or_pos (Nat.find (exists_reachIn hConn root v)) with h | h
      · rw [h] at hspec
        exact absurd hspec hv
      · exact ⟨Nat.find (exists_reachIn hConn root v) - 1, by omega⟩
    rw [hj] at hspec
    have hmin := Nat.find_min (exists_reachIn hConn root v) (m := j) (by omega)
    rcases hspec with hspec | ⟨w, hw, hedge⟩
    · exact absurd hspec hmin
    · refine ⟨w, hedge, ?_⟩
      have hle : Nat.find (exists_reachIn hConn root w) ≤ j :=
        Nat.find_le (h := exists_reachIn hConn root w) hw
      show Nat.find (exists_reachIn hConn root w) <
        Nat.find (exists_reachIn hConn root v)
      omega

/-- **The breadth-first vertex labelling.**  A connected graph on `n + 1`
vertices is numbered `0, …, n` so that every vertex but `0` has a neighbour with
a strictly smaller number.  Depth to the root gives the primary order and an
arbitrary enumeration breaks ties. -/
theorem exists_rankEquiv {G : CFGraph.{0}} (hConn : graph_connected G) (n : ℕ)
    (hCard : Fintype.card G.V = n + 1) :
    ∃ rank : G.V ≃ Fin (n + 1), ∀ i : Fin n,
      ∃ w : G.V, (rank w).val ≤ i.val ∧ 0 < num_edges G w (rank.symm i.succ) := by
  classical
  obtain ⟨root⟩ := (inferInstance : Nonempty G.V)
  obtain ⟨depth, hzero, hstep⟩ := exists_depth hConn root
  obtain ⟨key, hkeyinj, hkeymono⟩ : ∃ key : G.V → ℕ, Function.Injective key ∧
      ∀ u v, depth u < depth v → key u < key v := by
    have hidxlt : ∀ v : G.V, (Fintype.equivFin G.V v).val < n + 1 := by
      intro v
      have hlt := (Fintype.equivFin G.V v).isLt
      omega
    have hmono : ∀ u v : G.V, depth u < depth v →
        (Fintype.equivFin G.V u).val + depth u * (n + 1)
          < (Fintype.equivFin G.V v).val + depth v * (n + 1) := by
      intro u v huv
      have hstepMul : (depth u + 1) * (n + 1) ≤ depth v * (n + 1) :=
        Nat.mul_le_mul_right _ huv
      have hexpand : (depth u + 1) * (n + 1) = depth u * (n + 1) + (n + 1) := by ring
      have hbound := hidxlt u
      omega
    refine ⟨fun v => (Fintype.equivFin G.V v).val + depth v * (n + 1), ?_, hmono⟩
    intro a b hab
    have hab' : (Fintype.equivFin G.V a).val + depth a * (n + 1)
        = (Fintype.equivFin G.V b).val + depth b * (n + 1) := hab
    have hdepth : depth a = depth b := by
      rcases lt_trichotomy (depth a) (depth b) with h | h | h
      · exact absurd hab' (Nat.ne_of_lt (hmono a b h))
      · exact h
      · exact absurd hab'.symm (Nat.ne_of_lt (hmono b a h))
    rw [hdepth] at hab'
    exact (Fintype.equivFin G.V).injective (Fin.ext (by omega))
  have hkeyroot : ∀ w, w ≠ root → key root < key w := by
    intro w hw
    refine hkeymono _ _ ?_
    rw [(hzero root).mpr rfl]
    exact Nat.pos_of_ne_zero fun h => hw ((hzero w).mp h)
  obtain ⟨rk, hrkbound, hrkinj, hrkmono, hrkroot⟩ :=
    exists_rank_of_key key hkeyinj root hkeyroot
  have hrklt : ∀ v, rk v < n + 1 := by
    intro v
    have hb := hrkbound v
    rw [hCard] at hb
    exact hb
  have hrfinj : Function.Injective (fun v : G.V => (⟨rk v, hrklt v⟩ : Fin (n + 1))) := by
    intro a b hab
    exact hrkinj (congrArg Fin.val hab)
  have hrfbij : Function.Bijective (fun v : G.V => (⟨rk v, hrklt v⟩ : Fin (n + 1))) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hrfinj, by rw [hCard, Fintype.card_fin]⟩
  refine ⟨Equiv.ofBijective _ hrfbij, ?_⟩
  intro i
  have hrankv : rk ((Equiv.ofBijective _ hrfbij).symm i.succ) = i.val + 1 :=
    congrArg Fin.val
      ((Equiv.ofBijective _ hrfbij).apply_symm_apply i.succ)
  have hvroot : (Equiv.ofBijective _ hrfbij).symm i.succ ≠ root := by
    intro h
    rw [h, hrkroot] at hrankv
    omega
  obtain ⟨w, hedge, hdlt⟩ := hstep _ hvroot
  refine ⟨w, ?_, hedge⟩
  have hlt := hrkmono w _ (hkeymono _ _ hdlt)
  show rk w ≤ i.val
  omega

/-! ## 4. The normal form -/

/-- A positive edge multiplicity is witnessed by an actual occurrence, stored in
one of the two orders. -/
theorem exists_occurrence {G : CFGraph.{0}} {v u : G.V} (h : 0 < num_edges G v u) :
    ∃ e : G.edges, ((e : G.V × G.V) = (v, u) ∨ (e : G.V × G.V) = (u, v)) := by
  obtain ⟨p, hp⟩ := Multiset.card_pos_iff_exists_mem.mp h
  obtain ⟨hmem, hshape⟩ := Multiset.mem_filter.mp hp
  exact ⟨⟨p, ⟨0, Multiset.count_pos.mpr hmem⟩⟩, hshape⟩

/-- **The normal form of a target.**  A vertex numbering, a parent map pointing
to strictly smaller numbers, an orientation bit for every tree edge, and --
this is the field the transport machinery needs and a `Utilities.CFGraphIso`
cannot supply -- the bijection of **edge occurrences** onto the occurrences of
`orientedTree`, respecting both stored endpoints. -/
structure NormalForm (G : CFGraph.{0}) (n : ℕ) where
  /-- The parent of tree edge `i`, as a vertex number. -/
  parent : Fin n → Fin (n + 1)
  /-- Parents point to strictly smaller numbers. -/
  parent_le : ∀ i : Fin n, (parent i).val ≤ i.val
  /-- How the occurrence of tree edge `i` is stored. -/
  flip : Fin n → Bool
  /-- The vertex numbering. -/
  vertexEquiv : G.V ≃ (orientedTree n parent parent_le flip).V
  /-- **The occurrence bijection, as data.** -/
  edgeEquiv : G.edges ≃ (orientedTree n parent parent_le flip).edges
  /-- It respects the first stored endpoint. -/
  ends_fst : ∀ e : G.edges,
    ((edgeEquiv e : (orientedTree n parent parent_le flip).edges) :
        (orientedTree n parent parent_le flip).V ×
          (orientedTree n parent parent_le flip).V).1
      = vertexEquiv ((e : G.V × G.V)).1
  /-- It respects the second stored endpoint. -/
  ends_snd : ∀ e : G.edges,
    ((edgeEquiv e : (orientedTree n parent parent_le flip).edges) :
        (orientedTree n parent parent_le flip).V ×
          (orientedTree n parent parent_le flip).V).2
      = vertexEquiv ((e : G.V × G.V)).2

namespace NormalForm

variable {G : CFGraph.{0}} {n : ℕ}

/-- The normal-form target of a normal form. -/
def target (nf : NormalForm G n) : CFGraph.{0} :=
  orientedTree n nf.parent nf.parent_le nf.flip

theorem target_connected (nf : NormalForm G n) : graph_connected nf.target :=
  orientedTree_connected n nf.parent nf.parent_le nf.flip

theorem target_genus (nf : NormalForm G n) : genus nf.target = 0 :=
  orientedTree_genus n nf.parent nf.parent_le nf.flip

theorem card_edges_target (nf : NormalForm G n) :
    Multiset.card nf.target.edges = n :=
  card_edges_orientedTree n nf.parent nf.parent_le nf.flip

theorem card_vertices_target (nf : NormalForm G n) :
    Fintype.card nf.target.V = n + 1 :=
  card_vertices_orientedTree n nf.parent nf.parent_le nf.flip

end NormalForm

/-- **Existence of the normal form.**  Every connected genus-zero `CFGraph` with
`n` edge occurrences is, occurrence by occurrence, an `orientedTree` on
`Fin (n + 1)` for a parent map pointing to strictly smaller numbers.  Genus zero
enters exactly once: it makes the `n` chosen parent occurrences exhaust the
occurrence multiset. -/
theorem exists_normalForm (G : CFGraph.{0}) (hConn : graph_connected G)
    (hGenus : genus G = 0) (n : ℕ) (hn : Multiset.card G.edges = n) :
    Nonempty (NormalForm G n) := by
  classical
  subst hn
  have hCard : Fintype.card G.V = Multiset.card G.edges + 1 := by
    have hg : (Multiset.card G.edges : ℤ) - (Fintype.card G.V : ℤ) + 1 = 0 := hGenus
    omega
  obtain ⟨rank, hrank⟩ := exists_rankEquiv hConn (Multiset.card G.edges) hCard
  choose w hwle hwedge using hrank
  have hne : ∀ i : Fin (Multiset.card G.edges), w i ≠ rank.symm i.succ := by
    intro i hEq
    have hval : (rank (w i)).val = i.val + 1 := by
      rw [hEq, Equiv.apply_symm_apply]
      rfl
    have := hwle i
    omega
  have hocc : ∀ i : Fin (Multiset.card G.edges), ∃ eb : G.edges × Bool,
      (eb.1 : G.V × G.V)
        = (if eb.2 then (rank.symm i.succ, w i) else (w i, rank.symm i.succ)) := by
    intro i
    obtain ⟨e, he | he⟩ := exists_occurrence (hwedge i)
    · exact ⟨(e, false), by simpa using he⟩
    · exact ⟨(e, true), by simpa using he⟩
  choose eb heb using hocc
  have hEnds : ∀ i : Fin (Multiset.card G.edges),
      orientedEdge (Multiset.card G.edges) (fun j => rank (w j)) (fun j => (eb j).2) i
        = (rank (((eb i).1 : G.V × G.V)).1, rank (((eb i).1 : G.V × G.V)).2) := by
    intro i
    rw [heb i]
    unfold orientedEdge
    by_cases hflip : (eb i).2 = true
    · simp [hflip, Equiv.apply_symm_apply]
    · simp only [Bool.not_eq_true] at hflip
      simp [hflip, Equiv.apply_symm_apply]
  have hInj : Function.Injective (fun i => (eb i).1) := by
    intro i j hEq
    have hEq' : (eb i).1 = (eb j).1 := hEq
    refine orientedEdge_injective (Multiset.card G.edges) (fun j => rank (w j))
      (fun j => hwle j) (fun j => (eb j).2) ?_
    rw [hEnds i, hEnds j, hEq']
  have hBij : Function.Bijective (fun i => (eb i).1) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hInj, by rw [Fintype.card_fin, Multiset.card_coe]⟩
  refine ⟨{ parent := fun j => rank (w j)
            parent_le := fun j => hwle j
            flip := fun j => (eb j).2
            vertexEquiv := rank
            edgeEquiv := (Equiv.ofBijective _ hBij).symm.trans
              (occEquiv (Multiset.card G.edges) (fun j => rank (w j))
                (fun j => hwle j) (fun j => (eb j).2))
            ends_fst := ?_
            ends_snd := ?_ }⟩
  · intro e
    have hback : (eb ((Equiv.ofBijective _ hBij).symm e)).1 = e :=
      (Equiv.ofBijective _ hBij).apply_symm_apply e
    have h := hEnds ((Equiv.ofBijective _ hBij).symm e)
    rw [hback] at h
    show (orientedEdge (Multiset.card G.edges) (fun j => rank (w j))
      (fun j => (eb j).2) ((Equiv.ofBijective _ hBij).symm e)).1 = _
    rw [h]
    rfl
  · intro e
    have hback : (eb ((Equiv.ofBijective _ hBij).symm e)).1 = e :=
      (Equiv.ofBijective _ hBij).apply_symm_apply e
    have h := hEnds ((Equiv.ofBijective _ hBij).symm e)
    rw [hback] at h
    show (orientedEdge (Multiset.card G.edges) (fun j => rank (w j))
      (fun j => (eb j).2) ((Equiv.ofBijective _ hBij).symm e)).2 = _
    rw [h]
    rfl

/-! ## 5. Transport of a gluing datum onto the normal-form target -/

section Pushforward

variable {target₁ target₂ : CFGraph} {degree : ℕ}

/-- **The datum pushed onto the other target.**  Both partition assignments are
read backwards through the two bijections; the refinement conditions survive
because the bijections respect the stored endpoints. -/
def pushforward (data : GluingDatum target₁ degree)
    (vertexEquiv : target₁.V ≃ target₂.V) (edgeEquiv : target₁.edges ≃ target₂.edges)
    (hfst : ∀ e : target₁.edges,
      ((edgeEquiv e : target₂.edges) : target₂.V × target₂.V).1
        = vertexEquiv ((e : target₁.V × target₁.V)).1)
    (hsnd : ∀ e : target₁.edges,
      ((edgeEquiv e : target₂.edges) : target₂.V × target₂.V).2
        = vertexEquiv ((e : target₁.V × target₁.V)).2) :
    GluingDatum target₂ degree where
  degree_pos := data.degree_pos
  vertexPartition vertex := data.vertexPartition (vertexEquiv.symm vertex)
  edgePartition edge := data.edgePartition (edgeEquiv.symm edge)
  refines_left edge := by
    have h := hfst (edgeEquiv.symm edge)
    rw [Equiv.apply_symm_apply] at h
    have h2 : vertexEquiv.symm ((edge : target₂.V × target₂.V)).1
        = ((edgeEquiv.symm edge : target₁.edges) : target₁.V × target₁.V).1 := by
      rw [h, Equiv.symm_apply_apply]
    show (data.edgePartition (edgeEquiv.symm edge)).Refines
      (data.vertexPartition (vertexEquiv.symm ((edge : target₂.V × target₂.V)).1))
    rw [h2]
    exact data.refines_left (edgeEquiv.symm edge)
  refines_right edge := by
    have h := hsnd (edgeEquiv.symm edge)
    rw [Equiv.apply_symm_apply] at h
    have h2 : vertexEquiv.symm ((edge : target₂.V × target₂.V)).2
        = ((edgeEquiv.symm edge : target₁.edges) : target₁.V × target₁.V).2 := by
      rw [h, Equiv.symm_apply_apply]
    show (data.edgePartition (edgeEquiv.symm edge)).Refines
      (data.vertexPartition (vertexEquiv.symm ((edge : target₂.V × target₂.V)).2))
    rw [h2]
    exact data.refines_right (edgeEquiv.symm edge)

/-- **The isomorphism of gluing data, with the occurrence bijection as data.**
Every sheet permutation is the identity, so the compatibility conditions of
`Count.Transport.DatumIso` hold by reflexivity; the whole content is the
prescribed pair `(vertexEquiv, edgeEquiv)`. -/
def datumIso (data : GluingDatum target₁ degree)
    (vertexEquiv : target₁.V ≃ target₂.V) (edgeEquiv : target₁.edges ≃ target₂.edges)
    (hfst : ∀ e : target₁.edges,
      ((edgeEquiv e : target₂.edges) : target₂.V × target₂.V).1
        = vertexEquiv ((e : target₁.V × target₁.V)).1)
    (hsnd : ∀ e : target₁.edges,
      ((edgeEquiv e : target₂.edges) : target₂.V × target₂.V).2
        = vertexEquiv ((e : target₁.V × target₁.V)).2) :
    DatumIso data (pushforward data vertexEquiv edgeEquiv hfst hsnd) where
  targetVertex := vertexEquiv
  targetEdge := edgeEquiv
  ends_fst := hfst
  ends_snd := hsnd
  vertexPerm _ := Equiv.refl _
  edgePerm _ := Equiv.refl _
  vertexPartition vertex := by
    show data.vertexPartition (vertexEquiv.symm (vertexEquiv vertex))
      = (data.vertexPartition vertex).relabel (Equiv.refl _)
    rw [Equiv.symm_apply_apply, DatumIso.relabel_refl]
  edgePartition edge := by
    show data.edgePartition (edgeEquiv.symm (edgeEquiv edge))
      = (data.edgePartition edge).relabel (Equiv.refl _)
    rw [Equiv.symm_apply_apply, DatumIso.relabel_refl]
  compatible_fst _ _ := rfl
  compatible_snd _ _ := rfl

@[simp] theorem datumIso_targetEdge (data : GluingDatum target₁ degree)
    (vertexEquiv : target₁.V ≃ target₂.V) (edgeEquiv : target₁.edges ≃ target₂.edges)
    (hfst : ∀ e : target₁.edges,
      ((edgeEquiv e : target₂.edges) : target₂.V × target₂.V).1
        = vertexEquiv ((e : target₁.V × target₁.V)).1)
    (hsnd : ∀ e : target₁.edges,
      ((edgeEquiv e : target₂.edges) : target₂.V × target₂.V).2
        = vertexEquiv ((e : target₁.V × target₁.V)).2) :
    (datumIso data vertexEquiv edgeEquiv hfst hsnd).targetEdge = edgeEquiv := rfl

end Pushforward

namespace NormalForm

variable {G : CFGraph.{0}} {n : ℕ} {degree : ℕ}

/-- The datum moved onto the normal-form target. -/
def pushDatum (nf : NormalForm G n) (data : GluingDatum G degree) :
    GluingDatum nf.target degree :=
  pushforward data nf.vertexEquiv nf.edgeEquiv nf.ends_fst nf.ends_snd

/-- **The prescribed isomorphism of gluing data onto the normal form.**  Its
`targetEdge` is exactly the normal form's occurrence bijection. -/
def datumIso (nf : NormalForm G n) (data : GluingDatum G degree) :
    DatumIso data (nf.pushDatum data) :=
  TargetNormalForm.datumIso data nf.vertexEquiv nf.edgeEquiv nf.ends_fst nf.ends_snd

@[simp] theorem datumIso_targetEdge (nf : NormalForm G n) (data : GluingDatum G degree) :
    (nf.datumIso data).targetEdge = nf.edgeEquiv := rfl

@[simp] theorem datumIso_targetVertex (nf : NormalForm G n) (data : GluingDatum G degree) :
    (nf.datumIso data).targetVertex = nf.vertexEquiv := rfl

end NormalForm

/-! ## 6. Non-vacuity -/

/-- **The caterpillar-of-loops target tree is already in normal form.**  Its
parent map is `CaterpillarTree.catParent`, every occurrence is stored
parent-first, and both bijections are the identity. -/
def catNormalForm (m : ℕ) : NormalForm (CaterpillarTree.catTree m) (6 * m + 3) where
  parent := CaterpillarTree.catParent m
  parent_le := CaterpillarTree.catParent_le m
  flip := fun _ => false
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.refl _
  ends_fst _ := rfl
  ends_snd _ := rfl

theorem catNormalForm_target (m : ℕ) :
    (catNormalForm m).target = CaterpillarTree.catTree m := rfl

/-! ### The orientation bit is not a decoration -/

/-- Two occurrences into a common head, on three vertices: connected, genus
zero, and a tree -- but not a `TreeFamily.rootedTree`, because a rooted tree
stores its occurrences parent-first and no two of them then share a head. -/
def inPath : CFGraph.{0} where
  V := Fin 3
  edges := Multiset.ofList [((0 : Fin 3), (1 : Fin 3)), ((2 : Fin 3), (1 : Fin 3))]
  loopless := by decide

theorem inPath_connected : graph_connected inPath :=
  (graphConnectedCheck_eq_true_iff inPath).mp (by decide)

theorem inPath_genus : genus inPath = 0 := by decide

theorem card_edges_inPath : Multiset.card inPath.edges = 2 := rfl

/-- The first occurrence of `inPath`. -/
def inPathFirst : inPath.edges := ⟨((0 : Fin 3), (1 : Fin 3)), ⟨0, by decide⟩⟩

/-- The second occurrence of `inPath`. -/
def inPathSecond : inPath.edges := ⟨((2 : Fin 3), (1 : Fin 3)), ⟨0, by decide⟩⟩

/-- **The obstruction.**  In every normal form of `inPath` some occurrence is
stored child-first.  The two occurrences share their second endpoint, whereas in
an `orientedTree` with `flip = false` the second endpoints are the pairwise
distinct successors `i.succ`.  Hence "isomorphic to a
`TreeFamily.rootedTree`" cannot be read with `DatumIso`'s endpoint equations,
and the orientation bit is forced. -/
theorem inPath_exists_flip (nf : NormalForm inPath 2) : ∃ i, nf.flip i = true := by
  by_contra hno
  have hno' : ∀ i, nf.flip i = false := by
    intro i
    cases h : nf.flip i with
    | false => rfl
    | true => exact absurd ⟨i, h⟩ hno
  have hdistinct : inPathFirst ≠ inPathSecond := by
    intro hEq
    exact absurd (congrArg Sigma.fst hEq) (by decide)
  set eq2 := occEquiv 2 nf.parent nf.parent_le nf.flip with heq2
  set a := eq2.symm (nf.edgeEquiv inPathFirst) with ha
  set b := eq2.symm (nf.edgeEquiv inPathSecond) with hb
  have hab : a ≠ b := by
    rw [ha, hb]
    exact fun h => hdistinct (nf.edgeEquiv.injective (eq2.symm.injective h))
  have hsucc : ∀ (e : inPath.edges) (i : Fin 2),
      eq2 i = nf.edgeEquiv e →
        (i.succ : Fin 3) = nf.vertexEquiv ((e : inPath.V × inPath.V)).2 := by
    intro e i hi
    have hends := nf.ends_snd e
    rw [← hi] at hends
    rw [← hends, heq2, occEquiv_apply, occ_coe]
    unfold orientedEdge
    simp [hno' i]
  have h1 := hsucc inPathFirst a (by rw [ha, Equiv.apply_symm_apply])
  have h2 := hsucc inPathSecond b (by rw [hb, Equiv.apply_symm_apply])
  have hsame : ((inPathFirst : inPath.V × inPath.V)).2
      = ((inPathSecond : inPath.V × inPath.V)).2 := rfl
  rw [hsame, ← h2] at h1
  exact hab (Fin.succ_injective 2 h1)

end DraismaVargas.Count.TargetNormalForm
