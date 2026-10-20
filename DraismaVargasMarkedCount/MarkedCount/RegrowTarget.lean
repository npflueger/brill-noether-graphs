module

public import GenusSixExistence.BrillNoetherRank.Tripod.Gluing

@[expose] public section

/-!
# Regrowth, part 1: the regrown target

Given a target `T` and `k` target vertices `x : Fin k → T.V` (the images of the marks),
`regrowTarget T x` attaches at every `x j` a path `x j — mid j — tip j` of two new edges, the
**bridge** edge `t_b j` and the **leaf** edge `t_l j`.

Per mark this is the public tripod's `Gluing.leafTarget` applied twice (attach a leaf at `x j`,
then at the new leaf); for `k` marks at once it is built in one step, so that the vertex type is
`T.V ⊕ (Fin k ⊕ Fin k)` (`oldV`, `midV`, `tipV`) and the occurrence type is
`(Fin k ⊕ Fin k) ⊕ T.edges` (`occEquiv`: bridges, leaves, old edges), with no recursion on `k`.

Proved here: the endpoints of every occurrence, the incident target edges at every vertex
(as sums), connectedness, genus and edge count.
-/

namespace DraismaVargas.Count.MarkedCount.Regrow

noncomputable section

open DraismaVargas.Infrastructure

variable {T : CFGraph.{0}} {k : ℕ}

/-- The occurrences of the regrown target: `inl (inl j)` is the bridge edge `t_b j`,
`inl (inr j)` the leaf edge `t_l j`, `inr e` the old edge `e`. -/
abbrev Occ (T : CFGraph.{0}) (k : ℕ) := (Fin k ⊕ Fin k) ⊕ T.edges

instance instDecidableEqOcc : DecidableEq (Occ T k) := Classical.decEq _

/-- The vertices of the regrown target: `inl v` old, `inr (inl j)` the middle vertex `u'_j`,
`inr (inr j)` the tip `v_{C,j}`. -/
abbrev Vtx (T : CFGraph.{0}) (k : ℕ) := T.V ⊕ (Fin k ⊕ Fin k)

/-- The endpoints of an occurrence. -/
def occEnds (x : Fin k → T.V) : Occ T k → Vtx T k × Vtx T k
  | .inl (.inl j) => (.inl (x j), .inr (.inl j))
  | .inl (.inr j) => (.inr (.inl j), .inr (.inr j))
  | .inr e => (.inl (e : T.V × T.V).1, .inl (e : T.V × T.V).2)

theorem occEnds_ne (x : Fin k → T.V) (o : Occ T k) : (occEnds x o).1 ≠ (occEnds x o).2 := by
  rcases o with (j | j) | e
  · simp [occEnds]
  · simp [occEnds]
  · simp only [occEnds, ne_eq, Sum.inl.injEq]
    exact GenusSixExistence.Tripod.Gluing.fst_ne_snd e

/-- **The regrown target**: a path of two new edges at every `x j`. -/
def regrowTarget (T : CFGraph.{0}) (x : Fin k → T.V) : CFGraph.{0} where
  V := Vtx T k
  instNonempty := ⟨.inl (Classical.choice T.instNonempty)⟩
  edges := (Finset.univ : Finset (Occ T k)).val.map (occEnds x)
  loopless := by
    intro v hmem
    obtain ⟨o, -, ho⟩ := Multiset.mem_map.mp hmem
    exact occEnds_ne x o ((congrArg Prod.fst ho).trans (congrArg Prod.snd ho).symm)

variable (x : Fin k → T.V)

/-- Enumerating `Finset.univ` of a finite type neither loses nor duplicates an element. -/
def univEnumeration (α : Type*) [Fintype α] [DecidableEq α] :
    Multiset.ToType ((Finset.univ : Finset α).val) ≃ α where
  toFun item := item.1
  invFun a := ⟨a, ⟨0, by
    rw [Multiset.count_eq_one_of_mem Finset.univ.nodup (by simp)]
    omega⟩⟩
  left_inv := by
    rintro ⟨a, index⟩
    have hCount : Multiset.count a (Finset.univ : Finset α).val = 1 :=
      Multiset.count_eq_one_of_mem Finset.univ.nodup (by simp)
    have hSub : Subsingleton (Fin (Multiset.count a (Finset.univ : Finset α).val)) := by
      rw [hCount]; infer_instance
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (hSub.elim _ _)
  right_inv _ := rfl

/-- **The occurrence dictionary** of the regrown target. -/
def occEquiv : Occ T k ≃ (regrowTarget T x).edges :=
  (univEnumeration (Occ T k)).symm.trans
    (Multiset.mapEquiv (Finset.univ : Finset (Occ T k)).val (occEnds x))

@[simp] theorem occEquiv_ends (o : Occ T k) :
    ((occEquiv x o : (regrowTarget T x).edges) :
      (regrowTarget T x).V × (regrowTarget T x).V) = occEnds x o := by
  unfold occEquiv
  exact Multiset.mapEquiv_apply _ _ _

/-! ## Names -/

/-- An old vertex. -/
def oldV (v : T.V) : (regrowTarget T x).V := Sum.inl v

/-- The middle vertex `u'_j`. -/
def midV (j : Fin k) : (regrowTarget T x).V := Sum.inr (Sum.inl j)

/-- The tip `v_{C,j}`. -/
def tipV (j : Fin k) : (regrowTarget T x).V := Sum.inr (Sum.inr j)

/-- An old edge. -/
def oldE (e : T.edges) : (regrowTarget T x).edges := occEquiv x (.inr e)

/-- The bridge edge `t_b j`, from `x j` to `mid j`. -/
def bridgeE (j : Fin k) : (regrowTarget T x).edges := occEquiv x (.inl (.inl j))

/-- The leaf edge `t_l j`, from `mid j` to `tip j`. -/
def leafE (j : Fin k) : (regrowTarget T x).edges := occEquiv x (.inl (.inr j))

@[simp] theorem oldE_ends (e : T.edges) :
    ((oldE x e : (regrowTarget T x).edges) : (regrowTarget T x).V × (regrowTarget T x).V) =
      (oldV x (e : T.V × T.V).1, oldV x (e : T.V × T.V).2) := occEquiv_ends x _

@[simp] theorem bridgeE_ends (j : Fin k) :
    ((bridgeE x j : (regrowTarget T x).edges) : (regrowTarget T x).V × (regrowTarget T x).V) =
      (oldV x (x j), midV x j) := occEquiv_ends x _

@[simp] theorem leafE_ends (j : Fin k) :
    ((leafE x j : (regrowTarget T x).edges) : (regrowTarget T x).V × (regrowTarget T x).V) =
      (midV x j, tipV x j) := occEquiv_ends x _

theorem oldV_injective : Function.Injective (oldV x) := Sum.inl_injective
theorem midV_injective : Function.Injective (midV x) := fun _ _ h ↦
  Sum.inl_injective (Sum.inr_injective h)
theorem tipV_injective : Function.Injective (tipV x) := fun _ _ h ↦
  Sum.inr_injective (Sum.inr_injective h)

@[simp] theorem oldV_inj {v w : T.V} : oldV x v = oldV x w ↔ v = w := (oldV_injective x).eq_iff
@[simp] theorem midV_inj {i j : Fin k} : midV x i = midV x j ↔ i = j := (midV_injective x).eq_iff
@[simp] theorem tipV_inj {i j : Fin k} : tipV x i = tipV x j ↔ i = j := (tipV_injective x).eq_iff
@[simp] theorem midV_ne_oldV (j : Fin k) (v : T.V) : midV x j ≠ oldV x v := Sum.inr_ne_inl
@[simp] theorem oldV_ne_midV (j : Fin k) (v : T.V) : oldV x v ≠ midV x j := Sum.inl_ne_inr
@[simp] theorem tipV_ne_oldV (j : Fin k) (v : T.V) : tipV x j ≠ oldV x v := Sum.inr_ne_inl
@[simp] theorem oldV_ne_tipV (j : Fin k) (v : T.V) : oldV x v ≠ tipV x j := Sum.inl_ne_inr
@[simp] theorem midV_ne_tipV (i j : Fin k) : midV x i ≠ tipV x j := by intro h; cases h
@[simp] theorem tipV_ne_midV (i j : Fin k) : tipV x i ≠ midV x j := by intro h; cases h

/-- Every vertex is old, a middle vertex or a tip. -/
theorem vertex_cases (v : (regrowTarget T x).V) :
    (∃ w, v = oldV x w) ∨ (∃ j, v = midV x j) ∨ (∃ j, v = tipV x j) := by
  rcases v with w | j | j
  · exact Or.inl ⟨w, rfl⟩
  · exact Or.inr (Or.inl ⟨j, rfl⟩)
  · exact Or.inr (Or.inr ⟨j, rfl⟩)

/-- Every occurrence is old, a bridge or a leaf edge. -/
theorem edge_cases (e : (regrowTarget T x).edges) :
    (∃ f, e = oldE x f) ∨ (∃ j, e = bridgeE x j) ∨ (∃ j, e = leafE x j) := by
  obtain ⟨o, rfl⟩ := (occEquiv x).surjective e
  rcases o with (j | j) | f
  · exact Or.inr (Or.inl ⟨j, rfl⟩)
  · exact Or.inr (Or.inr ⟨j, rfl⟩)
  · exact Or.inl ⟨f, rfl⟩

theorem oldE_injective : Function.Injective (oldE x) := fun _ _ h ↦ by
  simpa [oldE] using (occEquiv x).injective h
theorem bridgeE_injective : Function.Injective (bridgeE x) := fun _ _ h ↦ by
  simpa [bridgeE] using (occEquiv x).injective h
theorem leafE_injective : Function.Injective (leafE x) := fun _ _ h ↦ by
  simpa [leafE] using (occEquiv x).injective h

@[simp] theorem oldE_inj {e f : T.edges} : oldE x e = oldE x f ↔ e = f :=
  (oldE_injective x).eq_iff
@[simp] theorem bridgeE_inj {i j : Fin k} : bridgeE x i = bridgeE x j ↔ i = j :=
  (bridgeE_injective x).eq_iff
@[simp] theorem leafE_inj {i j : Fin k} : leafE x i = leafE x j ↔ i = j :=
  (leafE_injective x).eq_iff
@[simp] theorem oldE_ne_bridgeE (e : T.edges) (j : Fin k) : oldE x e ≠ bridgeE x j := fun h ↦ by
  simpa [oldE, bridgeE] using (occEquiv x).injective h
@[simp] theorem bridgeE_ne_oldE (e : T.edges) (j : Fin k) : bridgeE x j ≠ oldE x e :=
  fun h ↦ oldE_ne_bridgeE x e j h.symm
@[simp] theorem oldE_ne_leafE (e : T.edges) (j : Fin k) : oldE x e ≠ leafE x j := fun h ↦ by
  simpa [oldE, leafE] using (occEquiv x).injective h
@[simp] theorem leafE_ne_oldE (e : T.edges) (j : Fin k) : leafE x j ≠ oldE x e :=
  fun h ↦ oldE_ne_leafE x e j h.symm
@[simp] theorem bridgeE_ne_leafE (i j : Fin k) : bridgeE x i ≠ leafE x j := fun h ↦ by
  simpa [bridgeE, leafE] using (occEquiv x).injective h
@[simp] theorem leafE_ne_bridgeE (i j : Fin k) : leafE x j ≠ bridgeE x i :=
  fun h ↦ bridgeE_ne_leafE x i j h.symm

/-! ## Incident target edges -/

/-- Sums over the occurrences of the regrown target split into bridges, leaves and old edges. -/
theorem sum_edges {M : Type*} [AddCommMonoid M] (f : (regrowTarget T x).edges → M) :
    ∑ e, f e = ∑ j, f (bridgeE x j) + ∑ j, f (leafE x j) + ∑ e, f (oldE x e) := by
  rw [← (occEquiv x).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rfl

theorem incident_iff_oldV (e : (regrowTarget T x).edges) (v : T.V) :
    ((e : (regrowTarget T x).V × (regrowTarget T x).V).1 = oldV x v ∨
        (e : (regrowTarget T x).V × (regrowTarget T x).V).2 = oldV x v) ↔
      (∃ f : T.edges, e = oldE x f ∧ ((f : T.V × T.V).1 = v ∨ (f : T.V × T.V).2 = v)) ∨
        ∃ j, e = bridgeE x j ∧ x j = v := by
  rcases edge_cases x e with ⟨f, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp
  · simp [eq_comm]
  · simp

/-- **Sums over the incident target edges at an old vertex**: old incident edges and the bridges
of the marks over it. -/
theorem sum_incidentEdges_oldV {M : Type*} [AddCommMonoid M] (v : T.V)
    (f : (regrowTarget T x).edges → M) :
    ∑ e ∈ GluingDatum.incidentEdges (oldV x v), f e =
      ∑ e ∈ GluingDatum.incidentEdges v, f (oldE x e) +
        ∑ j ∈ Finset.univ.filter (fun j ↦ x j = v), f (bridgeE x j) := by
  classical
  unfold GluingDatum.incidentEdges
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, sum_edges]
  simp only [bridgeE_ends, leafE_ends, oldE_ends, oldV_inj, midV_ne_oldV, tipV_ne_oldV,
    or_false, ite_false, Finset.sum_const_zero, add_zero]
  rw [add_comm]

theorem card_incidentEdges_oldV (v : T.V) :
    (GluingDatum.incidentEdges (oldV x v)).card =
      (GluingDatum.incidentEdges v).card + (Finset.univ.filter (fun j ↦ x j = v)).card := by
  have h := sum_incidentEdges_oldV x v (fun _ ↦ (1 : ℕ))
  simpa using h

open Classical in
theorem incidentEdges_midV (j : Fin k) :
    GluingDatum.incidentEdges (midV x j) = {bridgeE x j, leafE x j} := by
  classical
  ext e
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  rcases edge_cases x e with ⟨f, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp
  · simp [eq_comm]
  · simp [eq_comm]

open Classical in
theorem incidentEdges_tipV (j : Fin k) :
    GluingDatum.incidentEdges (tipV x j) = {leafE x j} := by
  classical
  ext e
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  rcases edge_cases x e with ⟨f, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp
  · simp
  · simp [eq_comm]

open Classical in
theorem card_incidentEdges_midV (j : Fin k) :
    (GluingDatum.incidentEdges (midV x j)).card = 2 := by
  rw [incidentEdges_midV, Finset.card_pair (bridgeE_ne_leafE x j j)]

open Classical in
theorem card_incidentEdges_tipV (j : Fin k) :
    (GluingDatum.incidentEdges (tipV x j)).card = 1 := by
  rw [incidentEdges_tipV, Finset.card_singleton]

/-! ## Connectedness, genus, edge count -/

open GenusSixExistence.Tripod.Gluing in
theorem adj_of_occ (o : Occ T k) :
    (Utilities.underlyingSimpleGraph (regrowTarget T x)).Adj (occEnds x o).1 (occEnds x o).2 := by
  have hmem : occEnds x o ∈ (regrowTarget T x).edges :=
    Multiset.mem_map_of_mem _ (Finset.mem_val.mpr (Finset.mem_univ o))
  exact GraphContraction.num_edges_pos_of_mem_edges _ _ _ hmem

open GenusSixExistence.Tripod.Gluing in
/-- **The regrown target is connected** when `T` is. -/
theorem regrowTarget_connected (hT : graph_connected T) :
    graph_connected (regrowTarget T x) := by
  let H := Utilities.underlyingSimpleGraph (regrowTarget T x)
  have hOld : ∀ a b : T.V, H.Reachable (oldV x a) (oldV x b) :=
    reachable_of_targetEdges H (oldV x)
      (fun e ↦ (adj_of_occ x (.inr e)).reachable) hT
  obtain ⟨v₀⟩ := T.instNonempty
  rw [Utilities.graph_connected_iff_underlyingSimpleGraph_connected,
    SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨oldV x v₀, fun v ↦ ?_⟩
  have hMid : ∀ j, H.Reachable (oldV x v₀) (midV x j) := fun j ↦
    (hOld v₀ (x j)).trans (adj_of_occ x (.inl (.inl j))).reachable
  rcases vertex_cases x v with ⟨w, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact hOld v₀ w
  · exact hMid j
  · exact (hMid j).trans (adj_of_occ x (.inl (.inr j))).reachable

theorem card_edges_regrowTarget :
    Multiset.card (regrowTarget T x).edges = Multiset.card T.edges + (k + k) := by
  change Multiset.card ((Finset.univ : Finset (Occ T k)).val.map (occEnds x)) = _
  rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_sum,
    Fintype.card_sum, Fintype.card_fin, Multiset.card_coe]
  omega

theorem card_V_regrowTarget :
    Fintype.card (regrowTarget T x).V = Fintype.card T.V + (k + k) := by
  change Fintype.card (T.V ⊕ (Fin k ⊕ Fin k)) = _
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin]

/-- **The regrown target has the genus of `T`.** -/
theorem genus_regrowTarget : genus (regrowTarget T x) = genus T := by
  unfold genus
  rw [card_edges_regrowTarget, card_V_regrowTarget]
  push_cast
  ring

end

end DraismaVargas.Count.MarkedCount.Regrow
