module

public import Utilities.Foundations.PendantDeletion
public import Utilities.Iso.GraphContraction

@[expose] public section

/-!
# Chosen-divisor transport through pendant deletion

Unlike existential Brill--Noether transport, the map here retains every
coefficient of a chosen divisor and records the collapsed pendant edges.
The pushforward `push` carries divisors from the source graph of a fibre member to a
subdivision of the core in the endgame (step 5 of `Assembly`, via `DegeneratePlacement`).
-/

namespace DraismaVargas.Count.PendantDivisorTransport

open Utilities Utilities.Certificate
open DraismaVargas.Infrastructure.PendantDeletion

universe u v w

/-- Literal finite pushforward along a named vertex map. -/
noncomputable def push {G : CFGraph.{u}} {H : CFGraph.{v}}
    (f : G.V → H.V) (D : CFDiv G) : CFDiv H :=
  (GraphContractionCertificate.mk f).pushDiv D

theorem push_apply {G : CFGraph.{u}} {H : CFGraph.{v}}
    (f : G.V → H.V) (D : CFDiv G) (v : H.V) :
    push f D v = ∑ x : G.V, if f x = v then D x else 0 := rfl

theorem push_effective {G : CFGraph.{u}} {H : CFGraph.{v}}
    (f : G.V → H.V) {D : CFDiv G} (hD : effective D) : effective (push f D) :=
  (GraphContractionCertificate.mk f).effective_pushDiv hD

theorem push_degree {G : CFGraph.{u}} {H : CFGraph.{v}}
    (f : G.V → H.V) (D : CFDiv G) : deg (push f D) = deg D :=
  (GraphContractionCertificate.mk f).deg_pushDiv D

theorem push_comp {G : CFGraph.{u}} {H : CFGraph.{v}} {K : CFGraph.{w}}
    (f : G.V → H.V) (g : H.V → K.V) (D : CFDiv G) :
    push (g ∘ f) D = push g (push f D) := by
  classical
  funext v
  simp only [push_apply]
  have hDist : ∀ y : H.V,
      (if g y = v then ∑ x : G.V, if f x = y then D x else 0 else 0) =
        ∑ x : G.V, if g y = v ∧ f x = y then D x else 0 := by
    intro y
    by_cases h : g y = v <;> simp [h]
  simp only [hDist]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (f x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

theorem push_equiv {G : CFGraph.{u}} {H : CFGraph.{v}}
    (e : LaplacianEquiv G H) (D : CFDiv G) : push e D = e.mapDiv D := by
  classical
  funext v
  rw [push_apply, Finset.sum_eq_single (e.toEquiv.symm v)]
  · simp [LaplacianEquiv.mapDiv]
  · intro x _ hx
    have hne : e x ≠ v := by
      intro h
      exact hx (e.toEquiv.injective (h.trans (e.toEquiv.apply_symm_apply v).symm))
    simp [hne]
  · simp

theorem rank_mapDiv_eq {G : CFGraph.{u}} {H : CFGraph.{v}}
    (e : LaplacianEquiv G H) (D : CFDiv G) : rank H (e.mapDiv D) = rank G D := by
  apply le_antisymm
  · exact (e.rank_mapDiv_ge_iff D _).mp le_rfl
  · exact (e.rank_mapDiv_ge_iff D _).mpr le_rfl

/-- Collapse the one deleted leaf to its actual unique neighbor. -/
noncomputable def leafMap (G : CFGraph.{u}) (leaf : G.V)
    (hDegree : vertex_degree G leaf = 1) :
    G.V → (LeafPruning.deleteLeaf G leaf hDegree).V := by
  classical
  exact fun x ↦ if h : x = leaf then LeafPruning.rootInDeleteLeaf G leaf hDegree
    else ⟨x, h⟩

theorem leafMap_of_ne (G : CFGraph.{u}) (leaf : G.V)
    (hDegree : vertex_degree G leaf = 1) (x : G.V) (hx : x ≠ leaf) :
    leafMap G leaf hDegree x = prune G leaf hDegree hx := by
  exact dite_eq_right hx

theorem leafMap_leaf (G : CFGraph.{u}) (leaf : G.V)
    (hDegree : vertex_degree G leaf = 1) :
    leafMap G leaf hDegree leaf = LeafPruning.rootInDeleteLeaf G leaf hDegree := by
  simp [leafMap]

theorem push_leafMap (G : CFGraph.{u}) (leaf : G.V)
    (hDegree : vertex_degree G leaf = 1) (D : CFDiv G) :
    push (leafMap G leaf hDegree) D =
      LeafExtension.retractDiv (LeafPruning.deleteLeaf G leaf hDegree)
        (LeafPruning.rootInDeleteLeaf G leaf hDegree)
        ((LeafPruning.laplacianEquiv_deleteLeaf_addLeaf G leaf hDegree).mapDiv D) := by
  classical
  funext v
  rw [push_apply]
  rw [← Equiv.sum_comp (LeafPruning.vertexEquiv G leaf hDegree).symm]
  change (∑ x : Option (LeafPruning.Remaining G leaf),
    if leafMap G leaf hDegree ((LeafPruning.vertexEquiv G leaf hDegree).symm x) = v
    then D ((LeafPruning.vertexEquiv G leaf hDegree).symm x) else 0) = _
  rw [Fintype.sum_option]
  change (if leafMap G leaf hDegree leaf = v then D leaf else 0) +
    (∑ x : LeafPruning.Remaining G leaf,
      if leafMap G leaf hDegree x.val = v then D x.val else 0) = _
  rw [leafMap_leaf]
  have hSome : ∀ x : LeafPruning.Remaining G leaf,
      leafMap G leaf hDegree x.val = x := by
    intro x
    exact leafMap_of_ne G leaf hDegree x.val x.property
  have hSum : (∑ x : LeafPruning.Remaining G leaf,
      if leafMap G leaf hDegree x.val = v then D x.val else 0) = D v.val := by
    have h := Finset.sum_eq_single (s := Finset.univ)
      (f := fun x : LeafPruning.Remaining G leaf ↦
        if leafMap G leaf hDegree x.val = v then D x.val else 0) v
      (fun x _ hx ↦ ite_eq_right (fun hEq ↦ hx ((hSome x).symm.trans hEq)))
      (fun h ↦ False.elim (h (Finset.mem_univ (v : LeafPruning.Remaining G leaf))))
    exact h.trans (ite_eq_left (hSome v))
  rw [hSum]
  change (if LeafPruning.rootInDeleteLeaf G leaf hDegree = v then D leaf else 0) +
    D v.val = D v.val + if v = LeafPruning.rootInDeleteLeaf G leaf hDegree then D leaf else 0
  apply Eq.trans (add_comm _ _)
  apply congrArg (fun z : ℤ ↦ D v.val + z)
  by_cases hv : v = LeafPruning.rootInDeleteLeaf G leaf hDegree
  · exact (ite_eq_left hv.symm).trans (ite_eq_left hv).symm
  · exact (ite_eq_right (Ne.symm hv)).trans (ite_eq_right hv).symm

theorem rank_push_leafMap (G : CFGraph.{u}) (leaf : G.V)
    (hDegree : vertex_degree G leaf = 1) (D : CFDiv G) :
    rank (LeafPruning.deleteLeaf G leaf hDegree) (push (leafMap G leaf hDegree) D) =
      rank G D := by
  rw [push_leafMap, LeafExtension.rank_retractDiv, rank_mapDiv_eq]

theorem leafMap_eq_of_leaf_adjacent (G : CFGraph.{u}) (leaf : G.V)
    (hDegree : vertex_degree G leaf = 1) {x : G.V}
    (hAdj : 0 < num_edges G leaf x) :
    leafMap G leaf hDegree x = leafMap G leaf hDegree leaf := by
  have hx : x = (LeafPruning.leafData G leaf hDegree).root := by
    by_contra h
    rw [(LeafPruning.leafData G leaf hDegree).count_other x h] at hAdj
    exact Nat.not_lt_zero _ hAdj
  have hNe : x ≠ leaf := by
    intro h
    rw [h, num_edges_self_zero] at hAdj
    exact Nat.not_lt_zero _ hAdj
  rw [leafMap_of_ne G leaf hDegree x hNe, leafMap_leaf]
  exact Subtype.ext hx

/-- A retraction onto the actual induced graph, including its geometric and
chosen-divisor laws. Rank is preserved for every divisor, not just an
existentially chosen pencil. -/
structure PreservingRetraction (G : CFGraph.{u}) (S : Finset G.V) (hS : S.Nonempty) where
  vertexMap : G.V → (inducedSubgraph G S hS).V
  fixes : ∀ (x : G.V) (hx : x ∈ S), vertexMap x = induceMk G S hS hx
  collapses : ∀ a b : G.V, 0 < num_edges G a b →
    (a ∉ S ∨ b ∉ S) → vertexMap a = vertexMap b
  rank_push : ∀ D : CFDiv G, rank (inducedSubgraph G S hS) (push vertexMap D) = rank G D

private theorem exists_retraction_aux :
    ∀ bound : ℕ, ∀ (G : CFGraph.{u}) (S : Finset G.V) (hS : S.Nonempty),
      Fintype.card G.V = bound → graph_connected G →
      genus (inducedSubgraph G S hS) = genus G → Nonempty (PreservingRetraction G S hS) := by
  intro bound
  induction bound using Nat.strong_induction_on with
  | _ bound ih =>
    intro G S hS hCard hConnected hGenus
    classical
    by_cases hAll : ∀ v : G.V, v ∈ S
    · let e := laplacianEquiv_inducedSubgraph_univ G S hS hAll
      refine ⟨⟨e, ?_, ?_, ?_⟩⟩
      · intro x hx
        rfl
      · intro a b _ hOutside
        rcases hOutside with h | h
        · exact False.elim (h (hAll a))
        · exact False.elim (h (hAll b))
      · intro D
        rw [push_equiv, rank_mapDiv_eq]
    · obtain ⟨outside, hOutside⟩ := not_forall.mp hAll
      obtain ⟨leaf, hLeaf, hDegree⟩ :=
        exists_leaf_outside G S hS hConnected hGenus ⟨outside, hOutside⟩
      let G' := LeafPruning.deleteLeaf G leaf hDegree
      let S' := restrictSet G leaf hDegree S
      have hS' : S'.Nonempty := restrictSet_nonempty G leaf hDegree hS hLeaf
      let e := laplacianEquiv_inducedSubgraph_deleteLeaf G leaf hDegree hS hLeaf
      have hSmaller : Fintype.card G'.V < bound := by
        rw [← hCard]
        exact LeafReduction.card_vertices_deleteLeaf_lt G leaf hDegree
      have hConnected' : graph_connected G' :=
        LeafReduction.graph_connected_deleteLeaf G leaf hConnected hDegree
      have hGenusDelete : genus G' = genus G := LeafReduction.genus_deleteLeaf G leaf hDegree
      have hGenus' : genus (inducedSubgraph G' S' hS') = genus G' := by
        rw [e.genus_eq.symm.trans hGenus, hGenusDelete]
      obtain ⟨inner⟩ := ih (Fintype.card G'.V) hSmaller G' S' hS' rfl hConnected' hGenus'
      refine ⟨⟨e ∘ inner.vertexMap ∘ leafMap G leaf hDegree, ?_, ?_, ?_⟩⟩
      · intro x hx
        have hNe : x ≠ leaf := fun h ↦ hLeaf (h ▸ hx)
        change e (inner.vertexMap (leafMap G leaf hDegree x)) = _
        rw [leafMap_of_ne G leaf hDegree x hNe]
        have hx' : prune G leaf hDegree hNe ∈ S' := by
          exact (mem_restrictSet G leaf hDegree S _).mpr hx
        rw [inner.fixes _ hx']
        rfl
      · intro a b hAdj hOutside
        change e (inner.vertexMap (leafMap G leaf hDegree a)) =
          e (inner.vertexMap (leafMap G leaf hDegree b))
        by_cases ha : a = leaf
        · subst a
          rw [leafMap_eq_of_leaf_adjacent G leaf hDegree hAdj]
        · by_cases hb : b = leaf
          · subst b
            rw [leafMap_eq_of_leaf_adjacent G leaf hDegree
              (by rwa [num_edges_symmetric])]
          · rw [leafMap_of_ne G leaf hDegree a ha, leafMap_of_ne G leaf hDegree b hb]
            apply congrArg e
            apply inner.collapses
            · exact lt_of_lt_of_eq hAdj
                (LeafPruning.num_edges_deleteLeaf G leaf hDegree ⟨a, ha⟩ ⟨b, hb⟩).symm
            · rcases hOutside with h | h
              · exact Or.inl (fun ha' ↦ h ((mem_restrictSet G leaf hDegree S _).mp ha'))
              · exact Or.inr (fun hb' ↦ h ((mem_restrictSet G leaf hDegree S _).mp hb'))
      · intro D
        rw [push_comp, push_equiv, rank_mapDiv_eq, push_comp, inner.rank_push,
          rank_push_leafMap]

/-- Actual connected same-genus pendant deletion produces a literal rank-
preserving retraction, not merely a new divisor of the same rank and degree. -/
theorem exists_preservingRetraction (G : CFGraph.{u}) (S : Finset G.V) (hS : S.Nonempty)
    (hConnected : graph_connected G) (hGenus : genus (inducedSubgraph G S hS) = genus G) :
    Nonempty (PreservingRetraction G S hS) :=
  exists_retraction_aux (Fintype.card G.V) G S hS rfl hConnected hGenus

end DraismaVargas.Count.PendantDivisorTransport
