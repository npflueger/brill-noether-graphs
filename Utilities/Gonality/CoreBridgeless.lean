module

public import Utilities.Subdivision.CoreCutsAndFlats
public import Utilities.Subdivision.SlotIntervalFiring
public import Utilities.Gluing.TwoEdgeConnectedRigidity
public import Utilities.Gluing.VertexCutWedge
public import Utilities.Pseudocore.PseudocorePresentation

@[expose] public section

/-!
# Bridgelessness of a graph's unit-presentation core

This module transports connectedness and genus to the unit presentation and
provides two sufficient conditions for its core to be bridgeless:

* `core_bridgeless_of_twoEdgeCutCondition` uses `TwoEdgeCutCondition`.
  Every connected graph's fossil satisfies it (`twoEdgeCutCondition_fossil`),
  making this the route used by the genus-six odd-subdivision descent.
* `core_bridgeless` uses minimum degree three and `NotPositiveWedge`: in every
  one-vertex decomposition, one of the two induced factors has genus at most
  zero. This is an alternative criterion.

The wedge condition concerns induced factors, including the cut vertex. Merely
requiring at most one positive-genus component after deleting a cut vertex
would be weaker and would not suffice. Neither route imposes a subdivision
scale or a condition on a fine divisor.
-/

namespace Utilities.Gonality

open Utilities.Certificate Utilities.Certificate.SubdivisionGraph

/-! ## The wedge hypothesis -/

/-- `G` is **not a wedge of two positive-genus graphs**: for every one-vertex cut
of `G`, one of the two induced factors has genus at most zero.

The factors contain the cut vertex.  The weaker condition "no cut vertex
separates two positive-genus components" does **not** imply bridgelessness, even
together with minimum degree three. -/
def NotPositiveWedge (G : CFGraph) : Prop :=
  ∀ cut : OneVertexCut G, genus cut.leftGraph ≤ 0 ∨ genus cut.rightGraph ≤ 0

/-! ## Transporting the hypotheses to the unit presentation -/

/-- The unit subdivision presentation has all slot lengths one. -/
theorem isUnit_unitSpec (G : CFGraph) :
    (UnitSubdivisionPresentation.spec G).IsUnit := fun _ => rfl

/-- Connectivity transports to the core of the unit presentation. -/
theorem coreConnected_unitSpec (G : CFGraph) (hconn : graph_connected G) :
    (UnitSubdivisionPresentation.spec G).core.Connected :=
  PseudocorePresentation.core_connected_of_graph_connected _
    ((UnitSubdivisionPresentation.laplacianEquiv G).graphConnected hconn)

/-- The edge count expressed in terms of vertex count and genus. -/
theorem genus_unitSpec (G : CFGraph) :
    (G.edges.card : ℤ) = (Fintype.card G.V : ℤ) + genus G - 1 := by
  unfold genus
  omega

/-- A loopless graph of positive genus has at least two vertices: a single vertex
carries no loopless edge, so its genus is `0`. -/
theorem two_le_card_vertices (G : CFGraph) (hgenus : 0 < genus G) :
    2 ≤ Fintype.card G.V := by
  by_contra hlt
  have hpos : 0 < Fintype.card G.V := Fintype.card_pos
  have hcard : Fintype.card G.V = 1 := by omega
  have hsub : Subsingleton G.V := Fintype.card_le_one_iff_subsingleton.mp hcard.le
  have hne : G.edges ≠ 0 := by
    intro h
    unfold genus at hgenus
    rw [h, hcard] at hgenus
    norm_num at hgenus
  obtain ⟨e, he⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨x, y⟩ := e
  have hxy : y = x := Subsingleton.elim _ _
  subst hxy
  exact G.loopless _ he

/-! ## Bridgelessness of the core

The three private lemmas below are the arithmetic of the bridgelessness
argument.  The first identifies an edge multiplicity of `G` with a set of slots
of the unit presentation, so that "the only slot crossing the cut is `f`"
becomes a statement about `num_edges`.  The second and third are the degree
count that replaces the informal "a tree has a leaf": summing `min deg ≥ 3` over
a side of the cut and comparing with the handshake identity forces that side to
have positive genus. -/

/-- The slots of the unit presentation carrying a prescribed unordered pair of
endpoints are exactly the edge occurrences of `G` between them. -/
private theorem card_slots_eq_num_edges (G : CFGraph) (x y : G.V) :
    (Finset.univ.filter fun s : Fin G.edges.card =>
        UnitSubdivisionPresentation.edgeAt G s = (x, y) ∨
          UnitSubdivisionPresentation.edgeAt G s = (y, x)).card
      = num_edges G x y := by
  classical
  have hmap : (Finset.univ.filter fun occ : G.edges =>
        ((occ : G.V × G.V) = (x, y) ∨ (occ : G.V × G.V) = (y, x))).map
        (UnitSubdivisionPresentation.edgeEquiv G).toEmbedding
      = Finset.univ.filter fun s : Fin G.edges.card =>
        UnitSubdivisionPresentation.edgeAt G s = (x, y) ∨
          UnitSubdivisionPresentation.edgeAt G s = (y, x) := by
    ext s
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨occ, hocc, rfl⟩
      rwa [UnitSubdivisionPresentation.edgeAt_edgeEquiv]
    · intro hs
      exact ⟨(UnitSubdivisionPresentation.edgeEquiv G).symm s, hs, by simp⟩
  rw [← hmap, Finset.card_map,
    UnitSubdivisionPresentation.card_filter_occurrences G.edges
      (fun e => e = (x, y) ∨ e = (y, x))]
  rfl

/-- The degree of a vertex of an induced subgraph, read in the ambient graph. -/
private theorem vertex_degree_induced (G : CFGraph) (W : Finset G.V)
    (hW : W.Nonempty) (z : (inducedSubgraph G W hW).V) :
    vertex_degree (inducedSubgraph G W hW) z
      = ∑ y ∈ W, (num_edges G z.val y : ℤ) := by
  simp only [vertex_degree]
  rw [← Finset.sum_coe_sort W fun y => (num_edges G z.val y : ℤ)]
  exact Finset.sum_congr rfl fun y _ =>
    congrArg (fun m : ℕ => (m : ℤ)) (num_edges_inducedSubgraph G W hW z y)

/-- **The degree count of one side of a bridge.**  If every vertex of `W` other
than `u` has all of its `G`-neighbours inside `W`, then the handshake identity on
`G[W]` sees `min deg ≥ 3` at each of those `W.card - 1` vertices. -/
private theorem degree_sum_bound (G : CFGraph) (W : Finset G.V) (hW : W.Nonempty)
    (u : G.V) (hu : u ∈ W) (hmindeg : ∀ x : G.V, 3 ≤ vertex_degree G x)
    (hclosed : ∀ x ∈ W, x ≠ u → ∀ y : G.V, y ∉ W → num_edges G x y = 0) :
    3 * ((W.card : ℤ) - 1) + (∑ y ∈ W, (num_edges G u y : ℤ))
      ≤ 2 * (Multiset.card (inducedSubgraph G W hW).edges : ℤ) := by
  classical
  have hsum : ∑ z : (inducedSubgraph G W hW).V,
      vertex_degree (inducedSubgraph G W hW) z
      = 2 * (Multiset.card (inducedSubgraph G W hW).edges : ℤ) :=
    sum_vertex_degree_eq_twice_card_edges _
  have hsplit : ∑ z : (inducedSubgraph G W hW).V,
      vertex_degree (inducedSubgraph G W hW) z
      = vertex_degree (inducedSubgraph G W hW) ⟨u, hu⟩
        + ∑ z ∈ Finset.univ.erase (⟨u, hu⟩ : (inducedSubgraph G W hW).V),
            vertex_degree (inducedSubgraph G W hW) z :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ _)).symm
  have hUdeg : vertex_degree (inducedSubgraph G W hW) ⟨u, hu⟩
      = ∑ y ∈ W, (num_edges G u y : ℤ) := vertex_degree_induced G W hW _
  have hterm : ∀ z ∈ Finset.univ.erase (⟨u, hu⟩ : (inducedSubgraph G W hW).V),
      (3 : ℤ) ≤ vertex_degree (inducedSubgraph G W hW) z := by
    intro z hz
    have hzne : z.val ≠ u := fun h => (Finset.mem_erase.mp hz).1 (Subtype.ext h)
    have hval : ∑ y ∈ W, (num_edges G z.val y : ℤ) = vertex_degree G z.val := by
      simp only [vertex_degree]
      refine Finset.sum_subset (Finset.subset_univ W) ?_
      intro y _ hy
      rw [hclosed z.val z.property hzne y hy]
      simp
    rw [vertex_degree_induced G W hW z, hval]
    exact hmindeg z.val
  have hlow : 3 * ((Finset.univ.erase
        (⟨u, hu⟩ : (inducedSubgraph G W hW).V)).card : ℤ)
      ≤ ∑ z ∈ Finset.univ.erase (⟨u, hu⟩ : (inducedSubgraph G W hW).V),
          vertex_degree (inducedSubgraph G W hW) z := by
    calc 3 * ((Finset.univ.erase
          (⟨u, hu⟩ : (inducedSubgraph G W hW).V)).card : ℤ)
        = ∑ _z ∈ Finset.univ.erase (⟨u, hu⟩ : (inducedSubgraph G W hW).V),
            (3 : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum hterm
  have hcard1 : 1 ≤ W.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hcarderase : ((Finset.univ.erase
      (⟨u, hu⟩ : (inducedSubgraph G W hW).V)).card : ℤ) = (W.card : ℤ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_coe, Nat.cast_sub hcard1, Nat.cast_one]
  rw [hcarderase] at hlow
  linarith

/-- **The wedge contradiction.**  A cut of `G` whose only crossing edge is the
single occurrence `v—u` is impossible under `min deg ≥ 3` and
`NotPositiveWedge`: the wedge `G[S ∪ {u}] ∨_u G[Sᶜ]` has two factors, and
`degree_sum_bound` gives each of them positive genus. -/
private theorem no_bridge_aux (G : CFGraph)
    (hmindeg : ∀ x : G.V, 3 ≤ vertex_degree G x) (hwedge : NotPositiveWedge G)
    (S : Finset G.V) (u v : G.V) (hv : v ∈ S) (hu : u ∉ S)
    (hvu : num_edges G v u = 1)
    (hzero : ∀ x ∈ S, ∀ y : G.V, y ∉ S → ¬ (x = v ∧ y = u) →
      num_edges G x y = 0) : False := by
  classical
  have hleftne : (insert u S).Nonempty := ⟨u, Finset.mem_insert_self u S⟩
  have hrightne : (Sᶜ : Finset G.V).Nonempty := ⟨u, Finset.mem_compl.mpr hu⟩
  have hcut := hwedge
    { left := insert u S
      right := Sᶜ
      glue := u
      glue_mem_left := Finset.mem_insert_self u S
      glue_mem_right := Finset.mem_compl.mpr hu
      vertex_cover := by
        intro z
        by_cases hz : z ∈ S
        · exact Or.inl (Finset.mem_insert_of_mem hz)
        · exact Or.inr (Finset.mem_compl.mpr hz)
      only_overlap := by
        intro z hzl hzr
        rcases Finset.mem_insert.mp hzl with h | h
        · exact h
        · exact absurd h (Finset.mem_compl.mp hzr)
      no_cross := by
        intro a ha hane b hb hbne
        exact hzero a ((Finset.mem_insert.mp ha).resolve_left hane) b
          (Finset.mem_compl.mp hb) fun h => hbne h.2 }
  have hcut' : genus (inducedSubgraph G (insert u S) hleftne) ≤ 0 ∨
      genus (inducedSubgraph G (Sᶜ) hrightne) ≤ 0 := hcut
  rcases hcut' with hL | hR
  · have hclosed : ∀ x ∈ insert u S, x ≠ u → ∀ y : G.V, y ∉ insert u S →
        num_edges G x y = 0 := by
      intro x hx hxu y hy
      refine hzero x ((Finset.mem_insert.mp hx).resolve_left hxu) y
        (fun h => hy (Finset.mem_insert_of_mem h)) ?_
      rintro ⟨-, rfl⟩
      exact hy (Finset.mem_insert_self _ _)
    have hbound := degree_sum_bound G (insert u S) hleftne u
      (Finset.mem_insert_self u S) hmindeg hclosed
    have hnn : (0 : ℤ) ≤ ∑ y ∈ insert u S, (num_edges G u y : ℤ) :=
      Finset.sum_nonneg fun y _ => Int.natCast_nonneg _
    have hgen : (Multiset.card (inducedSubgraph G (insert u S) hleftne).edges : ℤ)
        - ((insert u S).card : ℤ) + 1 ≤ 0 := by
      have h := hL
      unfold genus at h
      rwa [inducedSubgraph_vertex_card] at h
    have hcard2 : 2 ≤ (insert u S).card := by
      rw [Finset.card_insert_of_notMem hu]
      have : 1 ≤ S.card := Finset.card_pos.mpr ⟨v, hv⟩
      omega
    have hcard2' : (2 : ℤ) ≤ ((insert u S).card : ℤ) := by exact_mod_cast hcard2
    linarith
  · have hclosed : ∀ x ∈ (Sᶜ : Finset G.V), x ≠ u → ∀ y : G.V,
        y ∉ (Sᶜ : Finset G.V) → num_edges G x y = 0 := by
      intro x hx hxu y hy
      have hy' : y ∈ S := by simpa using hy
      rw [num_edges_symmetric]
      exact hzero y hy' x (Finset.mem_compl.mp hx) fun h => hxu h.2
    have hbound := degree_sum_bound G (Sᶜ) hrightne u (Finset.mem_compl.mpr hu)
      hmindeg hclosed
    have hone : (∑ y ∈ S, (num_edges G u y : ℤ)) = 1 := by
      have hterm : ∀ y ∈ S, (num_edges G u y : ℤ) = if y = v then 1 else 0 := by
        intro y hy
        by_cases hyv : y = v
        · rw [ite_eq_left hyv, num_edges_symmetric G u y, hyv, hvu]
          norm_num
        · rw [ite_eq_right hyv, num_edges_symmetric G u y,
            hzero y hy u hu fun h => hyv h.1]
          norm_num
      rw [Finset.sum_congr rfl hterm,
        Finset.sum_ite_eq' S v fun _ => (1 : ℤ), ite_eq_left hv]
    have hdecomp : (∑ y ∈ S, (num_edges G u y : ℤ))
        + (∑ y ∈ (Sᶜ : Finset G.V), (num_edges G u y : ℤ))
        = vertex_degree G u := by
      rw [Finset.sum_add_sum_compl]
      rfl
    have hdegu := hmindeg u
    have hgen : (Multiset.card (inducedSubgraph G (Sᶜ) hrightne).edges : ℤ)
        - ((Sᶜ : Finset G.V).card : ℤ) + 1 ≤ 0 := by
      have h := hR
      unfold genus at h
      rwa [inducedSubgraph_vertex_card] at h
    have hcard1 : 1 ≤ (Sᶜ : Finset G.V).card := Finset.card_pos.mpr hrightne
    have hcard1' : (1 : ℤ) ≤ ((Sᶜ : Finset G.V).card : ℤ) := by exact_mod_cast hcard1
    linarith

/-- **The cut behind an alleged bridge of the core.**  This is the *first half*
of both bridgelessness criteria, shared by their two hypotheses (`min deg ≥ 3`
plus `NotPositiveWedge`, and `TwoEdgeCutCondition`): a bridge `f` of the unit
presentation's core produces a non-empty proper vertex set `S` of `G` whose
only crossing edge occurrence is a single `v—u` with `v ∈ S` and `u ∉ S`.

Nothing about genus, degrees or wedges enters here; the two second halves are
`no_bridge_aux` and the `cutMultiplicity` count of
`core_bridgeless_of_twoEdgeCutCondition`. -/
private theorem cut_of_core_isBridgeOff (G : CFGraph) (hconn : graph_connected G)
    (f : Fin G.edges.card)
    (hf : (UnitSubdivisionPresentation.spec G).core.IsBridgeOff ∅ f) :
    ∃ (S : Finset G.V) (v u : G.V), v ∈ S ∧ u ∉ S ∧ num_edges G v u = 1 ∧
      ∀ x ∈ S, ∀ y : G.V, y ∉ S → ¬ (x = v ∧ y = u) → num_edges G x y = 0 := by
  classical
  have htail : ∀ e : Fin G.edges.card,
      (UnitSubdivisionPresentation.spec G).core.tail e
        = UnitSubdivisionPresentation.vertexEquiv G
            (UnitSubdivisionPresentation.edgeAt G e).1 := fun _ => rfl
  have hhead : ∀ e : Fin G.edges.card,
      (UnitSubdivisionPresentation.spec G).core.head e
        = UnitSubdivisionPresentation.vertexEquiv G
            (UnitSubdivisionPresentation.edgeAt G e).2 := fun _ => rfl
  -- The cut disconnected by deleting the alleged bridge, read in `G`.
  obtain ⟨T, hTne, hTonly⟩ : ∃ T : Finset (Fin (Fintype.card G.V)),
      (∃ a b : Fin (Fintype.card G.V), a ∈ T ∧ b ∉ T) ∧
        ∀ e : Fin G.edges.card, e ≠ f →
          ¬ (UnitSubdivisionPresentation.spec G).core.Crosses T e := by
    by_contra hcon
    refine hf.2.2 fun T hT => ?_
    by_contra hno
    exact hcon ⟨T, hT, fun e hef hcross =>
      hno ⟨e, by simpa using hef, hcross⟩⟩
  set S : Finset G.V :=
    Finset.univ.filter fun x => UnitSubdivisionPresentation.vertexEquiv G x ∈ T
    with hSdef
  have hmemS : ∀ x : G.V,
      x ∈ S ↔ UnitSubdivisionPresentation.vertexEquiv G x ∈ T := by
    intro x; simp [hSdef]
  -- Every slot joining `S` to its complement is the alleged bridge.
  have hslot : ∀ x : G.V, x ∈ S → ∀ y : G.V, y ∉ S → ∀ e : Fin G.edges.card,
      (UnitSubdivisionPresentation.edgeAt G e = (x, y) ∨
        UnitSubdivisionPresentation.edgeAt G e = (y, x)) → e = f := by
    intro x hx y hy e he
    by_contra hne
    refine hTonly e hne ?_
    rcases he with he | he
    · exact Or.inl ⟨by rw [htail, he]; exact (hmemS x).mp hx,
        by rw [hhead, he]; exact fun h => hy ((hmemS y).mpr h)⟩
    · exact Or.inr ⟨by rw [hhead, he]; exact (hmemS x).mp hx,
        by rw [htail, he]; exact fun h => hy ((hmemS y).mpr h)⟩
  have hnumsub : ∀ x : G.V, x ∈ S → ∀ y : G.V, y ∉ S →
      (Finset.univ.filter fun e : Fin G.edges.card =>
          UnitSubdivisionPresentation.edgeAt G e = (x, y) ∨
            UnitSubdivisionPresentation.edgeAt G e = (y, x)) ⊆ {f} := by
    intro x hx y hy e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    simpa using hslot x hx y hy e he
  -- The bridge itself does cross, since `G` is connected.
  have hfcross : (UnitSubdivisionPresentation.spec G).core.Crosses T f := by
    obtain ⟨e, he⟩ := coreConnected_unitSpec G hconn T hTne
    by_cases hef : e = f
    · rwa [hef] at he
    · exact absurd he (hTonly e hef)
  obtain ⟨a, b, hab⟩ : ∃ a b : G.V,
      UnitSubdivisionPresentation.edgeAt G f = (a, b) := ⟨_, _, rfl⟩
  -- The heart: the near side of the cut, with the bridge as its only exit.
  have key : ∀ v u : G.V, v ∈ S → u ∉ S →
      (UnitSubdivisionPresentation.edgeAt G f = (v, u) ∨
        UnitSubdivisionPresentation.edgeAt G f = (u, v)) →
      ∃ (S' : Finset G.V) (v' u' : G.V), v' ∈ S' ∧ u' ∉ S' ∧
        num_edges G v' u' = 1 ∧
        ∀ x ∈ S', ∀ y : G.V, y ∉ S' → ¬ (x = v' ∧ y = u') →
          num_edges G x y = 0 := by
    intro v u hv hu hedge
    have hfmem : f ∈ Finset.univ.filter fun e : Fin G.edges.card =>
        UnitSubdivisionPresentation.edgeAt G e = (v, u) ∨
          UnitSubdivisionPresentation.edgeAt G e = (u, v) := by
      simpa using hedge
    have hvu : num_edges G v u = 1 := by
      rw [← card_slots_eq_num_edges G v u,
        Finset.Subset.antisymm (hnumsub v hv u hu)
          (Finset.singleton_subset_iff.mpr hfmem)]
      exact Finset.card_singleton f
    refine ⟨S, v, u, hv, hu, hvu, ?_⟩
    intro x hx y hy hne
    by_contra hnz
    have hpos : (Finset.univ.filter fun e : Fin G.edges.card =>
        UnitSubdivisionPresentation.edgeAt G e = (x, y) ∨
          UnitSubdivisionPresentation.edgeAt G e = (y, x)).Nonempty := by
      rw [← Finset.card_pos, card_slots_eq_num_edges]
      omega
    obtain ⟨e, hemem⟩ := hpos
    have hef : e = f := by simpa using hnumsub x hx y hy hemem
    rw [hef] at hemem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hemem
    refine hne ?_
    rcases hemem with h1 | h1 <;> rcases hedge with h2 | h2
    · exact ⟨congrArg Prod.fst (h1.symm.trans h2),
        congrArg Prod.snd (h1.symm.trans h2)⟩
    · exact absurd hx (by
        rw [show x = u from congrArg Prod.fst (h1.symm.trans h2)]; exact hu)
    · exact absurd hx (by
        rw [show x = u from congrArg Prod.snd (h1.symm.trans h2)]; exact hu)
    · exact ⟨congrArg Prod.snd (h1.symm.trans h2),
        congrArg Prod.fst (h1.symm.trans h2)⟩
  have hcross' : (UnitSubdivisionPresentation.vertexEquiv G a ∈ T ∧
      UnitSubdivisionPresentation.vertexEquiv G b ∉ T) ∨
      (UnitSubdivisionPresentation.vertexEquiv G b ∈ T ∧
        UnitSubdivisionPresentation.vertexEquiv G a ∉ T) := by
    have hta : (UnitSubdivisionPresentation.spec G).core.tail f
        = UnitSubdivisionPresentation.vertexEquiv G a := by rw [htail, hab]
    have hhb : (UnitSubdivisionPresentation.spec G).core.head f
        = UnitSubdivisionPresentation.vertexEquiv G b := by rw [hhead, hab]
    have h : ((UnitSubdivisionPresentation.spec G).core.tail f ∈ T ∧
        (UnitSubdivisionPresentation.spec G).core.head f ∉ T) ∨
        ((UnitSubdivisionPresentation.spec G).core.head f ∈ T ∧
          (UnitSubdivisionPresentation.spec G).core.tail f ∉ T) := hfcross
    rw [hta, hhb] at h
    exact h
  rcases hcross' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key a b ((hmemS a).mpr h1) (fun h => h2 ((hmemS b).mp h)) (Or.inl hab)
  · exact key b a ((hmemS b).mpr h1) (fun h => h2 ((hmemS a).mp h)) (Or.inr hab)

/-- **Bridgelessness from minimum degree three and `NotPositiveWedge`.**  If `G`
is connected, every vertex has degree at least three, and `G` is not a wedge of
two positive-genus graphs, then the core of its unit presentation is bridgeless.

Proof: let `f = uv` be a bridge with sides `S ∋ v` and `T ∋ u`.  Genus is
additive across a bridge, `g(G) = g(G[S]) + g(G[T])`.  If `g(G[S]) = 0` then
`G[S]` is a tree, which has a vertex of `G`-degree at most one (a leaf other
than `v`, or `S = {v}` itself), contradicting `min deg ≥ 3`.  So both sides have
positive genus and `G = G[S ∪ {u}] ∨_u G[T]` is the forbidden wedge.

`core_bridgeless_of_twoEdgeCutCondition` below reaches the same conclusion from
the two-edge-cut condition instead, with neither the degree hypothesis nor
`NotPositiveWedge`. -/
theorem core_bridgeless (G : CFGraph) (hconn : graph_connected G)
    (hmindeg : ∀ v : G.V, 3 ≤ vertex_degree G v) (hwedge : NotPositiveWedge G) :
    (UnitSubdivisionPresentation.spec G).core.Bridgeless := by
  intro f hf
  obtain ⟨S, v, u, hv, hu, hvu, hzero⟩ := cut_of_core_isBridgeOff G hconn f hf
  exact no_bridge_aux G hmindeg hwedge S u v hv hu hvu hzero

/-- **Bridgelessness from the two-edge-cut condition.**
`Utilities.TwoEdgeCutCondition` (`Utilities/Gluing/TwoEdgeConnectedRigidity.lean`)
is graph-level bridgelessness: every non-empty proper vertex cut carries at
least two edge occurrences.  It implies bridgelessness of the core directly,
with no degree hypothesis and no `NotPositiveWedge`.

Proof: `cut_of_core_isBridgeOff` produces the cut `S` whose only crossing
occurrence is a single `v—u`, so `cutMultiplicity G S = 1`, contradicting the
hypothesis at `S`.

Applied to `Utilities.fossil G`, which is connected of the same genus
(`graph_connected_fossil`, `genus_fossil`) and satisfies the condition
(`twoEdgeCutCondition_fossil`), this makes the core of the fossil's unit
presentation bridgeless for *every* connected graph `G`; the genus-six
odd-subdivision descent uses it in that form. -/
theorem core_bridgeless_of_twoEdgeCutCondition (G : CFGraph)
    (hconn : graph_connected G) (h2 : TwoEdgeCutCondition G) :
    (UnitSubdivisionPresentation.spec G).core.Bridgeless := by
  classical
  intro f hf
  obtain ⟨S, v, u, hv, hu, hvu, hzero⟩ := cut_of_core_isBridgeOff G hconn f hf
  -- The cut is non-empty and proper.
  have hne : S.Nonempty := ⟨v, hv⟩
  have hproper : S ≠ Finset.univ := fun h => hu (h ▸ Finset.mem_univ u)
  -- Its total outgoing multiplicity is exactly one: only `v—u` crosses.
  have huniv : u ∈ Finset.univ \ S := by simp [hu]
  have hterm : ∀ x ∈ S, outdeg_S G S x = if x = v then 1 else 0 := by
    intro x hx
    by_cases hxv : x = v
    · subst hxv
      rw [ite_eq_left rfl]
      unfold outdeg_S
      refine (Finset.sum_eq_single_of_mem u huniv ?_).trans ?_
      · intro y hy hyu
        have hy' : y ∉ S := (Finset.mem_sdiff.mp hy).2
        rw [hzero x hx y hy' fun h => hyu h.2]
        norm_num
      · rw [hvu]; norm_num
    · rw [ite_eq_right hxv]
      unfold outdeg_S
      refine Finset.sum_eq_zero ?_
      intro y hy
      have hy' : y ∉ S := (Finset.mem_sdiff.mp hy).2
      rw [hzero x hx y hy' fun h => hxv h.1]
      norm_num
  have hval : cutMultiplicity G S = 1 := by
    unfold cutMultiplicity
    rw [Finset.sum_congr rfl hterm,
      Finset.sum_ite_eq' S v fun _ => (1 : ℤ), ite_eq_left hv]
  have hcut := h2 S hne hproper
  rw [hval] at hcut
  omega

end Utilities.Gonality
