import DraismaVargas.Infrastructure.GluingDatum
import DraismaVargas.Infrastructure.GraphContraction
import Utilities.Iso.GraphIso
import Mathlib.Data.Sym.Sym2

/-!
# Transporting a gluing datum along an isomorphism of target graphs

`Utilities.CFGraphIso G H` records only an equivalence of vertex types together
with the equality of every edge multiplicity.  A `GluingDatum` however is
indexed by **edge occurrences**, i.e. by the multiset-as-type `G.edges`, so a
graph isomorphism does not literally carry a gluing datum from `G` to `H`.

This file supplies the missing occurrence-level bijection and uses it to
transport a datum together with its validity.

The occurrence bijection is built exactly as in
`DraismaVargas.Infrastructure.GluingContraction`: occurrences are grouped into
fibres over their unordered endpoint pair, the two fibres over corresponding
pairs have the same cardinality because `map_num_edges` says so, and
`Equiv.ofFiberEquiv` assembles the fibrewise bijections.  No occurrence is
matched by an arbitrary choice inside a fibre in a way that would forget
parallel edges: parallel occurrences stay inside their own fibre.

Note that `CFGraph` stores edges as ordered pairs but `num_edges` is symmetric,
so an isomorphism is free to reverse the stored orientation of an occurrence.
Consequently the endpoint statement `edgeEquiv_key` is an equality of
**unordered** pairs, equivalently the disjunction `edgeEquiv_ends`.

Both graphs live in the same universe here, because `Equiv.ofFiberEquiv`
(through `Equiv.sigmaCongrRight`) needs the two fibre families to do so.
-/

namespace DraismaVargas.Infrastructure.GluingTransport

open Utilities

universe u

variable {G H : CFGraph.{u}} {degree : ℕ}

/-! ## Counting occurrences inside a multiset-as-type -/

/-- The occurrences of a multiset satisfying a predicate on the underlying
element are counted by the filtered multiset. -/
theorem card_subtype_coe {α : Type u} [DecidableEq α] (m : Multiset α)
    (P : α → Prop) [DecidablePred P] :
    Fintype.card {x : m // P (x : α)} = Multiset.card (m.filter P) := by
  rw [Fintype.card_subtype]
  conv_rhs => rw [← Multiset.map_univ_coe m]
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

/-! ## The unordered endpoint pair of an occurrence -/

/-- The unordered endpoint pair of an edge occurrence. -/
def edgeKey (G : CFGraph.{u}) (e : G.edges) : Sym2 G.V :=
  s((e : G.V × G.V).1, (e : G.V × G.V).2)

/-- The unordered endpoint pair of an edge occurrence, pushed forward along a
graph isomorphism. -/
def mappedEdgeKey (φ : CFGraphIso G H) (e : G.edges) : Sym2 H.V :=
  s(φ.vertexEquiv (e : G.V × G.V).1, φ.vertexEquiv (e : G.V × G.V).2)

theorem card_edgeKey_fiber (G : CFGraph.{u}) (v w : G.V) :
    Fintype.card {e : G.edges // edgeKey G e = s(v, w)} = num_edges G v w := by
  have hEquiv : {e : G.edges // edgeKey G e = s(v, w)} ≃
      {e : G.edges // (e : G.V × G.V) = (v, w) ∨ (e : G.V × G.V) = (w, v)} := by
    refine Equiv.subtypeEquivRight fun e => ?_
    rw [edgeKey, Sym2.eq_iff, Prod.ext_iff, Prod.ext_iff]
  rw [Fintype.card_congr hEquiv,
    card_subtype_coe G.edges (fun e => e = (v, w) ∨ e = (w, v))]
  rfl

theorem card_mappedEdgeKey_fiber (φ : CFGraphIso G H) (v w : G.V) :
    Fintype.card {e : G.edges //
        mappedEdgeKey φ e = s(φ.vertexEquiv v, φ.vertexEquiv w)}
      = num_edges G v w := by
  have hEquiv : {e : G.edges //
      mappedEdgeKey φ e = s(φ.vertexEquiv v, φ.vertexEquiv w)} ≃
      {e : G.edges // (e : G.V × G.V) = (v, w) ∨ (e : G.V × G.V) = (w, v)} := by
    refine Equiv.subtypeEquivRight fun e => ?_
    rw [mappedEdgeKey, Sym2.eq_iff, Prod.ext_iff, Prod.ext_iff]
    simp only [Equiv.apply_eq_iff_eq]
  rw [Fintype.card_congr hEquiv,
    card_subtype_coe G.edges (fun e => e = (v, w) ∨ e = (w, v))]
  rfl

/-- Corresponding fibres of the unordered endpoint map have equal size: this is
exactly `map_num_edges`. -/
theorem card_fiber_eq (φ : CFGraphIso G H) (key : Sym2 H.V) :
    Fintype.card {e : G.edges // mappedEdgeKey φ e = key}
      = Fintype.card {e : H.edges // edgeKey H e = key} := by
  induction key using Sym2.ind with
  | _ x y =>
    obtain ⟨v, rfl⟩ := φ.vertexEquiv.surjective x
    obtain ⟨w, rfl⟩ := φ.vertexEquiv.surjective y
    rw [card_mappedEdgeKey_fiber, card_edgeKey_fiber, φ.map_num_edges]

/-! ## The occurrence equivalence -/

/-- The bijection between the edge occurrences of isomorphic graphs. -/
noncomputable def edgeEquiv (φ : CFGraphIso G H) : G.edges ≃ H.edges :=
  Equiv.ofFiberEquiv (f := mappedEdgeKey φ) (g := edgeKey H)
    fun key => Fintype.equivOfCardEq (card_fiber_eq φ key)

/-- The occurrence bijection preserves unordered endpoint pairs. -/
theorem edgeEquiv_key (φ : CFGraphIso G H) (e : G.edges) :
    edgeKey H (edgeEquiv φ e) = mappedEdgeKey φ e :=
  Equiv.ofFiberEquiv_map _ e

/-- The occurrence bijection preserves unordered endpoint pairs, read backwards. -/
theorem edgeEquiv_symm_key (φ : CFGraphIso G H) (e : H.edges) :
    mappedEdgeKey φ ((edgeEquiv φ).symm e) = edgeKey H e := by
  conv_rhs => rw [← (edgeEquiv φ).apply_symm_apply e]
  exact (edgeEquiv_key φ _).symm

/-- Endpoints of a transported occurrence, in ordered form.  The stored
orientation of an occurrence is not part of the data an isomorphism preserves,
so the statement is a disjunction. -/
theorem edgeEquiv_ends (φ : CFGraphIso G H) (e : G.edges) :
    ((edgeEquiv φ e : H.V × H.V)) =
      (φ.vertexEquiv (e : G.V × G.V).1, φ.vertexEquiv (e : G.V × G.V).2) ∨
    ((edgeEquiv φ e : H.V × H.V)) =
      (φ.vertexEquiv (e : G.V × G.V).2, φ.vertexEquiv (e : G.V × G.V).1) := by
  have hKey := edgeEquiv_key φ e
  rw [edgeKey, mappedEdgeKey, Sym2.eq_iff] at hKey
  rcases hKey with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Prod.ext h1 h2)

/-- Endpoints of an occurrence pulled back along the occurrence bijection. -/
theorem edgeEquiv_symm_ends (φ : CFGraphIso G H) (e : H.edges) :
    ((e : H.V × H.V)) =
      (φ.vertexEquiv (((edgeEquiv φ).symm e : G.edges) : G.V × G.V).1,
        φ.vertexEquiv (((edgeEquiv φ).symm e : G.edges) : G.V × G.V).2) ∨
    ((e : H.V × H.V)) =
      (φ.vertexEquiv (((edgeEquiv φ).symm e : G.edges) : G.V × G.V).2,
        φ.vertexEquiv (((edgeEquiv φ).symm e : G.edges) : G.V × G.V).1) := by
  have hKey := edgeEquiv_symm_key φ e
  rw [mappedEdgeKey, edgeKey, Sym2.eq_iff] at hKey
  rcases hKey with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Prod.ext h1.symm h2.symm)
  · exact Or.inr (Prod.ext h2.symm h1.symm)

/-! ## The transported gluing datum -/

/-- Transport a gluing datum along an isomorphism of target graphs.  Vertex and
edge partitions are literally carried across by the vertex equivalence and by
`edgeEquiv`; refinement at each end of an occurrence is inherited, with the two
ends possibly exchanged. -/
noncomputable def transport (φ : CFGraphIso G H) (data : GluingDatum G degree) :
    GluingDatum H degree where
  degree_pos := data.degree_pos
  vertexPartition y := data.vertexPartition (φ.vertexEquiv.symm y)
  edgePartition e := data.edgePartition ((edgeEquiv φ).symm e)
  refines_left := by
    intro e
    show (data.edgePartition ((edgeEquiv φ).symm e)).Refines
      (data.vertexPartition (φ.vertexEquiv.symm (e : H.V × H.V).1))
    have hKey := edgeEquiv_symm_key φ e
    rw [mappedEdgeKey, edgeKey, Sym2.eq_iff] at hKey
    rcases hKey with ⟨h1, _⟩ | ⟨_, h2⟩
    · rw [← h1, Equiv.symm_apply_apply]
      exact data.refines_left _
    · rw [← h2, Equiv.symm_apply_apply]
      exact data.refines_right _
  refines_right := by
    intro e
    show (data.edgePartition ((edgeEquiv φ).symm e)).Refines
      (data.vertexPartition (φ.vertexEquiv.symm (e : H.V × H.V).2))
    have hKey := edgeEquiv_symm_key φ e
    rw [mappedEdgeKey, edgeKey, Sym2.eq_iff] at hKey
    rcases hKey with ⟨_, h2⟩ | ⟨h1, _⟩
    · rw [← h2, Equiv.symm_apply_apply]
      exact data.refines_right _
    · rw [← h1, Equiv.symm_apply_apply]
      exact data.refines_left _

@[simp] theorem transport_vertexPartition (φ : CFGraphIso G H)
    (data : GluingDatum G degree) (y : H.V) :
    (transport φ data).vertexPartition y =
      data.vertexPartition (φ.vertexEquiv.symm y) := rfl

@[simp] theorem transport_edgePartition (φ : CFGraphIso G H)
    (data : GluingDatum G degree) (e : H.edges) :
    (transport φ data).edgePartition e =
      data.edgePartition ((edgeEquiv φ).symm e) := rfl

theorem transport_vertexPartition_apply (φ : CFGraphIso G H)
    (data : GluingDatum G degree) (v : G.V) :
    (transport φ data).vertexPartition (φ.vertexEquiv v) =
      data.vertexPartition v := by
  rw [transport_vertexPartition, Equiv.symm_apply_apply]

theorem transport_edgePartition_apply (φ : CFGraphIso G H)
    (data : GluingDatum G degree) (f : G.edges) :
    (transport φ data).edgePartition (edgeEquiv φ f) = data.edgePartition f := by
  rw [transport_edgePartition, Equiv.symm_apply_apply]

/-! ## The source correspondence -/

/-- Quotient-source vertices are carried across by the vertex equivalence. -/
noncomputable def sourceVertexMap (φ : CFGraphIso G H)
    (data : GluingDatum G degree) (x : data.SourceVertex) :
    (transport φ data).SourceVertex :=
  ⟨(φ.vertexEquiv x.1.1, x.1.2), by
    show (data.vertexPartition
      (φ.vertexEquiv.symm (φ.vertexEquiv x.1.1))).repr x.1.2 = x.1.2
    rw [Equiv.symm_apply_apply]
    exact x.2⟩

@[simp] theorem sourceVertexMap_fst (φ : CFGraphIso G H)
    (data : GluingDatum G degree) (x : data.SourceVertex) :
    (sourceVertexMap φ data x).1.1 = φ.vertexEquiv x.1.1 := rfl

@[simp] theorem sourceVertexMap_snd (φ : CFGraphIso G H)
    (data : GluingDatum G degree) (x : data.SourceVertex) :
    (sourceVertexMap φ data x).1.2 = x.1.2 := rfl

theorem sourceVertexMap_surjective (φ : CFGraphIso G H)
    (data : GluingDatum G degree) :
    Function.Surjective (sourceVertexMap φ data) := by
  rintro ⟨⟨y, sheet⟩, hy⟩
  refine ⟨⟨(φ.vertexEquiv.symm y, sheet), hy⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact φ.vertexEquiv.apply_symm_apply y
  · rfl

/-- Quotient-source edge occurrences are carried across by `edgeEquiv`. -/
noncomputable def sourceEdgeMap (φ : CFGraphIso G H)
    (data : GluingDatum G degree) (e : data.SourceEdge) :
    (transport φ data).SourceEdge :=
  ⟨(edgeEquiv φ e.1.1, e.1.2), by
    rw [transport_edgePartition_apply]
    exact e.2⟩

/-- Canonical endpoints commute with the source correspondence. -/
theorem sourceEndpoint_map (φ : CFGraphIso G H) (data : GluingDatum G degree)
    (v : G.V) (sheet : Fin degree) :
    (transport φ data).sourceEndpoint (φ.vertexEquiv v) sheet
      = sourceVertexMap φ data (data.sourceEndpoint v sheet) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · show ((transport φ data).vertexPartition (φ.vertexEquiv v)).repr sheet
      = (data.vertexPartition v).repr sheet
    rw [transport_vertexPartition_apply]

/-- The endpoints of a transported source occurrence are the images of its
endpoints, possibly in the other order. -/
theorem sourceEnds_sourceEdgeMap (φ : CFGraphIso G H)
    (data : GluingDatum G degree) (e : data.SourceEdge) :
    (transport φ data).sourceEnds (sourceEdgeMap φ data e)
        = (sourceVertexMap φ data (data.sourceEnds e).1,
          sourceVertexMap φ data (data.sourceEnds e).2) ∨
      (transport φ data).sourceEnds (sourceEdgeMap φ data e)
        = (sourceVertexMap φ data (data.sourceEnds e).2,
          sourceVertexMap φ data (data.sourceEnds e).1) := by
  have hEnds : (transport φ data).sourceEnds (sourceEdgeMap φ data e)
      = ((transport φ data).sourceEndpoint
            ((edgeEquiv φ e.1.1 : H.V × H.V)).1 e.1.2,
          (transport φ data).sourceEndpoint
            ((edgeEquiv φ e.1.1 : H.V × H.V)).2 e.1.2) := rfl
  rcases edgeEquiv_ends φ e.1.1 with h | h
  · refine Or.inl ?_
    rw [hEnds, h]
    exact Prod.ext (sourceEndpoint_map φ data _ _) (sourceEndpoint_map φ data _ _)
  · refine Or.inr ?_
    rw [hEnds, h]
    exact Prod.ext (sourceEndpoint_map φ data _ _) (sourceEndpoint_map φ data _ _)

/-! ## Connectivity -/

/-- Transporting a gluing datum preserves connectedness of the quotient
source. -/
theorem connected_transport (φ : CFGraphIso G H) (data : GluingDatum G degree)
    (hConnected : data.Connected) : (transport φ data).Connected := by
  classical
  intro T hT
  obtain ⟨x₀, y₀, hx₀, hy₀⟩ := hT
  set S : Finset data.SourceVertex :=
    Finset.univ.filter (fun v => sourceVertexMap φ data v ∈ T) with hSdef
  have hmemS : ∀ v : data.SourceVertex,
      v ∈ S ↔ sourceVertexMap φ data v ∈ T := by
    intro v
    rw [hSdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ v, h⟩⟩
  obtain ⟨x, hx⟩ := sourceVertexMap_surjective φ data x₀
  obtain ⟨y, hy⟩ := sourceVertexMap_surjective φ data y₀
  have hxS : x ∈ S := (hmemS x).mpr (by rw [hx]; exact hx₀)
  have hyS : y ∉ S := fun h => hy₀ (by rw [← hy]; exact (hmemS y).mp h)
  obtain ⟨v, hvS, w, hwS, hpos⟩ := hConnected S ⟨x, y, hxS, hyS⟩
  obtain ⟨edge, hedgeMem, hends⟩ :=
    GraphContraction.exists_mem_edges_of_num_edges_pos data.sourceGraph v w hpos
  obtain ⟨se, -, hse⟩ := Multiset.mem_map.mp
    (show edge ∈ (Finset.univ : Finset data.SourceEdge).val.map data.sourceEnds
      from hedgeMem)
  have hmem : (transport φ data).sourceEnds (sourceEdgeMap φ data se)
      ∈ (transport φ data).sourceGraph.edges :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ _)
  refine ⟨sourceVertexMap φ data v, (hmemS v).mp hvS,
    sourceVertexMap φ data w, fun hcon => hwS ((hmemS w).mpr hcon), ?_⟩
  rcases hends with rfl | rfl <;>
    rcases sourceEnds_sourceEdgeMap φ data se with hOr | hOr <;>
      rw [hOr, hse] at hmem
  · exact GraphContraction.num_edges_pos_of_mem_edges
      (transport φ data).sourceGraph _ _ hmem
  · exact GraphContraction.num_edges_pos_of_mem_edges'
      (transport φ data).sourceGraph _ _ hmem
  · exact GraphContraction.num_edges_pos_of_mem_edges'
      (transport φ data).sourceGraph _ _ hmem
  · exact GraphContraction.num_edges_pos_of_mem_edges
      (transport φ data).sourceGraph _ _ hmem

/-! ## Incident occurrences -/

/-- Local copy of the membership description of `GluingDatum.incidentEdges`
(the same statement is proved in `GluingContraction`, which this module does
not import). -/
theorem mem_incidentEdges_iff_local {K : CFGraph.{u}} (vertex : K.V)
    (edge : K.edges) :
    edge ∈ GluingDatum.incidentEdges vertex ↔
      (edge : K.V × K.V).1 = vertex ∨ (edge : K.V × K.V).2 = vertex := by
  rw [GluingDatum.incidentEdges, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ edge, h⟩⟩

/-- The occurrence bijection carries the occurrences incident to a target
vertex onto the occurrences incident to its image. -/
theorem incidentEdges_map (φ : CFGraphIso G H) (y : H.V) :
    GluingDatum.incidentEdges y
      = (GluingDatum.incidentEdges (φ.vertexEquiv.symm y)).map
        (edgeEquiv φ).toEmbedding := by
  ext e
  rw [Finset.mem_map_equiv, mem_incidentEdges_iff_local,
    mem_incidentEdges_iff_local]
  have hKey := edgeEquiv_symm_key φ e
  rw [mappedEdgeKey, edgeKey, Sym2.eq_iff] at hKey
  rcases hKey with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]
    simp [Equiv.eq_symm_apply]
  · rw [← h1, ← h2]
    simp [Equiv.eq_symm_apply, or_comm]

/-! ## Riemann--Hurwitz -/

/-- The transported local Riemann--Hurwitz condition at a target vertex is the
original condition at its preimage. -/
theorem riemannHurwitzAtTargetVertex_transport (φ : CFGraphIso G H)
    (data : GluingDatum G degree) (y : H.V)
    (h : data.RiemannHurwitzAtTargetVertex (φ.vertexEquiv.symm y)) :
    (transport φ data).RiemannHurwitzAtTargetVertex y := by
  intro sheet
  have hCard : (GluingDatum.incidentEdges y).card
      = (GluingDatum.incidentEdges (φ.vertexEquiv.symm y)).card := by
    rw [incidentEdges_map φ y, Finset.card_map]
  have hSum :
      (∑ edge ∈ GluingDatum.incidentEdges y,
        (((transport φ data).edgePartition edge).blockCountWithin
          ((transport φ data).vertexPartition y) sheet : ℤ))
      = ∑ edge ∈ GluingDatum.incidentEdges (φ.vertexEquiv.symm y),
        ((data.edgePartition edge).blockCountWithin
          (data.vertexPartition (φ.vertexEquiv.symm y)) sheet : ℤ) := by
    rw [incidentEdges_map φ y, Finset.sum_map]
    refine Finset.sum_congr rfl fun edge _ => ?_
    rw [Equiv.coe_toEmbedding, transport_edgePartition_apply]
    rfl
  have hGoal := h sheet
  rw [hSum, hCard]
  exact hGoal

/-- Transporting a gluing datum preserves the local Riemann--Hurwitz
condition. -/
theorem riemannHurwitz_transport (φ : CFGraphIso G H)
    (data : GluingDatum G degree) (h : data.RiemannHurwitz) :
    (transport φ data).RiemannHurwitz := by
  intro y
  exact riemannHurwitzAtTargetVertex_transport φ data y
    (fun sheet => h (φ.vertexEquiv.symm y) sheet)

/-! ## Validity -/

/-- Transporting a gluing datum along an isomorphism of target graphs
preserves validity. -/
theorem valid_transport (φ : CFGraphIso G H) (data : GluingDatum G degree)
    (h : data.Valid) : (transport φ data).Valid :=
  ⟨connected_transport φ data h.1, riemannHurwitz_transport φ data h.2⟩

end DraismaVargas.Infrastructure.GluingTransport
