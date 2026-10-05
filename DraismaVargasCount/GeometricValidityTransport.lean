module

public import DraismaVargasCount.GeometricTransport

@[expose] public section

/-!
# Geometric transport of target invariants and validity

Explicit orientation-independent occurrence bijections preserve target
incidence counts, graph multiplicities, genus, leaves, and the local
Riemann--Hurwitz inequalities. No count quotient is modified here.
-/

namespace DraismaVargas.Count.GeometricDatumIso

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open Utilities Utilities.Certificate

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

theorem mem_incidentEdges_map (iso : GeometricDatumIso first second) (vertex : target₁.V)
    (edge : target₁.edges) :
    iso.targetEdge edge ∈ GluingDatum.incidentEdges (iso.targetVertex vertex) ↔
      edge ∈ GluingDatum.incidentEdges vertex := by
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  exact iso.target_incident_map_iff edge vertex

theorem incidentEdges_card_map (iso : GeometricDatumIso first second) (vertex : target₁.V) :
    (GluingDatum.incidentEdges (iso.targetVertex vertex)).card =
      (GluingDatum.incidentEdges vertex).card := by
  refine (Finset.card_bij (fun edge _ ↦ iso.targetEdge edge) ?_ ?_ ?_).symm
  · exact fun edge hEdge ↦ (iso.mem_incidentEdges_map vertex edge).mpr hEdge
  · exact fun _ _ _ _ h ↦ iso.targetEdge.injective h
  · intro edge hEdge
    refine ⟨iso.targetEdge.symm edge, ?_, iso.targetEdge.apply_symm_apply edge⟩
    refine (iso.mem_incidentEdges_map vertex _).mp ?_
    rwa [Equiv.apply_symm_apply]

/-- Every target edge multiplicity is preserved. -/
theorem targetNumEdges_map (iso : GeometricDatumIso first second) (left right : target₁.V) :
    num_edges target₂ (iso.targetVertex left) (iso.targetVertex right) =
      num_edges target₁ left right := by
  rw [← GluingTransport.card_edgeKey_fiber target₂ (iso.targetVertex left)
      (iso.targetVertex right),
    ← GluingTransport.card_edgeKey_fiber target₁ left right]
  refine Fintype.card_congr (Equiv.subtypeEquiv iso.targetEdge ?_).symm
  intro edge
  unfold GluingTransport.edgeKey
  rcases iso.ends edge with h | h <;> rw [h] <;>
    simp only [Sym2.eq_iff, Equiv.apply_eq_iff_eq]
  tauto

/-- The target relabelling is an adjacency-preserving vertex equivalence. -/
def targetLaplacianEquiv (iso : GeometricDatumIso first second) :
    LaplacianEquiv target₁ target₂ where
  toEquiv := iso.targetVertex
  num_edges_eq := iso.targetNumEdges_map

theorem targetConnected_map (iso : GeometricDatumIso first second)
    (hConnected : graph_connected target₁) : graph_connected target₂ :=
  iso.targetLaplacianEquiv.graphConnected hConnected

theorem targetEdgeCard_map (iso : GeometricDatumIso first second) :
    Multiset.card target₂.edges = Multiset.card target₁.edges := by
  rw [← Multiset.card_coe target₂.edges, ← Multiset.card_coe target₁.edges]
  exact Fintype.card_congr iso.targetEdge.symm

theorem targetGenus_map (iso : GeometricDatumIso first second) : genus target₂ = genus target₁ := by
  unfold genus
  rw [iso.targetEdgeCard_map, Fintype.card_congr iso.targetVertex]

theorem genus_sourceGraph (data : GluingDatum target₁ degree) :
    genus data.sourceGraph =
      (Fintype.card data.SourceEdge : ℤ) - (Fintype.card data.SourceVertex : ℤ) + 1 := by
  unfold genus
  have hEdges : Multiset.card data.sourceGraph.edges = Fintype.card data.SourceEdge := by
    show Multiset.card
      ((Finset.univ : Finset data.SourceEdge).val.map data.sourceEnds) = _
    rw [Multiset.card_map]
    rfl
  rw [hEdges]
  congr 2

theorem sourceGenus_map (iso : GeometricDatumIso first second) :
    genus second.sourceGraph = genus first.sourceGraph := by
  rw [genus_sourceGraph, genus_sourceGraph,
    Fintype.card_congr iso.sourceEdgeEquiv.symm,
    Fintype.card_congr iso.sourceVertexEquiv.symm]

/-- Refinement counts are preserved at an incident target vertex. -/
theorem blockCountWithin_map (iso : GeometricDatumIso first second) (vertex : target₁.V)
    (edge : target₁.edges) (hIncident : edge ∈ GluingDatum.incidentEdges vertex)
    (sheet : Fin degree) :
    (second.edgePartition (iso.targetEdge edge)).blockCountWithin
        (second.vertexPartition (iso.targetVertex vertex)) (iso.vertexPerm vertex sheet) =
      (first.edgePartition edge).blockCountWithin (first.vertexPartition vertex) sheet := by
  classical
  have hPoint : ∀ item : Fin degree,
      (first.vertexPartition vertex).Rel
        ((iso.edgePerm edge).trans (iso.vertexPerm vertex).symm item) item := by
    exact iso.compatible edge vertex (Finset.mem_filter.mp hIncident).2
  have hSplit : (first.edgePartition edge).relabel (iso.edgePerm edge) =
      ((first.edgePartition edge).relabel
        ((iso.edgePerm edge).trans (iso.vertexPerm vertex).symm)).relabel
          (iso.vertexPerm vertex) := by
    rw [SheetPartition.relabel_relabel]
    congr 1
    ext item
    simp
  rw [iso.edgePartition edge, iso.vertexPartition vertex, hSplit,
    SheetPartition.relabel_blockCountWithin,
    SheetPartition.relabel_blockCountWithin_fixed_of_pointwise _ _ _ hPoint]

/-- The local Riemann--Hurwitz inequalities transport. -/
theorem riemannHurwitz_map (iso : GeometricDatumIso first second)
    (hRiemannHurwitz : first.RiemannHurwitz) : second.RiemannHurwitz := by
  classical
  intro vertex sheet
  obtain ⟨vertex, rfl⟩ := iso.targetVertex.surjective vertex
  obtain ⟨sheet, rfl⟩ := (iso.vertexPerm vertex).surjective sheet
  have hBase := hRiemannHurwitz vertex sheet
  have hSum : (∑ edge ∈ GluingDatum.incidentEdges (iso.targetVertex vertex),
      ((second.edgePartition edge).blockCountWithin
        (second.vertexPartition (iso.targetVertex vertex))
          (iso.vertexPerm vertex sheet) : ℤ)) =
      ∑ edge ∈ GluingDatum.incidentEdges vertex,
        ((first.edgePartition edge).blockCountWithin
          (first.vertexPartition vertex) sheet : ℤ) := by
    refine (Finset.sum_bij (fun edge _ ↦ iso.targetEdge edge) ?_ ?_ ?_ ?_).symm
    · exact fun edge hEdge ↦ (iso.mem_incidentEdges_map vertex edge).mpr hEdge
    · exact fun _ _ _ _ h ↦ iso.targetEdge.injective h
    · intro edge hEdge
      refine ⟨iso.targetEdge.symm edge, ?_, iso.targetEdge.apply_symm_apply edge⟩
      refine (iso.mem_incidentEdges_map vertex _).mp ?_
      rwa [Equiv.apply_symm_apply]
    · intro edge hEdge
      rw [iso.blockCountWithin_map vertex edge hEdge sheet]
  have hCard := iso.incidentEdges_card_map vertex
  have hBlock : (second.vertexPartition (iso.targetVertex vertex)).blockCard
      (iso.vertexPerm vertex sheet) =
      (first.vertexPartition vertex).blockCard sheet := by
    rw [iso.vertexPartition vertex, SheetPartition.relabel_blockCard]
  change (∑ edge ∈ GluingDatum.incidentEdges (iso.targetVertex vertex),
      ((second.edgePartition edge).blockCountWithin
        (second.vertexPartition (iso.targetVertex vertex))
          (iso.vertexPerm vertex sheet) : ℤ)) - 2 ≥
    ((second.vertexPartition (iso.targetVertex vertex)).blockCard
      (iso.vertexPerm vertex sheet) : ℤ) *
      (((GluingDatum.incidentEdges (iso.targetVertex vertex)).card : ℤ) - 2)
  rw [hSum, hCard, hBlock]
  exact hBase

theorem valid_map (iso : GeometricDatumIso first second) (hValid : first.Valid) : second.Valid :=
  ⟨iso.connected hValid.1, iso.riemannHurwitz_map hValid.2⟩


end DraismaVargas.Count.GeometricDatumIso
