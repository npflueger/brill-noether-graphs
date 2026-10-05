module

public import DraismaVargas.Infrastructure.GluingTransport
public import DraismaVargas.LocalCases.SheetRelabelPruning

@[expose] public section

/-!
# Literal source isomorphism and pruning under a target relabelling

The source's compatible-labelling rule allows target graph isomorphisms as
well as sheet relabellings. Extend the existing occurrence-safe target
transport by its actual source equivalences and pruning correspondence.
Stored target/source edge orientations may reverse.
-/

namespace DraismaVargas.LocalCases.TargetRelabelPruning

open Utilities Utilities.Certificate DraismaVargas.Infrastructure
open GluingTransport W4StableSource SheetRelabelPruning

variable {G H : CFGraph} {degree : ℕ} (φ : CFGraphIso G H)
  (data : GluingDatum G degree)

theorem sourceVertexMap_injective : Function.Injective (sourceVertexMap φ data) := by
  intro first second h
  apply Subtype.ext
  exact Prod.ext (φ.vertexEquiv.injective (congrArg (fun v ↦ v.1.1) h))
    (congrArg (fun v ↦ v.1.2) h)

noncomputable def sourceVertexEquiv : data.SourceVertex ≃ (transport φ data).SourceVertex :=
  Equiv.ofBijective (sourceVertexMap φ data)
    ⟨sourceVertexMap_injective φ data, sourceVertexMap_surjective φ data⟩

theorem sourceEdgeMap_injective : Function.Injective (sourceEdgeMap φ data) := by
  intro first second h
  apply Subtype.ext
  exact Prod.ext ((edgeEquiv φ).injective (congrArg (fun e ↦ e.1.1) h))
    (congrArg (fun e ↦ e.1.2) h)

theorem sourceEdgeMap_surjective : Function.Surjective (sourceEdgeMap φ data) := by
  intro edge
  let old : data.SourceEdge := ⟨((edgeEquiv φ).symm edge.1.1, edge.1.2), edge.2⟩
  refine ⟨old, Subtype.ext (Prod.ext ?_ rfl)⟩
  exact (edgeEquiv φ).apply_symm_apply edge.1.1

noncomputable def sourceEdgeEquiv : data.SourceEdge ≃ (transport φ data).SourceEdge :=
  Equiv.ofBijective (sourceEdgeMap φ data)
    ⟨sourceEdgeMap_injective φ data, sourceEdgeMap_surjective φ data⟩

theorem sourceEnds_map (edge : data.SourceEdge) :
    (transport φ data).sourceEnds (sourceEdgeEquiv φ data edge) =
        (sourceVertexEquiv φ data (data.sourceEnds edge).1,
          sourceVertexEquiv φ data (data.sourceEnds edge).2) ∨
      (transport φ data).sourceEnds (sourceEdgeEquiv φ data edge) =
        (sourceVertexEquiv φ data (data.sourceEnds edge).2,
          sourceVertexEquiv φ data (data.sourceEnds edge).1) :=
  sourceEnds_sourceEdgeMap φ data edge

/-- Unordered multiplicities are unaffected by possible stored-orientation reversals. -/
theorem num_edges_sourceVertexEquiv (first second : data.SourceVertex) :
    num_edges (transport φ data).sourceGraph
      (sourceVertexEquiv φ data first) (sourceVertexEquiv φ data second) =
        num_edges data.sourceGraph first second := by
  rw [GluingDatum.SheetRelabeling.num_edges_sourceGraph_eq_sum,
    GluingDatum.SheetRelabeling.num_edges_sourceGraph_eq_sum,
    ← (sourceEdgeEquiv φ data).sum_comp]
  apply Finset.sum_congr rfl
  intro edge _
  rcases sourceEnds_map φ data edge with h | h <;> rw [h] <;>
    simp only [Prod.ext_iff, Equiv.apply_eq_iff_eq]
  congr 1
  apply propext
  tauto

noncomputable def sourceGraphLaplacianEquiv :
    LaplacianEquiv data.sourceGraph (transport φ data).sourceGraph where
  toEquiv := sourceVertexEquiv φ data
  num_edges_eq := num_edges_sourceVertexEquiv φ data

theorem incident_sourceEdgeEquiv_iff (edge : data.SourceEdge) (vertex : data.SourceVertex) :
    Incident (transport φ data) (sourceEdgeEquiv φ data edge) (sourceVertexEquiv φ data vertex) ↔
      Incident data edge vertex := by
  unfold Incident
  rcases sourceEnds_map φ data edge with h | h <;> rw [h] <;>
    simp only [Equiv.apply_eq_iff_eq]
  exact or_comm

/-- Pruning respects unordered endpoint transport as well as ordered transport. -/
theorem isDangling_map_unordered {target₁ target₂ : CFGraph} {d₁ d₂ : ℕ}
    {first : GluingDatum target₁ d₁} {second : GluingDatum target₂ d₂}
    (equivalence : LaplacianEquiv first.sourceGraph second.sourceGraph)
    (hConnected : second.Connected) (edge : first.SourceEdge) (other : second.SourceEdge)
    (hEnds : second.sourceEnds other =
        (equivalence.toEquiv (first.sourceEnds edge).1, equivalence.toEquiv (first.sourceEnds edge).2) ∨
      second.sourceEnds other =
        (equivalence.toEquiv (first.sourceEnds edge).2, equivalence.toEquiv (first.sourceEnds edge).1))
    (hDangling : IsDangling first edge) : IsDangling second other := by
  rcases hEnds with h | h
  · exact SheetRelabelPruning.isDangling_map second equivalence hConnected edge other h hDangling
  · unfold IsDangling
    rw [h]
    unfold IsDangling at hDangling
    rcases hDangling with hDangling | hDangling
    · obtain ⟨dangling⟩ := hDangling
      exact Or.inr ⟨mapDanglingSide equivalence hConnected dangling⟩
    · obtain ⟨dangling⟩ := hDangling
      exact Or.inl ⟨mapDanglingSide equivalence hConnected dangling⟩

/-- The actual target-transport source occurrence dangles exactly when its
original occurrence does; edge orientations are immaterial. -/
theorem isDangling_sourceEdgeEquiv_iff (hConnected : data.Connected) (edge : data.SourceEdge) :
    IsDangling (transport φ data) (sourceEdgeEquiv φ data edge) ↔ IsDangling data edge := by
  constructor
  · intro hDangling
    apply isDangling_map_unordered (sourceGraphLaplacianEquiv φ data).symm hConnected
      (sourceEdgeEquiv φ data edge) edge _ hDangling
    rcases sourceEnds_map φ data edge with h | h
    · left
      rw [h]
      change data.sourceEnds edge =
        ((sourceVertexEquiv φ data).symm (sourceVertexEquiv φ data (data.sourceEnds edge).1),
          (sourceVertexEquiv φ data).symm (sourceVertexEquiv φ data (data.sourceEnds edge).2))
      simp only [Equiv.symm_apply_apply]
    · right
      rw [h]
      change data.sourceEnds edge =
        ((sourceVertexEquiv φ data).symm (sourceVertexEquiv φ data (data.sourceEnds edge).1),
          (sourceVertexEquiv φ data).symm (sourceVertexEquiv φ data (data.sourceEnds edge).2))
      simp only [Equiv.symm_apply_apply]
  · exact isDangling_map_unordered (sourceGraphLaplacianEquiv φ data)
      (connected_transport φ data hConnected) edge (sourceEdgeEquiv φ data edge)
      (sourceEnds_map φ data edge)

theorem sourceEdgeIndex_map (edge : data.SourceEdge) :
    (transport φ data).sourceEdgeIndex (sourceEdgeEquiv φ data edge) = data.sourceEdgeIndex edge := by
  change ((transport φ data).edgePartition (edgeEquiv φ edge.1.1)).blockCard edge.1.2 = _
  rw [transport_edgePartition_apply]
  rfl

end DraismaVargas.LocalCases.TargetRelabelPruning
