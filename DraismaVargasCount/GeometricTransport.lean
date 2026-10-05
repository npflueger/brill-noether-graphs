module

public import DraismaVargasCount.Transport

@[expose] public section

/-!
# Orientation-independent transport of gluing data

An explicit target occurrence bijection preserves unordered endpoints, while
compatible local sheet permutations preserve the glued source incidences and
indices. Strict `Transport.DatumIso` embeds into this API; actual
`GluingTransport.transport` also supplies an isomorphism even when endpoint
storage orientations change. This module does not change any counting quotient.
-/

namespace DraismaVargas.Count

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open Utilities Utilities.Certificate

def UnorderedEnds {α β : Type*} (vertices : α ≃ β) (first : α × α) (second : β × β) : Prop :=
  second = (vertices first.1, vertices first.2) ∨
    second = (vertices first.2, vertices first.1)

theorem UnorderedEnds.refl {α : Type*} (ends : α × α) :
    UnorderedEnds (Equiv.refl α) ends ends := Or.inl rfl

theorem UnorderedEnds.symm {α β : Type*} {vertices : α ≃ β} {first : α × α}
    {second : β × β} (h : UnorderedEnds vertices first second) :
    UnorderedEnds vertices.symm second first := by
  rcases h with h | h <;> rw [h] <;> simp [UnorderedEnds]

theorem UnorderedEnds.trans {α β γ : Type*} {v₁ : α ≃ β} {v₂ : β ≃ γ}
    {first : α × α} {second : β × β} {third : γ × γ}
    (h : UnorderedEnds v₁ first second) (h' : UnorderedEnds v₂ second third) :
    UnorderedEnds (v₁.trans v₂) first third := by
  rcases h with h | h <;> rcases h' with h' | h' <;>
    simp [UnorderedEnds, h', h]

theorem UnorderedEnds.incident_iff {α β : Type*} {vertices : α ≃ β}
    {first : α × α} {second : β × β} (h : UnorderedEnds vertices first second) (v : α) :
    (second.1 = vertices v ∨ second.2 = vertices v) ↔ (first.1 = v ∨ first.2 = v) := by
  rcases h with h | h <;> rw [h] <;> simp only [Equiv.apply_eq_iff_eq]
  exact or_comm

variable {target₁ target₂ target₃ : CFGraph} {degree : ℕ}

structure GeometricDatumIso (first : GluingDatum target₁ degree)
    (second : GluingDatum target₂ degree) where
  targetVertex : target₁.V ≃ target₂.V
  targetEdge : target₁.edges ≃ target₂.edges
  ends : ∀ edge : target₁.edges,
    UnorderedEnds targetVertex (edge : target₁.V × target₁.V)
      (targetEdge edge : target₂.V × target₂.V)
  vertexPerm : target₁.V → Equiv.Perm (Fin degree)
  edgePerm : target₁.edges → Equiv.Perm (Fin degree)
  vertexPartition : ∀ vertex : target₁.V,
    second.vertexPartition (targetVertex vertex) =
      (first.vertexPartition vertex).relabel (vertexPerm vertex)
  edgePartition : ∀ edge : target₁.edges,
    second.edgePartition (targetEdge edge) =
      (first.edgePartition edge).relabel (edgePerm edge)
  compatible : ∀ (edge : target₁.edges) (vertex : target₁.V),
    ((edge : target₁.V × target₁.V).1 = vertex ∨
      (edge : target₁.V × target₁.V).2 = vertex) → ∀ sheet : Fin degree,
    (first.vertexPartition vertex).Rel ((vertexPerm vertex).symm (edgePerm edge sheet)) sheet

namespace GeometricDatumIso

variable {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
  {third : GluingDatum target₃ degree}

def ofStrict (iso : Transport.DatumIso first second) : GeometricDatumIso first second where
  targetVertex := iso.targetVertex
  targetEdge := iso.targetEdge
  ends edge := Or.inl (Prod.ext (iso.ends_fst edge) (iso.ends_snd edge))
  vertexPerm := iso.vertexPerm
  edgePerm := iso.edgePerm
  vertexPartition := iso.vertexPartition
  edgePartition := iso.edgePartition
  compatible edge vertex hv sheet := by
    rcases hv with h | h
    · subst vertex
      exact iso.compatible_fst edge sheet
    · subst vertex
      exact iso.compatible_snd edge sheet

def refl (data : GluingDatum target₁ degree) : GeometricDatumIso data data :=
  ofStrict (Transport.DatumIso.refl data)

theorem target_incident_map_iff (iso : GeometricDatumIso first second)
    (edge : target₁.edges) (vertex : target₁.V) :
    (((iso.targetEdge edge : target₂.V × target₂.V).1 = iso.targetVertex vertex ∨
      (iso.targetEdge edge : target₂.V × target₂.V).2 = iso.targetVertex vertex)) ↔
      ((edge : target₁.V × target₁.V).1 = vertex ∨
        (edge : target₁.V × target₁.V).2 = vertex) :=
  (iso.ends edge).incident_iff vertex

def symm (iso : GeometricDatumIso first second) : GeometricDatumIso second first where
  targetVertex := iso.targetVertex.symm
  targetEdge := iso.targetEdge.symm
  ends edge := by
    have h := (iso.ends (iso.targetEdge.symm edge)).symm
    simpa only [Equiv.apply_symm_apply] using h
  vertexPerm vertex := (iso.vertexPerm (iso.targetVertex.symm vertex)).symm
  edgePerm edge := (iso.edgePerm (iso.targetEdge.symm edge)).symm
  vertexPartition vertex := by
    have hForward := iso.vertexPartition (iso.targetVertex.symm vertex)
    rw [Equiv.apply_symm_apply] at hForward
    rw [hForward, Transport.DatumIso.relabel_symm_relabel]
  edgePartition edge := by
    have hForward := iso.edgePartition (iso.targetEdge.symm edge)
    rw [Equiv.apply_symm_apply] at hForward
    rw [hForward, Transport.DatumIso.relabel_symm_relabel]
  compatible edge vertex hv sheet := by
    let old := iso.targetEdge.symm edge
    let oldVertex := iso.targetVertex.symm vertex
    have hold : (old : target₁.V × target₁.V).1 = oldVertex ∨
        (old : target₁.V × target₁.V).2 = oldVertex := by
      apply (iso.target_incident_map_iff old oldVertex).mp
      simpa only [old, oldVertex, Equiv.apply_symm_apply] using hv
    have hBase := iso.compatible old oldVertex hold ((iso.edgePerm old).symm sheet)
    rw [Equiv.apply_symm_apply] at hBase
    have hGoal := ((first.vertexPartition oldVertex).relabel_rel_iff
      (iso.vertexPerm oldVertex) ((iso.edgePerm old).symm sheet)
      ((iso.vertexPerm oldVertex).symm sheet)).mpr hBase.symm
    rw [Equiv.apply_symm_apply] at hGoal
    have hpart := iso.vertexPartition oldVertex
    simp only [oldVertex, Equiv.apply_symm_apply] at hpart
    rw [hpart]
    exact hGoal

def trans (left : GeometricDatumIso first second) (right : GeometricDatumIso second third) :
    GeometricDatumIso first third where
  targetVertex := left.targetVertex.trans right.targetVertex
  targetEdge := left.targetEdge.trans right.targetEdge
  ends edge := (left.ends edge).trans (right.ends (left.targetEdge edge))
  vertexPerm vertex := (left.vertexPerm vertex).trans (right.vertexPerm (left.targetVertex vertex))
  edgePerm edge := (left.edgePerm edge).trans (right.edgePerm (left.targetEdge edge))
  vertexPartition vertex := by
    rw [Equiv.trans_apply, right.vertexPartition, left.vertexPartition,
      SheetPartition.relabel_relabel]
  edgePartition edge := by
    rw [Equiv.trans_apply, right.edgePartition, left.edgePartition,
      SheetPartition.relabel_relabel]
  compatible edge vertex hv sheet := by
    have hRight := right.compatible (left.targetEdge edge) (left.targetVertex vertex)
      ((left.target_incident_map_iff edge vertex).mpr hv) (left.edgePerm edge sheet)
    rw [left.vertexPartition] at hRight
    have hPulled := ((first.vertexPartition vertex).relabel_rel_iff
        (left.vertexPerm vertex)
        ((left.vertexPerm vertex).symm ((right.vertexPerm (left.targetVertex vertex)).symm
          (right.edgePerm (left.targetEdge edge) (left.edgePerm edge sheet))))
        ((left.vertexPerm vertex).symm (left.edgePerm edge sheet))).mp (by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hRight)
    exact hPulled.trans (left.compatible edge vertex hv sheet)

noncomputable def ofTargetIso (φ : CFGraphIso target₁ target₂) (data : GluingDatum target₁ degree) :
    GeometricDatumIso data (GluingTransport.transport φ data) where
  targetVertex := φ.vertexEquiv
  targetEdge := GluingTransport.edgeEquiv φ
  ends := GluingTransport.edgeEquiv_ends φ
  vertexPerm _ := Equiv.refl _
  edgePerm _ := Equiv.refl _
  vertexPartition vertex := by
    rw [GluingTransport.transport_vertexPartition_apply, Transport.DatumIso.relabel_refl]
  edgePartition edge := by
    rw [GluingTransport.transport_edgePartition_apply, Transport.DatumIso.relabel_refl]
  compatible _ _ _ _ := rfl

theorem vertexRepr_iff (iso : GeometricDatumIso first second) (vertex : target₁.V)
    (sheet : Fin degree) :
    (second.vertexPartition (iso.targetVertex vertex)).repr (iso.vertexPerm vertex sheet) =
        iso.vertexPerm vertex sheet ↔
      (first.vertexPartition vertex).repr sheet = sheet := by
  rw [iso.vertexPartition vertex]
  simp [SheetPartition.relabel]

theorem edgeRepr_iff (iso : GeometricDatumIso first second) (edge : target₁.edges)
    (sheet : Fin degree) :
    (second.edgePartition (iso.targetEdge edge)).repr (iso.edgePerm edge sheet) =
        iso.edgePerm edge sheet ↔ (first.edgePartition edge).repr sheet = sheet := by
  rw [iso.edgePartition edge]
  simp [SheetPartition.relabel]

def vertexPairEquiv (iso : GeometricDatumIso first second) :
    target₁.V × Fin degree ≃ target₂.V × Fin degree where
  toFun item := (iso.targetVertex item.1, iso.vertexPerm item.1 item.2)
  invFun item := (iso.targetVertex.symm item.1,
    (iso.vertexPerm (iso.targetVertex.symm item.1)).symm item.2)
  left_inv := by rintro ⟨vertex, sheet⟩; simp
  right_inv := by rintro ⟨vertex, sheet⟩; simp

def edgePairEquiv (iso : GeometricDatumIso first second) :
    target₁.edges × Fin degree ≃ target₂.edges × Fin degree where
  toFun item := (iso.targetEdge item.1, iso.edgePerm item.1 item.2)
  invFun item := (iso.targetEdge.symm item.1,
    (iso.edgePerm (iso.targetEdge.symm item.1)).symm item.2)
  left_inv := by rintro ⟨edge, sheet⟩; simp
  right_inv := by rintro ⟨edge, sheet⟩; simp

def sourceVertexEquiv (iso : GeometricDatumIso first second) :
    first.SourceVertex ≃ second.SourceVertex :=
  Equiv.subtypeEquiv iso.vertexPairEquiv fun item ↦
    (iso.vertexRepr_iff item.1 item.2).symm

def sourceEdgeEquiv (iso : GeometricDatumIso first second) :
    first.SourceEdge ≃ second.SourceEdge :=
  Equiv.subtypeEquiv iso.edgePairEquiv fun item ↦
    (iso.edgeRepr_iff item.1 item.2).symm

theorem sourceEndpoint_edge (iso : GeometricDatumIso first second)
    (edge : target₁.edges) (vertex : target₁.V)
    (hv : (edge : target₁.V × target₁.V).1 = vertex ∨
      (edge : target₁.V × target₁.V).2 = vertex) (sheet : Fin degree) :
    second.sourceEndpoint (iso.targetVertex vertex) (iso.edgePerm edge sheet) =
      iso.sourceVertexEquiv (first.sourceEndpoint vertex sheet) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (second.vertexPartition (iso.targetVertex vertex)).repr (iso.edgePerm edge sheet) =
      iso.vertexPerm vertex ((first.vertexPartition vertex).repr sheet)
    rw [iso.vertexPartition]
    change iso.vertexPerm vertex ((first.vertexPartition vertex).repr
      ((iso.vertexPerm vertex).symm (iso.edgePerm edge sheet))) = _
    exact congrArg (iso.vertexPerm vertex) (iso.compatible edge vertex hv sheet)

theorem sourceEnds_map (iso : GeometricDatumIso first second) (edge : first.SourceEdge) :
    UnorderedEnds iso.sourceVertexEquiv (first.sourceEnds edge)
      (second.sourceEnds (iso.sourceEdgeEquiv edge)) := by
  have hfst := iso.sourceEndpoint_edge edge.1.1 (edge.1.1 : target₁.V × target₁.V).1
    (Or.inl rfl) edge.1.2
  have hsnd := iso.sourceEndpoint_edge edge.1.1 (edge.1.1 : target₁.V × target₁.V).2
    (Or.inr rfl) edge.1.2
  rcases iso.ends edge.1.1 with h | h
  · apply Or.inl
    change (second.sourceEndpoint (iso.targetEdge edge.1.1 : target₂.V × target₂.V).1
        (iso.edgePerm edge.1.1 edge.1.2),
      second.sourceEndpoint (iso.targetEdge edge.1.1 : target₂.V × target₂.V).2
        (iso.edgePerm edge.1.1 edge.1.2)) = _
    rw [h]
    exact Prod.ext hfst hsnd
  · apply Or.inr
    change (second.sourceEndpoint (iso.targetEdge edge.1.1 : target₂.V × target₂.V).1
        (iso.edgePerm edge.1.1 edge.1.2),
      second.sourceEndpoint (iso.targetEdge edge.1.1 : target₂.V × target₂.V).2
        (iso.edgePerm edge.1.1 edge.1.2)) = _
    rw [h]
    exact Prod.ext hsnd hfst

theorem incident_map_iff (iso : GeometricDatumIso first second) (edge : first.SourceEdge)
    (vertex : first.SourceVertex) :
    Incident second (iso.sourceEdgeEquiv edge) (iso.sourceVertexEquiv vertex) ↔
      Incident first edge vertex :=
  (iso.sourceEnds_map edge).incident_iff vertex

theorem sourceEdgeIndex_map (iso : GeometricDatumIso first second) (edge : first.SourceEdge) :
    second.sourceEdgeIndex (iso.sourceEdgeEquiv edge) = first.sourceEdgeIndex edge := by
  change (second.edgePartition (iso.targetEdge edge.1.1)).blockCard
    (iso.edgePerm edge.1.1 edge.1.2) = _
  rw [iso.edgePartition edge.1.1]
  exact (first.edgePartition edge.1.1).relabel_blockCard (iso.edgePerm edge.1.1) edge.1.2

theorem num_edges_map (iso : GeometricDatumIso first second)
    (left right : first.SourceVertex) :
    num_edges second.sourceGraph (iso.sourceVertexEquiv left) (iso.sourceVertexEquiv right) =
      num_edges first.sourceGraph left right := by
  rw [GluingDatum.SheetRelabeling.num_edges_sourceGraph_eq_sum,
    GluingDatum.SheetRelabeling.num_edges_sourceGraph_eq_sum,
    ← iso.sourceEdgeEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro edge _
  rcases iso.sourceEnds_map edge with h | h <;> rw [h] <;>
    simp only [Prod.ext_iff, Equiv.apply_eq_iff_eq]
  congr 1
  apply propext
  tauto

def sourceGraphLaplacianEquiv (iso : GeometricDatumIso first second) :
    LaplacianEquiv first.sourceGraph second.sourceGraph where
  toEquiv := iso.sourceVertexEquiv
  num_edges_eq := iso.num_edges_map

theorem connected (iso : GeometricDatumIso first second) (h : first.Connected) :
    second.Connected := iso.sourceGraphLaplacianEquiv.graphConnected h

end GeometricDatumIso
end DraismaVargas.Count

