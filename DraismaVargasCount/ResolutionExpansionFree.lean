import DraismaVargasCount.M11WallExhaustion

/-!
# Resolution expansions with decoupled endpoint permutations

Draisma--Vargas Part I, Figure 32 (the M-11 local resolutions) and the subsection "Trees
contracting to T₀" (`sub-graphs-to-T0`: the expansion of the target at a wall vertex); the
construction refines `ResolutionExpansion` and `M11WallExhaustion`.

## Why

`ResolutionExpansion.lift` puts the wall's merged sheet permutation `V` on both
expanded endpoints and on the regrown occurrence, so its `Transport` asks each wall
occurrence permutation `E` to agree with `V` modulo the *endpoint* partitions.  That is too
rigid: a frame relabelled by a global sheet permutation `σ` is in the wall's own class, but `V`
is pinned by the merged partition's stored representatives while `E = σ`.  So the receipt
`M11WallExhaustion.Covers`, which is stated with `Transport`, fails at every split wall.

## The decoupled transport

`TransportFree` carries three free permutations, `oldPerm`, `freshPerm`, `newPerm`,
for the retained wall copy, the fresh vertex and the regrown occurrence.  Each endpoint
permutation need only agree with `V` modulo the **merged** partition (`old_merged`,
`fresh_merged`); the three resolution relabels, the regrown occurrence's two
compatibilities and `endpoint_compatible` are stated against the endpoint they belong
to.  `ofTransport` embeds `ResolutionExpansion.Transport` (all three `:= V`).

* §2 `liftFree` and its dictionaries `sourceVertexMap_liftFree` (the only place the
  merged agreement is used) and `retainedSourceEdge_liftFree` (untouched by the free
  permutations).
* §3 `incomingResolution_congr`, `incomingResolution_globalRelabel`: relabelling a frame by a
  global sheet permutation relabels its presented resolution, literally (the normalization is
  sheet-blind).  This is what lets a relabelled split frame be received by the wall's own frame
  at the split placement, with all three free permutations equal to `σ⁻¹`.
* §4 `transIsoFree`, `frameDatumFree`, `source_squareFree`, `edge_squareFree`,
  `frameIsoFree`, `CoversFree`, `exists_cls_eq_free`, `cls_surjective_free`, and the
  weaker existential receipt `CoversFreeSome` with `exists_cls_eq_freeSome`,
  `card_le_of_index_free`, `starEquivFree`, `card_eq_of_index_free`.  Generic in the
  wall: no valency, family or figure enters except through the
  `memberPlacement`/`memberResolution` the index is stated with.
  `coversFree_of_covers`: the decoupled receipt loses nothing `Covers` had.

`TransportFree`, `liftFree` and `frameIsoFree` are used by `M11StarParityFree` and
`ValencyThreeRigidity`.

## Remarks

* `CoversFree` is `M11WallExhaustion.Covers` with `Transport` replaced by
  `Nonempty TransportFree`, and is implied by `Covers` (`coversFree_of_covers`).
  `CoversFreeSome` is the same, quantifying one limit isomorphism per star member instead of
  all, and is implied by `CoversFree` (`coversFreeSome_of_coversFree`).  Both are hypotheses of
  every §4 exhaustion statement; `M11StarParityFree` shows that at an M-11 wall with an
  incoherent member even `CoversFreeSome` fails, and handles that family by a census of
  positions instead.
* **The `∀ iso` form may be false where the `∃ iso` form is true.**  A limit isomorphism
  differing from a good one by a wall automorphism that moves one occurrence's sheets
  inside a merged block would violate `endpoint_compatible` at a discrete endpoint.
* **`M11WallExhaustion.Separates`** remains a hypothesis of `starEquivFree` /
  `card_eq_of_index_free`.
* The index is stated with `memberPlacement` (the divalent census of `M11WallExhaustion` §2),
  so §4 applies verbatim only at divalent walls; other valencies need their own member normal
  form.
-/

namespace DraismaVargas.Count.ResolutionExpansionFree

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open TargetExpansion
open ResolutionM11 (LocalResolution)

variable {target otherTarget : CFGraph} {degree : ℕ}

/-! ## 1.  The decoupled transport -/

/-- The sheet permutation a lift puts on each expanded vertex: `oldPerm` on the
retained wall copy, `freshPerm` on the fresh vertex, the base permutation
elsewhere. -/
def endpointPerm {first : GluingDatum target degree} {second : GluingDatum otherTarget degree}
    (iso : GeometricDatumIso first second) (wall : target.V)
    (oldPerm freshPerm : Equiv.Perm (Fin degree)) : Vertex target → Equiv.Perm (Fin degree)
  | Sum.inl vertex => if vertex = wall then oldPerm else iso.vertexPerm vertex
  | Sum.inr _ => freshPerm

section EndpointPerm

variable {first : GluingDatum target degree} {second : GluingDatum otherTarget degree}
  (iso : GeometricDatumIso first second) (wall : target.V)
  (oldPerm freshPerm : Equiv.Perm (Fin degree))

@[simp] theorem endpointPerm_old_wall :
    endpointPerm iso wall oldPerm freshPerm (oldVertex target wall) = oldPerm := by
  simp [endpointPerm, oldVertex]

theorem endpointPerm_old_of_ne (vertex : target.V) (h : vertex ≠ wall) :
    endpointPerm iso wall oldPerm freshPerm (oldVertex target vertex) = iso.vertexPerm vertex := by
  simp [endpointPerm, oldVertex, h]

@[simp] theorem endpointPerm_fresh :
    endpointPerm iso wall oldPerm freshPerm (freshVertex target) = freshPerm := rfl

theorem endpointPerm_expandedEndpoint (right : target.edges → Bool) (edge : target.edges)
    (vertex : target.V) :
    endpointPerm iso wall oldPerm freshPerm (expandedEndpoint target wall right edge vertex) =
      if vertex = wall then (if right edge then freshPerm else oldPerm)
      else iso.vertexPerm vertex := by
  unfold expandedEndpoint
  by_cases hSide : right edge = true
  · by_cases hWall : vertex = wall
    · subst vertex; simp [hSide, endpointPerm, freshVertex]
    · simp [hSide, hWall, endpointPerm, oldVertex]
  · simp only [Bool.not_eq_true] at hSide
    by_cases hWall : vertex = wall
    · subst vertex; simp [hSide, endpointPerm, oldVertex]
    · simp [hSide, hWall, endpointPerm, oldVertex]

end EndpointPerm

/-- **The decoupled transport.**  `ResolutionExpansion.Transport` with the
wall's single merged permutation replaced, at the two expanded endpoints and on
the regrown occurrence, by three free permutations.  Each endpoint permutation
is only asked to agree with the base wall permutation modulo the **merged**
wall partition (`old_merged`, `fresh_merged`) -- which is all the source
contraction square needs -- and every finer condition is stated against the
endpoint it belongs to. -/
structure TransportFree {first : GluingDatum target degree}
    {second : GluingDatum otherTarget degree}
    (iso : GeometricDatumIso first second) (wall : target.V) (otherWall : otherTarget.V)
    (right : target.edges → Bool) (otherRight : otherTarget.edges → Bool)
    (resolution otherResolution : LocalResolution degree) where
  /-- The permutation on the retained wall copy. -/
  oldPerm : Equiv.Perm (Fin degree)
  /-- The permutation on the fresh vertex. -/
  freshPerm : Equiv.Perm (Fin degree)
  /-- The permutation on the regrown occurrence. -/
  newPerm : Equiv.Perm (Fin degree)
  /-- The wall vertex is matched. -/
  wall_map : iso.targetVertex wall = otherWall
  /-- The two side assignments agree along the occurrence bijection. -/
  side_map : ∀ edge : target.edges, otherRight (iso.targetEdge edge) = right edge
  /-- `oldPerm` agrees with the wall permutation modulo the merged partition. -/
  old_merged : ∀ sheet : Fin degree,
    (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (oldPerm sheet)) sheet
  /-- …and so does `freshPerm`. -/
  fresh_merged : ∀ sheet : Fin degree,
    (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (freshPerm sheet)) sheet
  /-- The retained endpoint partition is relabelled by `oldPerm`. -/
  left_relabel : otherResolution.left = resolution.left.relabel oldPerm
  /-- The fresh endpoint partition is relabelled by `freshPerm`. -/
  right_relabel : otherResolution.right = resolution.right.relabel freshPerm
  /-- The regrown occurrence partition is relabelled by `newPerm`. -/
  newEdge_relabel : otherResolution.newEdge = resolution.newEdge.relabel newPerm
  /-- `newPerm` agrees with `oldPerm` modulo the retained endpoint partition. -/
  newEdge_old : ∀ sheet : Fin degree, resolution.left.Rel (oldPerm.symm (newPerm sheet)) sheet
  /-- …and with `freshPerm` modulo the fresh endpoint partition. -/
  newEdge_fresh : ∀ sheet : Fin degree,
    resolution.right.Rel (freshPerm.symm (newPerm sheet)) sheet
  /-- **The endpoint compatibility, against the endpoint's own permutation.** -/
  endpoint_compatible : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨ (edge : target.V × target.V).2 = wall) →
    ∀ sheet : Fin degree,
      (if right edge then resolution.right else resolution.left).Rel
        ((if right edge then freshPerm else oldPerm).symm (iso.edgePerm edge sheet)) sheet

/-- **`ResolutionExpansion.Transport` is the special case `oldPerm = freshPerm =
newPerm = iso.vertexPerm wall`.**  So nothing `Transport` receives is lost. -/
def ofTransport {first : GluingDatum target degree} {second : GluingDatum otherTarget degree}
    {iso : GeometricDatumIso first second} {wall : target.V} {otherWall : otherTarget.V}
    {right : target.edges → Bool} {otherRight : otherTarget.edges → Bool}
    {resolution otherResolution : LocalResolution degree}
    (transport : ResolutionExpansion.Transport iso wall otherWall right otherRight resolution
      otherResolution) :
    TransportFree iso wall otherWall right otherRight resolution otherResolution where
  oldPerm := iso.vertexPerm wall
  freshPerm := iso.vertexPerm wall
  newPerm := iso.vertexPerm wall
  wall_map := transport.wall_map
  side_map := transport.side_map
  old_merged sheet := by rw [Equiv.symm_apply_apply]; rfl
  fresh_merged sheet := by rw [Equiv.symm_apply_apply]; rfl
  left_relabel := transport.left_relabel
  right_relabel := transport.right_relabel
  newEdge_relabel := transport.newEdge_relabel
  newEdge_old sheet := by rw [Equiv.symm_apply_apply]; rfl
  newEdge_fresh sheet := by rw [Equiv.symm_apply_apply]; rfl
  endpoint_compatible edge hIncident sheet := by
    rw [ite_self]
    exact transport.endpoint_compatible edge hIncident sheet

/-! ## 2.  The lift -/

/-- The occurrence permutation of the lift: `newPerm` on the regrown
occurrence, the base permutation on every retained one. -/
noncomputable def edgePermFree {first : GluingDatum target degree}
    {second : GluingDatum otherTarget degree} (iso : GeometricDatumIso first second)
    (wall : target.V) (right : target.edges → Bool) (newPerm : Equiv.Perm (Fin degree))
    (edge : (graph target wall right).edges) : Equiv.Perm (Fin degree) :=
  match (occurrenceEquiv target wall right).symm edge with
  | none => newPerm
  | some edge => iso.edgePerm edge

section Lift

variable {first : GluingDatum target degree} {second : GluingDatum otherTarget degree}
  (iso : GeometricDatumIso first second) (wall : target.V) (otherWall : otherTarget.V)
  (right : target.edges → Bool) (otherRight : otherTarget.edges → Bool)
  (resolution otherResolution : LocalResolution degree)
  (hCompatible : GlobalResolution.OldCompatible first wall right resolution)
  (hOther : GlobalResolution.OldCompatible second otherWall otherRight otherResolution)
  (transport : TransportFree iso wall otherWall right otherRight resolution otherResolution)

theorem edgePermFree_none (newPerm : Equiv.Perm (Fin degree)) :
    edgePermFree iso wall right newPerm (occurrenceEquiv target wall right none) = newPerm := by
  simp only [edgePermFree, Equiv.symm_apply_apply]

theorem edgePermFree_some (newPerm : Equiv.Perm (Fin degree)) (edge : target.edges) :
    edgePermFree iso wall right newPerm (occurrenceEquiv target wall right (some edge)) =
      iso.edgePerm edge := by
  simp only [edgePermFree, Equiv.symm_apply_apply]

/-- **Base change for a resolution expansion, with decoupled endpoint
permutations.**  Target dictionaries as in `ResolutionExpansion.lift`
(literally `GeometricUniformExpansion.vertices` / `.edges`); only the sheet
permutations at the two expanded endpoints and on the regrown occurrence
change. -/
noncomputable def liftFree :
    GeometricDatumIso (GlobalResolution.datum first wall right resolution hCompatible)
      (GlobalResolution.datum second otherWall otherRight otherResolution hOther) where
  targetVertex := GeometricUniformExpansion.vertices iso
  targetEdge := GeometricUniformExpansion.edges iso wall otherWall right otherRight
  ends := GeometricUniformExpansion.edges_ends iso wall otherWall transport.wall_map right
    otherRight transport.side_map
  vertexPerm := endpointPerm iso wall transport.oldPerm transport.freshPerm
  edgePerm := edgePermFree iso wall right transport.newPerm
  vertexPartition vertex := by
    cases vertex with
    | inl vertex =>
      by_cases hWall : vertex = wall
      · subst vertex
        have hLHS : (GlobalResolution.datum second otherWall otherRight otherResolution
            hOther).vertexPartition (GeometricUniformExpansion.vertices iso
              (oldVertex target wall)) = otherResolution.left := by
          change (GlobalResolution.datum second otherWall otherRight otherResolution
            hOther).vertexPartition (oldVertex otherTarget (iso.targetVertex wall)) = _
          rw [transport.wall_map]
          exact GlobalResolution.datum_vertexPartition_old_wall _ _ _ _ _
        change _ = ((GlobalResolution.datum first wall right resolution
            hCompatible).vertexPartition (oldVertex target wall)).relabel
            (endpointPerm iso wall transport.oldPerm transport.freshPerm (oldVertex target wall))
        refine hLHS.trans ?_
        rw [GlobalResolution.datum_vertexPartition_old_wall, endpointPerm_old_wall]
        exact transport.left_relabel
      · have hNe : iso.targetVertex vertex ≠ otherWall := by
          rw [← transport.wall_map]
          exact fun h ↦ hWall (iso.targetVertex.injective h)
        have hLHS : (GlobalResolution.datum second otherWall otherRight otherResolution
            hOther).vertexPartition (GeometricUniformExpansion.vertices iso
              (oldVertex target vertex)) = second.vertexPartition (iso.targetVertex vertex) :=
          GlobalResolution.datum_vertexPartition_old_of_ne _ _ _ _ _ _ hNe
        change _ = ((GlobalResolution.datum first wall right resolution
            hCompatible).vertexPartition (oldVertex target vertex)).relabel
            (endpointPerm iso wall transport.oldPerm transport.freshPerm (oldVertex target vertex))
        refine hLHS.trans ?_
        rw [GlobalResolution.datum_vertexPartition_old_of_ne _ _ _ _ _ _ hWall,
          endpointPerm_old_of_ne _ _ _ _ _ hWall]
        exact iso.vertexPartition vertex
    | inr vertex =>
      cases vertex
      have hLHS : (GlobalResolution.datum second otherWall otherRight otherResolution
          hOther).vertexPartition (GeometricUniformExpansion.vertices iso
            (freshVertex target)) = otherResolution.right :=
        GlobalResolution.datum_vertexPartition_fresh _ _ _ _ _
      change _ = ((GlobalResolution.datum first wall right resolution
          hCompatible).vertexPartition (freshVertex target)).relabel
          (endpointPerm iso wall transport.oldPerm transport.freshPerm (freshVertex target))
      refine hLHS.trans ?_
      rw [GlobalResolution.datum_vertexPartition_fresh, endpointPerm_fresh]
      exact transport.right_relabel
  edgePartition edge := by
    obtain ⟨label, rfl⟩ := (occurrenceEquiv target wall right).surjective edge
    rw [GeometricUniformExpansion.edges_occurrence]
    cases label with
    | none =>
      rw [Option.map_none, GlobalResolution.datum_edgePartition_new,
        GlobalResolution.datum_edgePartition_new, transport.newEdge_relabel,
        edgePermFree_none]
    | some edge =>
      rw [Option.map_some, GlobalResolution.datum_edgePartition_old,
        GlobalResolution.datum_edgePartition_old, edgePermFree_some]
      exact iso.edgePartition edge
  compatible edge vertex hIncident sheet := by
    obtain ⟨label, rfl⟩ := (occurrenceEquiv target wall right).surjective edge
    cases label with
    | none =>
      simp only [occurrenceEquiv_none, newEnds] at hIncident
      rw [edgePermFree_none]
      rcases hIncident with rfl | rfl
      · rw [GlobalResolution.datum_vertexPartition_old_wall, endpointPerm_old_wall]
        exact transport.newEdge_old sheet
      · rw [GlobalResolution.datum_vertexPartition_fresh, endpointPerm_fresh]
        exact transport.newEdge_fresh sheet
    | some edge =>
      simp only [occurrenceEquiv_some, oldEnds] at hIncident
      rw [edgePermFree_some]
      rcases hIncident with rfl | rfl
      · show (GlobalResolution.expandedVertexPartition first wall resolution
          (expandedEndpoint target wall right edge (edge : target.V × target.V).1)).Rel _ _
        rw [ResolutionExpansion.expandedVertexPartition_expandedEndpoint,
          endpointPerm_expandedEndpoint]
        by_cases hWall : (edge : target.V × target.V).1 = wall
        · rw [if_pos hWall, if_pos hWall]
          exact transport.endpoint_compatible edge (Or.inl hWall) sheet
        · rw [if_neg hWall, if_neg hWall]
          exact iso.compatible edge _ (Or.inl rfl) sheet
      · show (GlobalResolution.expandedVertexPartition first wall resolution
          (expandedEndpoint target wall right edge (edge : target.V × target.V).2)).Rel _ _
        rw [ResolutionExpansion.expandedVertexPartition_expandedEndpoint,
          endpointPerm_expandedEndpoint]
        by_cases hWall : (edge : target.V × target.V).2 = wall
        · rw [if_pos hWall, if_pos hWall]
          exact transport.endpoint_compatible edge (Or.inr hWall) sheet
        · rw [if_neg hWall, if_neg hWall]
          exact iso.compatible edge _ (Or.inr rfl) sheet

theorem liftFree_targetEdge_occurrence (label : Option target.edges) :
    (liftFree iso wall otherWall right otherRight resolution otherResolution hCompatible hOther
        transport).targetEdge (occurrenceEquiv target wall right label) =
      occurrenceEquiv otherTarget otherWall otherRight (label.map iso.targetEdge) :=
  GeometricUniformExpansion.edges_occurrence iso wall otherWall right otherRight label

@[simp] theorem liftFree_targetVertex (vertex : Vertex target) :
    (liftFree iso wall otherWall right otherRight resolution otherResolution hCompatible hOther
        transport).targetVertex vertex = GeometricUniformExpansion.vertices iso vertex := rfl

@[simp] theorem liftFree_vertexPerm (vertex : Vertex target) :
    (liftFree iso wall otherWall right otherRight resolution otherResolution hCompatible hOther
        transport).vertexPerm vertex =
      endpointPerm iso wall transport.oldPerm transport.freshPerm vertex := rfl

@[simp] theorem liftFree_edgePerm (edge : (graph target wall right).edges) :
    (liftFree iso wall otherWall right otherRight resolution otherResolution hCompatible hOther
        transport).edgePerm edge = edgePermFree iso wall right transport.newPerm edge := rfl

/-- A permutation agreeing with a base vertex permutation modulo the base
partition sends quotient-source endpoints to the same place. -/
theorem sourceEndpoint_of_rel (vertex : target.V) (permutation : Equiv.Perm (Fin degree))
    (hRel : ∀ sheet, (first.vertexPartition vertex).Rel
      ((iso.vertexPerm vertex).symm (permutation sheet)) sheet) (sheet : Fin degree) :
    second.sourceEndpoint (iso.targetVertex vertex) (permutation sheet) =
      second.sourceEndpoint (iso.targetVertex vertex) (iso.vertexPerm vertex sheet) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (second.vertexPartition (iso.targetVertex vertex)).repr (permutation sheet) =
      (second.vertexPartition (iso.targetVertex vertex)).repr (iso.vertexPerm vertex sheet)
    rw [iso.vertexPartition]
    simp only [SheetPartition.relabel, Equiv.symm_apply_apply]
    exact congrArg (iso.vertexPerm vertex) (hRel sheet)

/-- The endpoint permutation agrees with the base permutation of the
contracted vertex, modulo the base partition, at every expanded vertex. -/
theorem endpointPerm_rel (vertex : Vertex target) (sheet : Fin degree) :
    (first.vertexPartition (contractVertex target wall vertex)).Rel
      ((iso.vertexPerm (contractVertex target wall vertex)).symm
        (endpointPerm iso wall transport.oldPerm transport.freshPerm vertex sheet)) sheet := by
  cases vertex with
  | inl vertex =>
    by_cases hWall : vertex = wall
    · subst vertex
      change (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm
        (endpointPerm iso wall transport.oldPerm transport.freshPerm (oldVertex target wall)
          sheet)) sheet
      rw [endpointPerm_old_wall]
      exact transport.old_merged sheet
    · change (first.vertexPartition vertex).Rel ((iso.vertexPerm vertex).symm
        (endpointPerm iso wall transport.oldPerm transport.freshPerm (oldVertex target vertex)
          sheet)) sheet
      rw [endpointPerm_old_of_ne _ _ _ _ _ hWall, Equiv.symm_apply_apply]
      rfl
  | inr vertex =>
    cases vertex
    exact transport.fresh_merged sheet

/-- **The source-contraction square**, for the decoupled lift.  The only input
beyond `ResolutionExpansion.sourceVertexMap_lift` is that the free endpoint
permutations agree with the wall permutation modulo the merged partition. -/
theorem sourceVertexMap_liftFree
    (vertex : (GlobalResolution.datum first wall right resolution hCompatible).SourceVertex) :
    iso.sourceVertexEquiv
        (GlobalResolution.sourceVertexMap first wall right resolution hCompatible vertex) =
      GlobalResolution.sourceVertexMap second otherWall otherRight otherResolution hOther
        ((liftFree iso wall otherWall right otherRight resolution otherResolution hCompatible
          hOther transport).sourceVertexEquiv vertex) := by
  have hContract := GeometricUniformExpansion.contractVertex_vertices iso wall otherWall
    transport.wall_map vertex.1.1
  refine (ResolutionExpansion.sourceEndpoint_vertexPerm iso
    (contractVertex target wall vertex.1.1) vertex.1.2).symm.trans ?_
  change second.sourceEndpoint (iso.targetVertex (contractVertex target wall vertex.1.1)) _ =
    second.sourceEndpoint (contractVertex otherTarget otherWall
      (GeometricUniformExpansion.vertices iso vertex.1.1))
      (endpointPerm iso wall transport.oldPerm transport.freshPerm vertex.1.1 vertex.1.2)
  rw [hContract]
  exact (sourceEndpoint_of_rel iso _ _
    (endpointPerm_rel iso wall otherWall right otherRight resolution otherResolution transport
      vertex.1.1) vertex.1.2).symm

/-- **The row square**, for the decoupled lift: retained quotient-source
occurrences are untouched by the free permutations. -/
theorem retainedSourceEdge_liftFree (edge : first.SourceEdge) :
    (liftFree iso wall otherWall right otherRight resolution otherResolution hCompatible hOther
          transport).sourceEdgeEquiv
        (ResolutionExpansion.retainedSourceEdge first wall right resolution hCompatible edge) =
      ResolutionExpansion.retainedSourceEdge second otherWall otherRight otherResolution hOther
        (iso.sourceEdgeEquiv edge) := by
  apply Subtype.ext
  apply Prod.ext
  · exact liftFree_targetEdge_occurrence iso wall otherWall right otherRight resolution
      otherResolution hCompatible hOther transport (some edge.1.1)
  · exact congrArg (fun permutation : Equiv.Perm (Fin degree) ↦ permutation edge.1.2)
      (edgePermFree_some iso wall right transport.newPerm edge.1.1)

end Lift

/-! ## 3.  Relabelled frames

A split frame relabelled by a global sheet permutation `σ` is in the wall's own
class, but `ResolutionExpansion.Transport` does not receive it.  With decoupled
permutations it is received, for **every** relabelling `σ` (not only the
transposition of a two-sheet block), by the wall's own frame presented at the
split placement: take all three free permutations to be `σ⁻¹`.  The lemmas below
are the resolution-level input: relabelling the frame relabels the presented
resolution. -/

section RelabelAccepted

open GraphContraction GluingContraction
open M11WallExhaustion
open WallStar (Regrowth Nondegenerate)
open W4WallExhaustion (mergeVertex)
open Utilities.Certificate.ExplicitPotential (Core)

/-- The incoming resolution depends on the placement only through its value. -/
theorem incomingResolution_congr {target : CFGraph} {a b : target.V}
    {contracted : target.edges} (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {second second' : (contract target hab hOne).edges → Bool}
    (hEq : second = second')
    (hPlacement :
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = second edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = !(second edge)))
    (hPlacement' :
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = second' edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = !(second' edge))) :
    incomingResolution data hc hab hOne second hPlacement =
      incomingResolution data hc hab hOne second' hPlacement' := by
  subst hEq
  rfl

/-- **Relabelling the frame relabels the presented resolution**, literally: the
normalization is sheet-blind. -/
theorem incomingResolution_globalRelabel {target : CFGraph} {a b : target.V}
    {contracted : target.edges} (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (second : (contract target hab hOne).edges → Bool)
    (hPlacement :
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = second edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = !(second edge)))
    (σ : Equiv.Perm (Fin degree)) :
    incomingResolution (Transport.DatumIso.globalRelabelDatum data σ) hc hab hOne second
        hPlacement =
      ResolutionExpansion.relabel (incomingResolution data hc hab hOne second hPlacement) σ :=
  rfl

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ} {hy : Nondegenerate y}
  {wall : Regrowth core y degree} (hPin : Pinned hy wall)
  (star : W2R1Target.TwoStar (wall.frame.limitTarget wall.column) (mergeVertex wall))

/-! ### A permutation forced on three sheets -/

section Pilot

private theorem pilot_forced_perm : ∀ π : Equiv.Perm (Fin 3),
    (fun i ↦ π (Equiv.swap 1 0 ((![0, 0, 2] : Fin 3 → Fin 3)
      ((Equiv.swap 1 0).symm (π.symm i))))) = (![0, 0, 2] : Fin 3 → Fin 3) →
      π = Equiv.swap 1 0 := by
  decide

end Pilot

end RelabelAccepted

/-! ## 4.  The upward frame isomorphism and exhaustion, on the decoupled lift

`M11WallExhaustion` §5–§6 re-derived verbatim from `liftFree`; nothing below is
about valency, M-11 or the divalent census except through the
`memberPlacement`/`memberResolution` the index is stated with. -/

section Consumers

open GraphContraction GluingContraction
open M11WallExhaustion
open WallStar (Regrowth Nondegenerate)
open W4WallExhaustion (mergeVertex)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ} {hy : Nondegenerate y}
  {wall : Regrowth core y degree} (hPin : Pinned hy wall)
  (star : W2R1Target.TwoStar (wall.frame.limitTarget wall.column) (mergeVertex wall))
  {placement : (wall.frame.limitTarget wall.column).edges → Bool}
  {resolution : ResolutionM11.LocalResolution degree}

/-- The receipt a member must present to be received by a candidate. -/
abbrev MemberTransport (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall)
    (placement : (wall.frame.limitTarget wall.column).edges → Bool)
    (resolution : ResolutionM11.LocalResolution degree) : Type :=
  TransportFree iso.datum (mergeVertex other) (mergeVertex wall)
    (memberPlacement hPin star other iso) placement (memberResolution hPin star other iso)
    resolution

/-- **Step two, decoupled.** -/
noncomputable def transIsoFree (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (c : Candidate hy wall placement resolution)
    (transport : MemberTransport hPin star other iso placement resolution) :
    GeometricDatumIso
      (GlobalResolution.datum other.limit (mergeVertex other)
        (memberPlacement hPin star other iso) (memberResolution hPin star other iso)
        (memberCompatible hPin star other iso))
      (GlobalResolution.datum wall.limit (mergeVertex wall) placement resolution
        c.oldCompatible) :=
  liftFree iso.datum (mergeVertex other) (mergeVertex wall)
    (memberPlacement hPin star other iso) placement (memberResolution hPin star other iso)
    resolution (memberCompatible hPin star other iso) c.oldCompatible transport

/-- **The datum half of the upward lift**, decoupled. -/
noncomputable def frameDatumFree (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (c : Candidate hy wall placement resolution)
    (transport : MemberTransport hPin star other iso placement resolution) :
    GeometricDatumIso other.frame.data c.data :=
  ((normIso hPin star other iso).trans (transIsoFree hPin star other iso c transport)).trans
    (UniformExpansionRecognition.ofEq c.data_eq.symm)

theorem frameDatumFree_sourceVertex (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (c : Candidate hy wall placement resolution)
    (transport : MemberTransport hPin star other iso placement resolution)
    (vertex : other.frame.data.SourceVertex) :
    ((frameDatumFree hPin star other iso c transport).sourceVertexEquiv vertex).1 =
      ((transIsoFree hPin star other iso c transport).sourceVertexEquiv
        ((normIso hPin star other iso).sourceVertexEquiv vertex)).1 :=
  UniformExpansionRecognition.ofEq_sourceVertexEquiv c.data_eq.symm
    ((transIsoFree hPin star other iso c transport).sourceVertexEquiv
      ((normIso hPin star other iso).sourceVertexEquiv vertex))

theorem frameDatumFree_sourceEdge (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (c : Candidate hy wall placement resolution)
    (transport : MemberTransport hPin star other iso placement resolution)
    (edge : other.frame.data.SourceEdge) :
    ((frameDatumFree hPin star other iso c transport).sourceEdgeEquiv edge).1 =
      ((transIsoFree hPin star other iso c transport).sourceEdgeEquiv
        ((normIso hPin star other iso).sourceEdgeEquiv edge)).1 :=
  UniformExpansionRecognition.ofEq_sourceEdgeEquiv c.data_eq.symm
    ((transIsoFree hPin star other iso c transport).sourceEdgeEquiv
      ((normIso hPin star other iso).sourceEdgeEquiv edge))

/-- **The branch square**, decoupled. -/
theorem source_squareFree (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (c : Candidate hy wall placement resolution)
    (transport : MemberTransport hPin star other iso placement resolution)
    (vertex : other.frame.data.SourceVertex) :
    c.datumIso.sourceVertexEquiv
        (InheritedLimitBranches.vertexMap c.regrowth
          ((frameDatumFree hPin star other iso c transport).sourceVertexEquiv vertex)) =
      iso.datum.sourceVertexEquiv (InheritedLimitBranches.vertexMap other vertex) := by
  have hMember := Candidate.member_contractSourceVertex c
    ((frameDatumFree hPin star other iso c transport).sourceVertexEquiv vertex)
  have hVal := frameDatumFree_sourceVertex hPin star other iso c transport vertex
  have hNorm : InheritedLimitBranches.vertexMap other vertex =
      GlobalResolution.sourceVertexMap other.limit (mergeVertex other)
        (memberPlacement hPin star other iso) (memberResolution hPin star other iso)
        (memberCompatible hPin star other iso)
        ((normIso hPin star other iso).sourceVertexEquiv vertex) :=
    sourceVertexMap_datumIso other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column))
      (other.frame.numEdges_edgeOf other.column) (memberPlacement hPin star other iso)
      (memberPlacement_spec hPin star other iso) other.frame.fullDim.targetConnected
      other.frame.fullDim.targetGenus vertex
  have hLift := sourceVertexMap_liftFree iso.datum (mergeVertex other)
    (mergeVertex wall) (memberPlacement hPin star other iso) placement
    (memberResolution hPin star other iso) resolution (memberCompatible hPin star other iso)
    c.oldCompatible transport ((normIso hPin star other iso).sourceVertexEquiv vertex)
  rw [hMember, hVal, hNorm, hLift]
  rfl

/-- **The row square**, decoupled. -/
theorem edge_squareFree (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (c : Candidate hy wall placement resolution)
    (transport : MemberTransport hPin star other iso placement resolution)
    (edge : other.limit.SourceEdge) :
    (frameDatumFree hPin star other iso c transport).sourceEdgeEquiv
        (InheritedLimitRows.edgeEmbedding other edge) =
      InheritedLimitRows.edgeEmbedding c.regrowth
        (StarFrameIso.transfer iso c.starLimitIso edge) := by
  apply Subtype.ext
  have hNorm : (normIso hPin star other iso).sourceEdgeEquiv
      (InheritedLimitRows.edgeEmbedding other edge) =
      ResolutionExpansion.retainedSourceEdge other.limit (mergeVertex other)
        (memberPlacement hPin star other iso) (memberResolution hPin star other iso)
        (memberCompatible hPin star other iso) edge :=
    retainedSourceEdge_datumIso other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column))
      (other.frame.numEdges_edgeOf other.column) (memberPlacement hPin star other iso)
      (memberPlacement_spec hPin star other iso) other.frame.fullDim.targetConnected
      other.frame.fullDim.targetGenus edge
  have hLift : (transIsoFree hPin star other iso c transport).sourceEdgeEquiv
      (ResolutionExpansion.retainedSourceEdge other.limit (mergeVertex other)
        (memberPlacement hPin star other iso) (memberResolution hPin star other iso)
        (memberCompatible hPin star other iso) edge) =
      ResolutionExpansion.retainedSourceEdge wall.limit (mergeVertex wall) placement resolution
        c.oldCompatible (iso.datum.sourceEdgeEquiv edge) :=
    retainedSourceEdge_liftFree iso.datum (mergeVertex other)
      (mergeVertex wall) (memberPlacement hPin star other iso) placement
      (memberResolution hPin star other iso) resolution (memberCompatible hPin star other iso)
      c.oldCompatible transport edge
  have hMember := Candidate.member_edgeEmbedding_val c
    (StarFrameIso.transfer iso c.starLimitIso edge)
  have hTransfer : c.datumIso.sourceEdgeEquiv (StarFrameIso.transfer iso c.starLimitIso edge) =
      iso.datum.sourceEdgeEquiv edge :=
    StarFrameIso.datum_sourceEdgeEquiv_transfer iso c.starLimitIso edge
  rw [frameDatumFree_sourceEdge, hNorm, hLift, hMember, hTransfer]
  rfl

/-- **The upward frame isomorphism, decoupled.** -/
noncomputable def frameIsoFree (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (c : Candidate hy wall placement resolution)
    (transport : MemberTransport hPin star other iso placement resolution) :
    GeometricSegmentWalls.FrameIso other.frame c.frame :=
  StarFrameIso.ofLimitSquare iso c.starLimitIso (frameDatumFree hPin star other iso c transport)
    (source_squareFree hPin star other iso c transport)
    (edge_squareFree hPin star other iso c transport)

section Exhaustion

variable {ι : Type*} (P : ι → ((wall.frame.limitTarget wall.column).edges → Bool))
  (R : ι → ResolutionM11.LocalResolution degree)
  (cand : ∀ i : ι, Candidate hy wall (P i) (R i))

/-- **The decoupled classification receipt.**  `M11WallExhaustion.Covers` with
`ResolutionExpansion.Transport` replaced by `TransportFree`. -/
def CoversFree : Prop :=
  ∀ (other : Regrowth core y degree) (iso : GeometricStar.LimitIso hy other wall),
    ∃ i : ι, Nonempty (MemberTransport hPin star other iso (P i) (R i))

/-- `CoversFree` is implied by `Covers` (`ofTransport`); so it is at worst as
hard. -/
theorem coversFree_of_covers (hCover : Covers hPin star P R) : CoversFree hPin star P R := by
  intro other iso
  obtain ⟨i, transport⟩ := hCover other iso
  exact ⟨i, ⟨ofTransport transport⟩⟩

/-- **Exhaustion, decoupled.** -/
theorem exists_cls_eq_free (hCover : CoversFree hPin star P R)
    (member : GeometricStar.StarMember hy wall) :
    ∃ i : ι, member.cls = ((cand i).starMember).cls := by
  obtain ⟨limIso⟩ := member.specializes
  obtain ⟨i, ⟨transport⟩⟩ := hCover member.member limIso
  exact ⟨i, Quotient.sound ⟨frameIsoFree hPin star member.member limIso (cand i) transport⟩⟩

theorem cls_surjective_free (hCover : CoversFree hPin star P R) :
    Function.Surjective fun i : ι ↦ ((cand i).starMember).cls := by
  refine Quotient.ind ?_
  intro member
  obtain ⟨i, hi⟩ := exists_cls_eq_free hPin star P R cand hCover member
  exact ⟨i, hi.symm⟩

/-- **The existential receipt.**  `CoversFree` asks for a transport of *every*
labelled limit isomorphism; exhaustion only ever uses *one* per member.  This
is the weaker supply, and the one to produce: a limit isomorphism that differs
from a good one by a wall automorphism moving one occurrence's sheets inside a
merged block can violate `endpoint_compatible` at a discrete endpoint, and
nothing here excludes such automorphisms. -/
def CoversFreeSome : Prop :=
  ∀ member : GeometricStar.StarMember hy wall,
    ∃ (iso : GeometricStar.LimitIso hy member.member wall) (i : ι),
      Nonempty (MemberTransport hPin star member.member iso (P i) (R i))

theorem coversFreeSome_of_coversFree (hCover : CoversFree hPin star P R) :
    CoversFreeSome hPin star P R := by
  intro member
  obtain ⟨limIso⟩ := member.specializes
  obtain ⟨i, transport⟩ := hCover member.member limIso
  exact ⟨limIso, i, transport⟩

/-- **Exhaustion from the existential receipt.** -/
theorem exists_cls_eq_freeSome (hCover : CoversFreeSome hPin star P R)
    (member : GeometricStar.StarMember hy wall) :
    ∃ i : ι, member.cls = ((cand i).starMember).cls := by
  obtain ⟨limIso, i, ⟨transport⟩⟩ := hCover member
  exact ⟨i, Quotient.sound ⟨frameIsoFree hPin star member.member limIso (cand i) transport⟩⟩

theorem cls_surjective_freeSome (hCover : CoversFreeSome hPin star P R) :
    Function.Surjective fun i : ι ↦ ((cand i).starMember).cls := by
  refine Quotient.ind ?_
  intro member
  obtain ⟨i, hi⟩ := exists_cls_eq_freeSome hPin star P R cand hCover member
  exact ⟨i, hi.symm⟩

include cand in
/-- **The upper bound**, decoupled. -/
theorem card_le_of_index_free [Fintype ι] (hCover : CoversFreeSome hPin star P R) :
    Fintype.card (GeometricStar.Star hy wall) ≤ Fintype.card ι :=
  Fintype.card_le_of_surjective _ (cls_surjective_freeSome hPin star P R cand hCover)

/-- **The wall's labelled geometric star is the index type**, given the
existential decoupled receipt and `Separates`. -/
noncomputable def starEquivFree (hCover : CoversFreeSome hPin star P R)
    (hSep : Separates P R cand) : ι ≃ GeometricStar.Star hy wall :=
  Equiv.ofBijective _ ⟨hSep, cls_surjective_freeSome hPin star P R cand hCover⟩

theorem card_eq_of_index_free [Fintype ι] (hCover : CoversFreeSome hPin star P R)
    (hSep : Separates P R cand) :
    Fintype.card (GeometricStar.Star hy wall) = Fintype.card ι :=
  (Fintype.card_congr (starEquivFree hPin star P R cand hCover hSep)).symm

end Exhaustion

end Consumers

end DraismaVargas.Count.ResolutionExpansionFree
