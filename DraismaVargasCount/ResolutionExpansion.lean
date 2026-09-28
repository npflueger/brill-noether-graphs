import DraismaVargasCount.GeometricUniformExpansion
import DraismaVargasCount.UniformExpansionRecognition

/-!
# Target expansions carrying an arbitrary local resolution

Source: Draisma--Vargas Part I, section "Constructions", subsection "Trees contracting
to T₀" (`sub-graphs-to-T0`), where the wall vertex `w_0` of a limit is regrown back to
an edge (the target expansion at a wall vertex), and Part I, Figure 32 (the local
resolutions of case `{w2-r2-nd3-M-11}`).

## Why this module exists

`Count.GeometricUniformExpansion` fixes one local resolution — the *joined*
one, `LocalCases.ResolutionM11.joinedResolutionAt`, which duplicates the wall
partition at both expanded endpoints and on the regrown occurrence — and
builds the datum, the recognition statement and the base-change lift for it.
At a **four-valent discrete** wall that is no loss: `Count.DiscreteW4Normalization`
shows the joined resolution is the only one available there.

At a wall whose merged partition is not discrete — and by
`Count.W4WallExhaustion.vertexPartition_ne_discrete_of_card_ne_four` that is
*every* wall of the nine non-`w4` families — the local resolution is a genuine
second coordinate beside the placement.  This module redoes the three pieces
for an arbitrary `LocalResolution degree`:

* `oldCompatible_of_expansion` and `eq_resolutionDatum` — **recognition**.  A
  gluing datum on the expanded target whose five displayed partitions are the
  prescribed ones *is* `LocalCases.GlobalResolution.datum` at the resolution
  read off its own two endpoint partitions and its own new occurrence.  This
  is the exact analogue of `Count.UniformExpansionRecognition.eq_uniformExpansion`,
  and specializes back to it (`uniform_eq_resolutionDatum`).
* `relabel` — the sheet relabelling of a `LocalResolution`, which is what a
  geometric datum isomorphism does to the three local partitions.
* `lift` — **base change**.  A geometric isomorphism of the two base data
  which matches the placements, relabels the resolution, and satisfies the
  displayed endpoint compatibility, lifts to the two expanded data.  Its
  target dictionaries are literally `GeometricUniformExpansion.vertices` and
  `.edges`, so all of that module's occurrence bookkeeping is reused verbatim.

## What is NOT proved (every surviving hypothesis, explicitly)

* **`lift` carries an endpoint sheet-compatibility hypothesis**
  (`Transport.endpoint_compatible`), and it is not vacuous.  A `GeometricDatumIso` only promises that its occurrence
  permutation agrees with its vertex permutation *modulo the blocks of the
  base vertex partition*; the expanded datum asks for agreement modulo the
  blocks of `resolution.left` / `resolution.right`, which are finer.  When
  the resolution is the joined one those partitions coincide and the
  hypothesis is discharged by `uniformTransport`, which is why
  `GeometricUniformExpansion.lift` needed no such field.  Nothing here says
  that an arbitrary limit isomorphism admits such a transport; that is the
  endpoint sheet-rigidity condition discussed in `Count.M11WallExhaustion`.
* Nothing about validity, full dimensionality, connectivity, branch vertices,
  stable rows or inherited core labels of either datum.
* Nothing selects a resolution: no statement here says which
  `LocalResolution` a wall of the Draisma--Vargas count schedule carries, or
  how many there are.

## Consumers

`DraismaVargas.Count.M11WallExhaustion` (the star at a wall of type
`{w2-r2-nd3-M-11}`), for steps 2 and 3 of `Assembly`.
-/

namespace DraismaVargas.Count.ResolutionExpansion

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open TargetExpansion
open ResolutionM11 (LocalResolution)

variable {target otherTarget : CFGraph} {degree : ℕ}

/-! ## 1.  Relabelling a local resolution -/

/-- Transport the three local partitions of a resolution along a sheet
permutation.  This is what a `GeometricDatumIso` does to them. -/
def relabel (resolution : LocalResolution degree) (permutation : Equiv.Perm (Fin degree)) :
    LocalResolution degree where
  left := resolution.left.relabel permutation
  right := resolution.right.relabel permutation
  newEdge := resolution.newEdge.relabel permutation
  edge_refines_left := SheetPartition.relabel_refines resolution.edge_refines_left permutation
  edge_refines_right := SheetPartition.relabel_refines resolution.edge_refines_right permutation

@[simp] theorem relabel_left (resolution : LocalResolution degree)
    (permutation : Equiv.Perm (Fin degree)) :
    (relabel resolution permutation).left = resolution.left.relabel permutation := rfl

@[simp] theorem relabel_right (resolution : LocalResolution degree)
    (permutation : Equiv.Perm (Fin degree)) :
    (relabel resolution permutation).right = resolution.right.relabel permutation := rfl

@[simp] theorem relabel_newEdge (resolution : LocalResolution degree)
    (permutation : Equiv.Perm (Fin degree)) :
    (relabel resolution permutation).newEdge = resolution.newEdge.relabel permutation := rfl

/-- The local resolution a gluing datum on an expanded target presents: its
two expanded endpoint partitions and its regrown occurrence. -/
noncomputable def readOff (right : target.edges → Bool) {wall : target.V}
    (expanded : GluingDatum (graph target wall right) degree) : LocalResolution degree where
  left := expanded.vertexPartition (oldVertex target wall)
  right := expanded.vertexPartition (freshVertex target)
  newEdge := expanded.edgePartition (occurrenceEquiv target wall right none)
  edge_refines_left := by
    have h := expanded.refines_left (occurrenceEquiv target wall right none)
    rwa [occurrenceEquiv_none] at h
  edge_refines_right := by
    have h := expanded.refines_right (occurrenceEquiv target wall right none)
    rwa [occurrenceEquiv_none] at h

@[simp] theorem readOff_left (right : target.edges → Bool) {wall : target.V}
    (expanded : GluingDatum (graph target wall right) degree) :
    (readOff right expanded).left = expanded.vertexPartition (oldVertex target wall) := rfl

@[simp] theorem readOff_right (right : target.edges → Bool) {wall : target.V}
    (expanded : GluingDatum (graph target wall right) degree) :
    (readOff right expanded).right = expanded.vertexPartition (freshVertex target) := rfl

@[simp] theorem readOff_newEdge (right : target.edges → Bool) {wall : target.V}
    (expanded : GluingDatum (graph target wall right) degree) :
    (readOff right expanded).newEdge =
      expanded.edgePartition (occurrenceEquiv target wall right none) := rfl

/-! ## 2.  Recognition -/

section Recognition

variable (base : GluingDatum target degree) (wall : target.V) (right : target.edges → Bool)
  (resolution : LocalResolution degree)
  (expanded : GluingDatum (graph target wall right) degree)

/-- The vertex-partition half of the recognition hypotheses, packaged as the
statement that the expanded datum's vertex partition *is* the one
`LocalCases.GlobalResolution` prescribes. -/
theorem vertexPartition_eq_expanded
    (hOldWall : expanded.vertexPartition (oldVertex target wall) = resolution.left)
    (hFresh : expanded.vertexPartition (freshVertex target) = resolution.right)
    (hAway : ∀ vertex : target.V, vertex ≠ wall →
      expanded.vertexPartition (oldVertex target vertex) = base.vertexPartition vertex) :
    expanded.vertexPartition = GlobalResolution.expandedVertexPartition base wall resolution := by
  funext vertex
  cases vertex with
  | inl vertex =>
    by_cases h : vertex = wall
    · subst vertex
      exact hOldWall.trans
        (GlobalResolution.expandedVertexPartition_old_wall base wall resolution).symm
    · exact (hAway vertex h).trans
        (GlobalResolution.expandedVertexPartition_old_of_ne base wall vertex resolution h).symm
  | inr vertex =>
    cases vertex
    exact hFresh

/-- The occurrence-partition half of the recognition hypotheses. -/
theorem edgePartition_eq_expanded
    (hNew : expanded.edgePartition (occurrenceEquiv target wall right none) =
      resolution.newEdge)
    (hRetained : ∀ edge : target.edges,
      expanded.edgePartition (occurrenceEquiv target wall right (some edge)) =
        base.edgePartition edge) :
    expanded.edgePartition =
      GlobalResolution.expandedEdgePartition base wall right resolution := by
  funext edge
  obtain ⟨label, rfl⟩ := (occurrenceEquiv target wall right).surjective edge
  cases label with
  | none => rw [hNew, GlobalResolution.expandedEdgePartition_new]
  | some edge => rw [hRetained, GlobalResolution.expandedEdgePartition_old]

/-- **The exterior compatibility obligation is a theorem, not an input, once
an actual expanded gluing datum with the prescribed partitions exists.**  Its
own `refines_left`/`refines_right` fields say exactly that. -/
theorem oldCompatible_of_expansion
    (hOldWall : expanded.vertexPartition (oldVertex target wall) = resolution.left)
    (hFresh : expanded.vertexPartition (freshVertex target) = resolution.right)
    (hAway : ∀ vertex : target.V, vertex ≠ wall →
      expanded.vertexPartition (oldVertex target vertex) = base.vertexPartition vertex)
    (hRetained : ∀ edge : target.edges,
      expanded.edgePartition (occurrenceEquiv target wall right (some edge)) =
        base.edgePartition edge) :
    GlobalResolution.OldCompatible base wall right resolution := by
  have hVertex := vertexPartition_eq_expanded base wall right resolution expanded
    hOldWall hFresh hAway
  intro edge
  have hLeft := expanded.refines_left (occurrenceEquiv target wall right (some edge))
  have hRight := expanded.refines_right (occurrenceEquiv target wall right (some edge))
  rw [occurrenceEquiv_some, hRetained edge] at hLeft hRight
  rw [hVertex] at hLeft hRight
  exact ⟨hLeft, hRight⟩

/-- **Recognition of a resolution expansion.**  A gluing datum on the expanded
target which carries the resolution's two endpoint partitions and new-edge
partition, and the base partitions everywhere else, is literally
`LocalCases.GlobalResolution.datum`. -/
theorem eq_resolutionDatum
    (hCompatible : GlobalResolution.OldCompatible base wall right resolution)
    (hOldWall : expanded.vertexPartition (oldVertex target wall) = resolution.left)
    (hFresh : expanded.vertexPartition (freshVertex target) = resolution.right)
    (hAway : ∀ vertex : target.V, vertex ≠ wall →
      expanded.vertexPartition (oldVertex target vertex) = base.vertexPartition vertex)
    (hNew : expanded.edgePartition (occurrenceEquiv target wall right none) =
      resolution.newEdge)
    (hRetained : ∀ edge : target.edges,
      expanded.edgePartition (occurrenceEquiv target wall right (some edge)) =
        base.edgePartition edge) :
    expanded = GlobalResolution.datum base wall right resolution hCompatible :=
  gluingDatum_ext
    (vertexPartition_eq_expanded base wall right resolution expanded hOldWall hFresh hAway)
    (edgePartition_eq_expanded base wall right resolution expanded hNew hRetained)

end Recognition

/-! ## 3.  Base change -/

/-- The expanded vertex partition at a remapped old endpoint. -/
theorem expandedVertexPartition_expandedEndpoint (base : GluingDatum target degree)
    (wall : target.V) (right : target.edges → Bool) (resolution : LocalResolution degree)
    (edge : target.edges) (vertex : target.V) :
    GlobalResolution.expandedVertexPartition base wall resolution
        (expandedEndpoint target wall right edge vertex) =
      if vertex = wall then (if right edge then resolution.right else resolution.left)
      else base.vertexPartition vertex := by
  unfold expandedEndpoint
  by_cases hSide : right edge = true
  · by_cases hWall : vertex = wall
    · subst vertex
      simp [hSide, GlobalResolution.expandedVertexPartition, freshVertex]
    · simp [hSide, hWall, GlobalResolution.expandedVertexPartition, oldVertex]
  · simp only [Bool.not_eq_true] at hSide
    by_cases hWall : vertex = wall
    · subst vertex
      simp [hSide, GlobalResolution.expandedVertexPartition, oldVertex]
    · simp [hSide, hWall, GlobalResolution.expandedVertexPartition, oldVertex]

/-- **What a base isomorphism has to do to transport a resolution expansion.**
The first two fields are exactly `Count.GeometricUniformExpansion.lift`'s
hypotheses; the next three say the target resolution is the source one
relabelled by the wall's sheet permutation.  The last field is the one that
has no counterpart in the uniform case: it asks the occurrence permutation of
a wall-incident retained occurrence to agree with the wall's vertex
permutation **modulo the blocks of the resolution's endpoint partition**,
which is finer than the base wall partition that `GeometricDatumIso.compatible`
controls.  When `resolution` is the joined one the two coincide
(`uniformTransport`). -/
structure Transport {first : GluingDatum target degree} {second : GluingDatum otherTarget degree}
    (iso : GeometricDatumIso first second) (wall : target.V) (otherWall : otherTarget.V)
    (right : target.edges → Bool) (otherRight : otherTarget.edges → Bool)
    (resolution otherResolution : LocalResolution degree) : Prop where
  /-- The wall vertex is matched. -/
  wall_map : iso.targetVertex wall = otherWall
  /-- The two side assignments agree along the occurrence bijection. -/
  side_map : ∀ edge : target.edges, otherRight (iso.targetEdge edge) = right edge
  /-- The retained endpoint partition is relabelled by the wall permutation. -/
  left_relabel : otherResolution.left = resolution.left.relabel (iso.vertexPerm wall)
  /-- …and so is the fresh endpoint partition. -/
  right_relabel : otherResolution.right = resolution.right.relabel (iso.vertexPerm wall)
  /-- …and so is the regrown occurrence partition. -/
  newEdge_relabel : otherResolution.newEdge = resolution.newEdge.relabel (iso.vertexPerm wall)
  /-- **The finer endpoint compatibility.**  Not implied by
  `GeometricDatumIso.compatible` unless the resolution's endpoint partitions
  are the base wall partition. -/
  endpoint_compatible : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨ (edge : target.V × target.V).2 = wall) →
    ∀ sheet : Fin degree,
      (if right edge then resolution.right else resolution.left).Rel
        ((iso.vertexPerm wall).symm (iso.edgePerm edge sheet)) sheet

section Lift

variable {first : GluingDatum target degree} {second : GluingDatum otherTarget degree}
  (iso : GeometricDatumIso first second) (wall : target.V) (otherWall : otherTarget.V)
  (right : target.edges → Bool) (otherRight : otherTarget.edges → Bool)
  (resolution otherResolution : LocalResolution degree)
  (hCompatible : GlobalResolution.OldCompatible first wall right resolution)
  (hOther : GlobalResolution.OldCompatible second otherWall otherRight otherResolution)
  (transport : Transport iso wall otherWall right otherRight resolution otherResolution)

/-- **Base change for a resolution expansion.**  The target dictionaries are
literally `Count.GeometricUniformExpansion.vertices` and `.edges`, so every
occurrence identity proved there applies verbatim. -/
noncomputable def lift :
    GeometricDatumIso (GlobalResolution.datum first wall right resolution hCompatible)
      (GlobalResolution.datum second otherWall otherRight otherResolution hOther) where
  targetVertex := GeometricUniformExpansion.vertices iso
  targetEdge := GeometricUniformExpansion.edges iso wall otherWall right otherRight
  ends := GeometricUniformExpansion.edges_ends iso wall otherWall transport.wall_map right
    otherRight transport.side_map
  vertexPerm vertex := iso.vertexPerm (contractVertex target wall vertex)
  edgePerm := GeometricUniformExpansion.edgePerm iso wall right
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
        have hRHS : (GlobalResolution.datum first wall right resolution
            hCompatible).vertexPartition (oldVertex target wall) = resolution.left :=
          GlobalResolution.datum_vertexPartition_old_wall _ _ _ _ _
        exact hLHS.trans (transport.left_relabel.trans
          (congrArg (fun P : SheetPartition degree ↦ P.relabel (iso.vertexPerm wall)) hRHS.symm))
      · have hNe : iso.targetVertex vertex ≠ otherWall := by
          rw [← transport.wall_map]
          exact fun h ↦ hWall (iso.targetVertex.injective h)
        have hLHS : (GlobalResolution.datum second otherWall otherRight otherResolution
            hOther).vertexPartition (GeometricUniformExpansion.vertices iso
              (oldVertex target vertex)) = second.vertexPartition (iso.targetVertex vertex) :=
          GlobalResolution.datum_vertexPartition_old_of_ne _ _ _ _ _ _ hNe
        have hRHS : (GlobalResolution.datum first wall right resolution
            hCompatible).vertexPartition (oldVertex target vertex) =
            first.vertexPartition vertex :=
          GlobalResolution.datum_vertexPartition_old_of_ne _ _ _ _ _ _ hWall
        exact hLHS.trans ((iso.vertexPartition vertex).trans
          (congrArg (fun P : SheetPartition degree ↦ P.relabel (iso.vertexPerm vertex))
            hRHS.symm))
    | inr vertex =>
      cases vertex
      have hLHS : (GlobalResolution.datum second otherWall otherRight otherResolution
          hOther).vertexPartition (GeometricUniformExpansion.vertices iso
            (freshVertex target)) = otherResolution.right :=
        GlobalResolution.datum_vertexPartition_fresh _ _ _ _ _
      have hRHS : (GlobalResolution.datum first wall right resolution
          hCompatible).vertexPartition (freshVertex target) = resolution.right :=
        GlobalResolution.datum_vertexPartition_fresh _ _ _ _ _
      exact hLHS.trans (transport.right_relabel.trans
        (congrArg (fun P : SheetPartition degree ↦ P.relabel (iso.vertexPerm wall)) hRHS.symm))
  edgePartition edge := by
    obtain ⟨label, rfl⟩ := (occurrenceEquiv target wall right).surjective edge
    rw [GeometricUniformExpansion.edges_occurrence]
    cases label with
    | none =>
      rw [Option.map_none, GlobalResolution.datum_edgePartition_new,
        GlobalResolution.datum_edgePartition_new, transport.newEdge_relabel,
        GeometricUniformExpansion.edgePerm_none]
    | some edge =>
      rw [Option.map_some, GlobalResolution.datum_edgePartition_old,
        GlobalResolution.datum_edgePartition_old, GeometricUniformExpansion.edgePerm_some]
      exact iso.edgePartition edge
  compatible edge vertex hIncident sheet := by
    obtain ⟨label, rfl⟩ := (occurrenceEquiv target wall right).surjective edge
    cases label with
    | none =>
      simp only [occurrenceEquiv_none, newEnds] at hIncident
      rcases hIncident with rfl | rfl <;>
        simp only [GeometricUniformExpansion.edgePerm_none, contract_oldVertex,
          contract_freshVertex, Equiv.symm_apply_apply, SheetPartition.rel_iff]
    | some edge =>
      simp only [occurrenceEquiv_some, oldEnds] at hIncident
      rw [GeometricUniformExpansion.edgePerm_some]
      rcases hIncident with rfl | rfl
      · show (GlobalResolution.expandedVertexPartition first wall resolution
          (expandedEndpoint target wall right edge (edge : target.V × target.V).1)).Rel _ _
        rw [expandedVertexPartition_expandedEndpoint, contract_expandedEndpoint]
        by_cases hWall : (edge : target.V × target.V).1 = wall
        · rw [if_pos hWall, hWall]
          exact transport.endpoint_compatible edge (Or.inl hWall) sheet
        · rw [if_neg hWall]
          exact iso.compatible edge _ (Or.inl rfl) sheet
      · show (GlobalResolution.expandedVertexPartition first wall resolution
          (expandedEndpoint target wall right edge (edge : target.V × target.V).2)).Rel _ _
        rw [expandedVertexPartition_expandedEndpoint, contract_expandedEndpoint]
        by_cases hWall : (edge : target.V × target.V).2 = wall
        · rw [if_pos hWall, hWall]
          exact transport.endpoint_compatible edge (Or.inr hWall) sheet
        · rw [if_neg hWall]
          exact iso.compatible edge _ (Or.inr rfl) sheet

theorem lift_targetEdge_occurrence (label : Option target.edges) :
    (lift iso wall otherWall right otherRight resolution otherResolution hCompatible hOther
        transport).targetEdge (occurrenceEquiv target wall right label) =
      occurrenceEquiv otherTarget otherWall otherRight (label.map iso.targetEdge) :=
  GeometricUniformExpansion.edges_occurrence iso wall otherWall right otherRight label

@[simp] theorem lift_targetVertex (vertex : Vertex target) :
    (lift iso wall otherWall right otherRight resolution otherResolution hCompatible hOther
        transport).targetVertex vertex = GeometricUniformExpansion.vertices iso vertex := rfl

@[simp] theorem lift_vertexPerm (vertex : Vertex target) :
    (lift iso wall otherWall right otherRight resolution otherResolution hCompatible hOther
        transport).vertexPerm vertex = iso.vertexPerm (contractVertex target wall vertex) := rfl

@[simp] theorem lift_edgePerm (edge : (graph target wall right).edges) :
    (lift iso wall otherWall right otherRight resolution otherResolution hCompatible hOther
        transport).edgePerm edge = GeometricUniformExpansion.edgePerm iso wall right edge := rfl

/-- A base isomorphism carries quotient-source endpoints to quotient-source
endpoints; the sheet representative is normalized on both sides. -/
theorem sourceEndpoint_vertexPerm (vertex : target.V) (sheet : Fin degree) :
    second.sourceEndpoint (iso.targetVertex vertex) (iso.vertexPerm vertex sheet) =
      iso.sourceVertexEquiv (first.sourceEndpoint vertex sheet) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (second.vertexPartition (iso.targetVertex vertex)).repr (iso.vertexPerm vertex sheet) =
      iso.vertexPerm vertex ((first.vertexPartition vertex).repr sheet)
    rw [iso.vertexPartition]
    simp [SheetPartition.relabel]

/-- **The source-contraction square.**  Contracting the expanded source and
transporting agree with transporting and then contracting.  Unlike the
uniform case the stored sheet representative really does move, so the
statement is in `GluingDatum.sourceEndpoint` normal form. -/
theorem sourceVertexMap_lift
    (vertex : (GlobalResolution.datum first wall right resolution hCompatible).SourceVertex) :
    iso.sourceVertexEquiv
        (GlobalResolution.sourceVertexMap first wall right resolution hCompatible vertex) =
      GlobalResolution.sourceVertexMap second otherWall otherRight otherResolution hOther
        ((lift iso wall otherWall right otherRight resolution otherResolution hCompatible hOther
          transport).sourceVertexEquiv vertex) := by
  have hContract := GeometricUniformExpansion.contractVertex_vertices iso wall otherWall
    transport.wall_map vertex.1.1
  refine (sourceEndpoint_vertexPerm iso (contractVertex target wall vertex.1.1) vertex.1.2).symm.trans ?_
  change second.sourceEndpoint (iso.targetVertex (contractVertex target wall vertex.1.1)) _ =
    second.sourceEndpoint (contractVertex otherTarget otherWall
      (GeometricUniformExpansion.vertices iso vertex.1.1)) _
  rw [hContract]
  rfl

/-- The retained quotient-source occurrence of a resolution expansion. -/
noncomputable def retainedSourceEdge (base : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : GlobalResolution.OldCompatible base wall right resolution)
    (edge : base.SourceEdge) :
    (GlobalResolution.datum base wall right resolution hCompatible).SourceEdge :=
  ⟨(occurrenceEquiv target wall right (some edge.1.1), edge.1.2), by
    rw [GlobalResolution.datum_edgePartition_old]
    exact edge.2⟩

@[simp] theorem retainedSourceEdge_val (base : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : GlobalResolution.OldCompatible base wall right resolution)
    (edge : base.SourceEdge) :
    (retainedSourceEdge base wall right resolution hCompatible edge).1 =
      (occurrenceEquiv target wall right (some edge.1.1), edge.1.2) := rfl

/-- **The row square.**  Retained quotient-source occurrences, including
their stored sheets, commute with base change. -/
theorem retainedSourceEdge_lift (edge : first.SourceEdge) :
    (lift iso wall otherWall right otherRight resolution otherResolution hCompatible hOther
          transport).sourceEdgeEquiv
        (retainedSourceEdge first wall right resolution hCompatible edge) =
      retainedSourceEdge second otherWall otherRight otherResolution hOther
        (iso.sourceEdgeEquiv edge) := by
  apply Subtype.ext
  apply Prod.ext
  · exact lift_targetEdge_occurrence iso wall otherWall right otherRight resolution
      otherResolution hCompatible hOther transport (some edge.1.1)
  · exact congrArg (fun permutation : Equiv.Perm (Fin degree) ↦ permutation edge.1.2)
      (GeometricUniformExpansion.edgePerm_some iso wall right edge.1.1)

end Lift

/-- The joined resolution of a base partition at a wall, as a `LocalResolution`. -/
noncomputable abbrev joined (base : GluingDatum target degree) (wall : target.V) :
    LocalResolution degree :=
  ResolutionM11.joinedResolutionAt (base.vertexPartition wall)

/-- **At the joined resolution the finer endpoint compatibility is free.**
Both endpoint partitions of `joined` are the base wall partition, which is
exactly what `GeometricDatumIso.compatible` controls.  This is the precise
reason `Count.GeometricUniformExpansion.lift` needs no such hypothesis, and
the precise reason a non-joined resolution does. -/
theorem uniformTransport {first : GluingDatum target degree}
    {second : GluingDatum otherTarget degree} (iso : GeometricDatumIso first second)
    (wall : target.V) (otherWall : otherTarget.V) (hWall : iso.targetVertex wall = otherWall)
    (right : target.edges → Bool) (otherRight : otherTarget.edges → Bool)
    (hRight : ∀ edge : target.edges, otherRight (iso.targetEdge edge) = right edge) :
    Transport iso wall otherWall right otherRight (joined first wall) (joined second otherWall) where
  wall_map := hWall
  side_map := hRight
  left_relabel := by
    show second.vertexPartition otherWall = (first.vertexPartition wall).relabel _
    rw [← hWall]
    exact iso.vertexPartition wall
  right_relabel := by
    show second.vertexPartition otherWall = (first.vertexPartition wall).relabel _
    rw [← hWall]
    exact iso.vertexPartition wall
  newEdge_relabel := by
    show second.vertexPartition otherWall = (first.vertexPartition wall).relabel _
    rw [← hWall]
    exact iso.vertexPartition wall
  endpoint_compatible edge hIncident sheet := by
    show (if right edge then first.vertexPartition wall else first.vertexPartition wall).Rel _ _
    rw [ite_self]
    exact iso.compatible edge wall hIncident sheet

/-- **The uniform expansion is the resolution expansion at the joined
resolution.**  A literal equality of gluing data, so every statement below
specializes to `Count.GeometricUniformExpansion`. -/
theorem uniform_eq_resolutionDatum (base : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool)
    (hCompatible : GlobalResolution.OldCompatible base wall right (joined base wall)) :
    GeometricUniformExpansion.data base wall right =
      GlobalResolution.datum base wall right (joined base wall) hCompatible := by
  apply eq_resolutionDatum base wall right _ _ hCompatible
  · exact GeometricUniformExpansion.vertexPartition base wall right _
  · exact GeometricUniformExpansion.vertexPartition base wall right _
  · intro vertex _
    exact GeometricUniformExpansion.vertexPartition base wall right _
  · exact GeometricUniformExpansion.edgePartition_none base wall right
  · exact GeometricUniformExpansion.edgePartition_some base wall right

end DraismaVargas.Count.ResolutionExpansion
