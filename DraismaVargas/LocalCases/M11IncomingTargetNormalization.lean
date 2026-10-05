module

public import DraismaVargas.LocalCases.IncomingW2TargetPlacement

@[expose] public section

/-!
# Literal incoming target normalization for M11

Two expansions with the same incident placements are isomorphic by identity
vertices, even if their side predicates differ away from the wall.  Complementary
incident placements are isomorphic by exchanging the retained wall and fresh
vertices.  Both maps keep each `Option target.edges` occurrence label; only the
stored orientation of the new occurrence reverses in the swap case.

Composing with actual contraction/re-expansion gives incoming-to-normalized
target isomorphisms.  On incoming tree targets the canonical `GluingTransport`
occurrence map equals this literal dictionary, since unordered endpoint fibres
are singletons.  The checked incoming placement census then selects the split's
constant-true assignment or the joined candidate's actual `star.right` assignment.
No fixed left/right location of `profile.doubleLabel` is imposed.

The final `exists_candidateTargetIso` matches the real family's target and
`M11CommonBalance.columnEquiv`, with position 0 or 2.  It proves no equality of
source partitions, cover isomorphism, stable-row matching, or matrix matching;
in particular the two split candidates need not have isomorphic source covers
merely because their targets agree.
-/

namespace DraismaVargas.LocalCases.M11IncomingTargetNormalization

open DraismaVargas.Infrastructure TargetExpansion GluingContraction
open W2R1Target

variable {target : CFGraph} {wall : target.V}

/-- Preserve the literal Option occurrence labels between two expansions. -/
noncomputable def columnEquiv (first second : target.edges → Bool) :
    (graph target wall first).edges ≃ (graph target wall second).edges :=
  (occurrenceEquiv target wall first).symm.trans (occurrenceEquiv target wall second)

@[simp] theorem columnEquiv_apply (first second : target.edges → Bool)
    (column : Option target.edges) :
    columnEquiv (wall := wall) first second (occurrenceEquiv target wall first column) =
      occurrenceEquiv target wall second column := by
  exact (occurrenceEquiv target wall second).congr_arg
    ((occurrenceEquiv target wall first).symm_apply_apply column)

private theorem expandedEndpoint_congr (first second : target.edges → Bool)
    (hSupport : ∀ edge ∈ GluingDatum.incidentEdges wall, first edge = second edge)
    (edge : target.edges) (vertex : target.V)
    (hEnd : edge.1.1 = vertex ∨ edge.1.2 = vertex) :
    expandedEndpoint target wall first edge vertex =
      expandedEndpoint target wall second edge vertex := by
  by_cases hWall : vertex = wall
  · have hAt : edge ∈ GluingDatum.incidentEdges wall :=
      (mem_incidentEdges_iff wall edge).mpr (hWall ▸ hEnd)
    rw [expandedEndpoint, expandedEndpoint, hSupport edge hAt]
  · simp [expandedEndpoint, hWall]

/-- The only nontrivial vertex permutation: exchange the retained wall with
the fresh endpoint and leave every other retained vertex unchanged. -/
noncomputable def swapVertices : Vertex target ≃ Vertex target :=
  Equiv.swap (oldVertex target wall) (freshVertex target)

@[simp] theorem swapVertices_old_wall :
    swapVertices (target := target) (wall := wall) (oldVertex target wall) =
      freshVertex target := Equiv.swap_apply_left _ _

@[simp] theorem swapVertices_fresh :
    swapVertices (target := target) (wall := wall) (freshVertex target) =
      oldVertex target wall := Equiv.swap_apply_right _ _

theorem swapVertices_old_of_ne (vertex : target.V) (h : vertex ≠ wall) :
    swapVertices (target := target) (wall := wall) (oldVertex target vertex) =
      oldVertex target vertex := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact fun heq => h (Sum.inl.inj heq)
  · exact Sum.inl_ne_inr

private theorem expandedEndpoint_swap (first second : target.edges → Bool)
    (hSupport : ∀ edge ∈ GluingDatum.incidentEdges wall, first edge = !(second edge))
    (edge : target.edges) (vertex : target.V)
    (hEnd : edge.1.1 = vertex ∨ edge.1.2 = vertex) :
    swapVertices (target := target) (wall := wall)
      (expandedEndpoint target wall first edge vertex) =
      expandedEndpoint target wall second edge vertex := by
  by_cases hWall : vertex = wall
  · have hAt : edge ∈ GluingDatum.incidentEdges wall :=
      (mem_incidentEdges_iff wall edge).mpr (hWall ▸ hEnd)
    rw [hWall, expandedEndpoint, hSupport edge hAt, expandedEndpoint]
    cases second edge <;> simp
  · simp only [expandedEndpoint, hWall, ↓reduceIte, ite_self]
    exact swapVertices_old_of_ne vertex hWall

/-- The narrow graph-isomorphism construction consumes literal Option-column
endpoint identities, not an assumed graph-isomorphism or arbitrary row map. -/
noncomputable def isoOfColumns (first second : target.edges → Bool)
    (vertices : Vertex target ≃ Vertex target)
    (hColumns : ∀ column : Option target.edges,
      GluingTransport.edgeKey (graph target wall second)
        (occurrenceEquiv target wall second column) =
      s(vertices (occurrenceEquiv target wall first column).1.1,
        vertices (occurrenceEquiv target wall first column).1.2)) :
    Utilities.CFGraphIso (graph target wall first) (graph target wall second) where
  vertexEquiv := vertices
  map_num_edges x y := by
    rw [← GluingTransport.card_edgeKey_fiber, ← GluingTransport.card_edgeKey_fiber]
    symm
    apply Fintype.card_congr
    apply (columnEquiv (wall := wall) first second).subtypeEquiv
    intro edge
    obtain ⟨column, rfl⟩ := (occurrenceEquiv target wall first).surjective edge
    rw [columnEquiv_apply, hColumns]
    change (s((occurrenceEquiv target wall first column).1.1,
      (occurrenceEquiv target wall first column).1.2) : Sym2 (Vertex target)) = s(x, y) ↔
      (s(vertices (occurrenceEquiv target wall first column).1.1,
        vertices (occurrenceEquiv target wall first column).1.2) : Sym2 (Vertex target)) =
        s(vertices x, vertices y)
    constructor
    · intro h
      exact congrArg (Sym2.map vertices) h
    · intro h
      exact Sym2.map.injective vertices.injective h

theorem support_columns (first second : target.edges → Bool)
    (hSupport : ∀ edge ∈ GluingDatum.incidentEdges wall, first edge = second edge)
    (column : Option target.edges) :
    GluingTransport.edgeKey (graph target wall second)
      (occurrenceEquiv target wall second column) =
      s((occurrenceEquiv target wall first column).1.1,
        (occurrenceEquiv target wall first column).1.2) := by
  cases column with
  | none => rfl
  | some edge =>
    unfold GluingTransport.edgeKey
    erw [occurrenceEquiv_some, occurrenceEquiv_some]
    exact congrArg (fun pair : Vertex target × Vertex target => s(pair.1, pair.2))
      (Prod.ext
        (expandedEndpoint_congr second first (fun edge h => (hSupport edge h).symm) edge _ (Or.inl rfl))
        (expandedEndpoint_congr second first (fun edge h => (hSupport edge h).symm) edge _ (Or.inr rfl)))

theorem swap_columns (first second : target.edges → Bool)
    (hSupport : ∀ edge ∈ GluingDatum.incidentEdges wall, first edge = !(second edge))
    (column : Option target.edges) :
    GluingTransport.edgeKey (graph target wall second)
      (occurrenceEquiv target wall second column) =
      s(swapVertices (target := target) (wall := wall) (occurrenceEquiv target wall first column).1.1,
        swapVertices (target := target) (wall := wall) (occurrenceEquiv target wall first column).1.2) := by
  cases column with
  | none =>
    change s(oldVertex target wall, freshVertex target) =
      s(swapVertices (oldVertex target wall), swapVertices (freshVertex target))
    rw [swapVertices_old_wall, swapVertices_fresh]
    exact Sym2.eq_swap
  | some edge =>
    unfold GluingTransport.edgeKey
    erw [occurrenceEquiv_some, occurrenceEquiv_some]
    change s((oldEnds target wall second edge).1, (oldEnds target wall second edge).2) = _
    apply congrArg₂ (fun x y : Vertex target => s(x, y))
    · exact (expandedEndpoint_swap first second hSupport edge _ (Or.inl rfl)).symm
    · exact (expandedEndpoint_swap first second hSupport edge _ (Or.inr rfl)).symm

/-- Off-wall side values have no effect on the actual target endpoints. -/
noncomputable def supportIso (first second : target.edges → Bool)
    (hSupport : ∀ edge ∈ GluingDatum.incidentEdges wall, first edge = second edge) :
    Utilities.CFGraphIso (graph target wall first) (graph target wall second) :=
  isoOfColumns first second (Equiv.refl _) (support_columns first second hSupport)

/-- Complementing incident placements exchanges the two expanded endpoints.
The new occurrence is preserved, though its stored orientation is reversed. -/
noncomputable def swapIso (first second : target.edges → Bool)
    (hSupport : ∀ edge ∈ GluingDatum.incidentEdges wall, first edge = !(second edge)) :
    Utilities.CFGraphIso (graph target wall first) (graph target wall second) :=
  isoOfColumns first second swapVertices (swap_columns first second hSupport)

@[simp] theorem supportIso_vertex (first second : target.edges → Bool)
    (hSupport : ∀ edge ∈ GluingDatum.incidentEdges wall, first edge = second edge) :
    (supportIso first second hSupport).vertexEquiv = Equiv.refl (Vertex target) := rfl

@[simp] theorem swapIso_vertex (first second : target.edges → Bool)
    (hSupport : ∀ edge ∈ GluingDatum.incidentEdges wall, first edge = !(second edge)) :
    (swapIso first second hSupport).vertexEquiv = swapVertices (wall := wall) := rfl

/-- The support census determines whether the literal endpoint map is the
identity or the explicit wall/fresh transposition. -/
noncomputable def normalizationIso (first second : target.edges → Bool)
    (hPlacement : (∀ edge ∈ GluingDatum.incidentEdges wall, first edge = second edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges wall, first edge = !(second edge))) :
    Utilities.CFGraphIso (graph target wall first) (graph target wall second) := by
  classical
  exact if h : ∀ edge ∈ GluingDatum.incidentEdges wall, first edge = second edge
    then supportIso first second h
    else swapIso first second (hPlacement.resolve_left h)

theorem normalizationIso_columns (first second : target.edges → Bool)
    (hPlacement : (∀ edge ∈ GluingDatum.incidentEdges wall, first edge = second edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges wall, first edge = !(second edge)))
    (column : Option target.edges) :
    GluingTransport.edgeKey (graph target wall second)
      (occurrenceEquiv target wall second column) =
      s((normalizationIso first second hPlacement).vertexEquiv
          (occurrenceEquiv target wall first column).1.1,
        (normalizationIso first second hPlacement).vertexEquiv
          (occurrenceEquiv target wall first column).1.2) := by
  classical
  unfold normalizationIso
  split_ifs with h
  · exact support_columns first second h column
  · exact swap_columns first second (hPlacement.resolve_left h) column

section Incoming

open GraphContraction IncomingW2TargetPlacement M11IncomingCoordinates

variable {incoming : CFGraph} {a b : incoming.V} {contracted : incoming.edges}

/-- Reconstruct the actual incoming target, then normalize by identity or
the explicit endpoint transposition.  The side census is a target-only input. -/
noncomputable def incomingIso
    (hc : (contracted : incoming.V × incoming.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges incoming a b = 1)
    (second : (contract incoming hab hOne).edges → Bool)
    (hPlacement :
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = second edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = !(second edge))) :
    Utilities.CFGraphIso incoming (graph (contract incoming hab hOne) ⟨a, hab⟩ second) :=
  (IncomingTargetExpansion.graphIso hc hab hOne).symm.trans
    (normalizationIso (IncomingTargetExpansion.right hc hab hOne) second hPlacement)

theorem incomingIso_vertex
    (hc : (contracted : incoming.V × incoming.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges incoming a b = 1)
    (second : (contract incoming hab hOne).edges → Bool)
    (hPlacement :
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = second edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = !(second edge)))
    (vertex : incoming.V) :
    (incomingIso hc hab hOne second hPlacement).vertexEquiv vertex =
      (normalizationIso (IncomingTargetExpansion.right hc hab hOne) second hPlacement).vertexEquiv
        ((IncomingTargetExpansion.vertexEquiv hab hOne).symm vertex) := rfl

theorem incomingIso_column_key
    (hc : (contracted : incoming.V × incoming.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges incoming a b = 1)
    (second : (contract incoming hab hOne).edges → Bool)
    (hPlacement :
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = second edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = !(second edge)))
    (column : Option (contract incoming hab hOne).edges) :
    GluingTransport.edgeKey (graph (contract incoming hab hOne) ⟨a, hab⟩ second)
      (occurrenceEquiv (contract incoming hab hOne) ⟨a, hab⟩ second column) =
      GluingTransport.mappedEdgeKey (incomingIso hc hab hOne second hPlacement)
        (incomingColumnEquiv hc hab hOne column) := by
  let first := IncomingTargetExpansion.right hc hab hOne
  let occurrence := occurrenceEquiv (contract incoming hab hOne) ⟨a, hab⟩ first column
  have hEdge : IncomingTargetExpansion.edgeEquiv hc hab hOne occurrence =
      incomingColumnEquiv hc hab hOne column := by
    exact (incomingColumnEquiv hc hab hOne).congr_arg
      ((occurrenceEquiv (contract incoming hab hOne) ⟨a, hab⟩ first).symm_apply_apply column)
  have hEnds := IncomingTargetExpansion.edgeEquiv_ends hc hab hOne occurrence
  rw [hEdge] at hEnds
  rw [normalizationIso_columns first second hPlacement]
  unfold GluingTransport.mappedEdgeKey
  apply congrArg₂ (fun x y : Vertex (contract incoming hab hOne) => s(x, y))
  · change _ = (normalizationIso first second hPlacement).vertexEquiv
      ((IncomingTargetExpansion.vertexEquiv hab hOne).symm
        (incomingColumnEquiv hc hab hOne column).1.1)
    rw [show (incomingColumnEquiv hc hab hOne column).1.1 =
      IncomingTargetExpansion.vertexEquiv hab hOne occurrence.1.1 from congrArg Prod.fst hEnds]
    exact congrArg (normalizationIso first second hPlacement).vertexEquiv
      ((IncomingTargetExpansion.vertexEquiv hab hOne).symm_apply_apply occurrence.1.1).symm
  · change _ = (normalizationIso first second hPlacement).vertexEquiv
      ((IncomingTargetExpansion.vertexEquiv hab hOne).symm
        (incomingColumnEquiv hc hab hOne column).1.2)
    rw [show (incomingColumnEquiv hc hab hOne column).1.2 =
      IncomingTargetExpansion.vertexEquiv hab hOne occurrence.1.2 from congrArg Prod.snd hEnds]
    exact congrArg (normalizationIso first second hPlacement).vertexEquiv
      ((IncomingTargetExpansion.vertexEquiv hab hOne).symm_apply_apply occurrence.1.2).symm

/-- Tree fibres are singletons, so canonical graph transport preserves every
literal Option column of the incoming contraction, including `none`. -/
theorem incomingIso_occurrence
    (hc : (contracted : incoming.V × incoming.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges incoming a b = 1)
    (second : (contract incoming hab hOne).edges → Bool)
    (hPlacement :
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = second edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = !(second edge)))
    (hConnected : graph_connected incoming) (hGenus : genus incoming = 0)
    (column : Option (contract incoming hab hOne).edges) :
    GluingTransport.edgeEquiv (incomingIso hc hab hOne second hPlacement)
      (incomingColumnEquiv hc hab hOne column) =
      occurrenceEquiv (contract incoming hab hOne) ⟨a, hab⟩ second column := by
  classical
  let iso := incomingIso hc hab hOne second hPlacement
  let output := graph (contract incoming hab hOne) ⟨a, hab⟩ second
  let first := iso.vertexEquiv (incomingColumnEquiv hc hab hOne column).1.1
  let last := iso.vertexEquiv (incomingColumnEquiv hc hab hOne column).1.2
  have hCard : Fintype.card {e : output.edges //
      GluingTransport.edgeKey output e = s(first, last)} ≤ 1 := by
    rw [GluingTransport.card_edgeKey_fiber]
    change num_edges output (iso.vertexEquiv _) (iso.vertexEquiv _) ≤ 1
    rw [iso.map_num_edges]
    exact IteratedContraction.num_edges_le_one_of_genus_zero_of_connected
      incoming hConnected hGenus _ _
  have hUnique := Fintype.card_le_one_iff_subsingleton.mp hCard
  have hCanonical := GluingTransport.edgeEquiv_key iso (incomingColumnEquiv hc hab hOne column)
  have hLiteral := incomingIso_column_key hc hab hOne second hPlacement column
  exact congrArg Subtype.val (hUnique.elim
    ⟨GluingTransport.edgeEquiv iso (incomingColumnEquiv hc hab hOne column), hCanonical⟩
    ⟨occurrenceEquiv (contract incoming hab hOne) ⟨a, hab⟩ second column, hLiteral⟩)

/-- Either incoming leaf orientation normalizes to the split's constant-true
assignment; agreement is asserted only where the assignment affects endpoints. -/
theorem splitPlacement
    (hc : (contracted : incoming.V × incoming.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges incoming a b = 1)
    (star : TwoStar (contract incoming hab hOne) ⟨a, hab⟩)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨ (GluingDatum.incidentEdges b).card = 1) :
    (∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = true) ∨
    (∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = !true) := by
  rcases hLeaf with hLeft | hRight
  · left
    intro edge hAt
    obtain ⟨label, hLabel⟩ := star.label.surjective ⟨edge, hAt⟩
    have hEdge : star.edge label = edge := congrArg Subtype.val hLabel
    rw [← hEdge]
    exact right_star_of_leaf_left hc hab hOne star hLeft label
  · right
    intro edge hAt
    obtain ⟨label, hLabel⟩ := star.label.surjective ⟨edge, hAt⟩
    have hEdge : star.edge label = edge := congrArg Subtype.val hLabel
    rw [← hEdge]
    exact right_star_of_leaf_right hc hab hOne star hRight label

/-- Normalize to the actual joined candidate's `star.right` (label 1), without
fixing which source-profile label is double. -/
theorem joinedPlacement
    (hc : (contracted : incoming.V × incoming.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges incoming a b = 1)
    (star : TwoStar (contract incoming hab hOne) ⟨a, hab⟩)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    (∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = star.right edge) ∨
    (∀ edge ∈ GluingDatum.incidentEdges (target := contract incoming hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = !(star.right edge)) := by
  classical
  obtain ⟨label, hPredicate⟩ := right_eq_singleton_of_divalent hc hab hOne star hLeft hRight
  fin_cases label
  · right
    intro edge hAt
    obtain ⟨label, hLabel⟩ := star.label.surjective ⟨edge, hAt⟩
    have hEdge : star.edge label = edge := congrArg Subtype.val hLabel
    rw [← hEdge]
    have hNe : star.edge 0 ≠ star.edge 1 := star.edge_injective.ne (by decide)
    fin_cases label <;> simp [hPredicate, TwoStar.right, hNe, Ne.symm hNe]
  · left
    intro edge _
    simp only [hPredicate, TwoStar.right]
    by_cases h : edge = star.edge 1
    · simp only [h, decide_true]
      exact decide_eq_true rfl
    · simp only [h, decide_false]
      exact decide_eq_false h

noncomputable def splitIso
    (hc : (contracted : incoming.V × incoming.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges incoming a b = 1)
    (star : TwoStar (contract incoming hab hOne) ⟨a, hab⟩)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨ (GluingDatum.incidentEdges b).card = 1) :
    Utilities.CFGraphIso incoming (graph (contract incoming hab hOne) ⟨a, hab⟩ (fun _ => true)) :=
  incomingIso hc hab hOne (fun _ => true) (splitPlacement hc hab hOne star hLeaf)

noncomputable def joinedIso
    (hc : (contracted : incoming.V × incoming.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges incoming a b = 1)
    (star : TwoStar (contract incoming hab hOne) ⟨a, hab⟩)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    Utilities.CFGraphIso incoming (graph (contract incoming hab hOne) ⟨a, hab⟩ star.right) :=
  incomingIso hc hab hOne star.right (joinedPlacement hc hab hOne star hLeft hRight)

theorem splitIso_occurrence
    (hc : (contracted : incoming.V × incoming.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges incoming a b = 1)
    (star : TwoStar (contract incoming hab hOne) ⟨a, hab⟩)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨ (GluingDatum.incidentEdges b).card = 1)
    (hConnected : graph_connected incoming) (hGenus : genus incoming = 0)
    (column : Option (contract incoming hab hOne).edges) :
    GluingTransport.edgeEquiv (splitIso hc hab hOne star hLeaf)
      (incomingColumnEquiv hc hab hOne column) =
      occurrenceEquiv (contract incoming hab hOne) ⟨a, hab⟩ (fun _ => true) column :=
  incomingIso_occurrence hc hab hOne _ (splitPlacement hc hab hOne star hLeaf)
    hConnected hGenus column

theorem joinedIso_occurrence
    (hc : (contracted : incoming.V × incoming.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges incoming a b = 1)
    (star : TwoStar (contract incoming hab hOne) ⟨a, hab⟩)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2)
    (hConnected : graph_connected incoming) (hGenus : genus incoming = 0)
    (column : Option (contract incoming hab hOne).edges) :
    GluingTransport.edgeEquiv (joinedIso hc hab hOne star hLeft hRight)
      (incomingColumnEquiv hc hab hOne column) =
      occurrenceEquiv (contract incoming hab hOne) ⟨a, hab⟩ star.right column :=
  incomingIso_occurrence hc hab hOne _ (joinedPlacement hc hab hOne star hLeft hRight)
    hConnected hGenus column

/-- The target-only matching endpoint for the actual M11 family.  It selects
the first split or joined target using the proved incoming valency split and
preserves `M11CommonBalance.columnEquiv` at every literal column.  This is not a
source-cover, sheet-partition, stable-row, or matrix matching theorem. -/
theorem exists_candidateTargetIso {degree : ℕ} (data : GluingDatum incoming degree)
    (hc : (contracted : incoming.V × incoming.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges incoming a b = 1) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (hConnected : graph_connected incoming) (hGenus : genus incoming = 0)
    {star : TwoStar (contract incoming hab hOne) ⟨a, hab⟩}
    (input : SecondEquation.W2SourceInput (contractDatum data hc hab hOne) star)
    {block : W4Assembly.WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile (contractDatum data hc hab hOne) star block)
    (hCard : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard block.1 = 2) :
    ∃ position : Fin 3, (position = 0 ∨ position = 2) ∧
      ∃ iso : Utilities.CFGraphIso incoming
        (M11RemoteCandidates.candidates input profile hCard position).outgoingTarget,
        ∀ column : Option (contract incoming hab hOne).edges,
          GluingTransport.edgeEquiv iso (incomingColumnEquiv hc hab hOne column) =
            M11CommonBalance.columnEquiv input profile hCard position column := by
  rcases SecondEquation.valencySplit_of_twoStar data hc hab hOne hValid hMinimal star with
    ⟨hLeft, hRight, _, _⟩ | ⟨hLeft, _, _, _⟩ | ⟨_, hRight, _, _⟩
  · refine ⟨2, Or.inr rfl, joinedIso hc hab hOne star hLeft hRight, ?_⟩
    intro column
    exact joinedIso_occurrence hc hab hOne star hLeft hRight hConnected hGenus column
  · refine ⟨0, Or.inl rfl, splitIso hc hab hOne star (Or.inl hLeft), ?_⟩
    intro column
    exact splitIso_occurrence hc hab hOne star (Or.inl hLeft) hConnected hGenus column
  · refine ⟨0, Or.inl rfl, splitIso hc hab hOne star (Or.inr hRight), ?_⟩
    intro column
    exact splitIso_occurrence hc hab hOne star (Or.inr hRight) hConnected hGenus column

end Incoming

end DraismaVargas.LocalCases.M11IncomingTargetNormalization
