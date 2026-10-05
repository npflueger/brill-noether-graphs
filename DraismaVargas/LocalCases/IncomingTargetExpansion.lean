module

public import DraismaVargas.LocalCases.M11IncomingCoordinates

@[expose] public section

/-!
# Re-expanding an actual contracted incoming target

Contracting a unique nonloop occurrence and then expanding its merged vertex
recovers the original graph.  The expansion side of each retained occurrence is
read from its actual unfolded endpoints, not chosen from a displayed model.
The explicit occurrence equivalence preserves even the stored orientation.

For a connected genus-zero incoming target, unordered endpoint fibres are
singletons, so `GluingTransport.edgeEquiv` agrees with that explicit dictionary.
This supplies the target-only reconstruction and exact Option column matching;
it does not identify source partitions with an M11 candidate or prove an incoming
cover matching theorem.
-/

namespace DraismaVargas.LocalCases.IncomingTargetExpansion

open DraismaVargas.Infrastructure GraphContraction GluingContraction
open M11IncomingCoordinates

variable {target : CFGraph} {a b : target.V} {contracted : target.edges}

/-- Move a retained occurrence's merged endpoint to the fresh vertex exactly
when its original unfolded occurrence meets the removed vertex. -/
noncomputable def right
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (edge : (contract target hab hOne).edges) : Bool :=
  decide ((unfoldEdge hc hab hOne edge : target.V × target.V).1 = b ∨
    (unfoldEdge hc hab hOne edge : target.V × target.V).2 = b)

/-- Retained vertices are included literally; the fresh vertex restores `b`. -/
noncomputable def vertexEquiv (hab : a ≠ b) (hOne : num_edges target a b = 1) :
    TargetExpansion.Vertex (contract target hab hOne) ≃ target.V where
  toFun
    | Sum.inl vertex => vertex.1
    | Sum.inr _ => b
  invFun vertex := if h : vertex = b then Sum.inr () else Sum.inl ⟨vertex, h⟩
  left_inv := by
    intro vertex
    cases vertex with
    | inl vertex =>
      change (if h : vertex.1 = b then Sum.inr () else Sum.inl ⟨vertex.1, h⟩) = Sum.inl vertex
      rw [dite_eq_right vertex.2]
      rfl
    | inr fresh =>
      cases fresh
      change (if h : b = b then Sum.inr () else Sum.inl ⟨b, h⟩ :
        TargetExpansion.Vertex (contract target hab hOne)) = Sum.inr ()
      rw [dite_eq_left rfl]
  right_inv := by
    intro vertex
    dsimp only
    split_ifs with h
    · exact h.symm
    · rfl

@[simp] theorem vertexEquiv_old (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (vertex : (contract target hab hOne).V) :
    vertexEquiv hab hOne (TargetExpansion.oldVertex _ vertex) = vertex.1 := rfl

@[simp] theorem vertexEquiv_fresh (hab : a ≠ b) (hOne : num_edges target a b = 1) :
    vertexEquiv hab hOne (TargetExpansion.freshVertex _) = b := rfl

private theorem restore_endpoint
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (edge : (contract target hab hOne).edges)
    (first second : target.V) (hApart : fold target hab first ≠ fold target hab second)
    (hRight : right hc hab hOne edge = decide (first = b ∨ second = b)) :
    vertexEquiv hab hOne (TargetExpansion.expandedEndpoint (contract target hab hOne) ⟨a, hab⟩
      (right hc hab hOne) edge (fold target hab first)) = first := by
  classical
  by_cases hFirst : first = b
  · subst first
    have hR : right hc hab hOne edge = true := by simp [hRight]
    simp only [TargetExpansion.expandedEndpoint, hR, ↓reduceIte, fold_self]
    erw [ite_eq_left rfl]
    rfl
  · by_cases hSecond : second = b
    · have hNotWall : fold target hab first ≠ ⟨a, hab⟩ := by
        simpa only [hSecond, fold_self] using hApart
      have hR : right hc hab hOne edge = true := by simp [hRight, hSecond]
      simp only [TargetExpansion.expandedEndpoint, hR, ↓reduceIte]
      erw [ite_eq_right hNotWall]
      change (fold target hab first).1 = first
      rw [fold_of_ne target hab hFirst]
    · have hR : right hc hab hOne edge = false := by simp [hRight, hFirst, hSecond]
      simp only [TargetExpansion.expandedEndpoint, hR, Bool.false_eq_true, ↓reduceIte,
        fold_of_ne target hab hFirst]
      rfl

/-- Both stored endpoints of each retained occurrence are restored in order. -/
theorem oldEnds_map
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (edge : (contract target hab hOne).edges) :
    (vertexEquiv hab hOne (TargetExpansion.oldEnds (contract target hab hOne) ⟨a, hab⟩ (right hc hab hOne) edge).1,
      vertexEquiv hab hOne (TargetExpansion.oldEnds (contract target hab hOne) ⟨a, hab⟩ (right hc hab hOne) edge).2) =
      (unfoldEdge hc hab hOne edge : target.V × target.V) := by
  have hFold := fold_unfoldEdge hc hab hOne edge
  have hApart :
      fold target hab (unfoldEdge hc hab hOne edge : target.V × target.V).1 ≠
      fold target hab (unfoldEdge hc hab hOne edge : target.V × target.V).2 := by
    intro hEq
    apply GluingContraction.fst_ne_snd edge
    exact (congrArg Prod.fst hFold).symm.trans (hEq.trans (congrArg Prod.snd hFold))
  change (vertexEquiv hab hOne (TargetExpansion.expandedEndpoint (contract target hab hOne) ⟨a, hab⟩
      (right hc hab hOne) edge (edge : (contract target hab hOne).V × (contract target hab hOne).V).1),
    vertexEquiv hab hOne (TargetExpansion.expandedEndpoint (contract target hab hOne) ⟨a, hab⟩
      (right hc hab hOne) edge (edge : (contract target hab hOne).V × (contract target hab hOne).V).2)) = _
  rw [← hFold]
  apply Prod.ext
  · exact restore_endpoint hc hab hOne edge _ _ hApart rfl
  · apply restore_endpoint hc hab hOne edge _ _ hApart.symm
    simp only [right, or_comm]

/-- Literal occurrence dictionary: the new occurrence restores `contracted`,
and a retained occurrence restores its `unfoldEdge`. -/
noncomputable def edgeEquiv
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    (TargetExpansion.graph (contract target hab hOne) ⟨a, hab⟩ (right hc hab hOne)).edges ≃
      target.edges :=
  (TargetExpansion.occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (right hc hab hOne)).symm.trans
    (incomingColumnEquiv hc hab hOne)

theorem edgeEquiv_ends
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (edge : (TargetExpansion.graph (contract target hab hOne) ⟨a, hab⟩ (right hc hab hOne)).edges) :
    (edgeEquiv hc hab hOne edge : target.V × target.V) =
      (vertexEquiv hab hOne edge.1.1, vertexEquiv hab hOne edge.1.2) := by
  obtain ⟨column, rfl⟩ :=
    (TargetExpansion.occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (right hc hab hOne)).surjective edge
  simp only [edgeEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  cases column with
  | none =>
    rw [incomingColumnEquiv_none, hc]
    rfl
  | some old =>
    rw [incomingColumnEquiv_some]
    erw [TargetExpansion.occurrenceEquiv_some]
    exact (oldEnds_map hc hab hOne old).symm

/-- Actual target reconstruction, without a tree or cover-isomorphism premise. -/
noncomputable def graphIso
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    Utilities.CFGraphIso
      (TargetExpansion.graph (contract target hab hOne) ⟨a, hab⟩ (right hc hab hOne)) target where
  vertexEquiv := vertexEquiv hab hOne
  map_num_edges first second := by
    rw [← GluingTransport.card_edgeKey_fiber, ← GluingTransport.card_edgeKey_fiber]
    symm
    apply Fintype.card_congr
    apply (edgeEquiv hc hab hOne).subtypeEquiv
    intro edge
    unfold GluingTransport.edgeKey
    rw [edgeEquiv_ends]
    simp only [Sym2.eq_iff]
    constructor
    · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
      · exact Or.inl ⟨congrArg (vertexEquiv hab hOne) h₁,
          congrArg (vertexEquiv hab hOne) h₂⟩
      · exact Or.inr ⟨congrArg (vertexEquiv hab hOne) h₁,
          congrArg (vertexEquiv hab hOne) h₂⟩
    · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
      · exact Or.inl ⟨(vertexEquiv hab hOne).injective h₁,
          (vertexEquiv hab hOne).injective h₂⟩
      · exact Or.inr ⟨(vertexEquiv hab hOne).injective h₁,
          (vertexEquiv hab hOne).injective h₂⟩

/-- On a tree target, the general transport's unordered-fibre choice agrees
with the literal contraction/re-expansion occurrence dictionary.  This is the
only result here which needs the incoming target's tree assumptions. -/
theorem transport_edgeEquiv_eq
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    GluingTransport.edgeEquiv (graphIso hc hab hOne) = edgeEquiv hc hab hOne := by
  classical
  apply Equiv.ext
  intro edge
  let first := vertexEquiv hab hOne edge.1.1
  let second := vertexEquiv hab hOne edge.1.2
  have hCard : Fintype.card {e : target.edges //
      GluingTransport.edgeKey target e = s(first, second)} ≤ 1 := by
    rw [GluingTransport.card_edgeKey_fiber]
    exact IteratedContraction.num_edges_le_one_of_genus_zero_of_connected
      target hConnected hGenus first second
  have hUnique := Fintype.card_le_one_iff_subsingleton.mp hCard
  have hCanonical : GluingTransport.edgeKey target
      (GluingTransport.edgeEquiv (graphIso hc hab hOne) edge) = s(first, second) :=
    GluingTransport.edgeEquiv_key (graphIso hc hab hOne) edge
  have hLiteral : GluingTransport.edgeKey target (edgeEquiv hc hab hOne edge) =
      s(first, second) := by
    unfold GluingTransport.edgeKey
    rw [edgeEquiv_ends]
  exact congrArg Subtype.val (hUnique.elim
    ⟨GluingTransport.edgeEquiv (graphIso hc hab hOne) edge, hCanonical⟩
    ⟨edgeEquiv hc hab hOne edge, hLiteral⟩)

/-- Exact common column dictionary, including the newly expanded occurrence. -/
theorem transport_occurrenceEquiv
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (column : Option (contract target hab hOne).edges) :
    GluingTransport.edgeEquiv (graphIso hc hab hOne)
      (TargetExpansion.occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
        (right hc hab hOne) column) = incomingColumnEquiv hc hab hOne column := by
  rw [transport_edgeEquiv_eq hc hab hOne hConnected hGenus]
  exact (incomingColumnEquiv hc hab hOne).congr_arg
    ((TargetExpansion.occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
      (right hc hab hOne)).symm_apply_apply column)

theorem transport_occurrenceEquiv_none
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    GluingTransport.edgeEquiv (graphIso hc hab hOne)
      (TargetExpansion.occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
        (right hc hab hOne) none) = contracted :=
  transport_occurrenceEquiv hc hab hOne hConnected hGenus none

theorem transport_occurrenceEquiv_some
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (edge : (contract target hab hOne).edges) :
    GluingTransport.edgeEquiv (graphIso hc hab hOne)
      (TargetExpansion.occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
        (right hc hab hOne) (some edge)) = unfoldEdge hc hab hOne edge :=
  transport_occurrenceEquiv hc hab hOne hConnected hGenus (some edge)

end DraismaVargas.LocalCases.IncomingTargetExpansion
