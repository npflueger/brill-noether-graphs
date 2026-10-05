module

public import DraismaVargasCount.GeometricTransport
public import DraismaVargas.Infrastructure.GluingContraction
public import DraismaVargas.LocalCases.W4TargetPairings

@[expose] public section

/-!
# A target expansion remembers its own `2+2` split

Source: Draisma--Vargas Part I (arXiv:1909.12924), the inherited properties of limits
(`section-inherited-properties`: the W4 target expansions of a four-valent wall), together
with Vargas, Part II (arXiv:2609.09109), the star of a codimension-one wall. The three
pairings themselves are
`DraismaVargas.LocalCases.W4TargetPairings`.

## What is proved

Fix a wall vertex `wall` of a target `target` and two side assignments
`right`, `right'`. Suppose the two expanded targets are related by a vertex
bijection and an occurrence bijection that preserves unordered endpoint pairs
and **matches the canonical occurrence labels** of `TargetExpansion`. Then the
two assignments agree on every occurrence incident to `wall`, or are opposite
on every such occurrence (`incidentRight_eq_or_not`). For the three canonical
W4 pairings of a `FourStar` the opposite alternative is impossible, because
the star label `0` lies on the distinguished side of all three pairings;
hence the pairing index is determined (`pairing_eq_of_expansionIso`).

Only the *unordered* endpoint pair of each occurrence is used, which is exactly
what `Count.GeometricDatumIso` supplies; no orientation, no sheet partition
and no source data enter.

## What is NOT proved

Nothing here concerns gluing data, stars or counts. The hypothesis `hlabel` —
that the occurrence dictionary is the canonical one — is an explicit
hypothesis and is *not* derived here; in the applications it comes from
the coordinate rigidity of the frames (see `FrameColumnRigidity`). No claim is made that
the three expanded targets are pairwise non-isomorphic as abstract graphs: the statement
is that no isomorphism between them can preserve the canonical occurrence
labelling.

## Consumers

`W4StarParity` (`pairing_eq_of_frameIso2`) and `W4NonDiscreteStarCensus`
(`pairing_eq_of_frameIso`): distinct pairings give distinct star classes at a four-valent
wall.
-/

namespace DraismaVargas.Count.W4PairingRigidity

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open TargetExpansion W4TargetPairings
open GluingContraction (fst_ne_snd)

variable (target : CFGraph) (wall : target.V)

/-- The expanded copy of the wall named by a side value. -/
def sideVertex (side : Bool) : Vertex target :=
  if side then freshVertex target else oldVertex target wall

@[simp] theorem sideVertex_false : sideVertex target wall false = oldVertex target wall := rfl

@[simp] theorem sideVertex_true : sideVertex target wall true = freshVertex target := rfl

theorem sideVertex_injective : Function.Injective (sideVertex target wall) := by
  intro first second h
  cases first <;> cases second <;> first
    | rfl
    | exact absurd h Sum.inl_ne_inr
    | exact absurd h.symm Sum.inl_ne_inr

variable {target wall} {right right' : target.edges → Bool}

theorem expandedEndpoint_wall (edge : target.edges) :
    expandedEndpoint target wall right edge wall = sideVertex target wall (right edge) := by
  simp only [expandedEndpoint, sideVertex, ite_true]

theorem expandedEndpoint_of_ne (edge : target.edges) {vertex : target.V}
    (h : vertex ≠ wall) :
    expandedEndpoint target wall right edge vertex = oldVertex target vertex := by
  simp only [expandedEndpoint, ite_eq_right h, ite_self]

theorem oldVertex_ne_sideVertex {u : target.V} (hu : u ≠ wall) (side : Bool) :
    oldVertex target u ≠ sideVertex target wall side := by
  cases side with
  | false => exact fun h ↦ hu (Sum.inl_injective h)
  | true => exact Sum.inl_ne_inr

section Iso

variable (vertices : (graph target wall right).V ≃ (graph target wall right').V)
  (edges : (graph target wall right).edges ≃ (graph target wall right').edges)
  (hends : ∀ edge : (graph target wall right).edges,
    UnorderedEnds vertices (edge : (graph target wall right).V × (graph target wall right).V)
      (edges edge : (graph target wall right').V × (graph target wall right').V))
  (hlabel : ∀ label : Option target.edges,
    edges (occurrenceEquiv target wall right label) =
      occurrenceEquiv target wall right' label)

include edges hends hlabel in
/-- The canonical label of the new occurrence is preserved, so the two
expanded copies of the wall are preserved, possibly interchanged. -/
theorem wallPair_map :
    (∀ side : Bool, vertices (sideVertex target wall side) = sideVertex target wall side) ∨
      (∀ side : Bool,
        vertices (sideVertex target wall side) = sideVertex target wall (!side)) := by
  have h := hends (occurrenceEquiv target wall right none)
  rw [hlabel none] at h
  change UnorderedEnds vertices (occurrenceEquiv target wall right none).1
    (occurrenceEquiv target wall right' none).1 at h
  rw [occurrenceEquiv_none, occurrenceEquiv_none] at h
  rcases h with h | h
  · refine Or.inl fun side ↦ ?_
    cases side with
    | false => exact (congrArg Prod.fst h).symm
    | true => exact (congrArg Prod.snd h).symm
  · refine Or.inr fun side ↦ ?_
    cases side with
    | false => exact (congrArg Prod.snd h).symm
    | true => exact (congrArg Prod.fst h).symm

variable {vertices edges}

/-- Nothing above an old vertex other than the wall is sent to an expanded
copy of the wall. -/
theorem sideVertex_ne_image
    (hpair : (∀ side : Bool, vertices (sideVertex target wall side) = sideVertex target wall side) ∨
      (∀ side : Bool,
        vertices (sideVertex target wall side) = sideVertex target wall (!side)))
    {u : target.V} (hu : u ≠ wall) (side : Bool) :
    vertices (oldVertex target u) ≠ sideVertex target wall side := by
  intro h
  rcases hpair with hFix | hSwap
  · exact oldVertex_ne_sideVertex hu side (vertices.injective (h.trans (hFix side).symm))
  · exact oldVertex_ne_sideVertex hu (!side)
      (vertices.injective (h.trans (by rw [hSwap (!side), Bool.not_not])))

include edges hends hlabel in
/-- The expanded wall copy an incident occurrence sits on is transported to the
expanded wall copy the other side assignment gives it. -/
theorem wallSide_map
    (hpair : (∀ side : Bool, vertices (sideVertex target wall side) = sideVertex target wall side) ∨
      (∀ side : Bool,
        vertices (sideVertex target wall side) = sideVertex target wall (!side)))
    (edge : target.edges) (hedge : edge ∈ GluingDatum.incidentEdges wall) :
    vertices (sideVertex target wall (right edge)) = sideVertex target wall (right' edge) := by
  have hIncident : (edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall := by
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      using hedge
  have hNe := fst_ne_snd edge
  have h := hends (occurrenceEquiv target wall right (some edge))
  rw [hlabel (some edge)] at h
  change UnorderedEnds vertices (occurrenceEquiv target wall right (some edge)).1
    (occurrenceEquiv target wall right' (some edge)).1 at h
  rw [occurrenceEquiv_some, occurrenceEquiv_some] at h
  rcases hIncident with hFirst | hSecond
  · have hOther : (edge : target.V × target.V).2 ≠ wall := fun hh ↦ hNe (hFirst.trans hh.symm)
    have hA : (oldEnds target wall right edge).1 = sideVertex target wall (right edge) := by
      show expandedEndpoint target wall right edge (edge : target.V × target.V).1 = _
      rw [hFirst, expandedEndpoint_wall]
    have hA' : (oldEnds target wall right' edge).1 = sideVertex target wall (right' edge) := by
      show expandedEndpoint target wall right' edge (edge : target.V × target.V).1 = _
      rw [hFirst, expandedEndpoint_wall]
    have hB : (oldEnds target wall right edge).2 =
        oldVertex target (edge : target.V × target.V).2 :=
      expandedEndpoint_of_ne (right := right) edge hOther
    rcases h with h | h
    · exact (hA'.symm.trans ((congrArg Prod.fst h).trans (congrArg vertices hA))).symm
    · exact absurd (((congrArg Prod.fst h).trans (congrArg vertices hB)).symm.trans hA')
        (sideVertex_ne_image hpair hOther (right' edge))
  · have hOther : (edge : target.V × target.V).1 ≠ wall := fun hh ↦ hNe (hh.trans hSecond.symm)
    have hA : (oldEnds target wall right edge).2 = sideVertex target wall (right edge) := by
      show expandedEndpoint target wall right edge (edge : target.V × target.V).2 = _
      rw [hSecond, expandedEndpoint_wall]
    have hA' : (oldEnds target wall right' edge).2 = sideVertex target wall (right' edge) := by
      show expandedEndpoint target wall right' edge (edge : target.V × target.V).2 = _
      rw [hSecond, expandedEndpoint_wall]
    have hB : (oldEnds target wall right edge).1 =
        oldVertex target (edge : target.V × target.V).1 :=
      expandedEndpoint_of_ne (right := right) edge hOther
    rcases h with h | h
    · exact (hA'.symm.trans ((congrArg Prod.snd h).trans (congrArg vertices hA))).symm
    · exact absurd (((congrArg Prod.snd h).trans (congrArg vertices hB)).symm.trans hA')
        (sideVertex_ne_image hpair hOther (right' edge))

variable (vertices edges)

include vertices edges hends hlabel in
/-- **Two expansions of the same wall with the same occurrence labels have the
same split, or exactly the opposite one.** -/
theorem incidentRight_eq_or_not :
    (∀ edge ∈ GluingDatum.incidentEdges wall, right' edge = right edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges wall, right' edge = !(right edge)) := by
  have hpair := wallPair_map (vertices := vertices) edges hends hlabel
  have hmap : ∀ edge ∈ GluingDatum.incidentEdges wall,
      vertices (sideVertex target wall (right edge)) = sideVertex target wall (right' edge) :=
    fun edge hedge ↦ wallSide_map hends hlabel hpair edge hedge
  rcases hpair with hFix | hSwap
  · refine Or.inl fun edge hedge ↦ ?_
    exact sideVertex_injective target wall ((hmap edge hedge).symm.trans (hFix (right edge)))
  · refine Or.inr fun edge hedge ↦ ?_
    exact sideVertex_injective target wall ((hmap edge hedge).symm.trans (hSwap (right edge)))

end Iso

/-- **The pairing index of a canonical W4 expansion is determined.** An
isomorphism of the two expanded targets matching the canonical occurrence
labels forces the two pairings to coincide. -/
theorem pairing_eq_of_expansionIso (star : FourStar target wall) (first second : Fin 3)
    (vertices : (graph target wall (star.right first)).V ≃
      (graph target wall (star.right second)).V)
    (edges : (graph target wall (star.right first)).edges ≃
      (graph target wall (star.right second)).edges)
    (hends : ∀ edge : (graph target wall (star.right first)).edges,
      UnorderedEnds vertices
        (edge : (graph target wall (star.right first)).V ×
          (graph target wall (star.right first)).V)
        (edges edge : (graph target wall (star.right second)).V ×
          (graph target wall (star.right second)).V))
    (hlabel : ∀ label : Option target.edges,
      edges (occurrenceEquiv target wall (star.right first) label) =
        occurrenceEquiv target wall (star.right second) label) :
    first = second := by
  have key : ∀ a b : Fin 3,
      ((∀ i : Fin 4, Pairing.labelRight b i = Pairing.labelRight a i) → a = b) ∧
        ((∀ i : Fin 4, Pairing.labelRight b i = !(Pairing.labelRight a i)) → a = b) := by
    decide
  rcases incidentRight_eq_or_not (right := star.right first) (right' := star.right second)
    vertices edges hends hlabel with hSame | hFlip
  · refine (key first second).1 fun i ↦ ?_
    have h := hSame (star.edge i) (star.edge_mem_incidentEdges i)
    rwa [FourStar.right_edge, FourStar.right_edge] at h
  · refine (key first second).2 fun i ↦ ?_
    have h := hFlip (star.edge i) (star.edge_mem_incidentEdges i)
    rwa [FourStar.right_edge, FourStar.right_edge] at h

end DraismaVargas.Count.W4PairingRigidity
