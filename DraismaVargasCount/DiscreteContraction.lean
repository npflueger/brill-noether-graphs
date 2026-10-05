module

public import DraismaVargasCount.GeometricContraction
public import DraismaVargas.Infrastructure.ContractionRamification
public import DraismaVargasCount.GeometricValidityTransport
public import DraismaVargas.LocalCases.FullDimensionalSource
public import DraismaVargas.LocalCases.W4TargetPairings

@[expose] public section

/-!
# Forced local partitions above a discrete contracted vertex

At a discrete valency-four wall in degree four, the merged vertex of the limit
carries four singleton sheet blocks. Any regrowth over such a limit has no choice
of local partition: both endpoint partitions and the contracted occurrence
partition are discrete. This is one direction of the classification of the
regrowths at such a wall (used by `DiscreteW4Normalization` and `W4StarParity`),
not a finite-star exhaustion theorem.
-/

namespace DraismaVargas.Count.DiscreteContraction
open DraismaVargas.Infrastructure
open GluingContraction ContractionRamification

variable {degree : ℕ}

theorem eq_discrete_of_refines (partition : SheetPartition degree)
    (h : partition.Refines (SheetPartition.discrete degree)) :
    partition = SheetPartition.discrete degree := by
  apply SheetPartition.ext_repr
  funext sheet
  exact (SheetPartition.discrete_rel_iff _ _).mp
    (h.rel (partition.rel_repr_left sheet))

theorem eq_discrete_of_relabel (partition : SheetPartition degree)
    (permutation : Equiv.Perm (Fin degree))
    (h : partition.relabel permutation = SheetPartition.discrete degree) :
    partition = SheetPartition.discrete degree := by
  have hh := congrArg (fun P : SheetPartition degree ↦ P.relabel permutation.symm) h
  simpa only [Transport.DatumIso.relabel_symm_relabel,SheetPartition.discrete_relabel] using hh

theorem join_eq_discrete_iff (first second : SheetPartition degree) :
    SheetPartition.join first second = SheetPartition.discrete degree ↔
      first = SheetPartition.discrete degree ∧ second = SheetPartition.discrete degree := by
  constructor
  · intro h
    constructor
    · apply eq_discrete_of_refines
      rw [← h]
      exact SheetPartition.left_refines_join first second
    · apply eq_discrete_of_refines
      rw [← h]
      exact SheetPartition.right_refines_join first second
  · rintro ⟨rfl,rfl⟩
    apply eq_discrete_of_refines
    exact (SheetPartition.join_refines_iff _ _ _).mpr
      ⟨SheetPartition.discrete_refines _,SheetPartition.discrete_refines _⟩

variable {target otherTarget : CFGraph} {a b : target.V} {contracted : target.edges}

/-- A full-dimensional target has valency at most three away from its
contracted vertex. Hence any four-valent vertex of its limit is the merge. -/
theorem eq_merge_of_four_valent {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (fd : DraismaVargas.LocalCases.FullDimensionalSource.FullDimensionalSourcePresentation
      data coordinate)
    (hc : (contracted : target.V × target.V) = (a,b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (v : (GraphContraction.contract target hab hOne).V)
    (hFour : (GluingDatum.incidentEdges v).card = 4) : v = ⟨a,hab⟩ := by
  apply Subtype.ext
  by_contra hne
  have hBound := GluingDatum.incidentEdges_card_le_three_of_changeMinimalAt data
    fd.valid v.val (fd.changeMinimal v.val)
  have hCard := card_incidentEdges_contract_of_ne hc hab hOne v.property hne
  change (GluingDatum.incidentEdges (target := target) v.val).card =
    (GluingDatum.incidentEdges (target := GraphContraction.contract target hab hOne) v).card at hCard
  omega

/-- An arbitrary geometric limit isomorphism must carry the merged vertex
to the four-valent vertex; this is derived from full-dimensionality. -/
theorem map_merge_of_four_valent {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (fd : DraismaVargas.LocalCases.FullDimensionalSource.FullDimensionalSourcePresentation
      data coordinate)
    (hc : (contracted : target.V × target.V) = (a,b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (other : GluingDatum otherTarget degree)
    (iso : GeometricDatumIso (contractDatum data hc hab hOne) other)
    (vertex : otherTarget.V) (hFour : (GluingDatum.incidentEdges vertex).card = 4) :
    iso.targetVertex ⟨a,hab⟩ = vertex := by
  have hCard := iso.incidentEdges_card_map (iso.targetVertex.symm vertex)
  rw [Equiv.apply_symm_apply,hFour] at hCard
  have hMerge := eq_merge_of_four_valent data fd hc hab hOne
    (iso.targetVertex.symm vertex) hCard.symm
  exact (congrArg iso.targetVertex hMerge).symm.trans (iso.targetVertex.apply_symm_apply vertex)

/-- Actual contraction to singleton sheet blocks forces all three local
partitions; no local splitting or sheet-order receipt is supplied. -/
theorem partitions_discrete (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a,b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hLimit : (contractDatum data hc hab hOne).vertexPartition ⟨a,hab⟩ =
      SheetPartition.discrete degree) :
    data.vertexPartition a = SheetPartition.discrete degree ∧
    data.vertexPartition b = SheetPartition.discrete degree ∧
    data.edgePartition contracted = SheetPartition.discrete degree := by
  rw [contractDatum_vertexPartition_merge] at hLimit
  obtain ⟨hLeft,hRight⟩ := (join_eq_discrete_iff _ _).mp hLimit
  refine ⟨hLeft,hRight,eq_discrete_of_refines _ ?_⟩
  rw [← hLeft]
  simpa only [hc] using data.refines_left contracted

/-- Geometric limit isomorphisms preserve the property needed by the local
classification, even when target occurrences reverse orientation. -/
theorem partitions_discrete_of_iso (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a,b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (other : GluingDatum otherTarget degree)
    (iso : GeometricDatumIso (contractDatum data hc hab hOne) other)
    (hDiscrete : other.vertexPartition (iso.targetVertex ⟨a,hab⟩) =
      SheetPartition.discrete degree) :
    data.vertexPartition a = SheetPartition.discrete degree ∧
    data.vertexPartition b = SheetPartition.discrete degree ∧
    data.edgePartition contracted = SheetPartition.discrete degree := by
  apply partitions_discrete data hc hab hOne
  apply eq_discrete_of_relabel _ (iso.vertexPerm ⟨a,hab⟩)
  exact (iso.vertexPartition ⟨a,hab⟩).symm.trans hDiscrete

/-- At a discrete endpoint, compatible sheet permutations are literally
equal. Thus a proposed lift cannot hide an independent local permutation. -/
theorem edgePerm_eq_vertexPerm (first : GluingDatum target degree)
    (second : GluingDatum otherTarget degree) (iso : GeometricDatumIso first second)
    (edge : target.edges) (vertex : target.V)
    (hIncident : (edge : target.V × target.V).1 = vertex ∨
      (edge : target.V × target.V).2 = vertex)
    (hDiscrete : first.vertexPartition vertex = SheetPartition.discrete degree) :
    iso.edgePerm edge = iso.vertexPerm vertex := by
  apply Equiv.ext
  intro sheet
  have h := iso.compatible edge vertex hIncident sheet
  rw [hDiscrete,SheetPartition.discrete_rel_iff] at h
  simpa only [Equiv.apply_symm_apply] using congrArg (iso.vertexPerm vertex) h

/-- The local partition census for every actual full-dimensional regrowth
of a four-valent discrete limit. No hypothesis pins the merged vertex or
chooses a compatible sheet permutation; both are forced. -/
theorem partitions_discrete_of_four_valent_iso {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (fd : DraismaVargas.LocalCases.FullDimensionalSource.FullDimensionalSourcePresentation
      data coordinate)
    (hc : (contracted : target.V × target.V) = (a,b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (other : GluingDatum otherTarget degree)
    (iso : GeometricDatumIso (contractDatum data hc hab hOne) other)
    (vertex : otherTarget.V) (hFour : (GluingDatum.incidentEdges vertex).card = 4)
    (hDiscrete : other.vertexPartition vertex = SheetPartition.discrete degree) :
    data.vertexPartition a = SheetPartition.discrete degree ∧
    data.vertexPartition b = SheetPartition.discrete degree ∧
    data.edgePartition contracted = SheetPartition.discrete degree := by
  apply partitions_discrete_of_iso data hc hab hOne other iso
  rw [map_merge_of_four_valent data fd hc hab hOne other iso vertex hFour]
  exact hDiscrete

/-- Pull the four named retained occurrences back along the actual target
occurrence bijection. The labels are not freshly chosen by cardinality. -/
noncomputable def pullbackFourStar (first : GluingDatum target degree)
    (second : GluingDatum otherTarget degree) (iso : GeometricDatumIso first second)
    (vertex : target.V) (otherVertex : otherTarget.V)
    (hVertex : iso.targetVertex vertex = otherVertex)
    (star : DraismaVargas.LocalCases.W4TargetPairings.FourStar otherTarget otherVertex) :
    DraismaVargas.LocalCases.W4TargetPairings.FourStar target vertex where
  label := star.label.trans (Equiv.subtypeEquiv iso.targetEdge (fun edge ↦ by
    rw [← hVertex]
    exact (iso.mem_incidentEdges_map vertex edge).symm)).symm

theorem pullbackFourStar_edge (first : GluingDatum target degree)
    (second : GluingDatum otherTarget degree) (iso : GeometricDatumIso first second)
    (vertex : target.V) (otherVertex : otherTarget.V)
    (hVertex : iso.targetVertex vertex = otherVertex)
    (star : DraismaVargas.LocalCases.W4TargetPairings.FourStar otherTarget otherVertex)
    (label : Fin 4) :
    iso.targetEdge ((pullbackFourStar first second iso vertex otherVertex hVertex star).edge label) =
      star.edge label := by
  exact iso.targetEdge.apply_symm_apply (star.edge label)

end DraismaVargas.Count.DiscreteContraction
