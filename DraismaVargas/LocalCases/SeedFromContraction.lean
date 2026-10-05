module

public import DraismaVargas.LocalCases.SeedCandidate
public import DraismaVargas.LocalCases.IncomingTargetExpansion
public import DraismaVargas.LocalCases.RelabelFullDimensional

@[expose] public section

/-!
# A neutral seed from an actual cover and a contractible target edge

The target contraction/re-expansion isomorphism already exists. Here the
endpoint and edge partitions are restored too, yielding an actual candidate
for the original cover, up to that explicit target transport. No wall figure
or supplied expansion receipt is needed.
-/

namespace DraismaVargas.LocalCases.SeedFromContraction

open Utilities
open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open TargetExpansion ResolutionM11 SeedCandidate

variable {target : CFGraph.{0}} {degree : ℕ} {a b : target.V}
  {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b))
  (hab : a ≠ b) (hOne : num_edges target a b = 1)

/-- Reuse the three literal incoming partitions. -/
def resolution : LocalResolution degree where
  left := data.vertexPartition a
  right := data.vertexPartition b
  newEdge := data.edgePartition contracted
  edge_refines_left := by
    have h := data.refines_left contracted
    simpa only [hc] using h
  edge_refines_right := by
    have h := data.refines_right contracted
    simpa only [hc] using h

theorem resolution_contracts :
    (resolution data hc).ContractsTo
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) := by
  change SheetPartition.IsJoin (data.vertexPartition a) (data.vertexPartition b) _
  rw [contractDatum_vertexPartition_merge]
  exact SheetPartition.isJoin_join _ _

/-- Refinement at any incident endpoint, without choosing an orientation. -/
theorem refines_of_incident (edge : target.edges) (vertex : target.V)
    (hIncident : edge ∈ GluingDatum.incidentEdges vertex) :
    (data.edgePartition edge).Refines (data.vertexPartition vertex) := by
  rcases (mem_incidentEdges_iff vertex edge).mp hIncident with h | h
  · simpa only [h] using data.refines_left edge
  · simpa only [h] using data.refines_right edge

/-- Each retained wall occurrence returns to the endpoint it originally met. -/
theorem exterior : ExteriorRefines (contractDatum data hc hab hOne) ⟨a, hab⟩
    (IncomingTargetExpansion.right hc hab hOne) (resolution data hc) := by
  intro edge hIncident
  have hUnion := unfoldEdge_mem_incidentEdges_union hc hab hOne
    ((mem_incidentEdges_iff _ _).mpr hIncident)
  rw [contractDatum_edgePartition]
  change (data.edgePartition (unfoldEdge hc hab hOne edge)).Refines
    (if IncomingTargetExpansion.right hc hab hOne edge then
      data.vertexPartition b else data.vertexPartition a)
  by_cases hB : unfoldEdge hc hab hOne edge ∈ GluingDatum.incidentEdges b
  · have hRight : IncomingTargetExpansion.right hc hab hOne edge = true := by
      simpa only [IncomingTargetExpansion.right, decide_eq_true_eq] using
        (mem_incidentEdges_iff _ _).mp hB
    rw [hRight, ite_eq_left rfl]
    exact refines_of_incident data _ _ hB
  · have hRight : IncomingTargetExpansion.right hc hab hOne edge = false := by
      simp only [IncomingTargetExpansion.right, decide_eq_false_iff_not]
      exact fun h ↦ hB ((mem_incidentEdges_iff _ _).mpr h)
    rw [hRight]
    exact refines_of_incident data _ _ ((Finset.mem_union.mp hUnion).resolve_right hB)

/-- The actual target isomorphism, directed from the input to its re-expansion. -/
noncomputable def iso := (IncomingTargetExpansion.graphIso hc hab hOne).symm

theorem inverse_edgeEquiv (hConnected : graph_connected target) (hGenus : genus target = 0)
    (edge : (graph (contract target hab hOne) ⟨a, hab⟩
      (IncomingTargetExpansion.right hc hab hOne)).edges) :
    (GluingTransport.edgeEquiv (iso hc hab hOne)).symm edge =
      IncomingTargetExpansion.edgeEquiv hc hab hOne edge := by
  classical
  let first := IncomingTargetExpansion.vertexEquiv hab hOne edge.1.1
  let second := IncomingTargetExpansion.vertexEquiv hab hOne edge.1.2
  have hCard : Fintype.card {e : target.edges //
      GluingTransport.edgeKey target e = s(first, second)} ≤ 1 := by
    rw [GluingTransport.card_edgeKey_fiber]
    exact IteratedContraction.num_edges_le_one_of_genus_zero_of_connected
      target hConnected hGenus first second
  have hUnique := Fintype.card_le_one_iff_subsingleton.mp hCard
  have hCanonical : GluingTransport.edgeKey target
      ((GluingTransport.edgeEquiv (iso hc hab hOne)).symm edge) = s(first, second) := by
    have h := GluingTransport.edgeEquiv_symm_ends (iso hc hab hOne) edge
    rcases h with h | h
    · have h' := congrArg (fun pair ↦
        (IncomingTargetExpansion.vertexEquiv hab hOne pair.1,
          IncomingTargetExpansion.vertexEquiv hab hOne pair.2)) h
      exact Sym2.eq_iff.mpr (Or.inl
        ⟨(Equiv.apply_symm_apply (IncomingTargetExpansion.vertexEquiv hab hOne) _).symm.trans
            (congrArg Prod.fst h').symm,
          (Equiv.apply_symm_apply (IncomingTargetExpansion.vertexEquiv hab hOne) _).symm.trans
            (congrArg Prod.snd h').symm⟩)
    · have h' := congrArg (fun pair ↦
        (IncomingTargetExpansion.vertexEquiv hab hOne pair.1,
          IncomingTargetExpansion.vertexEquiv hab hOne pair.2)) h
      exact Sym2.eq_iff.mpr (Or.inr
        ⟨(Equiv.apply_symm_apply (IncomingTargetExpansion.vertexEquiv hab hOne) _).symm.trans
            (congrArg Prod.snd h').symm,
          (Equiv.apply_symm_apply (IncomingTargetExpansion.vertexEquiv hab hOne) _).symm.trans
            (congrArg Prod.fst h').symm⟩)
  have hLiteral : GluingTransport.edgeKey target
      (IncomingTargetExpansion.edgeEquiv hc hab hOne edge) = s(first, second) := by
    unfold GluingTransport.edgeKey
    rw [IncomingTargetExpansion.edgeEquiv_ends]
  exact congrArg Subtype.val (hUnique.elim ⟨_, hCanonical⟩ ⟨_, hLiteral⟩)

/-- Contracting and re-expanding restores every vertex and occurrence partition,
not only the underlying target graph. -/
theorem transported_eq (hConnected : graph_connected target) (hGenus : genus target = 0) :
    GluingTransport.transport (iso hc hab hOne) data =
      GlobalResolution.datum (contractDatum data hc hab hOne) ⟨a, hab⟩
        (IncomingTargetExpansion.right hc hab hOne) (resolution data hc)
        (exterior data hc hab hOne).oldCompatible := by
  apply gluingDatum_ext
  · funext vertex
    cases vertex with
    | inl vertex =>
      by_cases hVertex : vertex = (⟨a, hab⟩ : (contract target hab hOne).V)
      · subst vertex
        exact (GlobalResolution.datum_vertexPartition_old_wall
          (contractDatum data hc hab hOne) ⟨a, hab⟩
          (IncomingTargetExpansion.right hc hab hOne) (resolution data hc)
          (exterior data hc hab hOne).oldCompatible).symm
      ·
        have hValue : vertex.1 ≠ a := fun h ↦ hVertex (Subtype.ext h)
        exact ((GlobalResolution.datum_vertexPartition_old_of_ne _ _ _ _ _ _ hVertex).trans
          (contractVertexPartition_of_ne data a b hValue)).symm
    | inr vertex =>
      cases vertex
      exact (GlobalResolution.datum_vertexPartition_fresh
        (contractDatum data hc hab hOne) ⟨a, hab⟩
        (IncomingTargetExpansion.right hc hab hOne) (resolution data hc)
        (exterior data hc hab hOne).oldCompatible).symm
  · funext edge
    obtain ⟨column, rfl⟩ := (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
      (IncomingTargetExpansion.right hc hab hOne)).surjective edge
    rw [GluingTransport.transport_edgePartition, inverse_edgeEquiv hc hab hOne hConnected hGenus]
    simp only [IncomingTargetExpansion.edgeEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
    cases column with
    | none =>
      rw [M11IncomingCoordinates.incomingColumnEquiv_none]
      exact (GlobalResolution.datum_edgePartition_new
        (contractDatum data hc hab hOne) ⟨a, hab⟩
        (IncomingTargetExpansion.right hc hab hOne) (resolution data hc)
        (exterior data hc hab hOne).oldCompatible).symm
    | some edge =>
      rw [M11IncomingCoordinates.incomingColumnEquiv_some]
      exact (GlobalResolution.datum_edgePartition_old
        (contractDatum data hc hab hOne) ⟨a, hab⟩
        (IncomingTargetExpansion.right hc hab hOne) (resolution data hc)
        (exterior data hc hab hOne).oldCompatible edge).symm

/-- An actual inhabitant of the earlier neutral constructor's reconstruction
receipt. Only tree geometry is used to identify its occurrence maps. -/
noncomputable def expansionReceipt (hConnected : graph_connected target)
    (hGenus : genus target = 0) :
    ExpansionReceipt data (contractDatum data hc hab hOne) ⟨a, hab⟩
      (IncomingTargetExpansion.right hc hab hOne) (resolution data hc)
      (exterior data hc hab hOne) where
  iso := iso hc hab hOne
  transported := transported_eq data hc hab hOne hConnected hGenus

/-- An actual valid cover supplies the two endpoint inequalities of its neutral
candidate by transport. -/
noncomputable def presentation (hConnected : graph_connected target)
    (hGenus : genus target = 0) (hRH : data.RiemannHurwitz) :
    Presentation (contractDatum data hc hab hOne) ⟨a, hab⟩ :=
  Presentation.ofExpansionReceipt (resolution_contracts data hc hab hOne)
    (expansionReceipt data hc hab hOne hConnected hGenus) hRH

/-- The seed is the original cover presented as a neutral resolution. The only
contraction restriction is the actual source-fibre forest used by validity. -/
noncomputable def seed (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hValid : data.Valid) (hForest : ContractionForest data a b contracted) : Seed degree where
  target := contract target hab hOne
  data := contractDatum data hc hab hOne
  wall := ⟨a, hab⟩
  presentation := presentation data hc hab hOne hConnected hGenus hValid.2
  valid := valid_contractDatum data hc hab hOne hForest hValid
  targetConnected := graph_connected_contract target hab hOne hConnected
  targetGenus := (genus_contract target hab hOne).trans hGenus

theorem seed_datum (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hValid : data.Valid) (hForest : ContractionForest data a b contracted) :
    (seed data hc hab hOne hConnected hGenus hValid hForest).candidate.datum =
      GluingTransport.transport (iso hc hab hOne) data :=
  (transported_eq data hc hab hOne hConnected hGenus).symm

open FullDimensionalSource

/-- A full-dimensional presentation of the input cover gives one for this
actual seed, using the occurrence-induced target relabelling. -/
noncomputable def seedFullDim {coordinate : Type}
    [Fintype coordinate] [DecidableEq coordinate]
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted) :
    FullDimensionalSourcePresentation
      (seed data hc hab hOne fullDim.targetConnected fullDim.targetGenus
        fullDim.valid hForest).candidate.datum coordinate :=
  (seed_datum data hc hab hOne fullDim.targetConnected fullDim.targetGenus
    fullDim.valid hForest).symm ▸
      RelabelFullDimensional.targetPresentation (iso hc hab hOne) fullDim

private theorem castFullDim_matrix {other : GluingDatum target degree}
    {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
    (equality : data = other)
    (fullDim : FullDimensionalSourcePresentation data coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
      (equality ▸ fullDim).labelling.presentation =
    GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation := by
  subst other
  rfl

/-- The seed preserves the input's complete length matrix in induced
coordinates; in particular it does not append a zero pendant column. -/
theorem seedFullDim_matrix {coordinate : Type}
    [Fintype coordinate] [DecidableEq coordinate]
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted) :
    GluingDatum.LengthMatrixPresentation.matrix
      (seedFullDim data hc hab hOne fullDim hForest).labelling.presentation =
    GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation := by
  exact (castFullDim_matrix _
    (seed_datum data hc hab hOne fullDim.targetConnected fullDim.targetGenus
      fullDim.valid hForest).symm
    (RelabelFullDimensional.targetPresentation (iso hc hab hOne) fullDim)).trans
      (RelabelFullDimensional.target_matrix_eq (iso hc hab hOne) data
        fullDim.valid.1 fullDim.labelling)

include hc hab hOne in
/-- A full-dimensional actual cover on a tree and one contractible fibre
supply the semantic initial payload in the cover's original matrix. -/
theorem carriesClearedPencil {coordinate : Type}
    [Fintype coordinate] [DecidableEq coordinate]
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (coordinates : coordinate → ℚ) (hPositive : ∀ i, 0 < coordinates i) :
    SemanticAtlasMarch.CarriesClearedPencil degree
      (GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation)
      coordinates := by
  have h := (seed data hc hab hOne fullDim.targetConnected fullDim.targetGenus
    fullDim.valid hForest).carriesClearedPencil
      (seedFullDim data hc hab hOne fullDim hForest) coordinates hPositive
  rwa [seedFullDim_matrix] at h

end DraismaVargas.LocalCases.SeedFromContraction
