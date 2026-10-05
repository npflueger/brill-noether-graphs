module

public import DraismaVargas.LocalCases.W4Bridge
public import DraismaVargas.LocalCases.M11IncomingTargetNormalization

@[expose] public section

/-!
# Actual incoming W4 target normalization

Source: Draisma--Vargas Part I, Case `{aux-r0}` and the target-pairing
discussion of Case `{w4}`; Equation (1). The incoming 3+3 target endpoints
give a literal 2+2 partition of the four retained wall occurrences. Existing
finite pairing exhaustion and support/swap graph maps normalize it while
preserving every Option occurrence. No source-cover or stable-row matching
is asserted here.
-/

namespace DraismaVargas.LocalCases.W4IncomingTargetNormalization

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification TargetExpansion
open W4TargetPairings IncomingW2TargetPlacement M11IncomingCoordinates
open FullDimensionalSource W4StableSource

variable {target : CFGraph} {a b : target.V} {contracted : target.edges}

/-- The selected labels unfold to exactly the original right endpoint's
retained occurrences, not an arbitrary set of the same size. -/
theorem selectedLabels_unfold_image
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : FourStar (contract target hab hOne) ⟨a, hab⟩) :
    (star.selectedLabels (IncomingTargetExpansion.right hc hab hOne)).image
      (fun label ↦ unfoldEdge hc hab hOne (star.edge label)) =
      (GluingDatum.incidentEdges b).erase contracted := by
  classical
  ext edge
  constructor
  · rintro hEdge
    obtain ⟨label, hLabel, rfl⟩ := Finset.mem_image.mp hEdge
    refine Finset.mem_erase.mpr ⟨unfoldEdge_ne_contracted hc hab hOne _, ?_⟩
    exact (right_eq_true_iff hc hab hOne _).mp (Finset.mem_filter.mp hLabel).2
  · intro hEdge
    obtain ⟨hNe, hAt⟩ := Finset.mem_erase.mp hEdge
    have hFold := foldEdge_mem_incidentEdges_merge hc hab hOne hNe
      (Finset.mem_union_right _ hAt)
    obtain ⟨label, hLabel⟩ := star.exists_edge_eq _ hFold
    have hUnfold : unfoldEdge hc hab hOne (star.edge label) = edge := by
      rw [hLabel, unfoldEdge_foldEdge]
    apply Finset.mem_image.mpr
    refine ⟨label, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hUnfold⟩
    apply (right_eq_true_iff hc hab hOne _).mpr
    rwa [hUnfold]

/-- The actual selected-label count is the right endpoint valency minus its
one contracted occurrence. This retains exact unfolded occurrence names. -/
theorem selectedLabels_card_eq
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : FourStar (contract target hab hOne) ⟨a, hab⟩) :
    (star.selectedLabels (IncomingTargetExpansion.right hc hab hOne)).card =
      (GluingDatum.incidentEdges b).card - 1 := by
  classical
  have hImage := congrArg Finset.card (selectedLabels_unfold_image hc hab hOne star)
  rw [Finset.card_image_of_injective _ (by
    intro first second h
    exact star.edge_injective ((foldEdgeEquiv hc hab hOne).symm.injective (Subtype.ext h))),
    Finset.card_erase_of_mem (contracted_mem_incidentEdges_right hc)] at hImage
  exact hImage

/-- Convert the existing three-pairing finite census to the precise incident
support predicate used by the already proved target normalization maps. -/
theorem exists_support_pairing {wallTarget : CFGraph} {wall : wallTarget.V}
    (star : FourStar wallTarget wall) (assignment : wallTarget.edges → Bool)
    (hCard : (star.selectedLabels assignment).card = 2) :
    ∃ pairing : Fin 3,
      (∀ edge ∈ GluingDatum.incidentEdges wall, assignment edge = star.right pairing edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges wall, assignment edge = !(star.right pairing edge)) := by
  obtain ⟨pairing, hPairing | hPairing⟩ := star.exhausts_assignment_up_to_swap assignment hCard
  · refine ⟨pairing, Or.inl ?_⟩
    intro edge hEdge
    obtain ⟨label, rfl⟩ := star.exists_edge_eq edge hEdge
    rw [star.right_edge]
    apply Bool.eq_iff_iff.mpr
    have hMem := congrArg (fun labels : Finset (Fin 4) ↦ label ∈ labels) hPairing
    simpa only [FourStar.selectedLabels, Finset.mem_filter, Finset.mem_univ, true_and,
      Pairing.labelRight, decide_eq_true_eq] using iff_of_eq hMem
  · refine ⟨pairing, Or.inr ?_⟩
    intro edge hEdge
    obtain ⟨label, rfl⟩ := star.exists_edge_eq edge hEdge
    rw [star.right_edge]
    apply Bool.eq_iff_iff.mpr
    have hMem := congrArg (fun labels : Finset (Fin 4) ↦ label ∈ labels) hPairing
    have hNot : ¬(assignment (star.edge label) = true) ↔ label ∈ Pairing.side pairing := by
      simpa only [FourStar.selectedLabels, Finset.mem_compl, Finset.mem_filter,
        Finset.mem_univ, true_and] using iff_of_eq hMem
    simpa [Pairing.labelRight] using not_congr hNot

section Incoming

variable {degree : ℕ} {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : FourStar (contract target hab hOne) ⟨a, hab⟩)

include fd hc hab hOne star

/-- Incoming full-dimensionality forces the actual four directions into a
2+2 placement; the endpoint trivalence is derived, not a new input. -/
theorem selectedLabels_card :
    (star.selectedLabels (IncomingTargetExpansion.right hc hab hOne)).card = 2 := by
  obtain ⟨_, hB, _, _⟩ := W4Bridge.endpoints_trivalent_of_fourStar data hc hab hOne
    fd.valid fd.changeMinimal star
  rw [selectedLabels_card_eq hc hab hOne star, hB]

/-- One of the three named target pairings agrees with the actual incoming
placement, possibly after exchanging the expanded endpoints. -/
theorem exists_pairing :
    ∃ pairing : Fin 3,
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = star.right pairing edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = !(star.right pairing edge)) :=
  exists_support_pairing star _ (selectedLabels_card data fd hc hab hOne star)

/-- Choose among the three explicit Fin4 pairings; no graph-cardinality
bijection or source-cover matching receipt is used. -/
noncomputable def pairing : Fin 3 :=
  Classical.choose (exists_pairing data fd hc hab hOne star)

theorem pairing_placement :
    (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge =
        star.right (pairing data fd hc hab hOne star) edge) ∨
    (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge =
        !(star.right (pairing data fd hc hab hOne star) edge)) :=
  Classical.choose_spec (exists_pairing data fd hc hab hOne star)

/-- The actual incoming target is one of the canonical W4 expansion targets. -/
noncomputable def targetIso : Utilities.CFGraphIso target
    (graph (contract target hab hOne) ⟨a, hab⟩ (star.right (pairing data fd hc hab hOne star))) :=
  M11IncomingTargetNormalization.incomingIso hc hab hOne _
    (pairing_placement data fd hc hab hOne star)

/-- Canonical target transport respects every literal Option occurrence,
including the contracted occurrence at `none`. -/
theorem targetIso_occurrence (column : Option (contract target hab hOne).edges) :
    GluingTransport.edgeEquiv (targetIso data fd hc hab hOne star)
      (incomingColumnEquiv hc hab hOne column) =
      occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
        (star.right (pairing data fd hc hab hOne star)) column :=
  M11IncomingTargetNormalization.incomingIso_occurrence hc hab hOne _
    (pairing_placement data fd hc hab hOne star) fd.targetConnected fd.targetGenus column

/-- The selected isomorphism lands in the actual existing presented-family
candidate target. The family is constructed from the contracted W4 input;
no equality with the incoming source cover is supplied or concluded. -/
noncomputable def presentedFamilyTargetIso
    (input : AuxR0SourceInput (contractDatum data hc hab hOne) star) :
    Utilities.CFGraphIso target
      (graph (contract target hab hOne) ⟨a, hab⟩
        (((input.presentedFamily (contractDatum data hc hab hOne) star).candidate
          (pairing data fd hc hab hOne star)).right)) :=
  targetIso data fd hc hab hOne star

/-- The Option dictionary is exactly the target-edge labelling already used
by the actual W4 presented family, not a second arbitrary coordinate choice. -/
theorem presentedFamilyTargetIso_column
    (input : AuxR0SourceInput (contractDatum data hc hab hOne) star)
    (column : Option (contract target hab hOne).edges) :
    GluingTransport.edgeEquiv (presentedFamilyTargetIso data fd hc hab hOne star input)
      (incomingColumnEquiv hc hab hOne column) =
      ((input.presentedFamily (contractDatum data hc hab hOne) star).presentation
        (pairing data fd hc hab hOne star)).targetEdge column :=
  targetIso_occurrence data fd hc hab hOne star column

end Incoming

end DraismaVargas.LocalCases.W4IncomingTargetNormalization
