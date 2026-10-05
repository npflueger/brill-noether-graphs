module

public import DraismaVargas.LocalCases.IncomingW2TargetPlacement
public import DraismaVargas.LocalCases.W3Nd2FineCandidates
public import DraismaVargas.LocalCases.FullDimensionalSource

@[expose] public section

/-!
# Incoming target placement for the W3 nd2 wall

The three retained occurrences at a contracted trivalent wall split `1+2`
between the original endpoints.  This file records the literal split using
`IncomingTargetExpansion.right`, before any source-cover matching is chosen.
-/

namespace DraismaVargas.LocalCases.W3Nd2IncomingTargetPlacement

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open W4Assembly W4StableSource ThirdEquation W3R1SourceProfile
open IncomingTargetExpansion IncomingW2TargetPlacement FullDimensionalSource
open W3Nd2SourceCandidates W3Nd2FineRefinement

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
  {contracted : target.edges}

abbrev starEdge
    {wallTarget : CFGraph} {wall : wallTarget.V}
    (star : ThreeStar wallTarget wall) (label : Fin 3) : wallTarget.edges :=
  (star.label label).1

theorem starEdge_mem
    {wallTarget : CFGraph} {wall : wallTarget.V}
    (star : ThreeStar wallTarget wall) (label : Fin 3) :
    starEdge star label ∈ GluingDatum.incidentEdges wall :=
  (star.label label).2

theorem starEdge_injective
    {wallTarget : CFGraph} {wall : wallTarget.V}
    (star : ThreeStar wallTarget wall) : Function.Injective (starEdge star) := by
  intro first second h
  exact star.label.injective (Subtype.ext h)

/-- Labels whose literal unfolded occurrence is incident to the original
right endpoint. -/
noncomputable def rightLabels
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩) : Finset (Fin 3) :=
  Finset.univ.filter fun label ↦
    IncomingTargetExpansion.right hc hab hOne (starEdge star label) = true

/-- The selected labels unfold to exactly the retained occurrences at `b`. -/
theorem rightLabels_unfold_image
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩) :
    (rightLabels hc hab hOne star).image
        (fun label ↦ unfoldEdge hc hab hOne (starEdge star label)) =
      (GluingDatum.incidentEdges b).erase contracted := by
  classical
  ext edge
  constructor
  · intro hEdge
    obtain ⟨label, hLabel, rfl⟩ := Finset.mem_image.mp hEdge
    refine Finset.mem_erase.mpr ⟨unfoldEdge_ne_contracted hc hab hOne _, ?_⟩
    exact (right_eq_true_iff hc hab hOne _).mp (Finset.mem_filter.mp hLabel).2
  · intro hEdge
    obtain ⟨hNe, hAt⟩ := Finset.mem_erase.mp hEdge
    have hFold := foldEdge_mem_incidentEdges_merge hc hab hOne hNe
      (Finset.mem_union_right _ hAt)
    obtain ⟨label, hLabel⟩ := star.label.surjective
      ⟨foldEdge hc hab hOne ⟨edge, hNe⟩, hFold⟩
    have hFoldEq : starEdge star label = foldEdge hc hab hOne ⟨edge, hNe⟩ :=
      congrArg Subtype.val hLabel
    have hUnfold : unfoldEdge hc hab hOne (starEdge star label) = edge := by
      rw [hFoldEq, unfoldEdge_foldEdge]
    apply Finset.mem_image.mpr
    refine ⟨label, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hUnfold⟩
    apply (right_eq_true_iff hc hab hOne _).mpr
    rwa [hUnfold]

/-- The literal right-label count is the old right valency with the contracted
occurrence removed. -/
theorem rightLabels_card_eq
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩) :
    (rightLabels hc hab hOne star).card =
      (GluingDatum.incidentEdges b).card - 1 := by
  classical
  have hImage := congrArg Finset.card (rightLabels_unfold_image hc hab hOne star)
  rw [Finset.card_image_of_injective _ (by
    intro first second h
    exact starEdge_injective star
      ((foldEdgeEquiv hc hab hOne).symm.injective (Subtype.ext h))),
    Finset.card_erase_of_mem (contracted_mem_incidentEdges_right hc)] at hImage
  exact hImage

/-- Full-dimensional incoming data force the endpoints of a W3 contraction
to have valencies `2,3`, in one of the two literal orders. -/
theorem endpoint_valencies
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩) :
    ((GluingDatum.incidentEdges a).card = 2 ∧
        (GluingDatum.incidentEdges b).card = 3 ∧
        data.targetChange a = 1 ∧ data.targetChange b = 0) ∨
      ((GluingDatum.incidentEdges a).card = 3 ∧
        (GluingDatum.incidentEdges b).card = 2 ∧
        data.targetChange a = 0 ∧ data.targetChange b = 1) := by
  obtain ⟨hSum, hLeft, hRight, hChange⟩ :=
    endpoints_of_threeStar data hc hab hOne fullDim.valid fullDim.changeMinimal star
  have hMinLeft := fullDim.changeMinimal a
  have hMinRight := fullDim.changeMinimal b
  unfold GluingDatum.ChangeMinimalAt GluingDatum.targetExcess at hMinLeft hMinRight
  omega

/-- Consequently the actual side predicate has either one right label or two,
with the singleton side exactly the divalent endpoint. -/
theorem side_census
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩) :
    ((GluingDatum.incidentEdges a).card = 2 ∧
        (GluingDatum.incidentEdges b).card = 3 ∧
        (rightLabels hc hab hOne star).card = 2 ∧
        ((Finset.univ : Finset (Fin 3)) \ rightLabels hc hab hOne star).card = 1) ∨
      ((GluingDatum.incidentEdges a).card = 3 ∧
        (GluingDatum.incidentEdges b).card = 2 ∧
        (rightLabels hc hab hOne star).card = 1 ∧
        ((Finset.univ : Finset (Fin 3)) \ rightLabels hc hab hOne star).card = 2) := by
  classical
  rcases endpoint_valencies data hc hab hOne fullDim star with hLeft | hRight
  · left
    refine ⟨hLeft.1, hLeft.2.1, ?_, ?_⟩
    · rw [rightLabels_card_eq hc hab hOne star, hLeft.2.1]
    · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
        Finset.card_univ, Fintype.card_fin,
        rightLabels_card_eq hc hab hOne star, hLeft.2.1]
  · right
    refine ⟨hRight.1, hRight.2.1, ?_, ?_⟩
    · rw [rightLabels_card_eq hc hab hOne star, hRight.2.1]
    · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
        Finset.card_univ, Fintype.card_fin,
        rightLabels_card_eq hc hab hOne star, hRight.2.1]

/-- There is a unique retained wall occurrence at the divalent old endpoint.
The statement uses the actual source-edge side predicate, rather than a chosen
labelling of the displayed figure. -/
theorem exists_unique_divalent_occurrence
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩) :
    ∃! edge : (contract target hab hOne).edges,
      edge ∈ GluingDatum.incidentEdges
        (target := contract target hab hOne) ⟨a, hab⟩ ∧
        (((GluingDatum.incidentEdges a).card = 2 ∧
            IncomingTargetExpansion.right hc hab hOne edge = false) ∨
          ((GluingDatum.incidentEdges b).card = 2 ∧
            IncomingTargetExpansion.right hc hab hOne edge = true)) := by
  classical
  rcases side_census data hc hab hOne fullDim star with hLeft | hRight
  · obtain ⟨label, hSingleton⟩ := Finset.card_eq_one.mp hLeft.2.2.2
    refine ⟨starEdge star label,
      ⟨starEdge_mem star label, Or.inl ⟨hLeft.1, ?_⟩⟩, ?_⟩
    · have hMem : label ∉ rightLabels hc hab hOne star := by
        exact (Finset.mem_sdiff.mp
          (hSingleton.symm ▸ Finset.mem_singleton_self label)).2
      have hNotTrue : IncomingTargetExpansion.right hc hab hOne
          (starEdge star label) ≠ true := by
        simpa only [rightLabels, Finset.mem_filter, Finset.mem_univ,
          true_and] using hMem
      exact Bool.eq_false_iff.mpr hNotTrue
    · intro edge hEdge
      obtain ⟨other, hOther⟩ := star.label.surjective ⟨edge, hEdge.1⟩
      have hEdgeEq : starEdge star other = edge := congrArg Subtype.val hOther
      rw [← hEdgeEq]
      have hOtherNot : other ∉ rightLabels hc hab hOne star := by
        rcases hEdge.2 with hAtLeft | hAtRight
        · intro hMem
          have hTrue := (Finset.mem_filter.mp hMem).2
          rw [hEdgeEq, hAtLeft.2] at hTrue
          contradiction
        · omega
      have : other = label := by
        rw [← Finset.mem_singleton]
        rw [← hSingleton]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hOtherNot⟩
      rw [this]
  · obtain ⟨label, hSingleton⟩ := Finset.card_eq_one.mp hRight.2.2.1
    refine ⟨starEdge star label,
      ⟨starEdge_mem star label, Or.inr ⟨hRight.2.1, ?_⟩⟩, ?_⟩
    · have hMem : label ∈ rightLabels hc hab hOne star := by
        rw [hSingleton]
        exact Finset.mem_singleton_self label
      exact (Finset.mem_filter.mp hMem).2
    · intro edge hEdge
      obtain ⟨other, hOther⟩ := star.label.surjective ⟨edge, hEdge.1⟩
      have hEdgeEq : starEdge star other = edge := congrArg Subtype.val hOther
      rw [← hEdgeEq]
      have hOtherMem : other ∈ rightLabels hc hab hOne star := by
        rcases hEdge.2 with hAtLeft | hAtRight
        · omega
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          simpa only [hEdgeEq] using hAtRight.2
      have : other = label := by
        rw [← Finset.mem_singleton]
        rwa [← hSingleton]
      rw [this]

/-- The literal retained occurrence on the old divalent endpoint. -/
noncomputable def divalentOccurrence
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩) :
    (contract target hab hOne).edges :=
  Classical.choose (exists_unique_divalent_occurrence
    data hc hab hOne fullDim star)

theorem divalentOccurrence_spec
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩) :
    divalentOccurrence data hc hab hOne fullDim star ∈
        GluingDatum.incidentEdges
          (target := contract target hab hOne) ⟨a, hab⟩ ∧
      (((GluingDatum.incidentEdges a).card = 2 ∧
          IncomingTargetExpansion.right hc hab hOne
            (divalentOccurrence data hc hab hOne fullDim star) = false) ∨
        ((GluingDatum.incidentEdges b).card = 2 ∧
          IncomingTargetExpansion.right hc hab hOne
            (divalentOccurrence data hc hab hOne fullDim star) = true)) :=
  (Classical.choose_spec (exists_unique_divalent_occurrence
    data hc hab hOne fullDim star)).1

theorem divalentOccurrence_unique
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (edge : (contract target hab hOne).edges)
    (hEdge : edge ∈ GluingDatum.incidentEdges
        (target := contract target hab hOne) ⟨a, hab⟩ ∧
      (((GluingDatum.incidentEdges a).card = 2 ∧
          IncomingTargetExpansion.right hc hab hOne edge = false) ∨
        ((GluingDatum.incidentEdges b).card = 2 ∧
          IncomingTargetExpansion.right hc hab hOne edge = true))) :
    edge = divalentOccurrence data hc hab hOne fullDim star :=
  (Classical.choose_spec (exists_unique_divalent_occurrence
    data hc hab hOne fullDim star)).2 edge hEdge

/-- On wall occurrences the actual side predicate is exactly the canonical
singleton-left predicate, up to swapping the two expanded endpoints. -/
theorem divalentOccurrence_placement
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩) :
    (∀ edge ∈ GluingDatum.incidentEdges
        (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge =
        rightOf (divalentOccurrence data hc hab hOne fullDim star) edge) ∨
    (∀ edge ∈ GluingDatum.incidentEdges
        (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge =
        !(rightOf (divalentOccurrence data hc hab hOne fullDim star) edge)) := by
  classical
  have hIsolated := divalentOccurrence_spec data hc hab hOne fullDim star
  rcases hIsolated.2 with hLeft | hRight
  · left
    intro edge hAt
    apply Bool.eq_iff_iff.mpr
    simp only [rightOf, decide_eq_true_eq]
    constructor
    · intro hTrue hEq
      subst edge
      rw [hLeft.2] at hTrue
      contradiction
    · intro hNe
      cases hValue : IncomingTargetExpansion.right hc hab hOne edge
      · exfalso
        apply hNe
        exact divalentOccurrence_unique data hc hab hOne fullDim star edge
          ⟨hAt, Or.inl ⟨hLeft.1, hValue⟩⟩
      · rfl
  · right
    intro edge hAt
    apply Bool.eq_iff_iff.mpr
    rw [Bool.not_eq_true_eq_eq_false]
    simp only [rightOf, decide_eq_false_iff_not, Classical.not_not]
    constructor
    · intro hTrue
      exact divalentOccurrence_unique data hc hab hOne fullDim star edge
        ⟨hAt, Or.inr ⟨hRight.1, hTrue⟩⟩
    · intro hEq
      subst edge
      exact hRight.2

/-- With an actual W3 nd2 profile, the unique divalent-side occurrence is
literally one of the three source-named target directions.  The first two are
the Figure 31 coarse/fine candidates; the third alternative is the one
source-facing placement case that this lemma leaves as a disjunct. -/
theorem divalentOccurrence_eq_small_or_large_or_third
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd2Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock) :
    divalentOccurrence data hc hab hOne fullDim star =
        smallTarget input profile ∨
      divalentOccurrence data hc hab hOne fullDim star =
        largeTarget input profile ∨
      divalentOccurrence data hc hab hOne fullDim star =
        thirdTarget input profile := by
  have hAt := (divalentOccurrence_spec data hc hab hOne fullDim star).1
  rw [W3Nd2FineRefinement.incidentEdges_eq input profile] at hAt
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hAt

end DraismaVargas.LocalCases.W3Nd2IncomingTargetPlacement
