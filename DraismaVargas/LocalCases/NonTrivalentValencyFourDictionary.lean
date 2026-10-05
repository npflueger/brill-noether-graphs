module

public import DraismaVargas.LocalCases.NonTrivalentValencyFourRows
public import DraismaVargas.LocalCases.NonTrivalentUniqueFourValent

@[expose] public section

/-!
# The row dictionary of the `K = 0` candidate above a four-valent wall

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 -- in particular the
labelling convention (1): exactly one edge `h_1^(q)` of `H^(q)` contracts to
the four-valent vertex `A`, its trivalent endpoints are `A_1^(q)` and
`A_2^(q)`, and the other edges of `H^(q)` correspond bijectively to those of
`H_0` -- and Section 5.2 (Case {v4-nd4}) for the `K = 0` sizes.

This file continues `NonTrivalentValencyFourRows`, which proves that the
candidate preserves the source genus, transports the four-branch classifier to
the gauged datum, names the two endpoint vertices and the bridge occurrence
with their exact `K = 0` sizes, and shows that the bridge survives as soon as
both endpoints retain a survivor.

## What is proved here

* **Both new endpoint classes are trivalent** (`nonDanglingValency_endpointVertex`):
  `nd(A_1^(q)) = nd(A_2^(q)) = 3`, unconditionally.  The surviving star at each
  endpoint is computed exactly (`nonDanglingIncident_endpointVertex`): it is the
  bridge together with the two retained survivors of the two target directions
  the prescribed pairing assigns to that side.  The two inclusions are

  - `triple_subset_nonDanglingIncident`, from the incidence lemmas of
    `NonTrivalentValencyFourRows`, the survival of retained occurrences, and
    `bridgeEdge_survives` -- which is
    `NonTrivalentValencyFourRows.bridgeEdge_not_isDangling` fed with the
    retained survivors;
  - `nonDanglingIncident_endpointVertex_subset`, the exhaustion.  A retained
    occurrence is pinned down by `eq_survivorEdge`, i.e. target-direction
    injectivity in the *gauged* datum.  A new occurrence is either the bridge or
    sits on a singleton fine block, and
    `newSourceEdge_isDangling_of_singleton` shows the latter is dangling: every
    old occurrence at the fine-side vertex it carries is dangling by the same
    injectivity, so that vertex would otherwise have surviving valency one,
    which `NonDanglingValency.nonDanglingValency_ne_one` forbids.

* **The bridge is a stable row of its own** (`bridgeEdge_isolated`): both of its
  ends are trivalent, so by
  `NonTrivalentUniqueFourValent.eq_of_stablePath_eq_of_ends_ne_two` its
  stable-path class is the single occurrence `h_1^(q)`.  This is the "one new
  row" half of the dictionary.

* **The retained-row descent** (`retainedRow`): every stable row of the wall
  datum descends to a stable row of the candidate along the literal retained
  occurrences.  Off the wall this is
  `ResolutionAwayFromWall.consecutive_retained_of_away`; at the anchor block it
  is vacuous, because `nd = 4` there and a stable path only continues through a
  divalent vertex.  The remaining case -- a *non-anchor* wall block of surviving
  valency two -- is isolated as the named hypothesis `OrdinaryBlockDescent`.

* **The honest labelling, packaged** (`labelling`): from a square honest
  labelling of the wall datum and the row equivalence `retained ⊔ bridge`, the
  candidate gets a `W4StableSource.StableLengthMatrixLabelling` over
  `Option coordinate`.  `Option.none` -- the vanishing coordinate of the
  incoming chart -- labels the new target edge
  (`labelling_targetEdge_none`) and the bridge row.

* **Composed with the census producer** (`nonDanglingValency_endpointVertex_of_single_row`):
  at an actual four-valent wall of an incoming full-dimensional cover,
  `NonTrivalentUniqueFourValent`'s `ordinaryBlockProfile_of_single_row`
  discharges the census, so trivalence of the two endpoints carries **no**
  background, census, injectivity or trivalence receipt.

## What is NOT proved

Two named hypotheses, and one deliberate exclusion.

1. `OrdinaryBlockDescent` -- the retained-row descent across a *non-anchor* wall
   block of surviving valency two.  Its proof is the argument of
   `nonDanglingIncident_endpointVertex` re-run with that block's own canonical
   four-valent pattern (`W4Assembly.blockwiseResolution`): when the block's two active
   branches lie on the same side its new occurrence is dangling (the opposite
   endpoint is a singleton of surviving valency zero, by the same
   `nonDanglingValency_ne_one` step used in
   `newSourceEdge_isDangling_of_singleton`), so the two survivors stay
   consecutive; when they lie on opposite sides both endpoints are divalent and
   the two survivors are joined *through* the new occurrence.  The nd2/nd3
   classification needed is already carried by
   `NonTrivalentValencyFourBackground.OrdinaryBlockProfile`.
2. `rowEquiv : StablePath (candidate).datum ≃ Option (StablePath (gaugedData …))`
   -- the full row equivalence.  `retainedRow` is its retained half and
   `bridgeEdge_isolated` identifies the extra row; injectivity and surjectivity
   need the surviving-star census at *every* vertex of the candidate, i.e. (1)
   at every non-anchor wall block.
3. `AgreeOffColumn` against the incoming full-dimensional matrix is **not**
   attempted: it additionally needs the transport from the incoming cover to the
   wall datum through `GluingContraction.contractDatum`
   (`StablePath (contractDatum M …) ≃ {r : StablePath M // r ≠ facet}` with
   occurrence sets unchanged off the contracted column), which is a separate
   argument.  Nothing here depends on it.

## Consumers

The boundary dispatcher for Part II, Case {v4-nd4}
(`NonTrivalentValencyFourDispatcher`), and the nonsingularity and exit argument
built on `NonTrivalentLinkMatrix`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyFourDictionary

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.LocalCases.NonTrivalentValencyFourBackground
open DraismaVargas.LocalCases.NonTrivalentValencyFourRows

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall} {anchor : WallBlock data wall}
  (source : FourBranchAnchor data star anchor) (pairing : Fin 3)
  (hNoGlue : DanglingEdgeNoGlue data)
  (hRamification : data.localRamification wall anchor = 0)

/-! ## 1.  The gauge, sheet by sheet: the four survivors in the gauged datum -/

theorem gauge_edgePermutation_of_ne (hConnected : graph_connected target)
    (hGenus : genus target = 0) (label : Fin 4)
    (hOther : label ≠ secondSelectedLabel source pairing) :
    (relabeling source pairing hNoGlue hRamification).edgePermutation
        (star.edge label) = Equiv.refl (Fin degree) := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall _ _ (star.edge label))
    (permutation source pairing hNoGlue hRamification) = _
  rw [TargetSeparation.edgeMoved_eq_false hConnected hGenus
    (selectedEdge_incident (star := star) (secondSelectedLabel source pairing))
    (selectedEdge_incident (star := star) label)
    (fun hEqual ↦ hOther (star.edge_injective hEqual).symm)]
  rfl

theorem gauge_edgePermutation_second :
    (relabeling source pairing hNoGlue hRamification).edgePermutation
        (star.edge (secondSelectedLabel source pairing)) =
      permutation source pairing hNoGlue hRamification := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall _ _
      (star.edge (secondSelectedLabel source pairing)))
    (permutation source pairing hNoGlue hRamification) = _
  rw [TargetSeparation.edgeMoved_self_eq_true
    (selectedEdge_incident (star := star) (secondSelectedLabel source pairing))]
  rfl


/-- The sheet carrying the unique surviving occurrence of one target direction
at the anchor, read in the gauged datum. -/
noncomputable def survivorSheet (label : Fin 4) : Fin degree :=
  (relabeling source pairing hNoGlue hRamification).edgePermutation
    (star.edge label) (source.sheet label)

theorem survivorSheet_of_ne (hConnected : graph_connected target)
    (hGenus : genus target = 0) (label : Fin 4)
    (hOther : label ≠ secondSelectedLabel source pairing) :
    survivorSheet source pairing hNoGlue hRamification label =
      source.sheet label := by
  unfold survivorSheet
  rw [gauge_edgePermutation_of_ne source pairing hNoGlue hRamification hConnected
    hGenus label hOther]
  rfl

theorem survivorSheet_second :
    survivorSheet source pairing hNoGlue hRamification
        (secondSelectedLabel source pairing) =
      permutation source pairing hNoGlue hRamification
        (source.sheet (secondSelectedLabel source pairing)) := by
  unfold survivorSheet
  rw [gauge_edgePermutation_second source pairing hNoGlue hRamification]

theorem survivorSheet_wall_rel (label : Fin 4) :
    ((gaugedData source pairing hNoGlue hRamification).vertexPartition wall).Rel
      anchor.1 (survivorSheet source pairing hNoGlue hRamification label) := by
  refine (gauged_rel_iff source pairing hNoGlue hRamification _ _).mpr ?_
  exact (source.sheet_wall_rel label).trans
    (gauge_edgePermutation_rel source pairing hNoGlue hRamification
      (star.edge label) (source.sheet label)).symm

/-- The actual surviving occurrence of one target direction at the anchor of
the gauged datum. -/
noncomputable def survivorEdge (label : Fin 4) :
    (gaugedData source pairing hNoGlue hRamification).SourceEdge :=
  (gaugedData source pairing hNoGlue hRamification).sourceEdge (star.edge label)
    (survivorSheet source pairing hNoGlue hRamification label)

theorem survivorEdge_survives (hValid : data.Valid) (label : Fin 4) :
    ¬ IsDangling (gaugedData source pairing hNoGlue hRamification)
      (survivorEdge source pairing hNoGlue hRamification label) := by
  intro h
  exact source.sourceEdge_survives label
    ((gauged_isDangling_iff source pairing hNoGlue hRamification hValid
      (star.edge label) (source.sheet label)).mp h)

theorem survivorSheet_mem_selectedSheets_first (hConnected : graph_connected target)
    (hGenus : genus target = 0) :
    survivorSheet source pairing hNoGlue hRamification
        (firstSelectedLabel source pairing) ∈
      selectedSheets source pairing hNoGlue hRamification := by
  rw [survivorSheet_of_ne source pairing hNoGlue hRamification hConnected hGenus
    _ (firstSelectedLabel_ne_secondSelectedLabel source pairing)]
  exact Finset.mem_union_left _
    ((data.edgePartition (star.edge (firstSelectedLabel source pairing))).self_mem_block _)

theorem survivorSheet_mem_selectedSheets_second :
    survivorSheet source pairing hNoGlue hRamification
        (secondSelectedLabel source pairing) ∈
      selectedSheets source pairing hNoGlue hRamification := by
  rw [survivorSheet_second source pairing hNoGlue hRamification]
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
    ((data.edgePartition (star.edge (secondSelectedLabel source pairing))).self_mem_block _))

theorem label_eq_of_labelRight_smaller (label : Fin 4)
    (hSide : W4TargetPairings.Pairing.labelRight pairing label =
      smallerSide source pairing) :
    label = firstSelectedLabel source pairing ∨
      label = secondSelectedLabel source pairing := by
  have hMem : label ∈ W4TargetPairings.Pairing.labelsOnSide pairing
      (smallerSide source pairing) :=
    (W4TargetPairings.Pairing.mem_labelsOnSide _ _ _).mpr hSide
  rw [labelsOnSide_eq_pair] at hMem
  simpa [firstSelectedLabel, secondSelectedLabel] using hMem

theorem endpointForSide_rel_survivorSheet (hConnected : graph_connected target)
    (hGenus : genus target = 0) (sideValue : Bool) (label : Fin 4)
    (hSide : W4TargetPairings.Pairing.labelRight pairing label = sideValue) :
    (endpointForSide source pairing hNoGlue hRamification sideValue).Rel
      (selectedRepresentative source pairing)
      (survivorSheet source pairing hNoGlue hRamification label) := by
  unfold endpointForSide
  by_cases hSmall : sideValue = smallerSide source pairing
  · rw [ite_eq_left hSmall]
    refine ((finePartition source pairing hNoGlue hRamification).mem_block_iff
      _ _).mp ?_
    rw [finePartition_selected_block source pairing hNoGlue hRamification]
    subst hSmall
    rcases label_eq_of_labelRight_smaller source pairing label hSide with rfl | rfl
    · exact survivorSheet_mem_selectedSheets_first source pairing hNoGlue
        hRamification hConnected hGenus
    · exact survivorSheet_mem_selectedSheets_second source pairing hNoGlue
        hRamification
  · rw [ite_eq_right hSmall]
    exact Eq.trans
      (((gauged_rel_iff source pairing hNoGlue hRamification _ _).mpr
        (source.sheet_wall_rel (firstLabel pairing (smallerSide source pairing)))).symm)
      (survivorSheet_wall_rel source pairing hNoGlue hRamification label)


/-! ## 2.  Relations and incidences at the two expanded target vertices -/

section Candidate

variable (profile : OrdinaryBlockProfile data star anchor.1)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (hValid : data.Valid)

local notation "cand" =>
  (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
    hRamification profile hConnected hGenus hValid)
local notation "gauged" => (gaugedData source pairing hNoGlue hRamification)
theorem candidate_vertexPartition_rel_iff (sideValue : Bool) {a b : Fin degree}
    (hA : ((gauged).vertexPartition wall).Rel anchor.1 a) :
    ((cand).datum.vertexPartition (if sideValue then freshVertex target else oldVertex target wall)).Rel a b ↔
      (endpointForSide source pairing hNoGlue hRamification sideValue).Rel a b := by
  have hReprRel : ((gauged).vertexPartition wall).Rel anchor.1
      (((gauged).vertexPartition wall).repr a) :=
    hA.trans (((gauged).vertexPartition wall).rel_repr_right a)
  have hSelected := candidate_resolution_eq_selected source pairing hNoGlue
    hRamification profile hConnected hGenus hValid _ hReprRel
  cases sideValue
  · show (((cand).datum.vertexPartition (oldVertex target wall)).Rel a b) ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
    refine Iff.trans (SheetPartition.paste_rel_iff
      ((gauged).vertexPartition wall)
      (fun blk ↦ ((cand).resolution blk).left)
      (fun blk ↦ ((cand).contracts blk).left_refines) a b) ?_
    rw [hSelected, selectedResolution_left]
  · show (((cand).datum.vertexPartition (freshVertex target)).Rel a b) ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]
    refine Iff.trans (SheetPartition.paste_rel_iff
      ((gauged).vertexPartition wall)
      (fun blk ↦ ((cand).resolution blk).right)
      (fun blk ↦ ((cand).contracts blk).right_refines) a b) ?_
    rw [hSelected, selectedResolution_right]

theorem mem_incidentEdges_endpoint_old (sideValue : Bool) (edge : target.edges) :
    occurrenceEquiv target wall (cand).right (some edge) ∈
        GluingDatum.incidentEdges (if sideValue then freshVertex target else oldVertex target wall) ↔
      (edge ∈ GluingDatum.incidentEdges wall ∧
        star.right pairing edge = sideValue) := by
  rw [GluingContraction.mem_incidentEdges_iff, occurrenceEquiv_some,
    GluingContraction.mem_incidentEdges_iff]
  cases sideValue
  · exact oldEnds_incident_oldVertex_iff target wall (cand).right edge
  · exact oldEnds_incident_freshVertex_iff target wall (cand).right edge

theorem mem_incidentEdges_endpoint_new (sideValue : Bool) :
    occurrenceEquiv target wall (cand).right none ∈
      GluingDatum.incidentEdges (if sideValue then freshVertex target else oldVertex target wall) := by
  rw [GluingContraction.mem_incidentEdges_iff, occurrenceEquiv_none]
  cases sideValue
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem candidate_endpointPartition_refines (sideValue : Bool) :
    ((cand).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall)).Refines
      ((gauged).vertexPartition wall) := by
  cases sideValue
  · show ((cand).datum.vertexPartition (oldVertex target wall)).Refines _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
    exact LocalResolution.pasteLeft_refines
      ((gauged).vertexPartition wall) (cand).resolution (cand).contracts
  · show ((cand).datum.vertexPartition (freshVertex target)).Refines _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]
    exact LocalResolution.pasteRight_refines
      ((gauged).vertexPartition wall) (cand).resolution (cand).contracts

end Candidate

/-! ## 3.  Target-direction injectivity, read in the gauged datum -/

section Survivor

local notation "gauged" => (gaugedData source pairing hNoGlue hRamification)

theorem survivorEdge_wallBlock (label : Fin 4) :
    WallBlock.ofSheet (gauged) wall
        (survivorEdge source pairing hNoGlue hRamification label).1.2 =
      gaugedAnchor source pairing hNoGlue hRamification := by
  refine (WallBlock.ofSheet_eq_iff_rel (gauged) wall _ _).mpr ?_
  refine Eq.trans (survivorSheet_wall_rel source pairing hNoGlue hRamification
    label) ?_
  exact (star.edgePartition_refines_wall (gauged) label).rel
    (((gauged).edgePartition (star.edge label)).rel_repr_right _)

/-- Target-direction injectivity, in the form used by the endpoint census:
any surviving occurrence of one star direction at the anchor block of the
gauged datum is *the* survivor. -/
theorem eq_survivorEdge (hValid : data.Valid) (label : Fin 4)
    (edge : (gauged).SourceEdge)
    (hTarget : edge.1.1 = star.edge label)
    (hBlock : ((gauged).vertexPartition wall).Rel anchor.1 edge.1.2)
    (hSurvives : ¬ IsDangling (gauged) edge) :
    edge = survivorEdge source pairing hNoGlue hRamification label :=
  (gaugedSource source pairing hNoGlue hRamification hValid).target_injective.unique
    label edge (survivorEdge source pairing hNoGlue hRamification label)
    ((WallBlock.ofSheet_eq_iff_rel (gauged) wall _ _).mpr hBlock)
    (survivorEdge_wallBlock source pairing hNoGlue hRamification label)
    hTarget rfl hSurvives
    (survivorEdge_survives source pairing hNoGlue hRamification hValid label)

end Survivor

section Selected

theorem branchClass_first_subset (hConnected : graph_connected target)
    (hGenus : genus target = 0) :
    ((gaugedData source pairing hNoGlue hRamification).edgePartition
        (star.edge (firstSelectedLabel source pairing))).block
      (survivorSheet source pairing hNoGlue hRamification
        (firstSelectedLabel source pairing)) ⊆
      selectedSheets source pairing hNoGlue hRamification := by
  rw [survivorSheet_of_ne source pairing hNoGlue hRamification hConnected hGenus
      _ (firstSelectedLabel_ne_secondSelectedLabel source pairing),
    gaugedData_edgePartition_first source pairing hNoGlue hRamification
      hConnected hGenus]
  exact Finset.subset_union_left

theorem branchClass_second_subset :
    ((gaugedData source pairing hNoGlue hRamification).edgePartition
        (star.edge (secondSelectedLabel source pairing))).block
      (survivorSheet source pairing hNoGlue hRamification
        (secondSelectedLabel source pairing)) ⊆
      selectedSheets source pairing hNoGlue hRamification := by
  rw [survivorSheet_second source pairing hNoGlue hRamification,
    gaugedData_edgePartition_second source pairing hNoGlue hRamification,
    SheetPartition.relabel_block]
  exact Finset.subset_union_right

end Selected


/-! ## 4.  The surviving star at a `K = 0` endpoint vertex -/

section Census

variable (profile : OrdinaryBlockProfile data star anchor.1)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (hValid : data.Valid)

local notation "cand" =>
  (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
    hRamification profile hConnected hGenus hValid)
local notation "gauged" => (gaugedData source pairing hNoGlue hRamification)
local notation "rep" => (selectedRepresentative source pairing)

theorem endpointForSide_refines (sideValue : Bool) :
    (endpointForSide source pairing hNoGlue hRamification sideValue).Refines
      ((gauged).vertexPartition wall) := by
  unfold endpointForSide
  split_ifs
  · rw [gaugedData_vertexPartition_wall source pairing hNoGlue hRamification]
    exact finePartition_refines source pairing hNoGlue hRamification
  · exact SheetPartition.Refines.refl _

theorem label_eq_pair (sideValue : Bool) (label : Fin 4)
    (hSide : W4TargetPairings.Pairing.labelRight pairing label = sideValue) :
    label = firstLabel pairing sideValue ∨
      label = secondLabel pairing sideValue := by
  have hMem : label ∈ W4TargetPairings.Pairing.labelsOnSide pairing sideValue :=
    (W4TargetPairings.Pairing.mem_labelsOnSide _ _ _).mpr hSide
  rw [labelsOnSide_eq_pair] at hMem
  simpa using hMem

theorem endpointForSide_rel_of_incident (sideValue : Bool) {t : Fin degree}
    (hT : ((gauged).vertexPartition wall).Rel anchor.1 t)
    {e : (cand).datum.SourceEdge}
    (hIncident : Incident (cand).datum e
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid sideValue t)) :
    (endpointForSide source pairing hNoGlue hRamification sideValue).Rel t
      e.1.2 := by
  rw [incident_iff_target_mem_and_rel] at hIncident
  refine (candidate_vertexPartition_rel_iff source pairing hNoGlue hRamification
    profile hConnected hGenus hValid sideValue hT).mp ?_
  exact Eq.trans
    (((cand).datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right t)
    hIncident.2

theorem right_eq_of_incident_old (sideValue : Bool) {t : Fin degree}
    {old : (gauged).SourceEdge}
    (hIncident : Incident (cand).datum ((cand).oldSourceEdge old)
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid sideValue t)) :
    old.1.1 ∈ GluingDatum.incidentEdges wall ∧
      star.right pairing old.1.1 = sideValue := by
  rw [incident_iff_target_mem_and_rel] at hIncident
  have hTargetMem := hIncident.1
  rw [BalancedGlobal.Candidate.oldSourceEdge_target] at hTargetMem
  exact (mem_incidentEdges_endpoint_old source pairing hNoGlue hRamification
    profile hConnected hGenus hValid sideValue old.1.1).mp hTargetMem

theorem retained_survivor_incident (sideValue : Bool) (label : Fin 4)
    (hSide : W4TargetPairings.Pairing.labelRight pairing label = sideValue) :
    Incident (cand).datum
      ((cand).oldSourceEdge
        (survivorEdge source pairing hNoGlue hRamification label))
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid sideValue rep) := by
  have hEq := endpointVertex_eq source pairing hNoGlue hRamification profile
    hConnected hGenus hValid sideValue
    (survivorSheet_wall_rel source pairing hNoGlue hRamification label)
    (endpointForSide_rel_survivorSheet source pairing hNoGlue hRamification
      hConnected hGenus sideValue label hSide).symm
  rw [← hEq]
  exact retainedEdge_incident source pairing hNoGlue hRamification profile
    hConnected hGenus hValid (star.edge label)
    (star.edge_mem_incidentEdges label) sideValue
    ((star.right_edge pairing label).trans hSide)
    (survivorSheet source pairing hNoGlue hRamification label)

theorem retained_survivor_survives (label : Fin 4) :
    ¬ IsDangling (cand).datum
      ((cand).oldSourceEdge
        (survivorEdge source pairing hNoGlue hRamification label)) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _
    (gaugedData_valid source pairing hNoGlue hRamification hValid).1 _
    (survivorEdge_survives source pairing hNoGlue hRamification hValid label)

theorem nonDanglingValency_endpointVertex_ne_zero (sideValue : Bool) :
    nonDanglingValency (cand).datum
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid sideValue rep) ≠ 0 :=
  ClassInjectivity.nonDanglingValency_ne_zero_of_incident _
    (retained_survivor_survives source pairing hNoGlue hRamification profile
      hConnected hGenus hValid (firstLabel pairing sideValue))
    (retained_survivor_incident source pairing hNoGlue hRamification profile
      hConnected hGenus hValid sideValue (firstLabel pairing sideValue)
      ((W4TargetPairings.Pairing.mem_labelsOnSide _ _ _).mp
        (firstLabel_mem pairing sideValue)))

theorem newSourceEdge_eq_of_rel {a b : Fin degree}
    (h : (LocalResolution.paste ((gauged).vertexPartition wall)
      (cand).resolution (cand).contracts).newEdge.Rel a b) :
    (cand).newSourceEdge a = (cand).newSourceEdge b := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact h

theorem newEdge_rel_iff_finePartition {a b : Fin degree}
    (hA : ((gauged).vertexPartition wall).Rel anchor.1 a) :
    (LocalResolution.paste ((gauged).vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.Rel a b ↔
      (finePartition source pairing hNoGlue hRamification).Rel a b := by
  have hReprRel : ((gauged).vertexPartition wall).Rel anchor.1
      (((gauged).vertexPartition wall).repr a) :=
    hA.trans (((gauged).vertexPartition wall).rel_repr_right a)
  have hSelected := candidate_resolution_eq_selected source pairing hNoGlue
    hRamification profile hConnected hGenus hValid _ hReprRel
  refine Iff.trans (SheetPartition.paste_rel_iff ((gauged).vertexPartition wall)
    (fun blk ↦ ((cand).resolution blk).newEdge)
    (fun blk ↦ ((cand).resolution blk).edge_refines_left.trans
      ((cand).contracts blk).left_refines) a b) ?_
  rw [hSelected, selectedResolution_newEdge]

/-- The bridge occurrence at the selected representative survives. -/
theorem bridgeEdge_survives :
    ¬ IsDangling (cand).datum
      (bridgeEdge source pairing hNoGlue hRamification profile hConnected hGenus
        hValid rep) :=
  bridgeEdge_not_isDangling source pairing hNoGlue hRamification profile
    hConnected hGenus hValid rep
    (nonDanglingValency_endpointVertex_ne_zero source pairing hNoGlue
      hRamification profile hConnected hGenus hValid false)
    (nonDanglingValency_endpointVertex_ne_zero source pairing hNoGlue
      hRamification profile hConnected hGenus hValid true)

theorem endpointForSide_smaller :
    endpointForSide source pairing hNoGlue hRamification
        (smallerSide source pairing) =
      finePartition source pairing hNoGlue hRamification := ite_eq_left rfl

theorem nonDanglingIncident_singleton_subset {u : Fin degree}
    (hWall : ((gauged).vertexPartition wall).Rel anchor.1 u)
    (hSingleton : (finePartition source pairing hNoGlue hRamification).block u =
      {u})
    (hNotRel : ¬ (finePartition source pairing hNoGlue hRamification).Rel rep u) :
    nonDanglingIncident (cand).datum
        (endpointVertex source pairing hNoGlue hRamification profile hConnected
          hGenus hValid (smallerSide source pairing) u) ⊆
      {(cand).newSourceEdge u} := by
  classical
  intro f hf
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hf
  have hRelf : (finePartition source pairing hNoGlue hRamification).Rel u
      f.1.2 := by
    rw [← endpointForSide_smaller source pairing hNoGlue hRamification]
    exact endpointForSide_rel_of_incident source pairing hNoGlue hRamification
      profile hConnected hGenus hValid (smallerSide source pairing) hWall
      hIncident
  have hEqSheet : f.1.2 = u := by
    have hMem : f.1.2 ∈ (finePartition source pairing hNoGlue
        hRamification).block u :=
      ((finePartition source pairing hNoGlue hRamification).mem_block_iff u
        f.1.2).mpr hRelf
    rw [hSingleton] at hMem
    simpa using hMem
  rcases ResolutionPruning.sourceEdge_cases (cand) f with ⟨old, rfl⟩ | ⟨s, rfl⟩
  · exfalso
    obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old source pairing hNoGlue
      hRamification profile hConnected hGenus hValid
      (smallerSide source pairing) hIncident
    obtain ⟨label, hLabel⟩ := star.exists_edge_eq old.1.1 hAt
    have hLabelSide : W4TargetPairings.Pairing.labelRight pairing label =
        smallerSide source pairing := by
      rw [← star.right_edge pairing label, hLabel]
      exact hSide
    have hOldSheet : old.1.2 = u := hEqSheet
    have hOldSurv : ¬ IsDangling (gauged) old := fun h ↦ hSurvives
      ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid)
        (candidate_sourceGenus source pairing hNoGlue hRamification profile
          hConnected hGenus hValid) old).mpr h)
    have hBlockRel : ((gauged).vertexPartition wall).Rel anchor.1 old.1.2 :=
      hOldSheet ▸ hWall
    have hEq := eq_survivorEdge source pairing hNoGlue hRamification hValid
      label old hLabel.symm hBlockRel hOldSurv
    apply hNotRel
    refine ((finePartition source pairing hNoGlue hRamification).mem_block_iff
      rep u).mp ?_
    rw [finePartition_selected_block source pairing hNoGlue hRamification]
    have hu : u ∈ ((gauged).edgePartition (star.edge label)).block
        (survivorSheet source pairing hNoGlue hRamification label) := by
      rw [← hOldSheet, hEq]
      exact (((gauged).edgePartition (star.edge label)).mem_block_iff _ _).mpr
        (((gauged).edgePartition (star.edge label)).rel_repr_right _)
    rcases label_eq_of_labelRight_smaller source pairing label hLabelSide with
      rfl | rfl
    · exact branchClass_first_subset source pairing hNoGlue hRamification
        hConnected hGenus hu
    · exact branchClass_second_subset source pairing hNoGlue hRamification hu
  · have hRepr : (LocalResolution.paste ((gauged).vertexPartition wall)
        (cand).resolution (cand).contracts).newEdge.repr s = u := hEqSheet
    have hEq : (cand).newSourceEdge s = (cand).newSourceEdge u := by
      apply newSourceEdge_eq_of_rel
      show (LocalResolution.paste ((gauged).vertexPartition wall)
        (cand).resolution (cand).contracts).newEdge.repr s =
          (LocalResolution.paste ((gauged).vertexPartition wall)
            (cand).resolution (cand).contracts).newEdge.repr u
      rw [← hRepr, (LocalResolution.paste ((gauged).vertexPartition wall)
        (cand).resolution (cand).contracts).newEdge.repr_idem]
    rw [hEq]
    exact Finset.mem_singleton_self _

/-- A new occurrence on a singleton fine block is dangling: every old
occurrence at the fine-side vertex it carries is dangling by target-direction
injectivity, so that vertex would otherwise have surviving valency one. -/
theorem newSourceEdge_isDangling_of_singleton {u : Fin degree}
    (hWall : ((gauged).vertexPartition wall).Rel anchor.1 u)
    (hSingleton : (finePartition source pairing hNoGlue hRamification).block u =
      {u})
    (hNotRel : ¬ (finePartition source pairing hNoGlue hRamification).Rel rep u) :
    IsDangling (cand).datum ((cand).newSourceEdge u) := by
  classical
  by_contra hSurvives
  have hIncident := bridgeEdge_incident source pairing hNoGlue hRamification
    profile hConnected hGenus hValid (smallerSide source pairing) u
  have hCard := Finset.card_le_card
    (nonDanglingIncident_singleton_subset source pairing hNoGlue hRamification
      profile hConnected hGenus hValid hWall hSingleton hNotRel)
  rw [card_nonDanglingIncident, Finset.card_singleton] at hCard
  have hNe := NonDanglingValency.nonDanglingValency_ne_one (cand).datum
    ((cand).datum_valid
      (gaugedData_valid source pairing hNoGlue hRamification hValid)).1
    (endpointVertex source pairing hNoGlue hRamification profile hConnected
      hGenus hValid (smallerSide source pairing) u)
  have hPos := ClassInjectivity.nonDanglingValency_ne_zero_of_incident
    (cand).datum hSurvives hIncident
  omega

/-- **The surviving star at a `K = 0` endpoint vertex.**  Only the bridge and
the two retained survivors of the two target directions assigned to that side
survive there. -/
theorem nonDanglingIncident_endpointVertex_subset (sideValue : Bool) :
    nonDanglingIncident (cand).datum
        (endpointVertex source pairing hNoGlue hRamification profile hConnected
          hGenus hValid sideValue rep) ⊆
      {bridgeEdge source pairing hNoGlue hRamification profile hConnected hGenus
          hValid rep,
        (cand).oldSourceEdge (survivorEdge source pairing hNoGlue hRamification
          (firstLabel pairing sideValue)),
        (cand).oldSourceEdge (survivorEdge source pairing hNoGlue hRamification
          (secondLabel pairing sideValue))} := by
  classical
  intro e he
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp he
  have hRepWall : ((gauged).vertexPartition wall).Rel anchor.1 rep :=
    (gauged_rel_iff source pairing hNoGlue hRamification _ _).mpr
      (source.sheet_wall_rel _)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, rfl⟩ | ⟨s, rfl⟩
  · obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old source pairing hNoGlue
      hRamification profile hConnected hGenus hValid sideValue hIncident
    obtain ⟨label, hLabel⟩ := star.exists_edge_eq old.1.1 hAt
    have hLabelSide : W4TargetPairings.Pairing.labelRight pairing label =
        sideValue := by
      rw [← star.right_edge pairing label, hLabel]
      exact hSide
    have hRel := endpointForSide_rel_of_incident source pairing hNoGlue
      hRamification profile hConnected hGenus hValid sideValue hRepWall hIncident
    have hWallRel : ((gauged).vertexPartition wall).Rel anchor.1 old.1.2 :=
      hRepWall.trans
        ((endpointForSide_refines source pairing hNoGlue hRamification
          sideValue).rel hRel)
    have hOldSurv : ¬ IsDangling (gauged) old := fun h ↦ hSurvives
      ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid)
        (candidate_sourceGenus source pairing hNoGlue hRamification profile
          hConnected hGenus hValid) old).mpr h)
    have hEq := eq_survivorEdge source pairing hNoGlue hRamification hValid
      label old hLabel.symm hWallRel hOldSurv
    rcases label_eq_pair pairing sideValue label hLabelSide with rfl | rfl
    · exact Or.inr (Or.inl (congrArg (cand).oldSourceEdge hEq))
    · exact Or.inr (Or.inr (congrArg (cand).oldSourceEdge hEq))
  · left
    set u := (LocalResolution.paste ((gauged).vertexPartition wall)
      (cand).resolution (cand).contracts).newEdge.repr s with hu
    have hEqNew : (cand).newSourceEdge s = (cand).newSourceEdge u := by
      apply newSourceEdge_eq_of_rel
      show (LocalResolution.paste ((gauged).vertexPartition wall)
        (cand).resolution (cand).contracts).newEdge.repr s =
          (LocalResolution.paste ((gauged).vertexPartition wall)
            (cand).resolution (cand).contracts).newEdge.repr u
      rw [hu, (LocalResolution.paste ((gauged).vertexPartition wall)
        (cand).resolution (cand).contracts).newEdge.repr_idem]
    have hRel := endpointForSide_rel_of_incident source pairing hNoGlue
      hRamification profile hConnected hGenus hValid sideValue hRepWall hIncident
    have hWallRel : ((gauged).vertexPartition wall).Rel anchor.1 u :=
      hRepWall.trans
        ((endpointForSide_refines source pairing hNoGlue hRamification
          sideValue).rel hRel)
    have hWallRelData : (data.vertexPartition wall).Rel anchor.1 u :=
      (gauged_rel_iff source pairing hNoGlue hRamification _ _).mp hWallRel
    by_cases hR : (finePartition source pairing hNoGlue hRamification).Rel rep u
    · rw [hEqNew]
      exact newSourceEdge_eq_of_rel source pairing hNoGlue hRamification profile
        hConnected hGenus hValid
        ((newEdge_rel_iff_finePartition source pairing hNoGlue hRamification
          profile hConnected hGenus hValid hWallRel).mpr hR.symm)
    · exfalso
      rcases finePartition_rel_or_singleton source pairing hNoGlue hRamification
        u hWallRelData with hFine | hSing
      · exact hR hFine
      · exact hSurvives (hEqNew ▸ newSourceEdge_isDangling_of_singleton source
          pairing hNoGlue hRamification profile hConnected hGenus hValid
          hWallRel hSing hR)

theorem bridge_ne_retained (label : Fin 4) :
    bridgeEdge source pairing hNoGlue hRamification profile hConnected hGenus
        hValid rep ≠
      (cand).oldSourceEdge
        (survivorEdge source pairing hNoGlue hRamification label) := by
  intro hEq
  have h := congrArg (fun edge : (cand).datum.SourceEdge ↦ edge.1.1) hEq
  have hNone := (occurrenceEquiv target wall (cand).right).injective h
  cases hNone

theorem survivorEdge_ne {first second : Fin 4} (hNe : first ≠ second) :
    survivorEdge source pairing hNoGlue hRamification first ≠
      survivorEdge source pairing hNoGlue hRamification second := by
  intro hEq
  exact hNe (star.edge_injective
    (congrArg (fun e : (gauged).SourceEdge ↦ e.1.1) hEq))

theorem triple_subset_nonDanglingIncident (sideValue : Bool) :
    ({bridgeEdge source pairing hNoGlue hRamification profile hConnected hGenus
          hValid rep,
        (cand).oldSourceEdge (survivorEdge source pairing hNoGlue hRamification
          (firstLabel pairing sideValue)),
        (cand).oldSourceEdge (survivorEdge source pairing hNoGlue hRamification
          (secondLabel pairing sideValue))} : Finset (cand).datum.SourceEdge) ⊆
      nonDanglingIncident (cand).datum
        (endpointVertex source pairing hNoGlue hRamification profile hConnected
          hGenus hValid sideValue rep) := by
  classical
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨bridgeEdge_survives source pairing hNoGlue hRamification profile
        hConnected hGenus hValid,
        bridgeEdge_incident source pairing hNoGlue hRamification profile
          hConnected hGenus hValid sideValue rep⟩
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨retained_survivor_survives source pairing hNoGlue hRamification profile
          hConnected hGenus hValid _,
        retained_survivor_incident source pairing hNoGlue hRamification profile
          hConnected hGenus hValid sideValue _
          ((W4TargetPairings.Pairing.mem_labelsOnSide _ _ _).mp
            (firstLabel_mem pairing sideValue))⟩
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨retained_survivor_survives source pairing hNoGlue hRamification profile
          hConnected hGenus hValid _,
        retained_survivor_incident source pairing hNoGlue hRamification profile
          hConnected hGenus hValid sideValue _
          ((W4TargetPairings.Pairing.mem_labelsOnSide _ _ _).mp
            (secondLabel_mem pairing sideValue))⟩

/-- **The exact surviving star at each `K = 0` endpoint.** -/
theorem nonDanglingIncident_endpointVertex (sideValue : Bool) :
    nonDanglingIncident (cand).datum
        (endpointVertex source pairing hNoGlue hRamification profile hConnected
          hGenus hValid sideValue rep) =
      {bridgeEdge source pairing hNoGlue hRamification profile hConnected hGenus
          hValid rep,
        (cand).oldSourceEdge (survivorEdge source pairing hNoGlue hRamification
          (firstLabel pairing sideValue)),
        (cand).oldSourceEdge (survivorEdge source pairing hNoGlue hRamification
          (secondLabel pairing sideValue))} :=
  Finset.Subset.antisymm
    (nonDanglingIncident_endpointVertex_subset source pairing hNoGlue
      hRamification profile hConnected hGenus hValid sideValue)
    (triple_subset_nonDanglingIncident source pairing hNoGlue hRamification
      profile hConnected hGenus hValid sideValue)

/-- **Both new endpoint classes of the prescribed `K = 0` resolution are
trivalent.**  Part II, Section 5.1: the four-valent anchor `A` splits into
`A_1^{(q)}` and `A_2^{(q)}`, joined by the bridge `h_1^{(q)}`. -/
theorem nonDanglingValency_endpointVertex (sideValue : Bool) :
    nonDanglingValency (cand).datum
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid sideValue rep) = 3 := by
  classical
  have hRetainedNe :
      (cand).oldSourceEdge (survivorEdge source pairing hNoGlue hRamification
          (firstLabel pairing sideValue)) ≠
        (cand).oldSourceEdge (survivorEdge source pairing hNoGlue hRamification
          (secondLabel pairing sideValue)) := fun hEq ↦
    survivorEdge_ne source pairing hNoGlue hRamification
      (firstLabel_ne_secondLabel pairing sideValue)
      (ResolutionCut.oldSourceEdge_injective (cand) hEq)
  rw [← card_nonDanglingIncident,
    nonDanglingIncident_endpointVertex source pairing hNoGlue hRamification
      profile hConnected hGenus hValid sideValue]
  refine Finset.card_eq_three.mpr ⟨_, _, _, ?_, ?_, hRetainedNe, rfl⟩
  · exact bridge_ne_retained source pairing hNoGlue hRamification profile
      hConnected hGenus hValid _
  · exact bridge_ne_retained source pairing hNoGlue hRamification profile
      hConnected hGenus hValid _

/-! ### The bridge is a stable row of its own -/

theorem sourceEnds_bridgeEdge (sheet : Fin degree) :
    (cand).datum.sourceEnds
        (bridgeEdge source pairing hNoGlue hRamification profile hConnected
          hGenus hValid sheet) =
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
          hGenus hValid false sheet,
        endpointVertex source pairing hNoGlue hRamification profile hConnected
          hGenus hValid true sheet) :=
  GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet

/-- **The bridge occurrence is alone in its stable class.**  Both of its ends
are trivalent, and a stable path continues only through a divalent surviving
vertex, so `h_1^{(q)}` really is one new stable row. -/
theorem bridgeEdge_isolated
    (other : NonDanglingEdge (cand).datum)
    (hPath : other.stablePath =
      NonDanglingEdge.stablePath
        ⟨bridgeEdge source pairing hNoGlue hRamification profile hConnected
            hGenus hValid rep,
          bridgeEdge_survives source pairing hNoGlue hRamification profile
            hConnected hGenus hValid⟩) :
    other.1 = bridgeEdge source pairing hNoGlue hRamification profile hConnected
      hGenus hValid rep := by
  have hEnds := sourceEnds_bridgeEdge source pairing hNoGlue hRamification
    profile hConnected hGenus hValid rep
  refine congrArg Subtype.val
    (NonTrivalentUniqueFourValent.eq_of_stablePath_eq_of_ends_ne_two _ ?_ ?_
      other hPath)
  · rw [congrArg Prod.fst hEnds,
      nonDanglingValency_endpointVertex source pairing hNoGlue hRamification
        profile hConnected hGenus hValid false]
    omega
  · rw [congrArg Prod.snd hEnds,
      nonDanglingValency_endpointVertex source pairing hNoGlue hRamification
        profile hConnected hGenus hValid true]
    omega

/-! ## 5.  The retained-row descent and the packaged labelling

### The retained-row descent -/

/-- The remaining geometric input for the retained-row descent: at every wall
block *other than the anchor*, two surviving occurrences meeting at a divalent
quotient-source vertex still lie on one stable path of the candidate. -/
def OrdinaryBlockDescent : Prop :=
  ∀ (first second : NonDanglingEdge (gauged)) (vertex : (gauged).SourceVertex),
    vertex.1.1 = wall →
    ¬ ((gauged).vertexPartition wall).Rel anchor.1 vertex.1.2 →
    first ≠ second →
    Incident (gauged) first.1 vertex → Incident (gauged) second.1 vertex →
    nonDanglingValency (gauged) vertex = 2 →
    (ResolutionAwayFromWall.retainedEdge (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1
        first).stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1
        second).stablePath

theorem stablePath_retained_eq_of_consecutive
    (hDescent : OrdinaryBlockDescent source pairing hNoGlue hRamification
      profile hConnected hGenus hValid)
    {first second : NonDanglingEdge (gauged)}
    (h : Consecutive (gauged) first second) :
    (ResolutionAwayFromWall.retainedEdge (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1
        first).stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1
        second).stablePath := by
  obtain ⟨hNe, vertex, hFirst, hSecond, hValency⟩ := h
  by_cases hAt : vertex.1.1 = wall
  · by_cases hAnchorRel :
        ((gauged).vertexPartition wall).Rel anchor.1 vertex.1.2
    · exfalso
      have hVertex : WallBlock.sourceVertex (gauged) wall
          (gaugedAnchor source pairing hNoGlue hRamification) = vertex :=
        (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, hAnchorRel⟩
      rw [← hVertex, nonDanglingValency_gaugedAnchor source pairing hNoGlue
        hRamification hValid] at hValency
      omega
    · exact hDescent first second vertex hAt hAnchorRel hNe hFirst hSecond
        hValency
  · exact stablePath_eq_of_consecutive
      (ResolutionAwayFromWall.consecutive_retained_of_away (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid)
        (candidate_sourceGenus source pairing hNoGlue hRamification profile
          hConnected hGenus hValid)
        first second hNe vertex hAt hFirst hSecond hValency)

/-- **The retained-row map.**  Every stable row of the incoming wall datum
descends to a stable row of the outgoing candidate, following the literal
retained occurrences. -/
noncomputable def retainedRow
    (hDescent : OrdinaryBlockDescent source pairing hNoGlue hRamification
      profile hConnected hGenus hValid) :
    StablePath (gauged) → StablePath (cand).datum :=
  Quot.lift
    (fun e ↦ (ResolutionAwayFromWall.retainedEdge (cand)
      (gaugedData_valid source pairing hNoGlue hRamification hValid).1
      e).stablePath)
    (fun _ _ h ↦ stablePath_retained_eq_of_consecutive source pairing hNoGlue
      hRamification profile hConnected hGenus hValid hDescent h)

@[simp] theorem retainedRow_mk
    (hDescent : OrdinaryBlockDescent source pairing hNoGlue hRamification
      profile hConnected hGenus hValid) (e : NonDanglingEdge (gauged)) :
    retainedRow source pairing hNoGlue hRamification profile hConnected hGenus
        hValid hDescent e.stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1
        e).stablePath := rfl

/-! ### The honest labelling, packaged -/

/-- **The honest stable length-matrix labelling of the outgoing candidate.**
The wall datum's own square labelling supplies every retained row and column;
`Option.none` is the vanishing coordinate of the incoming chart, re-used here
for the new target edge and for the bridge row. -/
noncomputable def labelling {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate]
    (labelling₀ : StableLengthMatrixLabelling (gauged) coordinate)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath (gauged))) :
    StableLengthMatrixLabelling (cand).datum (Option coordinate) where
  targetEdge := (Equiv.optionCongr labelling₀.targetEdge).trans
    (occurrenceEquiv target wall (cand).right)
  row := rowEquiv.trans (Equiv.optionCongr labelling₀.row)

@[simp] theorem labelling_targetEdge_none {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate]
    (labelling₀ : StableLengthMatrixLabelling (gauged) coordinate)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath (gauged))) :
    (labelling source pairing hNoGlue hRamification profile hConnected hGenus
      hValid labelling₀ rowEquiv).targetEdge none =
      occurrenceEquiv target wall (cand).right none := rfl

@[simp] theorem labelling_targetEdge_some {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate]
    (labelling₀ : StableLengthMatrixLabelling (gauged) coordinate)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath (gauged)))
    (c : coordinate) :
    (labelling source pairing hNoGlue hRamification profile hConnected hGenus
      hValid labelling₀ rowEquiv).targetEdge (some c) =
      occurrenceEquiv target wall (cand).right (some (labelling₀.targetEdge c)) :=
  rfl

@[simp] theorem labelling_row {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate]
    (labelling₀ : StableLengthMatrixLabelling (gauged) coordinate)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath (gauged)))
    (path : StablePath (cand).datum) :
    (labelling source pairing hNoGlue hRamification profile hConnected hGenus
        hValid labelling₀ rowEquiv).row path =
      (rowEquiv path).map labelling₀.row := by
  cases h : rowEquiv path <;> simp [labelling, h]

end Census

/-! ## 6.  At an actual four-valent wall, with no census supplied -/

section ActualWall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.FullDimensionalSource

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (cover : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation cover coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (wallStar : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)
  (hForest : ContractionForest cover a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (anchorBlock : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩)
  (hAnchor : nonDanglingValency (contractDatum cover hc hab hOne)
    (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩
      anchorBlock) = 4)
  (pairing : Fin 3)

/-- **Both endpoint classes of the prescribed `K = 0` resolution are trivalent
at an actual four-valent wall.**  The hypotheses are exactly those of
`NonTrivalentUniqueFourValent.exists_valid_candidate_of_single_row`: an incoming
full-dimensional cover, the actual contraction forest, the wall metric with a
single vanishing stable row, and the anchor's `nd = 4`.  No census, background,
injectivity or trivalence receipt is supplied. -/
theorem nonDanglingValency_endpointVertex_of_single_row (sideValue : Bool) :
    nonDanglingValency
      (NonTrivalentValencyFourBackground.candidate
        (NonTrivalentUniqueFourValent.wallFourBranchAnchor cover fd hc hab hOne
          wallStar hForest anchorBlock hAnchor) pairing
        (NonTrivalentUniqueFourValent.wall_noGlue cover fd hc hab hOne hForest)
        (NonTrivalentUniqueFourValent.wall_ramification cover fd hc hab hOne
          wallStar hForest anchorBlock)
        (NonTrivalentUniqueFourValent.ordinaryBlockProfile_of_single_row cover fd
          hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord
          anchorBlock hAnchor)
        (NonTrivalentUniqueFourValent.wall_target_connected cover fd hab hOne)
        (NonTrivalentUniqueFourValent.wall_target_genus cover fd hab hOne)
        (NonTrivalentUniqueFourValent.wall_valid cover fd hc hab hOne
          hForest)).datum
      (endpointVertex
        (NonTrivalentUniqueFourValent.wallFourBranchAnchor cover fd hc hab hOne
          wallStar hForest anchorBlock hAnchor) pairing
        (NonTrivalentUniqueFourValent.wall_noGlue cover fd hc hab hOne hForest)
        (NonTrivalentUniqueFourValent.wall_ramification cover fd hc hab hOne
          wallStar hForest anchorBlock)
        (NonTrivalentUniqueFourValent.ordinaryBlockProfile_of_single_row cover fd
          hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord
          anchorBlock hAnchor)
        (NonTrivalentUniqueFourValent.wall_target_connected cover fd hab hOne)
        (NonTrivalentUniqueFourValent.wall_target_genus cover fd hab hOne)
        (NonTrivalentUniqueFourValent.wall_valid cover fd hc hab hOne hForest)
        sideValue
        (selectedRepresentative
          (NonTrivalentUniqueFourValent.wallFourBranchAnchor cover fd hc hab hOne
            wallStar hForest anchorBlock hAnchor) pairing)) = 3 :=
  nonDanglingValency_endpointVertex _ pairing _ _ _ _ _ _ sideValue

end ActualWall

end DraismaVargas.LocalCases.NonTrivalentValencyFourDictionary
