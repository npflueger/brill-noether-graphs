module

public import DraismaVargas.LocalCases.NonTrivalentValencyFourDescent
public import DraismaVargas.LocalCases.NonTrivalentUniqueFourValent
public import DraismaVargas.LocalCases.StablePathFacetContraction

@[expose] public section

/-!
# The `K = 0` row dictionary at a four-valent wall: the descent, unconditionally

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1: rigidity above `w_0`,
the labelling convention (1), and `lm:change-comb-type` (the wall matrix as the
common minor `A_{\varphi_0}` of the incoming matrices).

`NonTrivalentValencyFourRowEquiv` proves the local picture at a non-anchor
wall block, and `NonTrivalentValencyFourDescent` the shared helpers and the
first of the four descent cases.  This module finishes that case analysis,
proves the named hypothesis
`NonTrivalentValencyFourDictionary.OrdinaryBlockDescent`, and packages the
retained-row map and the outgoing honest labelling.

## What is proved

* **The other three descent cases at a non-anchor wall block** of surviving
  valency two with survivors `first != second`, split by the side the prescribed
  pairing assigns to each and by the block's new-edge classes:
  - `descent_of_mixed` (one survivor per side): the fine survivor's own new
    occurrence survives (`newSourceEdge_survives_of_unique_fine_survivor` at
    that survivor's sheet, uniqueness in its class from `eq_of_survivor`), is
    absorbed into its row (`stablePath_newSourceEdge_eq`), and the retaining
    endpoint carries exactly it and the retaining survivor
    (`nonDanglingIncident_ret_dichotomy`, `nonDanglingValency_eq_two_of_pair`);
  - `descent_of_both_fine_same` (both on the fine side, one new-edge class): the
    single new occurrence of that class is alone at the retaining endpoint,
    hence dangling (`isDangling_of_subset_singleton`), and the common fine
    endpoint carries exactly the two survivors
    (`nonDanglingIncident_fine_cases`);
  - `descent_of_both_fine_split` (both on the fine side, two classes): two
    surviving new occurrences, each absorbed into its survivor's row, and they
    are the only two objects at the retaining endpoint.

* **`ordinaryBlockDescent`** -- `OrdinaryBlockDescent` from the standing binders
  of the prescribed pairing, and therefore

* **`retainedRow`, unconditionally**: `StablePath (gaugedData ...) ->
  StablePath (candidate ...).datum`, with `retainedRow_mk`.  No geometric
  hypothesis about the candidate is needed.  `ordinaryBlockDescent_of_single_row` and
  `retainedRow_of_single_row` are the same statements at an *actual* four-valent
  wall, with `NonTrivalentUniqueFourValent.ordinaryBlockProfile_of_single_row`
  discharging the census: the hypotheses are exactly those of
  `NonTrivalentValencyFourAnchor.fourBranchAnchor_of_single_zero_row` plus the
  wall metric.

* **Towards the row equivalence.**  `newSourceEdge_anchor_eq_bridge` (a
  surviving new occurrence over the anchor block *is* the bridge),
  `retainedRow_ne_bridgeRow` (the bridge row is not retained, from
  `bridgeEdge_isolated`), and `stablePath_cases` (every stable row of the
  candidate is retained or carries a new occurrence).

* **The outgoing honest labelling and its matrix.**  `relabelLabelling`
  transports a square honest labelling of the wall datum across the
  block-preserving sheet gauge; `candidateLabelling` is
  `NonTrivalentValencyFourDictionary.labelling` over `Option coordinate`;
  `reindexLabelling` and `chartLabelling` re-index it along any
  `Option coordinate_0 ~= coordinate` -- for
  `Equiv.optionSubtypeNe` this puts `Option.none`, the new target occurrence and
  the bridge row, in the contracted column.  `occurrences_retainedRow` is the
  occurrence-set statement off the new column (the surviving occurrences of a
  retained row over an old target occurrence are the retained copies of the wall
  datum's), `matrix_retainedRow` its matrix form, `matrix_candidateLabelling`
  and `matrix_chartLabelling` the labelled forms, and
  `matrix_chartLabelling_eq_incoming` composes with
  `StablePathFacetContraction.matrix_wallLabelling` into the
  `AgreeOffColumn`-shaped identity: entry by entry, the outgoing matrix equals
  the incoming full-dimensional cover's off the contracted column.

## What is NOT proved

`rowEquiv : StablePath (candidate ...).datum ~= Option (StablePath (gaugedData ...))`
itself.  Every labelling statement in this file takes the equivalence as an
explicit argument, together with the single compatibility hypothesis
`hRowRetained : forall r, rowEquiv (retainedRow ... r) = some r`; nothing else
about the candidate is assumed.

**Where the row equivalence is constructed.**  `NonTrivalentValencyFourRowEquivFinal`
builds it.  The occurrence-level census it needs -- every survivor of a
non-anchor wall block over an active label, and `NonDanglingStarInjective`
there -- is available at an actual wall
(`ordinaryBlockProfile_of_single_row_active`, `wall_starInjective`) and is
transported across the block-preserving gauge at every block
(`activeLabels_gaugedBlock`, `nonDanglingStarInjective_gaugedBlock`).  A
reading of the fine classes by nd-pattern ("exactly one survivor at an nd3
block and at an opposite-side nd2 block, none otherwise") would fail on the
degenerate blocks where `retSide` cannot tell the two endpoints apart.  The
statement used instead is
`NonTrivalentValencyFourRowEquivFinal.newSourceEdge_absorbed` -- every
surviving new occurrence over a non-anchor block lies on the row of a retained
survivor of that block -- proved from target-direction injectivity and the
surviving-valency bound `nd <= 3` alone, through `eq_of_three_on_side` (a 2+2
pairing has two labels per side, so a block has at most two survivors per
side); no `retSide`-versus-singleton-side identification is needed.  With it
`rowMap = retained || bridge` is surjective, and
`NonTrivalentValencyFourRowEquivFinal.rowEquiv` / `rowEquiv_retainedRow` /
`chartLabelling_of_single_row` / `matrix_chartLabelling_eq_incoming_of_single_row`
carry exactly one further hypothesis, `Function.Injective (retainedRow ...)`,
which `NonTrivalentValencyFourRetainedInjective` proves.

## Consumers

The boundary dispatcher for Part II, Case {v4-nd4}
(`NonTrivalentValencyFourDispatcher`), and the nonsingularity and exit argument
built on `NonTrivalentLinkMatrix`, whose
`AgreeOffColumn` input is `matrix_chartLabelling_eq_incoming`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyFourRowDictionary

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
open DraismaVargas.LocalCases.NonTrivalentValencyFourDictionary
open DraismaVargas.LocalCases.NonTrivalentValencyFourRowEquiv
open DraismaVargas.LocalCases.NonTrivalentValencyFourDescent

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall} {anchor : WallBlock data wall}
  (source : FourBranchAnchor data star anchor) (pairing : Fin 3)
  (hNoGlue : DanglingEdgeNoGlue data)
  (hRamification : data.localRamification wall anchor = 0)
  (profile : OrdinaryBlockProfile data star anchor.1)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (hValid : data.Valid)

local notation "cand" =>
  (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
    hRamification profile hConnected hGenus hValid)
local notation "gauged" => (gaugedData source pairing hNoGlue hRamification)
local notation "coarse" =>
  (GluingDatum.vertexPartition
    (gaugedData source pairing hNoGlue hRamification) wall)
local notation "blockRes" =>
  (W4Assembly.blockwiseResolution
    (gaugedData source pairing hNoGlue hRamification) star profile.pattern
    pairing)

/-! ## Elementary bookkeeping -/

theorem bool_eq_not_of_ne {x y : Bool} (h : x ≠ y) : x = !y := by
  cases x <;> cases y <;> simp_all

theorem new_ne_old (s : Fin degree) (old : (gauged).SourceEdge) :
    (cand).oldSourceEdge old ≠ (cand).newSourceEdge s := by
  intro hEq
  have h := (occurrenceEquiv target wall (cand).right).injective
    (congrArg (fun e : (cand).datum.SourceEdge ↦ e.1.1) hEq)
  cases h

theorem newSourceEdge_rel_of_eq {a b : Fin degree}
    (h : (cand).newSourceEdge a = (cand).newSourceEdge b) :
    (LocalResolution.paste ((gauged).vertexPartition wall)
      (cand).resolution (cand).contracts).newEdge.Rel a b :=
  congrArg (fun e : (cand).datum.SourceEdge ↦ e.1.2) h

/-- The retaining-side endpoint of a non-anchor block, read on a sheet of the
block rather than on the block's representative. -/
theorem newSourceEdge_incident_ret {x : Fin degree}
    (hb : ¬ (coarse).Rel anchor.1 x) {y : Fin degree}
    (hRel : (coarse).Rel x y) :
    Incident (cand).datum ((cand).newSourceEdge y)
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x)) x) := by
  have h := bridgeEdge_incident source pairing hNoGlue hRamification profile
    hConnected hGenus hValid
    (retSide source pairing hNoGlue hRamification profile ((coarse).repr x)) y
  rw [endpointVertex_ret_eq source pairing hNoGlue hRamification profile
    hConnected hGenus hValid hb hRel] at h
  exact h

/-- A retained survivor of a non-anchor block assigned to the retaining side is
incident to that block's retaining endpoint. -/
theorem oldSourceEdge_incident_ret {x : Fin degree}
    (hb : ¬ (coarse).Rel anchor.1 x) {z : (gauged).SourceEdge}
    (hzAt : z.1.1 ∈ GluingDatum.incidentEdges wall)
    (hzRel : (coarse).Rel x z.1.2)
    (hzSide : star.right pairing z.1.1 =
      retSide source pairing hNoGlue hRamification profile ((coarse).repr x)) :
    Incident (cand).datum ((cand).oldSourceEdge z)
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x)) x) := by
  have h := retainedEdge_incident source pairing hNoGlue hRamification profile
    hConnected hGenus hValid z.1.1 hzAt _ hzSide z.1.2
  rw [GluingDatum.sourceEdge_self,
    endpointVertex_ret_eq source pairing hNoGlue hRamification profile
      hConnected hGenus hValid hb hzRel] at h
  exact h

/-! ## Case 2: one survivor on each side -/

/-- **The descent when one survivor is assigned to the retaining side and the
other to the fine side.**  The fine survivor's own new occurrence survives and
is absorbed into its row; at the retaining endpoint it is consecutive to the
retaining survivor. -/
theorem descent_of_mixed
    (first second : NonDanglingEdge (gauged))
    (vertex : (gauged).SourceVertex) (hAt : vertex.1.1 = wall)
    (hNe : first ≠ second)
    (hFirst : Incident (gauged) first.1 vertex)
    (hSecond : Incident (gauged) second.1 vertex)
    (hValency : nonDanglingValency (gauged) vertex = 2)
    (hbAnchor : ¬ (coarse).Rel anchor.1 vertex.1.2)
    (hsE : star.right pairing first.1.1.1 =
      retSide source pairing hNoGlue hRamification profile
        ((coarse).repr vertex.1.2))
    (hsF : star.right pairing second.1.1.1 =
      !retSide source pairing hNoGlue hRamification profile
        ((coarse).repr vertex.1.2)) :
    (ResolutionAwayFromWall.retainedEdge (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1
        first).stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1
        second).stablePath := by
  classical
  have hV : (gauged).sourceEndpoint wall vertex.1.2 = vertex :=
    (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
  obtain ⟨hAtE, hRelE⟩ := (incident_sourceEndpoint_iff source pairing hNoGlue
    hRamification _ first.1).mp (by rw [hV]; exact hFirst)
  obtain ⟨hAtF, hRelF⟩ := (incident_sourceEndpoint_iff source pairing hNoGlue
    hRamification _ second.1).mp (by rw [hV]; exact hSecond)
  have hRepr : (coarse).repr second.1.1.2 = (coarse).repr vertex.1.2 :=
    hRelF.symm
  have hbF : ¬ (coarse).Rel anchor.1 second.1.1.2 :=
    fun h ↦ hbAnchor (h.trans hRelF.symm)
  have hSideF : star.right pairing second.1.1.1 =
      !retSide source pairing hNoGlue hRamification profile
        ((coarse).repr second.1.1.2) := by rw [hRepr]; exact hsF
  have hRelSelf : (blockRes ((coarse).repr second.1.1.2)).newEdge.Rel
      second.1.1.2 second.1.1.2 := rfl
  have hUnique : ∀ other : (gauged).SourceEdge, ¬ IsDangling (gauged) other →
      other.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing other.1.1 =
        !retSide source pairing hNoGlue hRamification profile
          ((coarse).repr second.1.1.2) →
      (blockRes ((coarse).repr second.1.1.2)).newEdge.Rel second.1.1.2
        other.1.2 → other = second.1 := by
    intro other hoS hoAt hoSide hoRel
    have hCoarse : (coarse).Rel vertex.1.2 other.1.2 :=
      hRelF.trans ((blockRes_newEdge_refines source pairing hNoGlue
        hRamification profile _).rel hoRel)
    rcases eq_of_survivor source pairing hNoGlue hRamification first second
      vertex hAt hNe hFirst hSecond hValency other hoS hoAt hCoarse with
      rfl | rfl
    · exfalso
      rw [hRepr] at hoSide
      exact absurd (hsE.symm.trans hoSide) (by simp)
    · rfl
  obtain ⟨hNewSurv, _⟩ := newSourceEdge_survives_of_unique_fine_survivor source
    pairing hNoGlue hRamification profile hConnected hGenus hValid hbF second.2
    hAtF hSideF hRelSelf hUnique
  have hNewRow := stablePath_newSourceEdge_eq source pairing hNoGlue
    hRamification profile hConnected hGenus hValid hbF second.2 hAtF hSideF
    hRelSelf hUnique
  have hIncidA := oldSourceEdge_incident_ret source pairing hNoGlue hRamification
    profile hConnected hGenus hValid hbAnchor hAtE hRelE hsE
  have hIncidB := newSourceEdge_incident_ret source pairing hNoGlue hRamification
    profile hConnected hGenus hValid hbAnchor hRelF
  have hSurvA : ¬ IsDangling (cand).datum ((cand).oldSourceEdge first.1) :=
    ResolutionSurvival.not_isDangling_oldSourceEdge _
      (gaugedData_valid source pairing hNoGlue hRamification hValid).1 _ first.2
  have hNeAB := new_ne_old source pairing hNoGlue hRamification profile
    hConnected hGenus hValid second.1.1.2 first.1
  have hSubset :
      nonDanglingIncident (cand).datum
          (endpointVertex source pairing hNoGlue hRamification profile
            hConnected hGenus hValid
            (retSide source pairing hNoGlue hRamification profile
              ((coarse).repr vertex.1.2)) vertex.1.2) ⊆
        {(cand).oldSourceEdge first.1, (cand).newSourceEdge second.1.1.2} := by
    intro f hf
    obtain ⟨hfS, hfI⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    rcases nonDanglingIncident_ret_dichotomy source pairing hNoGlue hRamification
      profile hConnected hGenus hValid hbAnchor hfS hfI with
      ⟨old, hoS, hoAt, hoSide, hoRel, rfl⟩ | ⟨old, hoS, hoAt, hoSide, hoRel, rfl⟩
    · rcases eq_of_survivor source pairing hNoGlue hRamification first second
        vertex hAt hNe hFirst hSecond hValency old hoS hoAt hoRel with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact absurd (hsF.symm.trans hoSide) (by simp)
    · rcases eq_of_survivor source pairing hNoGlue hRamification first second
        vertex hAt hNe hFirst hSecond hValency old hoS hoAt hoRel with rfl | rfl
      · exact absurd (hsE.symm.trans hoSide) (by simp)
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hValency2 := nonDanglingValency_eq_two_of_pair source pairing hNoGlue
    hRamification profile hConnected hGenus hValid hNeAB hSubset
    ((mem_nonDanglingIncident _ _ _).mpr ⟨hSurvA, hIncidA⟩)
    ((mem_nonDanglingIncident _ _ _).mpr ⟨hNewSurv, hIncidB⟩)
  refine Eq.trans (stablePath_eq_of_consecutive
    (⟨fun h ↦ hNeAB (congrArg Subtype.val h),
      endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (retSide source pairing hNoGlue hRamification profile
          ((coarse).repr vertex.1.2)) vertex.1.2,
      hIncidA, hIncidB, hValency2⟩ :
      Consecutive (cand).datum
        (ResolutionAwayFromWall.retainedEdge (cand)
          (gaugedData_valid source pairing hNoGlue hRamification hValid).1 first)
        ⟨(cand).newSourceEdge second.1.1.2, hNewSurv⟩)) ?_
  exact hNewRow

/-! ## Cases 3 and 4: both survivors on the fine side -/

/-- **The descent when both survivors are assigned to the fine side and lie in
one new-edge class.**  The block's new occurrence is then alone at the retaining
endpoint, hence dangling, and the two survivors meet at their common fine
endpoint. -/
theorem descent_of_both_fine_same
    (first second : NonDanglingEdge (gauged))
    (vertex : (gauged).SourceVertex) (hAt : vertex.1.1 = wall)
    (hNe : first ≠ second)
    (hFirst : Incident (gauged) first.1 vertex)
    (hSecond : Incident (gauged) second.1 vertex)
    (hValency : nonDanglingValency (gauged) vertex = 2)
    (hbAnchor : ¬ (coarse).Rel anchor.1 vertex.1.2)
    (hsE : star.right pairing first.1.1.1 =
      !retSide source pairing hNoGlue hRamification profile
        ((coarse).repr vertex.1.2))
    (hsF : star.right pairing second.1.1.1 =
      !retSide source pairing hNoGlue hRamification profile
        ((coarse).repr vertex.1.2))
    (hClass : (blockRes ((coarse).repr vertex.1.2)).newEdge.Rel first.1.1.2
      second.1.1.2) :
    (ResolutionAwayFromWall.retainedEdge (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1
        first).stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1
        second).stablePath := by
  classical
  have hV : (gauged).sourceEndpoint wall vertex.1.2 = vertex :=
    (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
  obtain ⟨hAtE, hRelE⟩ := (incident_sourceEndpoint_iff source pairing hNoGlue
    hRamification _ first.1).mp (by rw [hV]; exact hFirst)
  obtain ⟨hAtF, hRelF⟩ := (incident_sourceEndpoint_iff source pairing hNoGlue
    hRamification _ second.1).mp (by rw [hV]; exact hSecond)
  have hReprE : (coarse).repr first.1.1.2 = (coarse).repr vertex.1.2 := hRelE.symm
  have hbE : ¬ (coarse).Rel anchor.1 first.1.1.2 :=
    fun h ↦ hbAnchor (h.trans hRelE.symm)
  have hsE' : star.right pairing first.1.1.1 =
      !retSide source pairing hNoGlue hRamification profile
        ((coarse).repr first.1.1.2) := by rw [hReprE]; exact hsE
  have hsF' : star.right pairing second.1.1.1 =
      !retSide source pairing hNoGlue hRamification profile
        ((coarse).repr first.1.1.2) := by rw [hReprE]; exact hsF
  have hClass' : (blockRes ((coarse).repr first.1.1.2)).newEdge.Rel first.1.1.2
      second.1.1.2 := by rw [hReprE]; exact hClass
  have hNewEq : (cand).newSourceEdge first.1.1.2 =
      (cand).newSourceEdge second.1.1.2 :=
    newSourceEdge_eq_of_rel source pairing hNoGlue hRamification profile
      hConnected hGenus hValid
      ((candidate_newEdge_rel_block source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hbE second.1.1.2).mpr hClass')
  -- the block's new occurrence is alone at the retaining endpoint, so dangling
  have hIncidNew := newSourceEdge_incident_ret source pairing hNoGlue
    hRamification profile hConnected hGenus hValid hbAnchor hRelE
  have hSubsetRet :
      nonDanglingIncident (cand).datum
          (endpointVertex source pairing hNoGlue hRamification profile
            hConnected hGenus hValid
            (retSide source pairing hNoGlue hRamification profile
              ((coarse).repr vertex.1.2)) vertex.1.2) ⊆
        {(cand).newSourceEdge first.1.1.2} := by
    intro f hf
    obtain ⟨hfS, hfI⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    rcases nonDanglingIncident_ret_dichotomy source pairing hNoGlue hRamification
      profile hConnected hGenus hValid hbAnchor hfS hfI with
      ⟨old, hoS, hoAt, hoSide, hoRel, rfl⟩ | ⟨old, hoS, hoAt, hoSide, hoRel, rfl⟩
    · rcases eq_of_survivor source pairing hNoGlue hRamification first second
        vertex hAt hNe hFirst hSecond hValency old hoS hoAt hoRel with rfl | rfl
      · exact absurd (hsE.symm.trans hoSide) (by simp)
      · exact absurd (hsF.symm.trans hoSide) (by simp)
    · rcases eq_of_survivor source pairing hNoGlue hRamification first second
        vertex hAt hNe hFirst hSecond hValency old hoS hoAt hoRel with rfl | rfl
      · exact Finset.mem_singleton_self _
      · rw [← hNewEq]
        exact Finset.mem_singleton_self _
  have hNewDangling := isDangling_of_subset_singleton source pairing hNoGlue
    hRamification profile hConnected hGenus hValid hSubsetRet hIncidNew
  -- the two survivors meet at the common fine endpoint
  have hIncidA : Incident (cand).datum ((cand).oldSourceEdge first.1)
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (!retSide source pairing hNoGlue hRamification profile
          ((coarse).repr first.1.1.2)) first.1.1.2) := by
    have h := retainedEdge_incident source pairing hNoGlue hRamification profile
      hConnected hGenus hValid first.1.1.1 hAtE _ hsE' first.1.1.2
    rw [GluingDatum.sourceEdge_self] at h
    exact h
  have hIncidB : Incident (cand).datum ((cand).oldSourceEdge second.1)
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (!retSide source pairing hNoGlue hRamification profile
          ((coarse).repr first.1.1.2)) first.1.1.2) := by
    have h := retainedEdge_incident source pairing hNoGlue hRamification profile
      hConnected hGenus hValid second.1.1.1 hAtF _ hsF' second.1.1.2
    rw [GluingDatum.sourceEdge_self,
      endpointVertex_fine_eq source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hbE hClass'] at h
    exact h
  have hSurvA : ¬ IsDangling (cand).datum ((cand).oldSourceEdge first.1) :=
    ResolutionSurvival.not_isDangling_oldSourceEdge _
      (gaugedData_valid source pairing hNoGlue hRamification hValid).1 _ first.2
  have hSurvB : ¬ IsDangling (cand).datum ((cand).oldSourceEdge second.1) :=
    ResolutionSurvival.not_isDangling_oldSourceEdge _
      (gaugedData_valid source pairing hNoGlue hRamification hValid).1 _ second.2
  have hNeVal : first.1 ≠ second.1 := fun h ↦ hNe (Subtype.ext h)
  have hNeAB : (cand).oldSourceEdge first.1 ≠ (cand).oldSourceEdge second.1 :=
    fun h ↦ hNeVal (ResolutionCut.oldSourceEdge_injective (cand) h)
  have hSubsetFine :
      nonDanglingIncident (cand).datum
          (endpointVertex source pairing hNoGlue hRamification profile
            hConnected hGenus hValid
            (!retSide source pairing hNoGlue hRamification profile
              ((coarse).repr first.1.1.2)) first.1.1.2) ⊆
        {(cand).oldSourceEdge first.1, (cand).oldSourceEdge second.1} := by
    intro f hf
    obtain ⟨hfS, hfI⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    rcases nonDanglingIncident_fine_cases source pairing hNoGlue hRamification
      profile hConnected hGenus hValid hbE hfS hfI with
      hNew | ⟨old, hoS, hoAt, _, hoRel, rfl⟩
    · exact absurd (hNew ▸ hfS) (by
        intro hBad
        exact hBad hNewDangling)
    · have hCoarse : (coarse).Rel vertex.1.2 old.1.2 :=
        hRelE.trans ((blockRes_newEdge_refines source pairing hNoGlue
          hRamification profile _).rel hoRel)
      rcases eq_of_survivor source pairing hNoGlue hRamification first second
        vertex hAt hNe hFirst hSecond hValency old hoS hoAt hCoarse with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact stablePath_eq_of_consecutive
    ⟨fun h ↦ hNeAB (congrArg Subtype.val h),
      endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (!retSide source pairing hNoGlue hRamification profile
          ((coarse).repr first.1.1.2)) first.1.1.2,
      hIncidA, hIncidB,
      nonDanglingValency_eq_two_of_pair source pairing hNoGlue hRamification
        profile hConnected hGenus hValid hNeAB hSubsetFine
        ((mem_nonDanglingIncident _ _ _).mpr ⟨hSurvA, hIncidA⟩)
        ((mem_nonDanglingIncident _ _ _).mpr ⟨hSurvB, hIncidB⟩)⟩

/-- **The descent when both survivors are assigned to the fine side and lie in
two different new-edge classes.**  Each survivor's own new occurrence survives
and is absorbed into its row, and those two new occurrences are the only objects
at the retaining endpoint. -/
theorem descent_of_both_fine_split
    (first second : NonDanglingEdge (gauged))
    (vertex : (gauged).SourceVertex) (hAt : vertex.1.1 = wall)
    (hNe : first ≠ second)
    (hFirst : Incident (gauged) first.1 vertex)
    (hSecond : Incident (gauged) second.1 vertex)
    (hValency : nonDanglingValency (gauged) vertex = 2)
    (hbAnchor : ¬ (coarse).Rel anchor.1 vertex.1.2)
    (hsE : star.right pairing first.1.1.1 =
      !retSide source pairing hNoGlue hRamification profile
        ((coarse).repr vertex.1.2))
    (hsF : star.right pairing second.1.1.1 =
      !retSide source pairing hNoGlue hRamification profile
        ((coarse).repr vertex.1.2))
    (hClass : ¬ (blockRes ((coarse).repr vertex.1.2)).newEdge.Rel first.1.1.2
      second.1.1.2) :
    (ResolutionAwayFromWall.retainedEdge (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1
        first).stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1
        second).stablePath := by
  classical
  have hV : (gauged).sourceEndpoint wall vertex.1.2 = vertex :=
    (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
  obtain ⟨hAtE, hRelE⟩ := (incident_sourceEndpoint_iff source pairing hNoGlue
    hRamification _ first.1).mp (by rw [hV]; exact hFirst)
  obtain ⟨hAtF, hRelF⟩ := (incident_sourceEndpoint_iff source pairing hNoGlue
    hRamification _ second.1).mp (by rw [hV]; exact hSecond)
  have hReprE : (coarse).repr first.1.1.2 = (coarse).repr vertex.1.2 := hRelE.symm
  have hReprF : (coarse).repr second.1.1.2 = (coarse).repr vertex.1.2 := hRelF.symm
  have hbE : ¬ (coarse).Rel anchor.1 first.1.1.2 :=
    fun h ↦ hbAnchor (h.trans hRelE.symm)
  have hbF : ¬ (coarse).Rel anchor.1 second.1.1.2 :=
    fun h ↦ hbAnchor (h.trans hRelF.symm)
  have hsE' : star.right pairing first.1.1.1 =
      !retSide source pairing hNoGlue hRamification profile
        ((coarse).repr first.1.1.2) := by rw [hReprE]; exact hsE
  have hsF' : star.right pairing second.1.1.1 =
      !retSide source pairing hNoGlue hRamification profile
        ((coarse).repr second.1.1.2) := by rw [hReprF]; exact hsF
  have hUniqueE : ∀ other : (gauged).SourceEdge, ¬ IsDangling (gauged) other →
      other.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing other.1.1 =
        !retSide source pairing hNoGlue hRamification profile
          ((coarse).repr first.1.1.2) →
      (blockRes ((coarse).repr first.1.1.2)).newEdge.Rel first.1.1.2 other.1.2 →
      other = first.1 := by
    intro other hoS hoAt _ hoRel
    have hCoarse : (coarse).Rel vertex.1.2 other.1.2 :=
      hRelE.trans ((blockRes_newEdge_refines source pairing hNoGlue
        hRamification profile _).rel hoRel)
    rcases eq_of_survivor source pairing hNoGlue hRamification first second
      vertex hAt hNe hFirst hSecond hValency other hoS hoAt hCoarse with rfl | rfl
    · rfl
    · exact absurd (by rw [← hReprE]; exact hoRel) hClass
  have hUniqueF : ∀ other : (gauged).SourceEdge, ¬ IsDangling (gauged) other →
      other.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing other.1.1 =
        !retSide source pairing hNoGlue hRamification profile
          ((coarse).repr second.1.1.2) →
      (blockRes ((coarse).repr second.1.1.2)).newEdge.Rel second.1.1.2
        other.1.2 → other = second.1 := by
    intro other hoS hoAt _ hoRel
    have hCoarse : (coarse).Rel vertex.1.2 other.1.2 :=
      hRelF.trans ((blockRes_newEdge_refines source pairing hNoGlue
        hRamification profile _).rel hoRel)
    rcases eq_of_survivor source pairing hNoGlue hRamification first second
      vertex hAt hNe hFirst hSecond hValency other hoS hoAt hCoarse with rfl | rfl
    · exact absurd (by rw [← hReprF] at hClass ⊢; exact hoRel.symm) hClass
    · rfl
  obtain ⟨hNewSurvE, _⟩ := newSourceEdge_survives_of_unique_fine_survivor source
    pairing hNoGlue hRamification profile hConnected hGenus hValid hbE first.2
    hAtE hsE' rfl hUniqueE
  obtain ⟨hNewSurvF, _⟩ := newSourceEdge_survives_of_unique_fine_survivor source
    pairing hNoGlue hRamification profile hConnected hGenus hValid hbF second.2
    hAtF hsF' rfl hUniqueF
  have hRowE := stablePath_newSourceEdge_eq source pairing hNoGlue hRamification
    profile hConnected hGenus hValid hbE first.2 hAtE hsE' rfl hUniqueE
  have hRowF := stablePath_newSourceEdge_eq source pairing hNoGlue hRamification
    profile hConnected hGenus hValid hbF second.2 hAtF hsF' rfl hUniqueF
  have hNeNew : (cand).newSourceEdge first.1.1.2 ≠
      (cand).newSourceEdge second.1.1.2 := by
    intro hEq
    refine hClass ?_
    rw [← hReprE]
    exact (candidate_newEdge_rel_block source pairing hNoGlue hRamification
      profile hConnected hGenus hValid hbE second.1.1.2).mp
      (newSourceEdge_rel_of_eq source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hEq)
  have hIncidA := newSourceEdge_incident_ret source pairing hNoGlue hRamification
    profile hConnected hGenus hValid hbAnchor hRelE
  have hIncidB := newSourceEdge_incident_ret source pairing hNoGlue hRamification
    profile hConnected hGenus hValid hbAnchor hRelF
  have hSubset :
      nonDanglingIncident (cand).datum
          (endpointVertex source pairing hNoGlue hRamification profile
            hConnected hGenus hValid
            (retSide source pairing hNoGlue hRamification profile
              ((coarse).repr vertex.1.2)) vertex.1.2) ⊆
        {(cand).newSourceEdge first.1.1.2, (cand).newSourceEdge second.1.1.2} := by
    intro f hf
    obtain ⟨hfS, hfI⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    rcases nonDanglingIncident_ret_dichotomy source pairing hNoGlue hRamification
      profile hConnected hGenus hValid hbAnchor hfS hfI with
      ⟨old, hoS, hoAt, hoSide, hoRel, rfl⟩ | ⟨old, hoS, hoAt, hoSide, hoRel, rfl⟩
    · rcases eq_of_survivor source pairing hNoGlue hRamification first second
        vertex hAt hNe hFirst hSecond hValency old hoS hoAt hoRel with rfl | rfl
      · exact absurd (hsE.symm.trans hoSide) (by simp)
      · exact absurd (hsF.symm.trans hoSide) (by simp)
    · rcases eq_of_survivor source pairing hNoGlue hRamification first second
        vertex hAt hNe hFirst hSecond hValency old hoS hoAt hoRel with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hJoin : NonDanglingEdge.stablePath
        (⟨(cand).newSourceEdge first.1.1.2, hNewSurvE⟩ :
          NonDanglingEdge (cand).datum) =
      NonDanglingEdge.stablePath
        (⟨(cand).newSourceEdge second.1.1.2, hNewSurvF⟩ :
          NonDanglingEdge (cand).datum) :=
    stablePath_eq_of_consecutive
      ⟨fun h ↦ hNeNew (congrArg Subtype.val h),
        endpointVertex source pairing hNoGlue hRamification profile hConnected
          hGenus hValid
          (retSide source pairing hNoGlue hRamification profile
            ((coarse).repr vertex.1.2)) vertex.1.2,
        hIncidA, hIncidB,
        nonDanglingValency_eq_two_of_pair source pairing hNoGlue hRamification
          profile hConnected hGenus hValid hNeNew hSubset
          ((mem_nonDanglingIncident _ _ _).mpr ⟨hNewSurvE, hIncidA⟩)
          ((mem_nonDanglingIncident _ _ _).mpr ⟨hNewSurvF, hIncidB⟩)⟩
  exact ((hRowE.symm.trans hJoin).trans hRowF)

/-! ## The descent, unconditionally -/

/-- **`OrdinaryBlockDescent` holds.**  The four cases above exhaust the
possibilities at a non-anchor wall block of surviving valency two. -/
theorem ordinaryBlockDescent :
    OrdinaryBlockDescent source pairing hNoGlue hRamification profile hConnected
      hGenus hValid := by
  classical
  intro first second vertex hAt hbAnchor hNe hFirst hSecond hValency
  by_cases hE : star.right pairing first.1.1.1 =
      retSide source pairing hNoGlue hRamification profile
        ((coarse).repr vertex.1.2)
  · by_cases hF : star.right pairing second.1.1.1 =
        retSide source pairing hNoGlue hRamification profile
          ((coarse).repr vertex.1.2)
    · exact descent_of_both_retaining source pairing hNoGlue hRamification
        profile hConnected hGenus hValid first second vertex hAt hNe hFirst
        hSecond hValency hbAnchor hE hF
    · exact descent_of_mixed source pairing hNoGlue hRamification profile
        hConnected hGenus hValid first second vertex hAt hNe hFirst hSecond
        hValency hbAnchor hE (bool_eq_not_of_ne hF)
  · by_cases hF : star.right pairing second.1.1.1 =
        retSide source pairing hNoGlue hRamification profile
          ((coarse).repr vertex.1.2)
    · exact (descent_of_mixed source pairing hNoGlue hRamification profile
        hConnected hGenus hValid second first vertex hAt hNe.symm hSecond hFirst
        hValency hbAnchor hF (bool_eq_not_of_ne hE)).symm
    · by_cases hRel : (blockRes ((coarse).repr vertex.1.2)).newEdge.Rel
          first.1.1.2 second.1.1.2
      · exact descent_of_both_fine_same source pairing hNoGlue hRamification
          profile hConnected hGenus hValid first second vertex hAt hNe hFirst
          hSecond hValency hbAnchor (bool_eq_not_of_ne hE)
          (bool_eq_not_of_ne hF) hRel
      · exact descent_of_both_fine_split source pairing hNoGlue hRamification
          profile hConnected hGenus hValid first second vertex hAt hNe hFirst
          hSecond hValency hbAnchor (bool_eq_not_of_ne hE)
          (bool_eq_not_of_ne hF) hRel

/-- **The retained-row map of the `K = 0` candidate, unconditionally.**  Every
stable row of the gauged wall datum descends to a stable row of the outgoing
candidate along the literal retained occurrences.  No geometric hypothesis
about the candidate is needed: the hypotheses are the standing binders of the
prescribed pairing. -/
noncomputable def retainedRow :
    StablePath (gauged) → StablePath (cand).datum :=
  NonTrivalentValencyFourDictionary.retainedRow source pairing hNoGlue
    hRamification profile hConnected hGenus hValid
    (ordinaryBlockDescent source pairing hNoGlue hRamification profile
      hConnected hGenus hValid)

@[simp] theorem retainedRow_mk (e : NonDanglingEdge (gauged)) :
    retainedRow source pairing hNoGlue hRamification profile hConnected hGenus
        hValid e.stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1
        e).stablePath := rfl

/-! ## Towards the row equivalence: the bridge row and the anchor block -/

theorem endpointForSide_not_smaller :
    endpointForSide source pairing hNoGlue hRamification
        (!smallerSide source pairing) =
      (gauged).vertexPartition wall :=
  ite_eq_right (by simp)

/-- **A surviving new occurrence over the anchor block is the bridge.**  Its
endpoint on the non-smaller side is the anchor's own endpoint vertex, whose
surviving star is the bridge together with two retained survivors. -/
theorem newSourceEdge_anchor_eq_bridge {s : Fin degree}
    (hs : ((gauged).vertexPartition wall).Rel anchor.1 s)
    (hSurv : ¬ IsDangling (cand).datum ((cand).newSourceEdge s)) :
    (cand).newSourceEdge s =
      bridgeEdge source pairing hNoGlue hRamification profile hConnected hGenus
        hValid (selectedRepresentative source pairing) := by
  classical
  have hRepRel : ((gauged).vertexPartition wall).Rel anchor.1
      (selectedRepresentative source pairing) :=
    (gauged_rel_iff source pairing hNoGlue hRamification _ _).mpr
      (source.sheet_wall_rel _)
  have hSide : (endpointForSide source pairing hNoGlue hRamification
      (!smallerSide source pairing)).Rel s
      (selectedRepresentative source pairing) := by
    rw [endpointForSide_not_smaller]
    exact hs.symm.trans hRepRel
  have hEq := endpointVertex_eq source pairing hNoGlue hRamification profile
    hConnected hGenus hValid (!smallerSide source pairing) hs hSide
  have hIncident := bridgeEdge_incident source pairing hNoGlue hRamification
    profile hConnected hGenus hValid (!smallerSide source pairing) s
  rw [hEq] at hIncident
  have hMem : (cand).newSourceEdge s ∈
      nonDanglingIncident (cand).datum
        (endpointVertex source pairing hNoGlue hRamification profile hConnected
          hGenus hValid (!smallerSide source pairing)
          (selectedRepresentative source pairing)) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨hSurv, hIncident⟩
  rw [nonDanglingIncident_endpointVertex source pairing hNoGlue hRamification
    profile hConnected hGenus hValid (!smallerSide source pairing)] at hMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
  rcases hMem with h | h | h
  · exact h
  · exact absurd h.symm (new_ne_old source pairing hNoGlue hRamification profile
      hConnected hGenus hValid s _)
  · exact absurd h.symm (new_ne_old source pairing hNoGlue hRamification profile
      hConnected hGenus hValid s _)

/-- **The bridge is not a retained row.**  Every occurrence of the bridge's
stable class is the bridge itself, which is a new occurrence. -/
theorem retainedRow_ne_bridgeRow (r : StablePath (gauged)) :
    retainedRow source pairing hNoGlue hRamification profile hConnected hGenus
        hValid r ≠
      NonDanglingEdge.stablePath
        (⟨bridgeEdge source pairing hNoGlue hRamification profile hConnected
            hGenus hValid (selectedRepresentative source pairing),
          bridgeEdge_survives source pairing hNoGlue hRamification profile
            hConnected hGenus hValid⟩ : NonDanglingEdge (cand).datum) := by
  obtain ⟨e, rfl⟩ := Quot.exists_rep r
  intro hBad
  exact new_ne_old source pairing hNoGlue hRamification profile hConnected
    hGenus hValid (selectedRepresentative source pairing) e.1
    (bridgeEdge_isolated source pairing hNoGlue hRamification profile hConnected
      hGenus hValid _ hBad)

/-- **Every stable row of the candidate is retained or carries a new
occurrence.**  This is the first step of surjectivity: what remains is the
non-anchor new occurrences, `newSourceEdge_anchor_eq_bridge` settling the
anchor ones. -/
theorem stablePath_cases (row : StablePath (cand).datum) :
    (∃ r : StablePath (gauged), row =
        retainedRow source pairing hNoGlue hRamification profile hConnected
          hGenus hValid r) ∨
      ∃ (s : Fin degree) (h : ¬ IsDangling (cand).datum ((cand).newSourceEdge s)),
        row = NonDanglingEdge.stablePath
          (⟨(cand).newSourceEdge s, h⟩ : NonDanglingEdge (cand).datum) := by
  obtain ⟨e, rfl⟩ := Quot.exists_rep row
  rcases ResolutionAwayFromWall.nonDanglingEdge_cases (cand)
    (gaugedData_valid source pairing hNoGlue hRamification hValid)
    (candidate_sourceGenus source pairing hNoGlue hRamification profile
      hConnected hGenus hValid) e with ⟨old, rfl⟩ | ⟨s, hs, rfl⟩
  · exact Or.inl ⟨old.stablePath, rfl⟩
  · exact Or.inr ⟨s, hs, rfl⟩

/-! ## The honest labelling of the candidate, from a labelling of the wall datum -/

section Labelling

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- A square honest labelling of the incoming wall datum transported across the
block-preserving sheet gauge.  The target is unchanged; the rows follow the
literal source-edge map of `SheetRelabelStable.stablePathEquiv`. -/
noncomputable def relabelLabelling
    (labelling₀ : StableLengthMatrixLabelling data coordinate) :
    StableLengthMatrixLabelling (gauged) coordinate where
  targetEdge := labelling₀.targetEdge
  row := (SheetRelabelStable.stablePathEquiv
    (relabeling source pairing hNoGlue hRamification) hValid.1).symm.trans
    labelling₀.row

omit [Fintype coordinate] [DecidableEq coordinate] in
@[simp] theorem relabelLabelling_row
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (path : StablePath (gauged)) :
    (relabelLabelling source pairing hNoGlue hRamification hValid
        labelling₀).row path =
      labelling₀.row ((SheetRelabelStable.stablePathEquiv
        (relabeling source pairing hNoGlue hRamification) hValid.1).symm path) :=
  rfl

omit [Fintype coordinate] [DecidableEq coordinate] in
@[simp] theorem relabelLabelling_targetEdge
    (labelling₀ : StableLengthMatrixLabelling data coordinate) (c : coordinate) :
    (relabelLabelling source pairing hNoGlue hRamification hValid
        labelling₀).targetEdge c = labelling₀.targetEdge c := rfl

/-- **The honest stable length-matrix labelling of the `K = 0` candidate**, over
`Option coordinate`: the wall datum's own square labelling supplies every
retained row and column, and `Option.none` is the vanishing coordinate of the
incoming chart, re-used for the new target edge and for the bridge row. -/
noncomputable def candidateLabelling
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath (gauged))) :
    StableLengthMatrixLabelling (cand).datum (Option coordinate) :=
  NonTrivalentValencyFourDictionary.labelling source pairing hNoGlue
    hRamification profile hConnected hGenus hValid
    (relabelLabelling source pairing hNoGlue hRamification hValid labelling₀)
    rowEquiv

@[simp] theorem candidateLabelling_targetEdge_none
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath (gauged))) :
    (candidateLabelling source pairing hNoGlue hRamification profile hConnected
      hGenus hValid labelling₀ rowEquiv).targetEdge none =
      occurrenceEquiv target wall (cand).right none := rfl

@[simp] theorem candidateLabelling_targetEdge_some
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath (gauged)))
    (c : coordinate) :
    (candidateLabelling source pairing hNoGlue hRamification profile hConnected
      hGenus hValid labelling₀ rowEquiv).targetEdge (some c) =
      occurrenceEquiv target wall (cand).right
        (some (labelling₀.targetEdge c)) := rfl

theorem candidateLabelling_row
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath (gauged)))
    (path : StablePath (cand).datum) :
    (candidateLabelling source pairing hNoGlue hRamification profile hConnected
        hGenus hValid labelling₀ rowEquiv).row path =
      (rowEquiv path).map
        (relabelLabelling source pairing hNoGlue hRamification hValid
          labelling₀).row :=
  NonTrivalentValencyFourDictionary.labelling_row source pairing hNoGlue
    hRamification profile hConnected hGenus hValid _ rowEquiv path

end Labelling

/-! ## The candidate's matrix off the new column -/

theorem retainedRow_injective
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath (gauged)))
    (hRowRetained : ∀ r, rowEquiv (retainedRow source pairing hNoGlue
      hRamification profile hConnected hGenus hValid r) = some r) :
    Function.Injective (retainedRow source pairing hNoGlue hRamification profile
      hConnected hGenus hValid) := by
  intro r r' hEq
  have h := congrArg (fun p ↦ rowEquiv p) hEq
  simp only [hRowRetained] at h
  exact Option.some.inj h

/-- **The surviving occurrences of a retained row over an old target
occurrence** are exactly the retained copies of the surviving occurrences of
that row of the wall datum. -/
theorem occurrences_retainedRow
    (hInj : Function.Injective (retainedRow source pairing hNoGlue hRamification
      profile hConnected hGenus hValid))
    (r : StablePath (gauged)) (e : target.edges) :
    StableSourceMatrix.occurrences (cand).datum
        (retainedRow source pairing hNoGlue hRamification profile hConnected
          hGenus hValid r)
        (occurrenceEquiv target wall (cand).right (some e)) =
      (StableSourceMatrix.occurrences (gauged) r e).image
        (cand).oldSourceEdge := by
  classical
  ext f
  rw [StableSourceMatrix.mem_occurrences]
  constructor
  · rintro ⟨⟨hSurv, hRow⟩, hTarget⟩
    rcases ResolutionPruning.sourceEdge_cases (cand) f with ⟨old, rfl⟩ | ⟨s, rfl⟩
    · have hOldSurv : ¬ IsDangling (gauged) old := fun h ↦ hSurv
        ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand)
          (gaugedData_valid source pairing hNoGlue hRamification hValid)
          (candidate_sourceGenus source pairing hNoGlue hRamification profile
            hConnected hGenus hValid) old).mpr h)
      have hOcc : occurrenceEquiv target wall (cand).right (some old.1.1) =
          occurrenceEquiv target wall (cand).right (some e) := hTarget
      have hTargetEq : old.1.1 = e :=
        Option.some.inj ((occurrenceEquiv target wall (cand).right).injective hOcc)
      refine Finset.mem_image.mpr ⟨old, ?_, rfl⟩
      rw [StableSourceMatrix.mem_occurrences]
      exact ⟨⟨hOldSurv, hInj ((retainedRow_mk source pairing hNoGlue hRamification
        profile hConnected hGenus hValid ⟨old, hOldSurv⟩).trans hRow)⟩, hTargetEq⟩
    · exfalso
      have hOcc : occurrenceEquiv target wall (cand).right none =
          occurrenceEquiv target wall (cand).right (some e) := hTarget
      have := (occurrenceEquiv target wall (cand).right).injective hOcc
      cases this
  · intro hMem
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hMem
    rw [StableSourceMatrix.mem_occurrences] at hg
    obtain ⟨⟨hgS, hgRow⟩, hgTarget⟩ := hg
    refine ⟨⟨ResolutionSurvival.not_isDangling_oldSourceEdge _
      (gaugedData_valid source pairing hNoGlue hRamification hValid).1 _ hgS, ?_⟩, ?_⟩
    · exact (retainedRow_mk source pairing hNoGlue hRamification profile
        hConnected hGenus hValid ⟨g, hgS⟩).symm.trans
        (congrArg (retainedRow source pairing hNoGlue hRamification profile
          hConnected hGenus hValid) hgRow)
    · show occurrenceEquiv target wall (cand).right (some g.1.1) =
        occurrenceEquiv target wall (cand).right (some e)
      rw [hgTarget]

/-- **The candidate's natural matrix in a retained row and an old column is the
wall datum's.** -/
theorem matrix_retainedRow
    (hInj : Function.Injective (retainedRow source pairing hNoGlue hRamification
      profile hConnected hGenus hValid))
    (r : StablePath (gauged)) (e : target.edges) :
    StableSourceMatrix.matrix (cand).datum
        (retainedRow source pairing hNoGlue hRamification profile hConnected
          hGenus hValid r)
        (occurrenceEquiv target wall (cand).right (some e)) =
      StableSourceMatrix.matrix (gauged) r e := by
  classical
  unfold StableSourceMatrix.matrix
  rw [occurrences_retainedRow source pairing hNoGlue hRamification profile
    hConnected hGenus hValid hInj r e,
    Finset.sum_image (fun _ _ _ _ h ↦
      ResolutionCut.oldSourceEdge_injective (cand) h)]
  exact Finset.sum_congr rfl fun g _ ↦ by
    rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]

section MatrixLabelling

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The candidate's honest matrix agrees with the wall datum's off the new
column.**  In the `Option coordinate` indexing, the entry of the candidate in
the retained row `some (labelling₀.row p)` and the retained column `some c` is
the wall datum's entry in row `labelling₀.row p` and column `c`.  Together with
`StablePathFacetContraction.matrix_wallLabelling` this is the common minor
`A_{φ₀}` of Part II `lm:change-comb-type`. -/
theorem matrix_candidateLabelling
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath (gauged)))
    (hRowRetained : ∀ r, rowEquiv (retainedRow source pairing hNoGlue
      hRamification profile hConnected hGenus hValid r) = some r)
    (p : StablePath data) (c : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (candidateLabelling source pairing hNoGlue hRamification profile
          hConnected hGenus hValid labelling₀ rowEquiv).presentation
        (some (labelling₀.row p)) (some c) =
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row p) c := by
  classical
  have hInj := retainedRow_injective source pairing hNoGlue hRamification profile
    hConnected hGenus hValid rowEquiv hRowRetained
  have hRowSymm : (candidateLabelling source pairing hNoGlue hRamification
        profile hConnected hGenus hValid labelling₀ rowEquiv).row.symm
        (some (labelling₀.row p)) =
      retainedRow source pairing hNoGlue hRamification profile hConnected hGenus
        hValid (SheetRelabelStable.stablePathEquiv
          (relabeling source pairing hNoGlue hRamification) hValid.1 p) := by
    rw [Equiv.symm_apply_eq, candidateLabelling_row]
    rw [show rowEquiv (retainedRow source pairing hNoGlue hRamification profile
        hConnected hGenus hValid (SheetRelabelStable.stablePathEquiv
          (relabeling source pairing hNoGlue hRamification) hValid.1 p)) =
        some (SheetRelabelStable.stablePathEquiv
          (relabeling source pairing hNoGlue hRamification) hValid.1 p) from
      hRowRetained _]
    exact congrArg (fun x ↦ some (labelling₀.row x))
      ((SheetRelabelStable.stablePathEquiv
        (relabeling source pairing hNoGlue hRamification)
        hValid.1).symm_apply_apply p).symm
  rw [StableSourceMatrix.labelling_matrix_eq, StableSourceMatrix.labelling_matrix_eq,
    hRowSymm, candidateLabelling_targetEdge_some, Equiv.symm_apply_apply]
  exact (matrix_retainedRow source pairing hNoGlue hRamification profile
      hConnected hGenus hValid hInj
      (SheetRelabelStable.stablePathEquiv
        (relabeling source pairing hNoGlue hRamification) hValid.1 p)
      (labelling₀.targetEdge c)).trans
    (SheetRelabelStable.matrix_map
      (relabeling source pairing hNoGlue hRamification) hValid.1 p
      (labelling₀.targetEdge c))

end MatrixLabelling

/-! ## Re-indexing the `Option` coordinate onto the incoming chart -/

section Reindex

/-- Transport a square honest labelling along an equivalence of index sets. -/
def reindexLabelling {targetX : CFGraph} {deg : ℕ}
    {datum : GluingDatum targetX deg} {A B : Type*} (e : A ≃ B)
    (labelling : StableLengthMatrixLabelling datum A) :
    StableLengthMatrixLabelling datum B where
  targetEdge := e.symm.trans labelling.targetEdge
  row := labelling.row.trans e

@[simp] theorem reindexLabelling_row {targetX : CFGraph} {deg : ℕ}
    {datum : GluingDatum targetX deg} {A B : Type*} (e : A ≃ B)
    (labelling : StableLengthMatrixLabelling datum A)
    (path : StablePath datum) :
    (reindexLabelling e labelling).row path = e (labelling.row path) := rfl

@[simp] theorem reindexLabelling_targetEdge {targetX : CFGraph} {deg : ℕ}
    {datum : GluingDatum targetX deg} {A B : Type*} (e : A ≃ B)
    (labelling : StableLengthMatrixLabelling datum A) (b : B) :
    (reindexLabelling e labelling).targetEdge b =
      labelling.targetEdge (e.symm b) := rfl

theorem matrix_reindexLabelling {targetX : CFGraph} {deg : ℕ}
    {datum : GluingDatum targetX deg} {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ≃ B)
    (labelling : StableLengthMatrixLabelling datum A) (row column : A) :
    GluingDatum.LengthMatrixPresentation.matrix
        (reindexLabelling e labelling).presentation (e row) (e column) =
      GluingDatum.LengthMatrixPresentation.matrix labelling.presentation row
        column := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq, StableSourceMatrix.labelling_matrix_eq,
    reindexLabelling_targetEdge, Equiv.symm_apply_apply]
  congr 1
  rw [Equiv.symm_apply_eq, reindexLabelling_row, Equiv.apply_symm_apply]

end Reindex

section ActualChart

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The outgoing chart, indexed by the incoming one.**  The candidate's honest
labelling over `Option coordinate₀` is re-indexed along any equivalence
`Option coordinate₀ ≃ coordinate`; taking `coordinate₀` to be the incoming
coordinates with the contracted column removed and the equivalence
`Equiv.optionSubtypeNe`, the outgoing matrix is indexed by the incoming chart
with `Option.none` sitting in the contracted column. -/
noncomputable def chartLabelling {coordinate₀ : Type*} [Fintype coordinate₀]
    [DecidableEq coordinate₀]
    (labelling₀ : StableLengthMatrixLabelling data coordinate₀)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath (gauged)))
    (chart : Option coordinate₀ ≃ coordinate) :
    StableLengthMatrixLabelling (cand).datum coordinate :=
  reindexLabelling chart
    (candidateLabelling source pairing hNoGlue hRamification profile hConnected
      hGenus hValid labelling₀ rowEquiv)

/-- **The `AgreeOffColumn`-shaped identity, entry by entry.**  In the incoming
chart, the outgoing matrix entry in the row of a retained stable row of the wall
datum and in a retained column is the wall datum's own entry.  Composing with
`StablePathFacetContraction.matrix_wallLabelling` (which identifies the wall
datum's entries with the incoming full-dimensional cover's off the contracted
column) gives the common minor `A_{φ₀}` of Part II `lm:change-comb-type`. -/
theorem matrix_chartLabelling {coordinate₀ : Type*} [Fintype coordinate₀]
    [DecidableEq coordinate₀]
    (labelling₀ : StableLengthMatrixLabelling data coordinate₀)
    (rowEquiv : StablePath (cand).datum ≃ Option (StablePath (gauged)))
    (hRowRetained : ∀ r, rowEquiv (retainedRow source pairing hNoGlue
      hRamification profile hConnected hGenus hValid r) = some r)
    (chart : Option coordinate₀ ≃ coordinate)
    (p : StablePath data) (c : coordinate₀) :
    GluingDatum.LengthMatrixPresentation.matrix
        (chartLabelling source pairing hNoGlue hRamification profile hConnected
          hGenus hValid labelling₀ rowEquiv chart).presentation
        (chart (some (labelling₀.row p))) (chart (some c)) =
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row p) c :=
  (matrix_reindexLabelling chart
    (candidateLabelling source pairing hNoGlue hRamification profile hConnected
      hGenus hValid labelling₀ rowEquiv) _ _).trans
    (matrix_candidateLabelling source pairing hNoGlue hRamification profile
      hConnected hGenus hValid labelling₀ rowEquiv hRowRetained p c)

end ActualChart

/-! ## At an actual four-valent wall, with no census supplied -/

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

/-- **The non-anchor descent at an actual four-valent wall.**  The hypotheses
are exactly those of
`NonTrivalentUniqueFourValent.exists_valid_candidate_of_single_row`: an incoming
full-dimensional cover, the actual contraction forest, the wall metric with a
single vanishing stable row, and the anchor's `nd = 4`.  No census, background,
injectivity or trivalence receipt is supplied. -/
theorem ordinaryBlockDescent_of_single_row :
    OrdinaryBlockDescent
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
      (NonTrivalentUniqueFourValent.wall_valid cover fd hc hab hOne hForest) :=
  ordinaryBlockDescent _ pairing _ _ _ _ _ _

/-- **The retained-row map at an actual four-valent wall**, with no receipt:
every stable row of the gauged wall datum descends to a stable row of the
outgoing `K = 0` candidate. -/
noncomputable def retainedRow_of_single_row :
    StablePath (gaugedData
        (NonTrivalentUniqueFourValent.wallFourBranchAnchor cover fd hc hab hOne
          wallStar hForest anchorBlock hAnchor) pairing
        (NonTrivalentUniqueFourValent.wall_noGlue cover fd hc hab hOne hForest)
        (NonTrivalentUniqueFourValent.wall_ramification cover fd hc hab hOne
          wallStar hForest anchorBlock)) →
      StablePath (NonTrivalentValencyFourBackground.candidate
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
          hForest)).datum :=
  retainedRow _ pairing _ _ _ _ _ _

end ActualWall

/-! ## The common minor: the outgoing matrix against the incoming one -/

section AgreeOffColumn

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.WallDegeneration

variable {targetIn : CFGraph} {deg : ℕ} {chartIndex : Type*} [Fintype chartIndex]
  [DecidableEq chartIndex]
  (cover : GluingDatum targetIn deg)
  (fd : FullDimensionalSourcePresentation cover chartIndex)
  {a b : targetIn.V} {contracted : targetIn.edges}
  (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges targetIn a b = 1)
  (hCompat : DanglingCompatible cover hc hab hOne)
  (hForest : ContractionForest cover a b contracted)
  (hNoReturn : NoContractedReturn cover contracted)
  (coordinates : chartIndex → ℚ) (facet : chartIndex)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)
  {wallStar : W4TargetPairings.FourStar (contract targetIn hab hOne) ⟨a, hab⟩}
  {anchorBlk : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩}
  (src : FourBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (pairing : Fin 3)
  (hNoGlue : DanglingEdgeNoGlue (contractDatum cover hc hab hOne))
  (hRamification : (contractDatum cover hc hab hOne).localRamification ⟨a, hab⟩
    anchorBlk = 0)
  (prof : OrdinaryBlockProfile (contractDatum cover hc hab hOne) wallStar
    anchorBlk.1)
  (hConn : graph_connected (contract targetIn hab hOne))
  (hGen : genus (contract targetIn hab hOne) = 0)
  (hVal : (contractDatum cover hc hab hOne).Valid)

/-- **The outgoing honest matrix equals the incoming one off the contracted
column**, entry by entry, once the row dictionary of the candidate is supplied.
Rows correspond through `retainedRow` on the outgoing side and
`StablePathFacetContraction.incomingRow` on the incoming side; columns through
the chart equivalence, which puts `Option.none` -- the new target occurrence and
the bridge row -- in the contracted column.  This is the common minor
`A_{φ₀}` of Part II, `lm:change-comb-type` (Section 5.1).

The only hypothesis about the candidate is `hRowRetained`: that the
supplied row equivalence sends each retained row to its wall row. -/
theorem matrix_chartLabelling_eq_incoming
    (rowEquiv : StablePath (NonTrivalentValencyFourBackground.candidate src
        pairing hNoGlue hRamification prof hConn hGen hVal).datum ≃
      Option (StablePath (gaugedData src pairing hNoGlue hRamification)))
    (hRowRetained : ∀ r, rowEquiv (retainedRow src pairing hNoGlue hRamification
      prof hConn hGen hVal r) = some r)
    (chart : Option {column : chartIndex //
        column ≠ fd.labelling.targetEdge.symm contracted} ≃ chartIndex)
    (p : StablePath (contractDatum cover hc hab hOne))
    (column : {column : chartIndex //
      column ≠ fd.labelling.targetEdge.symm contracted}) :
    GluingDatum.LengthMatrixPresentation.matrix
        (chartLabelling src pairing hNoGlue hRamification prof hConn hGen hVal
          (wallLabelling cover fd hc hab hOne hCompat hForest hNoReturn
            coordinates facet hRows hZeroCoord hPosCoord hFacetZero)
          rowEquiv chart).presentation
        (chart (some (wallRowIndex cover fd hc hab hOne hCompat hForest hNoReturn
          coordinates facet hRows hZeroCoord hPosCoord hFacetZero p)))
        (chart (some column)) =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
        (fd.labelling.row (incomingRow cover fd hc hab hOne hCompat hForest p))
        column.1 :=
  (matrix_chartLabelling src pairing hNoGlue hRamification prof hConn hGen hVal
    (wallLabelling cover fd hc hab hOne hCompat hForest hNoReturn coordinates
      facet hRows hZeroCoord hPosCoord hFacetZero) rowEquiv hRowRetained chart p
    column).trans
    (matrix_wallLabelling cover fd hc hab hOne hCompat hForest hNoReturn
      coordinates facet hRows hZeroCoord hPosCoord hFacetZero p column)

end AgreeOffColumn

end DraismaVargas.LocalCases.NonTrivalentValencyFourRowDictionary
