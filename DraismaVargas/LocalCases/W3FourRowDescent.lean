import DraismaVargas.LocalCases.W3FourSurvival
import DraismaVargas.LocalCases.LimitChainCore

/-!
# Stable lift, row descent and the retained columns of Figure 28's four members

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{w3-r1-nd3-t2-(a=k₄)}`, its Figure 28 and Equation (2), and the
induced-labelling / limit-matrix argument of Section 5 (Lemma
`lemma-limit-matrix-change`).

`W3FourSurvival` settles, for each of the four outgoing members, which
occurrences survive, the complete surviving star at each new endpoint, and the
stable row of each surviving new occurrence.  The identification of the stable
rows themselves — the stable lift, the explicit geometric row descent, the
occurrence-induced equivalence `stablePathEquiv`, the retained columns
`matrix_retained`, the support `mem_occurrences_new_iff` of the regrown column,
and the stable incidence graph `equivalence` — is the generic chain
`LimitChainCore`, stated there once for an arbitrary `GraphData`.  This module
instantiates it four times:

* `coreShape` reads a `W3FourSurvival.BackgroundShape` as the core's
  `BackgroundShape`: the fine-star receipt `resolution_eq` supplies the three
  block identities the core asks for;
* `PositionOne.rowData`, `PositionTwo.rowData` and `GrowMember.rowData` — the
  last covering `M⁽³⁾` and `M⁽⁴⁾` at once through an arbitrary
  `GrowProfile` — package each member's selected-star census as a
  `LimitChainCore.GraphData`, and the named forms `PositionOne.stablePathEquiv`
  / `matrix_retained` / `equivalence` and their `PositionTwo` and `GrowMember`
  counterparts are the core's, read on the member's own candidate.

## Why this is cheap

Two structural facts do the work.

* **The census does not cross the branch swap.**  There is no Position I or
  Position II.b member over `data` at all
  (`W3FourSourceCandidates.exists_sheet_outside_iff_not_disjoint`), so nothing
  is transported member to member.  Everything is stated once over
  `W3FourClosure.FourStarGeometry` together with
  `W3FourSurvival.SelectedSurvival`, and instantiated.
* **The distinguished source vertex is a branch vertex.**  Its three
  survivors `e₂`, `e₃`, `e₄` are distinct occurrences, so
  `selected_nonDanglingValency_eq_three` holds and **no consecutive pair of
  the incoming stable quotient meets it**: this is the core's
  `selected_valency_ne_two`.  Downstairs the same simplification recurs, at
  the divalent endpoint for `M⁽¹⁾`
  (`PositionOne.old_nonDanglingValency_eq_three`) and at the trivalent endpoint
  for `M⁽²⁾`, `M⁽³⁾`, `M⁽⁴⁾`
  (`PositionTwo.fresh_grow_nonDanglingValency_eq_three`,
  `GrowMember.fresh_nonDanglingValency_eq_three`).

The background half is the core's `Background.replace`, at arbitrary old
valency and with no ramification receipt; `Background.background_retained_eq_of_consecutive`
below is that statement read on a `W3FourSurvival.BackgroundShape`, which is
the form `W3Nd3LimitMatrix` consumes.

## Discipline

Every endpoint statement is an identity of **occurrence** sets, never of
stable-row labels; nothing below asks the rows of `e₂`, `e₃`, `e₄` to be
distinct, so a stable loop through a branch vertex is not excluded.  No
hypothesis beyond `FourStarGeometry`, `SelectedSurvival` and `data.Valid` is
added to any statement.
-/

namespace DraismaVargas.LocalCases.W3FourRowDescent

open DraismaVargas.Infrastructure
open TargetExpansion
open BalancedGlobal
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open ResolutionCoarseFine ResolutionM11
open ResolutionAwayFromWall StableSourceMatrix StablePathCount
open W3FourClosure (FourStarGeometry ofGrowProfile)
open W3FourSurvival
open LimitChainCore (GraphData wallSide wallSide_false wallSide_true)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## A four-star background shape is a core background shape -/

namespace Background

/-- Off the distinguished block the trivalent endpoint carries the whole wall
block. -/
theorem pasted_right_block (shape : BackgroundShape data wall) {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet) :
    shape.pasted.right.block sheet = (data.vertexPartition wall).block sheet := by
  change (LocalResolution.pasteRight (data.vertexPartition wall)
    shape.candidate.resolution shape.candidate.contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [(data.vertexPartition wall).paste_block]
  rw [shape.resolution_eq ((data.vertexPartition wall).repr sheet) (fun hRel ↦
    hSheet (hRel.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

end Background

/-- A `W3FourSurvival.BackgroundShape`, read as the core's: the fine-star
receipt `resolution_eq` gives the three block identities the core records. -/
noncomputable def coreShape (shape : BackgroundShape data wall) :
    LimitChainCore.BackgroundShape data wall where
  candidate := shape.candidate
  retainedTarget := shape.backgroundTarget
  target_mem := shape.target_mem
  left := shape.left
  unique := fun edge _ hRight ↦ shape.unique edge hRight
  selected := shape.selected
  left_block := fun hSheet ↦ shape.pasted_left_block hSheet
  right_block := fun hSheet ↦ Background.pasted_right_block shape hSheet
  newEdge_block := fun hSheet ↦ shape.pasted_newEdge_block hSheet
  genus_eq := shape.genus_eq

@[simp] theorem coreShape_candidate (shape : BackgroundShape data wall) :
    (coreShape shape).candidate = shape.candidate := rfl

@[simp] theorem coreShape_selected (shape : BackgroundShape data wall) :
    (coreShape shape).selected = shape.selected := rfl

namespace Background

/-- **The background half of the lift's well-definedness**, read on a
`W3FourSurvival.BackgroundShape`: a consecutive pair of the incoming stable
quotient meeting a background wall vertex keeps one outgoing row, at arbitrary
old valency and with no ramification receipt.  This is
`LimitChainCore.Background.background_retained_eq_of_consecutive`, in the form
`W3Nd3LimitMatrix` consumes. -/
theorem background_retained_eq_of_consecutive (shape : BackgroundShape data wall)
    (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet)
    (first second : NonDanglingEdge data) (hNe : first ≠ second)
    (hFirst : Incident data first.1 (data.sourceEndpoint wall sheet))
    (hSecond : Incident data second.1 (data.sourceEndpoint wall sheet))
    (hValency : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2) :
    (retainedEdge shape.candidate hValid.1 first).stablePath =
      (retainedEdge shape.candidate hValid.1 second).stablePath :=
  LimitChainCore.Background.background_retained_eq_of_consecutive (coreShape shape)
    hValid hSheet first second hNe hFirst hSecond hValency

end Background


/-! ## The distinguished source vertex is a branch vertex

`Consecutive` demands surviving valency two at the joining vertex, and the
incoming distinguished vertex has surviving valency three.  So no consecutive
pair of the incoming stable quotient meets it, which is the core's
`selected_valency_ne_two`. -/

section Selected

variable (geometry : FourStarGeometry data wall)

/-- The complete surviving star at the distinguished source vertex: `e₂`, `e₃`
and `e₄`, and nothing else. -/
theorem selected_nonDanglingIncident
    (survival : SelectedSurvival data wall geometry) :
    nonDanglingIncident data (data.sourceEndpoint wall geometry.growAnchor) =
      {data.sourceEdge geometry.growTarget geometry.growAnchor,
        data.sourceEdge geometry.otherTarget geometry.otherAnchor,
        data.sourceEdge geometry.largestTarget geometry.largestAnchor} := by
  classical
  apply Finset.Subset.antisymm
  · intro edge hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases survival.exhaustive edge hIncident hSurvives with hGrow | hOther | hLargest
    · exact Finset.mem_insert.mpr (Or.inl hGrow)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hOther))
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hLargest))
  · intro edge hMem
    rcases Finset.mem_insert.mp hMem with rfl | hRest
    · exact (mem_nonDanglingIncident _ _ _).mpr ⟨survival.grow_survives,
        incident_sourceEdge_sourceEndpoint data wall geometry.growTarget
          geometry.growTarget_mem geometry.growAnchor⟩
    · rcases Finset.mem_insert.mp hRest with rfl | hLargest
      · refine (mem_nonDanglingIncident _ _ _).mpr ⟨survival.other_survives, ?_⟩
        rw [LimitChainCore.sourceEndpoint_eq_of_rel data wall geometry.other_wall_rel]
        exact incident_sourceEdge_sourceEndpoint data wall geometry.otherTarget
          geometry.otherTarget_mem geometry.otherAnchor
      · rw [Finset.mem_singleton.mp hLargest]
        refine (mem_nonDanglingIncident _ _ _).mpr ⟨survival.largest_survives, ?_⟩
        rw [LimitChainCore.sourceEndpoint_eq_of_rel data wall geometry.largest_wall_rel]
        exact incident_sourceEdge_sourceEndpoint data wall geometry.largestTarget
          geometry.largestTarget_mem geometry.largestAnchor

/-- **The distinguished source vertex is trivalent.** -/
theorem selected_nonDanglingValency_eq_three
    (survival : SelectedSurvival data wall geometry) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel geometry.growAnchor sheet) :
    nonDanglingValency data (data.sourceEndpoint wall sheet) = 3 := by
  classical
  rw [← LimitChainCore.sourceEndpoint_eq_of_rel data wall hSheet,
    ← card_nonDanglingIncident, selected_nonDanglingIncident geometry survival]
  rw [Finset.card_insert_of_notMem (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨sourceEdge_ne_of_target_ne data geometry.grow_ne_other _ _,
      sourceEdge_ne_of_target_ne data geometry.grow_ne_largest _ _⟩),
    Finset.card_pair
      (sourceEdge_ne_of_target_ne data geometry.other_ne_largest _ _)]

/-- Hence no consecutive pair of the incoming stable quotient meets it. -/
theorem selected_nonDanglingValency_ne_two
    (survival : SelectedSurvival data wall geometry) :
    nonDanglingValency data (data.sourceEndpoint wall geometry.growAnchor) ≠ 2 := by
  rw [selected_nonDanglingValency_eq_three geometry survival
    (sheet := geometry.growAnchor) rfl]
  decide

end Selected

/-! ## The four members, packaged for the core

All four members share the background shape and differ only in what the
distinguished block's endpoints carry.  Each `rowData` below is a
`LimitChainCore.GraphData`: the old representative of a selected new
occurrence, the surviving star at whichever of the two selected endpoints has
surviving valency two (the other is a branch vertex or entirely pruned in every
member, so its clause is vacuous), and the flag dictionary at the branch
vertex. -/


/-! ## Figure 28's `M⁽³⁾` and `M⁽⁴⁾`: the grow members

Position II.a puts the refinement at the **divalent** endpoint, so the row
identification happens there and the trivalent endpoint is the branch vertex.
Every selected divalent endpoint other than the enlarged class's own is
entirely pruned, so its clause is vacuous as well. -/

namespace GrowMember

variable {star : ThreeStar target wall} {input : W3SourceInput data star}

/-- A grow member's branch flag: the enlarged new occurrence replaces `e₂`,
and `e₃`, `e₄` are retained. -/
noncomputable def flag (grown : W3FourSourceCandidates.GrowProfile input)
    (edge : data.SourceEdge) : grown.growCandidate.datum.SourceEdge :=
  if edge.1.1 = grown.growTarget then
    grown.growCandidate.newSourceEdge grown.growAnchor
  else grown.growCandidate.oldSourceEdge edge

theorem flag_grow (grown : W3FourSourceCandidates.GrowProfile input) :
    flag grown (data.sourceEdge grown.growTarget grown.growAnchor) =
      grown.growCandidate.newSourceEdge grown.growAnchor := if_pos rfl

theorem flag_of_ne (grown : W3FourSourceCandidates.GrowProfile input)
    {edge : data.SourceEdge} (hTarget : edge.1.1 ≠ grown.growTarget) :
    flag grown edge = grown.growCandidate.oldSourceEdge edge := if_neg hTarget

theorem flag_star (grown : W3FourSourceCandidates.GrowProfile input)
    (survival : SelectedSurvival data wall (ofGrowProfile grown))
    (hValid : data.Valid) :
    nonDanglingIncident grown.growCandidate.datum
        (grown.growCandidate.datum.sourceEndpoint (freshVertex target)
          grown.growAnchor) =
      (nonDanglingIncident data
        (data.sourceEndpoint wall grown.growAnchor)).image (flag grown) := by
  classical
  have hIncoming : nonDanglingIncident data
      (data.sourceEndpoint wall grown.growAnchor) =
      {data.sourceEdge grown.growTarget grown.growAnchor,
        data.sourceEdge grown.otherTarget grown.otherAnchor,
        data.sourceEdge grown.largestTarget grown.largestAnchor} :=
    selected_nonDanglingIncident (ofGrowProfile grown) survival
  rw [W3FourSurvival.GrowMember.nonDanglingIncident_fresh grown survival hValid,
    hIncoming,
    Finset.image_insert, Finset.image_insert, Finset.image_singleton,
    flag_grow grown,
    flag_of_ne grown (edge := data.sourceEdge grown.otherTarget grown.otherAnchor)
      (Ne.symm grown.grow_target_ne_other),
    flag_of_ne grown
      (edge := data.sourceEdge grown.largestTarget grown.largestAnchor)
      (Ne.symm grown.grow_target_ne_largest)]

theorem flag_injOn (grown : W3FourSourceCandidates.GrowProfile input)
    (survival : SelectedSurvival data wall (ofGrowProfile grown))
    (hValid : data.Valid) :
    Set.InjOn (flag grown)
      ↑(nonDanglingIncident data (data.sourceEndpoint wall grown.growAnchor)) := by
  classical
  apply Finset.injOn_of_card_image_eq
  rw [← flag_star grown survival hValid, card_nonDanglingIncident,
    card_nonDanglingIncident,
    W3FourSurvival.GrowMember.fresh_nonDanglingValency_eq_three grown survival
      hValid,
    selected_nonDanglingValency_eq_three (ofGrowProfile grown) survival
      (sheet := grown.growAnchor) rfl]

theorem flag_row (grown : W3FourSourceCandidates.GrowProfile input)
    (survival : SelectedSurvival data wall (ofGrowProfile grown))
    (hValid : data.Valid) (edge : data.SourceEdge)
    (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (data.sourceEndpoint wall grown.growAnchor))
    (hFlag : ¬ IsDangling grown.growCandidate.datum (flag grown edge)) :
    NonDanglingEdge.stablePath
        (⟨flag grown edge, hFlag⟩ :
          NonDanglingEdge grown.growCandidate.datum) =
      (retainedEdge grown.growCandidate hValid.1 ⟨edge, hSurvives⟩).stablePath := by
  rcases survival.exhaustive edge hIncident hSurvives with rfl | rfl | rfl
  · refine Eq.trans (congrArg NonDanglingEdge.stablePath
      (show (⟨flag grown (data.sourceEdge grown.growTarget grown.growAnchor),
            hFlag⟩ : NonDanglingEdge grown.growCandidate.datum) =
          ⟨grown.growCandidate.newSourceEdge grown.growAnchor,
            W3FourSurvival.GrowMember.new_grow_survives grown survival hValid⟩
        from Subtype.ext (flag_grow grown))) ?_
    exact W3FourSurvival.GrowMember.new_grow_stablePath grown survival hValid
  · exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (flag_of_ne grown (Ne.symm grown.grow_target_ne_other)))
  · exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (flag_of_ne grown (Ne.symm grown.grow_target_ne_largest)))

/-- A grow member, packaged for the core.  `M⁽³⁾` and `M⁽⁴⁾` are the
two `GrowProfile`s of the case, so both are covered at once. -/
noncomputable def rowData (grown : W3FourSourceCandidates.GrowProfile input)
    (survival : SelectedSurvival data wall (ofGrowProfile grown))
    (hValid : data.Valid) : GraphData data wall where
  toBackgroundShape := coreShape (W3FourSurvival.GrowMember.toBackgroundShape grown)
  valid := hValid
  selected_valency_ne_two :=
    selected_nonDanglingValency_ne_two (ofGrowProfile grown) survival
  selectedRep := fun _ ↦ data.sourceEdge grown.growTarget grown.growAnchor
  selectedRep_survives := fun _ _ ↦ survival.grow_survives
  selectedRep_congr := fun _ _ _ _ _ ↦ rfl
  selected_new_stablePath := by
    intro sheet hSheet hSurvives _
    have hGrowRel : grown.growPartition.Rel sheet grown.growAnchor := by
      by_contra hSep
      exact hSurvives (W3FourSurvival.GrowMember.new_dangles_of_separate grown
        survival hValid hSheet hSep)
    have hEqual : grown.growCandidate.newSourceEdge sheet =
        grown.growCandidate.newSourceEdge grown.growAnchor :=
      W3FourSurvival.GrowMember.newSourceEdge_eq_of_rel grown rfl hGrowRel.symm
    refine Eq.trans (congrArg NonDanglingEdge.stablePath
      (show (⟨grown.growCandidate.newSourceEdge sheet, hSurvives⟩ :
            NonDanglingEdge grown.growCandidate.datum) =
          ⟨grown.growCandidate.newSourceEdge grown.growAnchor,
            W3FourSurvival.GrowMember.new_grow_survives grown survival hValid⟩
        from Subtype.ext hEqual)) ?_
    exact W3FourSurvival.GrowMember.new_grow_stablePath grown survival hValid
  selected_left_pair := by
    intro sheet hSheet hValency
    have hValencyLeft : nonDanglingValency grown.growCandidate.datum
        (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall) sheet) =
        2 := hValency
    by_cases hGrowRel : grown.growPartition.Rel sheet grown.growAnchor
    · refine ⟨grown.growAnchor, rfl, ?_⟩
      show nonDanglingIncident grown.growCandidate.datum
          (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall)
            sheet) =
        {grown.growCandidate.newSourceEdge grown.growAnchor,
          grown.growCandidate.oldSourceEdge
            (data.sourceEdge grown.growTarget grown.growAnchor)}
      rw [W3FourSurvival.GrowMember.old_endpoint_eq grown hSheet hGrowRel]
      exact W3FourSurvival.GrowMember.nonDanglingIncident_old_grow grown survival
        hValid
    · exfalso
      rw [← card_nonDanglingIncident,
        W3FourSurvival.GrowMember.nonDanglingIncident_old_separate grown survival
          hValid hSheet hGrowRel, Finset.card_empty] at hValencyLeft
      exact absurd hValencyLeft (by decide)
  selected_right_pair := by
    intro sheet hSheet hValency
    exfalso
    have hValencyRight : nonDanglingValency grown.growCandidate.datum
        (grown.growCandidate.datum.sourceEndpoint (freshVertex target) sheet) =
        2 := hValency
    have hRel : (data.vertexPartition wall).Rel sheet grown.growAnchor :=
      hSheet.symm
    rw [W3FourSurvival.GrowMember.fresh_endpoint_eq grown hSheet hRel,
      W3FourSurvival.GrowMember.fresh_nonDanglingValency_eq_three grown survival
        hValid] at hValencyRight
    exact absurd hValencyRight (by decide)
  selectedSide := true
  selectedFlag := flag grown
  selectedFlag_star := flag_star grown survival hValid
  selectedFlag_injOn := flag_injOn grown survival hValid
  selected_not_branch := by
    intro side sheet hSheet hNe
    cases side with
    | false =>
        simp only [wallSide_false]
        show nonDanglingValency grown.growCandidate.datum
            (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall)
              sheet) ≤ 2
        by_cases hGrowRel : grown.growPartition.Rel sheet grown.growAnchor
        · refine le_of_eq ?_
          rw [W3FourSurvival.GrowMember.old_endpoint_eq grown hSheet hGrowRel]
          exact W3FourSurvival.GrowMember.old_grow_nonDanglingValency_eq_two grown
            survival hValid
        · rw [← card_nonDanglingIncident,
            W3FourSurvival.GrowMember.nonDanglingIncident_old_separate grown survival
              hValid hSheet hGrowRel, Finset.card_empty]
          omega
    | true =>
        simp only [wallSide_true] at hNe
        exact absurd (W3FourSurvival.GrowMember.fresh_endpoint_eq grown hSheet
          (show (data.vertexPartition wall).Rel sheet grown.growAnchor from
            hSheet.symm)) hNe
  selectedFlag_row := fun edge hSurvives hIncident hFlag ↦
    flag_row grown survival hValid edge hSurvives hIncident hFlag

@[simp] theorem rowData_candidate (grown : W3FourSourceCandidates.GrowProfile input)
    (survival : SelectedSurvival data wall (ofGrowProfile grown))
    (hValid : data.Valid) :
    (rowData grown survival hValid).candidate = grown.growCandidate := rfl

end GrowMember

/-! ## Figure 28's `M⁽²⁾`: Position II.b

The detached singleton new occurrence dangles, so the divalent endpoint
carries exactly the big new occurrence and the retained `e₄`; the trivalent
endpoint above `A⁽²⁾` is the branch vertex and the detached one is entirely
pruned, so both selected trivalent clauses are vacuous. -/

namespace PositionTwo

/-- `M⁽²⁾`'s branch flag at the trivalent endpoint: the big new occurrence
replaces `e₄`, and `e₂`, `e₃` are retained. -/
noncomputable def flag (position : W3FourClosure.PositionTwo data wall)
    (edge : data.SourceEdge) : position.candidate.datum.SourceEdge :=
  if edge.1.1 = position.largestTarget then
    position.candidate.newSourceEdge position.growAnchor
  else position.candidate.oldSourceEdge edge

theorem flag_largest (position : W3FourClosure.PositionTwo data wall) :
    flag position
        (data.sourceEdge position.largestTarget position.largestAnchor) =
      position.candidate.newSourceEdge position.growAnchor := if_pos rfl

theorem flag_of_ne (position : W3FourClosure.PositionTwo data wall)
    {edge : data.SourceEdge} (hTarget : edge.1.1 ≠ position.largestTarget) :
    flag position edge = position.candidate.oldSourceEdge edge := if_neg hTarget

theorem flag_star (position : W3FourClosure.PositionTwo data wall)
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    nonDanglingIncident position.candidate.datum
        (position.candidate.datum.sourceEndpoint (freshVertex target)
          position.growAnchor) =
      (nonDanglingIncident data
        (data.sourceEndpoint wall position.growAnchor)).image (flag position) := by
  classical
  have hIncoming : nonDanglingIncident data
      (data.sourceEndpoint wall position.growAnchor) =
      {data.sourceEdge position.growTarget position.growAnchor,
        data.sourceEdge position.otherTarget position.otherAnchor,
        data.sourceEdge position.largestTarget position.largestAnchor} :=
    selected_nonDanglingIncident position.toFourStarGeometry survival
  rw [W3FourSurvival.PositionTwo.nonDanglingIncident_fresh_grow position survival
      hValid, hIncoming,
    Finset.image_insert, Finset.image_insert, Finset.image_singleton,
    flag_of_ne position (edge := data.sourceEdge position.growTarget
      position.growAnchor) position.grow_ne_largest,
    flag_of_ne position (edge := data.sourceEdge position.otherTarget
      position.otherAnchor) position.other_ne_largest,
    flag_largest position]
  ext item
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem flag_injOn (position : W3FourClosure.PositionTwo data wall)
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    Set.InjOn (flag position)
      ↑(nonDanglingIncident data
        (data.sourceEndpoint wall position.growAnchor)) := by
  classical
  apply Finset.injOn_of_card_image_eq
  rw [← flag_star position survival hValid, card_nonDanglingIncident,
    card_nonDanglingIncident,
    W3FourSurvival.PositionTwo.fresh_grow_nonDanglingValency_eq_three position
      survival hValid,
    selected_nonDanglingValency_eq_three position.toFourStarGeometry survival
      (sheet := position.growAnchor) rfl]

theorem flag_row (position : W3FourClosure.PositionTwo data wall)
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) (edge : data.SourceEdge)
    (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge
      (data.sourceEndpoint wall position.growAnchor))
    (hFlag : ¬ IsDangling position.candidate.datum (flag position edge)) :
    NonDanglingEdge.stablePath
        (⟨flag position edge, hFlag⟩ :
          NonDanglingEdge position.candidate.datum) =
      (retainedEdge position.candidate hValid.1 ⟨edge, hSurvives⟩).stablePath := by
  rcases survival.exhaustive edge hIncident hSurvives with rfl | rfl | rfl
  · exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (flag_of_ne position position.grow_ne_largest))
  · exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (flag_of_ne position position.other_ne_largest))
  · refine Eq.trans (congrArg NonDanglingEdge.stablePath
      (show (⟨flag position (data.sourceEdge position.largestTarget
              position.largestAnchor), hFlag⟩ :
            NonDanglingEdge position.candidate.datum) =
          ⟨position.candidate.newSourceEdge position.growAnchor,
            W3FourSurvival.PositionTwo.new_grow_survives position survival hValid⟩
        from Subtype.ext (flag_largest position))) ?_
    exact W3FourSurvival.PositionTwo.new_grow_stablePath position survival hValid

/-- `M⁽²⁾`, packaged for the core. -/
noncomputable def rowData (position : W3FourClosure.PositionTwo data wall)
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) : GraphData data wall where
  toBackgroundShape :=
    coreShape (W3FourSurvival.PositionTwo.toReversedMember position).toBackgroundShape
  valid := hValid
  selected_valency_ne_two :=
    selected_nonDanglingValency_ne_two position.toFourStarGeometry survival
  selectedRep := fun _ ↦
    data.sourceEdge position.largestTarget position.largestAnchor
  selectedRep_survives := fun _ _ ↦ survival.largest_survives
  selectedRep_congr := fun _ _ _ _ _ ↦ rfl
  selected_new_stablePath := by
    intro sheet hSheet hSurvives _
    have hEqual := W3FourSurvival.PositionTwo.newSourceEdge_eq_of_survives position
      survival hValid sheet hSheet hSurvives
    refine Eq.trans (congrArg NonDanglingEdge.stablePath
      (show (⟨position.candidate.newSourceEdge sheet, hSurvives⟩ :
            NonDanglingEdge position.candidate.datum) =
          ⟨position.candidate.newSourceEdge position.growAnchor,
            W3FourSurvival.PositionTwo.new_grow_survives position survival hValid⟩
        from Subtype.ext hEqual)) ?_
    exact W3FourSurvival.PositionTwo.new_grow_stablePath position survival hValid
  selected_left_pair := by
    intro sheet hSheet _
    refine ⟨position.growAnchor, rfl, ?_⟩
    have hRel : (data.vertexPartition wall).Rel sheet position.growAnchor :=
      hSheet.symm
    refine Eq.trans (congrArg (nonDanglingIncident position.candidate.datum)
      ((W3FourSurvival.PositionTwo.toReversedMember position).old_endpoint_eq
        hSheet hRel)) ?_
    exact W3FourSurvival.PositionTwo.nonDanglingIncident_old position survival hValid
  selected_right_pair := by
    intro sheet hSheet hValency
    exfalso
    have hValency' : nonDanglingValency position.candidate.datum
        (position.candidate.datum.sourceEndpoint (freshVertex target) sheet) = 2 :=
      hValency
    by_cases hOutside : sheet = position.outside
    · subst hOutside
      exact absurd ((W3FourSurvival.PositionTwo.fresh_outside_nonDanglingValency_eq_zero
        position survival hValid).symm.trans hValency') (by decide)
    · have hFine : position.fine.Rel position.growAnchor sheet :=
        position.fine_rel_growAnchor_iff.mpr ⟨hOutside, hSheet⟩
      have hAnchor : (data.vertexPartition wall).Rel position.growAnchor
          position.growAnchor := rfl
      have hEndpoint :=
        (W3FourSurvival.PositionTwo.toReversedMember position).fresh_endpoint_eq
          hAnchor hFine
      exact absurd (((congrArg (nonDanglingValency position.candidate.datum)
        hEndpoint).symm.trans
        (W3FourSurvival.PositionTwo.fresh_grow_nonDanglingValency_eq_three position
          survival hValid)).symm.trans hValency') (by decide)
  selectedSide := true
  selectedFlag := flag position
  selectedFlag_star := flag_star position survival hValid
  selectedFlag_injOn := flag_injOn position survival hValid
  selected_not_branch := by
    intro side sheet hSheet hNe
    cases side with
    | false =>
        simp only [wallSide_false]
        refine le_of_eq ?_
        show nonDanglingValency position.candidate.datum
            (position.candidate.datum.sourceEndpoint (oldVertex target wall)
              sheet) = 2
        exact Eq.trans (congrArg (nonDanglingValency position.candidate.datum)
            ((W3FourSurvival.PositionTwo.toReversedMember position).old_endpoint_eq
              hSheet (show (data.vertexPartition wall).Rel sheet
                position.growAnchor from hSheet.symm)))
          (W3FourSurvival.PositionTwo.old_nonDanglingValency_eq_two position
            survival hValid)
    | true =>
        simp only [wallSide_true] at hNe ⊢
        show nonDanglingValency position.candidate.datum
            (position.candidate.datum.sourceEndpoint (freshVertex target)
              sheet) ≤ 2
        by_cases hOutside : sheet = position.outside
        · subst hOutside
          rw [W3FourSurvival.PositionTwo.fresh_outside_nonDanglingValency_eq_zero
            position survival hValid]
          omega
        · exact absurd
            ((W3FourSurvival.PositionTwo.toReversedMember position).fresh_endpoint_eq
              hSheet (position.fine_rel_growAnchor_iff.mpr ⟨hOutside, hSheet⟩).symm)
            hNe
  selectedFlag_row := fun edge hSurvives hIncident hFlag ↦
    flag_row position survival hValid edge hSurvives hIncident hFlag

@[simp] theorem rowData_candidate (position : W3FourClosure.PositionTwo data wall)
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    (rowData position survival hValid).candidate = position.candidate := rfl

end PositionTwo

/-! ## Figure 28's `M⁽¹⁾`: Position I

`fine` splits `A₀` into `e₂` and `e₃`, so both selected new occurrences survive
at their own valency-two trivalent endpoints, and the divalent endpoint is the
branch vertex -- so it is the selected divalent clause that is vacuous here. -/

namespace PositionOne

variable (position : W3FourClosure.PositionOne data wall)

/-- `M⁽¹⁾`'s selected representative: `e₂` on `e₂`'s own trivalent class and
`e₃` on the other. -/
noncomputable def rep (sheet : Fin degree) : data.SourceEdge :=
  if position.fine.Rel sheet position.growAnchor then
    data.sourceEdge position.growTarget position.growAnchor
  else data.sourceEdge position.otherTarget position.otherAnchor

theorem rep_of_grow {sheet : Fin degree}
    (hGrow : position.fine.Rel sheet position.growAnchor) :
    rep position sheet =
      data.sourceEdge position.growTarget position.growAnchor := if_pos hGrow

theorem rep_of_not_grow {sheet : Fin degree}
    (hGrow : ¬ position.fine.Rel sheet position.growAnchor) :
    rep position sheet =
      data.sourceEdge position.otherTarget position.otherAnchor := if_neg hGrow

theorem rep_grow : rep position position.growAnchor =
    data.sourceEdge position.growTarget position.growAnchor :=
  rep_of_grow position rfl

theorem rep_other : rep position position.otherAnchor =
    data.sourceEdge position.otherTarget position.otherAnchor :=
  rep_of_not_grow position (W3FourSurvival.PositionOne.fine_other_not_grow position)

theorem rep_survives
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (sheet : Fin degree) : ¬ IsDangling data (rep position sheet) := by
  by_cases hGrow : position.fine.Rel sheet position.growAnchor
  · rw [rep_of_grow position hGrow]; exact survival.grow_survives
  · rw [rep_of_not_grow position hGrow]; exact survival.other_survives

/-- `M⁽¹⁾`'s branch flag at the divalent endpoint: the two selected new
occurrences replace `e₂` and `e₃`, and `e₄` is retained. -/
noncomputable def branchFlag (edge : data.SourceEdge) :
    position.candidate.datum.SourceEdge :=
  if edge.1.1 = position.growTarget then
    position.candidate.newSourceEdge position.growAnchor
  else if edge.1.1 = position.otherTarget then
    position.candidate.newSourceEdge position.otherAnchor
  else position.candidate.oldSourceEdge edge

theorem branchFlag_grow :
    branchFlag position
        (data.sourceEdge position.growTarget position.growAnchor) =
      position.candidate.newSourceEdge position.growAnchor := if_pos rfl

theorem branchFlag_other :
    branchFlag position
        (data.sourceEdge position.otherTarget position.otherAnchor) =
      position.candidate.newSourceEdge position.otherAnchor := by
  unfold branchFlag
  rw [if_neg (show ¬ ((data.sourceEdge position.otherTarget
        position.otherAnchor).1.1 = position.growTarget) from
      Ne.symm position.grow_ne_other),
    if_pos (show (data.sourceEdge position.otherTarget
        position.otherAnchor).1.1 = position.otherTarget from rfl)]

theorem branchFlag_largest :
    branchFlag position
        (data.sourceEdge position.largestTarget position.largestAnchor) =
      position.candidate.oldSourceEdge
        (data.sourceEdge position.largestTarget position.largestAnchor) := by
  unfold branchFlag
  rw [if_neg (show ¬ ((data.sourceEdge position.largestTarget
        position.largestAnchor).1.1 = position.growTarget) from
      Ne.symm position.grow_ne_largest),
    if_neg (show ¬ ((data.sourceEdge position.largestTarget
        position.largestAnchor).1.1 = position.otherTarget) from
      Ne.symm position.other_ne_largest)]

theorem branchFlag_star
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    nonDanglingIncident position.candidate.datum
        (position.candidate.datum.sourceEndpoint (oldVertex target wall)
          position.growAnchor) =
      (nonDanglingIncident data
        (data.sourceEndpoint wall position.growAnchor)).image
        (branchFlag position) := by
  classical
  have hIncoming : nonDanglingIncident data
      (data.sourceEndpoint wall position.growAnchor) =
      {data.sourceEdge position.growTarget position.growAnchor,
        data.sourceEdge position.otherTarget position.otherAnchor,
        data.sourceEdge position.largestTarget position.largestAnchor} :=
    selected_nonDanglingIncident position.toFourStarGeometry survival
  rw [W3FourSurvival.PositionOne.nonDanglingIncident_old position survival hValid,
    hIncoming, Finset.image_insert, Finset.image_insert, Finset.image_singleton,
    branchFlag_grow position, branchFlag_other position,
    branchFlag_largest position]

theorem branchFlag_injOn
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    Set.InjOn (branchFlag position)
      ↑(nonDanglingIncident data
        (data.sourceEndpoint wall position.growAnchor)) := by
  classical
  apply Finset.injOn_of_card_image_eq
  rw [← branchFlag_star position survival hValid, card_nonDanglingIncident,
    card_nonDanglingIncident,
    W3FourSurvival.PositionOne.old_nonDanglingValency_eq_three position survival
      hValid,
    selected_nonDanglingValency_eq_three position.toFourStarGeometry survival
      (sheet := position.growAnchor) rfl]

theorem branchFlag_row
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) (edge : data.SourceEdge)
    (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge
      (data.sourceEndpoint wall position.growAnchor))
    (hFlag : ¬ IsDangling position.candidate.datum (branchFlag position edge)) :
    NonDanglingEdge.stablePath
        (⟨branchFlag position edge, hFlag⟩ :
          NonDanglingEdge position.candidate.datum) =
      (retainedEdge position.candidate hValid.1 ⟨edge, hSurvives⟩).stablePath := by
  rcases survival.exhaustive edge hIncident hSurvives with rfl | rfl | rfl
  · refine Eq.trans (congrArg NonDanglingEdge.stablePath
      (show (⟨branchFlag position (data.sourceEdge position.growTarget
              position.growAnchor), hFlag⟩ :
            NonDanglingEdge position.candidate.datum) =
          ⟨position.candidate.newSourceEdge position.growAnchor,
            W3FourSurvival.PositionOne.new_grow_survives position survival hValid⟩
        from Subtype.ext (branchFlag_grow position))) ?_
    exact W3FourSurvival.PositionOne.new_grow_stablePath position survival hValid
  · refine Eq.trans (congrArg NonDanglingEdge.stablePath
      (show (⟨branchFlag position (data.sourceEdge position.otherTarget
              position.otherAnchor), hFlag⟩ :
            NonDanglingEdge position.candidate.datum) =
          ⟨position.candidate.newSourceEdge position.otherAnchor,
            W3FourSurvival.PositionOne.new_other_survives position survival hValid⟩
        from Subtype.ext (branchFlag_other position))) ?_
    exact W3FourSurvival.PositionOne.new_other_stablePath position survival hValid
  · exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (branchFlag_largest position))

/-- `M⁽¹⁾`, packaged for the core. -/
noncomputable def rowData
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) : GraphData data wall where
  toBackgroundShape :=
    coreShape (W3FourSurvival.PositionOne.toReversedMember position).toBackgroundShape
  valid := hValid
  selected_valency_ne_two :=
    selected_nonDanglingValency_ne_two position.toFourStarGeometry survival
  selectedRep := rep position
  selectedRep_survives := fun sheet _ ↦ rep_survives position survival sheet
  selectedRep_congr := by
    intro first second hFirst _ hEqual
    have hRel := ((W3FourSurvival.PositionOne.toReversedMember
      position).newSourceEdge_eq_iff_fine_rel hFirst).mp hEqual
    by_cases hFirstGrow : position.fine.Rel first position.growAnchor
    · rw [rep_of_grow position hFirstGrow,
        rep_of_grow position (hRel.symm.trans hFirstGrow)]
    · rw [rep_of_not_grow position hFirstGrow,
        rep_of_not_grow position (fun hSecond ↦ hFirstGrow (hRel.trans hSecond))]
  selected_new_stablePath := by
    intro sheet hSheet hSurvives _
    by_cases hGrow : position.fine.Rel sheet position.growAnchor
    · have hEqual : position.candidate.newSourceEdge sheet =
          position.candidate.newSourceEdge position.growAnchor :=
        (W3FourSurvival.PositionOne.toReversedMember
          position).newSourceEdge_eq_of_fine_rel
          (first := position.growAnchor) (second := sheet) rfl hGrow.symm
      refine Eq.trans (congrArg NonDanglingEdge.stablePath
        (show (⟨position.candidate.newSourceEdge sheet, hSurvives⟩ :
              NonDanglingEdge position.candidate.datum) =
            ⟨position.candidate.newSourceEdge position.growAnchor,
              W3FourSurvival.PositionOne.new_grow_survives position survival hValid⟩
          from Subtype.ext hEqual)) ?_
      refine Eq.trans (W3FourSurvival.PositionOne.new_grow_stablePath position
        survival hValid) ?_
      exact congrArg NonDanglingEdge.stablePath (Subtype.ext
        (congrArg position.candidate.oldSourceEdge (rep_of_grow position hGrow).symm))
    · have hOther : position.fine.Rel position.otherAnchor sheet :=
        (W3FourSurvival.PositionOne.fine_cover position hSheet).resolve_left
          (fun hRel ↦ hGrow hRel.symm)
      have hEqual : position.candidate.newSourceEdge sheet =
          position.candidate.newSourceEdge position.otherAnchor :=
        (W3FourSurvival.PositionOne.toReversedMember
          position).newSourceEdge_eq_of_fine_rel
          (first := position.otherAnchor) (second := sheet)
          position.other_wall_rel hOther
      refine Eq.trans (congrArg NonDanglingEdge.stablePath
        (show (⟨position.candidate.newSourceEdge sheet, hSurvives⟩ :
              NonDanglingEdge position.candidate.datum) =
            ⟨position.candidate.newSourceEdge position.otherAnchor,
              W3FourSurvival.PositionOne.new_other_survives position survival hValid⟩
          from Subtype.ext hEqual)) ?_
      refine Eq.trans (W3FourSurvival.PositionOne.new_other_stablePath position
        survival hValid) ?_
      exact congrArg NonDanglingEdge.stablePath (Subtype.ext
        (congrArg position.candidate.oldSourceEdge
          (rep_of_not_grow position hGrow).symm))
  selected_left_pair := by
    intro sheet hSheet hValency
    exfalso
    have hValency' : nonDanglingValency position.candidate.datum
        (position.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) =
        2 := hValency
    have hRel : (data.vertexPartition wall).Rel sheet position.growAnchor :=
      hSheet.symm
    have hEndpoint :=
      (W3FourSurvival.PositionOne.toReversedMember position).old_endpoint_eq
        hSheet hRel
    exact absurd (((congrArg (nonDanglingValency position.candidate.datum)
      hEndpoint).trans
      (W3FourSurvival.PositionOne.old_nonDanglingValency_eq_three position survival
        hValid)).symm.trans hValency') (by decide)
  selected_right_pair := by
    intro sheet hSheet _
    rcases W3FourSurvival.PositionOne.fine_cover position hSheet with hGrow | hOther
    · refine ⟨position.growAnchor, rfl, ?_⟩
      have hEndpoint :=
        (W3FourSurvival.PositionOne.toReversedMember position).fresh_endpoint_eq
          (first := sheet) (second := position.growAnchor) hSheet hGrow.symm
      refine Eq.trans (congrArg (nonDanglingIncident position.candidate.datum)
        hEndpoint) ?_
      rw [rep_grow position]
      exact W3FourSurvival.PositionOne.nonDanglingIncident_fresh_grow position
        survival hValid
    · refine ⟨position.otherAnchor, position.other_wall_rel, ?_⟩
      have hEndpoint :=
        (W3FourSurvival.PositionOne.toReversedMember position).fresh_endpoint_eq
          (first := sheet) (second := position.otherAnchor) hSheet hOther.symm
      refine Eq.trans (congrArg (nonDanglingIncident position.candidate.datum)
        hEndpoint) ?_
      rw [rep_other position]
      exact W3FourSurvival.PositionOne.nonDanglingIncident_fresh_other position
        survival hValid
  selectedSide := false
  selectedFlag := branchFlag position
  selectedFlag_star := branchFlag_star position survival hValid
  selectedFlag_injOn := branchFlag_injOn position survival hValid
  selected_not_branch := by
    intro side sheet hSheet hNe
    cases side with
    | false =>
        simp only [wallSide_false] at hNe
        exact absurd
          ((W3FourSurvival.PositionOne.toReversedMember position).old_endpoint_eq
            hSheet (show (data.vertexPartition wall).Rel sheet position.growAnchor
              from hSheet.symm)) hNe
    | true =>
        simp only [wallSide_true]
        refine le_of_eq ?_
        show nonDanglingValency position.candidate.datum
            (position.candidate.datum.sourceEndpoint (freshVertex target)
              sheet) = 2
        rcases W3FourSurvival.PositionOne.fine_cover position hSheet with
          hGrow | hOther
        · exact Eq.trans (congrArg (nonDanglingValency position.candidate.datum)
              ((W3FourSurvival.PositionOne.toReversedMember
                position).fresh_endpoint_eq hSheet hGrow.symm))
            (W3FourSurvival.PositionOne.fresh_grow_nonDanglingValency_eq_two
              position survival hValid)
        · exact Eq.trans (congrArg (nonDanglingValency position.candidate.datum)
              ((W3FourSurvival.PositionOne.toReversedMember
                position).fresh_endpoint_eq hSheet hOther.symm))
            (W3FourSurvival.PositionOne.fresh_other_nonDanglingValency_eq_two
              position survival hValid)
  selectedFlag_row := fun edge hSurvives hIncident hFlag ↦
    branchFlag_row position survival hValid edge hSurvives hIncident hFlag

@[simp] theorem rowData_candidate
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    (rowData position survival hValid).candidate = position.candidate := rfl

end PositionOne

/-! ## The four members' row equivalences and retained columns

The named forms, stated on each member's own candidate.  `M⁽³⁾` and `M⁽⁴⁾` are
the two `GrowProfile`s of the case, so `GrowMember` covers both. -/

namespace PositionOne

variable (position : W3FourClosure.PositionOne data wall)
  (survival : SelectedSurvival data wall position.toFourStarGeometry)
  (hValid : data.Valid)

/-- **`M⁽¹⁾`'s occurrence-induced stable-row equivalence.** -/
noncomputable def stablePathEquiv :
    StablePath data ≃ StablePath position.candidate.datum :=
  (rowData position survival hValid).stablePathEquiv

@[simp] theorem stablePathEquiv_mk (edge : NonDanglingEdge data) :
    stablePathEquiv position survival hValid edge.stablePath =
      (retainedEdge position.candidate hValid.1 edge).stablePath := rfl

/-- **Every retained column of `M⁽¹⁾` is the incoming wall column.** -/
theorem matrix_retained (path : StablePath data) (place : target.edges) :
    matrix position.candidate.datum
        (stablePathEquiv position survival hValid path)
        (occurrenceEquiv target wall position.candidate.right (some place)) =
      matrix data path place :=
  (rowData position survival hValid).matrix_retained path place

end PositionOne

namespace PositionTwo

variable (position : W3FourClosure.PositionTwo data wall)
  (survival : SelectedSurvival data wall position.toFourStarGeometry)
  (hValid : data.Valid)

/-- **`M⁽²⁾`'s occurrence-induced stable-row equivalence.** -/
noncomputable def stablePathEquiv :
    StablePath data ≃ StablePath position.candidate.datum :=
  (rowData position survival hValid).stablePathEquiv

@[simp] theorem stablePathEquiv_mk (edge : NonDanglingEdge data) :
    stablePathEquiv position survival hValid edge.stablePath =
      (retainedEdge position.candidate hValid.1 edge).stablePath := rfl

/-- **Every retained column of `M⁽²⁾` is the incoming wall column.** -/
theorem matrix_retained (path : StablePath data) (place : target.edges) :
    matrix position.candidate.datum
        (stablePathEquiv position survival hValid path)
        (occurrenceEquiv target wall position.candidate.right (some place)) =
      matrix data path place :=
  (rowData position survival hValid).matrix_retained path place

end PositionTwo

namespace GrowMember

variable {star : ThreeStar target wall} {input : W3SourceInput data star}
  (grown : W3FourSourceCandidates.GrowProfile input)
  (survival : SelectedSurvival data wall (ofGrowProfile grown))
  (hValid : data.Valid)

/-- **A grow member's occurrence-induced stable-row equivalence**, hence
`M⁽³⁾`'s and `M⁽⁴⁾`'s. -/
noncomputable def stablePathEquiv :
    StablePath data ≃ StablePath grown.growCandidate.datum :=
  (rowData grown survival hValid).stablePathEquiv

@[simp] theorem stablePathEquiv_mk (edge : NonDanglingEdge data) :
    stablePathEquiv grown survival hValid edge.stablePath =
      (retainedEdge grown.growCandidate hValid.1 edge).stablePath := rfl

/-- **Every retained column of a grow member is the incoming wall column.** -/
theorem matrix_retained (path : StablePath data) (place : target.edges) :
    matrix grown.growCandidate.datum
        (stablePathEquiv grown survival hValid path)
        (occurrenceEquiv target wall grown.growCandidate.right (some place)) =
      matrix data path place :=
  (rowData grown survival hValid).matrix_retained path place

end GrowMember

/-! ## The four members' stable incidence graphs -/

/-- **`M⁽¹⁾`'s stable incidence graph is the incoming one.** -/
noncomputable def PositionOne.equivalence
    (position : W3FourClosure.PositionOne data wall)
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    StableGraphIncidence.Equivalence data position.candidate.datum :=
  (PositionOne.rowData position survival hValid).equivalence

/-- **`M⁽²⁾`'s stable incidence graph is the incoming one.** -/
noncomputable def PositionTwo.equivalence
    (position : W3FourClosure.PositionTwo data wall)
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    StableGraphIncidence.Equivalence data position.candidate.datum :=
  (PositionTwo.rowData position survival hValid).equivalence

/-- **A grow member's stable incidence graph is the incoming one**, hence
`M⁽³⁾`'s and `M⁽⁴⁾`'s. -/
noncomputable def GrowMember.equivalence {star : ThreeStar target wall}
    {input : W3SourceInput data star}
    (grown : W3FourSourceCandidates.GrowProfile input)
    (survival : SelectedSurvival data wall (ofGrowProfile grown))
    (hValid : data.Valid) :
    StableGraphIncidence.Equivalence data grown.growCandidate.datum :=
  (GrowMember.rowData grown survival hValid).equivalence
end DraismaVargas.LocalCases.W3FourRowDescent