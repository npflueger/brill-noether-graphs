module

public import DraismaVargas.LocalCases.NonTrivalentValencyTwoRows

@[expose] public section

/-!
# The ordinary-block census and the retained-row descent at a two-valent wall

Source: Vargas, Part II (arXiv:2609.09109), §5.4 (valency-two limits, case
`{v2-nd4}`), read through the labelling convention (1) of §5.1, and §5.1 (the
lemma on rigidity above `w_0`, `lemma-above-w0`) for the trivalence of the
ordinary blocks above `w_0`.

`NonTrivalentValencyTwoRows` proves the anchor picture -- the two trivalent
endpoint classes, the exact surviving stars, the divalent Configuration B
vertex, and `bridgeEdge_isolated` -- and states `retainedRow` conditionally on
the named `Prop` `NonTrivalentValencyTwoRows.OrdinaryBlockDescent`.  This
module supplies the ordinary-block census and discharges that `Prop`.

## The census

At a wall block `B` **other than the anchor** the candidate installs the
*neutral* joined resolution (`candidate_resolution_of_not_wall_rel`), so `B` is
not split at all: `candidate_vertexPartition_rel_ordinary` and
`newEdge_rel_ordinary` say that both endpoint partitions and the new-edge
partition restrict to the unchanged wall partition there.  Consequently, with
`star_s(B)` the wall datum's surviving occurrences at `B` whose target the base
tree assigns to side `s` (`ordinaryStar`):

* `mem_nonDanglingIncident_endpointVertex_ordinary` -- a surviving occurrence at
  the candidate's endpoint vertex over `B` on side `s` is either the retained
  copy of a member of `star_s(B)` or the single new occurrence of `B`;
* `nonDanglingValency_endpointVertex_of_new_dangling` and
  `..._of_new_survives` -- hence `nd(B_s) = |star_s(B)| + [new survives]`;
* `card_ordinaryStar_add` -- and `|star_u(B)| + |star_v(B)| = nd(B)`;
* `newSourceEdge_survives_iff_ordinary` -- the new occurrence of `B`
  survives exactly when both sides carry a survivor, because surviving valency
  one is impossible (`NonDanglingValency.nonDanglingValency_ne_one`).

Dangling-ness of a retained occurrence transports between `data` and the
candidate through `ResolutionPruning.isDangling_oldSourceEdge_iff`, whose genus
hypothesis is `NonTrivalentValencyTwoRows.candidate_sourceGenus`; that is the
wall-block analogue of `ResolutionAwayFromWall.nonDanglingIncident_retainedVertex`.

## What is proved

* `ordinaryBlockDescent`: `NonTrivalentValencyTwoRows.OrdinaryBlockDescent`
  holds for every wall datum and every valency-two anchor, with **no** extra
  hypothesis beyond `data.Valid`.  Two survivors at a divalent ordinary block
  either sit on the same side -- and then the new occurrence is dangling and
  they are consecutive at that endpoint -- or one on each side, and then the
  new occurrence survives, both new vertices are divalent, and the two-step
  consecutiveness carries the row across.
* `retainedRow` and `retainedRow_mk`: `NonTrivalentValencyTwoRows.retainedRow`
  becomes unconditional, its only hypothesis being `data.Valid`.

## What is NOT proved here

The row *equivalence* and the resulting unconditional labelling; those are
`NonTrivalentValencyTwoRowEquiv.rowEquiv` and `...labelling`, which build on
this module's census.  The ordinary-block bound `nd(B) <= 3` is *not* used for
the descent and is not assumed here; it is an input of the row equivalence,
isolated there as `OrdinaryTrivalent`.

## Consumers

`NonTrivalentValencyTwoRowEquiv`, `NonTrivalentValencyTwoRows.retainedRow`
(through `OrdinaryBlockDescent`), and the boundary dispatcher for Part II case
`{v2-nd4}` (`NonTrivalentValencyTwoDispatcher`).
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoDescent

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRows

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall}
  (source : TwoBranchAnchor data star anchor)
  (sel : Prescribed.Selection data star anchor)

local notation "cand" => (Prescribed.validCandidate sel)

local notation "rep" => (Prescribed.selectedRepresentative sel)

/-! ## 1.  The neutral resolution at an ordinary wall block -/

theorem not_rel_repr {a : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    ¬ (data.vertexPartition wall).Rel anchor.1 ((data.vertexPartition wall).repr a) :=
  fun h ↦ hA (h.trans ((data.vertexPartition wall).rel_repr_right a).symm)

/-- Over an ordinary wall block the candidate's endpoint partitions are the
*unchanged* wall partition, on both sides of the new target edge. -/
theorem candidate_vertexPartition_rel_ordinary (sideValue : Bool) {a b : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    ((cand).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall)).Rel a b ↔
      (data.vertexPartition wall).Rel a b := by
  have hJoined := candidate_resolution_of_not_wall_rel sel
    ((data.vertexPartition wall).repr a) (not_rel_repr hA)
  cases sideValue
  · show ((cand).datum.vertexPartition (oldVertex target wall)).Rel a b ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
    refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
      (fun blk ↦ ((cand).resolution blk).left)
      (fun blk ↦ ((cand).contracts blk).left_refines) a b) ?_
    rw [hJoined]
    rfl
  · show ((cand).datum.vertexPartition (freshVertex target)).Rel a b ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]
    refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
      (fun blk ↦ ((cand).resolution blk).right)
      (fun blk ↦ ((cand).contracts blk).right_refines) a b) ?_
    rw [hJoined]
    rfl

/-- The same for the new-edge partition: an ordinary block is not split. -/
theorem newEdge_rel_ordinary {a b : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.Rel a b ↔
      (data.vertexPartition wall).Rel a b := by
  have hJoined := candidate_resolution_of_not_wall_rel sel
    ((data.vertexPartition wall).repr a) (not_rel_repr hA)
  refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
    (fun blk ↦ ((cand).resolution blk).newEdge)
    (fun blk ↦ ((cand).resolution blk).edge_refines_left.trans
      ((cand).contracts blk).left_refines) a b) ?_
  rw [hJoined]
  rfl

/-! ### Incidence at the two ordinary endpoint vertices -/

theorem incident_sourceEndpoint_wall_iff (x : Fin degree) (old : data.SourceEdge) :
    Incident data old (data.sourceEndpoint wall x) ↔
      (old.1.1 ∈ GluingDatum.incidentEdges wall ∧
        (data.vertexPartition wall).Rel x old.1.2) := by
  constructor
  · intro hIncident
    obtain ⟨hMem, hRel⟩ := (incident_iff_target_mem_and_rel _ _ _).mp hIncident
    exact ⟨hMem, Eq.trans ((data.vertexPartition wall).rel_repr_right x) hRel⟩
  · rintro ⟨hMem, hRel⟩
    exact (incident_iff_target_mem_and_rel _ _ _).mpr
      ⟨hMem, Eq.trans ((data.vertexPartition wall).rel_repr_right x).symm hRel⟩

theorem incident_endpointVertex_iff (sideValue : Bool) (x : Fin degree)
    (e : (cand).datum.SourceEdge) :
    Incident (cand).datum e (endpointVertex sel sideValue x) ↔
      (e.1.1 ∈ GluingDatum.incidentEdges
          (if sideValue then freshVertex target else oldVertex target wall) ∧
        ((cand).datum.vertexPartition
          (if sideValue then freshVertex target else oldVertex target wall)).Rel x e.1.2) := by
  constructor
  · intro hIncident
    obtain ⟨hMem, hRel⟩ := (incident_iff_target_mem_and_rel _ _ _).mp hIncident
    exact ⟨hMem, Eq.trans (((cand).datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right x) hRel⟩
  · rintro ⟨hMem, hRel⟩
    refine (incident_iff_target_mem_and_rel _ _ _).mpr ⟨hMem, ?_⟩
    exact Eq.trans (((cand).datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right x).symm hRel

/-- **Retained occurrences at an ordinary block.**  The candidate's endpoint
vertex over `u` (resp. `v`) sees exactly the wall datum's occurrences at that
block whose target the base tree assigns to that side. -/
theorem incident_oldSourceEdge_endpointVertex_iff (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (old : data.SourceEdge) :
    Incident (cand).datum ((cand).oldSourceEdge old)
        (endpointVertex sel sideValue x) ↔
      (Incident data old (data.sourceEndpoint wall x) ∧
        Prescribed.rightAssignment data star anchor old.1.1 = sideValue) := by
  rw [incident_endpointVertex_iff, BalancedGlobal.Candidate.oldSourceEdge_target,
    mem_incidentEdges_endpoint_old, BalancedGlobal.Candidate.oldSourceEdge_sheet,
    candidate_vertexPartition_rel_ordinary sel sideValue hX,
    incident_sourceEndpoint_wall_iff]
  tauto

theorem newEdge_refines_wall :
    (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
      (cand).contracts).newEdge.Refines (data.vertexPartition wall) :=
  (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
    (cand).contracts).edge_refines_left.trans
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall) (cand).resolution
        (cand).contracts)

/-- **New occurrences at an ordinary block.**  The block is not split, so the
only new occurrence meeting either endpoint vertex over it is its own. -/
theorem newSourceEdge_eq_of_incident_ordinary (sideValue : Bool) {x y : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hIncident : Incident (cand).datum ((cand).newSourceEdge y)
      (endpointVertex sel sideValue x)) :
    (cand).newSourceEdge y = (cand).newSourceEdge x := by
  have hRel := ((incident_endpointVertex_iff sel sideValue x _).mp hIncident).2
  rw [candidate_vertexPartition_rel_ordinary sel sideValue hX] at hRel
  have hSheet : ((cand).newSourceEdge y).1.2 =
      (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.repr y := rfl
  rw [hSheet] at hRel
  have hBack : (data.vertexPartition wall).Rel
      ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.repr y) y :=
    (newEdge_refines_wall sel).rel
      ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.rel_repr_left y)
  exact (newSourceEdge_eq_of_rel sel
    ((newEdge_rel_ordinary sel hX).mpr (hRel.trans hBack))).symm

/-- The new occurrence of a block meets both of its endpoint vertices. -/
theorem newSourceEdge_incident_endpointVertex (sideValue : Bool) (x : Fin degree) :
    Incident (cand).datum ((cand).newSourceEdge x)
      (endpointVertex sel sideValue x) := by
  have h : Incident (cand).datum (bridgeEdge sel x)
      (endpointVertex sel sideValue x) := bridgeEdge_incident sel sideValue x
  exact h

/-! ## 2.  The ordinary-block census

Write `star_s(B)` for the wall datum's surviving occurrences at the block `B`
whose target the outgoing base tree assigns to the side `s`.  The two sides
partition the block's surviving star, and the candidate's endpoint vertex over
`B` on side `s` carries exactly the retained copies of `star_s(B)`, together
with the block's single new occurrence when that survives. -/

/-- The wall datum's surviving occurrences at one ordinary block, on one side
of the outgoing base tree. -/
noncomputable def ordinaryStar (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (x : Fin degree) (sideValue : Bool) : Finset data.SourceEdge := by
  classical
  exact (nonDanglingIncident data (data.sourceEndpoint wall x)).filter
    (fun old ↦ Prescribed.rightAssignment data star anchor old.1.1 = sideValue)

theorem mem_ordinaryStar {x : Fin degree} {sideValue : Bool} (old : data.SourceEdge) :
    old ∈ ordinaryStar data star anchor x sideValue ↔
      ((¬ IsDangling data old ∧ Incident data old (data.sourceEndpoint wall x)) ∧
        Prescribed.rightAssignment data star anchor old.1.1 = sideValue) := by
  classical
  rw [ordinaryStar, Finset.mem_filter, mem_nonDanglingIncident]

theorem ordinaryStar_disjoint (x : Fin degree) :
    Disjoint (ordinaryStar data star anchor x false)
      (ordinaryStar data star anchor x true) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro old hFalse hTrue
  rw [mem_ordinaryStar] at hFalse hTrue
  rw [hFalse.2] at hTrue
  exact Bool.false_ne_true hTrue.2

theorem ordinaryStar_union (x : Fin degree) :
    ordinaryStar data star anchor x false ∪ ordinaryStar data star anchor x true =
      nonDanglingIncident data (data.sourceEndpoint wall x) := by
  classical
  ext old
  rw [Finset.mem_union, mem_ordinaryStar, mem_ordinaryStar, mem_nonDanglingIncident]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    cases Prescribed.rightAssignment data star anchor old.1.1
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr ⟨h, rfl⟩

/-- **The two sides partition the block's surviving star.** -/
theorem card_ordinaryStar_add (x : Fin degree) :
    (ordinaryStar data star anchor x false).card +
        (ordinaryStar data star anchor x true).card =
      nonDanglingValency data (data.sourceEndpoint wall x) := by
  classical
  rw [← Finset.card_union_of_disjoint (ordinaryStar_disjoint (star := star) (anchor := anchor) x),
    ordinaryStar_union, card_nonDanglingIncident]

/-- **The ordinary-block census.**  A surviving occurrence at the candidate's
endpoint vertex over an ordinary block, on either side, is the retained copy of
a survivor of that side or the block's own new occurrence. -/
theorem mem_nonDanglingIncident_endpointVertex_ordinary (hValid : data.Valid)
    (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (e : (cand).datum.SourceEdge) :
    e ∈ nonDanglingIncident (cand).datum (endpointVertex sel sideValue x) ↔
      ((∃ old ∈ ordinaryStar data star anchor x sideValue, e = (cand).oldSourceEdge old) ∨
        (e = (cand).newSourceEdge x ∧
          ¬ IsDangling (cand).datum ((cand).newSourceEdge x))) := by
  classical
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, rfl⟩ | ⟨y, rfl⟩
    · refine Or.inl ⟨old, ?_, rfl⟩
      rw [mem_ordinaryStar]
      refine ⟨⟨fun h ↦ hSurvives ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand)
        hValid (candidate_sourceGenus sel) old).mpr h), ?_⟩, ?_⟩
      · exact ((incident_oldSourceEdge_endpointVertex_iff sel sideValue hX old).mp
          hIncident).1
      · exact ((incident_oldSourceEdge_endpointVertex_iff sel sideValue hX old).mp
          hIncident).2
    · have hEq := newSourceEdge_eq_of_incident_ordinary sel sideValue hX hIncident
      exact Or.inr ⟨hEq, hEq ▸ hSurvives⟩
  · rintro (⟨old, hOld, rfl⟩ | ⟨rfl, hSurvives⟩)
    · rw [mem_ordinaryStar] at hOld
      refine (mem_nonDanglingIncident _ _ _).mpr
        ⟨ResolutionSurvival.not_isDangling_oldSourceEdge (cand) hValid.1 old hOld.1.1, ?_⟩
      exact (incident_oldSourceEdge_endpointVertex_iff sel sideValue hX old).mpr
        ⟨hOld.1.2, hOld.2⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨hSurvives, newSourceEdge_incident_endpointVertex sel sideValue x⟩

theorem nonDanglingIncident_endpointVertex_of_new_dangling (hValid : data.Valid)
    (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hDangling : IsDangling (cand).datum ((cand).newSourceEdge x)) :
    nonDanglingIncident (cand).datum (endpointVertex sel sideValue x) =
      (ordinaryStar data star anchor x sideValue).image (cand).oldSourceEdge := by
  classical
  ext e
  rw [mem_nonDanglingIncident_endpointVertex_ordinary sel hValid sideValue hX,
    Finset.mem_image]
  constructor
  · rintro (⟨old, hOld, rfl⟩ | ⟨-, hSurvives⟩)
    · exact ⟨old, hOld, rfl⟩
    · exact absurd hDangling hSurvives
  · rintro ⟨old, hOld, rfl⟩
    exact Or.inl ⟨old, hOld, rfl⟩

theorem nonDanglingIncident_endpointVertex_of_new_survives (hValid : data.Valid)
    (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hSurvives : ¬ IsDangling (cand).datum ((cand).newSourceEdge x)) :
    nonDanglingIncident (cand).datum (endpointVertex sel sideValue x) =
      insert ((cand).newSourceEdge x)
        ((ordinaryStar data star anchor x sideValue).image (cand).oldSourceEdge) := by
  classical
  ext e
  rw [mem_nonDanglingIncident_endpointVertex_ordinary sel hValid sideValue hX,
    Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (⟨old, hOld, rfl⟩ | ⟨rfl, -⟩)
    · exact Or.inr ⟨old, hOld, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨old, hOld, rfl⟩)
    · exact Or.inr ⟨rfl, hSurvives⟩
    · exact Or.inl ⟨old, hOld, rfl⟩

theorem newSourceEdge_notMem_image (sideValue : Bool) (x : Fin degree) :
    (cand).newSourceEdge x ∉
      (ordinaryStar data star anchor x sideValue).image (cand).oldSourceEdge := by
  classical
  intro hMem
  obtain ⟨old, -, hEq⟩ := Finset.mem_image.mp hMem
  exact newSourceEdge_ne_oldSourceEdge sel x old hEq.symm

/-- `nd(B_s) = |star_s(B)|` when the block's new occurrence is dangling. -/
theorem nonDanglingValency_endpointVertex_of_new_dangling (hValid : data.Valid)
    (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hDangling : IsDangling (cand).datum ((cand).newSourceEdge x)) :
    nonDanglingValency (cand).datum (endpointVertex sel sideValue x) =
      (ordinaryStar data star anchor x sideValue).card := by
  classical
  rw [← card_nonDanglingIncident,
    nonDanglingIncident_endpointVertex_of_new_dangling sel hValid sideValue hX hDangling,
    Finset.card_image_of_injective _ (ResolutionCut.oldSourceEdge_injective (cand))]

/-- `nd(B_s) = |star_s(B)| + 1` when the block's new occurrence survives. -/
theorem nonDanglingValency_endpointVertex_of_new_survives (hValid : data.Valid)
    (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hSurvives : ¬ IsDangling (cand).datum ((cand).newSourceEdge x)) :
    nonDanglingValency (cand).datum (endpointVertex sel sideValue x) =
      (ordinaryStar data star anchor x sideValue).card + 1 := by
  classical
  rw [← card_nonDanglingIncident,
    nonDanglingIncident_endpointVertex_of_new_survives sel hValid sideValue hX hSurvives,
    Finset.card_insert_of_notMem (newSourceEdge_notMem_image sel sideValue x),
    Finset.card_image_of_injective _ (ResolutionCut.oldSourceEdge_injective (cand))]

theorem nonDanglingValency_candidate_ne_one (hValid : data.Valid)
    (vertex : (cand).datum.SourceVertex) :
    nonDanglingValency (cand).datum vertex ≠ 1 :=
  NonDanglingValency.nonDanglingValency_ne_one (cand).datum
    (Prescribed.validCandidate_datum_valid sel hValid).1 vertex

/-- **A block whose star is empty on one side has a dangling new occurrence.** -/
theorem newSourceEdge_isDangling_of_ordinaryStar_empty (hValid : data.Valid)
    (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hEmpty : (ordinaryStar data star anchor x sideValue).card = 0) :
    IsDangling (cand).datum ((cand).newSourceEdge x) := by
  classical
  by_contra hSurvives
  refine nonDanglingValency_candidate_ne_one sel hValid
    (endpointVertex sel sideValue x) ?_
  rw [nonDanglingValency_endpointVertex_of_new_survives sel hValid sideValue hX hSurvives,
    hEmpty]

/-- **A surviving new occurrence forces a survivor on each side.** -/
theorem ordinaryStar_card_ne_zero_of_new_survives (hValid : data.Valid)
    (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hSurvives : ¬ IsDangling (cand).datum ((cand).newSourceEdge x)) :
    (ordinaryStar data star anchor x sideValue).card ≠ 0 := by
  intro hEmpty
  exact hSurvives (newSourceEdge_isDangling_of_ordinaryStar_empty sel hValid sideValue
    hX hEmpty)

/-- **The new occurrence of an ordinary block survives exactly when both sides
carry a surviving retained occurrence.** -/
theorem newSourceEdge_survives_iff_ordinary (hValid : data.Valid) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    ¬ IsDangling (cand).datum ((cand).newSourceEdge x) ↔
      ((ordinaryStar data star anchor x false).card ≠ 0 ∧
        (ordinaryStar data star anchor x true).card ≠ 0) := by
  classical
  constructor
  · intro hSurvives
    exact ⟨ordinaryStar_card_ne_zero_of_new_survives sel hValid false hX hSurvives,
      ordinaryStar_card_ne_zero_of_new_survives sel hValid true hX hSurvives⟩
  · rintro ⟨hFalse, hTrue⟩
    intro hDangling
    have hEnds : (cand).datum.sourceEnds ((cand).newSourceEdge x) =
        (endpointVertex sel false x, endpointVertex sel true x) :=
      sourceEnds_bridgeEdge sel x
    have hNonZero : ∀ sideValue : Bool,
        nonDanglingValency (cand).datum (endpointVertex sel sideValue x) ≠ 0 := by
      intro sideValue
      rw [nonDanglingValency_endpointVertex_of_new_dangling sel hValid sideValue hX
        hDangling]
      cases sideValue
      · exact hFalse
      · exact hTrue
    rcases hDangling with hSide | hSide
    · obtain ⟨cut⟩ := hSide
      refine hNonZero false ?_
      have hFst := congrArg Prod.fst hEnds
      have hZero := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side
        _ cut cut.left_mem
      rwa [hFst] at hZero
    · obtain ⟨cut⟩ := hSide
      refine hNonZero true ?_
      have hSnd := congrArg Prod.snd hEnds
      have hZero := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side
        _ cut cut.left_mem
      rwa [hSnd] at hZero

/-! ## 3.  The descent across an ordinary block -/

theorem incident_retainedEdge_endpointVertex (hValid : data.Valid) (sideValue : Bool)
    {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    {old : NonDanglingEdge data}
    (hOld : old.1 ∈ ordinaryStar data star anchor x sideValue) :
    Incident (cand).datum (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old).1
      (endpointVertex sel sideValue x) := by
  rw [mem_ordinaryStar] at hOld
  exact (incident_oldSourceEdge_endpointVertex_iff sel sideValue hX old.1).mpr
    ⟨hOld.1.2, hOld.2⟩

/-- A retained survivor which is alone on its side of an ordinary block lies on
the stable row of that block's surviving new occurrence. -/
theorem stablePath_retainedEdge_eq_newSourceEdge (hValid : data.Valid) (sideValue : Bool)
    {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    {old : NonDanglingEdge data}
    (hOld : old.1 ∈ ordinaryStar data star anchor x sideValue)
    (hCard : (ordinaryStar data star anchor x sideValue).card = 1)
    (hSurvives : ¬ IsDangling (cand).datum ((cand).newSourceEdge x)) :
    (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old).stablePath =
      NonDanglingEdge.stablePath
        (⟨(cand).newSourceEdge x, hSurvives⟩ : NonDanglingEdge (cand).datum) := by
  refine stablePath_eq_of_consecutive ⟨?_, endpointVertex sel sideValue x, ?_, ?_, ?_⟩
  · intro hEq
    exact newSourceEdge_ne_oldSourceEdge sel x old.1 (congrArg Subtype.val hEq).symm
  · exact incident_retainedEdge_endpointVertex sel hValid sideValue hX hOld
  · exact newSourceEdge_incident_endpointVertex sel sideValue x
  · rw [nonDanglingValency_endpointVertex_of_new_survives sel hValid sideValue hX
      hSurvives, hCard]

/-- Two retained survivors on the *same* side of an ordinary block of surviving
valency two are consecutive at that endpoint of the candidate. -/
theorem stablePath_retainedEdge_eq_of_same_side (hValid : data.Valid) (sideValue : Bool)
    {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    {first second : NonDanglingEdge data} (hNe : first ≠ second)
    (hFirst : first.1 ∈ ordinaryStar data star anchor x sideValue)
    (hSecond : second.1 ∈ ordinaryStar data star anchor x sideValue)
    (hCard : (ordinaryStar data star anchor x sideValue).card = 2)
    (hDangling : IsDangling (cand).datum ((cand).newSourceEdge x)) :
    (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 first).stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 second).stablePath := by
  refine stablePath_eq_of_consecutive ⟨?_, endpointVertex sel sideValue x, ?_, ?_, ?_⟩
  · exact fun hEq ↦ hNe (ResolutionAwayFromWall.retainedEdge_injective (cand) hValid.1 hEq)
  · exact incident_retainedEdge_endpointVertex sel hValid sideValue hX hFirst
  · exact incident_retainedEdge_endpointVertex sel hValid sideValue hX hSecond
  · rw [nonDanglingValency_endpointVertex_of_new_dangling sel hValid sideValue hX
      hDangling, hCard]

/-- **The ordinary-block census, discharged.**  `OrdinaryBlockDescent` holds for
every wall datum and every valency-two anchor; no ordinary-block valency bound
and no further receipt is needed. -/
theorem ordinaryBlockDescent (hValid : data.Valid) : OrdinaryBlockDescent sel hValid := by
  classical
  intro first second vertex hAt hX hNe hFirst hSecond hValency
  set x := vertex.1.2 with hx
  have hVertex : data.sourceEndpoint wall x = vertex :=
    (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
  have hFirst' : Incident data first.1 (data.sourceEndpoint wall x) := by
    rw [hVertex]; exact hFirst
  have hSecond' : Incident data second.1 (data.sourceEndpoint wall x) := by
    rw [hVertex]; exact hSecond
  have hValNew : nonDanglingValency data (data.sourceEndpoint wall x) = 2 := by
    rw [hVertex]; exact hValency
  have hNeVal : first.1 ≠ second.1 := fun h ↦ hNe (Subtype.ext h)
  have hPairCard : ({first.1, second.1} : Finset data.SourceEdge).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hNeVal), Finset.card_singleton]
  have hSum := card_ordinaryStar_add (data := data) (star := star) (anchor := anchor) x
  rw [hValNew] at hSum
  have hMemFirst : ∀ sideValue : Bool,
      Prescribed.rightAssignment data star anchor first.1.1.1 = sideValue →
        first.1 ∈ ordinaryStar data star anchor x sideValue := by
    intro sideValue hSide
    exact (mem_ordinaryStar first.1).mpr ⟨⟨first.2, hFirst'⟩, hSide⟩
  have hMemSecond : ∀ sideValue : Bool,
      Prescribed.rightAssignment data star anchor second.1.1.1 = sideValue →
        second.1 ∈ ordinaryStar data star anchor x sideValue := by
    intro sideValue hSide
    exact (mem_ordinaryStar second.1).mpr ⟨⟨second.2, hSecond'⟩, hSide⟩
  by_cases hSame : Prescribed.rightAssignment data star anchor first.1.1.1 =
      Prescribed.rightAssignment data star anchor second.1.1.1
  · -- Both survivors sit on one side: the new occurrence is dangling.
    have hTwo : ∀ sideValue : Bool,
        first.1 ∈ ordinaryStar data star anchor x sideValue →
        second.1 ∈ ordinaryStar data star anchor x sideValue →
        (ordinaryStar data star anchor x sideValue).card = 2 ∧
          (ordinaryStar data star anchor x (!sideValue)).card = 0 := by
      intro sideValue hF hS
      have hSub : ({first.1, second.1} : Finset data.SourceEdge) ⊆
          ordinaryStar data star anchor x sideValue := by
        intro e he
        rw [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact hF
        · exact hS
      have hGe : 2 ≤ (ordinaryStar data star anchor x sideValue).card := by
        rw [← hPairCard]
        exact Finset.card_le_card hSub
      cases sideValue
      · simp only [Bool.not_false]
        omega
      · simp only [Bool.not_true]
        omega
    have hF := hMemFirst _ rfl
    have hS := hMemSecond _ hSame.symm
    obtain ⟨hCardTwo, hCardZero⟩ := hTwo _ hF hS
    exact stablePath_retainedEdge_eq_of_same_side sel hValid _ hX hNe hF hS hCardTwo
      (newSourceEdge_isDangling_of_ordinaryStar_empty sel hValid _ hX hCardZero)
  · -- One survivor on each side: the new occurrence survives and carries the row.
    have hBoolEq : ∀ a b c : Bool, ¬ (a = b) → ¬ (c = a) → c = b := by decide
    have hNonempty : ∀ sideValue : Bool,
        (ordinaryStar data star anchor x sideValue).Nonempty := by
      intro sideValue
      by_cases hCase : sideValue = Prescribed.rightAssignment data star anchor first.1.1.1
      · rw [hCase]
        exact ⟨first.1, hMemFirst _ rfl⟩
      · rw [hBoolEq _ _ sideValue hSame hCase]
        exact ⟨second.1, hMemSecond _ rfl⟩
    have hCardAll : ∀ sideValue : Bool,
        (ordinaryStar data star anchor x sideValue).card = 1 := by
      have h1 := (hNonempty false).card_pos
      have h2 := (hNonempty true).card_pos
      intro sideValue
      cases sideValue
      · omega
      · omega
    have hSurvives : ¬ IsDangling (cand).datum ((cand).newSourceEdge x) :=
      (newSourceEdge_survives_iff_ordinary sel hValid hX).mpr
        ⟨by rw [hCardAll false]; omega, by rw [hCardAll true]; omega⟩
    have hFirstRow := stablePath_retainedEdge_eq_newSourceEdge sel hValid _ hX
      (hMemFirst _ rfl) (hCardAll _) hSurvives
    have hSecondRow := stablePath_retainedEdge_eq_newSourceEdge sel hValid _ hX
      (hMemSecond _ rfl) (hCardAll _) hSurvives
    exact hFirstRow.trans hSecondRow.symm

/-- **`retainedRow`, unconditionally.**  Every stable row of the incoming wall
datum descends to a stable row of the outgoing valency-two candidate, with no
further geometric receipt. -/
noncomputable def retainedRow (hValid : data.Valid) :
    StablePath data → StablePath (cand).datum :=
  NonTrivalentValencyTwoRows.retainedRow source sel hValid (ordinaryBlockDescent sel hValid)

@[simp] theorem retainedRow_mk (hValid : data.Valid) (e : NonDanglingEdge data) :
    retainedRow source sel hValid e.stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 e).stablePath := rfl

end DraismaVargas.LocalCases.NonTrivalentValencyTwoDescent
