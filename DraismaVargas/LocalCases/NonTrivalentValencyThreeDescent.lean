import DraismaVargas.LocalCases.NonTrivalentValencyThreeRows

/-!
# The ordinary-block census and the retained-row descent at a three-valent wall

Source: Vargas, Part II, arXiv:2609.09109, the valency-3 case (subsection `subsec-case-v3`, case
`{v3-nd4}`, base tree `T_2`), read through the labelling conventions of the
combinatorial setup (subsection `subsec-setup-determinants`), together with the
rigidity lemma above `w_0` (`lemma-above-w0`) for the blocks above `w_0` other
than the anchor.

`NonTrivalentValencyThreeRows` proves the anchor picture -- the two trivalent
endpoint classes `A_u` and `A_v` with their exact surviving stars, and
`bridgeEdge_isolated` -- and states `retainedRow` conditionally on the named
`Prop` `NonTrivalentValencyThreeRows.OrdinaryBlockDescent`.  This module
supplies the ordinary-block census and discharges that `Prop`.

## The census

At a wall block `B` **other than the anchor** the candidate installs the single
global background resolution `Prescribed.ordinaryResolution`
(`candidate_resolution_of_not_wall_rel`), the fine resolution of the wall
partition along the doubled direction.  So `B` is split on the `u` side only:
over `v` its vertex is the whole of `B`, while over `u` there is one vertex
`C_u` for every class `C` of `data.edgePartition (Prescribed.doubledEdge source)`
inside `B` (`candidate_vertexPartition_rel_ordinary`, `newEdge_rel_ordinary`).
Writing `star_s(B)` (`ordinaryStar`) for the wall datum's surviving occurrences
at `B` whose target the base tree `T_2` assigns to the side `s` -- so
`star_false(B)` is carried by the doubled direction and `star_true(B)` by the
two simple ones -- the census reads:

* `mem_nonDanglingIncident_endpointVertex_false_ordinary`: a surviving
  occurrence at the vertex over the class of the sheet `x` is either the
  retained doubled-direction occurrence of `x` (`doubledOccurrence`) or that
  class's own new occurrence;
* `newSourceEdge_survives_iff_ordinary`: hence the new occurrence of a class `C`
  survives **exactly** when `C` carries a doubled-direction survivor, since
  surviving valency one is impossible
  (`NonDanglingValency.nonDanglingValency_ne_one`).  Consequently `nd(C_u) = 2`
  when `C` carries a survivor (`nonDanglingValency_endpointVertex_false_ordinary`)
  and `nd(C_u) = 0` otherwise;
* `nonDanglingIncident_endpointVertex_true_ordinary`: the trivalent end carries
  the retained copies of `star_true(B)` together with one new occurrence per
  member of `star_false(B)`, the map `old ↦ newSourceEdge old.1.2` being
  injective there (`newSourceEdge_sheet_injOn`);
* `nonDanglingValency_endpointVertex_true_ordinary`: so
  `nd(B_v) = |star_true(B)| + |star_false(B)| = nd(B)`, the block's own
  surviving valency.

Dangling-ness of a retained occurrence transports between `data` and the
candidate through `ResolutionPruning.isDangling_oldSourceEdge_iff`, whose genus
hypothesis is `NonTrivalentValencyThreeRows.candidate_sourceGenus`.

## What is proved

* `ordinaryBlockDescent`: `NonTrivalentValencyThreeRows.OrdinaryBlockDescent`
  holds for every wall datum and every valency-three anchor, with no hypothesis
  beyond the standing `data.Valid` and `DanglingEdgeNoGlue data`.  Two
  survivors at a divalent ordinary block are carried to the trivalent end by
  `exists_trivalentEndEdge` -- a retained survivor of a simple direction stays
  itself, a doubled-direction survivor is replaced by the new occurrence of its
  own fine class, which lies on its row by
  `stablePath_retainedEdge_eq_newSourceEdge` -- and the two representatives are
  distinct and consecutive at `B_v`, which is divalent by the census.
* `retainedRow` and `retainedRow_mk`: `NonTrivalentValencyThreeRows.retainedRow`
  becomes unconditional.

## What is not proved here

The row *equivalence* and the resulting labelling; those are
`NonTrivalentValencyThreeRowEquiv.rowEquiv` and `...labelling`, which build on
this module's census.  No ordinary-block valency bound `nd(B) <= 3` is used or
assumed anywhere in the valency-three construction.

## Consumers

`NonTrivalentValencyThreeRowEquiv`, `NonTrivalentValencyThreeRows.retainedRow`
(through `OrdinaryBlockDescent`), and the boundary dispatcher for Part II case
`{v3-nd4}`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeDescent

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.W3R1SourceProfile
open DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeRows

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall}
  (source : ThreeBranchAnchor data star anchor)
  (hNoGlue : DanglingEdgeNoGlue data) (hValid : data.Valid)

local notation "cand" => (Prescribed.validCandidate source hNoGlue hValid)

/-! ## 1.  The single background resolution at an ordinary wall block -/

@[simp] theorem ordinaryResolution_left :
    (Prescribed.ordinaryResolution source).left =
      data.edgePartition (Prescribed.doubledEdge source) := rfl

@[simp] theorem ordinaryResolution_right :
    (Prescribed.ordinaryResolution source).right = data.vertexPartition wall := rfl

@[simp] theorem ordinaryResolution_newEdge :
    (Prescribed.ordinaryResolution source).newEdge =
      data.edgePartition (Prescribed.doubledEdge source) := rfl

/-- The candidate's endpoint partition over an ordinary wall block: the
doubled-direction occurrence partition over the divalent end `u`, the
unchanged wall partition over the trivalent end `v`. -/
noncomputable def ordinaryPartition (source : ThreeBranchAnchor data star anchor)
    (sideValue : Bool) : SheetPartition degree :=
  if sideValue then data.vertexPartition wall
  else data.edgePartition (Prescribed.doubledEdge source)

@[simp] theorem ordinaryPartition_false :
    ordinaryPartition source false =
      data.edgePartition (Prescribed.doubledEdge source) := rfl

@[simp] theorem ordinaryPartition_true :
    ordinaryPartition source true = data.vertexPartition wall := rfl

theorem ordinaryPartition_refines (sideValue : Bool) :
    (ordinaryPartition source sideValue).Refines (data.vertexPartition wall) := by
  cases sideValue
  · exact Prescribed.doubledEdge_refines source
  · exact SheetPartition.Refines.refl _

theorem not_rel_repr {a : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    ¬ (data.vertexPartition wall).Rel anchor.1 ((data.vertexPartition wall).repr a) :=
  fun h ↦ hA (h.trans ((data.vertexPartition wall).rel_repr_right a).symm)

/-- Over an ordinary wall block the candidate's endpoint partitions are the
doubled-direction partition on the `u` side and the unchanged wall partition
on the `v` side. -/
theorem candidate_vertexPartition_rel_ordinary (sideValue : Bool) {a b : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    ((cand).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall)).Rel a b ↔
      (ordinaryPartition source sideValue).Rel a b := by
  have hOrd := candidate_resolution_of_not_wall_rel source hNoGlue hValid
    ((data.vertexPartition wall).repr a) (not_rel_repr hA)
  cases sideValue
  · show ((cand).datum.vertexPartition (oldVertex target wall)).Rel a b ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
    refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
      (fun blk ↦ ((cand).resolution blk).left)
      (fun blk ↦ ((cand).contracts blk).left_refines) a b) ?_
    rw [hOrd]
    rfl
  · show ((cand).datum.vertexPartition (freshVertex target)).Rel a b ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]
    refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
      (fun blk ↦ ((cand).resolution blk).right)
      (fun blk ↦ ((cand).contracts blk).right_refines) a b) ?_
    rw [hOrd]
    rfl

/-- The same for the new-edge partition: an ordinary block is split exactly
along the doubled direction. -/
theorem newEdge_rel_ordinary {a b : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.Rel a b ↔
      (data.edgePartition (Prescribed.doubledEdge source)).Rel a b := by
  have hOrd := candidate_resolution_of_not_wall_rel source hNoGlue hValid
    ((data.vertexPartition wall).repr a) (not_rel_repr hA)
  refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
    (fun blk ↦ ((cand).resolution blk).newEdge)
    (fun blk ↦ ((cand).resolution blk).edge_refines_left.trans
      ((cand).contracts blk).left_refines) a b) ?_
  rw [hOrd]
  rfl

/-! ## 2.  The doubled-direction occurrence of a sheet, and incidences -/

theorem newSourceEdge_ne_oldSourceEdge (s : Fin degree) (old : data.SourceEdge) :
    (cand).newSourceEdge s ≠ (cand).oldSourceEdge old := by
  intro hEq
  have h := congrArg (fun edge : (cand).datum.SourceEdge ↦ edge.1.1) hEq
  have hNone := (occurrenceEquiv target wall (cand).right).injective h
  cases hNone

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

theorem sourceEndpoint_eq_of_rel {a b : Fin degree}
    (hRel : (data.vertexPartition wall).Rel a b) :
    data.sourceEndpoint wall a = data.sourceEndpoint wall b := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hRel

/-- The doubled-direction occurrence carried by a sheet.  Over an ordinary
wall block this is the only old occurrence the base tree `T_2` sends to the
divalent end `u`. -/
noncomputable def doubledOccurrence (source : ThreeBranchAnchor data star anchor)
    (x : Fin degree) : data.SourceEdge :=
  data.sourceEdge (Prescribed.doubledEdge source) x

@[simp] theorem doubledOccurrence_target (x : Fin degree) :
    (doubledOccurrence source x).1.1 = Prescribed.doubledEdge source := rfl

@[simp] theorem doubledOccurrence_sheet (x : Fin degree) :
    (doubledOccurrence source x).1.2 =
      (data.edgePartition (Prescribed.doubledEdge source)).repr x := rfl

theorem rightAssignment_doubledOccurrence (x : Fin degree) :
    Prescribed.rightAssignment source (doubledOccurrence source x).1.1 = false :=
  Prescribed.rightAssignment_doubled source

theorem incident_doubledOccurrence (x : Fin degree) :
    Incident data (doubledOccurrence source x) (data.sourceEndpoint wall x) :=
  (incident_sourceEndpoint_wall_iff x _).mpr
    ⟨Prescribed.doubledEdge_mem_incidentEdges source,
      (Prescribed.doubledEdge_refines source).rel
        ((data.edgePartition (Prescribed.doubledEdge source)).rel_repr_right x)⟩

theorem doubledOccurrence_eq_of_rel {a b : Fin degree}
    (hRel : (data.edgePartition (Prescribed.doubledEdge source)).Rel a b) :
    doubledOccurrence source a = doubledOccurrence source b := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hRel

/-- An old occurrence which the base tree sends to the `u` side and whose
sheet lies in the doubled-direction class of `x` is literally the
doubled-direction occurrence of `x`. -/
theorem eq_doubledOccurrence {x : Fin degree} {old : data.SourceEdge}
    (hSide : Prescribed.rightAssignment source old.1.1 = false)
    (hRel : (data.edgePartition (Prescribed.doubledEdge source)).Rel x old.1.2) :
    old = doubledOccurrence source x := by
  have hTarget : old.1.1 = Prescribed.doubledEdge source :=
    (Prescribed.rightAssignment_eq_false_iff source old.1.1).mp hSide
  have hRepr : (data.edgePartition (Prescribed.doubledEdge source)).repr old.1.2 = old.1.2 := by
    have h := old.2
    rw [hTarget] at h
    exact h
  apply Subtype.ext
  apply Prod.ext
  · exact hTarget
  · show old.1.2 = (data.edgePartition (Prescribed.doubledEdge source)).repr x
    exact (hRel.trans hRepr).symm

/-! ### Incidence at the two ordinary endpoint vertices -/

theorem incident_endpointVertex_iff (sideValue : Bool) (x : Fin degree)
    (e : (cand).datum.SourceEdge) :
    Incident (cand).datum e (endpointVertex source hNoGlue hValid sideValue x) ↔
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

theorem endpointVertex_eq_ordinary (sideValue : Bool) {a b : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a)
    (hRel : (ordinaryPartition source sideValue).Rel a b) :
    endpointVertex source hNoGlue hValid sideValue a =
      endpointVertex source hNoGlue hValid sideValue b := by
  apply (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr
  refine ⟨rfl, ?_⟩
  refine Eq.trans ?_ (((cand).datum.vertexPartition
    (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right b)
  exact (candidate_vertexPartition_rel_ordinary source hNoGlue hValid sideValue hA).mpr hRel

/-- **Retained occurrences at an ordinary block.**  The candidate's endpoint
vertex over the doubled-direction class of `x` (resp. over the whole wall
block of `x`) sees exactly the wall datum's occurrences at that class
(resp. block) whose target the base tree assigns to that side. -/
theorem incident_oldSourceEdge_endpointVertex_iff (sideValue : Bool) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (old : data.SourceEdge) :
    Incident (cand).datum ((cand).oldSourceEdge old)
        (endpointVertex source hNoGlue hValid sideValue x) ↔
      ((old.1.1 ∈ GluingDatum.incidentEdges wall ∧
          (ordinaryPartition source sideValue).Rel x old.1.2) ∧
        Prescribed.rightAssignment source old.1.1 = sideValue) := by
  rw [incident_endpointVertex_iff, BalancedGlobal.Candidate.oldSourceEdge_target,
    mem_incidentEdges_endpoint_old, BalancedGlobal.Candidate.oldSourceEdge_sheet,
    candidate_vertexPartition_rel_ordinary source hNoGlue hValid sideValue hX]
  tauto

theorem newEdge_refines_wall :
    (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
      (cand).contracts).newEdge.Refines (data.vertexPartition wall) :=
  (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
    (cand).contracts).edge_refines_left.trans
      (LocalResolution.pasteLeft_refines (data.vertexPartition wall) (cand).resolution
        (cand).contracts)

/-- Two new occurrences over an ordinary block coincide exactly when their
sheets lie in one doubled-direction class. -/
theorem newSourceEdge_eq_iff_ordinary {a b : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    (cand).newSourceEdge a = (cand).newSourceEdge b ↔
      (data.edgePartition (Prescribed.doubledEdge source)).Rel a b := by
  constructor
  · intro hEq
    refine (newEdge_rel_ordinary source hNoGlue hValid hA).mp ?_
    exact congrArg (fun e : (cand).datum.SourceEdge ↦ e.1.2) hEq
  · intro hRel
    exact newSourceEdge_eq_of_rel source hNoGlue hValid
      ((newEdge_rel_ordinary source hNoGlue hValid hA).mpr hRel)

/-- The new occurrence of a doubled-direction class meets both of the
endpoint vertices it joins. -/
theorem newSourceEdge_incident_endpointVertex (sideValue : Bool) (x : Fin degree) :
    Incident (cand).datum ((cand).newSourceEdge x)
      (endpointVertex source hNoGlue hValid sideValue x) :=
  bridgeEdge_incident source hNoGlue hValid sideValue x

/-- **New occurrences at the divalent end.**  Over the `u` side an ordinary
block splits into its doubled-direction classes, so the only new occurrence
meeting the endpoint vertex of the class of `x` is that class's own. -/
theorem newSourceEdge_eq_of_incident_false {x y : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hIncident : Incident (cand).datum ((cand).newSourceEdge y)
      (endpointVertex source hNoGlue hValid false x)) :
    (cand).newSourceEdge y = (cand).newSourceEdge x := by
  have hRel := ((incident_endpointVertex_iff source hNoGlue hValid false x _).mp hIncident).2
  rw [candidate_vertexPartition_rel_ordinary source hNoGlue hValid false hX] at hRel
  have hSheet : ((cand).newSourceEdge y).1.2 =
      (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.repr y := rfl
  rw [hSheet] at hRel
  have hRelD : (data.edgePartition (Prescribed.doubledEdge source)).Rel x
      ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.repr y) := hRel
  have hBack : (data.vertexPartition wall).Rel
      ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.repr y) y :=
    (newEdge_refines_wall source hNoGlue hValid).rel
      ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.rel_repr_left y)
  have hY : ¬ (data.vertexPartition wall).Rel anchor.1 y := by
    intro h
    exact hX (h.trans (((Prescribed.doubledEdge_refines source).rel hRelD).trans hBack).symm)
  refine (newSourceEdge_eq_iff_ordinary source hNoGlue hValid hY).mpr ?_
  refine Eq.trans ?_ hRelD.symm
  exact (newEdge_rel_ordinary source hNoGlue hValid hY).mp
    (((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
      (cand).contracts).newEdge.rel_repr_left y).symm)

/-- **New occurrences at the trivalent end.**  Over the `v` side the block is
not split, so a new occurrence meeting its endpoint vertex is the new
occurrence of some doubled-direction class of that same block. -/
theorem wall_rel_of_incident_true {x y : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hIncident : Incident (cand).datum ((cand).newSourceEdge y)
      (endpointVertex source hNoGlue hValid true x)) :
    (data.vertexPartition wall).Rel x y := by
  have hRel := ((incident_endpointVertex_iff source hNoGlue hValid true x _).mp hIncident).2
  rw [candidate_vertexPartition_rel_ordinary source hNoGlue hValid true hX] at hRel
  have hSheet : ((cand).newSourceEdge y).1.2 =
      (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.repr y := rfl
  rw [hSheet] at hRel
  refine hRel.trans ?_
  exact (newEdge_refines_wall source hNoGlue hValid).rel
    ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
      (cand).contracts).newEdge.rel_repr_left y)


/-! ## 3.  The wall datum's star at an ordinary block, split by side -/

/-- The wall datum's surviving occurrences at one ordinary block, on one side
of the outgoing base tree `T_2`.  The `false` side carries only the doubled
direction, the `true` side the two simple ones. -/
noncomputable def ordinaryStar (source : ThreeBranchAnchor data star anchor)
    (x : Fin degree) (sideValue : Bool) : Finset data.SourceEdge := by
  classical
  exact (nonDanglingIncident data (data.sourceEndpoint wall x)).filter
    (fun old ↦ Prescribed.rightAssignment source old.1.1 = sideValue)

theorem mem_ordinaryStar {x : Fin degree} {sideValue : Bool} (old : data.SourceEdge) :
    old ∈ ordinaryStar source x sideValue ↔
      ((¬ IsDangling data old ∧ Incident data old (data.sourceEndpoint wall x)) ∧
        Prescribed.rightAssignment source old.1.1 = sideValue) := by
  classical
  rw [ordinaryStar, Finset.mem_filter, mem_nonDanglingIncident]

theorem ordinaryStar_disjoint (x : Fin degree) :
    Disjoint (ordinaryStar source x false) (ordinaryStar source x true) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro old hFalse hTrue
  rw [mem_ordinaryStar] at hFalse hTrue
  rw [hFalse.2] at hTrue
  exact Bool.false_ne_true hTrue.2

theorem ordinaryStar_union (x : Fin degree) :
    ordinaryStar source x false ∪ ordinaryStar source x true =
      nonDanglingIncident data (data.sourceEndpoint wall x) := by
  classical
  ext old
  rw [Finset.mem_union, mem_ordinaryStar, mem_ordinaryStar, mem_nonDanglingIncident]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    cases Prescribed.rightAssignment source old.1.1
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr ⟨h, rfl⟩

/-- **The two sides partition the block's surviving star.** -/
theorem card_ordinaryStar_add (x : Fin degree) :
    (ordinaryStar source x false).card + (ordinaryStar source x true).card =
      nonDanglingValency data (data.sourceEndpoint wall x) := by
  classical
  rw [← Finset.card_union_of_disjoint (ordinaryStar_disjoint source x),
    ordinaryStar_union, card_nonDanglingIncident]

theorem ordinaryStar_eq_of_rel {a b : Fin degree}
    (hRel : (data.vertexPartition wall).Rel a b) (sideValue : Bool) :
    ordinaryStar source a sideValue = ordinaryStar source b sideValue := by
  classical
  ext old
  rw [mem_ordinaryStar, mem_ordinaryStar, sourceEndpoint_eq_of_rel hRel]

/-- A retained survivor on the divalent side of a wall block is the
doubled-direction occurrence of its own sheet. -/
theorem eq_doubledOccurrence_self {old : data.SourceEdge}
    (hSide : Prescribed.rightAssignment source old.1.1 = false) :
    old = doubledOccurrence source old.1.2 :=
  eq_doubledOccurrence source hSide rfl

theorem wall_rel_of_mem_ordinaryStar {x : Fin degree} {sideValue : Bool}
    {old : data.SourceEdge} (hOld : old ∈ ordinaryStar source x sideValue) :
    (data.vertexPartition wall).Rel x old.1.2 :=
  ((incident_sourceEndpoint_wall_iff x old).mp
    ((mem_ordinaryStar source old).mp hOld).1.2).2

theorem mem_incidentEdges_of_mem_ordinaryStar {x : Fin degree} {sideValue : Bool}
    {old : data.SourceEdge} (hOld : old ∈ ordinaryStar source x sideValue) :
    old.1.1 ∈ GluingDatum.incidentEdges wall :=
  ((incident_sourceEndpoint_wall_iff x old).mp
    ((mem_ordinaryStar source old).mp hOld).1.2).1

/-! ## 4.  The census at the divalent end `C_u` of an ordinary block

Over the divalent end the block `B` is split into the classes of the doubled
direction.  The class `C` of the sheet `x` carries at most two surviving
occurrences: the retained doubled-direction occurrence of `x`, and the new
occurrence of `C`. -/

theorem incident_oldSourceEdge_doubledOccurrence {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    Incident (cand).datum ((cand).oldSourceEdge (doubledOccurrence source x))
      (endpointVertex source hNoGlue hValid false x) := by
  have hMem : (doubledOccurrence source x).1.1 ∈ GluingDatum.incidentEdges wall :=
    Prescribed.doubledEdge_mem_incidentEdges source
  have hRel : (ordinaryPartition source false).Rel x (doubledOccurrence source x).1.2 :=
    (data.edgePartition (Prescribed.doubledEdge source)).rel_repr_right x
  have hSide : Prescribed.rightAssignment source (doubledOccurrence source x).1.1 = false :=
    Prescribed.rightAssignment_doubled source
  exact (incident_oldSourceEdge_endpointVertex_iff source hNoGlue hValid false hX _).mpr
    ⟨⟨hMem, hRel⟩, hSide⟩

/-- **The census at a divalent ordinary endpoint.**  A surviving occurrence at
the candidate's endpoint vertex over the doubled-direction class of `x` is
either the retained doubled-direction occurrence of `x` or that class's own new
occurrence. -/
theorem mem_nonDanglingIncident_endpointVertex_false_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (e : (cand).datum.SourceEdge) :
    e ∈ nonDanglingIncident (cand).datum
        (endpointVertex source hNoGlue hValid false x) ↔
      ((e = (cand).oldSourceEdge (doubledOccurrence source x) ∧
          ¬ IsDangling data (doubledOccurrence source x)) ∨
        (e = (cand).newSourceEdge x ∧
          ¬ IsDangling (cand).datum ((cand).newSourceEdge x))) := by
  classical
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨⟨-, hRel⟩, hSide⟩ :=
        (incident_oldSourceEdge_endpointVertex_iff source hNoGlue hValid false hX old).mp
          hIncident
      have hEq : old = doubledOccurrence source x := eq_doubledOccurrence source hSide hRel
      refine Or.inl ⟨congrArg (cand).oldSourceEdge hEq, ?_⟩
      intro hDangling
      exact hSurvives ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand) hValid
        (candidate_sourceGenus source hNoGlue hValid) old).mpr (hEq ▸ hDangling))
    · have hEq := newSourceEdge_eq_of_incident_false source hNoGlue hValid hX hIncident
      exact Or.inr ⟨hEq, hEq ▸ hSurvives⟩
  · rintro (⟨rfl, hSurv⟩ | ⟨rfl, hSurv⟩)
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨ResolutionSurvival.not_isDangling_oldSourceEdge (cand) hValid.1 _ hSurv,
          incident_oldSourceEdge_doubledOccurrence source hNoGlue hValid hX⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨hSurv, newSourceEdge_incident_endpointVertex source hNoGlue hValid false x⟩

theorem nonDanglingIncident_endpointVertex_false_subset_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    nonDanglingIncident (cand).datum
        (endpointVertex source hNoGlue hValid false x) ⊆
      {(cand).oldSourceEdge (doubledOccurrence source x), (cand).newSourceEdge x} := by
  classical
  intro e he
  rcases (mem_nonDanglingIncident_endpointVertex_false_ordinary source hNoGlue hValid
    hX e).mp he with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem nonDanglingValency_candidate_ne_one (vertex : (cand).datum.SourceVertex) :
    nonDanglingValency (cand).datum vertex ≠ 1 :=
  NonDanglingValency.nonDanglingValency_ne_one (cand).datum
    (Prescribed.validCandidate_datum_valid source hNoGlue hValid).1 vertex

/-- **The new occurrence of a fine class survives exactly when the class
carries a doubled-direction survivor.**  Surviving valency one is impossible,
and the divalent endpoint over the class sees nothing else. -/
theorem newSourceEdge_survives_iff_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    ¬ IsDangling (cand).datum ((cand).newSourceEdge x) ↔
      ¬ IsDangling data (doubledOccurrence source x) := by
  classical
  constructor
  · intro hNew hOldDangling
    refine nonDanglingValency_candidate_ne_one source hNoGlue hValid
      (endpointVertex source hNoGlue hValid false x) ?_
    have hEq : nonDanglingIncident (cand).datum
        (endpointVertex source hNoGlue hValid false x) = {(cand).newSourceEdge x} := by
      refine Finset.Subset.antisymm ?_ ?_
      · intro e he
        rcases (mem_nonDanglingIncident_endpointVertex_false_ordinary source hNoGlue hValid
          hX e).mp he with ⟨-, hSurv⟩ | ⟨rfl, -⟩
        · exact absurd hOldDangling hSurv
        · exact Finset.mem_singleton_self _
      · intro e he
        rw [Finset.mem_singleton] at he
        subst he
        exact (mem_nonDanglingIncident_endpointVertex_false_ordinary source hNoGlue hValid
          hX _).mpr (Or.inr ⟨rfl, hNew⟩)
    rw [← card_nonDanglingIncident, hEq, Finset.card_singleton]
  · intro hOld hNewDangling
    refine nonDanglingValency_candidate_ne_one source hNoGlue hValid
      (endpointVertex source hNoGlue hValid false x) ?_
    have hEq : nonDanglingIncident (cand).datum
        (endpointVertex source hNoGlue hValid false x) =
          {(cand).oldSourceEdge (doubledOccurrence source x)} := by
      refine Finset.Subset.antisymm ?_ ?_
      · intro e he
        rcases (mem_nonDanglingIncident_endpointVertex_false_ordinary source hNoGlue hValid
          hX e).mp he with ⟨rfl, -⟩ | ⟨-, hSurv⟩
        · exact Finset.mem_singleton_self _
        · exact absurd hNewDangling hSurv
      · intro e he
        rw [Finset.mem_singleton] at he
        subst he
        exact (mem_nonDanglingIncident_endpointVertex_false_ordinary source hNoGlue hValid
          hX _).mpr (Or.inl ⟨rfl, hOld⟩)
    rw [← card_nonDanglingIncident, hEq, Finset.card_singleton]

/-- **The divalent end over a class with a survivor is divalent.** -/
theorem nonDanglingValency_endpointVertex_false_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (hOld : ¬ IsDangling data (doubledOccurrence source x)) :
    nonDanglingValency (cand).datum
      (endpointVertex source hNoGlue hValid false x) = 2 := by
  classical
  have hNew : ¬ IsDangling (cand).datum ((cand).newSourceEdge x) :=
    (newSourceEdge_survives_iff_ordinary source hNoGlue hValid hX).mpr hOld
  have hEq : nonDanglingIncident (cand).datum
      (endpointVertex source hNoGlue hValid false x) =
        {(cand).oldSourceEdge (doubledOccurrence source x), (cand).newSourceEdge x} := by
    refine Finset.Subset.antisymm
      (nonDanglingIncident_endpointVertex_false_subset_ordinary source hNoGlue hValid hX) ?_
    intro e he
    rw [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact (mem_nonDanglingIncident_endpointVertex_false_ordinary source hNoGlue hValid
        hX _).mpr (Or.inl ⟨rfl, hOld⟩)
    · exact (mem_nonDanglingIncident_endpointVertex_false_ordinary source hNoGlue hValid
        hX _).mpr (Or.inr ⟨rfl, hNew⟩)
  have hNotMem : (cand).oldSourceEdge (doubledOccurrence source x) ∉
      ({(cand).newSourceEdge x} : Finset (cand).datum.SourceEdge) := by
    rw [Finset.mem_singleton]
    intro h
    exact newSourceEdge_ne_oldSourceEdge source hNoGlue hValid x
      (doubledOccurrence source x) h.symm
  rw [← card_nonDanglingIncident, hEq, Finset.card_insert_of_notMem hNotMem,
    Finset.card_singleton]


/-! ## 5.  The census at the trivalent end `B_v` of an ordinary block

Over the trivalent end the block is not split: its endpoint vertex carries the
retained survivors of the two simple directions together with one new
occurrence for every doubled-direction survivor of the block.  So its surviving
valency is exactly the block's. -/

theorem not_rel_anchor_of_mem_ordinaryStar {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) {sideValue : Bool}
    {old : data.SourceEdge} (hOld : old ∈ ordinaryStar source x sideValue) :
    ¬ (data.vertexPartition wall).Rel anchor.1 old.1.2 :=
  fun h ↦ hX (h.trans (wall_rel_of_mem_ordinaryStar source hOld).symm)

/-- A doubled-direction survivor of an ordinary block is the doubled-direction
occurrence of its own fine class, and that class's new occurrence survives. -/
theorem newSourceEdge_survives_of_mem_ordinaryStar {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    {old : data.SourceEdge} (hOld : old ∈ ordinaryStar source x false) :
    ¬ IsDangling (cand).datum ((cand).newSourceEdge old.1.2) := by
  refine (newSourceEdge_survives_iff_ordinary source hNoGlue hValid
    (not_rel_anchor_of_mem_ordinaryStar source hX hOld)).mpr ?_
  rw [← eq_doubledOccurrence_self source ((mem_ordinaryStar source old).mp hOld).2]
  exact ((mem_ordinaryStar source old).mp hOld).1.1

theorem incident_newSourceEdge_endpointVertex_true {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    {sideValue : Bool} {old : data.SourceEdge}
    (hOld : old ∈ ordinaryStar source x sideValue) :
    Incident (cand).datum ((cand).newSourceEdge old.1.2)
      (endpointVertex source hNoGlue hValid true x) := by
  have hRel : (ordinaryPartition source true).Rel x old.1.2 :=
    wall_rel_of_mem_ordinaryStar source hOld
  rw [endpointVertex_eq_ordinary source hNoGlue hValid true hX hRel]
  exact newSourceEdge_incident_endpointVertex source hNoGlue hValid true old.1.2

/-- The new occurrence of the fine class of a sheet is the new occurrence of
its doubled-direction occurrence. -/
theorem newSourceEdge_doubledOccurrence_sheet {y : Fin degree}
    (hY : ¬ (data.vertexPartition wall).Rel anchor.1 y) :
    (cand).newSourceEdge (doubledOccurrence source y).1.2 = (cand).newSourceEdge y := by
  refine (newSourceEdge_eq_of_rel source hNoGlue hValid ?_).symm
  exact (newEdge_rel_ordinary source hNoGlue hValid hY).mpr
    ((data.edgePartition (Prescribed.doubledEdge source)).rel_repr_right y)

/-- **The census at a trivalent ordinary endpoint.** -/
theorem nonDanglingIncident_endpointVertex_true_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    nonDanglingIncident (cand).datum
        (endpointVertex source hNoGlue hValid true x) =
      (ordinaryStar source x true).image (cand).oldSourceEdge ∪
        (ordinaryStar source x false).image
          (fun old : data.SourceEdge ↦ (cand).newSourceEdge old.1.2) := by
  classical
  ext e
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨⟨hTargetMem, hRel⟩, hSide⟩ :=
        (incident_oldSourceEdge_endpointVertex_iff source hNoGlue hValid true hX old).mp
          hIncident
      refine Or.inl ⟨old, (mem_ordinaryStar source old).mpr ⟨⟨?_, ?_⟩, hSide⟩, rfl⟩
      · intro hDangling
        exact hSurvives ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand) hValid
          (candidate_sourceGenus source hNoGlue hValid) old).mpr hDangling)
      · exact (incident_sourceEndpoint_wall_iff x old).mpr ⟨hTargetMem, hRel⟩
    · have hWallRel : (data.vertexPartition wall).Rel x y :=
        wall_rel_of_incident_true source hNoGlue hValid hX hIncident
      have hY : ¬ (data.vertexPartition wall).Rel anchor.1 y :=
        fun h ↦ hX (h.trans hWallRel.symm)
      refine Or.inr ⟨doubledOccurrence source y, (mem_ordinaryStar source _).mpr
        ⟨⟨(newSourceEdge_survives_iff_ordinary source hNoGlue hValid hY).mp hSurvives, ?_⟩,
          Prescribed.rightAssignment_doubled source⟩,
        newSourceEdge_doubledOccurrence_sheet source hNoGlue hValid hY⟩
      rw [sourceEndpoint_eq_of_rel hWallRel]
      exact incident_doubledOccurrence source y
  · rintro (⟨old, hOld, rfl⟩ | ⟨old, hOld, rfl⟩)
    · refine (mem_nonDanglingIncident _ _ _).mpr
        ⟨ResolutionSurvival.not_isDangling_oldSourceEdge (cand) hValid.1 old
          ((mem_ordinaryStar source old).mp hOld).1.1, ?_⟩
      refine (incident_oldSourceEdge_endpointVertex_iff source hNoGlue hValid true hX old).mpr
        ⟨⟨mem_incidentEdges_of_mem_ordinaryStar source hOld,
          wall_rel_of_mem_ordinaryStar source hOld⟩, ((mem_ordinaryStar source old).mp hOld).2⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨newSourceEdge_survives_of_mem_ordinaryStar source hNoGlue hValid hX hOld,
          incident_newSourceEdge_endpointVertex_true source hNoGlue hValid hX hOld⟩

theorem newSourceEdge_sheet_injOn {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    Set.InjOn (fun old : data.SourceEdge ↦ (cand).newSourceEdge old.1.2)
      (ordinaryStar source x false : Set data.SourceEdge) := by
  classical
  intro a ha b hb hEq
  have hA : a ∈ ordinaryStar source x false := ha
  have hB : b ∈ ordinaryStar source x false := hb
  have hRel : (data.edgePartition (Prescribed.doubledEdge source)).Rel a.1.2 b.1.2 :=
    (newSourceEdge_eq_iff_ordinary source hNoGlue hValid
      (not_rel_anchor_of_mem_ordinaryStar source hX hA)).mp hEq
  rw [eq_doubledOccurrence_self source ((mem_ordinaryStar source a).mp hA).2,
    eq_doubledOccurrence_self source ((mem_ordinaryStar source b).mp hB).2]
  exact doubledOccurrence_eq_of_rel source hRel

/-- **The trivalent end of an ordinary block has the block's own surviving
valency.** -/
theorem nonDanglingValency_endpointVertex_true_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    nonDanglingValency (cand).datum
        (endpointVertex source hNoGlue hValid true x) =
      nonDanglingValency data (data.sourceEndpoint wall x) := by
  classical
  have hDisj : Disjoint ((ordinaryStar source x true).image (cand).oldSourceEdge)
      ((ordinaryStar source x false).image
        (fun old : data.SourceEdge ↦ (cand).newSourceEdge old.1.2)) := by
    refine Finset.disjoint_left.mpr ?_
    intro e heOld heNew
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp heOld
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp heNew
    exact newSourceEdge_ne_oldSourceEdge source hNoGlue hValid b.1.2 a hb
  have hSum := card_ordinaryStar_add source x
  rw [← card_nonDanglingIncident,
    nonDanglingIncident_endpointVertex_true_ordinary source hNoGlue hValid hX,
    Finset.card_union_of_disjoint hDisj,
    Finset.card_image_of_injective _ (ResolutionCut.oldSourceEdge_injective (cand)),
    Finset.card_image_of_injOn (newSourceEdge_sheet_injOn source hNoGlue hValid hX)]
  omega


/-! ## 6.  The retained-row descent across an ordinary block -/

/-- A retained survivor of the doubled direction and the new occurrence of its
own fine class are consecutive at the divalent endpoint over that class. -/
theorem stablePath_retainedEdge_eq_newSourceEdge {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    {old : NonDanglingEdge data} (hOld : old.1 ∈ ordinaryStar source x false) :
    (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old).stablePath =
      NonDanglingEdge.stablePath
        (⟨(cand).newSourceEdge old.1.1.2,
          newSourceEdge_survives_of_mem_ordinaryStar source hNoGlue hValid hX hOld⟩ :
            NonDanglingEdge (cand).datum) := by
  classical
  have hY : ¬ (data.vertexPartition wall).Rel anchor.1 old.1.1.2 :=
    not_rel_anchor_of_mem_ordinaryStar source hX hOld
  have hSide : Prescribed.rightAssignment source old.1.1.1 = false :=
    ((mem_ordinaryStar source old.1).mp hOld).2
  have hDoubled : old.1 = doubledOccurrence source old.1.1.2 :=
    eq_doubledOccurrence_self source hSide
  have hOldSurv : ¬ IsDangling data (doubledOccurrence source old.1.1.2) := by
    rw [← hDoubled]
    exact old.2
  refine stablePath_eq_of_consecutive
    ⟨?_, endpointVertex source hNoGlue hValid false old.1.1.2, ?_, ?_, ?_⟩
  · intro hEq
    exact newSourceEdge_ne_oldSourceEdge source hNoGlue hValid old.1.1.2 old.1
      (congrArg Subtype.val hEq).symm
  · refine (incident_oldSourceEdge_endpointVertex_iff source hNoGlue hValid false hY old.1).mpr
      ⟨⟨mem_incidentEdges_of_mem_ordinaryStar source hOld, ?_⟩, hSide⟩
    exact (rfl : (ordinaryPartition source false).Rel old.1.1.2 old.1.1.2)
  · exact newSourceEdge_incident_endpointVertex source hNoGlue hValid false old.1.1.2
  · exact nonDanglingValency_endpointVertex_false_ordinary source hNoGlue hValid hY hOldSurv

/-- **Every survivor of an ordinary block has a representative at the trivalent
end** carrying the same row of the candidate: the retained occurrence itself on
the `v` side, the new occurrence of its fine class on the `u` side. -/
theorem exists_trivalentEndEdge {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    {old : NonDanglingEdge data} {sideValue : Bool}
    (hOld : old.1 ∈ ordinaryStar source x sideValue) :
    ∃ e : NonDanglingEdge (cand).datum,
      Incident (cand).datum e.1 (endpointVertex source hNoGlue hValid true x) ∧
      e.stablePath = (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old).stablePath ∧
      ((sideValue = true ∧ e.1 = (cand).oldSourceEdge old.1) ∨
        (sideValue = false ∧ e.1 = (cand).newSourceEdge old.1.1.2)) := by
  classical
  cases sideValue
  · refine ⟨⟨(cand).newSourceEdge old.1.1.2,
      newSourceEdge_survives_of_mem_ordinaryStar source hNoGlue hValid hX hOld⟩, ?_,
      (stablePath_retainedEdge_eq_newSourceEdge source hNoGlue hValid hX hOld).symm,
      Or.inr ⟨rfl, rfl⟩⟩
    exact incident_newSourceEdge_endpointVertex_true source hNoGlue hValid hX hOld
  · refine ⟨ResolutionAwayFromWall.retainedEdge (cand) hValid.1 old, ?_, rfl,
      Or.inl ⟨rfl, rfl⟩⟩
    refine (incident_oldSourceEdge_endpointVertex_iff source hNoGlue hValid true hX old.1).mpr
      ⟨⟨mem_incidentEdges_of_mem_ordinaryStar source hOld,
        wall_rel_of_mem_ordinaryStar source hOld⟩,
        ((mem_ordinaryStar source old.1).mp hOld).2⟩

/-- **The ordinary-block descent, discharged.**  At a non-anchor wall block of
surviving valency two the two survivors keep one row of the candidate: on the
same side they are consecutive at the trivalent endpoint, on different sides the
row crosses through the new occurrence of the fine class involved.  No
hypothesis beyond `data.Valid` is used. -/
theorem ordinaryBlockDescent : OrdinaryBlockDescent source hNoGlue hValid := by
  classical
  intro first second vertex hAt hX hNe hFirst hSecond hValency
  have hVertex : data.sourceEndpoint wall vertex.1.2 = vertex :=
    (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
  have hFirst' : Incident data first.1 (data.sourceEndpoint wall vertex.1.2) := by
    rw [hVertex]; exact hFirst
  have hSecond' : Incident data second.1 (data.sourceEndpoint wall vertex.1.2) := by
    rw [hVertex]; exact hSecond
  have hMemFirst : first.1 ∈ ordinaryStar source vertex.1.2
      (Prescribed.rightAssignment source first.1.1.1) :=
    (mem_ordinaryStar source first.1).mpr ⟨⟨first.2, hFirst'⟩, rfl⟩
  have hMemSecond : second.1 ∈ ordinaryStar source vertex.1.2
      (Prescribed.rightAssignment source second.1.1.1) :=
    (mem_ordinaryStar source second.1).mpr ⟨⟨second.2, hSecond'⟩, rfl⟩
  obtain ⟨e1, hInc1, hRow1, hCase1⟩ :=
    exists_trivalentEndEdge source hNoGlue hValid hX hMemFirst
  obtain ⟨e2, hInc2, hRow2, hCase2⟩ :=
    exists_trivalentEndEdge source hNoGlue hValid hX hMemSecond
  have hNeVal : first.1 ≠ second.1 := fun h ↦ hNe (Subtype.ext h)
  have hNd : nonDanglingValency (cand).datum
      (endpointVertex source hNoGlue hValid true vertex.1.2) = 2 := by
    rw [nonDanglingValency_endpointVertex_true_ordinary source hNoGlue hValid hX, hVertex]
    exact hValency
  have hNe12 : e1 ≠ e2 := by
    intro hEq
    have hVal : e1.1 = e2.1 := congrArg Subtype.val hEq
    rcases hCase1 with ⟨hs1, h1⟩ | ⟨hs1, h1⟩ <;> rcases hCase2 with ⟨hs2, h2⟩ | ⟨hs2, h2⟩
    · exact hNeVal (ResolutionCut.oldSourceEdge_injective (cand)
        (by rw [← h1, ← h2, hVal]))
    · exact newSourceEdge_ne_oldSourceEdge source hNoGlue hValid second.1.1.2 first.1
        (by rw [← h2, ← h1, hVal])
    · exact newSourceEdge_ne_oldSourceEdge source hNoGlue hValid first.1.1.2 second.1
        (by rw [← h1, ← h2, hVal])
    · refine hNeVal ?_
      have hStarFirst : first.1 ∈ ordinaryStar source vertex.1.2 false := by
        rw [← hs1]; exact hMemFirst
      have hStarSecond : second.1 ∈ ordinaryStar source vertex.1.2 false := by
        rw [← hs2]; exact hMemSecond
      refine newSourceEdge_sheet_injOn source hNoGlue hValid hX hStarFirst hStarSecond ?_
      show (cand).newSourceEdge first.1.1.2 = (cand).newSourceEdge second.1.1.2
      rw [← h1, ← h2, hVal]
  rw [← hRow1, ← hRow2]
  exact stablePath_eq_of_consecutive
    ⟨hNe12, endpointVertex source hNoGlue hValid true vertex.1.2, hInc1, hInc2, hNd⟩

/-- **`retainedRow`, unconditionally.**  Every stable row of the incoming wall
datum descends to a stable row of the outgoing valency-three candidate, with no
further geometric hypothesis. -/
noncomputable def retainedRow : StablePath data → StablePath (cand).datum :=
  NonTrivalentValencyThreeRows.retainedRow source hNoGlue hValid
    (ordinaryBlockDescent source hNoGlue hValid)

@[simp] theorem retainedRow_mk (e : NonDanglingEdge data) :
    retainedRow source hNoGlue hValid e.stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand) hValid.1 e).stablePath := rfl

end DraismaVargas.LocalCases.NonTrivalentValencyThreeDescent
