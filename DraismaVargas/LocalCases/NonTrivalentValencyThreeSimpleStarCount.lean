module

public import DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleTracks
public import DraismaVargas.LocalCases.NonTrivalentValencyThreeStarCount

@[expose] public section

/-!
# The valency-three Types I / II star count, and the link from (H-I/II)

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 (a combinatorial type
change is a Whitehead move on the *ambient* tracked graph, with the labelling
convention (1)) and Section 5.3 (Case `{v3-nd4}`, base trees `T_alpha` with
`alpha` simple: the anchor `A` resolves into `A_u`, the **divalent** `A'` and
`A_v`; the case gives the exact star of `A_u` -- `e_alpha` above `t_alpha`, the
bridge `e_1` and a second occurrence `e'` above `t_1` running to the divalent
`A'`, which carries `e_delta` -- and records that the resulting combinatorial
type has `{h_alpha, h_delta}` meeting at `A_u` and `{h_beta, h_gamma}` at
`A_v`), together with Draisma--Vargas Part I (arXiv:1909.12924): the stable
graph `H(M)` (Section 3), its row labels (Section 5) and Lemma
`lemma-ndval-of-GqA0` (Section 6).

This is the Types I/II sibling of `NonTrivalentValencyThreeStarCount`
(Type III).  `NonTrivalentValencyThreeSimpleTracks` reduces
`OuterWalk.TypeChangeLink` at a three-valent wall, Types I and II, to **one**
obligation: the star count `hIncidence` of `typeChangeLink_of_incidence`.  This
module proves that count under (H-I/II) =
`NonTrivalentValencyThreeSimpleTracks.PrescribedSimpleMove`, and hence delivers
the link.

## What is reused from `NonTrivalentValencyThreeStarCount` by application

Every piece of `NonTrivalentValencyThreeStarCount` that mentions only the
incoming cover `wd.cover`, the wall datum `contractDatum wd.cover ...` and the
tracked ambient graph is valency- and type-agnostic, and is applied here with
`src := base.source`: `injective_incomingRow`, `incidenceCount_wall_eq_incoming`
(**(T2) at an ordinary wall block**, whose ramification input
`internalEdges_subsingleton_of_ne_anchor` is proved there and whose engine is
`WallSplitIncidenceOrdinary.incidenceCount_unramified`), `card_filter_label`,
`labelling_row_incomingRow_ne_base`, `natCard_moved_of_ne`,
`incidenceCount_facetRow_eq_zero`, `card_filter_pair`, `filter_moved_base`,
`dart_ne`, `sum_incidenceCount_branchVertex` and `sum_natCard_moved`.  Nothing
of them is copied.  What is *not* reusable is everything that mentions the
candidate: the Types I/II candidate lives over the two-fold branch gauge
`SimpleBase.gaugedData`, not over the wall datum, and its anchor resolves into
three vertices rather than two.

## What is proved

### 1.  The gauge on surviving occurrences

* `gaugeEdge`, `gaugeStablePath_stablePath`: the two branch gauges as one
  bijection on surviving occurrences, whose induced row map is
  `NonTrivalentValencyThreeSimpleRowDictionary.gaugeStablePath`.
* `gaugeEdge_alphaSurvivor`, `gaugeEdge_deltaSurvivor` and the row forms
  `gaugeStablePath_alphaSurvivor`, `gaugeStablePath_deltaSurvivor`: **the gauge
  carries `e_alpha` and `e_delta` of the wall datum to `alphaOccurrence` and
  `deltaOccurrence` of the gauged datum** (as named in
  `NonTrivalentValencyThreeSimpleRows`).  This is the bridge (H-I/II) needs: the
  hypothesis names `e_alpha`, `e_delta` upstairs, while the anchor stars of
  `NonTrivalentValencyThreeSimpleRows` name their gauged copies.  Both branch
  swaps fix the occurrences of `t_alpha`; the first moves those of the doubled
  direction by `deltaPerm`, which is exactly how `deltaRepr` is defined.

### 2.  (T1) `gauged -> cand` at an ordinary wall block

* `incidenceCount_endpointVertex_true_ordinary`: at an ordinary wall block the
  trivalent end `B_v` of the candidate keeps the block's row-filtered star.  The
  bijection is `trivEnd`: a beta/gamma-side survivor stays itself, an alpha-side
  survivor is replaced by the new occurrence of its own fine class.
  `NonTrivalentValencyThreeSimpleRows.nonDanglingIncident_endpointVertex_true_ordinary`
  lists the target star, `stablePath_retainedEdge_eq_newSourceEdge` puts the new
  occurrence on the row of the survivor it replaces, and `retainedRow` is
  injective (`retainedRow_injective`), so the row filter transports.
* `incidenceCount_candVertex`: (T1) at every gauged wall-datum vertex other than
  the anchor -- the ordinary-block case above, and
  `NonTrivalentValencyThreeSimpleTracks.incidenceCount_retainedVertex_retainedRow`
  away from the wall.

### 3.  The star count

* `incidence_inl_retained`, `incidence_inl_bridge`: away from the anchor.  On a
  retained row the count is (T1), then the gauge leg
  `NonTrivalentValencyThreeSimpleTracks.incidenceCount_sheetRelabel_gauge`, then
  (T2), then `NonTrivalentValencyThreeTracks.card_star_eq_incidenceCount` with
  `move_vert_eq_iff_of_ne` erasing the move; on the bridge row both sides
  vanish -- downstairs `e_1` joins `A_u` to `A_v`, upstairs the vanishing chart
  row is the single occurrence `h_1`.
* `incidence_inr_false_retained`, `incidence_inr_false_bridge`: **at `A_u`.**
  The exact star `NonTrivalentValencyThreeSimpleRows.nonDanglingIncident_hubLeft`
  = `{e_1, e', e_alpha}` is matched dart by dart against the moved star
  `{m.base, d_alpha, d_delta}` that (H-I/II) prescribes (`filter_moved_base`,
  `dart_ne`).  **The row `h_delta` at `A_u` is carried by the new occurrence
  `e'`, not by a retained copy of `e_delta`**, so it is read through
  `newSourceEdge_stablePath_eq_retained`;
  `NonTrivalentValencyThreeSimpleExit.outLabelling_row_bridge` /
  `_row_retained` supply the row side and `label_dart_lift_iff` the dart side --
  from the **row** equality of (H-I/II) alone
  (`IncomingPairing.label_dart_of_row`), which is all the count needs and all a
  pass-through survivor can give.
* `incidence_inr_true`: **at `A_v`, from the leftover equation.**  A stable row
  of the candidate meets its branch vertices twice in all
  (`sum_incidenceCount_branchVertex`), a chart row carries exactly two darts of
  the tracked graph (`card_filter_label`, `sum_natCard_moved`), and
  `vertexEquiv` is a bijection; the count agrees at every other branch vertex,
  so it agrees at `A_v`.  The divalent `A'` costs nothing: it is not a branch
  vertex, so no count is asked of it.
* `incidence_of_prescribedSimpleMove`, and
  `typeChangeLink_of_prescribedSimpleMove`: **`OuterWalk.TypeChangeLink` at a
  three-valent wall, Types I and II, from (H-I/II) alone.**
* `typeChangeLink_of_simpleSeparated`: the headline is not vacuous --
  `NonTrivalentValencyThreeSimpleTracks.prescribedMove`, which contracts the same
  edge as `m`, satisfies (H-I/II) from `SimpleSeparated` and the orientation
  clause.

## Hypotheses left explicit here

1. `hPres : NonTrivalentValencyThreeSimpleTracks.PrescribedSimpleMove m wd base`,
   i.e. (H-I/II), at row level: the two darts the move places with `m.base`
   carry the rows of `e_alpha` and `e_delta`.
   `NonTrivalentValencyThreeSimpleTracks` supplies its relative non-vacuity
   witness `prescribedSimpleMove_prescribedMove` from `SimpleSeparated` and the
   orientation clause, and the dispatcher's producer
   `prescribedSimpleMove_of_rows`; neither is derived here, and
   `typeChangeLink_of_simpleSeparated` only applies that witness.
2. `base : NonTrivalentValencyThreeSimpleCandidate.SimpleBase ...` (which fixes
   the outgoing type as I or II, and carries `wallStar` and `anchorBlk`) and
   `hValid`.
3. `wallStar : ThirdEquation.ThreeStar (contract wd.coverTarget wd.hab wd.hOne)
   <wd.a, wd.hab>`: the valency dispatcher of `OuterWalk.WallData.valency` is
   not built here, as in the other valency-three modules;
   `NonTrivalentValencyThreeDispatcher` builds it.
4. Nothing else: `HasPathEnds`, `NoContractedReturn`, the outgoing presentation
   and the common minor are in `NonTrivalentValencyThreeSimpleExit`, and the
   branch-vertex bijection is `NonTrivalentValencyThreeSimpleTracks.vertexEquiv`.

No structure is introduced.  Every definition (`gaugeEdge`, `trivEndEdge`,
`trivEnd`, `bridgeND`, `bridgeDeltaND`, `alphaND`, `deltaND`, `alphaRetained`,
`alphaWall`, `deltaWall`) is a named occurrence of an object already built, and
each is applied in the theorems above; the two `def`s that produce data,
`typeChangeLink_of_prescribedSimpleMove` and `typeChangeLink_of_simpleSeparated`,
are the deliverable and its non-vacuity witness.

## Consumers

`OuterWalk.TypeChangeLink` at Part II Case `{v3-nd4}`, Types I and II, hence the
`link` hypothesis of `OuterWalk.coneEntry_of_reaches`, once the valency
dispatcher supplies `wallStar` and (H-I/II).
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleStarCount

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRows
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRowEquiv
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRowDictionary
  (gaugeStablePath retainedRow_injective)
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleTracks

noncomputable section

/-! ## 1.  The two branch gauges on surviving occurrences -/

section Gauge

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall} (base : SimpleBase data star anchor) (hValid : data.Valid)

/-- Two occurrences over one target occurrence coincide when their sheets do. -/
theorem sourceEdge_congr {datum : GluingDatum target degree} (edge : target.edges)
    {sheetOne sheetTwo : Fin degree}
    (hRel : (datum.edgePartition edge).Rel sheetOne sheetTwo) :
    datum.sourceEdge edge sheetOne = datum.sourceEdge edge sheetTwo :=
  Subtype.ext (Prod.ext rfl hRel)

/-- Every occurrence is the canonical occurrence of its own target edge and
sheet. -/
theorem eq_sourceEdge_self {datum : GluingDatum target degree} (e : datum.SourceEdge)
    {edge : target.edges} (hTarget : e.1.1 = edge) :
    e = datum.sourceEdge edge e.1.2 := by
  refine Subtype.ext (Prod.ext hTarget ?_)
  show e.1.2 = (datum.edgePartition edge).repr e.1.2
  have h := e.2
  rw [hTarget] at h
  exact h.symm

/-- **The two branch gauges as one bijection on surviving occurrences.**  It is
the map whose induced row map is
`NonTrivalentValencyThreeSimpleRowDictionary.gaugeStablePath`. -/
def gaugeEdge (e : NonDanglingEdge data) : NonDanglingEdge base.gaugedData :=
  SheetRelabelStable.nonDanglingEdgeEquiv base.secondRelabeling
    (middleData_connected base hValid)
    (SheetRelabelStable.nonDanglingEdgeEquiv base.firstRelabeling hValid.1 e)

theorem gaugeEdge_val (e : NonDanglingEdge data) :
    (gaugeEdge base hValid e).1 =
      base.secondRelabeling.sourceEdgeEquiv (base.firstRelabeling.sourceEdgeEquiv e.1) := rfl

/-- **The gauge's row map is `gaugeStablePath`.** -/
theorem gaugeStablePath_stablePath (e : NonDanglingEdge data) :
    gaugeStablePath base hValid e.stablePath = (gaugeEdge base hValid e).stablePath := rfl

theorem gaugeEdge_sourceEdge (edge : target.edges) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling data (data.sourceEdge edge sheet)) :
    (gaugeEdge base hValid (⟨data.sourceEdge edge sheet, hSurvives⟩ : NonDanglingEdge data)).1 =
      base.gaugedData.sourceEdge edge
        (base.secondRelabeling.edgePermutation edge
          (base.firstRelabeling.edgePermutation edge sheet)) := by
  have hOne : base.firstRelabeling.sourceEdgeEquiv (data.sourceEdge edge sheet) =
      base.middleData.sourceEdge edge (base.firstRelabeling.edgePermutation edge sheet) :=
    SheetRelabelPruning.sourceEdgeEquiv_sourceEdge base.firstRelabeling edge sheet
  have hTwo : base.secondRelabeling.sourceEdgeEquiv
        (base.middleData.sourceEdge edge (base.firstRelabeling.edgePermutation edge sheet)) =
      base.gaugedData.sourceEdge edge
        (base.secondRelabeling.edgePermutation edge
          (base.firstRelabeling.edgePermutation edge sheet)) :=
    SheetRelabelPruning.sourceEdgeEquiv_sourceEdge base.secondRelabeling edge _
  rw [gaugeEdge_val base hValid
      (⟨data.sourceEdge edge sheet, hSurvives⟩ : NonDanglingEdge data), hOne, hTwo]

/-- **The gauge carries `e_alpha` to `alphaOccurrence`.**  Both branch swaps act
trivially on the occurrences of `t_alpha` (`first_edgePermutation_simple`,
`second_edgePermutation_alpha`), and `hubSheet` lies in the class of
`e_alpha`. -/
theorem gaugeEdge_alphaSurvivor :
    (gaugeEdge base hValid
        (⟨base.alphaSurvivor.1, alphaSurvivor_survives base⟩ : NonDanglingEdge data)).1 =
      alphaOccurrence base := by
  have hTarget : base.alphaSurvivor.1.1.1 = directionEdge star base.alphaLabel :=
    ((mem_directionSurvivors data star anchor base.alphaLabel base.alphaSurvivor).mp
      base.alphaSurvivor_mem).2
  have hSelf : base.alphaSurvivor.1 = data.sourceEdge (directionEdge star base.alphaLabel)
      (Prescribed.occurrenceSheet base.alphaSurvivor) :=
    eq_sourceEdge_self base.alphaSurvivor.1 hTarget
  have hSurv : ¬ IsDangling data (data.sourceEdge (directionEdge star base.alphaLabel)
      (Prescribed.occurrenceSheet base.alphaSurvivor)) := by
    rw [← hSelf]
    exact alphaSurvivor_survives base
  have hCong : (⟨base.alphaSurvivor.1, alphaSurvivor_survives base⟩ : NonDanglingEdge data) =
      (⟨data.sourceEdge (directionEdge star base.alphaLabel)
        (Prescribed.occurrenceSheet base.alphaSurvivor), hSurv⟩ : NonDanglingEdge data) :=
    Subtype.ext hSelf
  rw [hCong, gaugeEdge_sourceEdge base hValid _ _ hSurv,
    first_edgePermutation_simple base base.alphaLabel base.alpha_ne,
    second_edgePermutation_alpha base, Equiv.refl_apply, Equiv.refl_apply]
  exact sourceEdge_congr _ (alpha_rel_of_mem base
    (occurrenceSheet_mem_occurrenceBlock base.alphaSurvivor) base.hubSheet_mem_alpha)

/-- **The gauge carries `e_delta` to `deltaOccurrence`.**  The first branch swap
moves the occurrences of the doubled direction by `deltaPerm`, which is exactly
how `deltaRepr` is defined; the second leaves them alone. -/
theorem gaugeEdge_deltaSurvivor :
    (gaugeEdge base hValid
        (⟨base.deltaSurvivor.1, deltaSurvivor_survives base⟩ : NonDanglingEdge data)).1 =
      deltaOccurrence base := by
  have hTarget : base.deltaSurvivor.1.1.1 = Prescribed.doubledEdge base.source :=
    ((mem_directionSurvivors data star anchor (Prescribed.doubled base.source)
      base.deltaSurvivor).mp base.deltaSurvivor_mem).2
  have hSelf : base.deltaSurvivor.1 = data.sourceEdge (Prescribed.doubledEdge base.source)
      (Prescribed.occurrenceSheet base.deltaSurvivor) :=
    eq_sourceEdge_self base.deltaSurvivor.1 hTarget
  have hSurv : ¬ IsDangling data (data.sourceEdge (Prescribed.doubledEdge base.source)
      (Prescribed.occurrenceSheet base.deltaSurvivor)) := by
    rw [← hSelf]
    exact deltaSurvivor_survives base
  have hCong : (⟨base.deltaSurvivor.1, deltaSurvivor_survives base⟩ : NonDanglingEdge data) =
      (⟨data.sourceEdge (Prescribed.doubledEdge base.source)
        (Prescribed.occurrenceSheet base.deltaSurvivor), hSurv⟩ : NonDanglingEdge data) :=
    Subtype.ext hSelf
  rw [hCong, gaugeEdge_sourceEdge base hValid _ _ hSurv,
    first_edgePermutation_doubled base, second_edgePermutation_doubled base, Equiv.refl_apply]
  rfl

/-- **The gauge does not move the row of `e_alpha`.** -/
theorem gaugeStablePath_alphaSurvivor :
    gaugeStablePath base hValid
        (NonDanglingEdge.stablePath
          (⟨base.alphaSurvivor.1, alphaSurvivor_survives base⟩ : NonDanglingEdge data)) =
      NonDanglingEdge.stablePath
        (⟨alphaOccurrence base, alphaOccurrence_survives base hValid⟩ :
          NonDanglingEdge base.gaugedData) := by
  refine Eq.trans (gaugeStablePath_stablePath base hValid
    (⟨base.alphaSurvivor.1, alphaSurvivor_survives base⟩ : NonDanglingEdge data)) ?_
  exact congrArg NonDanglingEdge.stablePath
    (Subtype.ext (gaugeEdge_alphaSurvivor base hValid))

/-- **The gauge does not move the row of `e_delta`.** -/
theorem gaugeStablePath_deltaSurvivor :
    gaugeStablePath base hValid
        (NonDanglingEdge.stablePath
          (⟨base.deltaSurvivor.1, deltaSurvivor_survives base⟩ : NonDanglingEdge data)) =
      NonDanglingEdge.stablePath
        (⟨deltaOccurrence base, deltaOccurrence_survives base hValid⟩ :
          NonDanglingEdge base.gaugedData) := by
  refine Eq.trans (gaugeStablePath_stablePath base hValid
    (⟨base.deltaSurvivor.1, deltaSurvivor_survives base⟩ : NonDanglingEdge data)) ?_
  exact congrArg NonDanglingEdge.stablePath
    (Subtype.ext (gaugeEdge_deltaSurvivor base hValid))

end Gauge

/-! ## 2.  (T1) at an ordinary wall block -/

section Ordinary

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall} (base : SimpleBase data star anchor) (hValid : data.Valid)

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- The representative of a survivor of an ordinary wall block at the trivalent
end `B_v`: the retained occurrence itself on the beta/gamma side, the new
occurrence of its own fine class on the alpha side. -/
def trivEndEdge (e : NonDanglingEdge base.gaugedData) :
    (validCandidate base hValid).datum.SourceEdge :=
  if base.rightAssignment e.1.1.1 then (validCandidate base hValid).oldSourceEdge e.1
  else (validCandidate base hValid).newSourceEdge e.1.1.2

theorem trivEndEdge_survives {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (e : NonDanglingEdge base.gaugedData)
    (hInc : Incident base.gaugedData e.1 (base.gaugedData.sourceEndpoint wall x)) :
    ¬ IsDangling (validCandidate base hValid).datum (trivEndEdge base hValid e) := by
  classical
  unfold trivEndEdge
  by_cases hs : base.rightAssignment e.1.1.1 = true
  · rw [ite_eq_left hs]
    exact ResolutionSurvival.not_isDangling_oldSourceEdge (validCandidate base hValid)
      (base.gaugedData_valid hValid).1 e.1 e.2
  · have hs' : base.rightAssignment e.1.1.1 = false := by
      simpa using hs
    rw [ite_eq_right hs]
    exact newSourceEdge_survives_of_mem_ordinaryStar base hValid hX
      ((mem_ordinaryStar base e.1).mpr ⟨⟨e.2, hInc⟩, hs'⟩)

/-- The same representative, as a surviving occurrence of the candidate. -/
def trivEnd {x : Fin degree} (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x)
    (e : NonDanglingEdge base.gaugedData)
    (hInc : Incident base.gaugedData e.1 (base.gaugedData.sourceEndpoint wall x)) :
    NonDanglingEdge (validCandidate base hValid).datum :=
  ⟨trivEndEdge base hValid e, trivEndEdge_survives base hValid hX e hInc⟩

theorem stablePath_trivEnd {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (e : NonDanglingEdge base.gaugedData)
    (hInc : Incident base.gaugedData e.1 (base.gaugedData.sourceEndpoint wall x)) :
    (trivEnd base hValid hX e hInc).stablePath = retainedRow base hValid e.stablePath := by
  classical
  rw [retainedRow_mk base hValid e]
  by_cases hs : base.rightAssignment e.1.1.1 = true
  · refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
    show trivEndEdge base hValid e = (validCandidate base hValid).oldSourceEdge e.1
    unfold trivEndEdge
    rw [ite_eq_left hs]
  · have hs' : base.rightAssignment e.1.1.1 = false := by
      simpa using hs
    have hOld : e.1 ∈ ordinaryStar base x false :=
      (mem_ordinaryStar base e.1).mpr ⟨⟨e.2, hInc⟩, hs'⟩
    rw [stablePath_retainedEdge_eq_newSourceEdge base hValid hX hOld]
    refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
    show trivEndEdge base hValid e = (validCandidate base hValid).newSourceEdge e.1.1.2
    unfold trivEndEdge
    rw [ite_eq_right hs]

theorem incident_trivEnd {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (e : NonDanglingEdge base.gaugedData)
    (hInc : Incident base.gaugedData e.1 (base.gaugedData.sourceEndpoint wall x)) :
    Incident (validCandidate base hValid).datum (trivEnd base hValid hX e hInc).1
      (endpointVertex base hValid true x) := by
  classical
  by_cases hs : base.rightAssignment e.1.1.1 = true
  · have hOld : e.1 ∈ ordinaryStar base x true :=
      (mem_ordinaryStar base e.1).mpr ⟨⟨e.2, hInc⟩, hs⟩
    have hVal : (trivEnd base hValid hX e hInc).1 =
        (validCandidate base hValid).oldSourceEdge e.1 := by
      show trivEndEdge base hValid e = _
      unfold trivEndEdge
      rw [ite_eq_left hs]
    rw [hVal]
    exact (incident_oldSourceEdge_endpointVertex_iff base hValid true hX e.1).mpr
      ⟨⟨mem_incidentEdges_of_mem_ordinaryStar base hOld,
        wall_rel_of_mem_ordinaryStar base hOld⟩, hs⟩
  · have hs' : base.rightAssignment e.1.1.1 = false := by
      simpa using hs
    have hOld : e.1 ∈ ordinaryStar base x false :=
      (mem_ordinaryStar base e.1).mpr ⟨⟨e.2, hInc⟩, hs'⟩
    have hVal : (trivEnd base hValid hX e hInc).1 =
        (validCandidate base hValid).newSourceEdge e.1.1.2 := by
      show trivEndEdge base hValid e = _
      unfold trivEndEdge
      rw [ite_eq_right hs]
    rw [hVal]
    exact incident_newSourceEdge_endpointVertex_true base hValid hX hOld

/-- **(T1) at an ordinary wall block.**  The trivalent end `B_v` of a non-anchor
wall block keeps the block's row-filtered star: the retained copies of the
beta/gamma-side survivors, and one new occurrence for each alpha-side survivor,
on the row of the survivor it replaces. -/
theorem incidenceCount_endpointVertex_true_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (row : StablePath base.gaugedData) :
    incidenceCount base.gaugedData (base.gaugedData.sourceEndpoint wall x) row =
      incidenceCount (validCandidate base hValid).datum (endpointVertex base hValid true x)
        (retainedRow base hValid row) := by
  classical
  unfold incidenceCount
  refine Finset.card_bij (fun e he ↦ trivEnd base hValid hX e
    ((mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp he).1)) ?_ ?_ ?_
  · intro e he
    obtain ⟨hMem, hRow⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr
      (incident_trivEnd base hValid hX e _), ?_⟩
    rw [stablePath_trivEnd base hValid hX e _, hRow]
  · intro e₁ he₁ e₂ he₂ hEq
    have hVal : trivEndEdge base hValid e₁ = trivEndEdge base hValid e₂ :=
      congrArg Subtype.val hEq
    unfold trivEndEdge at hVal
    by_cases hs₁ : base.rightAssignment e₁.1.1.1 = true <;>
      by_cases hs₂ : base.rightAssignment e₂.1.1.1 = true
    · rw [ite_eq_left hs₁, ite_eq_left hs₂] at hVal
      exact Subtype.ext
        (ResolutionCut.oldSourceEdge_injective (validCandidate base hValid) hVal)
    · rw [ite_eq_left hs₁, ite_eq_right hs₂] at hVal
      exact absurd hVal.symm (newSourceEdge_ne_oldSourceEdge base hValid e₂.1.1.2 e₁.1)
    · rw [ite_eq_right hs₁, ite_eq_left hs₂] at hVal
      exact absurd hVal (newSourceEdge_ne_oldSourceEdge base hValid e₁.1.1.2 e₂.1)
    · rw [ite_eq_right hs₁, ite_eq_right hs₂] at hVal
      have hs₁' : base.rightAssignment e₁.1.1.1 = false := by simpa using hs₁
      have hs₂' : base.rightAssignment e₂.1.1.1 = false := by simpa using hs₂
      have hOld₁ : e₁.1 ∈ ordinaryStar base x false :=
        (mem_ordinaryStar base e₁.1).mpr
          ⟨⟨e₁.2, (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp he₁).1⟩, hs₁'⟩
      have hOld₂ : e₂.1 ∈ ordinaryStar base x false :=
        (mem_ordinaryStar base e₂.1).mpr
          ⟨⟨e₂.2, (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp he₂).1⟩, hs₂'⟩
      exact Subtype.ext (newSourceEdge_sheet_injOn base hValid hX hOld₁ hOld₂ hVal)
  · intro f hf
    obtain ⟨hMem, hRow⟩ := Finset.mem_filter.mp hf
    have hStar : f.1 ∈ nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid true x) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, (mem_incidentEdges _ _ _).mp hMem⟩
    rw [nonDanglingIncident_endpointVertex_true_ordinary base hValid hX,
      Finset.mem_union, Finset.mem_image, Finset.mem_image] at hStar
    rcases hStar with ⟨old, hOld, hEq⟩ | ⟨old, hOld, hEq⟩
    · obtain ⟨⟨hSurv, hIncOld⟩, hSide⟩ := (mem_ordinaryStar base old).mp hOld
      refine ⟨⟨old, hSurv⟩, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hIncOld, ?_⟩
        refine retainedRow_injective base hValid ?_
        rw [← stablePath_trivEnd base hValid hX ⟨old, hSurv⟩ hIncOld]
        refine Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)) hRow
        show trivEndEdge base hValid ⟨old, hSurv⟩ = f.1
        unfold trivEndEdge
        rw [ite_eq_left hSide]
        exact hEq
      · refine Subtype.ext ?_
        show trivEndEdge base hValid ⟨old, hSurv⟩ = f.1
        unfold trivEndEdge
        rw [ite_eq_left hSide]
        exact hEq
    · obtain ⟨⟨hSurv, hIncOld⟩, hSide⟩ := (mem_ordinaryStar base old).mp hOld
      have hSide' : ¬ (base.rightAssignment old.1.1 = true) := by
        rw [hSide]
        simp
      refine ⟨⟨old, hSurv⟩, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hIncOld, ?_⟩
        refine retainedRow_injective base hValid ?_
        rw [← stablePath_trivEnd base hValid hX ⟨old, hSurv⟩ hIncOld]
        refine Eq.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)) hRow
        show trivEndEdge base hValid ⟨old, hSurv⟩ = f.1
        unfold trivEndEdge
        rw [ite_eq_right hSide']
        exact hEq
      · refine Subtype.ext ?_
        show trivEndEdge base hValid ⟨old, hSurv⟩ = f.1
        unfold trivEndEdge
        rw [ite_eq_right hSide']
        exact hEq

/-- **(T1) at every gauged wall-datum vertex other than the anchor.** -/
theorem incidenceCount_candVertex (w : base.gaugedData.SourceVertex)
    (hne : w ≠ gaugedAnchorVertex base) (row : StablePath base.gaugedData) :
    incidenceCount base.gaugedData w row =
      incidenceCount (validCandidate base hValid).datum (candVertex base hValid w)
        (retainedRow base hValid row) := by
  classical
  by_cases hw : w.1.1 = wall
  · rw [candVertex_wall base hValid w hw]
    conv_lhs => rw [← sourceEndpoint_self base w hw]
    exact incidenceCount_endpointVertex_true_ordinary base hValid
      (not_rel_anchor_of_ne base w hw hne) row
  · rw [candVertex_away base hValid w hw]
    exact incidenceCount_retainedVertex_retainedRow base hValid w hw row

end Ordinary

/-! ## 3.  The three new vertices above the anchor -/

section Anchor

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall} (base : SimpleBase data star anchor) (hValid : data.Valid)

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

theorem retainedRow_ne_bridgeRow (r : StablePath base.gaugedData) :
    retainedRow base hValid r ≠ bridgeRow base hValid := by
  intro hBad
  have h := congrArg (rowEquiv base hValid) hBad
  rw [rowEquiv_retainedRow base hValid r, rowEquiv_bridgeRow base hValid] at h
  exact Option.some_ne_none r h

/-- The bridge occurrence `e_1`, as a surviving occurrence of the candidate. -/
def bridgeND : NonDanglingEdge (validCandidate base hValid).datum :=
  ⟨bridgeEdge base hValid base.hubSheet, bridgeEdge_hub_survives base hValid⟩

/-- The second occurrence `e'` above `t_1`, as a surviving occurrence of the
candidate.  It continues through the divalent `A'` onto the retained row of
`e_delta`. -/
def bridgeDeltaND : NonDanglingEdge (validCandidate base hValid).datum :=
  ⟨bridgeEdge base hValid base.deltaRepr, bridgeEdge_delta_survives base hValid⟩

/-- `e_alpha`, as a surviving occurrence of the gauged wall datum. -/
def alphaND : NonDanglingEdge base.gaugedData :=
  ⟨alphaOccurrence base, alphaOccurrence_survives base hValid⟩

/-- `e_delta`, as a surviving occurrence of the gauged wall datum. -/
def deltaND : NonDanglingEdge base.gaugedData :=
  ⟨deltaOccurrence base, deltaOccurrence_survives base hValid⟩

/-- The retained copy of `e_alpha` at `A_u`. -/
def alphaRetained : NonDanglingEdge (validCandidate base hValid).datum :=
  ResolutionAwayFromWall.retainedEdge (validCandidate base hValid)
    (base.gaugedData_valid hValid).1 (alphaND base hValid)

@[simp] theorem stablePath_bridgeND :
    (bridgeND base hValid).stablePath = bridgeRow base hValid := rfl

/-- **The row `h_delta` at `A_u` is carried by the new occurrence `e'`.** -/
theorem stablePath_bridgeDeltaND :
    (bridgeDeltaND base hValid).stablePath =
      retainedRow base hValid (deltaND base hValid).stablePath := by
  refine Eq.trans (newSourceEdge_stablePath_eq_retained base hValid) ?_
  exact (retainedRow_mk base hValid (deltaND base hValid)).symm

theorem stablePath_alphaRetained :
    (alphaRetained base hValid).stablePath =
      retainedRow base hValid (alphaND base hValid).stablePath :=
  (retainedRow_mk base hValid (alphaND base hValid)).symm

theorem bridgeDeltaND_ne_alphaRetained :
    bridgeDeltaND base hValid ≠ alphaRetained base hValid := by
  intro hBad
  exact newSourceEdge_ne_oldSourceEdge base hValid base.deltaRepr (alphaOccurrence base)
    (congrArg Subtype.val hBad)

/-- **The exact star at `A_u`** of `NonTrivalentValencyThreeSimpleRows`, read on
surviving occurrences: the bridge `e_1`, the second occurrence `e'` and the
retained `e_alpha`. -/
theorem incidentEdges_hubLeft :
    incidentEdges (validCandidate base hValid).datum
        (endpointVertex base hValid false base.hubSheet) =
      {bridgeND base hValid, bridgeDeltaND base hValid, alphaRetained base hValid} := by
  classical
  ext e
  rw [mem_incidentEdges]
  constructor
  · intro hInc
    have h : e.1 ∈ nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid false base.hubSheet) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hInc⟩
    rw [nonDanglingIncident_hubLeft base hValid] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  · intro h
    have h2 : e.1 ∈ nonDanglingIncident (validCandidate base hValid).datum
        (endpointVertex base hValid false base.hubSheet) := by
      rw [nonDanglingIncident_hubLeft base hValid]
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    exact ((mem_nonDanglingIncident _ _ _).mp h2).2

/-- A branch vertex of the candidate away from the anchor is neither `A_u` nor
`A_v`. -/
theorem endpointVertex_ne_candBranchMap_inl (side : Bool)
    (w : {w : BranchVertex base.gaugedData // w.1 ≠ gaugedAnchorVertex base}) :
    endpointVertex base hValid side base.hubSheet ≠
      (candBranchMap base hValid (Sum.inl w)).1 := by
  intro hBad
  exact Sum.inr_ne_inl (candBranchMap_injective base hValid (Subtype.ext hBad))

/-- **The bridge row does not reach a branch vertex of the candidate away from
the anchor**: its only occurrence joins `A_u` to `A_v`. -/
theorem incidenceCount_bridgeRow_inl_eq_zero
    (w : {w : BranchVertex base.gaugedData // w.1 ≠ gaugedAnchorVertex base}) :
    incidenceCount (validCandidate base hValid).datum
      (candBranchMap base hValid (Sum.inl w)).1 (bridgeRow base hValid) = 0 := by
  classical
  unfold incidenceCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hRow
  have hVal := bridgeEdge_isolated base hValid e hRow
  have hInc := (mem_incidentEdges _ _ _).mp he
  rw [hVal] at hInc
  have hInc' : ((validCandidate base hValid).datum.sourceEnds
        (bridgeEdge base hValid base.hubSheet)).1 =
      (candBranchMap base hValid (Sum.inl w)).1 ∨
      ((validCandidate base hValid).datum.sourceEnds
        (bridgeEdge base hValid base.hubSheet)).2 =
      (candBranchMap base hValid (Sum.inl w)).1 := hInc
  rw [sourceEnds_bridgeEdge base hValid base.hubSheet] at hInc'
  rcases hInc' with h | h
  · exact endpointVertex_ne_candBranchMap_inl base hValid false w h
  · exact endpointVertex_ne_candBranchMap_inl base hValid true w h

end Anchor

/-! ## 4.  The two transports at a wall of the outer walk -/

section Wall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.ClassInjectivity
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.NonTrivalentValencyThreeTracks
  (facetRow facetEdge leftEnd rightEnd anchorVertex branchEquivAnchorComplement
    branchEquivAnchorComplement_apply leftBranch rightBranch facetDartLeft liftEdge
    stablePath_liftEdge vert_base_eq vert_opBase_eq)
open DraismaVargas.LocalCases.NonTrivalentValencyThreeStarCount
  (injective_incomingRow incidenceCount_wall_eq_incoming card_filter_label
    labelling_row_incomingRow_ne_base natCard_moved_of_ne incidenceCount_facetRow_eq_zero
    card_filter_pair filter_moved_base dart_ne sum_incidenceCount_branchVertex
    sum_natCard_moved)

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

variable {wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (base : SimpleBase (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)

/-! ### The chart rows of the outgoing presentation (`NonTrivalentValencyThreeSimpleExit`) -/

/-- A retained row of the outgoing presentation keeps the chart coordinate of
its own incoming row; the two branch gauges do not move a stable row. -/
theorem outFD_row_retained (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (NonTrivalentValencyThreeSimpleExit.wallOutgoingFD m wd base hValid).labelling.row
        (retainedRow base hValid (gaugeStablePath base hValid p)) =
      wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) p) :=
  NonTrivalentValencyThreeSimpleExit.outLabelling_row_retained wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne (wd.hForest m)
    (NonTrivalentValencyThreeExit.noContractedReturn_of_valency_three m wd wallStar)
    wd.coordinates (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord wd.hFacetZero base
    hValid p

/-- The bridge row of the outgoing presentation occupies the vanishing chart
row `label m.base`. -/
theorem outFD_row_bridge :
    (NonTrivalentValencyThreeSimpleExit.wallOutgoingFD m wd base hValid).labelling.row
      (bridgeRow base hValid) = label m.base :=
  NonTrivalentValencyThreeSimpleExit.outLabelling_row_bridge wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne (wd.hForest m)
    (NonTrivalentValencyThreeExit.noContractedReturn_of_valency_three m wd wallStar)
    wd.coordinates (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord wd.hFacetZero base
    hValid

/-! ### Away from the anchor -/

/-- **The star count at a branch vertex away from the anchor, on a retained
row.**  It is (T1) at the gauged datum, then the gauge leg, then (T2) at the
wall contraction, then the incoming tracking. -/
theorem incidence_inl_retained
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base)
    (w : {w : BranchVertex base.gaugedData // w.1 ≠ gaugedAnchorVertex base})
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (validCandidate base hValid).datum
        (candBranchMap base hValid (Sum.inl w)).1
        (retainedRow base hValid (gaugeStablePath base hValid p)) =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd base hValid (candBranchMap base hValid (Sum.inl w)) ∧
        label d = (NonTrivalentValencyThreeSimpleExit.wallOutgoingFD m wd base
          hValid).labelling.row
          (retainedRow base hValid (gaugeStablePath base hValid p))} := by
  classical
  obtain ⟨v, rfl⟩ : ∃ v, branchEquivGaugedAnchorComplement m wd base hValid v = w :=
    ⟨(branchEquivGaugedAnchorComplement m wd base hValid).symm w,
      Equiv.apply_symm_apply _ _⟩
  rw [vertexEquiv_inl m wd base hValid (branchEquivGaugedAnchorComplement m wd base hValid v),
    Equiv.symm_apply_apply, outFD_row_retained m wd base hValid p,
    natCard_moved_of_ne m wd v.1 wallStar hBase v.2.1 v.2.2 _]
  have hT1 := incidenceCount_candVertex base hValid
    (branchEquivGaugedAnchorComplement m wd base hValid v).1.1
    (branchEquivGaugedAnchorComplement m wd base hValid v).2 (gaugeStablePath base hValid p)
  have hGauge := incidenceCount_sheetRelabel_gauge base hValid
    (branchEquivAnchorComplement m wd wallStar base.source v).1.1 p
  have hT2 := incidenceCount_wall_eq_incoming m wd wallStar base.source
    (branchEquivAnchorComplement m wd wallStar base.source v).1.1
    (branchEquivAnchorComplement m wd wallStar base.source v).2 v.1.1
    (branchEquivAnchorComplement_apply m wd wallStar base.source v).symm v.1.2 p
  exact hT1.symm.trans (hGauge.symm.trans hT2)

/-- **The star count at a branch vertex away from the anchor, on the bridge
row.**  Both sides vanish: downstairs the bridge joins `A_u` to `A_v`, upstairs
the vanishing chart row is the single occurrence `h_1`. -/
theorem incidence_inl_bridge
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base)
    (w : {w : BranchVertex base.gaugedData // w.1 ≠ gaugedAnchorVertex base}) :
    incidenceCount (validCandidate base hValid).datum
        (candBranchMap base hValid (Sum.inl w)).1 (bridgeRow base hValid) =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd base hValid (candBranchMap base hValid (Sum.inl w)) ∧
        label d = (NonTrivalentValencyThreeSimpleExit.wallOutgoingFD m wd base
          hValid).labelling.row (bridgeRow base hValid)} := by
  classical
  obtain ⟨v, rfl⟩ : ∃ v, branchEquivGaugedAnchorComplement m wd base hValid v = w :=
    ⟨(branchEquivGaugedAnchorComplement m wd base hValid).symm w,
      Equiv.apply_symm_apply _ _⟩
  rw [incidenceCount_bridgeRow_inl_eq_zero base hValid _]
  symm
  rw [vertexEquiv_inl m wd base hValid (branchEquivGaugedAnchorComplement m wd base hValid v),
    Equiv.symm_apply_apply, outFD_row_bridge m wd base hValid]
  have h := natCard_moved_of_ne m wd v.1 wallStar hBase v.2.1 v.2.2 (facetRow m wd)
  rw [show wd.fullDim.labelling.row (facetRow m wd) = label m.base
    from Equiv.apply_symm_apply _ _] at h
  exact h.trans (incidenceCount_facetRow_eq_zero m wd wallStar _ v.2.1 v.2.2)

/-! ### At `A_u` -/

/-- The chart label of the dart of an occurrence **on the row of** a lifted
wall-datum survivor.  Only the row equality is needed -- this is
`IncomingPairing.label_dart_of_row` composed with `stablePath_liftEdge` --
which is why (H-I/II) is stated at row level. -/
theorem label_dart_lift (d : StableSourceDarts.Dart wd.cover)
    (g : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hd : d.2.1.stablePath = (liftEdge m wd g).stablePath) :
    label (wd.tracks.iso.dart d) = wd.fullDim.labelling.row
      (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m)
        g.stablePath) := by
  rw [wd.tracks.row_map d]
  refine congrArg wd.fullDim.labelling.row ?_
  show NonDanglingEdge.stablePath d.2.1 = _
  rw [hd]
  exact stablePath_liftEdge m wd g

theorem label_dart_lift_iff (d : StableSourceDarts.Dart wd.cover)
    (g : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hd : d.2.1.stablePath = (liftEdge m wd g).stablePath)
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (label (wd.tracks.iso.dart d) = wd.fullDim.labelling.row
        (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m)
          (wd.hForest m) p)) ↔ g.stablePath = p := by
  rw [label_dart_lift m wd d g hd]
  constructor
  · intro h
    exact injective_incomingRow m wd wallStar (wd.fullDim.labelling.row.injective h)
  · intro h
    exact congrArg _ (congrArg _ h)

theorem label_dart_lift_ne_base (d : StableSourceDarts.Dart wd.cover)
    (g : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hd : d.2.1.stablePath = (liftEdge m wd g).stablePath) :
    label (wd.tracks.iso.dart d) ≠ label m.base := by
  rw [label_dart_lift m wd d g hd]
  exact labelling_row_incomingRow_ne_base m wd _

/-- `e_alpha`, as a surviving occurrence of the wall datum. -/
def alphaWall : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
  ⟨base.alphaSurvivor.1, alphaSurvivor_survives base⟩

/-- `e_delta`, as a surviving occurrence of the wall datum. -/
def deltaWall : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
  ⟨base.deltaSurvivor.1, deltaSurvivor_survives base⟩

theorem alphaLift_eq : alphaLift m wd base = liftEdge m wd (alphaWall m wd base) := rfl

theorem deltaLift_eq : deltaLift m wd base = liftEdge m wd (deltaWall m wd base) := rfl

/-- **The row of `e_alpha` at `A_u`.** -/
theorem stablePath_alphaRetained_wall :
    (alphaRetained base hValid).stablePath =
      retainedRow base hValid
        (gaugeStablePath base hValid (alphaWall m wd base).stablePath) := by
  rw [stablePath_alphaRetained base hValid]
  exact congrArg (retainedRow base hValid)
    (gaugeStablePath_alphaSurvivor base hValid).symm

/-- **The row `h_delta` at `A_u`, carried by the new occurrence `e'`.** -/
theorem stablePath_bridgeDeltaND_wall :
    (bridgeDeltaND base hValid).stablePath =
      retainedRow base hValid
        (gaugeStablePath base hValid (deltaWall m wd base).stablePath) := by
  rw [stablePath_bridgeDeltaND base hValid]
  exact congrArg (retainedRow base hValid)
    (gaugeStablePath_deltaSurvivor base hValid).symm

theorem retainedRow_gauge_iff (g : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (retainedRow base hValid (gaugeStablePath base hValid g.stablePath) =
        retainedRow base hValid (gaugeStablePath base hValid p)) ↔ g.stablePath = p := by
  constructor
  · intro h
    exact (gaugeStablePath base hValid).injective (retainedRow_injective base hValid h)
  · intro h
    exact congrArg _ (congrArg _ h)

/-- **The star count at `A_u`, on a retained row.**  The exact star
`{e_1, e', e_alpha}` is matched dart by dart with the star (H-I/II) prescribes:
`m.base` carries the vanishing chart row, and the two remaining darts carry the
incoming rows of `e_alpha` and `e_delta` -- the latter read at `A_u` through the
new occurrence `e'`. -/
theorem incidence_inr_false_retained
    (hPres : PrescribedSimpleMove m wd base)
    (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (validCandidate base hValid).datum
        (candBranchMap base hValid (Sum.inr false)).1
        (retainedRow base hValid (gaugeStablePath base hValid p)) =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd base hValid (candBranchMap base hValid (Sum.inr false)) ∧
        label d = (NonTrivalentValencyThreeSimpleExit.wallOutgoingFD m wd base
          hValid).labelling.row
          (retainedRow base hValid (gaugeStablePath base hValid p))} := by
  classical
  obtain ⟨hBase, first, second, hFirst, hSecond, hStar⟩ := hPres
  rw [vertexEquiv_anchor_false m wd base hValid hBase,
    outFD_row_retained m wd base hValid p]
  have hRHS : Nat.card {d : D // graph.vert (m.perm d) = graph.vert m.base ∧
      label d = wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab
        wd.hOne (wd.hCompat m) (wd.hForest m) p)} =
      ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
        fun d ↦ label d = wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc
          wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) p)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
  have hBridgeRow : ¬ ((bridgeND base hValid).stablePath =
      retainedRow base hValid (gaugeStablePath base hValid p)) := by
    rw [stablePath_bridgeND base hValid]
    exact fun h ↦ retainedRow_ne_bridgeRow base hValid _ h.symm
  rw [hRHS, filter_moved_base m wd first second hStar, Finset.filter_insert,
    ite_eq_right (Ne.symm (labelling_row_incomingRow_ne_base m wd p)),
    card_filter_pair _ _ (dart_ne m wd first second hStar)]
  show incidenceCount (validCandidate base hValid).datum
    (endpointVertex base hValid false base.hubSheet)
    (retainedRow base hValid (gaugeStablePath base hValid p)) = _
  unfold incidenceCount
  rw [incidentEdges_hubLeft base hValid, Finset.filter_insert, ite_eq_right hBridgeRow,
    card_filter_pair _ _ (bridgeDeltaND_ne_alphaRetained base hValid)]
  have hDelta : ((bridgeDeltaND base hValid).stablePath =
      retainedRow base hValid (gaugeStablePath base hValid p)) ↔
      (deltaWall m wd base).stablePath = p := by
    rw [stablePath_bridgeDeltaND_wall m wd base hValid]
    exact retainedRow_gauge_iff m wd base hValid (deltaWall m wd base) p
  have hAlpha : ((alphaRetained base hValid).stablePath =
      retainedRow base hValid (gaugeStablePath base hValid p)) ↔
      (alphaWall m wd base).stablePath = p := by
    rw [stablePath_alphaRetained_wall m wd base hValid]
    exact retainedRow_gauge_iff m wd base hValid (alphaWall m wd base) p
  rw [if_congr hDelta rfl rfl, if_congr hAlpha rfl rfl,
    if_congr (label_dart_lift_iff m wd first (alphaWall m wd base)
      (hFirst.trans (congrArg NonDanglingEdge.stablePath (alphaLift_eq m wd base))) wallStar p) rfl rfl,
    if_congr (label_dart_lift_iff m wd second (deltaWall m wd base)
      (hSecond.trans (congrArg NonDanglingEdge.stablePath (deltaLift_eq m wd base))) wallStar p) rfl rfl]
  exact Nat.add_comm _ _

/-- **The star count at `A_u`, on the bridge row.**  Both sides are one: the
bridge occurrence `e_1` downstairs, the contracted dart `m.base` upstairs. -/
theorem incidence_inr_false_bridge
    (hPres : PrescribedSimpleMove m wd base) :
    incidenceCount (validCandidate base hValid).datum
        (candBranchMap base hValid (Sum.inr false)).1 (bridgeRow base hValid) =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd base hValid (candBranchMap base hValid (Sum.inr false)) ∧
        label d = (NonTrivalentValencyThreeSimpleExit.wallOutgoingFD m wd base
          hValid).labelling.row (bridgeRow base hValid)} := by
  classical
  obtain ⟨hBase, first, second, hFirst, hSecond, hStar⟩ := hPres
  rw [vertexEquiv_anchor_false m wd base hValid hBase, outFD_row_bridge m wd base hValid]
  have hRHS : Nat.card {d : D // graph.vert (m.perm d) = graph.vert m.base ∧
      label d = label m.base} =
      ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
        fun d ↦ label d = label m.base).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
  have hEmptyD : (({wd.tracks.iso.dart first, wd.tracks.iso.dart second} : Finset D).filter
      fun d ↦ label d = label m.base) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact label_dart_lift_ne_base m wd first (alphaWall m wd base)
        (hFirst.trans (congrArg NonDanglingEdge.stablePath (alphaLift_eq m wd base)))
    · exact label_dart_lift_ne_base m wd second (deltaWall m wd base)
        (hSecond.trans (congrArg NonDanglingEdge.stablePath (deltaLift_eq m wd base)))
  have hR : ((Finset.univ.filter fun d : D ↦ graph.vert (m.perm d) = graph.vert m.base).filter
      fun d ↦ label d = label m.base).card = 1 := by
    rw [filter_moved_base m wd first second hStar, Finset.filter_insert, ite_eq_left rfl, hEmptyD]
    simp
  rw [hRHS, hR]
  show incidenceCount (validCandidate base hValid).datum
    (endpointVertex base hValid false base.hubSheet) (bridgeRow base hValid) = 1
  have hEmptyC : (({bridgeDeltaND base hValid, alphaRetained base hValid} :
        Finset (NonDanglingEdge (validCandidate base hValid).datum)).filter
      fun e ↦ e.stablePath = bridgeRow base hValid) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · rw [stablePath_bridgeDeltaND base hValid]
      exact retainedRow_ne_bridgeRow base hValid _
    · rw [stablePath_alphaRetained base hValid]
      exact retainedRow_ne_bridgeRow base hValid _
  unfold incidenceCount
  rw [incidentEdges_hubLeft base hValid, Finset.filter_insert,
    ite_eq_left (stablePath_bridgeND base hValid), hEmptyC]
  simp

/-! ### The leftover equation at `A_v`, and the link -/

/-- **The star count at every branch vertex except `A_v`.** -/
theorem incidence_of_ne_rightAnchor
    (hPres : PrescribedSimpleMove m wd base)
    (v : BranchVertex (validCandidate base hValid).datum)
    (hv : v ≠ candBranchMap base hValid (Sum.inr true))
    (r : StablePath (validCandidate base hValid).datum) :
    incidenceCount (validCandidate base hValid).datum v.1 r =
      Nat.card {d : D // graph.vert (m.perm d) = vertexEquiv m wd base hValid v ∧
        label d = (NonTrivalentValencyThreeSimpleExit.wallOutgoingFD m wd base
          hValid).labelling.row r} := by
  classical
  obtain ⟨x, rfl⟩ : ∃ x, candBranchMap base hValid x = v :=
    ⟨(candBranchEquiv base hValid).symm v, (candBranchEquiv base hValid).apply_symm_apply v⟩
  obtain ⟨r', rfl⟩ : ∃ r', rowMap base hValid r' = r :=
    ⟨rowEquiv base hValid r, (rowEquiv base hValid).left_inv r⟩
  cases x with
  | inl w =>
    cases r' with
    | none => exact incidence_inl_bridge m wd base hValid hPres.1 w
    | some rg =>
      obtain ⟨p, rfl⟩ : ∃ p, gaugeStablePath base hValid p = rg :=
        ⟨(gaugeStablePath base hValid).symm rg, Equiv.apply_symm_apply _ _⟩
      exact incidence_inl_retained m wd base hValid hPres.1 w p
  | inr side =>
    cases side with
    | true => exact absurd rfl hv
    | false =>
      cases r' with
      | none => exact incidence_inr_false_bridge m wd base hValid hPres
      | some rg =>
        obtain ⟨p, rfl⟩ : ∃ p, gaugeStablePath base hValid p = rg :=
          ⟨(gaugeStablePath base hValid).symm rg, Equiv.apply_symm_apply _ _⟩
        exact incidence_inr_false_retained m wd base hValid hPres p

/-- **The star count at `A_v`, from the leftover equation.**  A stable row of
the candidate meets its branch vertices twice in all, a chart row carries two
darts of the moved graph, `vertexEquiv` is a bijection, and the count agrees at
every other branch vertex; so it agrees at `A_v` too. -/
theorem incidence_inr_true
    (hPres : PrescribedSimpleMove m wd base)
    (r : StablePath (validCandidate base hValid).datum) :
    incidenceCount (validCandidate base hValid).datum
        (candBranchMap base hValid (Sum.inr true)).1 r =
      Nat.card {d : D // graph.vert (m.perm d) =
          vertexEquiv m wd base hValid (candBranchMap base hValid (Sum.inr true)) ∧
        label d = (NonTrivalentValencyThreeSimpleExit.wallOutgoingFD m wd base
          hValid).labelling.row r} := by
  classical
  set outFD := NonTrivalentValencyThreeSimpleExit.wallOutgoingFD m wd base hValid with houtFD
  set v₀ := candBranchMap base hValid (Sum.inr true) with hv₀
  set f : BranchVertex (validCandidate base hValid).datum → ℕ :=
    fun v ↦ incidenceCount (validCandidate base hValid).datum v.1 r with hf
  set g : BranchVertex (validCandidate base hValid).datum → ℕ :=
    fun v ↦ Nat.card {d : D // graph.vert (m.perm d) = vertexEquiv m wd base hValid v ∧
      label d = outFD.labelling.row r} with hg
  have hSumF : ∑ v, f v = 2 :=
    sum_incidenceCount_branchVertex (validCandidate base hValid).datum outFD.connected
      outFD.pathEnds r
  have hSumG : ∑ v, g v = 2 := by
    rw [Fintype.sum_equiv (vertexEquiv m wd base hValid) g
      (fun x : V ↦ Nat.card {d : D // graph.vert (m.perm d) = x ∧
        label d = outFD.labelling.row r}) (fun v ↦ rfl)]
    exact sum_natCard_moved m wd (outFD.labelling.row r)
  have hAway : ∀ v ∈ Finset.univ.erase v₀, f v = g v := by
    intro v hv
    exact incidence_of_ne_rightAnchor m wd base hValid hPres v (Finset.mem_erase.mp hv).1 r
  have hfsum := Finset.add_sum_erase Finset.univ f (Finset.mem_univ v₀)
  have hgsum := Finset.add_sum_erase Finset.univ g (Finset.mem_univ v₀)
  have hEq : ∑ x ∈ Finset.univ.erase v₀, f x = ∑ x ∈ Finset.univ.erase v₀, g x :=
    Finset.sum_congr rfl hAway
  show f v₀ = g v₀
  omega

/-- **The star count, at every branch vertex and every row.**  This is the one
geometric obligation of `NonTrivalentValencyThreeSimpleTracks.typeChangeLink_of_incidence`,
proved under (H-I/II). -/
theorem incidence_of_prescribedSimpleMove
    (hPres : PrescribedSimpleMove m wd base)
    (v : BranchVertex (validCandidate base hValid).datum)
    (r : StablePath (validCandidate base hValid).datum) :
    incidenceCount (validCandidate base hValid).datum v.1 r =
      Nat.card {d : D // graph.vert (m.perm d) = vertexEquiv m wd base hValid v ∧
        label d = (NonTrivalentValencyThreeSimpleExit.wallOutgoingFD m wd base
          hValid).labelling.row r} := by
  classical
  by_cases hv : v = candBranchMap base hValid (Sum.inr true)
  · subst hv
    exact incidence_inr_true m wd base hValid hPres r
  · exact incidence_of_ne_rightAnchor m wd base hValid hPres v hv r

/-- **`OuterWalk.TypeChangeLink` at a three-valent wall, Types I and II, under
(H-I/II).**  `NonTrivalentValencyThreeSimpleTracks` reduces the link to the star
count; this discharges it. -/
def typeChangeLink_of_prescribedSimpleMove
    (hPres : PrescribedSimpleMove m wd base) :
    TypeChangeLink m wd :=
  typeChangeLink_of_incidence m wd base hValid
    (incidence_of_prescribedSimpleMove m wd base hValid hPres)

/-! ### Relative non-vacuity -/

/-- **Relative non-vacuity of the headline.**  At a wall whose vanishing
occurrence is oriented with its `A_u` end at `graph.vert m.base`, and whose two
paired survivors `e_alpha`, `e_delta` sit at the two different ends,
`NonTrivalentValencyThreeSimpleTracks.prescribedMove` -- which contracts the
*same* edge as `m` -- satisfies (H-I/II), so the link above is an actual
inhabitant for that move.  As in `NonTrivalentValencyThreeSimpleTracks`, an
absolute `exists m, ...` does not typecheck, because
`wd : WallData arrival` with
`arrival : FacetArrival degree graph label (label m.base)` fixes `m.base`. -/
def typeChangeLink_of_simpleSeparated
    (hSep : SimpleSeparated m wd base)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    TypeChangeLink (prescribedMove m wd base hSep hBase) wd :=
  typeChangeLink_of_prescribedSimpleMove (prescribedMove m wd base hSep hBase) wd base hValid
    (prescribedSimpleMove_prescribedMove m wd base hSep hBase)

end Wall


end

end DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleStarCount
