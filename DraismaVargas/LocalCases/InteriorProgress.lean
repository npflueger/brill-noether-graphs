module

public import DraismaVargas.LocalCases.OuterWalk
public import DraismaVargas.LocalCases.TrackedWallProgressMore
public import DraismaVargas.LocalCases.WallAdmissibility
public import DraismaVargas.LocalCases.WallAdmissibilityStable
public import DraismaVargas.LocalCases.ReachableMarch

@[expose] public section

/-!
# Interior progress: tracked progress at every nonterminal state of a cone

Source: Vargas, Part II, arXiv:2609.09109, the wall-crossing proposition
(`proposition-walking-through-II`) and the proof of the main theorem, in which a
path from a caterpillar of loops crosses finitely many walls; read against the
ten-way interior classification of Draisma–Vargas Part I, arXiv:1909.12924
(`IncomingSourceCases`), and the tracked wiring of `TrackedWallProgress` /
`TrackedWallProgressMore`.

This file supplies, in tracked form, the hypothesis of
`OuterWalk.coneEntry_of_reaches` that concerns interior (non-type-changing)
walls -- its other hypothesis, `link`, is the type change at a non-trivalent
wall:

```
interior : ∀ K, Reaches G K → ∀ baseStart baseFinish
  (current : TrackedState degree K label (MatrixAtlas.atlasMatrix …) baseStart baseFinish),
  ¬ current.Terminal → TrackedProgress current
```

It is reduced here to three named inputs -- the per-tag bridges, the march's
metric facts and the genericity of the start -- and six of the ten per-tag
bridges are proved outright.

## What is proved here

### 1.  The wall metric and the classification at one chart coordinate

`AdmissibleColumn fullDim column` says the cover `fullDim` admits a
*nonnegative* chart point vanishing at `column` whose stable rows are all
nonzero -- the interior (non-type-changing) wall metric at that coordinate.
Everything else at that coordinate is derived with no further hypothesis:

* `hc_column`, `hab_column`, `hOne_column`: the coordinate's target occurrence,
  its two distinct endpoints and their unit multiplicity, from
  `GluingContraction.fst_ne_snd` and
  `IteratedContraction.num_edges_eq_one_of_genus_zero_of_connected` at the
  presentation's own `targetConnected`/`targetGenus`.  The target of a
  full-dimensional presentation is a tree, so *every* coordinate has them.
* `nonempty_classification_of_admissibleColumn`: the ten-way
  `IncomingSourceCases.Classification` at that occurrence, with **all three**
  wall-degeneration inputs discharged --
  `WallAdmissibilityStable.stablePath_equiv`,
  `WallAdmissibility.danglingCompatible_of_fullDimensional` and
  `WallAdmissibilityStable.trivalent_of_fullDimensional`.  Nothing about
  `hStable`/`hCompat`/`hTrivalent` is carried anywhere in this file.
* `admissibleColumn_of_state` and `admissibleColumn_of_firstWall`: the march's
  own supply.  At an interior time
  `0 ≤ t < 1` of a state whose registered chart is the cover's honest length
  matrix, `NonTrivalentWallSetup.rows_ne_zero_of_lt_one` gives the rows, so a
  nonnegative point of the segment vanishing at `column` is an admissible
  metric.  Its three side conditions are the march's metric facts:
  `0 ≤ restartTime` (reachability from a time-zero seed), `0 < baseStart` and
  `0 ≤ baseFinish`.
* `exists_admissibleColumn_of_nonterminal`: at a nonterminal state with
  `SimpleNegativeCrossings`, `RationalAffineWall.exists_first_positiveOrthant_exit`
  produces the first wall, and that coordinate *is* admissible.  So the
  coordinate the march actually crosses always satisfies the hypothesis.
* `separated_of_admissibleColumn` and
  `not_admissibleColumn_of_stablePath_over_column`: admissibility at `column`
  is exactly "no stable class of the cover lies entirely over `column`",
  which is what separates an interior crossing from a Part II wall.
* `admissibleColumn_of_offColumn_entry`: the concrete sufficient condition --
  a nonnegative length matrix with one positive off-`column` entry in every
  row -- inhabiting `AdmissibleColumn` with no march at all.

### 2.  The per-tag bridges and the ten-way dispatcher

`W4Bridge`, `W3Bridge tag`, `W2Bridge tag` are the per-tag inputs, each landing
in `Nonempty (TrackedWallProgress.TrackedRoutedWall …)`: given the cover, the
crossed coordinate, the chart identity, the incoming `Tracks` and the wall
metric, together with the tag's own star/input/profile as the classification
hands them over, produce that coordinate's tracked routed wall.
`wallBridge_of_tagBridges` dispatches over all ten tags by the
classification's own case analysis and produces `WallBridge`, a tracked routed
wall at one chart, in exactly the shape
`TrackedWallProgressMore.TrackedClassified` consumes.

Six of the ten tags are discharged here: `w4Bridge_w4` (Equation (1)),
`w3Bridge_nd2` (Figure 31), `w3Bridge_nd3` (Figure 30), `w2Bridge_m11`
(Figure 32), `w2Bridge_p` (Equation (9)) and `w2Bridge_r1` (Equation (10)).
Each is the same three steps: the per-tag payload extractor
(`exists_w2*_payload`, or the classification's own constructor for the
trivalent tags) hands the local data out of the classification;
`exists_matched_tracking` identifies the incoming cover as a *named family
member* carrying its own honest presentation, its row equation and hence an
`InteriorGraphTracking.Tracks`; and the family's regrown column is the crossed
coordinate.  Then `TrackedWallProgress.trackedW4`/`trackedNd2`/`trackedNd3`/
`trackedW2M11`/`trackedW2P`/`trackedW2R1` apply.  The contraction forest and
the dangling compatibility are derived from the wall metric inside each
bridge, so nothing is carried.

Two small identities for the `w3Nd2CoarseFine`/`w3Nd3CoarseFine` tags are
proved here: `nd2WallColumn_eq`/`nd3WallColumn_eq`, that the family's regrown
column is the identified member's own wall occurrence (the analogue of
`W4PositiveExit.wallColumn_eq`, `A04MoreTags.ofW2P_family_wallColumn`,
`A04R1Wiring.r1Family_wallColumn` and `A04M11Wiring.m11Family_wallColumn`, by
the same `Equiv` cancellation); and
`ofNd2CoarseFine_family_matrix`/`ofNd3CoarseFine_family_matrix`, that the wall
input presents member `i` by that member's own honest square matrix
(`fin_cases`, because `W3WallInput.nd2Presentation` is defined by cases).

### 3.  The assembly

`trackedClassified_of_state`, `trackedProgress_of_bridge`,
`interior_of_bridges` and `coneEntry_of_reaches_of_bridges`: the tracked
classification at a state, the tracked progress
(`TrackedWallProgressMore.trackedProgressOfTrackedClassification`), the
`interior` hypothesis in literally the shape `OuterWalk.coneEntry_of_reaches`
takes, and the application to that theorem, so the fit is checked by Lean.

## The hypotheses that remain explicit in this file

* Four of the ten per-tag bridges are *named here* as hypotheses --
  `w3Four`, `w3Shift`, `w2M1k` and `w2Mkk` -- and `wallBridge_of_remaining` is
  the whole of `WallBridge` at one chart on exactly those four.  They are
  proved in modules that import this one: `w3Bridge_shift` and
  `w3Bridge_four` in `InteriorBridgesTrivalent`, `w2Bridge_m1k` and
  `w2Bridge_mkk` in `InteriorBridgesDivalent`, and
  `InteriorBridgesAll.wallBridge` is `WallBridge` with no hypothesis at all.
* The three metric facts of the march: `0 < baseStart`, `0 ≤ baseFinish` and
  `0 ≤ current.restartTime`, quantified over the chain exactly as `interior`
  is (`interior_of_bridges`'s `metric` argument).  They are *not* a consequence
  of the classification: `OuterWalk.exists_facetArrival` has all three at its
  point of use (the cone entry's `hstart`, the facet-generic finish of
  `FacetGenericity.exists_facetGeneric` and
  `OuterWalkInterior.restartTime_nonneg_of_reachable`), and
  `OuterWalkInterior.interior'_of_bridges` discharges them from the restated
  binder, leaving only the per-tag bridges.

  The wall metric is asked for only at the coordinate the march actually
  crosses: `SemanticAtlasMarch.State.PresentedProgress` and
  `TrackedWallProgressMore.TrackedClassified` are restricted to
  `SemanticAtlasMarch.IsFirstWall`, where `admissibleColumn_of_firstWall`
  supplies the metric outright.  Asking it at **every** chart coordinate of the
  state's cover would be too strong: `not_admissibleColumn_of_stablePath_over_column`
  exhibits a coordinate carrying a whole stable class, which admits no interior
  metric at all.
* `SimpleNegativeCrossings` at every state, exactly as in
  `TrackedWallProgress.exists_terminal_tracked_caterpillar_of_routedWalls`.  As
  with the metric facts, this is a genuine argument of `interior_of_bridges` in
  *this* file, but at the level of the walk it is derived:
  `OuterWalkInterior.interior'_unconditional` obtains it from the cone entry's
  own `AtlasGeneric` (`hgeneric.simpleNegativeCrossings`), so no genericity
  hypothesis reaches `OuterWalk.coneEntry_of_reaches` either.

Nothing here identifies a graph by a matrix: every tracking travels along the
actual `StableGraphIncidence.Equivalence` that `exists_matched_tracking`
returns.  The source-side demand of `SemanticAtlasMarch`, `WallProgress`,
`A04FourTags`, `A04MoreTags`, `TrackedState`, `TrackedWallProgress` and
`TrackedWallProgressMore` is guarded by `SemanticAtlasMarch.IsFirstWall`;
`OuterWalk` is consumed verbatim, and the restated `interior` binder it needs
lives in `OuterWalkInterior`.

Consumer: `OuterWalk.coneEntry_of_reaches` (through `interior_of_bridges`), and
through it the outer walk's `OuterWalk.exists_terminal_of_chain`.
-/

namespace DraismaVargas.LocalCases.InteriorProgress

noncomputable section

open Utilities
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.RationalAffineWall
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.InteriorGraphTracking

/-! ## 1.  The wall metric and the classification at one chart coordinate -/

section Column

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}

/-- **The interior wall metric at one chart coordinate.**  A nonnegative chart
point that vanishes at `column` and keeps every stable row length nonzero.
This is precisely the metric input of `IncomingSourceCases.exists_classification`,
and it is what distinguishes an interior crossing from a Part II wall: by
`separated_of_admissibleColumn` it says no stable class of the cover lies
entirely over the coordinate's target occurrence. -/
def AdmissibleColumn (fullDim : FullDimensionalSourcePresentation data coordinate)
    (column : coordinate) : Prop :=
  ∃ z : coordinate → ℚ, (∀ c, 0 ≤ z c) ∧ z column = 0 ∧
    ∀ row, (GluingDatum.LengthMatrixPresentation.matrix
      fullDim.labelling.presentation).mulVec z row ≠ 0

variable (fullDim : FullDimensionalSourcePresentation data coordinate) (column : coordinate)

/-- The target occurrence the coordinate names.  The cover's target is a tree,
so this is a non-loop of multiplicity one at every coordinate. -/
abbrev contractedEdge : target.edges := fullDim.labelling.targetEdge column

/-- Its first endpoint. -/
abbrev leftEnd : target.V := (contractedEdge fullDim column : target.V × target.V).1

/-- Its second endpoint. -/
abbrev rightEnd : target.V := (contractedEdge fullDim column : target.V × target.V).2

/-- The contracted occurrence's endpoint pair, definitionally. -/
theorem hc_column :
    ((contractedEdge fullDim column : target.V × target.V)) =
      (leftEnd fullDim column, rightEnd fullDim column) := rfl

/-- A tree has no loops. -/
theorem hab_column : leftEnd fullDim column ≠ rightEnd fullDim column :=
  GluingContraction.fst_ne_snd _

/-- A connected genus-zero target has a single edge between any two vertices. -/
theorem hOne_column :
    num_edges target (leftEnd fullDim column) (rightEnd fullDim column) = 1 :=
  IteratedContraction.num_edges_eq_one_of_genus_zero_of_connected target
    fullDim.targetConnected fullDim.targetGenus _

/-- The occurrence dictionary sends the occurrence back to its coordinate. -/
theorem targetEdge_symm_contractedEdge :
    fullDim.labelling.targetEdge.symm (contractedEdge fullDim column) = column :=
  Equiv.symm_apply_apply _ _

/-- **The interior classification at an admissible coordinate.**  The ten-way
`IncomingSourceCases.Classification` of the coordinate's contracted wall
datum, with all three wall-degeneration inputs discharged from the metric
alone.  No `hStable`, `hCompat` or `hTrivalent` is carried. -/
theorem nonempty_classification_of_admissibleColumn
    (h : AdmissibleColumn fullDim column) :
    Nonempty (IncomingSourceCases.Classification
      (contractDatum data (hc_column fullDim column) (hab_column fullDim column)
        (hOne_column fullDim column)) ⟨leftEnd fullDim column, hab_column fullDim column⟩) := by
  obtain ⟨z, hNonneg, hZeroCol, hRows⟩ := h
  have hZero : z (fullDim.labelling.targetEdge.symm (contractedEdge fullDim column)) = 0 := by
    rw [targetEdge_symm_contractedEdge]; exact hZeroCol
  exact IncomingSourceCases.exists_classification (coordinate := coordinate) data
    (hc_column fullDim column) (hab_column fullDim column) (hOne_column fullDim column)
    fullDim z hNonneg hRows hZero
    (WallAdmissibilityStable.stablePath_equiv data (hc_column fullDim column)
      (hab_column fullDim column) (hOne_column fullDim column) fullDim z hNonneg hRows hZero)
    (WallAdmissibility.danglingCompatible_of_fullDimensional data (hc_column fullDim column)
      (hab_column fullDim column) (hOne_column fullDim column) fullDim z hNonneg hRows hZero)
    (WallAdmissibilityStable.trivalent_of_fullDimensional data (hc_column fullDim column)
      (hab_column fullDim column) (hOne_column fullDim column) fullDim z hNonneg hRows hZero)

/-- **From the march.**  At an interior time of a reached state whose chart is
the cover's own honest length matrix, the stable rows are all positive
(`NonTrivalentWallSetup.rows_ne_zero_of_lt_one`), so a nonnegative point of the
segment vanishing at `column` is an admissible wall metric.  The three side
conditions are the march's metric facts: `0 ≤ restartTime`, `0 < baseStart`,
`0 ≤ baseFinish`. -/
theorem admissibleColumn_of_state {chart : Type*} [Fintype chart] [DecidableEq chart]
    {matrix : chart → Matrix coordinate coordinate ℚ}
    {baseStart baseFinish : coordinate → ℚ}
    (state : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (hmatrix : GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation =
      matrix state.label)
    (hstart : ∀ i, 0 < baseStart i) (hfinish : ∀ i, 0 ≤ baseFinish i)
    (hrestart : 0 ≤ state.restartTime) {time : ℚ} (h0 : 0 ≤ time) (h1 : time < 1)
    (hNonneg : ∀ c, 0 ≤ segment state.currentStart state.currentFinish time c)
    (hZeroCol : segment state.currentStart state.currentFinish time column = 0) :
    AdmissibleColumn fullDim column :=
  ⟨segment state.currentStart state.currentFinish time, hNonneg, hZeroCol,
    NonTrivalentWallSetup.rows_ne_zero_of_lt_one fullDim state hmatrix hstart hfinish
      hrestart h0 h1⟩

/-- **A concrete sufficient condition, with no march.**  A nonnegative length
matrix with one strictly positive off-`column` entry in every row makes the
indicator of the complement of `column` an admissible wall metric.  This is the
non-vacuity witness of `AdmissibleColumn`. -/
theorem admissibleColumn_of_offColumn_entry
    (hNonneg : ∀ i j, 0 ≤ GluingDatum.LengthMatrixPresentation.matrix
      fullDim.labelling.presentation i j)
    (hOff : ∀ row, ∃ c, c ≠ column ∧
      0 < GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation row c) :
    AdmissibleColumn fullDim column := by
  classical
  refine ⟨fun c ↦ if c = column then 0 else 1, ?_, by simp, ?_⟩
  · intro c; by_cases h : c = column <;> simp [h]
  · intro row
    have : 0 < (GluingDatum.LengthMatrixPresentation.matrix
        fullDim.labelling.presentation).mulVec (fun c ↦ if c = column then 0 else 1) row := by
      obtain ⟨c, hc, hpos⟩ := hOff row
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_pos' (fun j _ ↦ ?_) ⟨c, Finset.mem_univ c, ?_⟩
      · by_cases hj : j = column <;> simp [hj, hNonneg row j]
      · simp [hc, hpos]
    exact this.ne'

/-- **What admissibility says.**  Every stable class of the incoming cover has
a surviving occurrence off the contracted one
(`WallAdmissibilityStable.exists_stablePath_eq_target_ne`). -/
theorem separated_of_admissibleColumn (h : AdmissibleColumn fullDim column)
    (edge : W4StableSource.NonDanglingEdge data) :
    ∃ other : W4StableSource.NonDanglingEdge data,
      other.stablePath = edge.stablePath ∧ other.1.1.1 ≠ contractedEdge fullDim column := by
  obtain ⟨z, _, hZeroCol, hRows⟩ := h
  refine WallAdmissibilityStable.exists_stablePath_eq_target_ne fullDim.labelling z hRows ?_ edge
  rw [targetEdge_symm_contractedEdge]; exact hZeroCol

/-- **Every first wall of the state's current segment is admissible.**  This is
`admissibleColumn_of_state` with the metric point read off the guard
`SemanticAtlasMarch.IsFirstWall`, and it is the step that lets the first-wall
restricted `PresentedProgress` be supplied at all: the march asks for wall data
only where `IsFirstWall` holds, and there the interior wall metric exists. -/
theorem admissibleColumn_of_firstWall {chart : Type*} [Fintype chart]
    [DecidableEq chart] {matrix : chart → Matrix coordinate coordinate ℚ}
    {baseStart baseFinish : coordinate → ℚ}
    (state : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (hmatrix : GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation =
      matrix state.label)
    (hstart : ∀ i, 0 < baseStart i) (hfinish : ∀ i, 0 ≤ baseFinish i)
    (hrestart : 0 ≤ state.restartTime)
    (hw : SemanticAtlasMarch.IsFirstWall state.currentStart state.currentFinish column) :
    AdmissibleColumn fullDim column := by
  obtain ⟨time, h0, h1, hNonneg, hZero⟩ := hw.exists_nonneg_zero
  exact admissibleColumn_of_state fullDim column state hmatrix hstart hfinish hrestart
    h0 h1 hNonneg hZero

/-- **The first wall of a nonterminal march is admissible.** -/
theorem exists_admissibleColumn_of_nonterminal {chart : Type*} [Fintype chart]
    [DecidableEq chart] {matrix : chart → Matrix coordinate coordinate ℚ}
    {baseStart baseFinish : coordinate → ℚ}
    (state : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (hmatrix : GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation =
      matrix state.label)
    (hstart : ∀ i, 0 < baseStart i) (hfinish : ∀ i, 0 ≤ baseFinish i)
    (hrestart : 0 ≤ state.restartTime)
    (hsimple : SimpleNegativeCrossings state.currentStart state.currentFinish)
    (hNonterminal : ¬ FiniteAtlasMarch.State.Terminal state) :
    ∃ column : coordinate, AdmissibleColumn fullDim column := by
  have houtside : ∃ i, state.currentFinish i < 0 := by
    simp only [FiniteAtlasMarch.State.Terminal, not_forall, not_le] at hNonterminal
    exact hNonterminal
  obtain ⟨wall, time, htPos, htLt, hzero, hpos, -⟩ :=
    exists_first_positiveOrthant_exit state.currentStart state.currentFinish
      state.currentStart_positive houtside hsimple
  refine ⟨wall, admissibleColumn_of_state fullDim wall state hmatrix hstart hfinish hrestart
    htPos.le htLt (fun c ↦ ?_) hzero⟩
  by_cases hcw : c = wall
  · subst hcw; exact le_of_eq hzero.symm
  · exact (hpos c hcw).le

/-- **Why admissibility can fail.**  If some stable class of the incoming cover
lies entirely over the coordinate's target occurrence, contracting that
occurrence kills a stable row and there is no interior wall metric at all: the
crossing is a Part II type change, not an interior wall.  This is the exact
converse of `separated_of_admissibleColumn`.  It is why the march asks for the
wall metric only at the first-wall coordinate, not at every chart coordinate
(see the module docstring). -/
theorem not_admissibleColumn_of_stablePath_over_column
    (edge : W4StableSource.NonDanglingEdge data)
    (hAll : ∀ other : W4StableSource.NonDanglingEdge data,
      other.stablePath = edge.stablePath → other.1.1.1 = contractedEdge fullDim column) :
    ¬ AdmissibleColumn fullDim column := by
  intro h
  obtain ⟨other, hPath, hNe⟩ := separated_of_admissibleColumn fullDim column h edge
  exact hNe (hAll other hPath)

end Column

/-! ## 2.  The per-tag bridges and the ten-way dispatcher -/

section Bridges

open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W4TargetPairings
open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.ClassifiedContinuation (SourceCase)

variable (degree : ℕ) (coordinate : Type) [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  (chart : Matrix coordinate coordinate ℚ) (graph : CubicDartGraph D V) (label : D → coordinate)

/-- **A tracked routed wall at one chart, in the shape
`TrackedWallProgressMore.TrackedClassified` consumes.**  At every cover
displaying the chart, with its tracking, and at
every coordinate carrying an interior wall metric, a tracked routed wall. -/
def WallBridge : Prop :=
  ∀ (target : CFGraph.{0}) (data : GluingDatum target degree)
    (fullDim : FullDimensionalSourcePresentation data coordinate) (column : coordinate),
    GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation = chart →
    Tracks fullDim graph label → AdmissibleColumn fullDim column →
      Nonempty (TrackedWallProgress.TrackedRoutedWall degree coordinate chart column graph label)

/-- **The four-valent bridge**, Equation (1).  The classification's own
`FourStar` and `AuxR0SourceInput` are handed over; what a producer
(`TrackedWallProgress.trackedW4`) additionally needs is the incoming member
index with its full-dimensional presentation, its nonsingularity and its matrix
identity. -/
def W4Bridge : Prop :=
  ∀ (target : CFGraph.{0}) (data : GluingDatum target degree)
    (fullDim : FullDimensionalSourcePresentation data coordinate) (column : coordinate),
    GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation = chart →
    Tracks fullDim graph label → AdmissibleColumn fullDim column →
    ∀ (star : FourStar (contract target (hab_column fullDim column) (hOne_column fullDim column))
        ⟨leftEnd fullDim column, hab_column fullDim column⟩),
      AuxR0SourceInput (contractDatum data (hc_column fullDim column)
        (hab_column fullDim column) (hOne_column fullDim column)) star →
      Nonempty (TrackedWallProgress.TrackedRoutedWall degree coordinate chart column graph label)

/-- **A trivalent bridge, one tag** (`w3Four`, `w3Shift`, `w3Nd3CoarseFine`,
`w3Nd2CoarseFine`).  From the cover, the crossed coordinate, the chart identity,
the incoming tracking and the wall metric, together with the classification's
own three-star, source input and profile of that tag, a tracked routed wall. -/
def W3Bridge (tag : SourceCase) : Prop :=
  ∀ (target : CFGraph.{0}) (data : GluingDatum target degree)
    (fullDim : FullDimensionalSourcePresentation data coordinate) (column : coordinate),
    GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation = chart →
    Tracks fullDim graph label → AdmissibleColumn fullDim column →
    ∀ (star : ThreeStar (contract target (hab_column fullDim column) (hOne_column fullDim column))
        ⟨leftEnd fullDim column, hab_column fullDim column⟩)
      (input : W3SourceInput (contractDatum data (hc_column fullDim column)
        (hab_column fullDim column) (hOne_column fullDim column)) star)
      (classification : W3IncomingClassification.Classification
        (contractDatum data (hc_column fullDim column) (hab_column fullDim column)
          (hOne_column fullDim column)) star input),
      classification.sourceCase = tag →
      Nonempty (TrackedWallProgress.TrackedRoutedWall degree coordinate chart column graph label)

/-- **A divalent bridge, one tag** (`w2M11`, `w2M1k`, `w2Mkk`, `w2P`, `w2R1`).
From the cover, the crossed coordinate, the chart identity, the incoming
tracking and the wall metric, together with the classification's own two-star,
source input and profile of that tag, a tracked routed wall. -/
def W2Bridge (tag : SourceCase) : Prop :=
  ∀ (target : CFGraph.{0}) (data : GluingDatum target degree)
    (fullDim : FullDimensionalSourcePresentation data coordinate) (column : coordinate),
    GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation = chart →
    Tracks fullDim graph label → AdmissibleColumn fullDim column →
    ∀ (star : TwoStar (contract target (hab_column fullDim column) (hOne_column fullDim column))
        ⟨leftEnd fullDim column, hab_column fullDim column⟩)
      (input : W2SourceInput (contractDatum data (hc_column fullDim column)
        (hab_column fullDim column) (hOne_column fullDim column)) star)
      (classification : IncomingSourceCases.W2.Classification
        (contractDatum data (hc_column fullDim column) (hab_column fullDim column)
          (hOne_column fullDim column)) star input),
      classification.sourceCase = tag →
      Nonempty (TrackedWallProgress.TrackedRoutedWall degree coordinate chart column graph label)

/-- **The ten-way dispatcher.**  The classification's own case analysis: the
wall metric selects the tag, and the tag's bridge produces that coordinate's
tracked routed wall. -/
theorem wallBridge_of_tagBridges
    (b4 : W4Bridge degree coordinate chart graph label)
    (b3Four : W3Bridge degree coordinate chart graph label SourceCase.w3Four)
    (b3Shift : W3Bridge degree coordinate chart graph label SourceCase.w3Shift)
    (b3Nd3 : W3Bridge degree coordinate chart graph label SourceCase.w3Nd3CoarseFine)
    (b3Nd2 : W3Bridge degree coordinate chart graph label SourceCase.w3Nd2CoarseFine)
    (b2M11 : W2Bridge degree coordinate chart graph label SourceCase.w2M11)
    (b2M1k : W2Bridge degree coordinate chart graph label SourceCase.w2M1k)
    (b2Mkk : W2Bridge degree coordinate chart graph label SourceCase.w2Mkk)
    (b2P : W2Bridge degree coordinate chart graph label SourceCase.w2P)
    (b2R1 : W2Bridge degree coordinate chart graph label SourceCase.w2R1) :
    WallBridge degree coordinate chart graph label := by
  intro target data fullDim column hChart tracks hAdmissible
  obtain ⟨classification⟩ :=
    nonempty_classification_of_admissibleColumn fullDim column hAdmissible
  cases classification with
  | w4 star input => exact b4 target data fullDim column hChart tracks hAdmissible star input
  | w3 star input profile =>
    cases profile with
    | four sourceProfile directions largest_index pair_index =>
      exact b3Four target data fullDim column hChart tracks hAdmissible star input
        (.four sourceProfile directions largest_index pair_index) rfl
    | shift sourceProfile directions largest_lt indices_two_le =>
      exact b3Shift target data fullDim column hChart tracks hAdmissible star input
        (.shift sourceProfile directions largest_lt indices_two_le) rfl
    | nd3CoarseFine sourceProfile same_direction pair_index largest_index =>
      exact b3Nd3 target data fullDim column hChart tracks hAdmissible star input
        (.nd3CoarseFine sourceProfile same_direction pair_index largest_index) rfl
    | nd2CoarseFine sourceProfile =>
      exact b3Nd2 target data fullDim column hChart tracks hAdmissible star input
        (.nd2CoarseFine sourceProfile) rfl
  | w2 star input profile =>
    cases profile with
    | m11 block source deleted_target pair_card single_succ_card background first_one
        second_one third_one block_card_two =>
      exact b2M11 target data fullDim column hChart tracks hAdmissible star input
        (.m11 block source deleted_target pair_card single_succ_card background first_one
          second_one third_one block_card_two) rfl
    | m1k block source deleted_target pair_card single_succ_card background unit_large =>
      exact b2M1k target data fullDim column hChart tracks hAdmissible star input
        (.m1k block source deleted_target pair_card single_succ_card background unit_large) rfl
    | mkk block source deleted_target pair_card single_succ_card background first_two_le
        second_two_le =>
      exact b2Mkk target data fullDim column hChart tracks hAdmissible star input
        (.mkk block source deleted_target pair_card single_succ_card background first_two_le
          second_two_le) rfl
    | p block source deleted_target pair_succ_card single_card background =>
      exact b2P target data fullDim column hChart tracks hAdmissible star input
        (.p block source deleted_target pair_succ_card single_card background) rfl
    | r1 first second distinct firstProfile secondProfile background =>
      exact b2R1 target data fullDim column hChart tracks hAdmissible star input
        (.r1 first second distinct firstProfile secondProfile background) rfl

end Bridges

/-! ## 3.  The assembly: `interior` -/

section Progress

open DraismaVargas.LocalCases.SemanticAtlasMarch
open DraismaVargas.LocalCases.TrackedWallProgress
open DraismaVargas.LocalCases.TrackedWallProgressMore

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  {baseStart baseFinish : coordinate → ℚ}

/-- **The tracked classification at one state.**  The payload's own retained
cover, its chart identity and its tracking are read off
`TrackedState.carriesTrackedPencil` under one binder; nothing is chosen twice
and no matrix identifies a graph.

The wall metric is not a hypothesis.  `TrackedClassified` is asked only at
a first wall of the state's own segment, and there `admissibleColumn_of_firstWall`
produces `AdmissibleColumn` outright from the three metric facts of the march
(`0 < baseStart`, `0 ≤ baseFinish`, `0 ≤ restartTime`). -/
theorem trackedClassified_of_state
    (current : TrackedState degree graph label
      (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
      baseStart baseFinish)
    (bridge : WallBridge degree coordinate
      (MatrixAtlas.atlasMatrix current.toMatrixState.label) graph label)
    (hstart : ∀ i, 0 < baseStart i) (hfinish : ∀ i, 0 ≤ baseFinish i)
    (hrestart : 0 ≤ current.toMatrixState.restartTime) :
    TrackedClassified degree coordinate
      (MatrixAtlas.atlasMatrix current.toMatrixState.label)
      current.toMatrixState.currentStart current.toMatrixState.currentFinish
      graph label := by
  intro column hw
  obtain ⟨target, data, wallVertex, candidate, fullDim, hmatrix, -, -, -, -, ⟨tracks⟩, -⟩ :=
    current.carriesTrackedPencil
  exact bridge _ _ fullDim column hmatrix tracks
    (admissibleColumn_of_firstWall fullDim column current.toMatrixState hmatrix hstart
      hfinish hrestart hw)

/-- **The tracked progress at one state.**  This is
`TrackedWallProgressMore.trackedProgressOfTrackedClassification`, so its
underlying presented progress is `A04MoreTags.presentedProgressOfRoutedWalls`
of the selected routed walls, exactly as in the untracked march. -/
def trackedProgress_of_bridge
    (current : TrackedState degree graph label
      (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
      baseStart baseFinish)
    (bridge : WallBridge degree coordinate
      (MatrixAtlas.atlasMatrix current.toMatrixState.label) graph label)
    (hstart : ∀ i, 0 < baseStart i) (hfinish : ∀ i, 0 ≤ baseFinish i)
    (hrestart : 0 ≤ current.toMatrixState.restartTime)
    (hA02Generic : SimpleNegativeCrossings current.toMatrixState.currentStart
      current.toMatrixState.currentFinish) :
    TrackedProgress current :=
  trackedProgressOfTrackedClassification current
    (trackedClassified_of_state current bridge hstart hfinish hrestart) hA02Generic

/-- **The `interior` hypothesis of `OuterWalk.coneEntry_of_reaches`**, produced
from the wall bridge, the march's three metric facts and the genericity
hypothesis, all three quantified over the chain's graphs exactly as the consumer
quantifies them.  `OuterWalkInterior.interior'_of_bridges` is the same term with
the metric triple and the genericity read off a binder that carries them, so it
needs the bridges alone. -/
def interior_of_bridges {G : CubicDartGraph D V}
    (bridge : ∀ (K : CubicDartGraph D V), CubicDartGraph.Reaches G K →
      ∀ (baseStart baseFinish : coordinate → ℚ)
        (current : TrackedState degree K label
          (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
          baseStart baseFinish),
        ¬ current.Terminal →
        WallBridge degree coordinate
          (MatrixAtlas.atlasMatrix current.toMatrixState.label) K label)
    (metric : ∀ (K : CubicDartGraph D V), CubicDartGraph.Reaches G K →
      ∀ (baseStart baseFinish : coordinate → ℚ)
        (current : TrackedState degree K label
          (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
          baseStart baseFinish),
        ¬ current.Terminal →
        (∀ i, 0 < baseStart i) ∧ (∀ i, 0 ≤ baseFinish i) ∧
          0 ≤ current.toMatrixState.restartTime)
    (hA02Generic : ∀ (K : CubicDartGraph D V), CubicDartGraph.Reaches G K →
      ∀ (baseStart baseFinish : coordinate → ℚ)
        (current : TrackedState degree K label
          (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
          baseStart baseFinish),
        SimpleNegativeCrossings current.toMatrixState.currentStart
          current.toMatrixState.currentFinish) :
    ∀ (K : CubicDartGraph D V), CubicDartGraph.Reaches G K →
      ∀ (baseStart baseFinish : coordinate → ℚ)
        (current : TrackedState degree K label
          (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
          baseStart baseFinish),
        ¬ current.Terminal → TrackedProgress current :=
  fun K hK bStart bFinish current hNonterminal ↦
    trackedProgress_of_bridge current (bridge K hK bStart bFinish current hNonterminal)
      (metric K hK bStart bFinish current hNonterminal).1
      (metric K hK bStart bFinish current hNonterminal).2.1
      (metric K hK bStart bFinish current hNonterminal).2.2
      (hA02Generic K hK bStart bFinish current)

/-- **Fit check against the consumer.**  `interior_of_bridges` is literally the
`interior` argument of `OuterWalk.coneEntry_of_reaches`: this theorem is that
application, so the shape is checked by Lean rather than asserted. -/
theorem coneEntry_of_reaches_of_bridges {G H : CubicDartGraph D V}
    (hDegree : 2 ≤ degree) (hReach : CubicDartGraph.Reaches G H)
    (bridge : ∀ (K : CubicDartGraph D V), CubicDartGraph.Reaches G K →
      ∀ (baseStart baseFinish : coordinate → ℚ)
        (current : TrackedState degree K label
          (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
          baseStart baseFinish),
        ¬ current.Terminal →
        WallBridge degree coordinate
          (MatrixAtlas.atlasMatrix current.toMatrixState.label) K label)
    (metric : ∀ (K : CubicDartGraph D V), CubicDartGraph.Reaches G K →
      ∀ (baseStart baseFinish : coordinate → ℚ)
        (current : TrackedState degree K label
          (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
          baseStart baseFinish),
        ¬ current.Terminal →
        (∀ i, 0 < baseStart i) ∧ (∀ i, 0 ≤ baseFinish i) ∧
          0 ≤ current.toMatrixState.restartTime)
    (hA02Generic : ∀ (K : CubicDartGraph D V), CubicDartGraph.Reaches G K →
      ∀ (baseStart baseFinish : coordinate → ℚ)
        (current : TrackedState degree K label
          (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
          baseStart baseFinish),
        SimpleNegativeCrossings current.toMatrixState.currentStart
          current.toMatrixState.currentFinish)
    (link : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : OuterWalk.FacetArrival degree K label (label m.base))
        (wd : OuterWalk.WallData arrival), OuterWalk.TypeChangeLink m wd)
    (entry : OuterWalk.ConeEntry degree G label) : OuterWalk.ConeEntry degree H label :=
  OuterWalk.coneEntry_of_reaches hDegree label hReach
    (interior_of_bridges bridge metric hA02Generic) link entry

end Progress

/-! ## 4.  Six of the ten tags, discharged -/

section TagBridges

open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W4TargetPairings
open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.ClassifiedContinuation (SourceCase)

variable {degree : ℕ} {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {chart : Matrix coordinate coordinate ℚ} {graph : CubicDartGraph D V} {label : D → coordinate}

/-- **Equation (10), the `w2R1` tag, discharged.**  `exists_w2R1_payload`
rebuilds the Equation (10) pair from the `r1` constructor;
`W2R1GraphTracking.exists_matched_tracking` identifies the incoming cover as a
named member with its row equation and hence with a tracking; and
`A04R1Wiring.r1Family_wallColumn` says that member's regrown column is the
crossed coordinate.  The contraction forest is derived from the wall metric. -/
theorem w2Bridge_r1 : W2Bridge degree coordinate chart graph label SourceCase.w2R1 := by
  intro target data fullDim column hChart tracks hAdm star input classification hTag
  obtain ⟨z, hNonneg, hZeroCol, hRows⟩ := hAdm
  have hZero : z (fullDim.labelling.targetEdge.symm (contractedEdge fullDim column)) = 0 := by
    rw [targetEdge_symm_contractedEdge]; exact hZeroCol
  have hForest := SourceFibreForest.contractionForest_of_fullDimensional fullDim z hNonneg hRows
    (hc_column fullDim column) hZero
  obtain ⟨pair⟩ := W2R1ArbitraryIncomingExit.exists_w2R1_payload data (hc_column fullDim column)
    (hab_column fullDim column) (hOne_column fullDim column) star input classification hTag
  obtain ⟨position, fd, hMatrix, hColumn, -, -, ⟨trackFd⟩⟩ :=
    W2R1GraphTracking.exists_matched_tracking data (hc_column fullDim column)
      (hab_column fullDim column) (hOne_column fullDim column) fullDim hForest star pair tracks
  refine ⟨TrackedWallProgress.trackedW2R1 (wall := column) pair input
    (graph_connected_contract target (hab_column fullDim column) (hOne_column fullDim column)
      fullDim.targetConnected)
    ((genus_contract target (hab_column fullDim column) (hOne_column fullDim column)).trans
      fullDim.targetGenus)
    position fd ?_ ⟨leftEnd fullDim column, hab_column fullDim column⟩ chart
    (hMatrix.trans hChart) trackFd⟩
  rw [A04R1Wiring.r1Family_wallColumn pair input position fd, hColumn]
  exact targetEdge_symm_contractedEdge fullDim column

/-- **Equation (9), the `w2P` tag, discharged.**  Same three steps, with
`W2PArbitraryIncomingExit.exists_w2P_payload`,
`W2PGraphTracking.exists_matched_tracking` and
`A04MoreTags.ofW2P_family_wallColumn`. -/
theorem w2Bridge_p : W2Bridge degree coordinate chart graph label SourceCase.w2P := by
  intro target data fullDim column hChart tracks hAdm star input classification hTag
  obtain ⟨z, hNonneg, hZeroCol, hRows⟩ := hAdm
  have hZero : z (fullDim.labelling.targetEdge.symm (contractedEdge fullDim column)) = 0 := by
    rw [targetEdge_symm_contractedEdge]; exact hZeroCol
  have hForest := SourceFibreForest.contractionForest_of_fullDimensional fullDim z hNonneg hRows
    (hc_column fullDim column) hZero
  obtain ⟨wallBlock, sourceProfile, shape, hBackground⟩ :=
    W2PArbitraryIncomingExit.exists_w2P_payload data (hc_column fullDim column)
      (hab_column fullDim column) (hOne_column fullDim column) star input classification hTag
  obtain ⟨position, fd, hMatrix, hColumn, -, -, ⟨trackFd⟩⟩ :=
    W2PGraphTracking.exists_matched_tracking data (hc_column fullDim column)
      (hab_column fullDim column) (hOne_column fullDim column) fullDim hForest star sourceProfile
      shape hBackground tracks
  refine ⟨TrackedWallProgress.trackedW2P (wall := column) input shape
    (graph_connected_contract target (hab_column fullDim column) (hOne_column fullDim column)
      fullDim.targetConnected)
    ((genus_contract target (hab_column fullDim column) (hOne_column fullDim column)).trans
      fullDim.targetGenus)
    position fd ?_ ⟨leftEnd fullDim column, hab_column fullDim column⟩ chart
    (hMatrix.trans hChart) trackFd⟩
  rw [A04MoreTags.ofW2P_family_wallColumn input shape position fd, hColumn]
  exact targetEdge_symm_contractedEdge fullDim column

/-- **Figure 32, the `w2M11` tag, discharged.**  Same three steps, with
`W2M11GraphTracking.exists_w2M11_payload` and `exists_matched_tracking` and
`A04M11Wiring.m11Family_wallColumn`; the dangling compatibility the matched
tracking takes is `WallAdmissibility.danglingCompatible_of_contractionForest`
of the forest derived from the wall metric. -/
theorem w2Bridge_m11 : W2Bridge degree coordinate chart graph label SourceCase.w2M11 := by
  intro target data fullDim column hChart tracks hAdm star input classification hTag
  obtain ⟨z, hNonneg, hZeroCol, hRows⟩ := hAdm
  have hZero : z (fullDim.labelling.targetEdge.symm (contractedEdge fullDim column)) = 0 := by
    rw [targetEdge_symm_contractedEdge]; exact hZeroCol
  have hForest := SourceFibreForest.contractionForest_of_fullDimensional fullDim z hNonneg hRows
    (hc_column fullDim column) hZero
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest data
    (hc_column fullDim column) (hab_column fullDim column) (hOne_column fullDim column) hForest
  obtain ⟨wallBlock, sourceProfile, hBlockCard⟩ :=
    W2M11GraphTracking.exists_w2M11_payload data (hc_column fullDim column)
      (hab_column fullDim column) (hOne_column fullDim column) star input classification hTag
  obtain ⟨position, fd, hMatrix, hColumn, -, -, ⟨trackFd⟩⟩ :=
    W2M11GraphTracking.exists_matched_tracking data (hc_column fullDim column)
      (hab_column fullDim column) (hOne_column fullDim column) fullDim hForest hCompat input
      sourceProfile hBlockCard tracks
  refine ⟨TrackedWallProgress.trackedW2M11 (wall := column) input sourceProfile hBlockCard
    (graph_connected_contract target (hab_column fullDim column) (hOne_column fullDim column)
      fullDim.targetConnected)
    ((genus_contract target (hab_column fullDim column) (hOne_column fullDim column)).trans
      fullDim.targetGenus)
    position fd ?_ ⟨leftEnd fullDim column, hab_column fullDim column⟩ chart
    (hMatrix.trans hChart) trackFd⟩
  rw [A04M11Wiring.m11Family_wallColumn input sourceProfile hBlockCard _ _ position fd, hColumn]
  exact targetEdge_symm_contractedEdge fullDim column

/-- **Equation (1), the `w4` tag.** -/
theorem w4Bridge_w4 : W4Bridge degree coordinate chart graph label := by
  classical
  intro target data fullDim column hChart tracks hAdm star source
  obtain ⟨z, hNonneg, hZeroCol, hRows⟩ := hAdm
  have hZero : z (fullDim.labelling.targetEdge.symm (contractedEdge fullDim column)) = 0 := by
    rw [targetEdge_symm_contractedEdge]; exact hZeroCol
  have hForest := SourceFibreForest.contractionForest_of_fullDimensional fullDim z hNonneg hRows
    (hc_column fullDim column) hZero
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest data
    (hc_column fullDim column) (hab_column fullDim column) (hOne_column fullDim column) hForest
  obtain ⟨matched, ⟨trackFd⟩, hMatrix, -, hColumn⟩ :=
    InteriorGraphTracking.exists_matched_tracking data fullDim tracks (hc_column fullDim column)
      (hab_column fullDim column) (hOne_column fullDim column) star hForest hCompat source
  have hwallColumn : W4PositiveExit.wallColumn source _ matched = column :=
    (W4PositiveExit.wallColumn_eq source _ matched).trans
      (hColumn.trans (targetEdge_symm_contractedEdge fullDim column))
  refine ⟨TrackedWallProgress.trackedW4 (wall := column) source
    (graph_connected_contract target (hab_column fullDim column) (hOne_column fullDim column)
      fullDim.targetConnected)
    ((genus_contract target (hab_column fullDim column) (hOne_column fullDim column)).trans
      fullDim.targetGenus)
    _ matched hwallColumn ⟨leftEnd fullDim column, hab_column fullDim column⟩ chart _
    (W4PositiveExit.incomingDet_ne_zero source _ matched) ?_ trackFd⟩
  exact (W4PositiveExit.memberMatrix_self source _ matched).trans (hMatrix.trans hChart)

/-- **Figure 31's regrown column**, read on the identified member's own
occurrence dictionary.  The analogue of the `w4`/`w2P`/`w2R1`/`w2M11` identities
(`W4PositiveExit.wallColumn_eq`, `A04MoreTags.ofW2P_family_wallColumn`,
`A04R1Wiring.r1Family_wallColumn`, `A04M11Wiring.m11Family_wallColumn`), by the
same `Equiv` cancellation. -/
theorem nd2WallColumn_eq {target : CFGraph.{0}} {wallVertex : target.V}
    {data : GluingDatum target degree} {star : ThirdEquation.ThreeStar target wallVertex}
    (input : ThirdEquation.W3SourceInput data star)
    (profile : W3R1SourceProfile.Nd2Profile data
      (ThirdEquation.W3SourceInput.distinguishedBlock input))
    (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd2CommonBalance.candidates input profile incoming).datum coordinate) :
    W3Nd2CommonBalance.wallColumn input profile
        (W3Nd2PositiveExit.initialLabelling input profile incoming incomingFD) =
      incomingFD.labelling.targetEdge.symm
        (W3Nd2CommonBalance.columnEquiv input profile incoming none) := by
  show ((incomingFD.labelling.targetEdge.trans
      ((W3Nd2CommonBalance.columnEquiv input profile incoming).symm.trans
        (W3Nd2CommonBalance.columnEquiv input profile 0))).trans
      (W3Nd2CommonBalance.columnEquiv input profile 0).symm).symm none = _
  refine (Equiv.symm_apply_eq _).mpr ?_
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- **Figure 31's wall input presents its members by their own honest square
matrices.**  The `w4` analogue is `W4PositiveExit.memberMatrix_self` composed
with `A04FourTags.ofFourValentHonest`'s definitional unfolding;
`W3WallInput.nd2Presentation` is defined by cases on the member, so the
identity needs `fin_cases` rather than `rfl`. -/
theorem ofNd2CoarseFine_family_matrix {wall : coordinate} {target : CFGraph.{0}}
    {wallVertex : target.V} {data : GluingDatum target degree}
    {star : ThirdEquation.ThreeStar target wallVertex}
    (input : ThirdEquation.W3SourceInput data star)
    (profile : W3R1SourceProfile.Nd2Profile data
      (ThirdEquation.W3SourceInput.distinguishedBlock input))
    (initial : StableLengthMatrixLabelling
      (W3Nd2CommonBalance.candidates input profile 0).datum coordinate)
    (hwallColumn : W3Nd2CommonBalance.wallColumn input profile initial = wall)
    (hConnected : graph_connected target) (hGenus : genus target = 0) (root : target.V)
    (position : Fin 2) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((W3WallInput.ofNd2CoarseFine (wall := wall) input profile initial hwallColumn
          hConnected hGenus root).family.presentation position) =
      W3Nd2CommonBalance.squareMatrix input profile initial position := by
  fin_cases position <;> rfl

/-- **Figure 31, the `w3Nd2CoarseFine` tag.** -/
theorem w3Bridge_nd2 : W3Bridge degree coordinate chart graph label
    SourceCase.w3Nd2CoarseFine := by
  intro target data fullDim column hChart tracks hAdm star input classification hTag
  obtain ⟨z, hNonneg, hZeroCol, hRows⟩ := hAdm
  have hZero : z (fullDim.labelling.targetEdge.symm (contractedEdge fullDim column)) = 0 := by
    rw [targetEdge_symm_contractedEdge]; exact hZeroCol
  have hForest := SourceFibreForest.contractionForest_of_fullDimensional fullDim z hNonneg hRows
    (hc_column fullDim column) hZero
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest data
    (hc_column fullDim column) (hab_column fullDim column) (hOne_column fullDim column) hForest
  have hConn : graph_connected (contract target (hab_column fullDim column)
      (hOne_column fullDim column)) :=
    graph_connected_contract target (hab_column fullDim column) (hOne_column fullDim column)
      fullDim.targetConnected
  have hGen : genus (contract target (hab_column fullDim column)
      (hOne_column fullDim column)) = 0 :=
    (genus_contract target (hab_column fullDim column) (hOne_column fullDim column)).trans
      fullDim.targetGenus
  cases classification with
  | four => cases hTag
  | shift => cases hTag
  | nd3CoarseFine => cases hTag
  | nd2CoarseFine profile =>
    obtain ⟨position, fd, hMatrix, hColumn, -, -, ⟨trackFd⟩⟩ :=
      W3Nd2GraphTracking.exists_matched_tracking data (hc_column fullDim column)
        (hab_column fullDim column) (hOne_column fullDim column) fullDim hForest hCompat star
        input profile tracks
    have hwallColumn : W3Nd2CommonBalance.wallColumn input profile
        (W3Nd2PositiveExit.initialLabelling input profile position fd) = column :=
      (nd2WallColumn_eq input profile position fd).trans
        (hColumn.trans (targetEdge_symm_contractedEdge fullDim column))
    have hSelfMatrix : W3Nd2CommonBalance.squareMatrix input profile
        (W3Nd2PositiveExit.initialLabelling input profile position fd) position =
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation := by
      change GluingDatum.LengthMatrixPresentation.matrix
        (W3Nd2PositiveExit.outgoingLabelling input profile position fd position).presentation = _
      exact congrArg
        (fun l : StableLengthMatrixLabelling
            (W3Nd2CommonBalance.candidates input profile position).datum coordinate ↦
          GluingDatum.LengthMatrixPresentation.matrix l.presentation)
        (W3Nd2PositiveExit.outgoingLabelling_self input profile position fd)
    have hFamMatrix := ofNd2CoarseFine_family_matrix (wall := column) input profile
      (W3Nd2PositiveExit.initialLabelling input profile position fd) hwallColumn hConn hGen
      ⟨leftEnd fullDim column, hab_column fullDim column⟩ position
    exact ⟨TrackedWallProgress.trackedNd2 (wall := column) input profile hConn hGen
      position fd hwallColumn ⟨leftEnd fullDim column, hab_column fullDim column⟩ chart position
      (by rw [hFamMatrix]; exact W3Nd2PositiveExit.incomingDet_ne_zero input profile position fd)
      (hFamMatrix.trans (hSelfMatrix.trans (hMatrix.trans hChart))) trackFd⟩

/-- **Figure 30's regrown column**, read on the identified member's own
occurrence dictionary.  Same `Equiv` cancellation as `nd2WallColumn_eq`. -/
theorem nd3WallColumn_eq {target : CFGraph.{0}} {wallVertex : target.V}
    {data : GluingDatum target degree} {star : ThirdEquation.ThreeStar target wallVertex}
    (input : ThirdEquation.W3SourceInput data star)
    (profile : W3R1SourceProfile.Nd3Profile data
      (ThirdEquation.W3SourceInput.distinguishedBlock input))
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd3CommonBalance.candidates input profile hSame incoming).datum coordinate) :
    W3Nd3CommonBalance.wallColumn input profile hSame
        (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming incomingFD) =
      incomingFD.labelling.targetEdge.symm
        (W3Nd3CommonBalance.columnEquiv input profile hSame incoming none) := by
  show ((incomingFD.labelling.targetEdge.trans
      ((W3Nd3CommonBalance.columnEquiv input profile hSame incoming).symm.trans
        (W3Nd3CommonBalance.columnEquiv input profile hSame 0))).trans
      (W3Nd3CommonBalance.columnEquiv input profile hSame 0).symm).symm none = _
  refine (Equiv.symm_apply_eq _).mpr ?_
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- **Figure 30's wall input presents its members by their own honest square
matrices.**  `nd2`'s analogue, `fin_cases` for the same reason. -/
theorem ofNd3CoarseFine_family_matrix {wall : coordinate} {target : CFGraph.{0}}
    {wallVertex : target.V} {data : GluingDatum target degree}
    {star : ThirdEquation.ThreeStar target wallVertex}
    (input : ThirdEquation.W3SourceInput data star)
    (profile : W3R1SourceProfile.Nd3Profile data
      (ThirdEquation.W3SourceInput.distinguishedBlock input))
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (initial : StableLengthMatrixLabelling
      (W3Nd3CommonBalance.candidates input profile hSame 0).datum coordinate)
    (hwallColumn : W3Nd3CommonBalance.wallColumn input profile hSame initial = wall)
    (hConnected : graph_connected target) (hGenus : genus target = 0) (root : target.V)
    (position : Fin 2) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((W3WallInput.ofNd3CoarseFine (wall := wall) input profile hSame initial hwallColumn
          hConnected hGenus root).family.presentation position) =
      W3Nd3CommonBalance.squareMatrix input profile hSame initial position := by
  fin_cases position <;> rfl

/-- **Figure 30, the `w3Nd3CoarseFine` tag.** -/
theorem w3Bridge_nd3 : W3Bridge degree coordinate chart graph label
    SourceCase.w3Nd3CoarseFine := by
  intro target data fullDim column hChart tracks hAdm star input classification hTag
  obtain ⟨z, hNonneg, hZeroCol, hRows⟩ := hAdm
  have hZero : z (fullDim.labelling.targetEdge.symm (contractedEdge fullDim column)) = 0 := by
    rw [targetEdge_symm_contractedEdge]; exact hZeroCol
  have hForest := SourceFibreForest.contractionForest_of_fullDimensional fullDim z hNonneg hRows
    (hc_column fullDim column) hZero
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest data
    (hc_column fullDim column) (hab_column fullDim column) (hOne_column fullDim column) hForest
  have hConn : graph_connected (contract target (hab_column fullDim column)
      (hOne_column fullDim column)) :=
    graph_connected_contract target (hab_column fullDim column) (hOne_column fullDim column)
      fullDim.targetConnected
  have hGen : genus (contract target (hab_column fullDim column)
      (hOne_column fullDim column)) = 0 :=
    (genus_contract target (hab_column fullDim column) (hOne_column fullDim column)).trans
      fullDim.targetGenus
  cases classification with
  | four => cases hTag
  | shift => cases hTag
  | nd2CoarseFine => cases hTag
  | nd3CoarseFine profile hSame pair_index largest_index =>
    obtain ⟨position, fd, hMatrix, hColumn, -, -, ⟨trackFd⟩⟩ :=
      W3Nd3GraphTracking.exists_matched_tracking data (hc_column fullDim column)
        (hab_column fullDim column) (hOne_column fullDim column) fullDim hForest hCompat star
        input profile hSame tracks
    have hwallColumn : W3Nd3CommonBalance.wallColumn input profile hSame
        (W3Nd3ArbitraryExit.initialLabelling input profile hSame position fd) = column :=
      (nd3WallColumn_eq input profile hSame position fd).trans
        (hColumn.trans (targetEdge_symm_contractedEdge fullDim column))
    have hSelfMatrix : W3Nd3CommonBalance.squareMatrix input profile hSame
        (W3Nd3ArbitraryExit.initialLabelling input profile hSame position fd) position =
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation := by
      change GluingDatum.LengthMatrixPresentation.matrix
        (W3Nd3ArbitraryExit.outgoingLabelling input profile hSame position fd
          position).presentation = _
      exact congrArg
        (fun l : StableLengthMatrixLabelling
            (W3Nd3CommonBalance.candidates input profile hSame position).datum coordinate ↦
          GluingDatum.LengthMatrixPresentation.matrix l.presentation)
        (W3Nd3ArbitraryExit.outgoingLabelling_self input profile hSame position fd)
    have hFamMatrix := ofNd3CoarseFine_family_matrix (wall := column) input profile hSame
      (W3Nd3ArbitraryExit.initialLabelling input profile hSame position fd) hwallColumn
      hConn hGen ⟨leftEnd fullDim column, hab_column fullDim column⟩ position
    exact ⟨TrackedWallProgress.trackedNd3 (wall := column) input profile hSame hConn hGen
      position fd hwallColumn ⟨leftEnd fullDim column, hab_column fullDim column⟩ chart position
      (by
        rw [hFamMatrix]
        exact W3Nd3ArbitraryExit.incomingDet_ne_zero input profile hSame position fd)
      (hFamMatrix.trans (hSelfMatrix.trans (hMatrix.trans hChart))) trackFd⟩

/-- **Routed walls at one chart, from the other four tags.**  The six bridges
proved here are supplied; what is left is exactly `w3Four`, `w3Shift`, `w2M1k`
and `w2Mkk`.  Composed with `trackedClassified_of_state` and
`interior_of_bridges` this is the whole of `interior` on those four plus the
march's three metric facts and the genericity hypothesis.  The four bridges are
proved in `InteriorBridgesTrivalent` and `InteriorBridgesDivalent`, and the
metric facts and genericity are derived in `OuterWalkInterior`. -/
theorem wallBridge_of_remaining
    (b3Four : W3Bridge degree coordinate chart graph label SourceCase.w3Four)
    (b3Shift : W3Bridge degree coordinate chart graph label SourceCase.w3Shift)
    (b2M1k : W2Bridge degree coordinate chart graph label SourceCase.w2M1k)
    (b2Mkk : W2Bridge degree coordinate chart graph label SourceCase.w2Mkk) :
    WallBridge degree coordinate chart graph label :=
  wallBridge_of_tagBridges degree coordinate chart graph label w4Bridge_w4 b3Four b3Shift
    w3Bridge_nd3 w3Bridge_nd2 w2Bridge_m11 b2M1k b2Mkk w2Bridge_p w2Bridge_r1

end TagBridges

end

end DraismaVargas.LocalCases.InteriorProgress
