import DraismaVargas.LocalCases.InteriorBridgesAll
import DraismaVargas.LocalCases.ReachableMarch

/-!
# The outer walk's `interior` hypothesis, restated at the march's own metric

Source: Vargas, Part II (arXiv:2609.09109), Section 4 (the wall-crossing
proposition, and the proof of the main theorem, which walks a generic path from
a caterpillar of loops across codimension-one walls), read against
`DraismaVargas/LocalCases/OuterWalk.lean` §2 and §5 and the first-wall
restriction of `SemanticAtlasMarch.State.PresentedProgress`.

`OuterWalk.coneEntry_of_reaches` takes its `interior` hypothesis with the
segment data **bare**:

```
interior : ∀ K, Reaches G K → ∀ baseStart baseFinish
  (current : TrackedState degree K label (MatrixAtlas.atlasMatrix …) baseStart baseFinish),
  ¬ current.Terminal → TrackedProgress current
```

so a producer of `TrackedProgress` has to work at an *arbitrary* state of an
*arbitrary* segment.  But the interior wall metric that the first-wall-restricted
presented progress needs -- `NonTrivalentWallSetup.rows_ne_zero_of_lt_one`, hence
`InteriorProgress.admissibleColumn_of_firstWall` -- rests on three facts
(`0 < baseStart`, `0 ≤ baseFinish`, `0 ≤ current.restartTime`) that the walk
establishes at every state it actually visits and that an arbitrary state of an
arbitrary segment need not satisfy.  This module restates the hypothesis with
those facts in the binder, and runs the walk on the restated form.

## What is proved here

* `Interior'`: the same hypothesis with **four** facts in the binder -- those
  three metric ones and the genericity of the cone's base pair,
  `AtlasGenericStart.AtlasGeneric degree baseStart baseFinish`.
* `restartTime_nonneg_of_reachable` and
  `exists_terminal_of_reachable_tracked_progress`: the tracked march needs
  progress only on the states reachable from its own seed
  (`FiniteStrictMarch.exists_terminal_reachable_of_reachable_progress`, from
  `ReachableMarch`), which is what makes `0 ≤ restartTime` available at the
  point of use rather than assumable everywhere.
* `exists_facetArrival'` and `coneEntry_of_reaches'`: `OuterWalk`'s
  `exists_facetArrival` and `coneEntry_of_reaches` with `Interior'` in place of
  `interior`.  The four facts are discharged exactly where `FacetArrival` and
  `OuterWalk.ConeEntry` already record them: `entry`'s own `hstart` and its
  second conjunct `AtlasGenericStart.AtlasGeneric`, both at the very
  `baseStart`/`baseFinish` pair this cone march runs on; the facet-generic
  finish (`FacetGenericity.exists_facetGeneric`, zero at the facet and positive
  elsewhere); and `FiniteAtlasMarch.State.restartTime_nonneg_of_reachable` at the
  time-zero seed.  Nothing about the walk changes; the induction of
  `coneEntry_of_reaches` is repeated verbatim with the restated arrival.
* `interior'_of_bridges`: `Interior'` **from the per-tag wall bridges alone** --
  neither the metric triple nor the genericity is a hypothesis, because the
  binder carries both.  The base pair is fixed inside a cone, so the entry's
  genericity is genericity at *every* state of that cone:
  `AtlasGenericStart.AtlasGeneric.simpleNegativeCrossings`, read through
  `TrackedState.toSemanticState`, supplies `SimpleNegativeCrossings` at the state
  in hand.
* `coneEntry_of_reaches_of_bridges'`: the application to `coneEntry_of_reaches'`,
  so the fit is checked by Lean.
* `interior'_unconditional` and `coneEntry_of_reaches_unconditional`: the same
  with the bridges themselves discharged by `InteriorBridgesAll.wallBridge`,
  which has no hypothesis at all.  `interior'_unconditional :
  Interior' degree graph label` therefore carries **no hypothesis whatsoever**:
  it is both the non-vacuity witness of `Interior'` and the discharge of the
  interior side of the outer walk.  `interior'_of_a02` and
  `coneEntry_of_reaches_of_a02` are the same two results under other names; the
  genericity of the base pair that the `a02` in those names refers to is not
  among their hypotheses.
* `exists_terminal_of_chain'`: `OuterWalk.exists_terminal_of_chain` on
  `Interior'`.  The walk uses its interior hypothesis a second time, in the last
  cone at the requested finish; that use goes through
  `exists_terminal_of_reachable_tracked_progress` here, so `0 ≤ restartTime`
  comes from the time-zero entry state, `0 ≤ baseFinish` is the hypothesis
  `hRequested` (free when the requested lengths are those of a `Spec`, which
  are natural numbers), and the genericity is again the cone entry's own second
  conjunct.
* `exists_terminal_of_chain''`: the same theorem with the interior binder
  **discharged**, by `interior'_unconditional`.  Its binders are `m`, `core`,
  `hCubic`, `hCoreConnected`, `hGenus`, `link`, `requestedLength` and
  `hRequested` only.

## Hypotheses left explicit here

* `OuterWalk.TypeChangeLink` at every wall data of every chain graph, the
  `link` argument of `coneEntry_of_reaches`, unchanged.
* `2 ≤ degree` and the cone invariant `OuterWalk.ConeEntry` at the chain's
  source, unchanged; at the caterpillar seed the invariant is proved
  (`OuterWalk.coneEntry_caterpillar`) and that is the only one the chain
  theorems use.

The chain theorems return the terminal tracked state together with its tracked
pencil and cleared face; identifying that terminal state
(`TerminalIdentification`) is left to the consumer.

The genericity `SimpleNegativeCrossings` is **not** a hypothesis of this file.
It is not an extra assumption of the walk: every cone is entered through
`OuterWalk.ConeEntry`, whose second conjunct is
`AtlasGenericStart.AtlasGeneric degree baseStart baseFinish` at the base pair
that cone march runs on, and `AtlasGeneric.simpleNegativeCrossings` converts it
at every state over that pair.  Putting the conjunct in the `Interior'` binder
is what makes it reachable from the producer.
`InteriorProgress.interior_of_bridges` takes the genericity (and the metric
triple) as hypotheses; it is the bare-binder form.

Consumers: `StatementFromLink.nonempty_evenSubdivisionPencil_of_link`, through
`exists_terminal_of_chain''`.  `OuterWalk.coneEntry_of_reaches` and
`OuterWalk.exists_terminal_of_chain` remain available for a caller that has the
bare `interior` (`interior'_of_interior` is the one-way forgetful map).
-/

namespace DraismaVargas.LocalCases.OuterWalkInterior

noncomputable section

open Utilities
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.RationalAffineWall
open DraismaVargas.LocalCases.InteriorProgress
open DraismaVargas.LocalCases.SemanticAtlasMarch

/-! ## 1.  The tracked march on its own reachable component -/

section Reachable

variable {coordinate chart D V : Type*}
  [Fintype coordinate] [DecidableEq coordinate]
  [Fintype chart] [DecidableEq chart]
  [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}

omit [Fintype chart] [DecidableEq chart] in
/-- Reachability of tracked states projects to reachability of matrix states.
This is `OuterWalk.reflTransGen_toMatrixState`, at an arbitrary chart rather
than at the universal atlas. -/
theorem reflTransGen_toMatrixState
    {s t : TrackedState degree graph label matrix baseStart baseFinish}
    (h : Relation.ReflTransGen TrackedState.Step s t) :
    Relation.ReflTransGen FiniteAtlasMarch.State.Step s.toMatrixState t.toMatrixState := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih ((TrackedState.step_iff _ _).mp hbc)

omit [Fintype chart] [DecidableEq chart] in
/-- **The clock at a reached tracked state.**  A tracked chain projects to a
matrix chain, and a matrix chain out of a time-zero seed never acquires a
negative restart (`FiniteAtlasMarch.State.restartTime_nonneg_of_reachable`). -/
theorem restartTime_nonneg_of_reachable
    {initial current : TrackedState degree graph label matrix baseStart baseFinish}
    (hzero : initial.toMatrixState.restartTime = 0)
    (hreach : Relation.ReflTransGen TrackedState.Step initial current) :
    0 ≤ current.toMatrixState.restartTime :=
  FiniteAtlasMarch.State.restartTime_nonneg_of_reachable hzero
    (reflTransGen_toMatrixState hreach)

omit [DecidableEq chart] in
/-- **Tracked termination from progress on the reachable component only.**  This
is `TrackedState.exists_terminal_reachable_of_tracked_progress` with
`FiniteStrictMarch.exists_terminal_reachable_of_reachable_progress` in place of
`exists_terminal_reachable`, so the progress producer may use the seed's own
reachability facts -- which is exactly what `0 ≤ restartTime` is. -/
theorem exists_terminal_of_reachable_tracked_progress (hDegree : 2 ≤ degree)
    (hdet : ∀ l, (matrix l).det ≠ 0)
    (initial : TrackedState degree graph label matrix baseStart baseFinish)
    (localProgress : ∀ current : TrackedState degree graph label matrix baseStart baseFinish,
      Relation.ReflTransGen TrackedState.Step initial current →
      ¬ TrackedState.Terminal current → TrackedProgress current) :
    ∃ final, Relation.ReflTransGen TrackedState.Step initial final ∧
      TrackedState.Terminal final := by
  apply (TrackedState.march degree graph label matrix hdet baseStart
    baseFinish).exists_terminal_reachable_of_reachable_progress
    TrackedState.Terminal initial
  intro current hreach
  by_cases hterminal : TrackedState.Terminal current
  · exact Or.inl hterminal
  · exact Or.inr ((localProgress current hreach hterminal).exists_step hDegree hdet hterminal)

end Reachable

/-! ## 2.  The restated `interior` binder and the walk on it -/

section Walk

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ}

/-- **The `interior` hypothesis of the outer walk, at the march's own metric.**
Identical to `OuterWalk.coneEntry_of_reaches`'s `interior` except that the four
facts a producer needs travel in the binder: the three the interior wall metric
rests on, and the genericity of the base pair.  Every state the walk
actually visits satisfies all four (`exists_facetArrival'`), because each is
recorded by `OuterWalk.ConeEntry` or by `FacetArrival` at the very base pair the
cone march runs on. -/
abbrev Interior' (degree : ℕ) (graph : CubicDartGraph D V) (label : D → coordinate) :=
  ∀ (baseStart baseFinish : coordinate → ℚ)
    (current : TrackedState degree graph label
      (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
      baseStart baseFinish),
    (∀ i, 0 < baseStart i) → (∀ i, 0 ≤ baseFinish i) →
    0 ≤ current.toMatrixState.restartTime →
    AtlasGenericStart.AtlasGeneric degree baseStart baseFinish →
    ¬ current.Terminal → TrackedProgress current

/-- The bare `interior` of `OuterWalk` is stronger: forgetting the four facts
lands in `Interior'`. -/
def interior'_of_interior {graph : CubicDartGraph D V} {label : D → coordinate}
    (interior : ∀ (baseStart baseFinish : coordinate → ℚ)
      (current : TrackedState degree graph label
        (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
        baseStart baseFinish),
      ¬ current.Terminal → TrackedProgress current) :
    Interior' degree graph label :=
  fun bStart bFinish current _ _ _ _ hNonterminal ↦
    interior bStart bFinish current hNonterminal

/-- **One cone march, on the restated binder.**  `OuterWalk.exists_facetArrival`
with `Interior'` in place of `interior`: the cone entry supplies `0 < baseStart`
and the genericity of the pair, the facet-generic finish is zero at the facet and
positive elsewhere hence nonnegative, and the reachable-component march supplies
`0 ≤ restartTime` at every state the progress is asked at. -/
theorem exists_facetArrival' (hDegree : 2 ≤ degree)
    {graph : CubicDartGraph D V} {label : D → coordinate}
    (entry : OuterWalk.ConeEntry degree graph label)
    (interior : Interior' degree graph label)
    (facet : coordinate) :
    Nonempty (OuterWalk.FacetArrival degree graph label facet) := by
  obtain ⟨baseFinish, hfacet, hother, hgeneric⟩ :=
    FacetGenericity.exists_facetGeneric degree facet
  obtain ⟨baseStart, hstart, hAtlasGeneric, initial, hzero⟩ := entry baseFinish
  have hfinish : ∀ i, 0 ≤ baseFinish i := by
    intro i
    by_cases hi : i = facet
    · subst hi; exact le_of_eq hfacet.symm
    · exact (hother i hi).le
  obtain ⟨final, hreach, hterminal⟩ :=
    exists_terminal_of_reachable_tracked_progress hDegree
      (fun l ↦ MatrixAtlas.atlasMatrix_det_ne_zero l) initial
      (fun current hcurrent hNonterminal ↦
        interior baseStart baseFinish current hstart hfinish
          (restartTime_nonneg_of_reachable hzero hcurrent) hAtlasGeneric hNonterminal)
  exact ⟨⟨baseStart, baseFinish, hstart, hfacet, hother, hgeneric, final, hterminal,
    FiniteAtlasMarch.State.restartTime_nonneg_of_reachable hzero
      (reflTransGen_toMatrixState hreach)⟩⟩

/-- **The outer walk on the restated binder.**  `OuterWalk.coneEntry_of_reaches`
verbatim -- the same induction on the Whitehead chain, the same wall data and the
same type-change link -- with `exists_facetArrival'` supplying each cone march.
`OuterWalk.coneEntry_of_reaches` is not weakened and not re-proved: its
`interior` argument cannot be built from `Interior'`, so the four-line induction
is repeated. -/
theorem coneEntry_of_reaches' (hDegree : 2 ≤ degree) (label : D → coordinate)
    {G H : CubicDartGraph D V} (hReach : CubicDartGraph.Reaches G H)
    (interior : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      Interior' degree K label)
    (link : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : OuterWalk.FacetArrival degree K label (label m.base))
        (wd : OuterWalk.WallData arrival), OuterWalk.TypeChangeLink m wd)
    (entry : OuterWalk.ConeEntry degree G label) : OuterWalk.ConeEntry degree H label := by
  induction hReach with
  | refl => exact entry
  | tail hGK hKH ih =>
    obtain ⟨m, rfl⟩ := hKH
    obtain ⟨arrival⟩ := exists_facetArrival' hDegree ih (interior _ hGK) (label m.base)
    obtain ⟨wd⟩ := arrival.nonempty_wallData
    exact (link _ hGK m arrival wd).coneEntry hDegree

end Walk

/-! ## 3.  `Interior'` from the wall bridges -/

section Bridges

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {label : D → coordinate}

/-- **The restated `interior` from the per-tag bridges alone.**  The three
metric facts and the genericity that `InteriorProgress.interior_of_bridges`
takes as hypotheses are read off the binder here, so neither the wall
metric nor genericity is assumed: `InteriorProgress.admissibleColumn_of_firstWall`
derives admissibility at the coordinate `SemanticAtlasMarch.IsFirstWall` names,
which is the only coordinate the first-wall-restricted `PresentedProgress` asks
about, and `AtlasGenericStart.AtlasGeneric.simpleNegativeCrossings` -- read on
`TrackedState.toSemanticState`, since `WallProgress.atlasChartMatrix coordinate
degree` is `MatrixAtlas.atlasMatrix` -- turns the binder's genericity at the base
pair into `SimpleNegativeCrossings` at this state. -/
def interior'_of_bridges {G : CubicDartGraph D V}
    (bridge : ∀ (K : CubicDartGraph D V), CubicDartGraph.Reaches G K →
      ∀ (baseStart baseFinish : coordinate → ℚ)
        (current : TrackedState degree K label
          (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
          baseStart baseFinish),
        ¬ current.Terminal →
        WallBridge degree coordinate
          (MatrixAtlas.atlasMatrix current.toMatrixState.label) K label) :
    ∀ (K : CubicDartGraph D V), CubicDartGraph.Reaches G K → Interior' degree K label :=
  fun K hK bStart bFinish current hstart hfinish hrestart hgeneric hNonterminal ↦
    trackedProgress_of_bridge current (bridge K hK bStart bFinish current hNonterminal)
      hstart hfinish hrestart (hgeneric.simpleNegativeCrossings current.toSemanticState)

/-- **Fit check against the consumer.**  `interior'_of_bridges` is literally the
`interior` argument of `coneEntry_of_reaches'`: this theorem is that
application, so the shape is checked by Lean rather than asserted. -/
theorem coneEntry_of_reaches_of_bridges' {G H : CubicDartGraph D V}
    (hDegree : 2 ≤ degree) (hReach : CubicDartGraph.Reaches G H)
    (bridge : ∀ (K : CubicDartGraph D V), CubicDartGraph.Reaches G K →
      ∀ (baseStart baseFinish : coordinate → ℚ)
        (current : TrackedState degree K label
          (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
          baseStart baseFinish),
        ¬ current.Terminal →
        WallBridge degree coordinate
          (MatrixAtlas.atlasMatrix current.toMatrixState.label) K label)
    (link : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : OuterWalk.FacetArrival degree K label (label m.base))
        (wd : OuterWalk.WallData arrival), OuterWalk.TypeChangeLink m wd)
    (entry : OuterWalk.ConeEntry degree G label) : OuterWalk.ConeEntry degree H label :=
  coneEntry_of_reaches' hDegree label hReach (interior'_of_bridges bridge) link entry

/-- **Non-vacuity, and the interior side discharged: `Interior'` with no
hypothesis at all.**  All ten per-tag bridges are discharged
(`InteriorBridgesAll.wallBridge`, no hypothesis), and the genericity the
dispatcher needs is read off the binder, where the cone entry put it.  So the
restated `interior` of every cone of the chain is a theorem: the genericity
that `InteriorProgress.interior_of_bridges` and
`TrackedWallProgress.exists_terminal_tracked_caterpillar_of_routedWalls`
take as a hypothesis is not an assumption of the walk. -/
def interior'_unconditional {graph : CubicDartGraph D V} : Interior' degree graph label :=
  fun _ _ current hstart hfinish hrestart hgeneric _ ↦
    trackedProgress_of_bridge current InteriorBridgesAll.wallBridge hstart hfinish hrestart
      (hgeneric.simpleNegativeCrossings current.toSemanticState)

/-- **The outer walk on the type-change link and the cone invariant alone.**
The interior side of `OuterWalk.coneEntry_of_reaches` is discharged: what remains
is the type-change link `TypeChangeLink` and the invariant at the chain's
source. -/
theorem coneEntry_of_reaches_unconditional {G H : CubicDartGraph D V}
    (hDegree : 2 ≤ degree) (hReach : CubicDartGraph.Reaches G H)
    (link : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : OuterWalk.FacetArrival degree K label (label m.base))
        (wd : OuterWalk.WallData arrival), OuterWalk.TypeChangeLink m wd)
    (entry : OuterWalk.ConeEntry degree G label) : OuterWalk.ConeEntry degree H label :=
  coneEntry_of_reaches' hDegree label hReach (fun _ _ ↦ interior'_unconditional) link entry

/-- Another name for `interior'_unconditional`, in the shape
`coneEntry_of_reaches'` quantifies over.  The genericity of the base pair that
the `a02` in the name refers to is **not** a hypothesis of it. -/
def interior'_of_a02 {G : CubicDartGraph D V} :
    ∀ (K : CubicDartGraph D V), CubicDartGraph.Reaches G K → Interior' degree K label :=
  fun _ _ ↦ interior'_unconditional

/-- Another name for `coneEntry_of_reaches_unconditional`.  The genericity of
the base pair that the `a02` in the name refers to is **not** a hypothesis of
it. -/
theorem coneEntry_of_reaches_of_a02 {G H : CubicDartGraph D V}
    (hDegree : 2 ≤ degree) (hReach : CubicDartGraph.Reaches G H)
    (link : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : OuterWalk.FacetArrival degree K label (label m.base))
        (wd : OuterWalk.WallData arrival), OuterWalk.TypeChangeLink m wd)
    (entry : OuterWalk.ConeEntry degree G label) : OuterWalk.ConeEntry degree H label :=
  coneEntry_of_reaches_unconditional hDegree hReach link entry

end Bridges

/-! ## 4.  The walk, end to end, on the restated binder -/

section Chain

open Utilities.Certificate
open Utilities.Certificate.ExplicitPotential
open Utilities.Certificate.SubdivisionGraph
open Utilities.Gonality
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StableSourceDarts
open DraismaVargas.LocalCases.OuterWalk

/-- **The walk, on the restated binder.**  `OuterWalk.exists_terminal_of_chain`
with `Interior'` in place of `interior`.  The walk uses its interior hypothesis
twice, and both uses discharge all four binder facts:

* along the chain, through `coneEntry_of_reaches'`;
* in the last cone, at the requested finish, where the generic start of the cone
  invariant is positive and `AtlasGeneric` against that finish, the requested
  lengths are assumed nonnegative and the reachable-component march
  (`exists_terminal_of_reachable_tracked_progress`) supplies `0 ≤ restartTime`
  from the time-zero entry state.

`hRequested` is the one additional hypothesis, and it is free at the consumer,
which reads the requested lengths off a `Spec`, where they are natural numbers.
Everything `OuterWalk.exists_terminal_of_chain` returns is returned here, so this
is a drop-in replacement for it. -/
theorem exists_terminal_of_chain' (m : ℕ) {n p : ℕ} (core : Core n p)
    (hCubic : core.Cubic) (hCoreConnected : core.Connected)
    (hGenus : p + 1 - n = 2 * m + 2)
    (interior : ∀ K : CubicDartGraph (Dart (CaterpillarSeed.seed m).candidate.datum)
        (BranchVertex (CaterpillarSeed.seed m).candidate.datum),
      CubicDartGraph.Reaches (seedGraph m) K → Interior' (m + 2) K (seedLabel m))
    (link : ∀ K : CubicDartGraph (Dart (CaterpillarSeed.seed m).candidate.datum)
        (BranchVertex (CaterpillarSeed.seed m).candidate.datum),
      CubicDartGraph.Reaches (seedGraph m) K →
      ∀ (mv : K.MoveData)
        (arrival : OuterWalk.FacetArrival (m + 2) K (seedLabel m) (seedLabel m mv.base))
        (wd : OuterWalk.WallData arrival), OuterWalk.TypeChangeLink mv wd)
    (requestedLength : Fin p → ℚ) (hRequested : ∀ e, 0 ≤ requestedLength e) :
    ∃ (last : CubicDartGraph (Dart (CaterpillarSeed.seed m).candidate.datum)
        (BranchVertex (CaterpillarSeed.seed m).candidate.datum))
      (endpoint : last.Iso (CubicCoreDarts.ofCore core hCubic hCoreConnected))
      (slots : Fin (6 * m + 3) ≃ Fin p),
      CubicDartGraph.Reaches (seedGraph m) last ∧
      (∀ d, slots (seedLabel m d) = (endpoint.dart d).1) ∧
      ∃ baseStart : Fin (6 * m + 3) → ℚ,
        (∀ i, 0 < baseStart i) ∧
        AtlasGenericStart.AtlasGeneric (m + 2) baseStart
          (fun row ↦ requestedLength (slots row)) ∧
        ∃ initial final : TrackedState (m + 2) last (seedLabel m)
            (MatrixAtlas.atlasMatrix (coordinate := Fin (6 * m + 3)) (degree := m + 2))
            baseStart (fun row ↦ requestedLength (slots row)),
          initial.toMatrixState.restartTime = 0 ∧
          Relation.ReflTransGen TrackedState.Step initial final ∧
          final.Terminal ∧
          TrackedPencil (m + 2) last (seedLabel m)
            (MatrixAtlas.atlasMatrix final.toMatrixState.label)
            final.toMatrixState.currentStart ∧
          SemanticAtlasMarch.CarriesClearedFace (m + 2)
            (MatrixAtlas.atlasMatrix final.toMatrixState.label)
            final.toMatrixState.currentFinish := by
  have hSameGenus : genus (CaterpillarSeed.seed m).candidate.datum.sourceGraph =
      ((p + 1 - n : ℕ) : ℤ) := by
    rw [OuterWalk.genus_seed m, hGenus]
    push_cast
    ring
  obtain ⟨last, -, hReach, -, -, -, endpoint, -, slots, -, -, hslots⟩ :=
    StableSourceWhiteheadChain.exists_chain_of_fullDimensional
      (CaterpillarSeed.seed m).candidate.datum core hCubic hCoreConnected
      (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)) (by omega) hSameGenus
  have hEntry : OuterWalk.ConeEntry (m + 2) last (seedLabel m) :=
    coneEntry_of_reaches' (by omega) (seedLabel m) hReach interior link
      (OuterWalk.coneEntry_caterpillar m)
  obtain ⟨baseStart, hStart, hGeneric, initial, hZero⟩ :=
    hEntry (fun row ↦ requestedLength (slots row))
  obtain ⟨final, hreach, hterminal⟩ :=
    exists_terminal_of_reachable_tracked_progress (by omega)
      (fun l ↦ MatrixAtlas.atlasMatrix_det_ne_zero l) initial
      (fun current hcurrent hNonterminal ↦
        interior last hReach baseStart (fun row ↦ requestedLength (slots row)) current
          hStart (fun row ↦ hRequested (slots row))
          (restartTime_nonneg_of_reachable hZero hcurrent) hGeneric hNonterminal)
  exact ⟨last, endpoint, slots, hReach, hslots, baseStart, hStart, hGeneric, initial, final,
    hZero, hreach, hterminal, final.carriesTrackedPencil, final.clearedFace hterminal⟩

/-! ### The interior binder, discharged -/

/-- **The walk from the caterpillar seed, with no interior hypothesis.**
`exists_terminal_of_chain'` on `interior'_unconditional`: the tracked progress
at every nonterminal state of every cone of the chain is a theorem, so the only
local input left is the type-change `link`. -/
theorem exists_terminal_of_chain'' (m : ℕ) {n p : ℕ} (core : Core n p)
    (hCubic : core.Cubic) (hCoreConnected : core.Connected)
    (hGenus : p + 1 - n = 2 * m + 2)
    (link : ∀ K : CubicDartGraph (Dart (CaterpillarSeed.seed m).candidate.datum)
        (BranchVertex (CaterpillarSeed.seed m).candidate.datum),
      CubicDartGraph.Reaches (seedGraph m) K →
      ∀ (mv : K.MoveData)
        (arrival : OuterWalk.FacetArrival (m + 2) K (seedLabel m) (seedLabel m mv.base))
        (wd : OuterWalk.WallData arrival), OuterWalk.TypeChangeLink mv wd)
    (requestedLength : Fin p → ℚ) (hRequested : ∀ e, 0 ≤ requestedLength e) :
    ∃ (last : CubicDartGraph (Dart (CaterpillarSeed.seed m).candidate.datum)
        (BranchVertex (CaterpillarSeed.seed m).candidate.datum))
      (endpoint : last.Iso (CubicCoreDarts.ofCore core hCubic hCoreConnected))
      (slots : Fin (6 * m + 3) ≃ Fin p),
      CubicDartGraph.Reaches (seedGraph m) last ∧
      (∀ d, slots (seedLabel m d) = (endpoint.dart d).1) ∧
      ∃ baseStart : Fin (6 * m + 3) → ℚ,
        (∀ i, 0 < baseStart i) ∧
        AtlasGenericStart.AtlasGeneric (m + 2) baseStart
          (fun row ↦ requestedLength (slots row)) ∧
        ∃ initial final : TrackedState (m + 2) last (seedLabel m)
            (MatrixAtlas.atlasMatrix (coordinate := Fin (6 * m + 3)) (degree := m + 2))
            baseStart (fun row ↦ requestedLength (slots row)),
          initial.toMatrixState.restartTime = 0 ∧
          Relation.ReflTransGen TrackedState.Step initial final ∧
          final.Terminal ∧
          TrackedPencil (m + 2) last (seedLabel m)
            (MatrixAtlas.atlasMatrix final.toMatrixState.label)
            final.toMatrixState.currentStart ∧
          SemanticAtlasMarch.CarriesClearedFace (m + 2)
            (MatrixAtlas.atlasMatrix final.toMatrixState.label)
            final.toMatrixState.currentFinish :=
  exists_terminal_of_chain' m core hCubic hCoreConnected hGenus
    (fun _ _ ↦ interior'_unconditional) link requestedLength hRequested

end Chain

end

end DraismaVargas.LocalCases.OuterWalkInterior
