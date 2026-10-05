module

public import DraismaVargas.LocalCases.TrackedWallProgress
public import DraismaVargas.LocalCases.FacetGenericity
public import DraismaVargas.LocalCases.NonTrivalentLinkMatrix
public import DraismaVargas.LocalCases.NonTrivalentUniqueFourValent
public import DraismaVargas.LocalCases.NonTrivalentAnchorValency
public import DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
public import DraismaVargas.LocalCases.CertifiedPencil

@[expose] public section

/-!
# The outer walk: cone marches strung along the Whitehead chain

Source: Vargas, Part II, arXiv:2609.09109, Section 4.4 (the proof of the main theorem: a
piecewise-linear path from the caterpillar of loops to the requested metric
graph, meeting the codimension-one walls of `M_g^trop` transversely in finitely
many points), together with Section 5.1 (the labelling conventions at a
non-trivalent wall and the rigidity of every fibre vertex other than the
four-valent anchor).  In the formal route a Part II wall is never an inner wall
event of one march; it is the *terminal state* of a march whose endpoint was
chosen on an open facet of the current type's cone, followed by a *link* into a
fresh march in the next type's cone.

## What is proved here

* `ConeEntry` -- the invariant carried between cones: for every finishing
  vector there is a positive, atlas-generic start and a time-zero
  `TrackedState` in the cone of the current row-labelled graph.  It is
  inhabited at the caterpillar seed (`coneEntry_caterpillar`), from
  `TrackedState.caterpillarGeneric` and the same finite-hyperplane avoidance
  `CaterpillarGenericSeed.exists_genericInitialState` uses.
* `FacetArrival` -- how one cone march ends when its finish is a facet-generic
  point (`FacetGenericity.exists_facetGeneric`) on the facet `{facet = 0}`: a
  reachable terminal tracked state at which exactly one chart coordinate and
  exactly one stable row, namely `facet`, vanish (`existsUnique_zero_column`,
  `existsUnique_zero_stableRow`).  `exists_facetArrival` produces it from
  `ConeEntry` and the interior progress hypothesis.
* `WallData` -- the terminal payload unpacked at that facet, with the unique
  zero column named: the contracted target occurrence, its distinct endpoints
  (`fst_ne_snd`) and unit multiplicity (the target is a tree), the wall metric
  in the shape every non-trivalent wall construction takes, the contraction
  forest derived from the tracked non-loop dart (`Tracks.noContractedCycle`),
  dangling compatibility, the wall valency `∈ {2, 3, 4}`, the wall datum's
  validity, connectedness and genus zero, and -- per valency -- the anchor and
  the valid prescribed candidate with no further hypothesis
  (`exists_valid_candidate_four/three/two`).
* `TypeChangeLink` -- exactly what a type-changing *exit* must return at such a
  wall: a valid base datum over the wall target (the wall datum at valencies
  three and two; at valency four its block-preserving branch gauge
  `PrescribedPairing.gaugedData`, which is the base the `K = 0` candidate
  actually lives over), a candidate over it, its full-dimensional
  presentation, a tracking of the **next** graph `graph.move m` at the
  **same** labels, and the common-minor agreement off the contracted column.
  From these the file derives the outgoing corner, the same-sign determinant
  identity, the positive reflected start with its metric identity
  (`NonTrivalentLinkMatrix`), the atlas registration, the cleared pencil, and
  `TypeChangeLink.coneEntry`: the invariant in the next cone.
* `coneEntry_of_reaches` -- the finite induction along `Reaches`, the
  Whitehead chain of `StableSourceWhiteheadChain`, with the interior progress
  and the type-change links as named hypotheses quantified over the chain's
  graphs.
* `exists_terminal_of_chain` -- from the tracked caterpillar seed to a
  terminal tracked state in the cone of a graph isomorphic to the requested
  cubic core, at the requested finish read through the chain's slot map.

## The hypotheses of the walk, and where they are discharged

* `interior`: a `TrackedProgress` at every nonterminal tracked state of every
  cone -- the ten-way interior classification wired at every wall.  It is
  discharged with **no** remaining input by
  `OuterWalkInterior.interior'_unconditional` (via
  `InteriorBridgesAll.wallBridge`), so the walk itself needs only `link`.
* `link`: a `TypeChangeLink` at every `WallData` of every chain graph (the
  outgoing full-dimensional presentation with its row dictionary, the tracking
  of `graph.move m`, and `AgreeOffColumn`; the candidates themselves are built
  below).  `NonTrivalentValencyFourDispatcher.typeChangeLink_four` treats the
  four-valent walls, deriving the gauged base's validity and the pairing index
  prescribed by `m` from the wall valency alone (`card (incidentEdges ...) = 4`);
  `NonTrivalentValencyThreeDispatcher` treats the three-valent walls; and
  `NonTrivalentValencyTwoBaseOneLink.crossPairLink` settles the two-valent
  cross-pair hypothesis, so `NonTrivalentValencyTwoBaseOneLink.link_all`
  inhabits `link` at every wall datum of every chain graph with no hypothesis.

The terminal tracked state returned by `exists_terminal_of_chain` still has to
be identified with a pencil on the requested graph; that is done downstream
(`TerminalIdentification`, `StatementFromLink`).

Non-vacuity: `FacetArrival` and `WallData` are inhabited at the caterpillar
seed with no hypothesis (`nonempty_facetArrival_caterpillar`,
`nonempty_wallData_caterpillar`: the seed chart is diagonal, so the
facet-generic finish is already in its closed cone); `TypeChangeLink` is
inhabited at every wall datum by `NonTrivalentValencyTwoBaseOneLink.link_all`.

Nothing here identifies a graph by a matrix; every graph statement travels
along an actual `Tracks` or `Iso`.

Consumers: the type-changing exits at non-trivalent walls (through
`TypeChangeLink`), the interior progress (through `interior`), and the final
assembly (`StatementFromLink`, through `OuterWalkInterior.exists_terminal_of_chain''`).
-/

namespace DraismaVargas.LocalCases.OuterWalk

noncomputable section

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Gonality
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.RationalAffineWall
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StableSourceDarts
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.FiniteAtlasMarch
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.WallDegeneration

/-! ## 1.  The invariant between cones -/

section Entry

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- **The invariant carried from cone to cone.**  In the cone of the row-labelled
graph `graph`, every finishing vector admits a positive start, atlas-generic
(`AtlasGenericStart.AtlasGeneric`) against that finish, and a time-zero tracked
state of the universal
atlas march from that start to that finish.

The finish is universally quantified because the link into the next cone is
performed *before* the next cone's finish is known: `exists_positiveInChart_atlasGeneric`
perturbs the reflected start against whatever finish the next march is given. -/
def ConeEntry (degree : ℕ) (graph : CubicDartGraph D V) (label : D → coordinate) : Prop :=
  ∀ baseFinish : coordinate → ℚ,
    ∃ baseStart : coordinate → ℚ,
      (∀ i, 0 < baseStart i) ∧
      AtlasGenericStart.AtlasGeneric degree baseStart baseFinish ∧
      ∃ initial : TrackedState degree graph label
          (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
          baseStart baseFinish,
        initial.toMatrixState.restartTime = 0

end Entry

/-! ### Non-vacuity: the caterpillar seed enters its own cone -/

section Seed

/-- The seed cover's own constructed stable graph, the ambient graph of the
first cone. -/
noncomputable abbrev seedGraph (m : ℕ) :=
  TrackedPencil.seedGraph (CaterpillarSeed.seed m)
    (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m))

/-- The seed cover's literal row labels, the labels of every cone of the walk. -/
noncomputable abbrev seedLabel (m : ℕ) :=
  TrackedPencil.seedLabel (CaterpillarSeed.seed m)
    (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m))

/-- **The caterpillar seed inhabits the invariant.**  This is
`CaterpillarGenericSeed.exists_genericInitialState` with the tracked state
`TrackedState.caterpillarGeneric` in place of the semantic one: the same
generic start, chosen inside the seed's own chart against the given finish. -/
theorem coneEntry_caterpillar (m : ℕ) : ConeEntry (m + 2) (seedGraph m) (seedLabel m) := by
  intro baseFinish
  have hInverse : chartCoordinates (MatrixAtlas.atlasMatrix (CaterpillarGenericSeed.label m))
      ((CaterpillarGenericSeed.matrix m).mulVec fun _ ↦ (1 : ℚ)) = (fun _ ↦ (1 : ℚ)) := by
    rw [CaterpillarGenericSeed.atlasMatrix_label]
    exact chartCoordinates_eq_of_mulVec_eq _ (CaterpillarRows.fullDim m).det_ne_zero rfl
  obtain ⟨baseStart, hPositive, hGeneric⟩ :=
    AtlasGenericStart.exists_positiveInChart_atlasGeneric (m + 2)
      (CaterpillarGenericSeed.label m)
      ((CaterpillarGenericSeed.matrix m).mulVec fun _ ↦ (1 : ℚ)) baseFinish (by
        intro i
        rw [hInverse]
        exact one_pos)
  have hMap : (CaterpillarGenericSeed.matrix m).mulVec
      (chartCoordinates (MatrixAtlas.atlasMatrix (CaterpillarGenericSeed.label m)) baseStart) =
        baseStart := by
    rw [← CaterpillarGenericSeed.atlasMatrix_label]
    exact mulVec_chartCoordinates _ (MatrixAtlas.atlasMatrix_det_ne_zero _) baseStart
  refine ⟨baseStart, ?_, hGeneric,
    TrackedState.caterpillarGeneric m _ hPositive baseStart baseFinish hMap, rfl⟩
  intro row
  rw [← hMap]
  exact CaterpillarGenericSeed.mulVec_pos m _ hPositive row

end Seed

/-! ## 2.  How a cone march ends: arrival at a facet -/

section Arrival

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- **A cone march that ended on the open facet `{facet = 0}`.**  The finish is a
facet-generic point (`FacetGenericity.exists_facetGeneric`): zero at `facet`, positive
elsewhere, facet-generic for every chart of the universal atlas.  The final
state is terminal, i.e. its chart cone contains that endpoint, and it was
reached from a time-zero state, so its restart time is nonnegative (the
hypothesis under which the seed lemmas make every interior stable row
nonzero). -/
structure FacetArrival (degree : ℕ) (graph : CubicDartGraph D V) (label : D → coordinate)
    (facet : coordinate) where
  baseStart : coordinate → ℚ
  baseFinish : coordinate → ℚ
  start_pos : ∀ i, 0 < baseStart i
  finish_facet : baseFinish facet = 0
  finish_pos : ∀ t, t ≠ facet → 0 < baseFinish t
  facetGeneric : FacetGenericity.FacetGeneric degree baseFinish
  final : TrackedState degree graph label
    (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
    baseStart baseFinish
  terminal : final.Terminal
  restart_nonneg : 0 ≤ final.toMatrixState.restartTime

/-- Reachability of tracked states projects to reachability of matrix states. -/
theorem reflTransGen_toMatrixState {degree : ℕ} {graph : CubicDartGraph D V}
    {label : D → coordinate} {baseStart baseFinish : coordinate → ℚ}
    {s t : TrackedState degree graph label
      (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
      baseStart baseFinish}
    (h : Relation.ReflTransGen TrackedState.Step s t) :
    Relation.ReflTransGen FiniteAtlasMarch.State.Step s.toMatrixState t.toMatrixState := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih ((TrackedState.step_iff _ _).mp hbc)

/-- **One cone march.**  From the invariant, a facet-generic finish on the facet, and
a tracked progress at every nonterminal state of that cone, the tracked
universal-atlas march reaches a terminal state on the facet.  This is
`TrackedState.exists_terminal_reachable_of_tracked_progress` at the entry state,
with the restart time carried by `FiniteAtlasMarch.State.restartTime_nonneg_of_reachable`. -/
theorem exists_facetArrival {degree : ℕ} (hDegree : 2 ≤ degree)
    {graph : CubicDartGraph D V} {label : D → coordinate}
    (entry : ConeEntry degree graph label)
    (interior : ∀ (baseStart baseFinish : coordinate → ℚ)
      (current : TrackedState degree graph label
        (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
        baseStart baseFinish),
      ¬ current.Terminal → TrackedProgress current)
    (facet : coordinate) :
    Nonempty (FacetArrival degree graph label facet) := by
  obtain ⟨baseFinish, hfacet, hother, hgeneric⟩ :=
    FacetGenericity.exists_facetGeneric degree facet
  obtain ⟨baseStart, hstart, -, initial, hzero⟩ := entry baseFinish
  obtain ⟨final, hreach, hterminal, -, -, -⟩ :=
    TrackedState.exists_terminal_reachable_of_tracked_progress hDegree
      (fun l ↦ MatrixAtlas.atlasMatrix_det_ne_zero l) (interior baseStart baseFinish) initial
  exact ⟨⟨baseStart, baseFinish, hstart, hfacet, hother, hgeneric, final, hterminal,
    FiniteAtlasMarch.State.restartTime_nonneg_of_reachable hzero
      (reflTransGen_toMatrixState hreach)⟩⟩

namespace FacetArrival

variable {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  {facet : coordinate} (arrival : FacetArrival degree graph label facet)

/-- The terminal state's chart coordinates are nonnegative. -/
theorem currentFinish_nonneg (i : coordinate) :
    0 ≤ arrival.final.toMatrixState.currentFinish i :=
  (TrackedState.terminal_iff arrival.final).mp arrival.terminal i

/-- At the endpoint the stable row lengths are the finish. -/
theorem mulVec_currentFinish (row : coordinate) :
    (MatrixAtlas.atlasMatrix arrival.final.toMatrixState.label).mulVec
      arrival.final.toMatrixState.currentFinish row = arrival.baseFinish row :=
  NonTrivalentWallSetup.mulVec_currentFinish arrival.final.toMatrixState row

/-- **Exactly one chart coordinate vanishes**: facet genericity at the terminal
state (`FacetGenericity.existsUnique_zero_of_facetGeneric_atlas`).  This is the
contracted target occurrence `t₁` of Part II, Section 5.1, convention (2). -/
theorem existsUnique_zero_column :
    ∃! column : coordinate, arrival.final.toMatrixState.currentFinish column = 0 :=
  FacetGenericity.existsUnique_zero_of_facetGeneric_atlas degree
    arrival.final.toMatrixState.label facet arrival.baseFinish
    arrival.final.toMatrixState.currentFinish arrival.facetGeneric
    arrival.final.toMatrixState.currentFinish_map arrival.finish_facet
    arrival.currentFinish_nonneg

/-- **Exactly one stable row vanishes, and it is `facet`**
(`NonTrivalentWallSetup.existsUnique_zero_stableRow_of_facet`).  This is the
vanishing-row test that separates a type change from an interior crossing:
along the march (`t < 1`) every stable row is positive, so the interior
classifier's `hRows` holds and no type change is possible; at the endpoint
exactly this row vanishes, so the interior classifier does not apply and the
link is the only continuation. -/
theorem existsUnique_zero_stableRow :
    ∃! row : coordinate,
      (MatrixAtlas.atlasMatrix arrival.final.toMatrixState.label).mulVec
        arrival.final.toMatrixState.currentFinish row = 0 :=
  NonTrivalentWallSetup.existsUnique_zero_stableRow_of_facet arrival.final.toMatrixState
    facet arrival.finish_facet arrival.finish_pos

theorem mulVec_currentFinish_facet :
    (MatrixAtlas.atlasMatrix arrival.final.toMatrixState.label).mulVec
      arrival.final.toMatrixState.currentFinish facet = 0 := by
  rw [arrival.mulVec_currentFinish]
  exact arrival.finish_facet

theorem mulVec_currentFinish_pos (row : coordinate) (hrow : row ≠ facet) :
    0 < (MatrixAtlas.atlasMatrix arrival.final.toMatrixState.label).mulVec
      arrival.final.toMatrixState.currentFinish row := by
  rw [arrival.mulVec_currentFinish]
  exact arrival.finish_pos row hrow

end FacetArrival

end Arrival

/-! ## 3.  The wall data: the terminal payload with its zero column named -/

section Wall

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}

/-- **The terminal payload at a facet, unpacked, with the unique zero chart
coordinate named.**  Everything is the arrival's own: the retained candidate
and its full-dimensional presentation display the terminal chart matrix, the
tracking is of the cone's ambient graph at the cone's labels, and `column` is
the one vanishing chart coordinate.  No witness is chosen twice. -/
structure WallData {facet : coordinate} (arrival : FacetArrival degree graph label facet) where
  target : CFGraph.{0}
  data : GluingDatum target degree
  wall : target.V
  candidate : Candidate target degree data wall
  fullDim : FullDimensionalSourcePresentation candidate.datum coordinate
  matrix_eq : GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation =
    MatrixAtlas.atlasMatrix arrival.final.toMatrixState.label
  tracks : Tracks fullDim graph label
  column : coordinate
  column_zero : arrival.final.toMatrixState.currentFinish column = 0
  column_unique : ∀ c, arrival.final.toMatrixState.currentFinish c = 0 → c = column

/-- Every facet arrival has wall data: the payload is `TrackedPencil` and the
zero column is the one given by facet genericity. -/
theorem FacetArrival.nonempty_wallData {facet : coordinate}
    (arrival : FacetArrival degree graph label facet) : Nonempty (WallData arrival) := by
  obtain ⟨target, data, wall, candidate, fullDim, hmatrix, -, -, -, -, ⟨tracks⟩, -⟩ :=
    arrival.final.carriesTrackedPencil
  obtain ⟨column, hzero, hunique⟩ := arrival.existsUnique_zero_column
  exact ⟨⟨target, data, wall, candidate, fullDim, hmatrix, tracks, column, hzero, hunique⟩⟩

namespace WallData

variable {facet : coordinate} {arrival : FacetArrival degree graph label facet}

/-- The target of the terminal cover: the base target expanded at the wall
(`Candidate.datum` lives over `TargetExpansion.graph target wall candidate.right`). -/
abbrev coverTarget (wd : WallData arrival) : CFGraph.{0} :=
  TargetExpansion.graph wd.target wd.wall wd.candidate.right

/-- The terminal cover, the datum the tracking is about. -/
abbrev cover (wd : WallData arrival) : GluingDatum wd.coverTarget degree := wd.candidate.datum

/-- The wall metric: the terminal state's chart coordinates. -/
abbrev coordinates (_wd : WallData arrival) : coordinate → ℚ :=
  arrival.final.toMatrixState.currentFinish

/-- The incoming honest length matrix. -/
abbrev incomingMatrix (wd : WallData arrival) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix wd.fullDim.labelling.presentation

variable (wd : WallData arrival)

theorem coordinates_nonneg (c : coordinate) : 0 ≤ wd.coordinates c :=
  arrival.currentFinish_nonneg c

theorem coordinates_pos (c : coordinate) (hc : c ≠ wd.column) : 0 < wd.coordinates c :=
  lt_of_le_of_ne (wd.coordinates_nonneg c) (fun h ↦ hc (wd.column_unique c h.symm))

/-- The contracted target occurrence: the target edge of the zero column. -/
abbrev contracted (wd : WallData arrival) : wd.coverTarget.edges :=
  wd.fullDim.labelling.targetEdge wd.column

/-- Its two endpoints. -/
abbrev a (wd : WallData arrival) : wd.coverTarget.V :=
  (wd.contracted : wd.coverTarget.V × wd.coverTarget.V).1

abbrev b (wd : WallData arrival) : wd.coverTarget.V :=
  (wd.contracted : wd.coverTarget.V × wd.coverTarget.V).2

theorem hc : (wd.contracted : wd.coverTarget.V × wd.coverTarget.V) = (wd.a, wd.b) := rfl

/-- The target graph is loopless. -/
theorem hab : wd.a ≠ wd.b := GluingContraction.fst_ne_snd wd.contracted

/-- The target is a tree, so the contracted occurrence is simple. -/
theorem hOne : num_edges wd.coverTarget wd.a wd.b = 1 :=
  IteratedContraction.num_edges_eq_one_of_genus_zero_of_connected wd.coverTarget
    wd.fullDim.targetConnected wd.fullDim.targetGenus wd.contracted

theorem targetEdge_symm_contracted : wd.fullDim.labelling.targetEdge.symm wd.contracted = wd.column :=
  Equiv.symm_apply_apply _ _

theorem hZeroCoord : wd.coordinates (wd.fullDim.labelling.targetEdge.symm wd.contracted) = 0 := by
  rw [wd.targetEdge_symm_contracted]
  exact wd.column_zero

theorem hPosCoord (c : coordinate)
    (hc : c ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted) : 0 < wd.coordinates c := by
  rw [wd.targetEdge_symm_contracted] at hc
  exact wd.coordinates_pos c hc

/-- The incoming matrix applied to the wall metric is the finish. -/
theorem mulVec_coordinates (row : coordinate) :
    wd.incomingMatrix.mulVec wd.coordinates row = arrival.baseFinish row := by
  rw [incomingMatrix, wd.matrix_eq]
  exact arrival.mulVec_currentFinish row

theorem hFacetZero : wd.incomingMatrix.mulVec wd.coordinates facet = 0 := by
  rw [wd.mulVec_coordinates]
  exact arrival.finish_facet

theorem hRows (row : coordinate) (hrow : row ≠ facet) :
    wd.incomingMatrix.mulVec wd.coordinates row ≠ 0 := by
  rw [wd.mulVec_coordinates]
  exact (arrival.finish_pos row hrow).ne'

/-- The incoming matrix is entrywise nonnegative: it is an atlas matrix. -/
theorem incomingMatrix_nonneg (i j : coordinate) : 0 ≤ wd.incomingMatrix i j := by
  rw [incomingMatrix, wd.matrix_eq]
  exact FacetGenericity.atlasMatrix_nonneg _ i j

/-- The vanishing row is supported on the contracted column
(`NonTrivalentLinkMatrix.row_supported_of_zero_image`). -/
theorem incomingMatrix_facet_eq_zero (c : coordinate) (hc : c ≠ wd.column) :
    wd.incomingMatrix facet c = 0 :=
  NonTrivalentLinkMatrix.row_supported_of_zero_image wd.incomingMatrix_nonneg
    wd.column_zero wd.coordinates_pos wd.hFacetZero c hc

/-- The incoming corner is nonzero: the incoming determinant expands along the
vanishing row (`NonTrivalentLinkMatrix.det_eq_corner_mul_cofactor`). -/
theorem incoming_corner_ne_zero : wd.incomingMatrix facet wd.column ≠ 0 := by
  intro h
  apply wd.fullDim.det_ne_zero
  rw [NonTrivalentLinkMatrix.det_eq_corner_mul_cofactor wd.incomingMatrix_facet_eq_zero, h,
    zero_mul]

theorem incoming_corner_pos : 0 < wd.incomingMatrix facet wd.column :=
  lt_of_le_of_ne (wd.incomingMatrix_nonneg _ _) wd.incoming_corner_ne_zero.symm

/-- The reflected start: the wall metric with the contracted column opened by
`s > 0` (`NonTrivalentLinkMatrix.positiveStart`).  It is a positive chart point of
the outgoing cone. -/
theorem positiveStart_pos {s : ℚ} (hs : 0 < s) (c : coordinate) :
    0 < NonTrivalentLinkMatrix.positiveStart wd.coordinates wd.column s c :=
  NonTrivalentLinkMatrix.positiveStart_pos wd.column_zero wd.coordinates_pos hs c


/-- The wall datum: the terminal cover contracted along the zero occurrence. -/
abbrev wallDatum (wd : WallData arrival) :
    GluingDatum (contract wd.coverTarget wd.hab wd.hOne) degree :=
  contractDatum wd.cover wd.hc wd.hab wd.hOne

/-- The wall datum lives over a connected target ... -/
theorem wallTarget_connected : graph_connected (contract wd.coverTarget wd.hab wd.hOne) :=
  NonTrivalentUniqueFourValent.wall_target_connected wd.cover wd.fullDim wd.hab wd.hOne

/-- ... of genus zero. -/
theorem wallTarget_genus : genus (contract wd.coverTarget wd.hab wd.hOne) = 0 :=
  NonTrivalentUniqueFourValent.wall_target_genus wd.cover wd.fullDim wd.hab wd.hOne

end WallData

end Wall

/-! ### The wall data at the facet of a Whitehead move

The facet is the label of the move's contracted dart `m.base`, a non-loop of the
current ambient graph (`MoveData.nonloop`).  Through the tracking that dart is a
stable row of the terminal cover with a simple end, so the zero fibre of the
wall metric is a forest and the wall valency is `2`, `3` or `4`. -/

section Move

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

namespace WallData

/-- **No cycle contracts**: the vanishing stable row is the tracked image of the
move's contracted dart, a non-loop of the ambient graph (`MoveData.nonloop`,
`InteriorGraphTracking.Tracks.noContractedCycle`). -/
theorem noContractedCycle :
    NonTrivalentWallSetup.NoContractedCycle (data := wd.cover)
      wd.fullDim.labelling.presentation wd.coordinates wd.coordinates_nonneg :=
  Tracks.noContractedCycle wd.tracks m.base m.nonloop wd.coordinates
    wd.coordinates_nonneg wd.hRows

/-- The contraction forest of the crossed occurrence, with no further hypothesis. -/
theorem hForest : ContractionForest wd.cover wd.a wd.b wd.contracted :=
  NonTrivalentWallSetup.contractionForest_of_noContractedCycle
    wd.fullDim.labelling.presentation wd.coordinates wd.coordinates_nonneg
    (wd.noContractedCycle m) wd.hc wd.hZeroCoord

theorem hCompat : DanglingCompatible wd.cover wd.hc wd.hab wd.hOne :=
  WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
    wd.hOne (wd.hForest m)

/-- **The wall valency is `2`, `3` or `4`** (Part II `lemma-above-w0` together
with the `val w₀ ≠ 1` exclusion of `MonovalentWall`). -/
theorem valency :
    (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩).card = 2 ∨
      (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩).card = 3 ∨
        (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩).card = 4 :=
  NonTrivalentWallSetup.card_incidentEdges_merge_eq_two_three_or_four_of_noContractedCycle
    wd.fullDim wd.coordinates wd.coordinates_nonneg (wd.noContractedCycle m) wd.hc wd.hab
    wd.hOne wd.hZeroCoord

/-- The base stage of the outgoing payload: the wall datum is valid. -/
theorem wallDatum_valid : wd.wallDatum.Valid :=
  NonTrivalentUniqueFourValent.wall_valid wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (wd.hForest m)

/-! #### The prescribed candidates at the wall data, with no further hypothesis

Each valency's prescribed candidate exists over the wall datum (valencies three
and two) or over its block-preserving branch gauge (valency four) with no source
hypothesis; what remains at the wall is the *exit* (`TypeChangeLink` below).  At
valency four the pairing index `pairing : Fin 3` is the resolution prescribed by the
move `m`; translating `m` into that index through the tracking and the
four-branch anchor's star labels is part of the exit. -/

/-- Valency four: the `K = 0` candidate of `NonTrivalentValencyFourKZero`, via
`NonTrivalentUniqueFourValent.exists_valid_candidate_of_single_row`.  Its base
datum is **not** the wall datum itself but its block-preserving branch gauge
`PrescribedPairing.gaugedData` (the two selected classes are aligned to one-sheet
overlap), exactly as Figure 28's `w3Four` members sit over gauge copies; this is
why `TypeChangeLink` carries its own `base`. -/
theorem exists_valid_candidate_four
    (h4 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 4) (pairing : Fin 3) :
    ∃ (base : GluingDatum (contract wd.coverTarget wd.hab wd.hOne) degree)
      (candidate : Candidate (contract wd.coverTarget wd.hab wd.hOne) degree base
        ⟨wd.a, wd.hab⟩), candidate.datum.Valid := by
  obtain ⟨star⟩ : Nonempty (W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩) := ⟨W4TargetPairings.FourStar.of_card h4⟩
  obtain ⟨anchorBlock, hAnchor⟩ :=
    NonTrivalentUniqueFourValent.exists_wallBlock_nonDanglingValency_eq_four
      wd.cover wd.fullDim wd.hc wd.hab wd.hOne star (wd.hCompat m) wd.coordinates
      (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨source, hNoGlue, hRamification, geometry, hConnected, hGenus, hValid, -, -⟩ :=
    NonTrivalentUniqueFourValent.exists_valid_candidate_of_single_row wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne star (wd.hForest m) wd.coordinates (label m.base)
      wd.hRows wd.hZeroCoord anchorBlock hAnchor pairing
  exact ⟨NonTrivalentValencyFourKZero.PrescribedPairing.gaugedData source pairing hNoGlue
    hRamification,
    NonTrivalentValencyFourKZero.PrescribedPairing.candidate source pairing hNoGlue
      hRamification geometry hConnected hGenus, hValid⟩

/-- Valency three: the Type III candidate of `NonTrivalentValencyThreeCandidate`,
its anchor from `NonTrivalentAnchorValency.threeBranchAnchor_of_single_row`. -/
theorem exists_valid_candidate_three
    (h3 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 3) :
    ∃ (base : GluingDatum (contract wd.coverTarget wd.hab wd.hOne) degree)
      (candidate : Candidate (contract wd.coverTarget wd.hab wd.hOne) degree base
        ⟨wd.a, wd.hab⟩), candidate.datum.Valid := by
  obtain ⟨star⟩ : Nonempty (ThirdEquation.ThreeStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩) := ⟨ThirdEquation.ThreeStar.of_card h3⟩
  obtain ⟨anchorBlock, hAnchor, -⟩ :=
    NonTrivalentAnchorValency.threeBranchAnchor_of_single_row wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) wd.coordinates (label m.base) wd.hRows wd.hZeroCoord
      wd.hPosCoord wd.hFacetZero star
  obtain ⟨source, hNoGlue, hValid, hCandidate, -, -⟩ :=
    NonTrivalentValencyThreeCandidate.exists_valid_candidate_of_contraction wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) (wd.hCompat m) star anchorBlock hAnchor
  exact ⟨wd.wallDatum, _, hCandidate⟩

/-- Valency two: the Base II merge candidate of `NonTrivalentValencyTwoCandidate`,
its anchor from `NonTrivalentAnchorValency.twoBranchAnchor_of_single_row`. -/
theorem exists_valid_candidate_two
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2) :
    ∃ (base : GluingDatum (contract wd.coverTarget wd.hab wd.hOne) degree)
      (candidate : Candidate (contract wd.coverTarget wd.hab wd.hOne) degree base
        ⟨wd.a, wd.hab⟩), candidate.datum.Valid := by
  obtain ⟨star⟩ : Nonempty (W2R1Target.TwoStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩) := ⟨W2R1Target.TwoStar.of_card h2⟩
  obtain ⟨anchorBlock, hAnchor, -⟩ :=
    NonTrivalentAnchorValency.twoBranchAnchor_of_single_row wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) wd.coordinates (label m.base) wd.hRows wd.hZeroCoord
      wd.hPosCoord wd.hFacetZero star
  obtain ⟨source, hSelection⟩ :=
    NonTrivalentValencyTwoCandidate.exists_valid_candidate_of_contraction wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) (wd.hCompat m) star anchorBlock hAnchor
  obtain ⟨hCandidate, -, -, -⟩ :=
    hSelection (NonTrivalentValencyTwoCandidate.Prescribed.Selection.default source)
  exact ⟨wd.wallDatum, _, hCandidate⟩

/-- **At every wall of the walk there is a valid prescribed candidate**, by the
valency trichotomy.  The pairing at valency four is left as the one datum the
exit must compute from the move. -/
theorem exists_valid_candidate (pairing : Fin 3) :
    ∃ (base : GluingDatum (contract wd.coverTarget wd.hab wd.hOne) degree)
      (candidate : Candidate (contract wd.coverTarget wd.hab wd.hOne) degree base
        ⟨wd.a, wd.hab⟩), candidate.datum.Valid := by
  rcases wd.valency m with h2 | h3 | h4
  · exact wd.exists_valid_candidate_two m h2
  · exact wd.exists_valid_candidate_three m h3
  · exact wd.exists_valid_candidate_four m h4 pairing

end WallData

end Move

/-! ## 4.  The type-change link: what a type-changing exit must return -/

section Link

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}

/-- **The type-change link.**  Exactly what a type-changing exit must return at
the wall data of a Whitehead move `m`:

* an actual candidate over the wall datum (the base stage of the outgoing
  payload, so its validity, connectedness and genus zero are the wall's own);
* a full-dimensional presentation of the outgoing cover on the same
  `coordinate` type -- this carries `det ≠ 0`, trivalence and path ends, which
  the row dictionary of the exit must supply (`presentationOfEquivalence` does not
  apply: there is no stable-graph isomorphism across a type change);
* a tracking of the **next** graph `graph.move m` at the **same** labels: the
  new bridge occupies the slot of the contracted row, so the label function
  never changes along the walk; and
* the common-minor agreement off the contracted column
  (`StablePathFacetContraction.matrix_wallLabelling` on the retained rows,
  both vanishing rows supported on that column), from which the outgoing corner,
  the same-sign determinant identity and the reflected start's metric identity
  follow (`NonTrivalentLinkMatrix`).

Nothing else is asked.  The cleared pencil is derived at any positive chart
point (`Candidate.clearedPencil`), the atlas registration is
`MatrixAtlas.encodePresentation`, and atlas genericity is re-established by
`AtlasGenericStart.exists_positiveInChart_atlasGeneric`. -/
structure TypeChangeLink (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
    (wd : WallData arrival) where
  /-- The base datum of the outgoing candidate: the wall datum (valencies three
  and two) or a sheet gauge of it (valency four, `PrescribedPairing.gaugedData`). -/
  base : GluingDatum (contract wd.coverTarget wd.hab wd.hOne) degree
  baseValid : base.Valid
  candidate : Candidate (contract wd.coverTarget wd.hab wd.hOne) degree base ⟨wd.a, wd.hab⟩
  outgoingFD : FullDimensionalSourcePresentation candidate.datum coordinate
  tracks : Tracks outgoingFD (graph.move m) label
  agree : AgreeOffColumn wd.incomingMatrix
    (GluingDatum.LengthMatrixPresentation.matrix outgoingFD.labelling.presentation) wd.column

namespace TypeChangeLink

variable {m : graph.MoveData} {arrival : FacetArrival degree graph label (label m.base)}
  {wd : WallData arrival} (link : TypeChangeLink m wd)

/-- The outgoing honest length matrix. -/
abbrev outgoingMatrix : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix link.outgoingFD.labelling.presentation

theorem outgoingMatrix_det_ne_zero : (link.outgoingMatrix).det ≠ 0 :=
  link.outgoingFD.det_ne_zero

/-- The outgoing chart, registered in the universal atlas. -/
noncomputable def outgoingLabel : MatrixAtlas.chart coordinate degree :=
  MatrixAtlas.encodePresentation link.outgoingFD.labelling.presentation
    (fun row ↦ A04MoreTags.nodup_labelling_path _ row) link.outgoingFD.det_ne_zero

theorem atlasMatrix_outgoingLabel :
    MatrixAtlas.atlasMatrix (link.outgoingLabel) = link.outgoingMatrix :=
  MatrixAtlas.atlasMatrix_encodePresentation _ _ _

theorem outgoingMatrix_nonneg (i j : coordinate) : 0 ≤ link.outgoingMatrix i j := by
  rw [← link.atlasMatrix_outgoingLabel]
  exact FacetGenericity.atlasMatrix_nonneg _ i j

/-- The new bridge row is supported on the contracted column, by agreement. -/
theorem outgoingMatrix_facet_eq_zero (c : coordinate) (hc : c ≠ wd.column) :
    link.outgoingMatrix (label m.base) c = 0 :=
  (link.agree (label m.base) c hc).symm.trans (wd.incomingMatrix_facet_eq_zero c hc)

/-- **The outgoing corner is nonzero**: the outgoing determinant expands along
the bridge row (`NonTrivalentLinkMatrix.det_eq_corner_mul_cofactor`). -/
theorem corner_ne_zero : link.outgoingMatrix (label m.base) wd.column ≠ 0 := by
  intro h
  apply link.outgoingMatrix_det_ne_zero
  rw [NonTrivalentLinkMatrix.det_eq_corner_mul_cofactor (link.outgoingMatrix_facet_eq_zero),
    h, zero_mul]

theorem corner_pos : 0 < link.outgoingMatrix (label m.base) wd.column :=
  lt_of_le_of_ne (link.outgoingMatrix_nonneg _ _) (link.corner_ne_zero).symm

/-- **Same determinant sign across the type change**
(`NonTrivalentLinkMatrix.det_mul_pos`): unlike an interior wall, no balancing
argument is needed. -/
theorem det_mul_pos : 0 < wd.incomingMatrix.det * (link.outgoingMatrix).det :=
  NonTrivalentLinkMatrix.det_mul_pos link.agree wd.incomingMatrix_facet_eq_zero
    (link.outgoingMatrix_facet_eq_zero) wd.fullDim.det_ne_zero wd.incoming_corner_pos
    link.corner_pos

/-- **The metric identity of the reflected start**: its base image is the facet
point plus `s` times the outgoing matrix's contracted column
(`NonTrivalentLinkMatrix.positiveStart_map`). -/
theorem positiveStart_map (s : ℚ) :
    (link.outgoingMatrix).mulVec
        (NonTrivalentLinkMatrix.positiveStart wd.coordinates wd.column s) =
      arrival.baseFinish +
        s • (link.outgoingMatrix).mulVec (Pi.single wd.column 1) := by
  rw [NonTrivalentLinkMatrix.positiveStart_map link.agree wd.column_zero s]
  congr 1
  funext row
  exact wd.mulVec_coordinates row

/-- The outgoing inverse chart returns the reflected start
(`NonTrivalentLinkMatrix.chartCoordinates_positiveStart`). -/
theorem chartCoordinates_positiveStart (s : ℚ) :
    chartCoordinates (link.outgoingMatrix)
        ((link.outgoingMatrix).mulVec
          (NonTrivalentLinkMatrix.positiveStart wd.coordinates wd.column s)) =
      NonTrivalentLinkMatrix.positiveStart wd.coordinates wd.column s :=
  chartCoordinates_eq_of_mulVec_eq _ (link.outgoingMatrix_det_ne_zero) rfl

/-- A nonnegative nonsingular matrix sends a positive vector to a positive
vector. -/
theorem mulVec_pos_of_pos {B : Matrix coordinate coordinate ℚ}
    (hnonneg : ∀ i j, 0 ≤ B i j) (hdet : B.det ≠ 0)
    {v : coordinate → ℚ} (hv : ∀ j, 0 < v j) (i : coordinate) : 0 < B.mulVec v i := by
  classical
  by_contra hle
  have hzero : ∀ j, B i j = 0 := by
    intro j
    have hsum : (∑ j, B i j * v j) ≤ 0 := not_lt.mp hle
    have hterm : ∀ j ∈ Finset.univ, 0 ≤ B i j * v j :=
      fun j _ ↦ mul_nonneg (hnonneg i j) (hv j).le
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp
      (le_antisymm hsum (Finset.sum_nonneg hterm))
    exact (mul_eq_zero.mp (hall j (Finset.mem_univ j))).resolve_right (hv j).ne'
  exact hdet (Matrix.det_eq_zero_of_row_eq_zero i hzero)

include link in
/-- **The link produces the invariant in the next cone.**  Given the next
finish: register the outgoing chart, perturb the reflected start inside it to
an atlas-generic start (`AtlasGenericStart.exists_positiveInChart_atlasGeneric`),
and build the time-zero tracked state whose payload is the link's candidate,
its presentation, the cleared pencil at the positive chart coordinates
(`Candidate.clearedPencil`), and the tracking of `graph.move m`
(`TrackedPencil.of_tracks`, which derives the genus conjunct). -/
theorem coneEntry (hDegree : 2 ≤ degree) : ConeEntry degree (graph.move m) label := by
  intro baseFinish
  have hdet := link.outgoingMatrix_det_ne_zero
  have hpos : ∀ i, 0 < chartCoordinates (MatrixAtlas.atlasMatrix link.outgoingLabel)
      (link.outgoingMatrix.mulVec
        (NonTrivalentLinkMatrix.positiveStart wd.coordinates wd.column 1)) i := by
    intro i
    rw [link.atlasMatrix_outgoingLabel, link.chartCoordinates_positiveStart]
    exact wd.positiveStart_pos one_pos i
  obtain ⟨baseStart, hStart, hGeneric⟩ :=
    AtlasGenericStart.exists_positiveInChart_atlasGeneric degree link.outgoingLabel _
      baseFinish hpos
  have hMap : (MatrixAtlas.atlasMatrix link.outgoingLabel).mulVec
      (chartCoordinates (MatrixAtlas.atlasMatrix link.outgoingLabel) baseStart) =
        baseStart :=
    mulVec_chartCoordinates _ (MatrixAtlas.atlasMatrix_det_ne_zero _) baseStart
  have hStart' : ∀ j, 0 < chartCoordinates link.outgoingMatrix baseStart j := by
    intro j
    have h := hStart j
    rwa [link.atlasMatrix_outgoingLabel] at h
  have hBase : ∀ i, 0 < baseStart i := by
    intro i
    have h := mulVec_pos_of_pos link.outgoingMatrix_nonneg hdet hStart' i
    rwa [mulVec_chartCoordinates _ hdet] at h
  refine ⟨baseStart, hBase, hGeneric,
    ⟨⟨FiniteAtlasMarch.State.initial link.outgoingLabel _
      (chartCoordinates (MatrixAtlas.atlasMatrix link.outgoingLabel) baseFinish)
      hStart hMap
      (mulVec_chartCoordinates _ (MatrixAtlas.atlasMatrix_det_ne_zero _) baseFinish), ?_⟩,
      rfl⟩⟩
  exact TrackedPencil.of_tracks hDegree (contract wd.coverTarget wd.hab wd.hOne) link.base
    ⟨wd.a, wd.hab⟩ link.candidate link.outgoingFD link.atlasMatrix_outgoingLabel.symm
    link.baseValid wd.wallTarget_connected wd.wallTarget_genus
    (Candidate.clearedPencil link.candidate link.baseValid wd.wallTarget_connected
      wd.wallTarget_genus ⟨wd.a, wd.hab⟩ _ _ hStart)
    link.tracks

end TypeChangeLink

end Link

/-! ## 5.  The finite induction along the Whitehead chain -/

section Chain

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- **The outer walk, one cone at a time.**  Induction on the length of the
Whitehead chain `Reaches G H`: the invariant at `G`, a tracked progress at every
nonterminal state of every chain graph's cone, and a type-change link at every
wall data of every chain graph produce the invariant at `H`.  Each step is one
cone march to the facet of the move's contracted dart (`exists_facetArrival`),
the wall data there (`FacetArrival.nonempty_wallData`), and the link
(`TypeChangeLink.coneEntry`). -/
theorem coneEntry_of_reaches {degree : ℕ} (hDegree : 2 ≤ degree) (label : D → coordinate)
    {G H : CubicDartGraph D V} (hReach : CubicDartGraph.Reaches G H)
    (interior : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (baseStart baseFinish : coordinate → ℚ)
        (current : TrackedState degree K label
          (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
          baseStart baseFinish),
        ¬ current.Terminal → TrackedProgress current)
    (link : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival), TypeChangeLink m wd)
    (entry : ConeEntry degree G label) : ConeEntry degree H label := by
  induction hReach with
  | refl => exact entry
  | tail hGK hKH ih =>
    obtain ⟨m, rfl⟩ := hKH
    obtain ⟨arrival⟩ := exists_facetArrival hDegree ih (interior _ hGK) (label m.base)
    obtain ⟨wd⟩ := arrival.nonempty_wallData
    exact (link _ hGK m arrival wd).coneEntry hDegree

end Chain

/-! ## 6.  From the caterpillar seed to the requested core -/

section Walk

open Utilities.Certificate.ExplicitPotential

/-- **Genus bookkeeping.**  A full-dimensional presentation on `Fin (6m+3)`
coordinates in degree `m + 2` has source genus `2m + 2`: the target has as many
occurrences as there are coordinates, and `saturated` reads
`3g − 3 = 2g + 2d − 5`. -/
theorem genus_sourceGraph_of_fullDim (m : ℕ) {target : CFGraph}
    {data : GluingDatum target (m + 2)}
    (fd : FullDimensionalSourcePresentation data (Fin (6 * m + 3))) :
    genus data.sourceGraph = 2 * (m : ℤ) + 2 := by
  have hsat := fd.saturated
  have hcard : (Multiset.card target.edges : ℤ) = 6 * (m : ℤ) + 3 := by
    have h := Fintype.card_congr fd.labelling.targetEdge
    simp only [Fintype.card_fin] at h
    have h' : Fintype.card (target.edges) = Multiset.card target.edges := Multiset.card_coe _
    omega
  push_cast at hsat
  omega

/-- The seed cover's source genus is `2m + 2`. -/
theorem genus_seed (m : ℕ) :
    genus (CaterpillarSeed.seed m).candidate.datum.sourceGraph = 2 * (m : ℤ) + 2 :=
  genus_sourceGraph_of_fullDim m (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m))

/-- **The walk.**  Fix the requested connected cubic core of genus `2m + 2` and
the requested stable lengths `requestedLength` on its slots.  The finite
Whitehead chain from the seed cover's own graph to that core
(`StableSourceWhiteheadChain.exists_chain_of_fullDimensional`) is walked cone by
cone by `coneEntry_of_reaches`; the last cone is entered at the requested finish
read through the chain's terminal slot map, and its march ends at a terminal
tracked state.

Returned: the terminal chain graph `last` with its isomorphism onto the core,
the slot map `slots : Fin (6m+3) ≃ Fin p` reading the seed labels to core slots
(the walk never changes the labels), the last cone's generic start, its
time-zero state, and the terminal tracked state reached from it with its
tracked payload and cleared face -- exactly what the terminal identification
(`TerminalIdentification`) takes. -/
theorem exists_terminal_of_chain (m : ℕ) {n p : ℕ} (core : Core n p)
    (hCubic : core.Cubic) (hCoreConnected : core.Connected)
    (hGenus : p + 1 - n = 2 * m + 2)
    (interior : ∀ K : CubicDartGraph (Dart (CaterpillarSeed.seed m).candidate.datum)
        (BranchVertex (CaterpillarSeed.seed m).candidate.datum),
      CubicDartGraph.Reaches (seedGraph m) K →
      ∀ (baseStart baseFinish : Fin (6 * m + 3) → ℚ)
        (current : TrackedState (m + 2) K (seedLabel m)
          (MatrixAtlas.atlasMatrix (coordinate := Fin (6 * m + 3)) (degree := m + 2))
          baseStart baseFinish),
        ¬ current.Terminal → TrackedProgress current)
    (link : ∀ K : CubicDartGraph (Dart (CaterpillarSeed.seed m).candidate.datum)
        (BranchVertex (CaterpillarSeed.seed m).candidate.datum),
      CubicDartGraph.Reaches (seedGraph m) K →
      ∀ (mv : K.MoveData) (arrival : FacetArrival (m + 2) K (seedLabel m) (seedLabel m mv.base))
        (wd : WallData arrival), TypeChangeLink mv wd)
    (requestedLength : Fin p → ℚ) :
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
    rw [genus_seed m, hGenus]
    push_cast
    ring
  obtain ⟨last, -, hReach, -, -, -, endpoint, -, slots, -, -, hslots⟩ :=
    StableSourceWhiteheadChain.exists_chain_of_fullDimensional
      (CaterpillarSeed.seed m).candidate.datum core hCubic hCoreConnected
      (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)) (by omega) hSameGenus
  have hEntry : ConeEntry (m + 2) last (seedLabel m) :=
    coneEntry_of_reaches (by omega) (seedLabel m) hReach interior link (coneEntry_caterpillar m)
  obtain ⟨baseStart, hStart, hGeneric, initial, hZero⟩ :=
    hEntry (fun row ↦ requestedLength (slots row))
  obtain ⟨final, hreach, hterminal, hpencil, hface, -⟩ :=
    TrackedState.exists_terminal_reachable_of_tracked_progress (by omega)
      (fun l ↦ MatrixAtlas.atlasMatrix_det_ne_zero l) (interior last hReach baseStart _) initial
  exact ⟨last, endpoint, slots, hReach, hslots, baseStart, hStart, hGeneric, initial, final,
    hZero, hreach, hterminal, hpencil, hface⟩

end Walk

/-! ## 7.  Non-vacuity

`FacetArrival` and hence `WallData` are inhabited **unconditionally** at the
caterpillar seed: the seed chart is diagonal with a positive diagonal
(`CaterpillarRows.diagonalPattern`), so its closed cone is the whole
nonnegative orthant of stable lengths and the facet-generic finish is already
inside it -- the time-zero state is terminal with no march step.

`TypeChangeLink` is a structure with a `Tracks` field on `graph.move m`, so an
inhabitant is an actual type change, which is what the type-changing exits
construct (`NonTrivalentValencyTwoBaseOneLink.link_all`); its fields are also
separately inhabited here (the candidates by `WallData.exists_valid_candidate`,
the agreement by the reflexive instance below). -/

section NonVacuity

/-- The seed chart's coordinates of a nonnegative base vector are nonnegative:
the seed's cone is the closed positive orthant. -/
theorem chartCoordinates_seed_nonneg (m : ℕ) (y : Fin (6 * m + 3) → ℚ)
    (hy : ∀ i, 0 ≤ y i) (i : Fin (6 * m + 3)) :
    0 ≤ chartCoordinates (MatrixAtlas.atlasMatrix (CaterpillarGenericSeed.label m)) y i := by
  rw [CaterpillarGenericSeed.atlasMatrix_label]
  have hd : ∀ t, 0 < (CaterpillarGenericSeed.matrix m) t t :=
    fun t ↦ (CaterpillarRows.diagonalPattern m).matrix_diag_pos t
  have hmap : (CaterpillarGenericSeed.matrix m).mulVec
      (fun t ↦ y t / (CaterpillarGenericSeed.matrix m) t t) = y := by
    funext t
    change (GluingDatum.LengthMatrixPresentation.matrix
      (CaterpillarRows.labelling m).presentation).mulVec _ t = y t
    rw [(CaterpillarRows.diagonalPattern m).matrix_eq_diagonal, Matrix.mulVec_diagonal,
      mul_comm]
    exact div_mul_cancel₀ (y t) (hd t).ne'
  rw [chartCoordinates_eq_of_mulVec_eq (CaterpillarGenericSeed.matrix m)
    (CaterpillarRows.fullDim m).det_ne_zero hmap]
  exact div_nonneg (hy i) (hd i).le

/-- **The caterpillar seed inhabits `FacetArrival` at every facet, with no
hypothesis.**  The facet-generic finish on `{facet = 0}` lies in the seed chart's closed
cone, so `TrackedState.caterpillarGeneric` at that finish is already terminal. -/
theorem nonempty_facetArrival_caterpillar (m : ℕ) (facet : Fin (6 * m + 3)) :
    Nonempty (FacetArrival (m + 2) (seedGraph m) (seedLabel m) facet) := by
  obtain ⟨y, hfacet, hother, hgeneric⟩ := FacetGenericity.exists_facetGeneric (m + 2) facet
  have hy : ∀ i, 0 ≤ y i := by
    intro i
    by_cases hi : i = facet
    · rw [hi, hfacet]
    · exact (hother i hi).le
  have hInverse : chartCoordinates (MatrixAtlas.atlasMatrix (CaterpillarGenericSeed.label m))
      ((CaterpillarGenericSeed.matrix m).mulVec fun _ ↦ (1 : ℚ)) = (fun _ ↦ (1 : ℚ)) := by
    rw [CaterpillarGenericSeed.atlasMatrix_label]
    exact chartCoordinates_eq_of_mulVec_eq _ (CaterpillarRows.fullDim m).det_ne_zero rfl
  obtain ⟨baseStart, hPositive, -⟩ :=
    AtlasGenericStart.exists_positiveInChart_atlasGeneric (m + 2)
      (CaterpillarGenericSeed.label m)
      ((CaterpillarGenericSeed.matrix m).mulVec fun _ ↦ (1 : ℚ)) y (by
        intro i
        rw [hInverse]
        exact one_pos)
  have hMap : (CaterpillarGenericSeed.matrix m).mulVec
      (chartCoordinates (MatrixAtlas.atlasMatrix (CaterpillarGenericSeed.label m)) baseStart) =
        baseStart := by
    rw [← CaterpillarGenericSeed.atlasMatrix_label]
    exact mulVec_chartCoordinates _ (MatrixAtlas.atlasMatrix_det_ne_zero _) baseStart
  refine ⟨⟨baseStart, y, ?_, hfacet, hother, hgeneric,
    TrackedState.caterpillarGeneric m _ hPositive baseStart y hMap,
    fun i ↦ chartCoordinates_seed_nonneg m y hy i, le_rfl⟩⟩
  intro row
  rw [← hMap]
  exact CaterpillarGenericSeed.mulVec_pos m _ hPositive row

/-- Hence `WallData` is inhabited at the seed with no hypothesis. -/
theorem nonempty_wallData_caterpillar (m : ℕ) (facet : Fin (6 * m + 3)) :
    ∃ arrival : FacetArrival (m + 2) (seedGraph m) (seedLabel m) facet,
      Nonempty (WallData arrival) := by
  obtain ⟨arrival⟩ := nonempty_facetArrival_caterpillar m facet
  exact ⟨arrival, arrival.nonempty_wallData⟩

/-- `AgreeOffColumn` is reflexive: the identity link's agreement field. -/
theorem agreeOffColumn_refl {ι : Type} (A : Matrix ι ι ℚ) (column : ι) :
    AgreeOffColumn A A column := fun _ _ _ ↦ rfl

end NonVacuity

end

end DraismaVargas.LocalCases.OuterWalk
