module

public import DraismaVargas.Infrastructure.GluingTransport
public import DraismaVargas.Infrastructure.SheetJoin
public import DraismaVargas.LocalCases.BalancedGlobal
public import DraismaVargas.LocalCases.SemanticAtlasMarch

@[expose] public section

/-!
# A neutral candidate constructor

Every other `BalancedGlobal.Candidate` in the library is produced inside one
source equation of the Draisma--Vargas local case analysis.  This file supplies
the neutral constructor that the universal seed needs instead: *present this
gluing datum as a resolution of one wall*, with no reference to any wall
figure.

## What a candidate really is

Unwinding `Candidate.datum`, a candidate over `(target, data, wall)` is exactly
a presentation of one gluing datum over the one-edge vertex expansion
`TargetExpansion.graph target wall right`.  So the constructor below is stated
in both directions:

* `Presentation` is the minimal blockwise-free input list, and
  `Presentation.candidate` turns it into a `Candidate`;
* `expandedDatum` names the resulting datum over the expanded target, and
  `datum_candidate` identifies it, so that a caller which built its cover
  *forwards* -- as an expansion of a smaller valid datum -- sees literally its
  own object come back out;
* `riemannHurwitzAt_oldVertex_iff` / `riemannHurwitzAt_freshVertex_iff`
  convert the two wall receipts into Riemann--Hurwitz of the expanded datum at
  the two copies of the wall -- the form in which a caller holding a valid big
  datum already has them -- and `Presentation.ofExpandedRiemannHurwitz` is the
  constructor that consumes that form directly;
* `Presentation.ofCandidate` runs the extraction backwards: a candidate whose
  local resolution does not vary across wall blocks *is* a presentation.  So
  the hypothesis list below is not merely sufficient, it is exactly the content
  of a uniform candidate -- nothing is assumed that a candidate does not
  already carry.

## The honest hypothesis list

`Presentation` asks for a side assignment `right`, one `LocalResolution`
(uniform across wall blocks -- the seed has no reason to vary it), the
contraction receipt, one refinement receipt per wall incidence, and the two
endpoint Riemann--Hurwitz inequalities.  Everything else that `Candidate`
stores -- the two occurrence lists and their multiset identifications, and the
blockwise form of the two inequalities -- is supplied here once and for all.

Of the four remaining receipts, three are free to a caller that already has a
valid cover over the expanded target: `contracts` by
`contractsTo_of_vertexPartition_eq_join` if it *defines* the contracted wall
partition as `SheetPartition.join` of its two endpoint partitions, `exterior`
by the two refinement fields of its own datum at the two copies of the wall,
and the two inequalities by `Presentation.ofExpandedRiemannHurwitz`.  Only
`right` is a genuine choice, and it is a choice the caller made when it split
the wall.

`Seed` then adds exactly the three facts about the *contracted* stage that
`Candidate.clearedPencil` and `SemanticAtlasMarch.CarriesClearedPencil`
consume and that no expansion lemma can recover: `data.Valid`,
`graph_connected target` and `genus target = 0`.  `Seed.carriesClearedPencil`
shows that a `Seed`, a length-matrix presentation and a positive rational
coordinate vector are together *sufficient*: nothing else is owed at the
semantic layer.

## What is deliberately not attempted

The pendant shortcut
(`right := fun _ ↦ false`, `resolution := joinedResolutionAt`) satisfies
`contracts` and `right_riemannHurwitz` for free, fails `left_riemannHurwitz`
off the discrete wall, and even when it holds the new target column of the
length matrix is identically zero.  Nothing here uses it.

The remaining glue for a caller that builds its cover as a literal `CFGraph`
and only afterwards wants to contract an edge is recorded in
`ExpansionReceipt`: it is the statement that the expansion of the contraction
is the original, i.e. a `CFGraph` isomorphism plus the identification of the
transported datum.  That statement is *not* proved here; it is stated so that
the obligation is explicit rather than implicit, and
`Presentation.ofExpansionReceipt` shows exactly what it buys.
-/

namespace DraismaVargas.LocalCases.SeedCandidate

open Utilities
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.BalancedGlobal

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree} {wall : target.V}

/-! ## The uniform exterior receipt -/

/-- Every old occurrence at the wall refines the endpoint partition of the side
it was assigned to.  This is the non-blockwise form of `Candidate.exterior`;
for a uniform local resolution the two are interchangeable. -/
def ExteriorRefines (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree) : Prop :=
  ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    (data.edgePartition edge).Refines
      (if right edge then resolution.right else resolution.left)

theorem ExteriorRefines.onBlock {right : target.edges → Bool}
    {resolution : LocalResolution degree}
    (hExterior : ExteriorRefines data wall right resolution) :
    ∀ edge : target.edges,
      ((edge : target.V × target.V).1 = wall ∨
        (edge : target.V × target.V).2 = wall) →
      ∀ anchor, (data.edgePartition edge).RefinesOnBlock
        (if right edge then resolution.right else resolution.left)
        (data.vertexPartition wall) anchor := by
  intro edge hIncident anchor
  exact (hExterior edge hIncident).refinesOnBlock anchor

theorem ExteriorRefines.oldCompatible {right : target.edges → Bool}
    {resolution : LocalResolution degree}
    (hExterior : ExteriorRefines data wall right resolution) :
    GlobalResolution.OldCompatible data wall right resolution :=
  GlobalResolution.oldCompatible_of_wall data wall right resolution hExterior

/-- The contraction receipt is free when the contracted wall partition is
literally the join of the two chosen endpoint partitions.  `SheetPartition.join`
is the general join constructor of `Infrastructure.SheetJoin`; a seed which
*defines* its
contracted wall partition this way owes nothing here. -/
theorem contractsTo_of_vertexPartition_eq_join
    (resolution : LocalResolution degree)
    (hWall : data.vertexPartition wall =
      SheetPartition.join resolution.left resolution.right) :
    resolution.ContractsTo (data.vertexPartition wall) := by
  rw [hWall]
  exact SheetPartition.isJoin_join resolution.left resolution.right

/-! ## The neutral presentation -/

/-- The complete input of the neutral candidate constructor.  Compare the ten
fields of `BalancedGlobal.Candidate`: the two occurrence lists, their two
multiset identifications and the blockwise quantifier of the two
Riemann--Hurwitz receipts are all discharged by `Presentation.candidate`. -/
structure Presentation (data : GluingDatum target degree) (wall : target.V) where
  /-- Which old wall occurrences move to the fresh copy of the wall. -/
  right : target.edges → Bool
  /-- The two endpoint partitions and the new-edge partition. -/
  resolution : LocalResolution degree
  /-- Contracting the new edge returns the wall partition. -/
  contracts : resolution.ContractsTo (data.vertexPartition wall)
  /-- Each old wall occurrence refines the endpoint it was assigned to. -/
  exterior : ExteriorRefines data wall right resolution
  /-- Riemann--Hurwitz at the retained copy of the wall. -/
  left_riemannHurwitz : SheetPartition.RiemannHurwitzAt resolution.left
    (resolution.newEdge ::
      (wallEdgesAssigned target wall right false).toList.map data.edgePartition)
  /-- Riemann--Hurwitz at the fresh copy of the wall. -/
  right_riemannHurwitz : SheetPartition.RiemannHurwitzAt resolution.right
    (resolution.newEdge ::
      (wallEdgesAssigned target wall right true).toList.map data.edgePartition)

namespace Presentation

variable (presentation : Presentation data wall)

/-- The neutral candidate.  No local wall figure is consulted. -/
noncomputable def candidate : Candidate target degree data wall where
  right := presentation.right
  resolution := fun _ ↦ presentation.resolution
  contracts := fun _ ↦ presentation.contracts
  exterior := presentation.exterior.onBlock
  leftEdges := (wallEdgesAssigned target wall presentation.right false).toList
  rightEdges := (wallEdgesAssigned target wall presentation.right true).toList
  leftEdges_eq := Finset.coe_toList _
  rightEdges_eq := Finset.coe_toList _
  left_riemannHurwitz := by
    intro anchor hCanonical
    exact (LocalResolution.riemannHurwitzAt_iff_forall_wallBlock
      (data.vertexPartition wall) presentation.resolution.left _).mp
      presentation.left_riemannHurwitz anchor hCanonical
  right_riemannHurwitz := by
    intro anchor hCanonical
    exact (LocalResolution.riemannHurwitzAt_iff_forall_wallBlock
      (data.vertexPartition wall) presentation.resolution.right _).mp
      presentation.right_riemannHurwitz anchor hCanonical

@[simp] theorem candidate_right :
    presentation.candidate.right = presentation.right := rfl

@[simp] theorem candidate_resolution (anchor : Fin degree) :
    presentation.candidate.resolution anchor = presentation.resolution := rfl

/-- The datum over the expanded target presented by the seed. -/
noncomputable def expandedDatum :
    GluingDatum (TargetExpansion.graph target wall presentation.right) degree :=
  GlobalResolution.datum data wall presentation.right presentation.resolution
    presentation.exterior.oldCompatible

/-- The candidate's own datum is literally the presented one: no transport
step separates a seed's cover from the object `CarriesClearedPencil` asks
about. -/
theorem datum_candidate :
    presentation.candidate.datum = presentation.expandedDatum := rfl

/-- The presented cover is a valid gluing datum as soon as the contracted one
is.  This is the only place where `data.Valid` is used, and it cannot be
avoided: `Candidate.datum_valid` consumes it. -/
theorem expandedDatum_valid (hValid : data.Valid) :
    presentation.expandedDatum.Valid :=
  presentation.candidate.datum_valid hValid

end Presentation

/-! ## The two wall receipts, read off the expanded datum -/

section ExpandedReceipts

variable (right : target.edges → Bool) (resolution : LocalResolution degree)
  (hCompatible : GlobalResolution.OldCompatible data wall right resolution)

/-- Riemann--Hurwitz at the retained copy of the wall, in the expanded datum,
is exactly the first wall receipt of `Presentation`. -/
theorem riemannHurwitzAt_oldVertex_iff :
    (GlobalResolution.datum data wall right resolution
        hCompatible).RiemannHurwitzAtTargetVertex (oldVertex target wall) ↔
      SheetPartition.RiemannHurwitzAt resolution.left
        (resolution.newEdge ::
          (wallEdgesAssigned target wall right false).toList.map
            data.edgePartition) := by
  rw [GluingDatum.riemannHurwitzAtTargetVertex_iff_incidentList
    (GlobalResolution.datum data wall right resolution hCompatible)
    (oldVertex target wall) (leftIncidentList target wall right)
    (leftIncidentList_multiset target wall right),
    GlobalResolution.datum_edgePartitions_incidentList,
    GlobalResolution.datum_vertexPartition_old_wall]

/-- Riemann--Hurwitz at the fresh copy of the wall, in the expanded datum, is
exactly the second wall receipt of `Presentation`. -/
theorem riemannHurwitzAt_freshVertex_iff :
    (GlobalResolution.datum data wall right resolution
        hCompatible).RiemannHurwitzAtTargetVertex (freshVertex target) ↔
      SheetPartition.RiemannHurwitzAt resolution.right
        (resolution.newEdge ::
          (wallEdgesAssigned target wall right true).toList.map
            data.edgePartition) := by
  rw [GluingDatum.riemannHurwitzAtTargetVertex_iff_incidentList
    (GlobalResolution.datum data wall right resolution hCompatible)
    (freshVertex target) (rightIncidentList target wall right)
    (rightIncidentList_multiset target wall right),
    GlobalResolution.datum_edgePartitions_incidentList,
    GlobalResolution.datum_vertexPartition_fresh]

end ExpandedReceipts

/-- A caller which already knows that its cover over the *expanded* target is a
valid gluing datum owes no wall receipt whatsoever: the two endpoint
inequalities of `Presentation` are its Riemann--Hurwitz condition at the two
copies of the wall.  This is the form in which a seed built forwards -- one
`TargetExpansion` step at a time -- has its information. -/
noncomputable def Presentation.ofExpandedRiemannHurwitz
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (contracts : resolution.ContractsTo (data.vertexPartition wall))
    (exterior : ExteriorRefines data wall right resolution)
    (hRiemannHurwitz : (GlobalResolution.datum data wall right resolution
      exterior.oldCompatible).RiemannHurwitz) :
    Presentation data wall where
  right := right
  resolution := resolution
  contracts := contracts
  exterior := exterior
  left_riemannHurwitz :=
    (riemannHurwitzAt_oldVertex_iff right resolution
      exterior.oldCompatible).mp (hRiemannHurwitz (oldVertex target wall))
  right_riemannHurwitz :=
    (riemannHurwitzAt_freshVertex_iff right resolution
      exterior.oldCompatible).mp (hRiemannHurwitz (freshVertex target))

@[simp] theorem Presentation.ofExpandedRiemannHurwitz_right
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (contracts : resolution.ContractsTo (data.vertexPartition wall))
    (exterior : ExteriorRefines data wall right resolution)
    (hRiemannHurwitz : (GlobalResolution.datum data wall right resolution
      exterior.oldCompatible).RiemannHurwitz) :
    (Presentation.ofExpandedRiemannHurwitz right resolution contracts exterior
      hRiemannHurwitz).right = right := rfl

@[simp] theorem Presentation.ofExpandedRiemannHurwitz_resolution
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (contracts : resolution.ContractsTo (data.vertexPartition wall))
    (exterior : ExteriorRefines data wall right resolution)
    (hRiemannHurwitz : (GlobalResolution.datum data wall right resolution
      exterior.oldCompatible).RiemannHurwitz) :
    (Presentation.ofExpandedRiemannHurwitz right resolution contracts exterior
      hRiemannHurwitz).resolution = resolution := rfl

theorem Presentation.expandedDatum_ofExpandedRiemannHurwitz
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (contracts : resolution.ContractsTo (data.vertexPartition wall))
    (exterior : ExteriorRefines data wall right resolution)
    (hRiemannHurwitz : (GlobalResolution.datum data wall right resolution
      exterior.oldCompatible).RiemannHurwitz) :
    (Presentation.ofExpandedRiemannHurwitz right resolution contracts exterior
      hRiemannHurwitz).expandedDatum =
      GlobalResolution.datum data wall right resolution
        exterior.oldCompatible := rfl

/-! ## The hypothesis list is also necessary -/

section Converse

variable (candidate : Candidate target degree data wall)
  (resolution : LocalResolution degree)
  (hUniform : candidate.resolution = fun _ ↦ resolution)

/-- Extract the wall receipts back out of a candidate whose local resolution
does not vary across wall blocks.  Together with `Presentation.candidate` this
says that the hypothesis list of the neutral constructor is not merely
sufficient but exactly right: a uniform-resolution candidate *is* a
presentation, with no receipt weakened and none added. -/
noncomputable def Presentation.ofCandidate : Presentation data wall where
  right := candidate.right
  resolution := resolution
  contracts := by
    have := candidate.contracts ⟨0, data.degree_pos⟩
    rwa [hUniform] at this
  exterior := by
    intro edge hIncident first second hFine
    have hBlock := candidate.exterior edge hIncident
      ((data.vertexPartition wall).repr first)
    rw [hUniform] at hBlock
    exact hBlock.rel ((data.vertexPartition wall).rel_repr_left first) hFine
  left_riemannHurwitz := by
    have hBlocks : ∀ anchor, (data.vertexPartition wall).repr anchor = anchor →
        LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
          resolution.left
          (resolution.newEdge :: candidate.leftEdges.map data.edgePartition)
          anchor := by
      intro anchor hCanonical
      have hAnchor := candidate.left_riemannHurwitz anchor hCanonical
      rwa [hUniform] at hAnchor
    refine (SheetPartition.riemannHurwitzAt_iff_of_perm resolution.left ?_).mp
      ((LocalResolution.riemannHurwitzAt_iff_forall_wallBlock
        (data.vertexPartition wall) resolution.left _).mpr hBlocks)
    refine List.Perm.cons _ (List.Perm.map _ (Multiset.coe_eq_coe.mp ?_))
    rw [Finset.coe_toList]
    exact candidate.leftEdges_eq
  right_riemannHurwitz := by
    have hBlocks : ∀ anchor, (data.vertexPartition wall).repr anchor = anchor →
        LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
          resolution.right
          (resolution.newEdge :: candidate.rightEdges.map data.edgePartition)
          anchor := by
      intro anchor hCanonical
      have hAnchor := candidate.right_riemannHurwitz anchor hCanonical
      rwa [hUniform] at hAnchor
    refine (SheetPartition.riemannHurwitzAt_iff_of_perm resolution.right ?_).mp
      ((LocalResolution.riemannHurwitzAt_iff_forall_wallBlock
        (data.vertexPartition wall) resolution.right _).mpr hBlocks)
    refine List.Perm.cons _ (List.Perm.map _ (Multiset.coe_eq_coe.mp ?_))
    rw [Finset.coe_toList]
    exact candidate.rightEdges_eq

/-- The round trip is the identity on the presented cover. -/
theorem Presentation.expandedDatum_ofCandidate :
    (Presentation.ofCandidate candidate resolution hUniform).expandedDatum =
      candidate.datum := by
  obtain ⟨right, localResolution, contracts, exterior, leftEdges, rightEdges,
    leftEdges_eq, rightEdges_eq, left_riemannHurwitz, right_riemannHurwitz⟩ :=
    candidate
  cases hUniform
  rfl

end Converse

/-! ## A complete seed at the semantic layer -/

/-- Everything a seed has to produce in order to inhabit
`SemanticAtlasMarch.CarriesClearedPencil`, apart from its length-matrix
presentation and its positive coordinate vector.

The three fields `valid`, `targetConnected` and `targetGenus` are about the
*contracted* stage and are exactly the incoming triple recorded by
`CarriesClearedPencil`.  They are not recoverable from the expansion: the
expansion lemmas `Candidate.datum_valid`, `TargetExpansion.graph_connected` and
`TargetExpansion.graph_genus` all run in the opposite direction. -/
structure Seed (degree : ℕ) where
  /-- The contracted target: the seed's own tree with the resolving edge
  contracted. -/
  target : CFGraph.{0}
  /-- The contracted gluing datum. -/
  data : GluingDatum target degree
  /-- The contracted vertex. -/
  wall : target.V
  /-- Presentation of the seed's cover as a resolution of `wall`. -/
  presentation : Presentation data wall
  /-- Validity of the contracted datum.  See the module docstring: in a seed
  built forwards this is the induction hypothesis, and in a seed built by
  contracting a finished cover it is
  `ContractionRamification.valid_contractDatumAt`, whose own hypothesis is a
  `ContractionForest` receipt. -/
  valid : data.Valid
  /-- Connectedness of the contracted target. -/
  targetConnected : graph_connected target
  /-- The contracted target is a tree. -/
  targetGenus : genus target = 0

namespace Seed

variable {degree : ℕ} (seed : Seed degree)

/-- The seed presented as a candidate. -/
noncomputable def candidate : Candidate seed.target degree seed.data seed.wall :=
  seed.presentation.candidate

/-- The seed's own cover, over its own (expanded) target. -/
noncomputable def datum :
    GluingDatum (TargetExpansion.graph seed.target seed.wall
      seed.presentation.right) degree :=
  seed.presentation.expandedDatum

theorem datum_candidate : seed.candidate.datum = seed.datum := rfl

/-- The seed's cover is a valid gluing datum. -/
theorem datum_valid : seed.candidate.datum.Valid :=
  seed.candidate.datum_valid seed.valid

/-- The seed's target is connected. -/
theorem expandedTarget_connected :
    graph_connected (TargetExpansion.graph seed.target seed.wall
      seed.presentation.right) :=
  TargetExpansion.graph_connected seed.target seed.wall
    seed.presentation.right seed.targetConnected

/-- The seed's target is a tree. -/
theorem expandedTarget_genus :
    genus (TargetExpansion.graph seed.target seed.wall
      seed.presentation.right) = 0 := by
  rw [TargetExpansion.graph_genus seed.target seed.wall seed.presentation.right,
    seed.targetGenus]

/-- Clearing a positive rational coordinate vector on a seed. -/
noncomputable def clearedPencil {coordinate : Type*}
    (lengths : seed.candidate.datum.LengthMatrixPresentation coordinate)
    (coordinates : coordinate → ℚ) (hPositive : ∀ i, 0 < coordinates i) :
    Candidate.ClearedPencil seed.candidate lengths coordinates :=
  seed.candidate.clearedPencil seed.valid seed.targetConnected seed.targetGenus
    seed.wall lengths coordinates hPositive

/-- **The seed obligation, closed at the semantic layer.**  A `Seed`, a
*full-dimensional* source presentation of its cover and a positive rational
coordinate vector together inhabit
`SemanticAtlasMarch.CarriesClearedPencil`, which is the `carriesPencil` field
of `SemanticAtlasMarch.State`.  Nothing further is owed here; what remains for
the march's initial state is the *matrix* side -- a chart whose matrix is this
presentation's honest stable length matrix and whose determinant is nonzero.

The input is a `FullDimensionalSource.FullDimensionalSourcePresentation`, not a
bare `GluingDatum.LengthMatrixPresentation`, because the march payload carries
one: progress along the march factors through
`IncomingSourceCases.exists_classification`, which takes one; see
`SemanticAtlasMarch.CarriesClearedPencil`.  A seed therefore has to produce the
full-dimensional package, and the `Seed` structure's own three fields are not
enough.  `det_ne_zero` is a *field of the input* rather than a separate
matrix-side hypothesis. -/
theorem carriesClearedPencil {coordinate : Type}
    [Fintype coordinate] [DecidableEq coordinate]
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation
      seed.candidate.datum coordinate)
    (coordinates : coordinate → ℚ) (hPositive : ∀ i, 0 < coordinates i) :
    DraismaVargas.LocalCases.SemanticAtlasMarch.CarriesClearedPencil degree
      (GluingDatum.LengthMatrixPresentation.matrix
        fullDim.labelling.presentation) coordinates :=
  ⟨seed.target, seed.data, seed.wall, seed.candidate, fullDim, rfl, seed.valid,
    seed.targetConnected, seed.targetGenus,
    ⟨seed.clearedPencil fullDim.labelling.presentation coordinates hPositive⟩⟩

end Seed

/-! ## The receipt for a cover that was built before the wall was chosen -/

section Contraction

open DraismaVargas.Infrastructure.GluingTransport

/-- The statement -- *not* a theorem -- that a caller which built its cover as a
literal `CFGraph` and only afterwards chose an edge to contract still owes.

`Candidate.datum` is definitionally a datum over
`TargetExpansion.graph target wall right`, so such a caller must identify its
own target with that expansion and its own datum with the expanded one.  A
`CFGraph` isomorphism does not by itself carry a gluing datum, because a datum
is indexed by edge *occurrences*; `GluingTransport.transport` is the map that
does, so the receipt is an isomorphism together with one equation.

Two things this receipt deliberately does **not** provide:

* `smallData.Valid`.  Validity of the contracted datum is a separate theorem,
  `ContractionRamification.valid_contractDatumAt`, whose hypothesis
  `ContractionForestAt` is a genuine restriction on the cover -- the
  degree-two cover of a single edge whose zero-length source is a 2-cycle
  fails it.
* Connectedness and genus zero of `smallTarget`.  Both expansion lemmas run
  the other way.

A caller that instead builds its cover *forwards*, as one `TargetExpansion`
step applied to an already valid smaller datum, needs no receipt at all:
`Presentation.datum_candidate` is `rfl`, and the three contracted-stage facts
are its induction hypothesis. -/
structure ExpansionReceipt {degree : ℕ} {bigTarget : CFGraph.{0}}
    (bigData : GluingDatum bigTarget degree) {smallTarget : CFGraph.{0}}
    (smallData : GluingDatum smallTarget degree) (wallVertex : smallTarget.V)
    (side : smallTarget.edges → Bool) (resolution : LocalResolution degree)
    (exterior : ExteriorRefines smallData wallVertex side resolution) where
  /-- The seed's own target is the one-edge expansion of the contracted one. -/
  iso : CFGraphIso bigTarget
    (TargetExpansion.graph smallTarget wallVertex side)
  /-- Under that isomorphism the seed's own cover is the expanded datum. -/
  transported : transport iso bigData =
    GlobalResolution.datum smallData wallVertex side resolution
      exterior.oldCompatible

/-- With an `ExpansionReceipt` in hand, a caller owes no wall receipt: the two
endpoint inequalities come from Riemann--Hurwitz of its own cover. -/
noncomputable def Presentation.ofExpansionReceipt {degree : ℕ}
    {bigTarget : CFGraph.{0}} {bigData : GluingDatum bigTarget degree}
    {smallTarget : CFGraph.{0}} {smallData : GluingDatum smallTarget degree}
    {wallVertex : smallTarget.V} {side : smallTarget.edges → Bool}
    {resolution : LocalResolution degree}
    {exterior : ExteriorRefines smallData wallVertex side resolution}
    (contracts :
      resolution.ContractsTo (smallData.vertexPartition wallVertex))
    (receipt : ExpansionReceipt bigData smallData wallVertex side resolution
      exterior)
    (hBig : bigData.RiemannHurwitz) :
    Presentation smallData wallVertex :=
  Presentation.ofExpandedRiemannHurwitz side resolution contracts exterior
    (receipt.transported ▸ riemannHurwitz_transport receipt.iso bigData hBig)

end Contraction

end DraismaVargas.LocalCases.SeedCandidate
