import DraismaVargas.LocalCases.WallProgress
import DraismaVargas.LocalCases.W3Nd2PositiveExit
import DraismaVargas.LocalCases.W3Nd3ArbitraryExit
import DraismaVargas.LocalCases.W3ShiftClosure
import DraismaVargas.LocalCases.W3FourStableGraph
import DraismaVargas.LocalCases.W3FourRegrownColumn

/-!
# The trivalent wall's route into `PresentedProgress`

`ClassifiedContinuation.SourceCase` has ten constructors, one per
determinant-balance shape.  This file gives each of the four **trivalent** tags
-- `w3Four`, `w3Shift`, `w3Nd3CoarseFine`, `w3Nd2CoarseFine` -- a
`WallProgress.WallInput`, so that the balanced family of each case reaches
`PresentedProgress`.  Three of them sit on top of the generic one-datum
constructor `WallProgress.WallInput.ofTrivalent`; `w3Four`, which no one-datum
constructor can serve, sits on top of `WallProgress.WallInput.ofGauge`.
Equations (2)--(5) and Figures 28 and 31 are those of Draisma–Vargas Part I,
arXiv:1909.12924.

## One constructor, three specializations, and why

`ofTrivalent` is one constructor for the three one-datum trivalent tags: it
takes the tag as a parameter together with an arity equation (and it serves
one-datum tags of other valencies the same way).  Nothing in `WallInput` beyond
the tag distinguishes those trivalent shapes: all a wall input wants is a
balanced family whose wall column is the crossed coordinate.

The four specializations below differ because the four *sources* differ, not
because the output does:

* `ofNd3CoarseFine` -- Equation (4), `W3Nd3CommonBalance.honestPresentedFamily`
  applied at the ambient coordinate.  A presented family already exists.
* `ofNd2CoarseFine` -- Equation (5).  `W3Nd2CommonBalance` stops at
  `BalancedGlobal.Family`, which forgets the presentations, so `nd2Family`
  below rebuilds the presented form from the same `labelling`,
  `positiveBalance` and `matrices_agree`.  Nothing is reproved: the arithmetic
  is `W3Nd2CommonBalance`'s.
* `ofShift` -- Equation (3).  `W3ShiftClosure.equationThreeGaugeFamily` targets
  `W3FourClosure.GaugeFamily`, but it sets `base := fun _ ↦ base`: both members
  of the shift pair live over the *one* gauge copy, so the family is a genuine
  `PresentedFamily` over that copy and `shiftFamily` says so.  The wall input's
  datum is then the gauge copy, valid by `W3FourDisjointness.BranchGauge.valid`
  in the form the caller passes as `gauge`.
* `ofFour` -- Equation (2), through the per-member base of a gauge family.
  This one is **not** a `PresentedFamily` and cannot be made one; see below.

## `w3Four`: the fourth tag, through the per-member base

Figure 28's four members are not a `PresentedFamily`: `M⁽¹⁾` and `M⁽²⁾` need
opposite gauge conditions, so the four members do not all live over one
`data`, as `W3FourClosure` records.  `BalancedGlobal.GaugeFamily` (which
`W3FourClosure.GaugeFamily` abbreviates) exists precisely because of that, with
a per-member `base : Fin n → GluingDatum target degree`.
`W3FourStableGraph.Figure28Receipts.gaugeFamily` instantiates it at
`base := fun i ↦ (receipts.member i).base`, four gauge copies.

`WallProgress.WallInput.family` and `SemanticAtlasMarch.PresentedProgress.familyAt`
both carry a `BalancedGlobal.GaugeFamily`, so they accept that family.
`WallProgress.WallInput.ofGauge` is the constructor, and `ofFour` below is
Figure 28's instance of it, reindexed from `Option target.edges` to the ambient
coordinate by `WallProgress.gaugeFamilyReindex` exactly as `ofFourValent` and
`ofShiftReindexed` reindex theirs.  The one-datum routes are unaffected:
`ofTrivalent` takes a `PresentedFamily` and is literally `ofGauge` of its
`toGaugeFamily` (`WallProgress.WallInput.ofTrivalent_eq_ofGauge`).

**What `ofFour` does and does not certify.**  Its family is the one Figure 28
carries, whose presentations are `W3FourStableGraph.MemberColumn.presentation`:
canonical presentations built from the members' regrown occurrences and the
limit's `LimitRows` census.  Two statements about them have to be kept apart.

*The matrices are honest.*  `W3FourRegrownColumn.exists_figure28Receipts_honest`
produces receipts at the limit's own rows (`W3FourLimitRows.limitRowsOfInput`)
for which every `receipts.presentation i` satisfies
`W3FourRegrownColumn.IsHonest` -- its length matrix **is** that member's
`StableSourceMatrix.matrix`, read through a bijection of the stable rows and the
canonical bijection of the columns.  `exists_ofFour_honest` below is `ofFour` on
exactly those receipts, and records what the reindexing does to them: the wall
input's own matrices are the honest ones submatrixed by `relabel`
(`ClassifierInterface.matrix_reindex`).

*The presentations are not `StableLengthMatrixLabelling`s.*  `IsHonest` is an
equality of **matrices** modulo a row bijection; the full-dimensional field
pair of `PresentedProgress` (see §4) needs an equality of
`LengthMatrixPresentation`s (`targetEdge` *and* `path`) together with a whole
`FullDimensionalSourcePresentation`, and no `StableGraphIncidence.Equivalence`
is built for any of the four members here.  So `ofFour` gives the wall
dispatcher its `w3Four` input, but not the full-dimensional field pair for it:
there is no `A04FourTags.FullDimSupply (ofFour …)`.  That supply is
`A04MoreTags.w3FourSupply`, on the sibling wall input `A04MoreTags.ofFourHonest`
whose family carries the members' own honest labellings.  That is exactly the
line `A04FourTags` draws for `w4` between `ofFourValent` and
`ofFourValentHonest`, and `W4OutgoingLimitMatrix.presentedFamily_matrix_eq` is
the same kind of matrix-only identification there.

`exists_ofFour` is the non-vacuity statement: on the branch flags of
`W3FourStableGraph.nonempty_figure28Receipts` -- which are
`W3FourClosure.exists_equationTwo_family`'s -- a `w3Four` wall input over the
incoming datum actually exists.

## Full-dimensional presentations, for the cases routed here

`SemanticAtlasMarch.PresentedProgress` carries `fullDimAt`/`fullDimPresentation`
as fields, gated on `det ≠ 0` at the outgoing member.  For the two coarse–fine
cases they come from a transport:
`StableGraphFullDimensional.presentationOfEquivalence` transports
**all eight** fields of a `FullDimensionalSourcePresentation` along a
`StableGraphIncidence.Equivalence` plus four numerical receipts, and
`W3Nd2PositiveExit.outgoingPresentation` / `W3Nd3ArbitraryExit.outgoingPresentation`
are exactly that transport for these families.  `nd2_exists_fullDim` and
`nd3_exists_fullDim` below are the resulting suppliers, one `exact` each, and
`presentedProgress_fullDim_gated` shows they have exactly the shape the gated
field pair yields.

The gate is not optional.  `det_ne_zero` is a field of
`FullDimensionalSourcePresentation`, so `fullDim_forces_det_ne_zero` and
`no_total_fullDim_of_singularFamily` below show that a *total* (ungated)
`fullDimAt` is not merely inconvenient but **unsatisfiable**: it forces every
member of every family to be nonsingular, and
`ClassifiedContinuation.SingularMember.singularFamily` is a `PresentedFamily`
with a provably singular member.  The two theorems record why the gate is
there, exactly as `SingularMember.no_total_registration_of_singularFamily` does
for `outgoingMatrix`.
-/

namespace DraismaVargas.LocalCases.W3WallInput

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.ClassifiedContinuation
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.W3R1SourceProfile
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W3Nd2SourceCandidates
open DraismaVargas.LocalCases.W3Nd2FineCandidates
open DraismaVargas.LocalCases.WallProgress

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {wall : coordinate}

/-! ## 1.  `w3Nd3CoarseFine` -/

section Nd3

variable {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wallVertex}
  (input : W3SourceInput data star)
  (profile : Nd3Profile data input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)

/-- **Equation (4)'s wall input.**  `W3Nd3CommonBalance.honestPresentedFamily`
is already a presented family over the incoming datum, parametric in the
coordinate; instantiating it at the march's coordinate through `initial` -- the
role `W3Nd3ArbitraryExit.initialLabelling` plays -- is the whole of the
construction. -/
noncomputable def ofNd3CoarseFine
    (initial : StableLengthMatrixLabelling
      (W3Nd3CommonBalance.members input profile hSame 0).datum coordinate)
    (hwallColumn : W3Nd3CommonBalance.wallColumn input profile hSame initial = wall)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) :
    WallInput degree coordinate wall :=
  WallInput.ofTrivalent
    (W3Nd3CommonBalance.honestPresentedFamily input profile hSame initial)
    input.valid SourceCase.w3Nd3CoarseFine rfl hwallColumn targetConnected
    targetGenus root

@[simp] theorem ofNd3CoarseFine_case
    (initial : StableLengthMatrixLabelling
      (W3Nd3CommonBalance.members input profile hSame 0).datum coordinate)
    (hwallColumn : W3Nd3CommonBalance.wallColumn input profile hSame initial = wall)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) :
    (ofNd3CoarseFine (wall := wall) input profile hSame initial hwallColumn
      targetConnected targetGenus root).case = SourceCase.w3Nd3CoarseFine := rfl

end Nd3

/-! ## 2.  `w3Nd2CoarseFine`

`W3Nd2CommonBalance` never packages its two Figure 31 members as a
`PresentedFamily`; `canonicalFamily` is a `BalancedGlobal.Family`, which has
only a `matrix` field.  The three definitions here restore the presentations.
The members are `W3Nd2SourceCandidates.coarseCandidate` and
`W3Nd2FineCandidates.fineCandidate` themselves rather than their `certified`
images, which is what a `PresentedFamily.candidate` slot needs; at each literal
position the two have the same `datum`, so `W3Nd2CommonBalance.labelling`
typechecks against them unchanged. -/

section Nd2

variable {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wallVertex}
  (input : W3SourceInput data star)
  (profile : Nd2Profile data input.distinguishedBlock)

/-- The two actual Figure 31 members, as `Candidate`s rather than as the
`CertifiedCandidate`s `W3Nd2CommonBalance.candidates` records. -/
noncomputable def nd2Members :
    Fin 2 → BalancedGlobal.Candidate target degree data wallVertex :=
  ![coarseCandidate input profile, fineCandidate input profile]

@[simp] theorem nd2Members_certified (position : Fin 2) :
    (nd2Members input profile position).certified =
      W3Nd2CommonBalance.candidates input profile position := by
  fin_cases position <;> rfl

/-- The induced honest square presentations, read on the members themselves. -/
noncomputable def nd2Presentation
    (initial : StableLengthMatrixLabelling
      (W3Nd2CommonBalance.candidates input profile 0).datum coordinate) :
    ∀ position : Fin 2,
      (nd2Members input profile position).datum.LengthMatrixPresentation coordinate
  | 0 => (W3Nd2CommonBalance.labelling input profile initial 0).presentation
  | 1 => (W3Nd2CommonBalance.labelling input profile initial 1).presentation

omit [Fintype coordinate] in
@[simp] theorem nd2Presentation_matrix
    (initial : StableLengthMatrixLabelling
      (W3Nd2CommonBalance.candidates input profile 0).datum coordinate)
    (position : Fin 2) :
    GluingDatum.LengthMatrixPresentation.matrix
        (nd2Presentation input profile initial position) =
      W3Nd2CommonBalance.squareMatrix input profile initial position := by
  fin_cases position <;> rfl

/-- **Equation (5) as a presented family.**  Same members, same labellings,
same balance and same off-wall agreement as `W3Nd2CommonBalance.family`; only
the presentations are retained instead of forgotten. -/
noncomputable def nd2Family
    (initial : StableLengthMatrixLabelling
      (W3Nd2CommonBalance.candidates input profile 0).datum coordinate) :
    BalancedGlobal.PresentedFamily (coordinate := coordinate) 2 data wallVertex where
  candidate := nd2Members input profile
  presentation := nd2Presentation input profile initial
  wallColumn := W3Nd2CommonBalance.wallColumn input profile initial
  weight := ![1, 1]
  positiveBalance := by
    have hmatrix : (fun position ↦ (GluingDatum.LengthMatrixPresentation.matrix
          (nd2Presentation input profile initial position)).det) =
        fun position ↦
          (W3Nd2CommonBalance.squareMatrix input profile initial position).det := by
      funext position
      rw [nd2Presentation_matrix]
    rw [hmatrix]
    exact W3Nd2CommonBalance.positiveBalance input profile initial
  agreeOffWall := by
    intro first second
    rw [nd2Presentation_matrix, nd2Presentation_matrix]
    exact W3Nd2CommonBalance.matrices_agree input profile initial first second

@[simp] theorem nd2Family_presentation
    (initial : StableLengthMatrixLabelling
      (W3Nd2CommonBalance.candidates input profile 0).datum coordinate)
    (position : Fin 2) :
    (nd2Family input profile initial).presentation position =
      nd2Presentation input profile initial position := rfl

@[simp] theorem nd2Family_wallColumn
    (initial : StableLengthMatrixLabelling
      (W3Nd2CommonBalance.candidates input profile 0).datum coordinate) :
    (nd2Family input profile initial).wallColumn =
      W3Nd2CommonBalance.wallColumn input profile initial := rfl

/-- **Equation (5)'s wall input.** -/
noncomputable def ofNd2CoarseFine
    (initial : StableLengthMatrixLabelling
      (W3Nd2CommonBalance.candidates input profile 0).datum coordinate)
    (hwallColumn : W3Nd2CommonBalance.wallColumn input profile initial = wall)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) :
    WallInput degree coordinate wall :=
  WallInput.ofTrivalent (nd2Family input profile initial) input.valid
    SourceCase.w3Nd2CoarseFine rfl hwallColumn targetConnected targetGenus root

@[simp] theorem ofNd2CoarseFine_case
    (initial : StableLengthMatrixLabelling
      (W3Nd2CommonBalance.candidates input profile 0).datum coordinate)
    (hwallColumn : W3Nd2CommonBalance.wallColumn input profile initial = wall)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) :
    (ofNd2CoarseFine (wall := wall) input profile initial hwallColumn
      targetConnected targetGenus root).case = SourceCase.w3Nd2CoarseFine := rfl

end Nd2

/-! ## 3.  `w3Shift` -/

section Shift

variable {target : CFGraph.{0}} {wallVertex : target.V}
  {data base : GluingDatum target degree}

/-- **Equation (3) as a presented family.**  `W3ShiftClosure.equationThreeGaugeFamily`
lands in `GaugeFamily` only because its statement is shared with Figure 28's
four-member case; its `base` field is the constant function, so the pair is a
`PresentedFamily` over the one gauge copy.  Weights, balance and off-wall
agreement are `W3ShiftClosure`'s. -/
noncomputable def shiftFamily
    (member : Fin 2 → BalancedGlobal.Candidate target degree base wallVertex)
    (rows : W3ShiftClosure.LimitRows member coordinate) :
    BalancedGlobal.PresentedFamily (coordinate := coordinate) 2 base wallVertex where
  candidate := member
  presentation := rows.presentation
  wallColumn := rows.wallColumn
  weight := ![rows.movingIndex - 1, rows.movingIndex + 1]
  positiveBalance := by
    rw [funext rows.det]
    exact BalancingRemaining.balance_shift_pair rows.one_lt_movingIndex'
      rows.wallRelation
  agreeOffWall := rows.agreeOffWall

@[simp] theorem shiftFamily_toGaugeFamily
    (gauge : data.Valid → base.Valid)
    (member : Fin 2 → BalancedGlobal.Candidate target degree base wallVertex)
    (rows : W3ShiftClosure.LimitRows member coordinate) (position : Fin 2) :
    (shiftFamily (coordinate := coordinate) member rows).presentation position =
      (W3ShiftClosure.equationThreeGaugeFamily (data := data) base gauge member
        rows).presentation position := rfl

/-- **Equation (3)'s wall input.**  The datum is the gauge copy the shift pair
lives over, not the incoming datum; `gauge` is `BranchGauge.valid`. -/
noncomputable def ofShift
    (member : Fin 2 → BalancedGlobal.Candidate target degree base wallVertex)
    (rows : W3ShiftClosure.LimitRows member coordinate)
    (hBase : base.Valid) (hwallColumn : rows.wallColumn = wall)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) :
    WallInput degree coordinate wall :=
  WallInput.ofTrivalent (shiftFamily member rows) hBase SourceCase.w3Shift rfl
    hwallColumn targetConnected targetGenus root

/-- **Equation (3)'s wall input at the ambient coordinate.**  The shift pair's
*derived* rows, `W3ShiftLimitRows.limitRows` -- the only inhabitant of
`W3ShiftClosure.LimitRows` the library produces, through
`W3ShiftLimitRows.exists_shift_limitRows` -- are stated at
`Option target.edges` with `wallColumn = none`, so getting them to the march's
coordinate needs the same reindexing along `relabel` that `ofFourValent` and
`ofFour` use.
`ofShift` above is the coordinate-free form; this is the composite. -/
noncomputable def ofShiftReindexed [DecidableEq target.edges]
    (member : Fin 2 → BalancedGlobal.Candidate target degree base wallVertex)
    (rows : W3ShiftClosure.LimitRows member (Option target.edges))
    (hBase : base.Valid) (hwallColumn : rows.wallColumn = none)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) (relabel : coordinate ≃ Option target.edges)
    (hrelabel : relabel wall = none) :
    WallInput degree coordinate wall :=
  WallInput.ofTrivalent
    (ClassifierInterface.familyReindex relabel (shiftFamily member rows))
    hBase SourceCase.w3Shift rfl
    (by
      rw [ClassifierInterface.familyReindex_wallColumn,
        show (shiftFamily (coordinate := Option target.edges) member rows).wallColumn
          = rows.wallColumn from rfl, hwallColumn]
      exact (Equiv.symm_apply_eq relabel).mpr hrelabel.symm)
    targetConnected targetGenus root

@[simp] theorem ofShiftReindexed_case [DecidableEq target.edges]
    (member : Fin 2 → BalancedGlobal.Candidate target degree base wallVertex)
    (rows : W3ShiftClosure.LimitRows member (Option target.edges))
    (hBase : base.Valid) (hwallColumn : rows.wallColumn = none)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) (relabel : coordinate ≃ Option target.edges)
    (hrelabel : relabel wall = none) :
    (ofShiftReindexed (wall := wall) member rows hBase hwallColumn targetConnected
      targetGenus root relabel hrelabel).case = SourceCase.w3Shift := rfl

@[simp] theorem ofShift_case
    (member : Fin 2 → BalancedGlobal.Candidate target degree base wallVertex)
    (rows : W3ShiftClosure.LimitRows member coordinate)
    (hBase : base.Valid) (hwallColumn : rows.wallColumn = wall)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) :
    (ofShift (wall := wall) member rows hBase hwallColumn targetConnected
      targetGenus root).case = SourceCase.w3Shift := rfl

end Shift

/-! ## 3b.  `w3Four`

The one trivalent tag that `ofTrivalent` cannot serve; it goes through
`WallProgress.WallInput.ofGauge`. -/

section Four

variable {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- **Equation (2)'s wall input.**  `W3FourStableGraph.Figure28Receipts.gaugeFamily`
is Figure 28's four members with their four gauge copies as `base`, their
`W3FourDisjointness.BranchGauge.valid` proofs as `valid_of_old`, Figure 28's four
determinants as `positiveBalance` (`det_eq_figure28`, proved, not assumed) and
the common off-wall columns as `agreeOffWall`
(`MemberColumn.presentation_agreeOffWall`, likewise proved).  It is stated over
`Option target.edges` with `wallColumn = none`, so reaching the march's
coordinate is the same reindexing `ofFourValent` and `ofShiftReindexed` perform.

The datum is the incoming wall datum itself: unlike `ofShift`, no gauge copy is
promoted to the wall input's `data`, because the four members disagree about
which copy they live on.  `hValid` is the incoming datum's validity, and each
member's own validity is `receipts.gaugeFamily.valid_of_old` inside the family.

This is the whole `w3Four` route.  It carries no honest-presentation claim; see
the module header. -/
noncomputable def ofFour
    {geometry : W3FourClosure.FourStarGeometry data wallVertex}
    (receipts : W3FourStableGraph.Figure28Receipts data wallVertex geometry)
    (hValid : data.Valid)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) (relabel : coordinate ≃ Option target.edges)
    (hrelabel : relabel wall = none) :
    WallInput degree coordinate wall :=
  WallInput.ofGauge (gaugeFamilyReindex relabel receipts.gaugeFamily)
    hValid SourceCase.w3Four rfl
    (by
      rw [gaugeFamilyReindex_wallColumn,
        W3FourStableGraph.Figure28Receipts.gaugeFamily_wallColumn]
      exact (Equiv.symm_apply_eq relabel).mpr hrelabel.symm)
    targetConnected targetGenus root

@[simp] theorem ofFour_case
    {geometry : W3FourClosure.FourStarGeometry data wallVertex}
    (receipts : W3FourStableGraph.Figure28Receipts data wallVertex geometry)
    (hValid : data.Valid)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) (relabel : coordinate ≃ Option target.edges)
    (hrelabel : relabel wall = none) :
    (ofFour (wall := wall) receipts hValid targetConnected targetGenus root
      relabel hrelabel).case = SourceCase.w3Four := rfl

@[simp] theorem ofFour_data
    {geometry : W3FourClosure.FourStarGeometry data wallVertex}
    (receipts : W3FourStableGraph.Figure28Receipts data wallVertex geometry)
    (hValid : data.Valid)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) (relabel : coordinate ≃ Option target.edges)
    (hrelabel : relabel wall = none) :
    (ofFour (wall := wall) receipts hValid targetConnected targetGenus root
      relabel hrelabel).data = data := rfl

/-- **The four members of the `w3Four` wall input are Figure 28's four members,
each over its own gauge copy.**  Nothing is transported and nothing is
identified: `ofFour`'s family reads back the receipts' members verbatim. -/
@[simp] theorem ofFour_family_candidate
    {geometry : W3FourClosure.FourStarGeometry data wallVertex}
    (receipts : W3FourStableGraph.Figure28Receipts data wallVertex geometry)
    (hValid : data.Valid)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) (relabel : coordinate ≃ Option target.edges)
    (hrelabel : relabel wall = none) (i : Fin 4) :
    (ofFour (wall := wall) receipts hValid targetConnected targetGenus root
        relabel hrelabel).family.candidate i =
      (receipts.member i).candidate := rfl

/-- and their base data are the four gauge copies. -/
@[simp] theorem ofFour_family_base
    {geometry : W3FourClosure.FourStarGeometry data wallVertex}
    (receipts : W3FourStableGraph.Figure28Receipts data wallVertex geometry)
    (hValid : data.Valid)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) (relabel : coordinate ≃ Option target.edges)
    (hrelabel : relabel wall = none) (i : Fin 4) :
    (ofFour (wall := wall) receipts hValid targetConnected targetGenus root
        relabel hrelabel).family.base i = (receipts.member i).base := rfl

/-- **The `w3Four` route is not vacuous.**  On every datum of the case carrying
the three branch flags -- the hypotheses of
`W3FourStableGraph.nonempty_figure28Receipts`, which are
`W3FourClosure.exists_equationTwo_family`'s -- there is an actual `w3Four` wall
input over the incoming datum.  Nothing new is assumed: the receipts come from
`exists_figure28Receipts` at the consistency census `LimitRows.model`, and the
validity is `input.valid`. -/
theorem exists_ofFour
    {star : ThreeStar target wallVertex} {input : W3SourceInput data star}
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wallVertex).blockCard input.distinguishedBlock.1)
    (root : target.V) (hRoot : root ≠ wallVertex)
    (hGrowFixed :
      TargetBranchRegion.edgeMoved wallVertex root hRoot profile.first.1.1.1 = false)
    (hLargestFixed :
      TargetBranchRegion.edgeMoved wallVertex root hRoot profile.largest.1.1.1 = false)
    (hOtherMoved :
      TargetBranchRegion.edgeMoved wallVertex root hRoot profile.second.1.1.1 = true)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (relabel : coordinate ≃ Option target.edges) (hrelabel : relabel wall = none) :
    ∃ wallInput : WallInput degree coordinate wall,
      wallInput.case = SourceCase.w3Four ∧ wallInput.target = target ∧
        HEq wallInput.data data := by
  obtain ⟨receipts⟩ := W3FourStableGraph.nonempty_figure28Receipts profile directions
    largest_index root hRoot hGrowFixed hLargestFixed hOtherMoved
  exact ⟨ofFour (wall := wall) receipts input.valid targetConnected targetGenus root
    relabel hrelabel, rfl, rfl, HEq.rfl⟩

/-- **The `w3Four` route on Figure 28's honest matrices.**
`W3FourRegrownColumn.exists_figure28Receipts_honest` produces the receipts at the
limit's own rows with every presented matrix proved to be the member's own
`StableSourceMatrix.matrix` (`W3FourRegrownColumn.IsHonest`), and `ofFour`
accepts them unchanged -- honesty is a property of the receipts, not an extra
field of the wall input.  The last conjunct is what the coordinate change does:
the wall input's matrices are those honest matrices submatrixed by `relabel`,
which is `ClassifierInterface.matrix_reindex`.

This does **not** supply the full-dimensional field pair for `w3Four`; see the
module header for the gap between a matrix identification and a
`FullDimensionalSourcePresentation`. -/
theorem exists_ofFour_honest
    {star : ThreeStar target wallVertex} {input : W3SourceInput data star}
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wallVertex).blockCard input.distinguishedBlock.1)
    (root : target.V) (hRoot : root ≠ wallVertex)
    (hGrowFixed :
      TargetBranchRegion.edgeMoved wallVertex root hRoot profile.first.1.1.1 = false)
    (hLargestFixed :
      TargetBranchRegion.edgeMoved wallVertex root hRoot profile.largest.1.1.1 = false)
    (hOtherMoved :
      TargetBranchRegion.edgeMoved wallVertex root hRoot profile.second.1.1.1 = true)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (relabel : coordinate ≃ Option target.edges) (hrelabel : relabel wall = none) :
    ∃ (geometry : W3FourClosure.FourStarGeometry data wallVertex)
        (receipts : W3FourStableGraph.Figure28Receipts data wallVertex geometry),
      (∀ i : Fin 4, W3FourRegrownColumn.IsHonest (receipts.member i).candidate
          (receipts.presentation i)) ∧
        (ofFour (wall := wall) receipts input.valid targetConnected targetGenus root
          relabel hrelabel).case = SourceCase.w3Four ∧
        ∀ i : Fin 4,
          GluingDatum.LengthMatrixPresentation.matrix
              ((ofFour (wall := wall) receipts input.valid targetConnected targetGenus
                root relabel hrelabel).family.presentation i) =
            (GluingDatum.LengthMatrixPresentation.matrix
              (receipts.presentation i)).submatrix relabel relabel := by
  obtain ⟨receipts, -, -, -, honest⟩ :=
    W3FourRegrownColumn.exists_figure28Receipts_honest input.valid profile directions
      largest_index root hRoot hGrowFixed hLargestFixed hOtherMoved
  exact ⟨_, receipts, honest, rfl,
    fun i ↦ ClassifierInterface.matrix_reindex relabel (receipts.presentation i)⟩

end Four

/-! ## 4.  The full-dimensional field pair, and its shape

`SemanticAtlasMarch.PresentedProgress` carries

```
fullDimAt : ∀ wall (outgoing : Fin (caseAt wall).arity),
  (matrix ((familyAt wall).presentation outgoing)).det ≠ 0 →
  FullDimensionalSourcePresentation ((familyAt wall).candidate outgoing).datum coordinate
fullDimPresentation : ∀ wall outgoing hdet,
  (fullDimAt wall outgoing hdet).labelling.presentation = (familyAt wall).presentation outgoing
```

as fields.  Two facts about that pair are proved here.

**It is available, per member, gated on nonsingularity.**  Not one of the eight
fields has to be re-derived: `StableGraphFullDimensional.presentationOfEquivalence`
transports the whole package along a `StableGraphIncidence.Equivalence`, and the
two coarse–fine cases have that equivalence --
`W3Nd2CoarseStableGraph.coarseStableGraphEquivalence`,
`W3Nd2FineStableGraph.fineStableGraphEquivalence`,
`W3Nd3LimitMatrix.coarseStableGraphEquivalence`/`fineStableGraphEquivalence`,
bundled as `W3Nd2PositiveExit.equivalence` and `W3Nd3ArbitraryExit.equivalence`.
`nd2_exists_fullDim` and `nd3_exists_fullDim` are one `exact` each on top of
`outgoingPresentation`, and `presentedProgress_fullDim_gated` is the check that
their conclusion is what the gated field pair reads off.

**It is not available totally, and no work can make it so.**
`fullDim_forces_det_ne_zero` reads an ungated pair together: it *implies* every
member of the family is nonsingular.  That is exactly the hypothesis the
nonsingularity gate avoids, and
`ClassifiedContinuation.SingularMember.singularFamily` refutes it outright --
`no_total_fullDim_of_singularFamily` is the same argument
`ClassifiedContinuation.SingularMember.no_total_registration_of_singularFamily`
makes against a total `outgoingMatrix`.  The fields are therefore gated, and the
two theorems record why. -/

section A04

/-- **An ungated `fullDimAt`/`fullDimPresentation` pair implies total
nonsingularity.**  A `FullDimensionalSourcePresentation` carries `det_ne_zero`
about its own labelling, and the presentation equation says that labelling
presents the member.  This is why `PresentedProgress` gates both fields. -/
theorem fullDim_forces_det_ne_zero {target : CFGraph.{0}} {n : ℕ}
    {data : GluingDatum target degree} {wallVertex : target.V}
    (family : BalancedGlobal.PresentedFamily (coordinate := coordinate) n data wallVertex)
    (fullDim : ∀ i, FullDimensionalSourcePresentation (family.candidate i).datum coordinate)
    (hPresentation : ∀ i, (fullDim i).labelling.presentation = family.presentation i)
    (i : Fin n) :
    (GluingDatum.LengthMatrixPresentation.matrix (family.presentation i)).det ≠ 0 := by
  rw [← hPresentation i]
  exact (fullDim i).det_ne_zero

/-- **So an ungated `fullDimAt`/`fullDimPresentation` pair is unsatisfiable.**
The witness is the one the gate was written for: a presented family with a
nonsingular incoming member, an opposite-sign partner, and a singular member
in between.  This is why `PresentedProgress` gates the fields. -/
theorem no_total_fullDim_of_singularFamily {target : CFGraph.{0}}
    {data : GluingDatum target degree} {wallVertex : target.V}
    (candidate : BalancedGlobal.Candidate target degree data wallVertex)
    (presentation : candidate.datum.LengthMatrixPresentation coordinate)
    (a b : coordinate) (hab : a ≠ b) :
    ¬ ∃ fullDim : ∀ i : Fin 3, FullDimensionalSourcePresentation
        ((SingularMember.singularFamily candidate presentation a b hab).candidate i).datum
          coordinate,
      ∀ i, (fullDim i).labelling.presentation =
        (SingularMember.singularFamily candidate presentation a b hab).presentation i := by
  rintro ⟨fullDim, hPresentation⟩
  refine fullDim_forces_det_ne_zero _ fullDim hPresentation 1 ?_
  exact SingularMember.singularFamily_det_one candidate presentation a b hab

/-- **The field pair is gated.**  Read at a
nonsingular member, `PresentedProgress.fullDimAt`/`fullDimPresentation` give
exactly the conclusion `nd2_exists_fullDim` and `nd3_exists_fullDim` supply.
This elaborates only while both fields take the determinant hypothesis; the
total form `no_total_fullDim_of_singularFamily` refutes would break it here. -/
theorem presentedProgress_fullDim_gated {chart : Type}
    {matrix : chart → Matrix coordinate coordinate ℚ}
    {baseStart baseFinish : coordinate → ℚ}
    {current : SemanticAtlasMarch.State degree matrix baseStart baseFinish}
    (progress : current.PresentedProgress) (wall : coordinate)
    (hw : current.FirstWall wall)
    (outgoing : Fin (progress.caseAt wall hw).arity)
    (hdet : (GluingDatum.LengthMatrixPresentation.matrix
      ((progress.familyAt wall hw).presentation outgoing)).det ≠ 0) :
    ∃ fd : FullDimensionalSourcePresentation
        ((progress.familyAt wall hw).candidate outgoing).datum coordinate,
      fd.labelling.presentation = (progress.familyAt wall hw).presentation outgoing :=
  ⟨progress.fullDimAt wall hw outgoing hdet,
    progress.fullDimPresentation wall hw outgoing hdet⟩

/-- **The full-dimensional presentation for `w3Nd2CoarseFine`, in the gated
form.**  Every field of the
outgoing package is transported; nothing is re-derived and nothing is assumed
beyond the incoming member's own full-dimensional presentation and the
standing target hypotheses. -/
theorem nd2_exists_fullDim {target : CFGraph.{0}} {wallVertex : target.V}
    {data : GluingDatum target degree} {star : ThreeStar target wallVertex}
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd2CommonBalance.candidates input profile incoming).datum coordinate)
    (outgoing : Fin 2)
    (hdet : (GluingDatum.LengthMatrixPresentation.matrix
      ((nd2Family input profile
        (W3Nd2PositiveExit.initialLabelling input profile incoming
          incomingFD)).presentation outgoing)).det ≠ 0) :
    ∃ fd : FullDimensionalSourcePresentation
        ((nd2Family input profile
          (W3Nd2PositiveExit.initialLabelling input profile incoming
            incomingFD)).candidate outgoing).datum coordinate,
      fd.labelling.presentation =
        (nd2Family input profile
          (W3Nd2PositiveExit.initialLabelling input profile incoming
            incomingFD)).presentation outgoing := by
  fin_cases outgoing
  · exact ⟨W3Nd2PositiveExit.outgoingPresentation input profile hConnected hGenus
      incoming 0 incomingFD hdet, rfl⟩
  · exact ⟨W3Nd2PositiveExit.outgoingPresentation input profile hConnected hGenus
      incoming 1 incomingFD hdet, rfl⟩

/-- **The full-dimensional presentation for `w3Nd3CoarseFine`, in the gated
form.** -/
theorem nd3_exists_fullDim {target : CFGraph.{0}} {wallVertex : target.V}
    {data : GluingDatum target degree} {star : ThreeStar target wallVertex}
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd3CommonBalance.candidates input profile hSame incoming).datum coordinate)
    (outgoing : Fin 2)
    (hdet : (GluingDatum.LengthMatrixPresentation.matrix
      ((W3Nd3CommonBalance.honestPresentedFamily input profile hSame
        (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming
          incomingFD)).presentation outgoing)).det ≠ 0) :
    ∃ fd : FullDimensionalSourcePresentation
        ((W3Nd3CommonBalance.honestPresentedFamily input profile hSame
          (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming
            incomingFD)).candidate outgoing).datum coordinate,
      fd.labelling.presentation =
        (W3Nd3CommonBalance.honestPresentedFamily input profile hSame
          (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming
            incomingFD)).presentation outgoing := by
  fin_cases outgoing
  · exact ⟨W3Nd3ArbitraryExit.outgoingPresentation input profile hSame hConnected
      hGenus incoming 0 incomingFD hdet, rfl⟩
  · exact ⟨W3Nd3ArbitraryExit.outgoingPresentation input profile hSame hConnected
      hGenus incoming 1 incomingFD hdet, rfl⟩

end A04

end DraismaVargas.LocalCases.W3WallInput
